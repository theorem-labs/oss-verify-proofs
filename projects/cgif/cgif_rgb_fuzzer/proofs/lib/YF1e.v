(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YK18 YK0k YQ0b YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Variable segs : list Segment.
Lemma amrealE_ibind_ext {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amrealE segs (f a) W1 c1 Q -> amrealE segs (g a) W1 c1 Q) ->
amrealE segs (ibind t f) W c Q -> amrealE segs (ibind t g) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q Hfg H; cbn [ibind amrealE] in *.
- img_exact (Hfg a W c H).
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; eapply IH; [img_try (img_exact Hfg) | img_try (img_exact (H8 i Hi))]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact Hfg) | img_try (img_exact HR)].
- img_exact H.
- img_exact I.
Qed.
Lemma amreal_ibind_ext2 {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amreal segs (f a) W1 c1 Q -> amreal segs (g a) W1 c1 Q) ->
(forall a W1 c1, amrealE segs (f a) W1 c1 Q -> amrealE segs (g a) W1 c1 Q) ->
amreal segs (ibind t f) W c Q -> amreal segs (ibind t g) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q Hfg HfgE H; cbn [ibind amreal] in *.
- img_exact (Hfg a W c H).
- eapply SRr_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hd & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (H8 i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [img_try (img_exact Hfg) | img_try (img_exact HfgE) | img_try (img_exact H8)] | eapply amrealE_ibind_ext; [img_try (img_exact HfgE) | img_try (img_exact H8)]]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact Hfg) | img_try (img_exact HfgE) | img_try (img_exact HR)].
- img_exact H.
- img_exact I.
Qed.
Lemma amrealE_ibind_assoc {A B R} : forall (t : itree astate A) (f : A -> itree astate B) (g : B -> itree astate R) W c
(Q : R -> world segs -> config -> Prop),
amrealE segs (ibind (ibind t f) g) W c Q <-> amrealE segs (ibind t (fun a => ibind (f a) g)) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q; cbn [ibind amrealE]; [img_try (tauto) | | img_try (tauto) | img_try (tauto)].
split; intros H.
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; img_apply (proj1 (IH _ f g _ _ Q)); img_exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. img_apply (proj1 (IH _ f g _ _ Q)). img_exact HR.
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; img_apply (proj2 (IH _ f g _ _ Q)); img_exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. img_apply (proj2 (IH _ f g _ _ Q)). img_exact HR.
Qed.
Lemma amreal_ibind_assoc {A B R} : forall (t : itree astate A) (f : A -> itree astate B) (g : B -> itree astate R) W c
(Q : R -> world segs -> config -> Prop),
amreal segs (ibind (ibind t f) g) W c Q <-> amreal segs (ibind t (fun a => ibind (f a) g)) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q; cbn [ibind amreal]; [img_try (tauto) | | img_try (tauto) | img_try (tauto)].
split; intros H.
- eapply SRr_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hd & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (H8 i Hi); destruct (Z.eqb (bit i) 1);
[img_apply (proj1 (IH _ f g _ _ Q)); img_exact H8 | img_apply (proj1 (amrealE_ibind_assoc _ f g _ _ Q)); img_exact H8]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. img_apply (proj1 (IH _ f g _ _ Q)). img_exact HR.
- eapply SRr_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hd & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (H8 i Hi); destruct (Z.eqb (bit i) 1);
[img_apply (proj2 (IH _ f g _ _ Q)); img_exact H8 | img_apply (proj2 (amrealE_ibind_assoc _ f g _ _ Q)); img_exact H8]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. img_apply (proj2 (IH _ f g _ _ Q)). img_exact HR.
Qed.
(* [comment removed for export] *)
Lemma amreal_ibind_ext {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amreal segs (f a) W1 c1 Q -> amreal segs (g a) W1 c1 Q) ->
(forall a W1 c1, amrealE segs (f a) W1 c1 Q -> amrealE segs (g a) W1 c1 Q) ->
amreal segs (ibind t f) W c Q -> amreal segs (ibind t g) W c Q.
Proof. intros. eapply amreal_ibind_ext2; eassumption. Qed.
Lemma amrealE_bind_assoc {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amrealE segs (bind (bind m1 m2) m3 s) W c Q -> amrealE segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj1 (amrealE_ibind_assoc _ _ _ _ _ _)) in H.
eapply amrealE_ibind_ext; [|img_try (img_exact H)]. intros [a s'] W1 c1 Ha. img_exact Ha.
Qed.
Lemma amreal_bind_assoc {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal segs (bind (bind m1 m2) m3 s) W c Q -> amreal segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj1 (amreal_ibind_assoc _ _ _ _ _ _)) in H.
eapply amreal_ibind_ext2; [| |img_try (img_exact H)]; intros [a s'] W1 c1 Ha; img_exact Ha.
Qed.
Lemma amrealE_bind_assoc' {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amrealE segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q -> amrealE segs (bind (bind m1 m2) m3 s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
img_apply (proj2 (amrealE_ibind_assoc _ _ _ _ _ _)).
eapply amrealE_ibind_ext; [|img_try (img_exact H)]. intros [a s'] W1 c1 Ha. img_exact Ha.
Qed.
Lemma amreal_bind_assoc' {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q -> amreal segs (bind (bind m1 m2) m3 s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
img_apply (proj2 (amreal_ibind_assoc _ _ _ _ _ _)).
eapply amreal_ibind_ext2; [| |img_try (img_exact H)]; intros [a s'] W1 c1 Ha; img_exact Ha.
Qed.
Lemma amrealE_apost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
apost t P -> amrealE segs t W c Q -> amrealE segs t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amrealE] in *.
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. split; [|img_try (img_exact HQ)]. img_apply (HP []). img_refl.
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> apost (k z) P).
{ intros z Hz tr a Hp. img_apply (HP ((q, z) :: tr)). cbn. split; [img_refl|]. split; [img_try (img_exact Hz) | img_try (img_exact Hp)]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; eapply IH; [img_try (img_exact (HPk _ (H3 i))) | img_try (img_exact (H8 i Hi))]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact (HPk _ Hz)) | img_try (img_exact HR)].
- img_exact H.
- img_exact I.
Qed.
Lemma amreal_apost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
apost t P -> amreal segs t W c Q -> amreal segs t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amreal] in *.
- eapply SRr_mono; [img_try (img_exact H)|]. intros W' c' _ HQ. split; [|img_try (img_exact HQ)]. img_apply (HP []). img_refl.
- eapply SRr_mono; [img_try (img_exact H)|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> apost (k z) P).
{ intros z Hz tr a Hp. img_apply (HP ((q, z) :: tr)). cbn. split; [img_refl|]. split; [img_try (img_exact Hz) | img_try (img_exact Hp)]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hd & H8); exists I, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (H8 i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [img_try (img_exact (HPk _ (H3 i))) | img_try (img_exact H8)] | eapply amrealE_apost; [img_try (img_exact (HPk _ (H3 i))) | img_try (img_exact H8)]]).
destruct HQ as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact (HPk _ Hz)) | img_try (img_exact HR)].
- img_exact H.
- img_exact I.
Qed.

End b.
