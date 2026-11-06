(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfk.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK18 YK0j YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Variable segs : list Segment.
Lemma amreal_ibind_ext {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amreal segs (f a) W1 c1 Q -> amreal segs (g a) W1 c1 Q) ->
amreal segs (ibind t f) W c Q -> amreal segs (ibind t g) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q Hfg H; cbn [ibind amreal] in *.
- exact (Hfg a W c H).
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact Hfg | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact Hfg | exact HR].
- exact H.
- exact I.
Qed.
Lemma amreal_ibind_assoc {A B R} : forall (t : itree astate A) (f : A -> itree astate B) (g : B -> itree astate R) W c
(Q : R -> world segs -> config -> Prop),
amreal segs (ibind (ibind t f) g) W c Q <-> amreal segs (ibind t (fun a => ibind (f a) g)) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q; cbn [ibind amreal]; [tauto | | tauto | tauto].
split; intros H.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply (proj1 (IH _ f g _ _ Q)); exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply (proj1 (IH _ f g _ _ Q)). exact HR.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply (proj2 (IH _ f g _ _ Q)); exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply (proj2 (IH _ f g _ _ Q)). exact HR.
Qed.
Lemma amreal_bind_assoc {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal segs (bind (bind m1 m2) m3 s) W c Q -> amreal segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj1 (amreal_ibind_assoc _ _ _ _ _ _)) in H.
eapply amreal_ibind_ext; [|exact H]. intros [a s'] W1 c1 Ha. exact Ha.
Qed.
Lemma amreal_bind_assoc' {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal segs (bind m1 (fun a => bind (m2 a) m3) s) W c Q -> amreal segs (bind (bind m1 m2) m3 s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj2 (amreal_ibind_assoc _ _ _ _ _ _)).
eapply amreal_ibind_ext; [|exact H]. intros [a s'] W1 c1 Ha. exact Ha.
Qed.
Lemma amreal_apost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
apost t P -> amreal segs t W c Q -> amreal segs t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amreal] in *.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. split; [|exact HQ]. apply (HP []). reflexivity.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> apost (k z) P).
{ intros z Hz tr a Hp. apply (HP ((q, z) :: tr)). cbn. split; [reflexivity|]. split; [exact Hz | exact Hp]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (HPk _ (H3 i)) | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact (HPk _ Hz) | exact HR].
- exact H.
- exact I.
Qed.
Lemma amreal_apostg {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
(forall tr r, apath t tr r -> gflag tr = true -> P r) -> amreal segs t W c Q -> amreal segs t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amreal] in *.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. split; [|exact HQ]. apply (HP []); reflexivity.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> progz q z = true -> forall tr a, apath (k z) tr a -> gflag tr = true -> P a).
{ intros z Hz Hpz tr a Hp Hg. apply (HP ((q, z) :: tr)); cbn; [split; [reflexivity|]; split; [exact Hz | exact Hp] | rewrite Hpz, Hg; reflexivity]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (HPk _ (H3 i) ltac:(rewrite (H6 i Hi); reflexivity)) | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact (HPk _ Hz eq_refl) | exact HR].
- exact H.
- exact I.
Qed.
End b.
