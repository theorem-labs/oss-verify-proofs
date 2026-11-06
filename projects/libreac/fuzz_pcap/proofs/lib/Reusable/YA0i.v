(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0i.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0i YK15 YK04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section b. Context {fx : YK11.FPState}.
Open Scope bv_scope.
Section c.
Variable segs : list Segment.
Definition AI (H : word -> bool) (A : list (Z * Z)) (md : Model) : Prop :=
H_off_segments segs H /\ A_wf A /\ lazy_cover H (m_vm_lazy md) A /\ MInv A md
/\ m_halted md = None.
Lemma AI_halted : forall H A md, AI H A md -> m_halted md = None.
Proof. intros H A md (_ & _ & _ & _ & Hh). exact Hh. Qed.
Lemma AI_MInv : forall H A md, AI H A md -> MInv A md.
Proof. intros H A md (_ & _ & _ & Hm & _). exact Hm. Qed.
Lemma AI_same : forall H A md md',
AI H A md -> same_but_materialized md md' -> MInv A md' -> AI H A md'.
Proof.
intros H A md md' (H1 & H2 & H3 & H4 & H5) Hs Hm.
pose proof (same_but_materialized_frame md md' Hs) as Hfr.
split; [exact H1|]. split; [exact H2|]. split.
- replace (m_vm_lazy md') with (m_vm_lazy md) by (symmetry; apply Hfr). exact H3.
- split; [exact Hm|]. replace (m_halted md') with (m_halted md) by (symmetry; apply Hfr). exact H5.
Qed.
Definition hsub (H' H : word -> bool) : Prop := forall a, H' a = true -> H a = true.
Lemma hsub_refl : forall H, hsub H H.
Proof. intros H a Ha. exact Ha. Qed.
Lemma hsub_trans : forall H1 H2 H3, hsub H1 H2 -> hsub H2 H3 -> hsub H1 H3.
Proof. intros H1 H2 H3 Ha Hb a Hx. apply Hb, Ha, Hx. Qed.
Lemma AI_hsub : forall H H' A md,
AI H A md -> hsub H' H ->
(forall w, H w = true -> H' w = false ->
page_in_ranges (page_base w) (m_vm_lazy md) = true ->
page_allowedb A (page_base w) = true) ->
AI H' A md.
Proof.
intros H H' A md (H1 & H2 & H3 & H4 & H5) Hsub Hnew.
split; [|split; [exact H2|split; [|split; [exact H4|exact H5]]]].
- intros a Ha. apply H1. apply Hsub. exact Ha.
- intros w Hl Hw. destruct (H w) eqn:Hw0.
+ exact (Hnew w Hw0 Hw Hl).
+ exact (H3 w Hl Hw0).
Qed.
Lemma page_allowedb_app : forall A1 A2 p,
page_allowedb (A1 ++ A2) p = page_allowedb A1 p || page_allowedb A2 p.
Proof. intros A1 A2 p. unfold page_allowedb. apply existsb_app. Qed.
Lemma A_bytes_app : forall A1 A2, A_bytes (A1 ++ A2) = (A_bytes A1 + A_bytes A2)%Z.
Proof. induction A1 as [|iv A1 IH]; intros A2; cbn; [reflexivity | rewrite IH; lia]. Qed.
Lemma AI_grow_A : forall H A A2 md,
AI H A md -> A_wf A2 ->
(eager_used md + A_bytes A2 + A_bytes A <= vm_limit (m_vmmaps md))%Z ->
AI H (A2 ++ A) md.
Proof.
intros H A A2 md (H1 & H2 & H3 & H4 & H5) Hwf Hb.
split; [exact H1|]. split; [apply Forall_app; split; assumption|]. split; [|split; [|exact H5]].
- intros w Hl Hw. rewrite page_allowedb_app, (H3 w Hl Hw). apply orb_true_r.
- destruct H4 as [N1 N2 N3 N4 N5]. constructor; try assumption.
+ intros p Hp. rewrite page_allowedb_app, (N3 p Hp). apply orb_true_r.
+ rewrite A_bytes_app. lia.
Qed.
Lemma AI_reset_A : forall H A A' md,
AI H A md -> A_wf A' ->
lazy_cover H (m_vm_lazy md) A' ->
(forall p, In p (m_vm_materialized md) -> page_allowedb A' p = true) ->
(eager_used md + A_bytes A' <= vm_limit (m_vmmaps md))%Z ->
AI H A' md.
Proof.
intros H A A' md (H1 & H2 & H3 & H4 & H5) Hwf Hcov Hal Hb.
split; [exact H1|]. split; [exact Hwf|]. split; [exact Hcov|]. split; [|exact H5].
destruct H4 as [N1 N2 N3 N4 N5]. constructor; try assumption.
Qed.
Lemma AI_transport : forall H A md md',
AI H A md ->
m_vm_materialized md' = m_vm_materialized md ->
m_vm_lazy md' = m_vm_lazy md ->
m_halted md' = None ->
(eager_used md' + A_bytes A <= vm_limit (m_vmmaps md'))%Z ->
AI H A md'.
Proof.
intros H A md md' (H1 & H2 & H3 & H4 & H5) Hm Hl Hh Hb.
split; [exact H1|]. split; [exact H2|]. split; [rewrite Hl; exact H3|].
split; [exact (MInv_transport A md md' H4 Hm Hl Hb) | exact Hh].
Qed.
Lemma AI_materialized_succ : forall H A md' accs,
H_off_segments segs H -> A_wf A ->
lazy_cover H (m_vm_lazy md') A -> MInv A md' -> m_halted md' = None ->
ranges_avoid H accs ->
AI H A (materialized_succ md' accs) /\ same_but_materialized md' (materialized_succ md' accs).
Proof.
intros H A md' accs HH Hwf Hcov Hinv Hh Hav.
destruct (materialize_restricted H A md' accs Hcov Hwf Hinv Hav) as (mat' & Hm & Hinv').
unfold materialized_succ. rewrite Hm.
pose proof (with_vm_backing_same md' mat') as Hsame.
split; [|exact Hsame].
apply (AI_same H A md'); [|exact Hsame|exact Hinv'].
split; [exact HH|]. split; [exact Hwf|]. split; [exact Hcov|]. split; [exact Hinv|exact Hh].
Qed.
End c.
End b.
Arguments AI segs H A md : clear implicits.
