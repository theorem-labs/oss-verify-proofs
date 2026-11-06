(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition not_frame (lo v : Z) : Prop := v <= lo \/ v mod 8 <> 0 \/ 2 ^ 63 <= v.

Lemma not_frame_stop : forall lo v f, not_frame lo v -> lo <= f -> fp_stop f v.
Proof. intros lo v f [H|[H|H]] Hf; unfold fp_stop; [left; lia | right; left; exact H | right; right; exact H]. Qed.

Lemma unwind_ch_nf : forall (m : mem) (ra s0 sp : word) lo,
In (bv_unsigned ra) ALLOC_RAS -> not_frame lo (bv_unsigned s0) -> lo <= bv_unsigned sp -> unwind_ch m ra s0 sp.
Proof.
intros m ra s0 sp lo Hra Hnf Hlo. exists []. split.
- unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists (bv_unsigned ra). split; [reflexivity | exact Hra].
- cbn [uw_chain]. exact (not_frame_stop lo _ _ Hnf Hlo).
Qed.

Lemma unwind_ch_of : forall (m : mem) (ra s0 sp : word) ras,
In (bv_unsigned ra :: ras) SITE_TRACES -> uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> unwind_ch m ra s0 sp.
Proof. intros m ra s0 sp ras H1 H2. exists ras. split; assumption. Qed.

Lemma uw_chain_sp : forall TOPB (m : mem) f f' fp r ras, uw_chain TOPB m f fp (r :: ras) -> f' <= f -> uw_chain TOPB m f' fp (r :: ras).
Proof. intros TOPB m f f' fp r ras (H1 & H2 & H3 & H4) Hf. cbn [uw_chain]. split; [lia|]. split; [exact H2|]. split; [exact H3 | exact H4]. Qed.

Lemma uw_chain_nil_nf : forall TOPB (m : mem) lo f v, not_frame lo v -> lo <= f -> uw_chain TOPB m f v [].
Proof. intros TOPB m lo f v H Hf. cbn [uw_chain]. exact (not_frame_stop lo v f H Hf). Qed.

Lemma uw_chain_munch : forall TOPB W (m m' : mem) ras f fp,
uw_chain TOPB m f fp ras -> munch W m m' -> wmono bsegs m m' ->
(forall a, f <= a -> a + 16 <= TOPB -> disjoint_from W a 16) -> uw_chain TOPB m' f fp ras.
Proof.
intros TOPB W m m' ras. induction ras as [|r ras IH]; intros f fp HU MU WM HW; [exact HU|].
cbn [uw_chain] in *. destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact Hfp'|]. split.
- apply (rw_cells_transport bsegs W m m' _ _ HC MU WM). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. apply HW; lia.
- apply (IH fp fp' HU MU WM). intros a Ha Ha'. apply HW; lia.
Qed.

Lemma below_disjoint : forall (W : list ivl) f, Forall (fun iv => snd iv <= f) W -> forall a, f <= a -> disjoint_from W a 16.
Proof.
induction W as [|[lo hi] W IH]; intros f HF a Ha; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HF as [H1 HF]. cbn [snd] in H1. split; [right; lia | exact (IH f HF a Ha)].
Qed.

Lemma uw_chain_push : forall TOPB (m : mem) f fp v r ras,
f + 16 <= fp -> fp mod 8 = 0 -> fp <= TOPB -> 0 <= v < 2 ^ 64 ->
rw_cells bsegs m (fp + -16) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 r)] -> uw_chain TOPB m fp v ras -> uw_chain TOPB m f fp (r :: ras).
Proof. intros TOPB m f fp v r ras H1 H2 H3 Hv HC HU. cbn [uw_chain]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists v. split; [exact Hv|]. split; assumption. Qed.

Lemma uw_chain_base : forall TOPB (m : mem) fp v, (v <= fp \/ v mod 8 <> 0 \/ 2 ^ 63 <= v) -> uw_chain TOPB m fp v [].
Proof. intros TOPB m fp v H. cbn [uw_chain]. exact H. Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition not_frame (lo v : Z) : Prop := v <= lo \/ v mod 8 <> 0 \/ 2 ^ 63 <= v.

Lemma not_frame_stop : forall lo v f, not_frame lo v -> lo <= f -> fp_stop f v.
Proof. intros lo v f [H|[H|H]] Hf; unfold fp_stop; [left; lia | right; left; exact H | right; right; exact H]. Qed.

Lemma unwind_ch_nf : forall (m : mem) (ra s0 sp : word) lo,
In (bv_unsigned ra) ALLOC_RAS -> not_frame lo (bv_unsigned s0) -> lo <= bv_unsigned sp -> unwind_ch m ra s0 sp.
Proof.
intros m ra s0 sp lo Hra Hnf Hlo. exists []. split.
- unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists (bv_unsigned ra). split; [reflexivity | exact Hra].
- cbn [uw_chain]. exact (not_frame_stop lo _ _ Hnf Hlo).
Qed.

Lemma unwind_ch_of : forall (m : mem) (ra s0 sp : word) ras,
In (bv_unsigned ra :: ras) SITE_TRACES -> uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> unwind_ch m ra s0 sp.
Proof. intros m ra s0 sp ras H1 H2. exists ras. split; assumption. Qed.

Lemma uw_chain_sp : forall TOPB (m : mem) f f' fp r ras, uw_chain TOPB m f fp (r :: ras) -> f' <= f -> uw_chain TOPB m f' fp (r :: ras).
Proof. intros TOPB m f f' fp r ras (H1 & H2 & H3 & H4) Hf. cbn [uw_chain]. split; [lia|]. split; [exact H2|]. split; [exact H3 | exact H4]. Qed.

Lemma uw_chain_nil_nf : forall TOPB (m : mem) lo f v, not_frame lo v -> lo <= f -> uw_chain TOPB m f v [].
Proof. intros TOPB m lo f v H Hf. cbn [uw_chain]. exact (not_frame_stop lo v f H Hf). Qed.

Lemma uw_chain_munch : forall TOPB W (m m' : mem) ras f fp,
uw_chain TOPB m f fp ras -> munch W m m' -> wmono asegs m m' ->
(forall a, f <= a -> a + 16 <= TOPB -> disjoint_from W a 16) -> uw_chain TOPB m' f fp ras.
Proof.
intros TOPB W m m' ras. induction ras as [|r ras IH]; intros f fp HU MU WM HW; [exact HU|].
cbn [uw_chain] in *. destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact Hfp'|]. split.
- apply (rw_cells_transport asegs W m m' _ _ HC MU WM). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. apply HW; lia.
- apply (IH fp fp' HU MU WM). intros a Ha Ha'. apply HW; lia.
Qed.

Lemma below_disjoint : forall (W : list ivl) f, Forall (fun iv => snd iv <= f) W -> forall a, f <= a -> disjoint_from W a 16.
Proof.
induction W as [|[lo hi] W IH]; intros f HF a Ha; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HF as [H1 HF]. cbn [snd] in H1. split; [right; lia | exact (IH f HF a Ha)].
Qed.

Lemma uw_chain_push : forall TOPB (m : mem) f fp v r ras,
f + 16 <= fp -> fp mod 8 = 0 -> fp <= TOPB -> 0 <= v < 2 ^ 64 ->
rw_cells asegs m (fp + -16) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 r)] -> uw_chain TOPB m fp v ras -> uw_chain TOPB m f fp (r :: ras).
Proof. intros TOPB m f fp v r ras H1 H2 H3 Hv HC HU. cbn [uw_chain]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists v. split; [exact Hv|]. split; assumption. Qed.

Lemma uw_chain_base : forall TOPB (m : mem) fp v, (v <= fp \/ v mod 8 <> 0 \/ 2 ^ 63 <= v) -> uw_chain TOPB m fp v [].
Proof. intros TOPB m fp v H. cbn [uw_chain]. exact H. Qed.
