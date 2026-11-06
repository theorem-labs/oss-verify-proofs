(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the FREE-HISTORY COUPLING.
   P8's top theorem (lib/Spec/PresetP8.v preset_room, no_null_preset) takes
     PresetRoom.fifo_ok (map PresetRoom.acct_size (H0 ++ hfrees_q (firstn i (hruns sm x os)))) (rs_quar s)
   (Spec/PresetRunQ.v's hfrees_q: the model's frees that enter the quarantine; comment updated by a Theorem Labs lane, 2026-10-30).
   The instance already proves everything about its own side: quar_bytes_ok_cf, quar_fifo_cf (the quarantine is a
   suffix of the free history), ck_n_acct_size and fifo_ok_acct_of_quar_fifo_cf (YGcfRoom.v). What is left is the
   ORDERING COUPLING: that the instance's accounted free history is, in order, H0 followed by the model's frees.
   That is the walk's obligation (h-pre-b1), so it gets ONE named predicate here instead of a restated obligation.
   cf_frees_follow is stated over a plain list of sizes, NOT over PresetRun's hev: the instance must not depend on
   the harness model. A caller instantiates mf := hfrees_q (firstn i (hruns sm x os)) and gets P8's premise verbatim
   from fifo_ok_of_frees_follow. No address, no event count. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG01cf YG00cf YGcfRoom.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The instance's accounted free history follows the model's: the requests of the chunks the instance has
   quarantined, in order, are H0 (what ran before the window) followed by mf (the model's frees in the window). *)
Definition cf_frees_follow (H0 mf : list Z) (hist : list chunk) : Prop := map ck_req hist = H0 ++ mf.

(* Every chunk of the history carries a non-negative request, so acct_size applies to it. *)
Definition cf_hist_ok (hist : list chunk) : Prop := Forall (fun k => 0 <= ck_req k) hist.

(* THE LEMMA: the coupling, the FIFO suffix and the request bound give P8's premise, at its own words. *)
Theorem fifo_ok_of_frees_follow : forall hist s H0 mf,
quar_fifo_cf hist s -> cf_hist_ok hist -> cf_frees_follow H0 mf hist ->
PresetRoom.fifo_ok (map PresetRoom.acct_size (H0 ++ mf)) (PresetRoom.rs_quar (room_of_cf s)).
Proof.
intros hist s H0 mf HQ HN HF. unfold cf_frees_follow in HF. rewrite <- HF.
exact (fifo_ok_acct_of_quar_fifo_cf hist s HQ HN).
Qed.

(* Start and steps, so a walk can carry the coupling instead of re-deriving it. *)
Lemma cf_frees_follow_init : cf_frees_follow [] [] [].
Proof. reflexivity. Qed.

Lemma cf_hist_ok_init : cf_hist_ok [].
Proof. constructor. Qed.

(* A malloc appends nothing to the history, so both parts are unchanged (quar_fifo_malloc_step carries the
   suffix). A free appends freed_cf s p, and the model's list grows by the same requests. *)
Lemma cf_frees_follow_free : forall H0 mf hist s p,
cf_frees_follow H0 mf hist -> cf_frees_follow H0 (mf ++ map ck_req (freed_cf s p)) (hist ++ freed_cf s p).
Proof.
intros H0 mf hist s p HF. unfold cf_frees_follow in *. rewrite map_app, HF, app_assoc. reflexivity.
Qed.

Section F. Context {ci : CfImg} {cp : CfParams}.

Lemma cf_hist_ok_free : forall U hist s p,
Wf_cf U s -> cf_hist_ok hist -> cf_hist_ok (hist ++ freed_cf s p).
Proof.
intros U hist s p W HN. unfold cf_hist_ok in *. apply Forall_app. split; [exact HN|].
exact (freed_cf_req_cf U s p W).
Qed.

(* The free step in one piece: the coupling, the history bound and the FIFO suffix all move together. *)
Lemma cf_frees_step_free : forall U H0 mf hist s p s' P,
Wf_cf U s -> quar_fifo_cf hist s -> cf_hist_ok hist -> cf_frees_follow H0 mf hist ->
q_fifo s ++ freed_cf s p = flat_map b_items P ++ q_fifo s' ->
quar_fifo_cf (hist ++ freed_cf s p) s' /\ cf_hist_ok (hist ++ freed_cf s p) /\
cf_frees_follow H0 (mf ++ map ck_req (freed_cf s p)) (hist ++ freed_cf s p).
Proof.
intros U H0 mf hist s p s' P W HQ HN HF E.
split; [exact (quar_fifo_free_step hist s p s' P HQ E)|].
split; [exact (cf_hist_ok_free U hist s p W HN) | exact (cf_frees_follow_free H0 mf hist s p HF)].
Qed.

End F.
