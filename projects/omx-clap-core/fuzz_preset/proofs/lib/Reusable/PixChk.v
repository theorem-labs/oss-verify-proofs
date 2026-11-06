(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (the producer check of the index-keyed set): lemmas of the dead set dead_shadow_new at the kit's
   INDEX-keyed body (YGcfRehidePost.v; core ruling 2026-10-30 18:00Z: the name stays, the body is the kit's, no second name).
   Ported from cgif/cgif_file_fuzzer lib/PixChk.v (file sha256 2e88698b2c8a; donor not released; module paths
   cgif -> preset Reusable; its _ix names now plain). (1) the kit's emptiness lemma and the provers of
   dead_shadow_new_off's premise are in YGcfRehidePost.v (core 33db28e0c9a; live_slots_placed_of_wf / _of_wf_cf); (2) the walk-level composition (rec_live, the backward liveness
   of each slot index, with YGcfRecStep.rec_step) and the two steps that keep rec_live; (3) the assumption audit of the
   restated producers. That donor file's DMrcRh / DMrcRhOk / DMrcCf parts are not ported: preset has no copy of those
   cgif-image walk files. Generic: no image, no address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0k YG04 YG06 YG0n YGcfRehidePost YGcfRecStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05 YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf.
Import ListNotations.
Local Open Scope Z_scope.

Section ix. Context {rc : YM05.RunCeil}.

(* ---- (1) dead_shadow_new_same_secs_empty and the premise of dead_shadow_new_off (live_slots_placed, with its
   provers live_slots_placed_of_wf / _of_wf_cf) are in YGcfRehidePost.v (core 33db28e0c9a). ---- *)

(* ---- (2) The walk-level producer: one call's set inside the walk's set (YGcfRecStep.v:1-4's composition). ---- *)
(* At the index-keyed body the extent conjunct of rec_step does not give that slot r was live at S0 (an extent value at
   S1 may be another slot's at S0: the alias). The step needs the backward liveness of each slot index instead. *)
Definition rec_live (S S' : astate) : Prop :=
  forall r sm', nth_error (st_secs S') r = Some sm' -> sm_live sm' = true ->
    exists sm, nth_error (st_secs S) r = Some sm /\ sm_live sm = true /\ sm_len sm = sm_len sm'.

Lemma rec_live_refl : forall S, rec_live S S.
Proof. intros S r sm' Hn Hl. exists sm'. split; [exact Hn|]. split; [exact Hl | reflexivity]. Qed.

Lemma rec_live_trans : forall S1 S2 S3, rec_live S1 S2 -> rec_live S2 S3 -> rec_live S1 S3.
Proof.
  intros S1 S2 S3 H12 H23 r sm3 Hn3 Hl3. destruct (H23 r sm3 Hn3 Hl3) as (sm2 & Hn2 & Hl2 & E2).
  destruct (H12 r sm2 Hn2 Hl2) as (sm1 & Hn1 & Hl1 & E1). exists sm1. split; [exact Hn1|]. split; [exact Hl1 | lia].
Qed.

Lemma dead_shadow_new_compose : forall ly S0 S1 S2 S3 a, rec_live S0 S1 -> rec_step ly S2 S3 ->
  dead_shadow_new ly S1 S2 a -> dead_shadow_new ly S0 S3 a.
Proof.
  intros ly S0 S1 S2 S3 a L01 [D23 _] (r & sm & sm0 & Hd & Hn0 & Hl0 & Hlen & Ha).
  destruct (D23 r sm Hd) as (sm' & Hd' & El).
  destruct (L01 r sm0 Hn0 Hl0) as (sm1 & Hn1 & Hl1 & E1).
  exists r, sm', sm1. rewrite El. split; [exact Hd'|]. split; [exact Hn1|]. split; [exact Hl1|]. split; [lia | exact Ha].
Qed.

(* The two steps YGcfRecStep covers keep rec_live (the same proofs as cache_dealloc_rec_step / recycle_chunk_rec_step). *)
Lemma cache_dealloc_rec_live : forall z X, apost (cache_dealloc kBatchClass z X) (fun r => rec_live X (snd r)).
Proof.
  intros z X. eapply apost_mono; [|apply (cache_dealloc_sc (st_secs X) (st_chunks X)); split; reflexivity].
  intros r [E1 _] r' sm' Hn Hl. rewrite E1 in Hn. exists sm'. split; [exact Hn|]. split; [exact Hl | reflexivity].
Qed.

Lemma recycle_chunk_rec_live : forall k X, apost (recycle_chunk k X) (fun r => rec_live X (snd r)).
Proof.
intros k X. unfold recycle_chunk.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
set (X1 := set_chunks (del_chunk (st_chunks X) (ck_beg k)) X).
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; [apply apost_fail | | | apply apost_fail].
- eapply apost_mono; [|apply (cache_dealloc_sc (st_secs X1) (st_chunks X1)); split; reflexivity].
  intros r0 [E1 _] r' sm' Hn Hl. rewrite E1 in Hn. exists sm'. split; [exact Hn|]. split; [exact Hl | reflexivity].
- unfold sec_dealloc. apply apost_bind. apply apost_get. cbn [fst snd].
  change (st_secs X1) with (st_secs X). change (st_sec_arr X1) with (st_sec_arr X).
  destruct (nth_error (st_secs X) r) as [sm|] eqn:En; [|apply apost_fail].
  destruct (index_of (st_sec_arr X) r 0) as [i|]; [|apply apost_fail].
  apply apost_bind. apply (apost_mono _ (fun r0 => snd r0 = X1)).
  2:{ apply apost_if; intros _; [|apply apost_ret; reflexivity].
      apply apost_bind. apply apost_askz. intros z0 _. cbn [fst snd].
      apply apost_if; intros _; [apply apost_ret; reflexivity | apply apost_spin]. }
  intros [u1 s1] Hs. cbn [fst snd] in Hs |- *. subst s1.
  apply apost_bind. apply apost_askz. intros z1 _. cbn [fst snd].
  apply apost_modify. cbn [snd]. unfold X1 in *.
  unfold rec_live. cbn [st_secs st_chunks st_sec_arr set_chunks set_sec_arr set_secs] in *.
  intros r' sm' Hn Hl. destruct (Nat.eq_dec r' r) as [->|Ne].
  + assert (Lt : (r < length (st_secs X))%nat) by (apply nth_error_Some; rewrite En; discriminate).
    rewrite (nth_error_lupd_same _ _ _ Lt) in Hn. injection Hn as <-. discriminate Hl.
  + rewrite (nth_error_lupd_other _ _ _ _ (not_eq_sym Ne)) in Hn. exists sm'. split; [exact Hn|]. split; [exact Hl | reflexivity].
Qed.
End ix.

(* ---- (3) Assumption audit of the restated producers (their text is unchanged; their posts now read the index key). ---- *)
Print Assumptions YGcfRehidePost.acall_post_cf_rh_of.
Print Assumptions YGcfRehidePost.acall_post_x_rh_of.
Print Assumptions YGcfRehidePost.dealloc_post_rh_of.
Print Assumptions YGcfRehidePost.dealloc_post_raw_rh_of.
Print Assumptions YG0dcfR.afree_realizes_cf_rh_of.
Print Assumptions YGcfRehidePost.live_slots_placed_of_wf.
Print Assumptions YGcfRehidePost.live_slots_placed_of_wf_cf.
Print Assumptions YGcfRehidePost.dead_shadow_new_same_secs_empty.
Print Assumptions dead_shadow_new_compose.
Print Assumptions recycle_chunk_rec_live.
Print Assumptions cache_dealloc_rec_live.
