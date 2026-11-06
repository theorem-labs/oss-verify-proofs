(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the MODEL LAWS record.
   cgif's YG0u.v exports malloc_gen_ns (:21) and malloc_ok_ns (:199), and cgif's model_laws record
   (YG0d.v:514-529) is assembled in YG05.v (model_laws_ok :139). Their cf forms:
   - malloc_gen_ns: malloc_gen_cf (YG07cf.v) carries its `fst r = PNull -> ...` conjunct, as a disjunction
     with the class-full arm, which returns PNull with no refused request.
   - malloc_ok_ns (cgif's ml_malloc_ns): its cf form ml_malloc_ns_cf is stated in apath / gflag form in
     YGcfPath.v (lane C), not here.
   - model_laws (YG0d.v:514): model_laws_cf below. Its event premises `st_nev s < EV_MAX` (:515, :517) are
     gone; the call premises are the instance's live-state ones (secondary count, ERRB_ROOM,
     batch_room_cf). ml_malloc_big / ml_free_big (:523-526) are dropped: they take regime_big, whose caps
     this instance breaks. ml_malloc_ns (:527) is lane C's, as above.
   free_post_ycf is YG03cf.v's (cgif's free_post with Wf_cf); free_cf's law is YG03dcf.v's ml_free_cf. The record's
   fields carry the prefix mlr_, so that none of them is named like that theorem.
   cgif's YG0u.v / YG0d.v / YG05.v are NOT edited. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfTok.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG05cf YG07cf YG03cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

Section LAWS.
Context {cp : CfParams} {ci : CfImg}.

Record model_laws_cf (U : Univ) : Prop := {
mlr_malloc_cf : forall s n tr, Wf_cf U s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max -> ERRB_ROOM s -> YG00cf.batch_room_cf s ->
atok_cf true (malloc_cf n tr s) (malloc_post_cf U s n);
mlr_free_cf : forall s p n tr, Wf_cf U s -> YG00cf.batch_room_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok_cf true (free_cf p tr s) (free_post_ycf U s p n);
mlr_stack_malloc_cf : forall s cid, Wf_cf U s -> 0 <= cid <= 10 -> atok_cf true (stack_malloc cid s) (stack_malloc_post_cf U s cid);
mlr_stack_malloc_progress_cf : forall s cid, Wf_cf U s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s');
mlr_stack_free_cf : forall s cid pos, Wf_cf U s -> In (cid, pos) (frames s) -> stack_free_post_cf U s cid pos
}.

(* cgif's model_laws_ok (YG05.v:139), in two steps. model_laws_cf_of_free takes the free law as its hypothesis
   HF, with exactly the field's statement; every other field is proved here (malloc: YG07cf.v; the fake stack:
   YG05cf.v). model_laws_cf_ok discharges HF with YG03dcf.v's ml_free_cf. *)
Theorem model_laws_cf_of_free : forall U, universe_ok U ->
(forall s p n tr, Wf_cf U s -> YG00cf.batch_room_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok_cf true (free_cf p tr s) (free_post_ycf U s p n)) ->
model_laws_cf U.
Proof.
intros U HU HF. constructor.
- intros s n tr W Hn Hlive Htr HS HR H24. exact (malloc_ok_cf U s n tr HU W Hn Hlive Htr HS HR H24).
- exact HF.
- intros s cid W Hc. apply atok_cf_of_atok. exact (stack_malloc_ok_cf U s cid W Hc).
- intros s cid W Hc Hcnt. exact (stack_malloc_progress_cf U s cid W Hc Hcnt).
- intros s cid pos W Hin. exact (stack_free_ok_cf U s cid pos W Hin).
Qed.

Theorem model_laws_cf_ok : forall U, universe_ok U -> model_laws_cf U.
Proof.
intros U HU. apply model_laws_cf_of_free; [exact HU|].
intros s p n tr W Hr Hp Htr. eapply YG03dcf.ml_free_cf; eassumption.
Qed.
End LAWS.
