(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c (a Theorem Labs lane's walk): the ROOM part of the walk's cuts in the
   post-implication form of the #102 reading texts (kit f97c8b2f046b: lib/A/PRH_FnParse.v tparse_value_specX,
   PRH_FnReader.v tparse_string_specX, PRH_FnAlloc.v tfuzz_malloc_specX). A text's post states, over its own trace's
   model events evs, (1) the room's live list moves as the events say,
   `Permutation (rs_live (room_of_cf S')) (hlive_from (rs_live (room_of_cf S)) evs)`, and (2) the run position moves by
   them, `forall sm x os i H0 hist, iface_room_pos .. i .. S -> prh_run_at sm x os i evs ->
   exists hist', iface_room_pos .. (i + length evs) .. S'`. rp_post is the two together; rp_keep is what a step with
   no model event keeps (the live list equal, the position kept). The arms of parse_value compose them: no event on the
   path (rp_nil), one callee whose events are the value's (rp_call), fuzz_malloc's two outcomes (rp_num).
   Model lemmas only; rule 24: no function proved. No numeral. *)
From Stdlib Require Import ZArith List Arith Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRoomPos PresetRoomPosKeep
  PresetReqAt PresetRun PjGrammar.
From Stdlib Require Import List.
Import ListNotations.

#[local] Notation live S := (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).

(* the run position moves by the events evs from S to S' (a text's post conjunct, verbatim) *)
Definition rp_pos (evs : list PresetReqAt.hev) (S S' : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i evs ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length evs)%nat H0 hist' S'.

(* the room post of a value trace tr: the live list and the position move by rd_hevs tr *)
Definition rp_post (tr : list PjGrammar.ev) (S S' : astate) : Prop :=
  Permutation (live S') (PresetReqAt.hlive_from (live S) (PresetReqAt.rd_hevs tr)) /\
  rp_pos (PresetReqAt.rd_hevs tr) S S'.

(* a step with no model event: the live list is the same and the position is kept *)
Definition rp_keep (S S' : astate) : Prop :=
  live S' = live S /\
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     exists hist', PresetRoomPos.iface_room_pos sm x os i H0 hist' S').

Lemma rp_keep_refl : forall S, rp_keep S S.
Proof. intros S. split; [reflexivity|]. intros sm x os i H0 hist P. exists hist. exact P. Qed.

Lemma rp_keep_eq : forall S S', S' = S -> rp_keep S S'.
Proof. intros S S' E. subst. apply rp_keep_refl. Qed.

Lemma rp_keep_trans : forall S1 S2 S3, rp_keep S1 S2 -> rp_keep S2 S3 -> rp_keep S1 S3.
Proof.
  intros S1 S2 S3 [L1 K1] [L2 K2]. split; [rewrite L2; exact L1|].
  intros sm x os i H0 hist P. destruct (K1 _ _ _ _ _ _ P) as [h P1]. exact (K2 _ _ _ _ _ _ P1).
Qed.

(* the fake-frame take (__asan_stack_malloc_0's post S2 = set_fs f S) and its release (stack_free_state) *)
Lemma rp_keep_set_fs : forall S f, rp_keep S (set_fs f S).
Proof.
  intros S f. split; [reflexivity|].
  intros sm x os i H0 hist P. exists hist. exact (PresetRoomPosKeep.room_pos_set_fs _ _ _ _ _ _ _ _ P).
Qed.

Lemma rp_keep_stack_free : forall S c p, rp_keep S (stack_free_state c p S).
Proof.
  intros S c p. split; [reflexivity|].
  intros sm x os i H0 hist P. exists hist. exact (PresetRoomPosKeep.room_pos_stack_free _ _ _ _ _ _ _ _ _ P).
Qed.

(* the count premises read the live list only, so a keep carries them *)
Lemma rp_keep_pkR : forall S S' f es, rp_keep S S' -> PresetRun.pkR f (live S') es = PresetRun.pkR f (live S) es.
Proof. intros S S' f es [L _]. rewrite L. reflexivity. Qed.

Lemma rp_keep_cnt : forall S S' f, rp_keep S S' -> PresetReqAt.cnt f (live S') = PresetReqAt.cnt f (live S).
Proof. intros S S' f [L _]. rewrite L. reflexivity. Qed.

(* p >= end and the literal arm: no model event on the path *)
Lemma rp_nil : forall tr S S', PresetReqAt.rd_hevs tr = [] -> rp_keep S S' -> rp_post tr S S'.
Proof.
  intros tr S S' E [L K]. unfold rp_post. rewrite E. cbn [PresetReqAt.hlive_from fold_left]. split.
  - rewrite L. apply Permutation_refl.
  - intros sm x os i H0 hist P _. cbn [length]. rewrite Nat.add_0_r. exact (K _ _ _ _ _ _ P).
Qed.

(* the string / items arm: entry -> call state kept, the callee's post over its events evs (the value's events),
   call return -> exit kept *)
Lemma rp_call : forall tr evs S Sc Sc' S',
  PresetReqAt.rd_hevs tr = evs -> rp_keep S Sc ->
  Permutation (live Sc') (PresetReqAt.hlive_from (live Sc) evs) -> rp_pos evs Sc Sc' ->
  rp_keep Sc' S' -> rp_post tr S S'.
Proof.
  intros tr evs S Sc Sc' S' E [L1 K1] HL HP [L2 K2]. unfold rp_post. rewrite E. split.
  - rewrite L2, <- L1. exact HL.
  - intros sm x os i H0 hist P R. destruct (K1 _ _ _ _ _ _ P) as [h1 P1].
    destruct (HP _ _ _ _ _ _ P1 R) as [h2 P2]. exact (K2 _ _ _ _ _ _ P2).
Qed.

(* a room post followed by a keep (the exit's fake-frame release) *)
Lemma rp_post_keep : forall tr S Sc S', rp_post tr S Sc -> rp_keep Sc S' -> rp_post tr S S'.
Proof.
  intros tr S Sc S' [HL HP] [L2 K2]. split.
  - rewrite L2. exact HL.
  - intros sm x os i H0 hist P R. destruct (HP _ _ _ _ _ _ P R) as [h1 P1]. exact (K2 _ _ _ _ _ _ P1).
Qed.

(* the number arm: fuzz_malloc's two outcomes at its call state Sc (res = 0: the position kept, no event, the live
   list unchanged; res <> 0: one event e, the request's HMal, and the live list moved by it), then strtod / the stores
   / the release keep *)
Lemma rp_num : forall (res : Z) e tr S Sc Sc' S',
  (res = 0%Z -> PresetReqAt.rd_hevs tr = []) -> (res <> 0%Z -> PresetReqAt.rd_hevs tr = [e]) ->
  rp_keep S Sc ->
  (res = 0%Z -> live Sc' = live Sc) -> (res = 0%Z -> rp_pos [] Sc Sc') ->
  (res <> 0%Z -> Permutation (live Sc') (PresetReqAt.hlive_from (live Sc) [e])) -> (res <> 0%Z -> rp_pos [e] Sc Sc') ->
  rp_keep Sc' S' -> rp_post tr S S'.
Proof.
  intros res e tr S Sc Sc' S' E0 E1 K1 L0 P0 L1 P1 K2.
  destruct (Z.eq_dec res 0%Z) as [Z0|Z0].
  - apply (rp_call tr [] S Sc Sc' S' (E0 Z0) K1); [|exact (P0 Z0)|exact K2].
    rewrite (L0 Z0). cbn [PresetReqAt.hlive_from fold_left]. apply Permutation_refl.
  - exact (rp_call tr [e] S Sc Sc' S' (E1 Z0) K1 (L1 Z0) (P1 Z0) K2).
Qed.

Print Assumptions rp_num.
