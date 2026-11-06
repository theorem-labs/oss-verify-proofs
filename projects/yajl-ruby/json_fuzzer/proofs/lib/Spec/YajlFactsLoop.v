(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode
     YajlParser YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma loop_pre_passes_left_pos : forall len h cx, loop_pre len h cx -> 1 <= passes_left len h.
Proof.
  intros len h cx [Hinv|(Hw & s & rest & Hst & He)]; unfold passes_left.
  - destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
    destruct (h_stack h) as [|s rest]; [contradiction|].
    rewrite (frames_ok_not_error _ _ Hfr). lia.
  - rewrite Hst, He. lia.
Qed.

Lemma loop_pre_used_pos : forall len h cx, loop_pre len h cx -> 0 < h_used h.
Proof.
  intros len h cx [Hinv|(Hw & s & rest & Hst & He)]; unfold h_used, zlength.
  - destruct Hinv as (_ & _ & _ & _ & (Hfr & _) & _ & _).
    destruct (h_stack h) as [|s rest]; [contradiction|]. cbn [length]. lia.
  - rewrite Hst. cbn [length]. lia.
Qed.

Lemma loop_pre_weak : forall len h cx, loop_pre len h cx -> weak_inv len h.
Proof. intros len h cx [Hinv|(Hw & _)]; [eapply hinv_weak; exact Hinv| exact Hw]. Qed.

(* [comment removed for export] *)
Lemma yparse_step_leaf_post : forall txt len h cx r,
  len = zlength txt -> len < 2^32 -> loop_pre len h cx ->
  yleaf (yparse_step jf_callbacks txt len h cx) r -> step_post len (h_bytesConsumed h) r.
Proof.
  intros txt len h cx r Hlen H32 [Hinv|(Hw & s & rest & Hst & He)] HL.
  - eapply ypost_yleaf; [apply yparse_step_post; eauto| exact HL].
  - unfold yparse_step in HL. rewrite (ybs_current_eq h s rest Hst) in HL. cbn [ybind] in HL.
    destruct s; try discriminate; cbn in HL; apply yleaf_ret_inv in HL; subst r; exact Hw.
Qed.

Lemma yparse_step_again_facts : forall txt len h cx h1 cx1,
  len = zlength txt -> len < 2^32 -> loop_pre len h cx ->
  yleaf (yparse_step jf_callbacks txt len h cx) (SR_again h1 cx1) ->
  loop_pre len h1 cx1 /\ 0 < h_used h1 /\ 1 <= passes_left len h1 < passes_left len h.
Proof.
  intros txt len h cx h1 cx1 Hlen H32 Hpre HL.
  pose proof (yparse_step_leaf_post _ _ _ _ _ Hlen H32 Hpre HL) as Hstep. cbn in Hstep.
  assert (Hpre1 : loop_pre len h1 cx1).
  { destruct Hstep as [[Hinv1 _]|Herr]; [left; exact Hinv1| right; exact Herr]. }
  split; [exact Hpre1|]. split; [eapply loop_pre_used_pos; exact Hpre1|].
  split; [eapply loop_pre_passes_left_pos; exact Hpre1|].
  (* [comment removed for export] *)
  destruct Hpre as [Hinv|(Hw & s & rest & Hst & He)].
  2:{ exfalso. unfold yparse_step in HL. rewrite (ybs_current_eq h s rest Hst) in HL. cbn [ybind] in HL.
      destruct s; try discriminate; cbn in HL; apply yleaf_ret_inv in HL; discriminate. }
  unfold passes_left.
  destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
  destruct (h_stack h) as [|s rest]; [contradiction|].
  rewrite (frames_ok_not_error _ _ Hfr).
  destruct Hstep as [[Hinv1 Hprog]|(Hw1 & s1 & rest1 & Hst1 & He1)].
  - destruct Hinv1 as (_ & Hoff1 & _ & _ & (Hfr1 & _) & _ & _).
    destruct (h_stack h1) as [|s1 rest1]; [contradiction|].
    rewrite (frames_ok_not_error _ _ Hfr1). lia.
  - rewrite Hst1, He1. lia.
Qed.

Lemma yparse_step_done_facts : forall txt len h cx st h1 cx1,
  len = zlength txt -> len < 2^32 -> loop_pre len h cx ->
  yleaf (yparse_step jf_callbacks txt len h cx) (SR_done st h1 cx1) -> weak_inv len h1.
Proof.
  intros txt len h cx st h1 cx1 Hlen H32 Hpre HL.
  exact (yparse_step_leaf_post _ _ _ _ _ Hlen H32 Hpre HL).
Qed.

(* [comment removed for export] *)
Lemma yparse_loop_leaf_done : forall txt len n h cx st h1 cx1,
  yleaf (yparse_step jf_callbacks txt len h cx) (SR_done st h1 cx1) ->
  yleaf (yparse_loop jf_callbacks txt len (S n) h cx) (st, h1, cx1).
Proof.
  intros txt len n h cx st h1 cx1 HL. cbn [yparse_loop].
  eapply yleaf_bind; [exact HL|]. cbn. apply yl_ret.
Qed.

Lemma yparse_loop_leaf_again : forall txt len n h cx h1 cx1 r,
  yleaf (yparse_step jf_callbacks txt len h cx) (SR_again h1 cx1) ->
  yleaf (yparse_loop jf_callbacks txt len n h1 cx1) r ->
  yleaf (yparse_loop jf_callbacks txt len (S n) h cx) r.
Proof.
  intros txt len n h cx h1 cx1 r HL HR. cbn [yparse_loop].
  eapply yleaf_bind; [exact HL|]. cbn. exact HR.
Qed.

Lemma yparse_loop_leaf_inv : forall txt len n h cx r,
  yleaf (yparse_loop jf_callbacks txt len (S n) h cx) r ->
  (exists st h1 cx1, r = (st, h1, cx1) /\ yleaf (yparse_step jf_callbacks txt len h cx) (SR_done st h1 cx1))
  \/ (exists h1 cx1, yleaf (yparse_step jf_callbacks txt len h cx) (SR_again h1 cx1)
                    /\ yleaf (yparse_loop jf_callbacks txt len n h1 cx1) r).
Proof.
  intros txt len n h cx r HL. cbn [yparse_loop] in HL.
  apply yleaf_bind_inv in HL. destruct HL as ([st h1 cx1|h1 cx1] & H1 & H2).
  - left. exists st, h1, cx1. cbn in H2. apply yleaf_ret_inv in H2. auto.
  - right. exists h1, cx1. auto.
Qed.

Lemma yparse_loop_zero : forall txt len h cx r, ~ yleaf (yparse_loop jf_callbacks txt len 0 h cx) r.
Proof. intros txt len h cx r HL. cbn in HL. exact (yleaf_abort_inv _ HL). Qed.

(* [comment removed for export] *)
Lemma yparse_loop_leaf_mono : forall txt len n n' h cx r,
  (n <= n')%nat -> yleaf (yparse_loop jf_callbacks txt len n h cx) r ->
  yleaf (yparse_loop jf_callbacks txt len n' h cx) r.
Proof.
  intros txt len n. induction n as [|n IH]; intros n' h cx r Hle HL.
  - exfalso. exact (yparse_loop_zero _ _ _ _ _ HL).
  - destruct n' as [|n']; [lia|].
    destruct (yparse_loop_leaf_inv _ _ _ _ _ _ HL) as [(st & h1 & cx1 & -> & HD)|(h1 & cx1 & HA & HR)].
    + apply yparse_loop_leaf_done. exact HD.
    + eapply yparse_loop_leaf_again; [exact HA|]. apply IH; [lia| exact HR].
Qed.

(* [comment removed for export] *)
Lemma ydo_parse_unfold : forall txt len h cx,
  ydo_parse jf_callbacks txt len h cx = yparse_loop jf_callbacks txt len (parse_fuel len) (h_set_off h 0) cx.
Proof. reflexivity. Qed.

Lemma ydo_parse_fuel : forall len h cx,
  0 <= len -> hinv len (h_set_off h 0) cx -> passes_left len (h_set_off h 0) <= Z.of_nat (parse_fuel len).
Proof.
  intros len h cx Hlen Hinv. unfold passes_left, parse_fuel.
  destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
  cbn [h_stack h_set_off h_bytesConsumed] in *.
  destruct (h_stack h) as [|s rest]; [contradiction|].
  rewrite (frames_ok_not_error _ _ Hfr). rewrite !Nat2Z.inj_succ, Z2Nat.id; lia.
Qed.

Lemma ydo_parse_loop_pre : forall len h cx, hinv len (h_set_off h 0) cx -> loop_pre len (h_set_off h 0) cx.
Proof. intros len h cx H. left. exact H. Qed.
