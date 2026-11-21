(** * ZReproQ6I — iterate/loop toolkit and mode dispatchers.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).  Extracted
    from the body-walk file so the LEN-chain shares it: composition of
    [inf_iter]/[inf_loop], first-step aliasing (two states whose next
    step is THE SAME step value share every iterate/loop of positive
    index — the fallthrough-call idiom), and the one-line [inf_step]
    dispatch reductions per mode.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0E.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma inf_iter_add : forall k1 k2 c q q1,
  inf_iter k1 c q = Some q1 ->
  inf_iter (k1 + k2) c q = inf_iter k2 c q1.
Proof.
  induction k1 as [|k1 IH]; intros k2 c q q1 H.
  - cbn in H. injection H as <-. reflexivity.
  - replace (S k1 + k2)%nat with (S (k1 + k2))%nat by lia.
    cbn [inf_iter] in H |- *.
    destruct (inf_step c q) as [q'| | | |]; try discriminate.
    now apply IH.
Qed.

Lemma inf_loop_after_iter : forall k c q q1 n r,
  inf_iter k c q = Some q1 ->
  inf_loop n c q1 = Some r ->
  inf_loop (k + n) c q = Some r.
Proof.
  induction k as [|k IH]; intros c q q1 n r HI HL.
  - cbn in HI. injection HI as <-. exact HL.
  - replace (S k + n)%nat with (S (k + n))%nat by lia.
    cbn [inf_iter] in HI. cbn [inf_loop].
    destruct (inf_step c q) as [q'| | | |]; try discriminate.
    now apply (IH c q' q1).
Qed.

Lemma inf_iter_one : forall c q q',
  inf_step c q = InfCont q' -> inf_iter 1 c q = Some q'.
Proof. intros c q q' H. cbn [inf_iter]. now rewrite H. Qed.

Lemma inf_loop_one_exit : forall c q r,
  inf_step c q = r ->
  (match r with InfCont _ => False | _ => True end) ->
  inf_loop 1 c q = Some r.
Proof.
  intros c q r H HX. cbn [inf_loop]. rewrite H.
  destruct r; try reflexivity. contradiction.
Qed.

Lemma inf_iter_alias_S : forall c a b k r,
  inf_step c a = inf_step c b ->
  inf_iter (S k) c b = Some r ->
  inf_iter (S k) c a = Some r.
Proof.
  intros c a b k r HE H. cbn [inf_iter] in *. now rewrite HE.
Qed.

Lemma inf_loop_alias_S : forall c a b n r,
  inf_step c a = inf_step c b ->
  inf_loop (S n) c b = Some r ->
  inf_loop (S n) c a = Some r.
Proof.
  intros c a b n r HE H. cbn [inf_loop] in *. now rewrite HE.
Qed.

(** The dispatch reductions. *)
Lemma zr_step_at_type : forall c q,
  zr_cflush_ok c ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  inf_step c q = inf_TYPEDO c q.
Proof.
  intros c q Hok Hm.
  unfold inf_step, q_mode. rewrite Hm.
  unfold inf_TYPE.
  now rewrite (zr_eqb_nB c Hok), (zr_eqb_nT c Hok).
Qed.

Lemma zr_step_at_stored : forall c q,
  h_mode (s_hdr (q_st q)) = M_STORED ->
  inf_step c q = inf_STORED c q.
Proof.
  intros c q Hm. unfold inf_step, q_mode. now rewrite Hm.
Qed.

Lemma zr_step_at_copy : forall c q,
  h_mode (s_hdr (q_st q)) = M_COPY ->
  inf_step c q = inf_COPY q.
Proof.
  intros c q Hm. unfold inf_step, q_mode. now rewrite Hm.
Qed.

Lemma zr_step_at_head0 : forall c q,
  h_mode (s_hdr (q_st q)) = M_HEAD ->
  h_wrap (s_hdr (q_st q)) = 0 ->
  inf_step c q = inf_TYPEDO c (qmode q M_TYPEDO).
Proof.
  intros c q Hm Hw. unfold inf_step, q_mode. rewrite Hm.
  unfold inf_HEAD. cbv zeta. rewrite Hw. reflexivity.
Qed.

Lemma zr_step_at_len : forall c q,
  h_mode (s_hdr (q_st q)) = M_LEN ->
  inf_step c q = inf_LEN q.
Proof.
  intros c q Hm. unfold inf_step, q_mode. now rewrite Hm.
Qed.

Lemma zr_step_at_lit : forall c q,
  h_mode (s_hdr (q_st q)) = M_LIT ->
  inf_step c q = inf_LIT q.
Proof.
  intros c q Hm. unfold inf_step, q_mode. now rewrite Hm.
Qed.

Lemma zr_step_at_match : forall c q,
  h_mode (s_hdr (q_st q)) = M_MATCH ->
  inf_step c q = inf_MATCH q.
Proof.
  intros c q Hm. unfold inf_step, q_mode. now rewrite Hm.
Qed.

Print Assumptions inf_loop_after_iter.
Print Assumptions zr_step_at_head0.
