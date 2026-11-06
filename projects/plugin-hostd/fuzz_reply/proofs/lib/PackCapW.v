From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0d YO03 PlaceCap PlaceCapW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack.
Local Open Scope Z_scope.

Lemma AREA2_mono : forall H H', 0 <= H <= H' -> AREA2 H <= AREA2 H'.
Proof.
  intros H H' Hh. unfold AREA2.
  assert (H / METAS_PER_AREA <= H' / METAS_PER_AREA) by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | lia]).
  unfold PGSZ. lia.
Qed.

Lemma RQ2_mono : forall H H' n n', 0 <= H <= H' -> n <= n' -> RQ2 H n <= RQ2 H' n'.
Proof.
  intros H H' n n' Hh Hn. unfold RQ2.
  pose proof (slot_round_mono (n + IB + UNIT) (n' + IB + UNIT) ltac:(lia)).
  pose proof (AREA2_mono H H' Hh). lia.
Qed.

Lemma RQ2_pos : forall H n, 0 < RQ2 H n.
Proof. intros H n. unfold RQ2. assert (0 < MMAX) by (unfold MMAX; lia). lia. Qed.

Lemma pack_capW : forall MB HB NB H M n, 0 <= H <= HB -> 0 <= M -> n <= NB ->
  M + H / METAS_PER_AREA <= MB ->
  MB + 42 + 5 + KRES <= slot_capW (RQ2 HB NB + PGSZ) ->
  SLOTS2 H M + 5 + KRES <= slot_capW (RQ2 H n + PGSZ).
Proof.
  intros MB HB NB H M n Hh HM Hn Hb Hw.
  pose proof (RQ2_mono H HB n NB Hh Hn) as Hq. pose proof (RQ2_pos H n).
  pose proof (slot_capW_anti (RQ2 H n + PGSZ) (RQ2 HB NB + PGSZ) ltac:(unfold PGSZ in *; lia)) as Ha.
  unfold SLOTS2, NA2. lia.
Qed.
