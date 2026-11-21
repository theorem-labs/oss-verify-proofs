(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MI_Kit MI_WGroup MI_WEnframe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wrs_read_other l : forall st r, Forall (fun av : aptr * Z => fst av <> r) l ->
  cell_read (get_shadow (wrs l st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r).
Proof.
  induction l as [|[a v] l IH]; intros st r HF; cbn [wrs]; [reflexivity|].
  inversion HF as [|x y H1 H2]; subst. cbn [fst] in H1.
  rewrite IH by exact H2. apply (MI_Kit.cell_read_wr8_other a v st r). congruence.
Qed.

Lemma enframe_at_read_user st g idx n off b o :
  m_mem (get_meta_rec st g) = Some b ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= get_stride (get_meta_rec st g) ->
  snd b + 16 + get_stride (get_meta_rec st g) * idx + 16 * off <= o < snd b + 16 + get_stride (get_meta_rec st g) * idx + 16 * off + n ->
  cell_read (get_shadow (fst (enframe_at st g idx n off)) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
  intros Hmem O0 N0 FIT Ho. rewrite enframe_at_eq. cbn [fst].
  change (cell_read (get_shadow (wrs (ef_list st g idx n off) st) (fst (fst b, o))) (snd (fst b, o))
          = cell_read (get_shadow st (fst (fst b, o))) (snd (fst b, o))).
  apply wrs_read_other.
  unfold ef_list. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT, IB. cbn [fst snd].
  set (S := get_stride (get_meta_rec st g)) in *.
  destruct (Z.eqb_spec off 0) as [E0|NE0]; cbn [negb fst snd app];
  [ subst off |];
  (match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (Z.eqb_spec x 0) as [R0|R0] end);
  (match goal with |- context [if 5 <=? ?x then _ else _] => destruct (Z.leb_spec 5 x) as [R5|R5] end);
  cbn [negb app]; repeat constructor; cbn [fst snd]; intros EQ; inversion EQ; lia.
Qed.

Lemma all_nth_repeat {A} (x : A) (l : list A) :
  (forall i, (i < length l)%nat -> nth_error l i = Some x) -> l = repeat x (length l).
Proof.
  induction l as [|y l IH]; intros H; [reflexivity|]. cbn [length repeat].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. inversion H0; subst y. f_equal.
  apply IH. intros i Hi. apply (H (S i)). cbn. lia.
Qed.

Lemma bytes_all_zero segs (m : word -> option byte) (A : Z) (bs : list byte) :
  bytes_at segs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> bytes_at segs m (A + i) [Z_to_bv 8 0]) ->
  bs = repeat (Z_to_bv 8 0) (length bs).
Proof.
  intros (A0 & A1 & HB) HZ. apply all_nth_repeat. intros i Hi.
  rewrite <- (HB i Hi). destruct (HZ (Z.of_nat i) ltac:(lia)) as (_ & _ & H1).
  specialize (H1 0%nat ltac:(cbn; lia)). cbn [nth_error] in H1. rewrite Z.add_0_r in H1. exact H1.
Qed.
