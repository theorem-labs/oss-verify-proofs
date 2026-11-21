(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel ScanModel TreeModel FlushBlockModel RefSendTree3 RefSendTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma send_loop_BINV : forall f P s t mc n p q c mx mn, 1 <= mn -> BINV P s ->
  send_tree_ok P f s t mc n p q c mx mn -> BINV P (send_tree_loop f s t mc n p q c mx mn).
Proof.
  induction f as [|f IH]; intros P s t mc n p q c mx mn Hmn BI OK; [exact BI|].
  rewrite send_loop_S by exact Hmn. cbn [send_tree_ok] in OK. cbv zeta in OK.
  destruct (n <=? mc); [|exact BI]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH; assumption|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:E.
  pose proof (tree_counts_range _ _ _ _ E) as [_ Hmn']. destruct OK as [OK1 OK2].
  apply IH; [lia| apply sbs_BINV; assumption| exact OK2].
Qed.

Lemma send_tree_BINV : forall P s t mc, BINV P s -> send_tree_safe P s t mc -> BINV P (send_tree s t mc).
Proof.
  intros P s t mc BI SAFE. unfold send_tree_safe, RefSendTree4.OK, RefSendTree3.cnts0 in SAFE. unfold send_tree.
  replace (mc + 1 - 0) with (mc + 1) in SAFE by lia.
  destruct (Len s t 0 =? 0); cbn [fst snd] in SAFE; apply send_loop_BINV; try assumption; lia.
Qed.

Lemma scan_tree_flat : forall s t mc, exists b',
  scan_tree s t mc = set_bl_tree_fc (set_Len s t (mc + 1) 65535) b' /\ arr_len b' = arr_len (ds_bl_tree_fc s).
Proof.
  intros s t mc. unfold scan_tree. cbv zeta.
  set (s1 := set_Len s t (mc + 1) 65535).
  assert (E1 : ds_bl_tree_fc s1 = ds_bl_tree_fc s) by (subst s1; apply (tree_fc_set_Len s t (mc + 1) 65535 TB)).
  clearbody s1.
  destruct (Len s t 0 =? 0).
  - destruct (scan_loop_shape (Z.to_nat (mc + 1)) s1 (ds_bl_tree_fc s1) t mc 0 (-1) (Len s t 0) 0 138 3) as (b' & E & Lb & _).
    rewrite sbf_self in E. exists b'. split; [exact E| rewrite Lb, E1; reflexivity].
  - destruct (scan_loop_shape (Z.to_nat (mc + 1)) s1 (ds_bl_tree_fc s1) t mc 0 (-1) (Len s t 0) 0 7 4) as (b' & E & Lb & _).
    rewrite sbf_self in E. exists b'. split; [exact E| rewrite Lb, E1; reflexivity].
Qed.


Lemma land1_testbit : forall m, (Z.land m 1 =? 0) = negb (Z.testbit m 0).
Proof.
  intros m. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod.
  destruct (Z.testbit m 0); reflexivity.
Qed.

Lemma dl1_some : forall f s n mask,
  (exists k, n <= k <= 31 /\ Z.testbit mask (k - n) = true /\ Freq s TL k <> 0) -> 32 - n <= Z.of_nat f ->
  detect_loop1 f s n mask = Some Z_BINARY.
Proof.
  induction f as [|f IH]; intros s n mask (k & Hk & Hb & Hf) Hfu; [lia|].
  cbn [detect_loop1]. rewrite (proj2 (Z.leb_le n 31)) by lia. rewrite land1_testbit, Bool.negb_involutive.
  destruct (Z.eq_dec k n) as [->|NE].
  - replace (n - n) with 0 in Hb by lia. rewrite Hb, (proj2 (Z.eqb_neq _ _) Hf). reflexivity.
  - destruct (Z.testbit mask 0 && negb (Freq s TL n =? 0)); [reflexivity|].
    apply IH; [|lia]. exists k. split; [lia|]. split; [|exact Hf].
    rewrite Z.shiftr_spec by lia. replace (k - (n + 1) + 1) with (k - n) by lia. exact Hb.
Qed.

Lemma dl1_none : forall f s n mask, 0 <= n ->
  (forall k, n <= k <= 31 -> Z.testbit mask (k - n) = true -> Freq s TL k = 0) ->
  detect_loop1 f s n mask = None.
Proof.
  induction f as [|f IH]; intros s n mask Hn H; [reflexivity|].
  cbn [detect_loop1]. destruct (Z.leb_spec n 31) as [Hle|Hgt]; [|reflexivity].
  rewrite land1_testbit, Bool.negb_involutive.
  destruct (Z.testbit mask 0) eqn:Eb.
  - rewrite (H n ltac:(lia)) by (replace (n - n) with 0 by lia; exact Eb). cbn [Z.eqb negb andb].
    apply IH; [lia|]. intros k Hk Hbk. apply H; [lia|]. rewrite Z.shiftr_spec in Hbk by lia. replace (k - (n + 1) + 1) with (k - n) in Hbk by lia. exact Hbk.
  - cbn [andb]. apply IH; [lia|]. intros k Hk Hbk. apply H; [lia|]. rewrite Z.shiftr_spec in Hbk by lia. replace (k - (n + 1) + 1) with (k - n) in Hbk by lia. exact Hbk.
Qed.

Lemma dl2_some : forall f s n, (exists k, n <= k < 256 /\ Freq s TL k <> 0) -> 256 - n <= Z.of_nat f -> detect_loop2 f s n = Some Z_TEXT.
Proof.
  induction f as [|f IH]; intros s n (k & Hk & Hf) Hfu; [lia|].
  cbn [detect_loop2]. unfold LITERALS. rewrite (proj2 (Z.ltb_lt n 256)) by lia.
  destruct (Z.eq_dec k n) as [->|NE].
  - rewrite (proj2 (Z.eqb_neq _ _) Hf). reflexivity.
  - destruct (negb (Freq s TL n =? 0)); [reflexivity|]. apply IH; [|lia]. exists k. split; [lia| exact Hf].
Qed.

Lemma dl2_none : forall f s n, (forall k, n <= k < 256 -> Freq s TL k = 0) -> detect_loop2 f s n = None.
Proof.
  induction f as [|f IH]; intros s n H; [reflexivity|].
  cbn [detect_loop2]. unfold LITERALS. destruct (Z.ltb_spec n 256) as [Hlt|Hge]; [|reflexivity].
  rewrite (H n ltac:(lia)). cbn [Z.eqb negb]. apply IH. intros k Hk. apply H. lia.
Qed.

Definition DD_MASK : Z := 4093624447.
Lemma ddt_binary : forall s k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k <> 0 -> detect_data_type s = Z_BINARY.
Proof.
  intros s k Hk Hb Hf. unfold detect_data_type. fold DD_MASK.
  rewrite (dl1_some 32 s 0 DD_MASK); [reflexivity| |cbn; lia]. exists k. replace (k - 0) with k by lia. auto.
Qed.
Lemma ddt_text1 : forall s, (forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0) ->
  (Freq s TL 9 <> 0 \/ Freq s TL 10 <> 0 \/ Freq s TL 13 <> 0) -> detect_data_type s = Z_TEXT.
Proof.
  intros s H0 H1. unfold detect_data_type. fold DD_MASK.
  assert (E1 : detect_loop1 32 s 0 DD_MASK = None).
  { apply dl1_none; [lia|]. intros k Hk Hb. apply H0; [lia|]. replace (k - 0) with k in Hb by lia. exact Hb. }
  rewrite E1.
  destruct H1 as [H1|[H1|H1]]; rewrite (proj2 (Z.eqb_neq _ _) H1); cbn [negb orb]; rewrite ?Bool.orb_true_r; reflexivity.
Qed.
Lemma ddt_rest : forall s, (forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0) ->
  Freq s TL 9 = 0 -> Freq s TL 10 = 0 -> Freq s TL 13 = 0 ->
  detect_data_type s = match detect_loop2 224%nat s 32 with Some r => r | None => Z_BINARY end.
Proof.
  intros s H0 H9 H10 H13. unfold detect_data_type. fold DD_MASK.
  assert (E1 : detect_loop1 32 s 0 DD_MASK = None).
  { apply dl1_none; [lia|]. intros k Hk Hb. apply H0; [lia|]. replace (k - 0) with k in Hb by lia. exact Hb. }
  rewrite E1.
  rewrite H9, H10, H13. reflexivity.
Qed.
