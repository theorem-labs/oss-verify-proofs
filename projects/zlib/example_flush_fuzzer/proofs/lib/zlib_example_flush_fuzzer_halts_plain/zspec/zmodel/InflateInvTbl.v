(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ItCovIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma iterK_nat_inv : forall {A B} (P : A -> Prop) (Q : B -> Prop) (step : A -> A + B),
  (forall a, P a -> match step a with inl a' => P a' | inr b => Q b end) ->
  forall n a, P a -> match iterK_nat n step a with inl a' => P a' | inr b => Q b end.
Proof.
  intros A B P Q step HS n. induction n as [|n IH]; intros a Pa; cbn [iterK_nat]; [exact Pa|].
  pose proof (HS a Pa) as X. destruct (step a) as [a'|b]; [apply IH; exact X | exact X].
Qed.

Lemma iterZ_inv : forall {A B} (P : A -> Prop) (Q : B -> Prop) n (step : A -> A + B) (dflt : A -> B) a,
  P a -> (forall a, P a -> match step a with inl a' => P a' | inr b => Q b end) ->
  (forall a, P a -> Q (dflt a)) -> Q (iterZ n step dflt a).
Proof.
  intros A B P Q n step dflt a Pa HS HD. rewrite iterZ_nat.
  pose proof (iterK_nat_inv P Q step HS (Z.to_nat n) a Pa) as X.
  destruct (iterK_nat _ _ _) as [a'|b]; [apply HD; exact X | exact X].
Qed.

Lemma loopZ_inv : forall {A} (P : A -> Prop) n (step : A -> bool * A) a,
  P a -> (forall a, P a -> P (snd (step a))) -> P (loopZ n step a).
Proof.
  intros A P n step a Pa HS. unfold loopZ.
  apply (iterZ_inv P P); [exact Pa | | intros a0 H; exact H].
  intros a0 H. pose proof (HS a0 H) as X. destruct (step a0) as [c a']. cbn [snd] in X. destruct c; exact X.
Qed.

Lemma forZ_inv : forall {A} (P : A -> Prop) lo hi (body : Z -> A -> A) a,
  P a -> (forall i a, P a -> P (body i a)) -> P (forZ lo hi body a).
Proof.
  intros A P lo hi body a Pa HB. unfold forZ.
  enough (X : (fun ia : Z * A => P (snd ia)) (loopZ (hi - lo) (fun ia : Z * A => let '(i, a0) := ia in if i <? hi then (true, (i + 1, body i a0)) else (false, (i, a0))) (lo, a))) by exact X.
  apply loopZ_inv; [exact Pa|]. intros [i a0] H. cbn [snd] in H |- *. destruct (i <? hi); cbn [snd]; [apply HB; exact H | exact H].
Qed.


Definition cells_below (B : Z) (a : arr) : Prop := forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < B.

Lemma cells_below_set : forall B a j v, cells_below B a -> 0 <= v < B -> cells_below B (arr_set a j v).
Proof.
  intros B a j v H Hv i Hi. rewrite arr_len_set in Hi. rewrite arr_get_set.
  destruct ((j =? i) && arr_inb a j); [exact Hv | exact (H i Hi)].
Qed.

Lemma code_pack_range : forall op bits val, 0 <= code_pack op bits val < 2 ^ 32.
Proof.
  intros op bits val. unfold code_pack.
  pose proof (w8_range op). pose proof (w8_range bits). pose proof (w16_range val). lia.
Qed.


Lemma it_fill_u32 : forall here incr huff drop next fill tbl,
  cells_below (2 ^ 32) tbl -> 0 <= here < 2 ^ 32 ->
  cells_below (2 ^ 32) (it_fill here incr huff drop next fill tbl) /\ arr_len (it_fill here incr huff drop next fill tbl) = arr_len tbl.
Proof.
  intros here incr huff drop next fill tbl H Hh. unfold it_fill.
  enough (X : (fun ft : Z * arr => cells_below (2 ^ 32) (snd ft) /\ arr_len (snd ft) = arr_len tbl)
               (loopZ fill (fun ft : Z * arr => let '(fill0, tbl0) := ft in
                  let fill1 := wrap32 (fill0 - incr) in
                  let tbl1 := arr_set tbl0 (next + (Z.shiftr huff drop + fill1)) here in
                  if negb (fill1 =? 0) then (true, (fill1, tbl1)) else (false, (fill1, tbl1))) (fill, tbl))) by exact X.
  apply loopZ_inv; [split; [exact H | reflexivity]|].
  intros [f t] [P L]. cbn [snd] in P, L |- *.
  destruct (negb (wrap32 (f - incr) =? 0)); cbn [snd]; (split; [apply cells_below_set; [exact P | exact Hh] | rewrite arr_len_set; exact L]).
Qed.

Lemma it_sort_u16 : forall lens lens_ofs codes offs work,
  cells_below (2 ^ 16) work ->
  cells_below (2 ^ 16) (snd (it_sort lens lens_ofs codes (offs, work))) /\ arr_len (snd (it_sort lens lens_ofs codes (offs, work))) = arr_len work.
Proof.
  intros lens lens_ofs codes offs work H. unfold it_sort.
  match goal with |- cells_below _ (snd (forZ 0 codes ?body ?a)) /\ _ =>
    enough (X : (fun ow : arr * arr => cells_below (2 ^ 16) (snd ow) /\ arr_len (snd ow) = arr_len work) (forZ 0 codes body a)) by exact X end.
  apply forZ_inv; [split; [exact H | reflexivity]|].
  intros i [o w] [P L]. cbn [snd] in P, L |- *.
  destruct (negb (arr_get lens (lens_ofs + i) =? 0)); cbn [snd]; [| split; [exact P | exact L]].
  split; [apply cells_below_set; [exact P | pose proof (w16_range i); lia] | rewrite arr_len_set; exact L].
Qed.

Definition st_ok (LT : Z) (work : arr) (st : ItSt) : Prop :=
  cells_below (2 ^ 32) (t_tbl st) /\ arr_len (t_tbl st) = LT /\ t_work st = work.

Lemma it_step_ok : forall x LT work st,
  st_ok LT work st ->
  match it_step x st with ItCont st' | ItBreak st' | ItFail st' => st_ok LT work st' end.
Proof.
  intros x LT work st (P & L & W). unfold it_step.
  destruct (if arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x) then _ else _) as [here_op here_val].
  set (here := code_pack here_op _ here_val).
  pose proof (code_pack_range here_op (wrap8 (t_len st - t_drop st)) here_val) as HR. fold here in HR.
  destruct (it_fill_u32 here (shl32 1 (t_len st - t_drop st)) (t_huff st) (t_drop st) (t_next st) (shl32 1 (t_curr st)) (t_tbl st) P HR) as [P1 L1].
  set (tbl1 := it_fill here _ _ _ _ _ _) in P1, L1 |- *.
  cbv zeta.
  repeat (lazymatch goal with |- context [match (if ?c then _ else _) with _ => _ end] => destruct c end);
    unfold st_ok; cbn [t_tbl t_work];
    first [ (split; [exact P1 | split; [rewrite L1; exact L | exact W]])
          | (split; [apply cells_below_set; [exact P1 | apply code_pack_range] | split; [rewrite arr_len_set, L1; exact L | exact W]]) ].
Qed.

Lemma it_loop_ok : forall x codes LT work st,
  st_ok LT work st -> match it_loop x codes st with inl st' | inr st' => st_ok LT work st' end.
Proof.
  intros x codes LT work st H. unfold it_loop.
  apply (iterZ_inv (st_ok LT work) (fun r : ItSt + ItSt => match r with inl st' | inr st' => st_ok LT work st' end)); [exact H | | intros a Ha; exact Ha].
  intros a Ha. pose proof (it_step_ok x LT work a Ha) as X. destruct (it_step x a); exact X.
Qed.

Theorem inflate_table_ranges : forall ty lens lens_ofs codes tbl table bits work,
  let '(ret, tbl', table', bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  (ret = 0 \/ ret = 1 \/ ret = -1)
  /\ (cells_below (2 ^ 32) tbl -> cells_below (2 ^ 32) tbl')
  /\ (cells_below (2 ^ 16) work -> cells_below (2 ^ 16) work')
  /\ arr_len tbl' = arr_len tbl /\ arr_len work' = arr_len work.
Proof.
  intros ty lens lens_ofs codes tbl table bits work. unfold inflate_table.
  destruct (it_find_max _ =? 0).
  { pose proof (code_pack_range 64 1 0) as HR.
    split; [left; reflexivity|]. split; [intros H; apply cells_below_set; [apply cells_below_set; [exact H | exact HR] | exact HR]|].
    split; [intros H; exact H|]. rewrite !arr_len_set. split; reflexivity. }
  destruct (it_left_check _) as [lft|].
  2:{ split; [right; right; reflexivity|]. split; [intros H; exact H|]. split; [intros H; exact H|]. split; reflexivity. }
  destruct ((0 <? lft) && _).
  { split; [right; right; reflexivity|]. split; [intros H; exact H|]. split; [intros H; exact H|]. split; reflexivity. }
  destruct (it_sort lens lens_ofs codes _) as [offs' work1] eqn:ES.
  assert (W1 : (cells_below (2 ^ 16) work -> cells_below (2 ^ 16) work1) /\ arr_len work1 = arr_len work).
  { match type of ES with it_sort _ _ _ (?o, _) = _ =>
      pose proof (it_sort_u16 lens lens_ofs codes o work) as X end.
    rewrite ES in X. cbn [snd] in X.
    split; [intros H; exact (proj1 (X H))|].
    match type of ES with it_sort _ _ _ (?o, _) = _ =>
      assert (L : (fun ow : arr * arr => arr_len (snd ow) = arr_len work) (it_sort lens lens_ofs codes (o, work))) end.
    { unfold it_sort. apply forZ_inv; [reflexivity|]. intros i [o0 w0] Hl. cbn [snd] in Hl |- *.
      destruct (negb (arr_get lens (lens_ofs + i) =? 0)); cbn [snd]; [rewrite arr_len_set; exact Hl | exact Hl]. }
    rewrite ES in L. exact L. }
  destruct W1 as [W1 LW1].
  destruct (it_not_enough ty _).
  { split; [right; left; reflexivity|]. split; [intros H; exact H|]. split; [exact W1|]. split; [reflexivity | exact LW1]. }
  match goal with |- context [it_loop ?x codes ?st0] =>
    pose proof (fun (P0 : cells_below (2 ^ 32) tbl) => it_loop_ok x codes (arr_len tbl) work1 st0 (conj P0 (conj eq_refl eq_refl))) as IL;
    assert (ILL : match it_loop x codes st0 with inl st' | inr st' => arr_len (t_tbl st') = arr_len tbl /\ t_work st' = work1 end)
  end.
  {
    match goal with |- match it_loop ?x codes ?st0 with _ => _ end =>
      apply (iterZ_inv (fun st => arr_len (t_tbl st) = arr_len tbl /\ t_work st = work1)
               (fun r : ItSt + ItSt => match r with inl st' | inr st' => arr_len (t_tbl st') = arr_len tbl /\ t_work st' = work1 end));
      [split; reflexivity | | intros a Ha; exact Ha] end.
    intros a [La Wa]. unfold it_step.
    destruct (if arr_get (t_work a) (t_sym a) + 1 <? it_match _ then _ else _) as [here_op here_val].
    match goal with |- context [it_fill ?h ?inc ?hu ?dr ?nx ?fi (t_tbl a)] =>
      pose proof (proj2 (it_fill_u32 h inc hu dr nx fi (arr_make (arr_len (t_tbl a)) 0) ltac:(intros i Hi; rewrite arr_get_make; lia) (code_pack_range _ _ _))) as LF end.
    clear LF.
    match goal with |- context [it_fill ?h ?inc ?hu ?dr ?nx ?fi (t_tbl a)] =>
      assert (LF : arr_len (it_fill h inc hu dr nx fi (t_tbl a)) = arr_len (t_tbl a)) end.
    { unfold it_fill.
      match goal with |- arr_len (snd (loopZ ?n ?body ?a0)) = _ =>
        enough (X : (fun ft : Z * arr => arr_len (snd ft) = arr_len (t_tbl a)) (loopZ n body a0)) by exact X end.
      apply loopZ_inv; [reflexivity|]. intros [f t] Hl. cbn [snd] in Hl |- *.
      destruct (negb (wrap32 (f - _) =? 0)); cbn [snd]; rewrite arr_len_set; exact Hl. }
    cbv zeta.
    repeat (lazymatch goal with |- context [match (if ?c then _ else _) with _ => _ end] => destruct c end);
      cbn [t_tbl t_work]; rewrite ?arr_len_set, LF; split; assumption. }
  destruct (it_loop _ codes _) as [st|st].
  - destruct ILL as [LT' WK']. split; [left; reflexivity|]. split.
    { intros H. destruct (IL H) as (P' & _ & _). destruct (negb (t_huff st =? 0)); [apply cells_below_set; [exact P' | apply code_pack_range] | exact P']. }
    split; [rewrite WK'; exact W1|]. split; [| rewrite WK'; exact LW1].
    destruct (negb (t_huff st =? 0)); [rewrite arr_len_set; exact LT' | exact LT'].
  - destruct ILL as [LT' WK']. split; [right; left; reflexivity|]. split; [intros H; exact (proj1 (IL H))|].
    split; [rewrite WK'; exact W1|]. split; [exact LT' | rewrite WK'; exact LW1].
Qed.
