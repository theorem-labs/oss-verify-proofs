(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorted.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition tokI (bs idxs : list Z) (k : Z) : Z := nth (Z.to_nat k) (idxs ++ [blen bs; blen bs; 0]) 0.
Definition tokT (bs idxs : list Z) (k : Z) : Z := B bs (tokI bs idxs k).
Definition tokn (idxs : list Z) : Z := Z.of_nat (length idxs).

Definition C_QUOTE := 34.  Definition C_COMMA := 44.  Definition C_COLON := 58.
Definition C_LBRACKET := 91.  Definition C_RBRACKET := 93.  Definition C_LBRACE := 123.  Definition C_RBRACE := 125.

Section TokenFacts.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.
  Notation n := (tokn idxs).
  Notation len := (blen bs).
  Notation I := (tokI bs idxs).
  Notation T := (tokT bs idxs).

  Lemma tokn_pos : 1 <= n.
  Proof using HS. pose proof (S1OUT_length_pos _ _ HS). unfold tokn. lia. Qed.

  Lemma tokn_le_len : n <= len.
  Proof using HS. exact (S1OUT_length_le _ _ HS). Qed.

  Lemma tokI_nth : forall k, 0 <= k < n -> nth_error idxs (Z.to_nat k) = Some (I k).
  Proof using HS.
    intros k Hk. unfold tokI, tokn in *. rewrite app_nth1 by lia.
    apply nth_error_nth'. lia.
  Qed.

  Lemma tokI_range : forall k, 0 <= k < n -> 0 <= I k < len.
  Proof using HS. intros k Hk. eapply S1OUT_nth_range; [exact HS| apply tokI_nth; exact Hk]. Qed.

  Lemma tokI_n : I n = len.
  Proof using HS.
    unfold tokI, tokn. rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma tokI_n1 : I (n + 1) = len.
  Proof using HS.
    unfold tokI, tokn. replace (Z.to_nat (Z.of_nat (length idxs) + 1)) with (S (length idxs)) by lia.
    rewrite app_nth2 by lia. replace (S (length idxs) - length idxs)%nat with 1%nat by lia. reflexivity.
  Qed.

  Lemma tokI_n2 : I (n + 2) = 0.
  Proof using HS.
    unfold tokI, tokn. replace (Z.to_nat (Z.of_nat (length idxs) + 2)) with (S (S (length idxs))) by lia.
    rewrite app_nth2 by lia. replace (S (S (length idxs)) - length idxs)%nat with 2%nat by lia. reflexivity.
  Qed.

  Lemma tokI_lt : forall a b, 0 <= a < b -> b <= n -> I a < I b.
  Proof using HS.
    intros a b Hab Hb. destruct (Z.eq_dec b n) as [->|Hne].
    - rewrite tokI_n. apply tokI_range. lia.
    - eapply S1OUT_nth_lt with (a := Z.to_nat a) (b := Z.to_nat b); [exact HS| lia| apply tokI_nth; lia| apply tokI_nth; lia].
  Qed.

  Lemma tokI_le : forall a b, 0 <= a <= b -> b <= n -> I a <= I b.
  Proof using HS. intros a b Hab Hb. destruct (Z.eq_dec a b) as [->|Hne]; [lia|]. pose proof (tokI_lt a b ltac:(lia) Hb). lia. Qed.

  Lemma tokI_ge : forall k, 0 <= k <= n -> k <= I k.
  Proof using HS.
    intros k Hk. destruct (Z.eq_dec k n) as [->|Hne].
    - rewrite tokI_n. apply tokn_le_len.
    - pose proof (S1OUT_nth_ge _ _ HS (Z.to_nat k) (I k) (tokI_nth k ltac:(lia))). lia.
  Qed.

  Lemma tokI_bound : forall k, 0 <= k <= n + 2 -> 0 <= I k <= len.
  Proof using HS.
    intros k Hk. pose proof (blen_nonneg bs) as HL.
    destruct (Z_lt_ge_dec k n) as [Hlt|Hge]; [pose proof (tokI_range k ltac:(lia)); lia|].
    destruct (Z.eq_dec k n) as [->|H1]; [rewrite tokI_n; lia|].
    destruct (Z.eq_dec k (n + 1)) as [->|H2]; [rewrite tokI_n1; lia|].
    replace k with (n + 2) by lia. rewrite tokI_n2. lia.
  Qed.

  Lemma tokT_n : T n = 0.
  Proof using HS. unfold tokT. rewrite tokI_n. apply B_pad. lia. Qed.

  Lemma tokT_nonzero_lt : forall k, 0 <= k <= n -> T k <> 0 -> k < n.
  Proof using HS. intros k Hk Hz. destruct (Z.eq_dec k n) as [->|Hne]; [rewrite tokT_n in Hz; congruence| lia]. Qed.

  Lemma tokT_string : forall k, 0 <= k < n -> T k = C_QUOTE ->
    exists j, closes bs (I k + 1) j /\ I k < j < len /\ j < I (k + 1).
  Proof using HS.
    intros k Hk Hq. destruct (S1OUT_string _ _ HS (Z.to_nat k) (I k) (tokI_nth k Hk) Hq) as (j & Hc & Hj & Hn).
    exists j. split; [exact Hc|]. split; [exact Hj|].
    destruct (Z.eq_dec (k + 1) n) as [E|Hne]; [rewrite E, tokI_n; lia|].
    apply Hn. replace (S (Z.to_nat k)) with (Z.to_nat (k + 1)) by lia. apply tokI_nth. lia.
  Qed.
End TokenFacts.

Record ost : Type := mkO { o_pos : Z; o_depth : Z; o_err : Z; o_alive : bool; o_sbo : Z }.

Definition o_adv (st : ost) (k : Z) : ost := mkO (o_pos st + k) (o_depth st) (o_err st) (o_alive st) (o_sbo st).
Definition o_setd (st : ost) (d : Z) : ost := mkO (o_pos st) d (o_err st) (o_alive st) (o_sbo st).
Definition o_sete (st : ost) (e : Z) : ost := mkO (o_pos st) (o_depth st) e (o_alive st) (o_sbo st).
Definition o_abandon (st : ost) : ost := mkO (o_pos st) 0 (o_err st) false (o_sbo st).

Definition TAPE_ERROR := 3.  Definition INCOMPLETE_ARRAY_OR_OBJECT := 28.

Section Machine.
  Variables (bs idxs : list Z).
  Notation n := (tokn idxs).
  Notation I := (tokI bs idxs).
  Notation T := (tokT bs idxs).

  Definition is_open (c : Z) : bool := (c =? C_LBRACKET) || (c =? C_LBRACE).
  Definition is_close (c : Z) : bool := (c =? C_RBRACKET) || (c =? C_RBRACE).

  Definition skip_first (p : Z) (st : ost) : ost * bool :=
    let c := T (o_pos st) in
    if is_open c || (c =? C_COLON) || (c =? C_COMMA) then (o_adv st 1, false)
    else if (c =? C_QUOTE) && (T (o_pos st + 1) =? C_COLON) then (o_adv st 2, false)
    else (o_setd (o_adv st 1) (o_depth st - 1), o_depth st - 1 <=? p).

  Fixpoint skip_loop (fuel : nat) (p : Z) (st : ost) : ost :=
    match fuel with
    | O => o_sete st TAPE_ERROR
    | S f =>
        if n <=? o_pos st then o_sete st TAPE_ERROR
        else let c := T (o_pos st) in
             if is_open c then skip_loop f p (o_setd (o_adv st 1) (o_depth st + 1))
             else if is_close c then
                    (if o_depth st - 1 <=? p then o_setd (o_adv st 1) (o_depth st - 1)
                     else skip_loop f p (o_setd (o_adv st 1) (o_depth st - 1)))
                  else skip_loop f p (o_adv st 1)
    end.

  Definition skip_child (p : Z) (st : ost) : ost :=
    if o_depth st <=? p then st
    else let '(st1, fin) := skip_first p st in
         if fin then st1 else skip_loop (Z.to_nat (n - o_pos st1)) p st1.

  Definition has_next (d : Z) (st : ost) : ost :=
    let c := T (o_pos st) in
    if c =? C_RBRACKET then o_setd (o_adv st 1) (d - 1)
    else if c =? C_COMMA then o_setd (o_adv st 1) (d + 1)
    else o_sete (o_adv st 1) TAPE_ERROR.

  Definition od_plus (d : Z) (st : ost) : ost :=
    let st1 := skip_child d st in
    if o_err st1 =? 0 then has_next d st1 else st1.

  Definition od_init : ost := mkO 0 1 0 true 0.
  Definition od_begin : ost * bool :=
    if negb (T 0 =? C_LBRACKET) then (od_init, false)
    else if negb (T (n - 1) =? C_RBRACKET) then (mkO 1 0 INCOMPLETE_ARRAY_OR_OBJECT false 0, false)
    else if T 1 =? C_RBRACKET then (mkO 2 0 0 true 0, true)
    else (mkO 1 2 0 true 0, true).

  Definition start_array (d : Z) (st : ost) : ost * bool :=
    if negb (T (o_pos st) =? C_LBRACKET) then (st, false)
    else if T (o_pos st + 1) =? C_RBRACKET then (o_setd (o_adv st 2) d, true)
    else (o_setd (o_adv st 1) (d + 2), true).

  Definition start_object (d : Z) (st : ost) : ost :=
    if negb (T (o_pos st) =? C_LBRACE) then st
    else if T (o_pos st + 1) =? C_RBRACE then o_setd (o_adv st 2) d
    else o_adv st 1.

  Definition consume (d : Z) (st : ost) : ost := o_setd (o_adv st 1) d.

  Inductive acc (d : Z) (st : ost) : ost -> Prop :=
  | acc_none : acc d st st
  | acc_scalar : acc d st (consume d st)
  | acc_string : forall j sbo',
      T (o_pos st) = C_QUOTE -> closes bs (I (o_pos st) + 1) j ->
      o_sbo st <= sbo' <= o_sbo st + (j - (I (o_pos st) + 1)) ->
      acc d st (mkO (o_pos st + 1) d (o_err st) (o_alive st) sbo')
  | acc_array : acc d st (fst (start_array d st))
  | acc_object : acc d st (start_object d st).

  Definition o_left (st : ost) : Z := n + 1 - o_pos st.
End Machine.

Ltac osplit := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section Inv.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.
  Notation n := (tokn idxs).
  Notation len := (blen bs).
  Notation I := (tokI bs idxs).
  Notation T := (tokT bs idxs).

  Hypothesis HLAST : T (n - 1) = C_RBRACKET.

  Definition sbo_ok (st : ost) : Prop := 0 <= o_sbo st /\ o_sbo st <= I (Z.min (o_pos st) n).

  Definition od_head_ok (d : Z) (st : ost) : Prop :=
    1 <= o_pos st <= n - 1 /\ o_depth st = d + 1 /\ o_err st = 0 /\ o_alive st = true /\ sbo_ok st.

  Definition od_plus_ok (d : Z) (st : ost) : Prop :=
    1 <= o_pos st <= n /\ (d < o_depth st -> o_pos st <= n - 1) /\ d <= o_depth st <= o_pos st + 2 + d
    /\ o_err st = 0 /\ o_alive st = true /\ sbo_ok st.

  Definition od_next_ok (d : Z) (st0 st : ost) : Prop :=
    o_pos st0 < o_pos st <= n + 1 /\ o_alive st = true /\ sbo_ok st /\ o_sbo st = o_sbo st0 /\
    (   (o_err st = TAPE_ERROR /\ d <= o_depth st <= o_pos st + 2 + d)
     \/ (o_err st = 0 /\ o_depth st = d - 1 /\ o_pos st <= n)
     \/ od_head_ok d st).

  Lemma tokT_last_lt : forall k c, 0 <= k <= n -> T k = c -> c <> 0 -> c <> C_RBRACKET -> k <= n - 2.
  Proof using HS HLAST.
    intros k c Hk Hc H0 Hr. assert (k < n) by (apply (tokT_nonzero_lt bs idxs HS); [lia| congruence]).
    destruct (Z.eq_dec k (n - 1)) as [E|E]; [|lia]. subst k. congruence.
  Qed.

  Lemma sbo_ok_adv : forall st k, 0 <= k -> 0 <= o_pos st -> sbo_ok st -> sbo_ok (o_adv st k).
  Proof using HS.
    intros st k Hk Hp [H0 H1]. pose proof (tokn_pos bs idxs HS) as Hn. split; [exact H0|]. cbn [o_adv o_pos o_sbo].
    eapply Z.le_trans; [exact H1|]. apply (tokI_le bs idxs HS); lia.
  Qed.

  Lemma sbo_ok_eq : forall st st', o_pos st' = o_pos st -> o_sbo st' = o_sbo st -> sbo_ok st -> sbo_ok st'.
  Proof. intros st st' Hp Hs [H0 H1]. unfold sbo_ok. rewrite Hp, Hs. auto. Qed.

  Ltac sbo_tac :=
    lazymatch goal with
    | |- sbo_ok _ =>
        first [ assumption
              | match goal with H : sbo_ok ?y |- _ => apply (sbo_ok_eq y); [reflexivity| reflexivity| exact H] end
              | match goal with H : sbo_ok ?y |- _ => apply (sbo_ok_eq (o_adv y 1)); [reflexivity| reflexivity| apply sbo_ok_adv; [lia| lia| exact H]] end
              | match goal with H : sbo_ok ?y |- _ => apply (sbo_ok_eq (o_adv y 2)); [reflexivity| reflexivity| apply sbo_ok_adv; [lia| lia| exact H]] end ]
    end.
  Ltac okt := cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo consume fst snd] in *; osplit; try assumption; try reflexivity; try lia; try sbo_tac.

  Lemma acc_plus_ok : forall d st st', 1 <= d -> od_head_ok d st -> acc bs idxs d st st' -> od_plus_ok d st'.
  Proof using HS HLAST.
    intros d st st' Hd (HP & HD & HE & HA & HB) H. pose proof (tokn_pos bs idxs HS) as Hn.
    destruct H as [| |j sbo' Hq Hc Hsb| |].
    -   unfold od_plus_ok. okt.
    -   unfold od_plus_ok, consume. okt.
    -
      destruct (tokT_string bs idxs HS (o_pos st) ltac:(lia) Hq) as (j' & Hc' & Hj' & Hn').
      assert (j' = j) by (eapply closes_det; eassumption). subst j'.
      destruct HB as [HB0 HB1]. rewrite Z.min_l in HB1 by lia.
      unfold od_plus_ok, sbo_ok. cbn [o_pos o_depth o_err o_alive o_sbo]. rewrite Z.min_l by lia. osplit; try assumption; lia.
    -
      unfold start_array. destruct (Z.eqb_spec (T (o_pos st)) C_LBRACKET) as [E|E]; cbn [negb fst].
      + assert (HP2 : o_pos st <= n - 2) by (eapply tokT_last_lt; [| exact E| unfold C_LBRACKET; lia| unfold C_LBRACKET, C_RBRACKET; lia]; lia).
        destruct (Z.eqb_spec (T (o_pos st + 1)) C_RBRACKET) as [E2|E2]; cbn [fst]; unfold od_plus_ok; okt.
      + unfold od_plus_ok. okt.
    -
      unfold start_object. destruct (Z.eqb_spec (T (o_pos st)) C_LBRACE) as [E|E]; cbn [negb].
      + assert (HP2 : o_pos st <= n - 2) by (eapply tokT_last_lt; [| exact E| unfold C_LBRACE; lia| unfold C_LBRACE, C_RBRACKET; lia]; lia).
        destruct (Z.eqb_spec (T (o_pos st + 1)) C_RBRACE) as [E2|E2]; unfold od_plus_ok; okt.
      + unfold od_plus_ok. okt.
  Qed.

  Definition od_skip_ok (d : Z) (st : ost) : Prop :=
    1 <= o_pos st <= n /\ d < o_depth st <= o_pos st + 2 + d /\ o_err st = 0 /\ o_alive st = true /\ sbo_ok st.

  Definition od_loop_post (d : Z) (st st' : ost) : Prop :=
    o_pos st <= o_pos st' <= n /\ o_alive st' = true /\ sbo_ok st' /\ o_sbo st' = o_sbo st /\
    d <= o_depth st' <= o_pos st' + 2 + d /\ ((o_err st' = 0 /\ o_depth st' = d /\ o_pos st < o_pos st') \/ o_err st' = TAPE_ERROR).

  Definition od_skipped_ok (d : Z) (st0 st : ost) : Prop :=
    o_pos st0 <= o_pos st <= n /\ o_alive st = true /\ sbo_ok st /\ o_sbo st = o_sbo st0 /\
    d <= o_depth st <= o_pos st + 2 + d /\
    ((o_err st = 0 /\ o_depth st = d) \/ (o_err st = TAPE_ERROR /\ o_pos st0 < o_pos st)).

  Lemma od_skip_ok_step : forall d st dd, od_skip_ok d st -> o_pos st < n -> d < dd <= o_depth st + 1 ->
    od_skip_ok d (o_setd (o_adv st 1) dd).
  Proof using HS. intros d st dd (HP & HD & HE & HA & HB) Hn Hd. unfold od_skip_ok. okt. Qed.

  Lemma od_skip_ok_key : forall d st, od_plus_ok d st -> d < o_depth st -> tokT bs idxs (o_pos st + 1) = C_COLON ->
    od_skip_ok d (o_adv st 2).
  Proof using HS HLAST.
    intros d st (HP & HPD & HD & HE & HA & HB) Hgt E2. specialize (HPD Hgt).
    assert (HP2 : o_pos st + 1 <= n - 2) by (eapply tokT_last_lt; [| exact E2| unfold C_COLON; lia| unfold C_COLON, C_RBRACKET; lia]; lia).
    unfold od_skip_ok. okt.
  Qed.

  Lemma od_skip_ok_first : forall d st dd, od_plus_ok d st -> d < o_depth st -> d < dd <= o_depth st ->
    od_skip_ok d (o_setd (o_adv st 1) dd).
  Proof using HS. intros d st dd (HP & HPD & HD & HE & HA & HB) Hgt Hd. specialize (HPD Hgt). unfold od_skip_ok. okt. Qed.

  Lemma od_skipped_plus_ok : forall d st, od_plus_ok d st -> o_depth st <= d -> 1 <= o_pos st <= n /\ o_depth st = d.
  Proof. intros d st (HP & HPD & HD & HE & HA & HB) Hd. lia. Qed.

  Lemma skip_loop_ok : forall fuel d st, n - o_pos st <= Z.of_nat fuel -> od_skip_ok d st ->
    od_loop_post d st (skip_loop bs idxs fuel d st).
  Proof using HS.
    induction fuel as [|f IH]; intros d st Hf (HP & HD & HE & HA & HB); cbn [skip_loop].
    - unfold od_loop_post. okt; try solve [right; reflexivity].
    - destruct (Z.leb_spec n (o_pos st)) as [Hge|Hlt].
      + unfold od_loop_post. okt; try solve [right; reflexivity].
      + destruct (is_open (tokT bs idxs (o_pos st))).
        * destruct (IH d (o_setd (o_adv st 1) (o_depth st + 1))) as (A1 & A2 & A3 & A4 & A5 & A6); [cbn [o_adv o_setd o_pos]; lia| unfold od_skip_ok; okt |].
          unfold od_loop_post. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; okt| right; exact B]].
        * destruct (is_close (tokT bs idxs (o_pos st))).
          -- destruct (Z.leb_spec (o_depth st - 1) d) as [Hle|Hgt].
             ++ unfold od_loop_post. okt; try solve [left; okt].
             ++ destruct (IH d (o_setd (o_adv st 1) (o_depth st - 1))) as (A1 & A2 & A3 & A4 & A5 & A6); [cbn [o_adv o_setd o_pos]; lia| unfold od_skip_ok; okt |].
                unfold od_loop_post. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; okt| right; exact B]].
          -- destruct (IH d (o_adv st 1)) as (A1 & A2 & A3 & A4 & A5 & A6); [cbn [o_adv o_pos]; lia| unfold od_skip_ok; okt |].
             unfold od_loop_post. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; okt| right; exact B]].
  Qed.

  Lemma skip_child_ok : forall d st, od_plus_ok d st -> od_skipped_ok d st (skip_child bs idxs d st).
  Proof using HS HLAST.
    intros d st (HP & HPD & HD & HE & HA & HB). unfold skip_child.
    destruct (Z.leb_spec (o_depth st) d) as [Hle|Hgt].
    - unfold od_skipped_ok. okt; try solve [left; split; [exact HE| lia]].
    - specialize (HPD Hgt). unfold skip_first.
      destruct (is_open (tokT bs idxs (o_pos st)) || (tokT bs idxs (o_pos st) =? C_COLON) || (tokT bs idxs (o_pos st) =? C_COMMA)) eqn:E1.
      + destruct (skip_loop_ok (Z.to_nat (n - o_pos (o_adv st 1))) d (o_adv st 1)) as (A1 & A2 & A3 & A4 & A5 & A6); [lia| unfold od_skip_ok; okt |].
        unfold od_skipped_ok. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; split; [exact B1| exact B2]| right; split; [exact B| lia]]].
      + destruct ((tokT bs idxs (o_pos st) =? C_QUOTE) && (tokT bs idxs (o_pos st + 1) =? C_COLON)) eqn:E2.
        * apply andb_prop in E2. destruct E2 as [_ E2]. apply Z.eqb_eq in E2.
          assert (HP2 : o_pos st + 1 <= n - 2) by (eapply tokT_last_lt; [| exact E2| unfold C_COLON; lia| unfold C_COLON, C_RBRACKET; lia]; lia).
          destruct (skip_loop_ok (Z.to_nat (n - o_pos (o_adv st 2))) d (o_adv st 2)) as (A1 & A2 & A3 & A4 & A5 & A6); [cbn [o_adv o_pos]; lia| unfold od_skip_ok; okt |].
          unfold od_skipped_ok. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; split; [exact B1| exact B2]| right; split; [exact B| lia]]].
        * destruct (Z.leb_spec (o_depth st - 1) d) as [Hle1|Hgt1].
          -- unfold od_skipped_ok. okt; try solve [left; split; [exact HE| lia]].
          -- destruct (skip_loop_ok (Z.to_nat (n - o_pos (o_setd (o_adv st 1) (o_depth st - 1)))) d (o_setd (o_adv st 1) (o_depth st - 1))) as (A1 & A2 & A3 & A4 & A5 & A6);
               [cbn [o_adv o_setd o_pos]; lia| unfold od_skip_ok; okt |].
             unfold od_skipped_ok. okt; try solve [destruct A6 as [(B1 & B2 & B3)|B]; [left; split; [exact B1| exact B2]| right; split; [exact B| lia]]].
  Qed.

  Theorem od_plus_spec : forall d st, 1 <= d -> od_plus_ok d st -> od_next_ok d st (od_plus bs idxs d st).
  Proof using HS HLAST.
    intros d st Hd OK. pose proof (skip_child_ok d st OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct OK as (HP & HPD & HD & HE & HA & HB).
    unfold od_plus. set (st1 := skip_child bs idxs d st) in *.
    destruct S6 as [(E0 & S7)|(E3 & PL)].
    -
      rewrite E0. cbn [Z.eqb]. unfold has_next.
      destruct (Z.eqb_spec (tokT bs idxs (o_pos st1)) C_RBRACKET) as [Ec|Ec].
      + assert (HPc : o_pos st1 < n) by (apply (tokT_nonzero_lt bs idxs HS); [lia| rewrite Ec; unfold C_RBRACKET; lia]).
        unfold od_next_ok. okt; try solve [right; left; okt].
      + destruct (Z.eqb_spec (tokT bs idxs (o_pos st1)) C_COMMA) as [Ek|Ek].
        * assert (HP2 : o_pos st1 <= n - 2) by (eapply tokT_last_lt; [| exact Ek| unfold C_COMMA; lia| unfold C_COMMA, C_RBRACKET; lia]; lia).
          unfold od_next_ok. okt; try solve [right; right; unfold od_head_ok; okt].
        * unfold od_next_ok. okt; try solve [left; split; [reflexivity| lia]].
    -
      rewrite E3. cbn [Z.eqb TAPE_ERROR]. unfold od_next_ok. okt; try solve [left; split; [exact E3| lia]].
  Qed.

  Lemma od_closed_plus_ok : forall d st0 st, 1 <= d -> 1 <= o_pos st0 -> od_next_ok (d + 1) st0 st -> o_err st = 0 -> o_depth st = d -> od_plus_ok d st.
  Proof using HS.
    intros d st0 st Hd HP0 (A1 & A2 & A3 & A4 & A5) E0 ED.
    destruct A5 as [(B & _)|[(_ & _ & B)|(B1 & B2 & _)]]; [unfold TAPE_ERROR in B; lia| | lia].
    unfold od_plus_ok. okt.
  Qed.

  Lemma od_inner_head_ok : forall d st, 1 <= d -> od_head_ok d st -> tokT bs idxs (o_pos st) = C_LBRACKET -> tokT bs idxs (o_pos st + 1) <> C_RBRACKET ->
    od_head_ok (d + 1) (o_setd (o_adv st 1) (d + 2)).
  Proof using HS HLAST.
    intros d st Hd (HP & HD & HE & HA & HB) E E2.
    assert (HP2 : o_pos st <= n - 2) by (eapply tokT_last_lt; [| exact E| unfold C_LBRACKET; lia| unfold C_LBRACKET, C_RBRACKET; lia]; lia).
    unfold od_head_ok. okt.
  Qed.

  Lemma od_begin_spec :
    let '(st, valid) := od_begin bs idxs in
    if valid then (od_head_ok 1 st \/ (o_depth st = 0 /\ o_err st = 0 /\ o_pos st = 2 /\ o_alive st = true /\ o_sbo st = 0))
    else (o_alive st = false /\ o_depth st = 0 /\ o_err st = INCOMPLETE_ARRAY_OR_OBJECT) \/ st = od_init.
  Proof using HS HLAST.
    unfold od_begin. pose proof (tokn_pos bs idxs HS) as Hn.
    destruct (Z.eqb_spec (T 0) C_LBRACKET) as [E0|E0]; cbn [negb]; [| right; reflexivity].
    destruct (Z.eqb_spec (T (n - 1)) C_RBRACKET) as [E1|E1]; cbn [negb]; [| left; osplit; reflexivity].
    assert (N2 : 2 <= n).
    { destruct (Z.eq_dec n 1) as [E|E]; [|lia]. exfalso. rewrite E in E1. cbn in E1. rewrite E0 in E1. unfold C_LBRACKET, C_RBRACKET in E1. lia. }
    destruct (Z.eqb_spec (T 1) C_RBRACKET) as [E2|E2].
    - right. osplit; reflexivity.
    - left. unfold od_head_ok, sbo_ok. cbn [o_pos o_depth o_err o_alive o_sbo].
      pose proof (tokI_bound bs idxs HS (Z.min 1 n) ltac:(lia)). osplit; try lia; try reflexivity.
  Qed.
End Inv.
