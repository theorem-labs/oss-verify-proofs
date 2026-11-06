(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module S1M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition char_class (c : Z) : Z :=
  if (c <? 0) || (255 <? c) then 0
  else if c <? 32 then (if (c =? 9) || (c =? 10) || (c =? 13) then 5 else 4)
  else if c =? 32 then 1
  else if (c =? 34) || (c =? 92) then 4
  else if (c =? 44) || (c =? 58) || (c =? 91) || (c =? 93) || (c =? 123) || (c =? 125) then 2
  else if c <? 128 then 0
  else 8.

(* [comment removed for export] *)
Definition char_table : list Z :=
  [4;4;4;4;4;4;4;4; 4;5;5;4;4;5;4;4; 4;4;4;4;4;4;4;4; 4;4;4;4;4;4;4;4;
   1;0;4;0;0;0;0;0; 0;0;0;0;2;0;0;0; 0;0;0;0;0;0;0;0; 0;0;2;0;0;0;0;0;
   0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;2;4;2;0;0;
   0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;0;0;0;0;0; 0;0;0;2;0;2;0;0;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;
   8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8].

Lemma char_table_length : length char_table = 256%nat.
Proof. reflexivity. Qed.

Lemma char_class_table : forall n : nat, (n < 256)%nat -> nth n char_table 0 = char_class (Z.of_nat n).
Proof.
  intros n Hn.
  do 256 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Definition is_space (c : Z) : bool := Z.testbit (char_class c) 0.
Definition is_op (c : Z) : bool := Z.testbit (char_class c) 1.
Definition is_space_or_op (c : Z) : bool := negb (Z.land (char_class c) 3 =? 0).
Definition is_ascii_stop (c : Z) : bool := negb (Z.land (char_class c) 12 =? 0).
Definition is_cont (c : Z) : bool := Z.land c 192 =? 128.       (* [comment removed for export] *)

Definition QUOTE : Z := 34.
Definition BACKSLASH : Z := 92.
Definition RS : Z := 30.                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SUCCESS : Z := 0.
Definition UTF8_ERROR : Z := 11.
Definition EMPTY : Z := 13.
Definition UNESCAPED_CHARS : Z := 14.
Definition UNCLOSED_STRING : Z := 15.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Scanner.
Variable b : Z -> Z.        (* [comment removed for export] *)
Variable len : Z.

(* [comment removed for export] *)
Ltac rd := cbn -[is_space is_op is_space_or_op is_ascii_stop is_cont char_class Z.add Z.sub Z.mul].
Ltac rdin H := cbn -[is_space is_op is_space_or_op is_ascii_stop is_cont char_class Z.add Z.sub Z.mul] in H.

(* [comment removed for export] *)
Definition vutf8 (idx err : Z) : Z * Z :=
  let c := b idx in
  if Z.land c 64 =? 0 then (idx + 1, UTF8_ERROR)
  else if Z.land c 32 =? 0 then
    if (len <? idx + 1) || negb (is_cont (b (idx + 1))) then (idx + 1, UTF8_ERROR)
    else (idx + 2, if c <=? 193 then UTF8_ERROR else err)
  else if Z.land c 16 =? 0 then
    if (len <? idx + 2) || negb (is_cont (b (idx + 1))) || negb (is_cont (b (idx + 2))) then (idx + 1, UTF8_ERROR)
    else (idx + 3, if ((c =? 224) && (b (idx + 1) <=? 159)) || ((c =? 237) && (160 <=? b (idx + 1))) then UTF8_ERROR else err)
  else
    if (len <? idx + 3) || negb (is_cont (b (idx + 1))) || negb (is_cont (b (idx + 2))) || negb (is_cont (b (idx + 3)))
    then (idx + 1, UTF8_ERROR)
    else (idx + 4, if ((c =? 240) && (b (idx + 1) <=? 143)) || ((c =? 244) && (144 <=? b (idx + 1))) || (245 <=? c)
                   then UTF8_ERROR else err).

(* [comment removed for export] *)
Fixpoint stoprun (fuel : nat) (idx : Z) : Z :=
  match fuel with
  | O => idx
  | S f => if is_ascii_stop (b idx) then idx
           else if idx + 1 <? len then stoprun f (idx + 1) else idx + 1
  end.

(* [comment removed for export] *)
Fixpoint vstring_loop (fuel : nat) (idx err : Z) : Z * Z * bool :=
  match fuel with
  | O => (idx, err, true)
  | S f =>
      if idx <? len then
        let i := stoprun (Z.to_nat (len - idx)) idx in
        if len <=? i then (i, err, true)
        else let c := b i in
          if c =? QUOTE then (i, err, false)
          else if c =? BACKSLASH then vstring_loop f (i + 2) err
          else if negb (Z.land c 128 =? 0) then let '(i', err') := vutf8 i err in vstring_loop f i' err'
          else vstring_loop f (i + 1) (if c <? 32 then UNESCAPED_CHARS else err)
      else (idx, err, true)
  end.
Definition vstring (idx err : Z) : Z * Z * bool := vstring_loop (Z.to_nat (len + 2)) (idx + 1) err.

(* [comment removed for export] *)
Fixpoint wsrun (fuel : nat) (idx : Z) : Z :=
  match fuel with
  | O => idx
  | S f => if is_space (b idx) then (if idx + 1 <? len then wsrun f (idx + 1) else idx + 1) else idx
  end.

(* [comment removed for export] *)
Fixpoint primrun (fuel : nat) (idx : Z) : Z :=
  match fuel with
  | O => idx
  | S f => if (idx + 1 <? len) && negb (is_space_or_op (b (idx + 1))) && negb (b (idx + 1) =? RS)
           then primrun f (idx + 1) else idx
  end.

(* [comment removed for export] *)
Record st := ST { s_idx : Z; s_out : list Z; s_err : Z; s_unclosed : bool }.

(* [comment removed for export] *)
Definition iter (s : st) : st :=
  let i := wsrun (Z.to_nat (len - s_idx s)) (s_idx s) in
  if len <=? i then ST i (s_out s) (s_err s) (s_unclosed s)       (* [comment removed for export] *)
  else let c := b i in
    if c =? QUOTE then
      let '(i', err', u) := vstring i (s_err s) in ST (i' + 1) (s_out s ++ [i]) err' (s_unclosed s || u)
    else if is_op c then ST (i + 1) (s_out s ++ [i]) (s_err s) (s_unclosed s)
    else ST (primrun (Z.to_nat (len - i)) i + 1) (s_out s ++ [i]) (s_err s) (s_unclosed s).

Fixpoint run (fuel : nat) (s : st) : st :=
  match fuel with
  | O => s
  | S f => if s_idx s <? len then run f (iter s) else s
  end.

Definition init : st := ST 0 [] SUCCESS false.
Definition final : st := run (Z.to_nat len + 1) init.

(* [comment removed for export] *)
Definition result : list Z * Z :=
  let s := final in
  let n := Z.of_nat (length (s_out s)) in
  if n =? 0 then (s_out s, EMPTY)
  else (s_out s, if s_unclosed s then UNCLOSED_STRING else s_err s).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive reach : st -> Prop :=
| reach_init : reach init
| reach_step : forall s, reach s -> s_idx s < len -> reach (iter s).

Lemma run_reach : forall fuel s, reach s -> reach (run fuel s).
Proof.
  induction fuel as [|f IH]; intros s Hs; rd; [exact Hs|].
  destruct (Z.ltb_spec (s_idx s) len); [|exact Hs].
  apply IH. apply reach_step; assumption.
Qed.

Lemma final_reach : reach final.
Proof. unfold final. apply run_reach. apply reach_init. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wsrun_ge : forall fuel idx, idx <= wsrun fuel idx.
Proof. induction fuel as [|f IH]; intros idx; rd; [lia|]. destruct (is_space (b idx)); [|lia]. destruct (idx + 1 <? len); [|lia]. specialize (IH (idx + 1)). lia. Qed.

Lemma primrun_ge : forall fuel idx, idx <= primrun fuel idx.
Proof. induction fuel as [|f IH]; intros idx; rd; [lia|]. destruct (_ && _ && _)%bool; [|lia]. specialize (IH (idx + 1)). lia. Qed.

Lemma primrun_lt : forall fuel idx, idx < len -> primrun fuel idx < len.
Proof.
  induction fuel as [|f IH]; intros idx H; rd; [lia|].
  destruct (Z.ltb_spec (idx + 1) len); rd; [|exact H].
  destruct (negb (is_space_or_op (b (idx + 1))) && negb (b (idx + 1) =? RS))%bool; [|exact H].
  apply IH. assumption.
Qed.

Lemma stoprun_ge : forall fuel idx, idx <= stoprun fuel idx.
Proof. induction fuel as [|f IH]; intros idx; rd; [lia|]. destruct (is_ascii_stop (b idx)); [lia|]. destruct (idx + 1 <? len); [|lia]. specialize (IH (idx + 1)). lia. Qed.

Lemma vutf8_gt : forall idx err, idx < fst (vutf8 idx err).
Proof.
  intros idx err. unfold vutf8.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); rd; lia.
Qed.

Lemma vstring_loop_ge : forall fuel idx err, idx <= fst (fst (vstring_loop fuel idx err)) \/ len <= fst (fst (vstring_loop fuel idx err)).
Proof.
  induction fuel as [|f IH]; intros idx err; rd; [left; lia|].
  destruct (Z.ltb_spec idx len); [|left; rd; lia].
  pose proof (stoprun_ge (Z.to_nat (len - idx)) idx) as Hs.
  set (i := stoprun (Z.to_nat (len - idx)) idx) in *.
  destruct (Z.leb_spec len i); [right; rd; lia|].
  destruct (b i =? QUOTE); [left; rd; lia|].
  destruct (b i =? BACKSLASH).
  { destruct (IH (i + 2) err); [left|right]; lia. }
  destruct (negb (Z.land (b i) 128 =? 0)).
  { destruct (vutf8 i err) as [i' err'] eqn:Hv. pose proof (vutf8_gt i err) as Hg. rewrite Hv in Hg. rdin Hg.
    destruct (IH i' err'); [left|right]; lia. }
  destruct (IH (i + 1) (if b i <? 32 then UNESCAPED_CHARS else err)); [left|right]; lia.
Qed.

(* [comment removed for export] *)
Definition sorted_lt (l : list Z) : Prop := forall i j : nat, (i < j)%nat -> (j < length l)%nat -> nth i l 0 < nth j l 0.
Definition wf (s : st) : Prop :=
  0 <= s_idx s /\ sorted_lt (s_out s) /\ (forall x, In x (s_out s) -> 0 <= x < len /\ x < s_idx s).

Lemma sorted_lt_app1 : forall l x, sorted_lt l -> (forall y, In y l -> y < x) -> sorted_lt (l ++ [x]).
Proof.
  intros l x Hs Hlt i j Hij Hj. rewrite length_app in Hj. rdin Hj.
  destruct (Nat.lt_ge_cases j (length l)) as [Hjl|Hjl].
  - rewrite !app_nth1 by lia. apply Hs; assumption.
  - assert (j = length l) as -> by lia. rewrite (@app_nth2 _ l [x] 0 (length l)) by lia. rewrite Nat.sub_diag. rd.
    rewrite (@app_nth1 _ l [x] 0 i) by lia. apply Hlt. apply nth_In. lia.
Qed.

Lemma wf_push : forall idx out err u i idx',
  wf (ST idx out err u) -> idx <= i -> i < len -> i < idx' -> wf (ST idx' (out ++ [i]) err u).
Proof.
  intros idx out err u i idx' (H0 & Hs & Hin) Hle Hlt Hlt'. unfold wf in *. cbn in *. split; [lia|]. split.
  - apply sorted_lt_app1; [exact Hs|]. intros y Hy. destruct (Hin y Hy). lia.
  - intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]. + destruct (Hin x Hx). lia. + lia.
Qed.

Lemma wf_iter : forall s, wf s -> s_idx s < len -> wf (iter s).
Proof.
  intros [idx out err u] Hwf Hlt. unfold iter. cbn [s_idx s_out s_err s_unclosed].
  pose proof (wsrun_ge (Z.to_nat (len - idx)) idx) as Hw. set (i := wsrun _ idx) in *.
  destruct (Z.leb_spec len i).
  { destruct Hwf as (H0 & Hs & Hin). unfold wf in *. cbn in *. split; [rd; lia|]. split; [exact Hs|]. intros x Hx. destruct (Hin x Hx). rd. lia. }
  destruct (b i =? QUOTE).
  { destruct (vstring i err) as [[i' err'] u'] eqn:Hv.
    assert (i <= i') as Hi'.
    { unfold vstring in Hv. pose proof (vstring_loop_ge (Z.to_nat (len + 2)) (i + 1) err) as HH. rewrite Hv in HH. rdin HH. lia. }
    eapply wf_push; [ | exact Hw | lia | lia].
    destruct Hwf as (A & B & C). split; [exact A|]. split; [exact B|]. exact C. }
  destruct (is_op (b i)).
  { eapply wf_push; [exact Hwf | exact Hw | lia | lia]. }
  pose proof (primrun_ge (Z.to_nat (len - i)) i).
  eapply wf_push; [exact Hwf | exact Hw | lia | lia].
Qed.

Lemma wf_reach : forall s, reach s -> wf s.
Proof.
  intros s Hr. induction Hr as [|s Hr IH Hlt].
  - unfold wf, init, sorted_lt. rd. split; [lia|]. split; [intros; lia|]. intros x [].
  - apply wf_iter; assumption.
Qed.

(* [comment removed for export] *)
Theorem indexes_lt_len : forall x, In x (fst result) -> 0 <= x < len.
Proof.
  intros x Hx. unfold result in Hx.
  assert (In x (s_out final)) as H by (destruct (_ =? 0); exact Hx).
  destruct (wf_reach final final_reach) as (_ & _ & Hin). destruct (Hin x H). lia.
Qed.

Theorem indexes_sorted : sorted_lt (fst result).
Proof.
  unfold result. destruct (wf_reach final final_reach) as (_ & Hs & _). destruct (_ =? 0); exact Hs.
Qed.

Lemma sorted_lt_nth_ge : forall l, sorted_lt l -> (forall x, In x l -> 0 <= x) ->
  forall j, (j < length l)%nat -> Z.of_nat j <= nth j l 0.
Proof.
  intros l Hs Hnn j. induction j as [|j IH]; intros Hj.
  - pose proof (Hnn (nth 0 l 0) (@nth_In _ 0 l 0 Hj)). cbn; lia.
  - specialize (IH ltac:(lia)). specialize (Hs j (S j) ltac:(lia) Hj). lia.
Qed.

Theorem n_le_len : 0 <= len -> Z.of_nat (length (fst result)) <= len.
Proof.
  intros Hlen.
  pose proof indexes_sorted as Hs. pose proof indexes_lt_len as Hin.
  set (l := fst result) in *. clearbody l.
  destruct (length l) as [|k] eqn:HL; [cbn; lia|].
  pose proof (sorted_lt_nth_ge l Hs ltac:(intros x Hx; destruct (Hin x Hx); lia) k ltac:(lia)) as Hk.
  pose proof (Hin (nth k l 0) (@nth_In _ k l 0 ltac:(lia))). rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qsearch (fuel : nat) (i : Z) : option Z :=
  match fuel with
  | O => None
  | S f => if b i =? QUOTE then Some i
           else if b i =? BACKSLASH then qsearch f (i + 2)
           else qsearch f (i + 1)
  end.

Lemma qsearch_ge : forall fuel i j, qsearch fuel i = Some j -> i <= j /\ b j = QUOTE.
Proof.
  induction fuel as [|f IH]; intros i j H; rdin H; [discriminate|].
  destruct (Z.eqb_spec (b i) QUOTE); [injection H as <-; split; [lia|assumption]|].
  destruct (b i =? BACKSLASH); apply IH in H; lia.
Qed.

Lemma qsearch_mono_fuel : forall fuel fuel' i j, qsearch fuel i = Some j -> (fuel <= fuel')%nat -> qsearch fuel' i = Some j.
Proof.
  induction fuel as [|f IH]; intros fuel' i j H Hle; rdin H; [discriminate|].
  destruct fuel' as [|f']; [lia|]. rd.
  destruct (b i =? QUOTE); [exact H|]. destruct (b i =? BACKSLASH); apply IH; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma quote_is_stop : is_ascii_stop QUOTE = true.      Proof. reflexivity. Qed.
Lemma backslash_is_stop : is_ascii_stop BACKSLASH = true. Proof. reflexivity. Qed.
Lemma high_is_stop : forall c, 128 <= c <= 255 -> is_ascii_stop c = true.
Proof.
  intros c Hc. unfold is_ascii_stop, char_class.
  destruct (Z.ltb_spec c 0); [lia|]. destruct (Z.ltb_spec 255 c); [lia|]. cbn [orb].
  destruct (Z.ltb_spec c 32); [lia|]. destruct (Z.eqb_spec c 32); [lia|].
  destruct (Z.eqb_spec c 34); [lia|]. destruct (Z.eqb_spec c 92); [lia|]. cbn [orb].
  destruct ((c =? 44) || (c =? 58) || (c =? 91) || (c =? 93) || (c =? 123) || (c =? 125))%bool eqn:E.
  { exfalso. repeat (apply Bool.orb_true_iff in E as [E|E]); apply Z.eqb_eq in E; lia. }
  destruct (Z.ltb_spec c 128); [lia|]. reflexivity.
Qed.

Lemma stoprun_skips : forall fuel idx k, idx <= k < stoprun fuel idx -> is_ascii_stop (b k) = false.
Proof.
  induction fuel as [|f IH]; intros idx k Hk; rdin Hk; [lia|].
  destruct (is_ascii_stop (b idx)) eqn:Hs; [lia|].
  destruct (Z.eq_dec k idx) as [->|]; [exact Hs|].
  destruct (idx + 1 <? len); [|lia]. apply (IH (idx + 1)). lia.
Qed.

Lemma qsearch_skip : forall fuel i j, i <= j -> (forall k, i <= k < j -> is_ascii_stop (b k) = false) ->
  forall r, qsearch fuel j = r -> qsearch (fuel + Z.to_nat (j - i)) i = r.
Proof.
  intros fuel i j Hij Hskip.
  remember (Z.to_nat (j - i)) as d eqn:Hd. revert i j Hij Hskip Hd.
  induction d as [|d IH]; intros i j Hij Hskip Hd r Hr.
  - assert (i = j) as -> by lia. rewrite Nat.add_0_r. exact Hr.
  - rewrite Nat.add_succ_r. rd.
    assert (Hi : is_ascii_stop (b i) = false) by (apply Hskip; lia).
    destruct (Z.eqb_spec (b i) QUOTE) as [E|]; [rewrite E, quote_is_stop in Hi; discriminate|].
    destruct (Z.eqb_spec (b i) BACKSLASH) as [E|]; [rewrite E, backslash_is_stop in Hi; discriminate|].
    apply (IH (i + 1) j); [lia| intros k Hk; apply Hskip; lia | lia | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma is_cont_not_quote : forall c, is_cont c = true -> c <> QUOTE /\ c <> BACKSLASH.
Proof.
  intros c H. unfold is_cont in H. apply Z.eqb_eq in H. unfold QUOTE, BACKSLASH. split; intros ->; cbv in H; discriminate.
Qed.

(* [comment removed for export] *)
Lemma vstring_loop_closed : forall fuel idx err j err',
  vstring_loop fuel idx err = (j, err', false) -> 0 <= idx ->
  (forall k, 0 <= k -> 0 <= b k <= 255) ->
  j < len /\ b j = QUOTE /\ exists fq, qsearch fq idx = Some j.
Proof.
  induction fuel as [|f IH]; intros idx err j err' H Hidx Hb; rdin H; [discriminate|].
  destruct (Z.ltb_spec idx len) as [Hlt|]; [|discriminate].
  pose proof (stoprun_ge (Z.to_nat (len - idx)) idx) as Hge.
  pose proof (stoprun_skips (Z.to_nat (len - idx)) idx) as Hsk.
  set (i := stoprun (Z.to_nat (len - idx)) idx) in *.
  destruct (Z.leb_spec len i) as [|Hil]; [discriminate|].
  destruct (Z.eqb_spec (b i) QUOTE) as [Eq|Nq].
  { injection H as <- <-. split; [exact Hil|]. split; [exact Eq|].
    exists (1 + Z.to_nat (i - idx))%nat. apply (qsearch_skip 1 idx i Hge Hsk). rd. rewrite (proj2 (Z.eqb_eq _ _) Eq). reflexivity. }
  destruct (Z.eqb_spec (b i) BACKSLASH) as [Eb|Nb].
  { destruct (IH (i + 2) err j err' H ltac:(lia) Hb) as (Hj & Hq & [fq Hfq]). split; [exact Hj|]. split; [exact Hq|].
    exists (S fq + Z.to_nat (i - idx))%nat. apply (qsearch_skip (S fq) idx i Hge Hsk). rd.
    rewrite (proj2 (Z.eqb_neq _ _) Nq). rewrite (proj2 (Z.eqb_eq _ _) Eb). exact Hfq. }
  destruct (negb (Z.land (b i) 128 =? 0)) eqn:Hhi.
  { destruct (vutf8 i err) as [i' e'] eqn:Hv.
    destruct (IH i' e' j err' H ltac:(pose proof (vutf8_gt i err) as X; rewrite Hv in X; rdin X; lia) Hb) as (Hj & Hq & [fq Hfq]).
    split; [exact Hj|]. split; [exact Hq|].
    (* [comment removed for export] *)
    assert (Hstep : forall fq', qsearch fq' i' = Some j -> exists fq'', qsearch fq'' i = Some j).
    { intros fq' Hfq'. unfold vutf8 in Hv.
      assert (C1 : forall k fq1, is_cont (b k) = true -> qsearch fq1 (k + 1) = Some j -> qsearch (S fq1) k = Some j).
      { intros k fq1 Hc Hs. rd. destruct (is_cont_not_quote _ Hc) as [A B].
        rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.eqb_neq _ _) B). exact Hs. }
      assert (C0 : forall fq1, qsearch fq1 (i + 1) = Some j -> qsearch (S fq1) i = Some j).
      { intros fq1 Hs. rd. rewrite (proj2 (Z.eqb_neq _ _) Nq), (proj2 (Z.eqb_neq _ _) Nb). exact Hs. }
      repeat match type of Hv with
      | context [if ?c then _ else _] => destruct c eqn:?
      end; injection Hv as <- <-;
      repeat match goal with
      | Hc : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in Hc as [? ?]
      end;
      repeat match goal with
      | Hn : negb (is_cont _) = false |- _ => apply Bool.negb_false_iff in Hn
      end;
      first
      [ exists (S fq'); apply C0; exact Hfq'
      | exists (2%nat + fq')%nat; apply C0; apply (C1 (i + 1)); [assumption|];
        replace (i + 1 + 1) with (i + 2) by lia; exact Hfq'
      | exists (3%nat + fq')%nat; apply C0; apply (C1 (i + 1)); [assumption|];
        apply (C1 (i + 1 + 1)); [replace (i + 1 + 1) with (i + 2) by lia; assumption|];
        replace (i + 1 + 1 + 1) with (i + 3) by lia; exact Hfq'
      | exists (4%nat + fq')%nat; apply C0; apply (C1 (i + 1)); [assumption|];
        apply (C1 (i + 1 + 1)); [replace (i + 1 + 1) with (i + 2) by lia; assumption|];
        apply (C1 (i + 1 + 1 + 1)); [replace (i + 1 + 1 + 1) with (i + 3) by lia; assumption|];
        replace (i + 1 + 1 + 1 + 1) with (i + 4) by lia; exact Hfq' ]. }
    destruct (Hstep fq Hfq) as [fq'' Hfq''].
    exists (fq'' + Z.to_nat (i - idx))%nat. apply (qsearch_skip fq'' idx i Hge Hsk). exact Hfq''. }
  destruct (IH (i + 1) _ j err' H ltac:(lia) Hb) as (Hj & Hq & [fq Hfq]). split; [exact Hj|]. split; [exact Hq|].
  exists (S fq + Z.to_nat (i - idx))%nat. apply (qsearch_skip (S fq) idx i Hge Hsk). rd.
  rewrite (proj2 (Z.eqb_neq _ _) Nq), (proj2 (Z.eqb_neq _ _) Nb). exact Hfq.
Qed.

Theorem vstring_closed : forall q err j err',
  vstring q err = (j, err', false) -> 0 <= q -> (forall k, 0 <= k -> 0 <= b k <= 255) ->
  q < j < len /\ b j = QUOTE /\ exists fq, qsearch fq (q + 1) = Some j.
Proof.
  intros q err j err' H Hq Hb. unfold vstring in H.
  destruct (vstring_loop_closed _ _ _ _ _ H ltac:(lia) Hb) as (A & B & [fq C]).
  pose proof (qsearch_ge _ _ _ C). split; [lia|]. split; [exact B|]. exists fq; exact C.
Qed.


(* [comment removed for export] *)
Definition strings_ok (s : st) : Prop :=
  s_unclosed s = false ->
  forall x, In x (s_out s) -> b x = QUOTE ->
    exists j fq, x < j < len /\ b j = QUOTE /\ qsearch fq (x + 1) = Some j /\ j < s_idx s.

Lemma is_op_not_quote : forall c, is_op c = true -> c <> QUOTE.
Proof. intros c H ->. cbv in H. discriminate. Qed.

Hypothesis bytes_range : forall k, 0 <= k -> 0 <= b k <= 255.

Lemma strings_ok_iter : forall s, wf s -> strings_ok s -> s_idx s < len -> strings_ok (iter s).
Proof.
  intros [idx out err u] Hwf Hok Hlt. unfold iter, strings_ok in *. cbn [s_idx s_out s_err s_unclosed] in *.
  pose proof (wsrun_ge (Z.to_nat (len - idx)) idx) as Hw. set (i := wsrun _ idx) in *.
  destruct Hwf as (H0 & _ & Hin). cbn [s_idx s_out] in H0, Hin.
  Ltac fin := cbn [s_idx s_out s_err s_unclosed] in *; repeat split; first [assumption | lia].
  destruct (Z.leb_spec len i).
  { cbn [s_idx s_out s_err s_unclosed]. intros Hu x Hx Hq. destruct (Hok Hu x Hx Hq) as (j & fq & A & B & C & D). exists j, fq. fin. }
  destruct (Z.eqb_spec (b i) QUOTE) as [Eq|Nq].
  { destruct (vstring i err) as [[i' err'] u'] eqn:Hv. cbn [s_unclosed s_out s_idx]. intros Hu x Hx Hq.
    apply Bool.orb_false_iff in Hu as [Hu Hu']. subst u'.
    assert (G : i + 1 <= i' \/ len <= i').
    { unfold vstring in Hv. pose proof (vstring_loop_ge (Z.to_nat (len + 2)) (i + 1) err) as G. rewrite Hv in G. cbn in G. exact G. }
    destruct (vstring_closed _ _ _ _ Hv ltac:(lia) bytes_range) as (A' & B' & [fq' C']).
    apply in_app_iff in Hx as [Hx|[<-|[]]].
    - destruct (Hok Hu x Hx Hq) as (j & fq & A & B & C & D). exists j, fq. fin.
    - exists i', fq'. fin. }
  destruct (is_op (b i)) eqn:Hop.
  { cbn [s_unclosed s_out s_idx]. intros Hu x Hx Hq. apply in_app_iff in Hx as [Hx|[<-|[]]].
    - destruct (Hok Hu x Hx Hq) as (j & fq & A & B & C & D). exists j, fq. fin.
    - exfalso. exact (is_op_not_quote _ Hop Hq). }
  cbn [s_unclosed s_out s_idx]. intros Hu x Hx Hq. apply in_app_iff in Hx as [Hx|[<-|[]]].
  - destruct (Hok Hu x Hx Hq) as (j & fq & A & B & C & D). exists j, fq. pose proof (primrun_ge (Z.to_nat (len - i)) i). fin.
  - exfalso. exact (Nq Hq).
Qed.

Lemma strings_ok_reach : forall s, reach s -> strings_ok s.
Proof.
  intros s Hr. induction Hr as [|s Hr IH Hlt].
  - intros _ x [].
  - apply strings_ok_iter; [apply wf_reach; exact Hr | exact IH | exact Hlt].
Qed.

(* [comment removed for export] *)
Definition strings_next (s : st) : Prop :=
  s_unclosed s = false ->
  forall i, (S i <= length (s_out s))%nat -> b (nth i (s_out s) 0) = QUOTE ->
    exists j fq, nth i (s_out s) 0 < j < len /\ b j = QUOTE /\ qsearch fq (nth i (s_out s) 0 + 1) = Some j /\
      j < s_idx s /\ ((S i < length (s_out s))%nat -> j < nth (S i) (s_out s) 0).

Lemma nth_app_last : forall (l : list Z) x i, (i < length l)%nat -> nth i (l ++ [x]) 0 = nth i l 0.
Proof. intros. apply app_nth1. assumption. Qed.
Lemma nth_app_new : forall (l : list Z) x, nth (length l) (l ++ [x]) 0 = x.
Proof. intros. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma strings_next_push : forall idx out err u i idx' err',
  strings_next (ST idx out err u) -> idx <= i -> i < idx' ->
  (b i = QUOTE -> exists j fq, i < j < len /\ b j = QUOTE /\ qsearch fq (i + 1) = Some j /\ j < idx') ->
  strings_next (ST idx' (out ++ [i]) err' u).
Proof.
  intros idx out err u i idx' err' Hok Hle Hlt Hnew. unfold strings_next in *. cbn [s_unclosed s_out s_idx] in *.
  intros Hu k Hk Hq. rewrite length_app in Hk. cbn [length] in Hk.
  destruct (Nat.lt_ge_cases k (length out)) as [Hko|Hko].
  - rewrite nth_app_last in Hq |- * by exact Hko.
    destruct (Hok Hu k ltac:(lia) Hq) as (j & fq & A & B & C & D & E). exists j, fq.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [lia|].
    intros Hk2. rewrite length_app in Hk2. cbn [length] in Hk2.
    destruct (Nat.lt_ge_cases (S k) (length out)) as [Hs|Hs].
    + rewrite nth_app_last by exact Hs. apply E. exact Hs.
    + assert (S k = length out) as -> by lia. rewrite nth_app_new. lia.
  - assert (k = length out) as -> by lia. rewrite nth_app_new in Hq |- *.
    destruct (Hnew Hq) as (j & fq & A & B & C & D). exists j, fq.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
    intros Hk2. rewrite length_app in Hk2. cbn [length] in Hk2. lia.
Qed.

Lemma strings_next_iter : forall s, wf s -> strings_next s -> s_idx s < len -> strings_next (iter s).
Proof.
  intros [idx out err u] Hwf Hok Hlt. unfold iter. cbn [s_idx s_out s_err s_unclosed].
  pose proof (wsrun_ge (Z.to_nat (len - idx)) idx) as Hw. set (i := wsrun _ idx) in *.
  destruct Hwf as (H0 & _ & Hin). cbn [s_idx s_out] in H0, Hin.
  destruct (Z.leb_spec len i).
  { unfold strings_next in *. cbn [s_idx s_out s_err s_unclosed] in *. intros Hu k Hk Hq.
    destruct (Hok Hu k Hk Hq) as (j & fq & A & B & C & D & E). exists j, fq. repeat split; try assumption; lia. }
  destruct (Z.eqb_spec (b i) QUOTE) as [Eq|Nq].
  { destruct (vstring i err) as [[i' err'] u'] eqn:Hv.
    destruct u'.
    { (* [comment removed for export] *)
      unfold strings_next. cbn [s_unclosed s_out s_idx]. intros Hu. rewrite Bool.orb_true_r in Hu. discriminate. }
    rewrite Bool.orb_false_r.
    destruct (vstring_closed _ _ _ _ Hv ltac:(lia) bytes_range) as (A' & B' & [fq' C']).
    apply (strings_next_push idx out err u i (i' + 1) err'); [exact Hok | lia | lia |].
    intros _. exists i', fq'. repeat split; try assumption; lia. }
  destruct (is_op (b i)) eqn:Hop.
  { apply (strings_next_push idx out err u i (i + 1) err); [exact Hok | lia | lia |]. intros Hq. exfalso. exact (Nq Hq). }
  pose proof (primrun_ge (Z.to_nat (len - i)) i).
  apply (strings_next_push idx out err u i (primrun (Z.to_nat (len - i)) i + 1) err); [exact Hok | lia | lia |].
  intros Hq. exfalso. exact (Nq Hq).
Qed.

Lemma strings_next_reach : forall s, reach s -> strings_next s.
Proof.
  intros s Hr. induction Hr as [|s Hr IH Hlt].
  - intros _ i Hi. cbn in Hi. lia.
  - apply strings_next_iter; [apply wf_reach; exact Hr | exact IH | exact Hlt].
Qed.

(* [comment removed for export] *)
Theorem string_next : snd result = SUCCESS ->
  forall i, (S i <= length (fst result))%nat -> b (nth i (fst result) 0) = QUOTE ->
  exists j fq, nth i (fst result) 0 < j < len /\ b j = QUOTE /\ qsearch fq (nth i (fst result) 0 + 1) = Some j /\
    ((S i < length (fst result))%nat -> j < nth (S i) (fst result) 0).
Proof.
  unfold result. intros Hs i Hi Hq.
  pose proof (strings_next_reach final final_reach) as Hok.
  destruct (Z.of_nat (length (s_out final)) =? 0); cbn [fst snd] in Hs, Hi, Hq |- *.
  { exfalso. cbv in Hs. discriminate. }
  destruct (s_unclosed final) eqn:Hu; [exfalso; cbv in Hs; discriminate|].
  destruct (Hok Hu i Hi Hq) as (j & fq & A & B & C & D & E). exists j, fq. repeat split; first [assumption | lia].
Qed.

(* [comment removed for export] *)
Theorem strings_closed : snd result = SUCCESS ->
  forall x, In x (fst result) -> b x = QUOTE ->
  exists j fq, x < j < len /\ b j = QUOTE /\ qsearch fq (x + 1) = Some j.
Proof.
  unfold result. intros Hs x Hx Hq.
  pose proof (strings_ok_reach final final_reach) as Hok.
  destruct (Z.of_nat (length (s_out final)) =? 0); cbn [fst snd] in Hs, Hx.
  { exfalso. cbv in Hs. discriminate. }
  destruct (s_unclosed final) eqn:Hu; [exfalso; cbv in Hs; discriminate|].
  destruct (Hok Hu x Hx Hq) as (j & fq & A & B & C & D). exists j, fq. repeat split; first [assumption | lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wsrun_fuel : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (f <= f')%nat -> wsrun f' idx = wsrun f idx.
Proof.
  induction f as [|f IH]; intros f' idx Hf Hle; [lia|]. destruct f' as [|f']; [lia|]. rd.
  destruct (is_space (b idx)); [|reflexivity]. destruct (Z.ltb_spec (idx + 1) len); [|reflexivity].
  apply IH; lia.
Qed.
Lemma stoprun_fuel : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (f <= f')%nat -> stoprun f' idx = stoprun f idx.
Proof.
  induction f as [|f IH]; intros f' idx Hf Hle; [lia|]. destruct f' as [|f']; [lia|]. rd.
  destruct (is_ascii_stop (b idx)); [reflexivity|]. destruct (Z.ltb_spec (idx + 1) len); [|reflexivity].
  apply IH; lia.
Qed.
Lemma primrun_fuel : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (f <= f')%nat -> primrun f' idx = primrun f idx.
Proof.
  induction f as [|f IH]; intros f' idx Hf Hle; [lia|]. destruct f' as [|f']; [lia|]. rd.
  destruct (Z.ltb_spec (idx + 1) len); rd; [|reflexivity].
  destruct (negb (is_space_or_op (b (idx + 1))) && negb (b (idx + 1) =? RS))%bool; [|reflexivity]. apply IH; lia.
Qed.
Lemma vstring_loop_fuel : forall f f' idx err, (Z.to_nat (len - idx) < f)%nat -> (f <= f')%nat ->
  vstring_loop f' idx err = vstring_loop f idx err.
Proof.
  induction f as [|f IH]; intros f' idx err Hf Hle; [lia|]. destruct f' as [|f']; [lia|]. rd.
  destruct (Z.ltb_spec idx len); [|reflexivity].
  pose proof (stoprun_ge (Z.to_nat (len - idx)) idx) as Hge. set (i := stoprun _ idx) in *.
  destruct (Z.leb_spec len i); [reflexivity|]. destruct (b i =? QUOTE); [reflexivity|].
  destruct (b i =? BACKSLASH); [apply IH; lia|].
  destruct (negb (Z.land (b i) 128 =? 0)).
  - destruct (vutf8 i err) as [i' e'] eqn:Hv. pose proof (vutf8_gt i err) as G. rewrite Hv in G. cbn in G. apply IH; lia.
  - apply IH; lia.
Qed.
(* [comment removed for export] *)
Lemma wsrun_fuel2 : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (Z.to_nat (len - idx) < f')%nat -> wsrun f idx = wsrun f' idx.
Proof. intros. destruct (Nat.le_ge_cases f f'); [symmetry; apply wsrun_fuel; lia | apply wsrun_fuel; lia]. Qed.
Lemma stoprun_fuel2 : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (Z.to_nat (len - idx) < f')%nat -> stoprun f idx = stoprun f' idx.
Proof. intros. destruct (Nat.le_ge_cases f f'); [symmetry; apply stoprun_fuel; lia | apply stoprun_fuel; lia]. Qed.
Lemma primrun_fuel2 : forall f f' idx, (Z.to_nat (len - idx) < f)%nat -> (Z.to_nat (len - idx) < f')%nat -> primrun f idx = primrun f' idx.
Proof. intros. destruct (Nat.le_ge_cases f f'); [symmetry; apply primrun_fuel; lia | apply primrun_fuel; lia]. Qed.
Lemma vstring_loop_fuel2 : forall f f' idx err, (Z.to_nat (len - idx) < f)%nat -> (Z.to_nat (len - idx) < f')%nat ->
  vstring_loop f idx err = vstring_loop f' idx err.
Proof. intros. destruct (Nat.le_ge_cases f f'); [symmetry; apply vstring_loop_fuel; lia | apply vstring_loop_fuel; lia]. Qed.

(* [comment removed for export] *)
Inductive ws_pos (i0 : Z) : Z -> Prop :=
| ws_here : i0 < len -> ws_pos i0 i0
| ws_next : forall J, ws_pos i0 J -> is_space (b J) = true -> J + 1 < len -> ws_pos i0 (J + 1).
Lemma ws_pos_lt : forall i0 J, ws_pos i0 J -> i0 <= J < len.
Proof. intros i0 J H. induction H; lia. Qed.
(* [comment removed for export] *)
Lemma ws_pos_run : forall i0 J, ws_pos i0 J -> forall f, wsrun (Z.to_nat (J - i0) + f) i0 = wsrun f J.
Proof.
  intros i0 J H. induction H as [Hi0|J H IH Hs Hlt]; intros f.
  - rewrite Z.sub_diag. reflexivity.
  - pose proof (ws_pos_lt _ _ H). replace (Z.to_nat (J + 1 - i0) + f)%nat with (Z.to_nat (J - i0) + S f)%nat by lia.
    rewrite (IH (S f)). rd. rewrite Hs. destruct (Z.ltb_spec (J + 1) len); [reflexivity | lia].
Qed.
(* [comment removed for export] *)
Lemma ws_pos_stop : forall i0 J, ws_pos i0 J -> is_space (b J) = false ->
  forall f, (Z.to_nat (J - i0) < f)%nat -> wsrun f i0 = J.
Proof.
  intros i0 J H Hs f Hf. replace f with (Z.to_nat (J - i0) + S (f - Z.to_nat (J - i0) - 1))%nat by lia.
  rewrite (ws_pos_run i0 J H). rd. rewrite Hs. reflexivity.
Qed.
Lemma ws_pos_end : forall i0 J, ws_pos i0 J -> is_space (b J) = true -> len <= J + 1 ->
  forall f, (Z.to_nat (J - i0) < f)%nat -> wsrun f i0 = J + 1.
Proof.
  intros i0 J H Hs Hle f Hf. replace f with (Z.to_nat (J - i0) + S (f - Z.to_nat (J - i0) - 1))%nat by lia.
  rewrite (ws_pos_run i0 J H). rd. rewrite Hs. destruct (Z.ltb_spec (J + 1) len); [lia | reflexivity].
Qed.

(* [comment removed for export] *)
Inductive stop_pos (i0 : Z) : Z -> Prop :=
| stop_here : i0 < len -> stop_pos i0 i0
| stop_next : forall J, stop_pos i0 J -> is_ascii_stop (b J) = false -> J + 1 < len -> stop_pos i0 (J + 1).
Lemma stop_pos_lt : forall i0 J, stop_pos i0 J -> i0 <= J < len.
Proof. intros i0 J H. induction H; lia. Qed.
Lemma stop_pos_run : forall i0 J, stop_pos i0 J -> forall f, stoprun (Z.to_nat (J - i0) + f) i0 = stoprun f J.
Proof.
  intros i0 J H. induction H as [Hi0|J H IH Hs Hlt]; intros f.
  - rewrite Z.sub_diag. reflexivity.
  - pose proof (stop_pos_lt _ _ H). replace (Z.to_nat (J + 1 - i0) + f)%nat with (Z.to_nat (J - i0) + S f)%nat by lia.
    rewrite (IH (S f)). rd. rewrite Hs. destruct (Z.ltb_spec (J + 1) len); [reflexivity | lia].
Qed.
Lemma stop_pos_stop : forall i0 J, stop_pos i0 J -> is_ascii_stop (b J) = true ->
  forall f, (Z.to_nat (J - i0) < f)%nat -> stoprun f i0 = J.
Proof.
  intros i0 J H Hs f Hf. replace f with (Z.to_nat (J - i0) + S (f - Z.to_nat (J - i0) - 1))%nat by lia.
  rewrite (stop_pos_run i0 J H). rd. rewrite Hs. reflexivity.
Qed.
Lemma stop_pos_end : forall i0 J, stop_pos i0 J -> is_ascii_stop (b J) = false -> len <= J + 1 ->
  forall f, (Z.to_nat (J - i0) < f)%nat -> stoprun f i0 = J + 1.
Proof.
  intros i0 J H Hs Hle f Hf. replace f with (Z.to_nat (J - i0) + S (f - Z.to_nat (J - i0) - 1))%nat by lia.
  rewrite (stop_pos_run i0 J H). rd. rewrite Hs. destruct (Z.ltb_spec (J + 1) len); [lia | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma stop_pos_skips : forall i0 J, stop_pos i0 J -> forall k, i0 <= k < J -> is_ascii_stop (b k) = false.
Proof.
  intros i0 J H. induction H as [Hi0|J H IH Hs Hlt]; intros k Hk; [lia|].
  destruct (Z.eq_dec k J) as [->|]; [exact Hs | apply IH; lia].
Qed.

(* [comment removed for export] *)
Inductive prim_pos (i : Z) : Z -> Prop :=
| prim_here : prim_pos i i
| prim_next : forall J, prim_pos i J -> J + 1 < len -> is_space_or_op (b (J + 1)) = false -> b (J + 1) <> RS -> prim_pos i (J + 1).
Lemma prim_pos_le : forall i J, prim_pos i J -> i <= J.
Proof. intros i J H. induction H; lia. Qed.
Lemma prim_pos_run : forall i J, prim_pos i J -> forall f, primrun (Z.to_nat (J - i) + f) i = primrun f J.
Proof.
  intros i J H. induction H as [|J H IH Hlt Hso Hrs]; intros f.
  - rewrite Z.sub_diag. reflexivity.
  - pose proof (prim_pos_le _ _ H). replace (Z.to_nat (J + 1 - i) + f)%nat with (Z.to_nat (J - i) + S f)%nat by lia.
    rewrite (IH (S f)). rd. destruct (Z.ltb_spec (J + 1) len); [|lia]. rd.
    rewrite Hso. destruct (Z.eqb_spec (b (J + 1)) RS); [contradiction|]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma prim_pos_stop : forall i J, prim_pos i J ->
  (len <= J + 1 \/ is_space_or_op (b (J + 1)) = true \/ b (J + 1) = RS) ->
  forall f, (Z.to_nat (J - i) < f)%nat -> primrun f i = J.
Proof.
  intros i J H Hstop f Hf. pose proof (prim_pos_le _ _ H).
  replace f with (Z.to_nat (J - i) + S (f - Z.to_nat (J - i) - 1))%nat by lia.
  rewrite (prim_pos_run i J H). rd.
  destruct (Z.ltb_spec (J + 1) len); rd; [|reflexivity].
  destruct Hstop as [Hs|[Hs|Hs]]; [lia | rewrite Hs; reflexivity |].
  rewrite Hs. rewrite Z.eqb_refl. cbn [negb]. rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive str_pos (q err0 : Z) : Z -> Z -> Prop :=
| str_start : str_pos q err0 (q + 1) err0
| str_backslash : forall idx err i, str_pos q err0 idx err -> idx < len -> stop_pos idx i -> is_ascii_stop (b i) = true ->
    b i = BACKSLASH -> str_pos q err0 (i + 2) err
| str_utf8 : forall idx err i, str_pos q err0 idx err -> idx < len -> stop_pos idx i -> is_ascii_stop (b i) = true ->
    b i <> QUOTE -> b i <> BACKSLASH -> negb (Z.land (b i) 128 =? 0) = true ->
    str_pos q err0 (fst (vutf8 i err)) (snd (vutf8 i err))
| str_ascii : forall idx err i, str_pos q err0 idx err -> idx < len -> stop_pos idx i -> is_ascii_stop (b i) = true ->
    b i <> QUOTE -> b i <> BACKSLASH -> negb (Z.land (b i) 128 =? 0) = false ->
    str_pos q err0 (i + 1) (if b i <? 32 then UNESCAPED_CHARS else err).

Lemma str_pos_gt : forall q err0 idx err, str_pos q err0 idx err -> q < idx.
Proof.
  intros q err0 idx err H.
  induction H as [|idx err i H IH Hlt HP Hs Hb|idx err i H IH Hlt HP Hs Hq Hb Hhi|idx err i H IH Hlt HP Hs Hq Hb Hhi]; [lia| | |];
    pose proof (stop_pos_lt _ _ HP); [lia| |lia].
  pose proof (vutf8_gt i err). lia.
Qed.

(* [comment removed for export] *)
Lemma vstring_loop_unfold : forall f idx err i, idx < len -> stop_pos idx i -> is_ascii_stop (b i) = true ->
  vstring_loop (S f) idx err =
    (if b i =? QUOTE then (i, err, false)
     else if b i =? BACKSLASH then vstring_loop f (i + 2) err
     else if negb (Z.land (b i) 128 =? 0) then (let '(i', err') := vutf8 i err in vstring_loop f i' err')
     else vstring_loop f (i + 1) (if b i <? 32 then UNESCAPED_CHARS else err)).
Proof.
  intros f idx err i Hlt HP Hs. pose proof (stop_pos_lt _ _ HP). rd.
  destruct (Z.ltb_spec idx len); [|lia].
  rewrite (stop_pos_stop idx i HP Hs (Z.to_nat (len - idx))) by lia.
  destruct (Z.leb_spec len i); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma str_pos_sim : forall q err0 idx err, str_pos q err0 idx err ->
  forall f f', (Z.to_nat (len - (q + 1)) < f)%nat -> (Z.to_nat (len - idx) < f')%nat ->
  vstring_loop f (q + 1) err0 = vstring_loop f' idx err.
Proof.
  intros q err0 idx err H.
  induction H as [|idx err i H IH Hlt HP Hs Hb|idx err i H IH Hlt HP Hs Hq Hb Hhi|idx err i H IH Hlt HP Hs Hq Hb Hhi];
    intros f f' Hf Hf'.
  - apply vstring_loop_fuel2; assumption.
  - pose proof (stop_pos_lt _ _ HP).
    rewrite (IH f (S (Z.to_nat (len - idx))) Hf ltac:(lia)).
    rewrite (vstring_loop_unfold _ idx err i Hlt HP Hs).
    rewrite Hb. cbn [Z.eqb QUOTE BACKSLASH Pos.eqb]. apply vstring_loop_fuel2; lia.
  - pose proof (stop_pos_lt _ _ HP). pose proof (vutf8_gt i err) as G.
    rewrite (IH f (S (Z.to_nat (len - idx))) Hf ltac:(lia)).
    rewrite (vstring_loop_unfold _ idx err i Hlt HP Hs).
    rewrite (proj2 (Z.eqb_neq _ _) Hq), (proj2 (Z.eqb_neq _ _) Hb), Hhi.
    destruct (vutf8 i err) as [i' e'] eqn:Hv. cbn [fst snd] in *. apply vstring_loop_fuel2; lia.
  - pose proof (stop_pos_lt _ _ HP).
    rewrite (IH f (S (Z.to_nat (len - idx))) Hf ltac:(lia)).
    rewrite (vstring_loop_unfold _ idx err i Hlt HP Hs).
    rewrite (proj2 (Z.eqb_neq _ _) Hq), (proj2 (Z.eqb_neq _ _) Hb), Hhi. apply vstring_loop_fuel2; lia.
Qed.


(* [comment removed for export] *)
Lemma iter_gt : forall s, s_idx s < len -> s_idx s < s_idx (iter s).
Proof.
  intros [idx out err u] Hidx. cbn [s_idx] in Hidx. unfold iter. cbn [s_idx s_out s_err s_unclosed].
  pose proof (wsrun_ge (Z.to_nat (len - idx)) idx) as Hw. set (i := wsrun _ idx) in *.
  destruct (Z.leb_spec len i); cbn [s_idx]; [lia|].
  destruct (b i =? QUOTE).
  - destruct (vstring i err) as [[i' e'] u'] eqn:Hv. cbn [s_idx].
    unfold vstring in Hv. pose proof (vstring_loop_ge (Z.to_nat (len + 2)) (i + 1) err) as G. rewrite Hv in G. cbn in G. lia.
  - destruct (is_op (b i)); cbn [s_idx]; [lia|]. pose proof (primrun_ge (Z.to_nat (len - i)) i). lia.
Qed.

Section Iteration.
Variable s : st.
Hypothesis Hs : reach s.
Hypothesis Hlt : s_idx s < len.
Let i0 := s_idx s.
Let Hi0 : 0 <= s_idx s := proj1 (wf_reach s Hs).

(* [comment removed for export] *)
Lemma iter_ws_end : forall J, ws_pos i0 J -> is_space (b J) = true -> len <= J + 1 ->
  iter s = ST (J + 1) (s_out s) (s_err s) (s_unclosed s).
Proof.
  intros J HW Hsp Hle. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW). unfold iter. fold i0.
  rewrite (ws_pos_end i0 J HW Hsp Hle) by lia. destruct (Z.leb_spec len (J + 1)); [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma iter_operator : forall J, ws_pos i0 J -> is_space (b J) = false -> b J <> QUOTE -> is_op (b J) = true ->
  iter s = ST (J + 1) (s_out s ++ [J]) (s_err s) (s_unclosed s).
Proof.
  intros J HW Hsp Hq Hop. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW). unfold iter. fold i0.
  rewrite (ws_pos_stop i0 J HW Hsp) by lia. destruct (Z.leb_spec len J); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) Hq), Hop. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iter_primitive : forall J J', ws_pos i0 J -> is_space (b J) = false -> b J <> QUOTE -> is_op (b J) = false ->
  prim_pos J J' -> (len <= J' + 1 \/ is_space_or_op (b (J' + 1)) = true \/ b (J' + 1) = RS) ->
  iter s = ST (J' + 1) (s_out s ++ [J]) (s_err s) (s_unclosed s).
Proof.
  intros J J' HW Hsp Hq Hop HP Hstop. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW). pose proof (prim_pos_le _ _ HP). unfold iter. fold i0.
  rewrite (ws_pos_stop i0 J HW Hsp) by lia. destruct (Z.leb_spec len J); [lia|].
  rewrite (proj2 (Z.eqb_neq _ _) Hq), Hop.
  assert (HJ' : J' < len).
  { inversion HP; [lia|]. lia. }
  rewrite (prim_pos_stop J J' HP Hstop) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iter_string_closed : forall J idx err j, ws_pos i0 J -> is_space (b J) = false -> b J = QUOTE ->
  str_pos J (s_err s) idx err -> idx < len -> stop_pos idx j -> b j = QUOTE ->
  iter s = ST (j + 1) (s_out s ++ [J]) err (s_unclosed s).
Proof.
  intros J idx err j HW Hsp Hq HS Hidx HP Hj. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW). pose proof (stop_pos_lt _ _ HP).
  unfold iter. fold i0. rewrite (ws_pos_stop i0 J HW Hsp) by lia. destruct (Z.leb_spec len J); [lia|].
  rewrite Hq, Z.eqb_refl. unfold vstring.
  rewrite (str_pos_sim J (s_err s) idx err HS (Z.to_nat (len + 2)) (S (Z.to_nat (len - idx)))) by lia.
  rewrite (vstring_loop_unfold _ idx err j Hidx HP ltac:(rewrite Hj; apply quote_is_stop)).
  rewrite Hj, Z.eqb_refl. rewrite Bool.orb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iter_string_unclosed_end : forall J idx err, ws_pos i0 J -> is_space (b J) = false -> b J = QUOTE ->
  str_pos J (s_err s) idx err -> len <= idx ->
  iter s = ST (idx + 1) (s_out s ++ [J]) err true.
Proof.
  intros J idx err HW Hsp Hq HS Hidx. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW).
  unfold iter. fold i0. rewrite (ws_pos_stop i0 J HW Hsp) by lia. destruct (Z.leb_spec len J); [lia|].
  rewrite Hq, Z.eqb_refl. unfold vstring.
  rewrite (str_pos_sim J (s_err s) idx err HS (Z.to_nat (len + 2)) (S (Z.to_nat (len - idx)))) by lia.
  rd. destruct (Z.ltb_spec idx len); [lia|]. rewrite Bool.orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iter_string_unclosed_run : forall J idx err j, ws_pos i0 J -> is_space (b J) = false -> b J = QUOTE ->
  str_pos J (s_err s) idx err -> idx < len -> stop_pos idx j -> is_ascii_stop (b j) = false -> len <= j + 1 ->
  iter s = ST (j + 1 + 1) (s_out s ++ [J]) err true.
Proof.
  intros J idx err j HW Hsp Hq HS Hidx HP Hj Hle. pose proof Hi0 as Hi0'. unfold i0 in *. pose proof (ws_pos_lt _ _ HW). pose proof (stop_pos_lt _ _ HP).
  unfold iter. fold i0. rewrite (ws_pos_stop i0 J HW Hsp) by lia. destruct (Z.leb_spec len J); [lia|].
  rewrite Hq, Z.eqb_refl. unfold vstring.
  rewrite (str_pos_sim J (s_err s) idx err HS (Z.to_nat (len + 2)) (S (Z.to_nat (len - idx)))) by lia.
  rd. destruct (Z.ltb_spec idx len); [|lia].
  rewrite (stop_pos_end idx j HP Hj Hle) by lia. destruct (Z.leb_spec len (j + 1)); [|lia].
  rewrite Bool.orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reach_iter : reach (iter s).
Proof. apply reach_step; assumption. Qed.
End Iteration.

(* [comment removed for export] *)
Lemma reach_run : 0 <= len -> forall s, reach s ->
  exists n, Z.of_nat n <= s_idx s /\ Z.of_nat n <= len /\ forall f, run (n + f) init = run f s.
Proof.
  intros Hlen s H. induction H as [|s H IH Hlt].
  - exists 0%nat. cbn. split; [lia|]. split; [lia|]. intros f. reflexivity.
  - destruct IH as (n & Hn & Hnl & Hrun). exists (S n). pose proof (iter_gt s Hlt) as G.
    split; [lia|]. split; [lia|]. intros f. replace (S n + f)%nat with (n + S f)%nat by lia. rewrite Hrun. rd.
    destruct (Z.ltb_spec (s_idx s) len); [reflexivity | lia].
Qed.
Theorem reach_final : 0 <= len -> forall s, reach s -> len <= s_idx s -> final = s.
Proof.
  intros Hlen s H Hge. destruct (reach_run Hlen s H) as (n & Hn & Hnl & Hrun). unfold final.
  replace (Z.to_nat len + 1)%nat with (n + S (Z.to_nat len - n))%nat by lia. rewrite Hrun. rd.
  destruct (Z.ltb_spec (s_idx s) len); [lia | reflexivity].
Qed.

End Scanner.
End S1M.
