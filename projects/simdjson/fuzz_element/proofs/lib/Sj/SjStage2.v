(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorted.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition c_quote  : Z := 34.   Definition c_comma : Z := 44.   Definition c_colon : Z := 58.
Definition c_lbrack : Z := 91.   Definition c_rbrack : Z := 93.  Definition c_lbrace : Z := 123.  Definition c_rbrace : Z := 125.
Definition c_minus  : Z := 45.   Definition c_t : Z := 116.      Definition c_f : Z := 102.        Definition c_n : Z := 110.

Definition is_digit (b : Z) : bool := (48 <=? b) && (b <=? 57).
Definition is_numstart (b : Z) : bool := (b =? c_minus) || is_digit b.
Definition is_atomstart (b : Z) : bool := (b =? c_t) || (b =? c_f) || (b =? c_n).

Section Stage2.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.

  Variables (tape_cap sbuf_cap : Z).
  Hypothesis Htape : blen bs + 3 <= tape_cap.
  Hypothesis Hsbuf : 5 * blen bs + 5 <= 3 * sbuf_cap.

  Definition n : Z := Z.of_nat (length idxs).
  Definition ext : list Z := idxs ++ [blen bs; blen bs; 0].
  Definition off (k : Z) : Z := nth (Z.to_nat k) ext 0.
  Definition tok (k : Z) : Z := B bs (off k).

  Lemma n_pos : 1 <= n.
  Proof. unfold n. pose proof (S1OUT_length_pos _ _ HS). lia. Qed.

  Lemma n_le_len : n <= blen bs.
  Proof. unfold n. apply (S1OUT_length_le _ _ HS). Qed.

  Lemma length_ext : Z.of_nat (length ext) = n + 3.
  Proof. unfold ext, n. rewrite length_app. simpl. lia. Qed.

  Lemma off_idx : forall k, 0 <= k < n -> nth_error idxs (Z.to_nat k) = Some (off k).
  Proof.
    intros k Hk. unfold off, ext, n in *.
    rewrite app_nth1 by lia. apply nth_error_nth'. lia.
  Qed.

  Lemma off_n : off n = blen bs.
  Proof.
    unfold off, ext, n. rewrite Nat2Z.id. rewrite app_nth2 by lia.
    replace (length idxs - length idxs)%nat with 0%nat by lia. reflexivity.
  Qed.

  Lemma off_n1 : off (n + 1) = blen bs.
  Proof.
    unfold off, ext, n. replace (Z.to_nat (Z.of_nat (length idxs) + 1)) with (S (length idxs)) by lia.
    rewrite app_nth2 by lia. replace (S (length idxs) - length idxs)%nat with 1%nat by lia. reflexivity.
  Qed.

  Lemma off_n2 : off (n + 2) = 0.
  Proof.
    unfold off, ext, n. replace (Z.to_nat (Z.of_nat (length idxs) + 2)) with (S (S (length idxs))) by lia.
    rewrite app_nth2 by lia. replace (S (S (length idxs)) - length idxs)%nat with 2%nat by lia. reflexivity.
  Qed.

  Lemma off_lt_len : forall k, 0 <= k < n -> 0 <= off k < blen bs.
  Proof. intros k Hk. eapply S1OUT_nth_range; [exact HS|]. apply off_idx; exact Hk. Qed.

  Lemma off_range : forall k, 0 <= k <= n -> 0 <= off k <= blen bs.
  Proof.
    intros k Hk. destruct (Z.eq_dec k n) as [->|Hne].
    - rewrite off_n. pose proof (blen_nonneg bs). lia.
    - pose proof (off_lt_len k). lia.
  Qed.

  Lemma off_mono : forall a b, 0 <= a -> a < b -> b <= n -> off a < off b.
  Proof.
    intros a b Ha Hab Hb. destruct (Z.eq_dec b n) as [->|Hne].
    - rewrite off_n. apply off_lt_len. lia.
    - eapply (S1OUT_nth_lt _ _ HS (Z.to_nat a) (Z.to_nat b)); [lia| |]; apply off_idx; lia.
  Qed.

  Lemma off_add : forall a c, 0 <= a -> 0 <= c -> a + c <= n -> off a + c <= off (a + c).
  Proof.
    intros a c Ha Hc. pattern c. apply natlike_ind; [| |exact Hc].
    - intros _. replace (a + 0) with a by lia. lia.
    - intros x Hx IH Hle. pose proof (off_mono (a + x) (a + Z.succ x)). lia.
  Qed.

  Lemma tok_n : tok n = 0.
  Proof. unfold tok. rewrite off_n. apply B_pad. lia. Qed.

  Lemma tok_nonzero_lt : forall k, 0 <= k <= n -> tok k <> 0 -> k < n.
  Proof. intros k Hk Hz. destruct (Z.eq_dec k n) as [->|]; [rewrite tok_n in Hz; congruence|lia]. Qed.

  Lemma tok_string : forall k, 0 <= k < n -> tok k = c_quote ->
    exists j, closes bs (off k + 1) j /\ off k < j /\ j < off (k + 1).
  Proof.
    intros k Hk Hq. pose proof (off_idx k Hk) as Hi.
    destruct (S1OUT_string _ _ HS _ _ Hi Hq) as (j & Hc & Hj & Hnext).
    exists j. split; [exact Hc|]. split; [lia|].
    destruct (Z.eq_dec (k + 1) n) as [E|E].
    - rewrite E, off_n. lia.
    - apply Hnext. replace (S (Z.to_nat k)) with (Z.to_nat (k + 1)) by lia. apply off_idx. lia.
  Qed.

  Record st : Type := mkst { k : Z; depth : Z; W : Z; sb : Z; scopes : list (bool * Z) }.

  Inductive label : Type :=
  | DocStart | ObjBegin | ObjField | ObjCont | ScopeEnd | ArrBegin | ArrValue | ArrCont | DocEnd.

  Definition s0 : st := mkst 0 0 1 0 [].

  Definition MAXDEPTH : Z := 1024.

  Definition slackW (l : label) : Z :=
    match l with
    | ObjBegin | ArrBegin => 0
    | DocStart | ArrValue | ObjField => 1
    | ObjCont | ArrCont | ScopeEnd | DocEnd => 2
    end.
  Definition slackS (l : label) : Z :=
    match l with
    | DocStart | ObjBegin | ArrBegin | ArrValue => 0
    | ObjField | ObjCont | ArrCont | ScopeEnd | DocEnd => 5
    end.

  Definition kind_ok (l : label) (sc : list (bool * Z)) : Prop :=
    match l with
    | DocStart | DocEnd => sc = []
    | ObjField | ObjCont => exists ti rest, sc = (false, ti) :: rest
    | ArrValue | ArrCont => exists ti rest, sc = (true, ti) :: rest
    | ScopeEnd => sc <> []
    | ObjBegin | ArrBegin => True
    end.

  Record Inv (l : label) (s : st) : Prop := {
    inv_k      : 0 <= k s <= n;
    inv_W      : 1 <= W s <= k s + slackW l;
    inv_sb     : 0 <= sb s /\ 3 * sb s <= 5 * off (k s) + slackS l;
    inv_depth  : depth s = Z.of_nat (length (scopes s)) /\ depth s < MAXDEPTH;
    inv_scopes : Forall (fun sc => 1 <= snd sc < W s) (scopes s);
    inv_kind   : kind_ok l (scopes s);
  }.

  Ltac ss := cbn [k depth W sb scopes slackW slackS kind_ok snd fst length s0] in *.

  Lemma Inv_s0 : Inv DocStart s0.
  Proof.
    constructor; ss; try lia.
    - pose proof n_pos; lia.
    - split; [lia|]. pose proof (off_range 0). pose proof n_pos. lia.
    - unfold MAXDEPTH; lia.
    - constructor.
    - reflexivity.
  Qed.

  Definition string_ok (t d : Z) : Prop :=
    exists j, closes bs (off t + 1) j /\ 0 <= d <= j - off t - 1.

  Inductive value_step (after : label) (s : st) : label -> st -> Prop :=
  | v_obj_empty : tok (k s) = c_lbrace -> tok (k s + 1) = c_rbrace ->
      value_step after s after (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))
  | v_obj : tok (k s) = c_lbrace -> tok (k s + 1) <> c_rbrace ->
      value_step after s ObjBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))
  | v_arr_empty : tok (k s) = c_lbrack -> tok (k s + 1) = c_rbrack ->
      value_step after s after (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s))
  | v_arr : tok (k s) = c_lbrack -> tok (k s + 1) <> c_rbrack ->
      value_step after s ArrBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))
  | v_string : forall d, tok (k s) = c_quote -> string_ok (k s) d ->
      value_step after s after (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))
  | v_number : is_numstart (tok (k s)) = true ->
      value_step after s after (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))
  | v_atom : is_atomstart (tok (k s)) = true ->
      value_step after s after (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).

  Inductive step : label -> st -> label -> st -> Prop :=
  | st_doc : forall s l' s', value_step DocEnd s l' s' -> step DocStart s l' s'
  | st_obj_begin : forall s d,
      depth s + 1 < MAXDEPTH -> tok (k s) = c_quote -> string_ok (k s) d ->
      step ObjBegin s ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s))
  | st_obj_field : forall s l' s',
      tok (k s) = c_colon ->
      value_step ObjCont (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) l' s' -> step ObjField s l' s'
  | st_obj_cont_comma : forall s d,
      tok (k s) = c_comma -> tok (k s + 1) = c_quote -> string_ok (k s + 1) d ->
      step ObjCont s ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s))
  | st_obj_cont_end : forall s,
      tok (k s) = c_rbrace ->
      step ObjCont s ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))
  | st_scope_end_doc : forall s sc,
      scopes s = [sc] ->
      step ScopeEnd s DocEnd (mkst (k s) (depth s - 1) (W s) (sb s) [])
  | st_scope_end_arr : forall s sc ti rest,
      scopes s = sc :: (true, ti) :: rest ->
      step ScopeEnd s ArrCont (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest))
  | st_scope_end_obj : forall s sc ti rest,
      scopes s = sc :: (false, ti) :: rest ->
      step ScopeEnd s ObjCont (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest))
  | st_arr_begin : forall s,
      depth s + 1 < MAXDEPTH ->
      step ArrBegin s ArrValue (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s))
  | st_arr_value : forall s l' s', value_step ArrCont s l' s' -> step ArrValue s l' s'
  | st_arr_cont_comma : forall s,
      tok (k s) = c_comma ->
      step ArrCont s ArrValue (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))
  | st_arr_cont_end : forall s,
      tok (k s) = c_rbrack ->
      step ArrCont s ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).

  Lemma inv_k_le : forall l s, Inv l s -> 0 <= k s <= n.
  Proof. intros l s H; exact (inv_k _ _ H). Qed.

  Lemma tape_room : forall l s c w, Inv l s -> 0 <= c -> k s + c <= n -> slackW l + w <= c + 3 -> W s + w <= tape_cap.
  Proof.
    intros l s c w H Hc Hk Hw. pose proof (inv_W _ _ H). pose proof n_le_len. lia.
  Qed.

  Lemma tape_room_docend : forall s, Inv DocEnd s -> W s + 1 <= tape_cap.
  Proof. intros s H. apply (tape_room DocEnd s 0 1 H); simpl; try lia. pose proof (inv_k _ _ H). lia. Qed.

  Lemma inv_scope_lt : forall l s isarr ti rest, Inv l s -> scopes s = (isarr, ti) :: rest -> 1 <= ti < W s /\ ti < tape_cap.
  Proof.
    intros l s isarr ti rest H E. pose proof (inv_scopes _ _ H) as Hf. rewrite E in Hf.
    inversion Hf as [|? ? Hh _]; subst. simpl in Hh. split; [exact Hh|].
    pose proof (inv_W _ _ H). pose proof (inv_k _ _ H). pose proof n_le_len. destruct l; simpl in *; lia.
  Qed.

  Lemma inv_depth_push : forall l s, Inv l s -> 0 <= depth s /\ (depth s + 1 < MAXDEPTH -> 1 <= depth s + 1 <= 1023).
  Proof. intros l s H. destruct (inv_depth _ _ H) as [E Hd]. unfold MAXDEPTH in *. lia. Qed.

  Lemma inv_depth_range : forall l s, Inv l s -> 0 <= depth s <= 1023.
  Proof. intros l s H. destruct (inv_depth _ _ H) as [E Hd]. unfold MAXDEPTH in *. lia. Qed.

  Lemma string_pre : forall l s c, Inv l s -> 0 <= c -> k s + c <= n -> slackS l <= 5 * c -> 3 * sb s <= 5 * off (k s + c).
  Proof.
    intros l s c H Hc Hk Hs. destruct (inv_sb _ _ H) as [_ Hsb]. pose proof (inv_k _ _ H).
    pose proof (off_add (k s) c). lia.
  Qed.

  Lemma str_room : forall sbv i j, 0 <= sbv -> 0 <= i -> 3 * sbv <= 5 * i -> i < j -> j < blen bs -> sbv + (j - i) + 4 <= sbuf_cap.
  Proof. intros. lia. Qed.

  Lemma str_post : forall sbv i j d o', 3 * sbv <= 5 * i -> i < j -> j < o' -> 0 <= d <= j - i - 1 -> 3 * (sbv + d + 5) <= 5 * o' + 5.
  Proof. intros. lia. Qed.

  Lemma value_step_inv : forall after s l' s',
    value_step after s l' s' ->
    0 <= k s <= n -> 1 <= W s <= k s + 1 -> 0 <= sb s -> 3 * sb s <= 5 * off (k s) ->
    (depth s = Z.of_nat (length (scopes s)) /\ depth s < MAXDEPTH) ->
    Forall (fun sc => 1 <= snd sc < W s) (scopes s) ->
    kind_ok after (scopes s) -> slackW after = 2 -> slackS after = 5 ->
    Inv l' s'.
  Proof.
    intros after s l' s' Hv Hk HW Hsb0 Hsb Hd Hsc Hkind HsW HsS.
    assert (Hmono : forall w, 0 <= w -> Forall (fun sc => 1 <= snd sc < W s + w) (scopes s)).
    { intros w Hw. eapply Forall_impl; [|exact Hsc]. cbn beta; intros; lia. }
    inversion Hv; subst; clear Hv.
    -
      assert (k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_lbrace in *; lia).
      assert (k s + 1 < n) by (apply tok_nonzero_lt; [lia|]; unfold c_rbrace in *; lia).
      pose proof (off_add (k s) 2).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
    -
      assert (k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_lbrace in *; lia).
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | exact Hsc | exact I].
    -
      assert (k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_lbrack in *; lia).
      assert (k s + 1 < n) by (apply tok_nonzero_lt; [lia|]; unfold c_rbrack in *; lia).
      pose proof (off_add (k s) 2).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
    -
      assert (k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_lbrack in *; lia).
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | exact Hsc | exact I].
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_quote in *; lia).
      match goal with Hso : string_ok _ _ |- _ => destruct Hso as (j & Hc & Hdd) end.
      destruct (tok_string (k s)) as (j' & Hc' & Hj1 & Hj2); [lia|assumption|].
      assert (j = j') by (eapply closes_det; eauto). subst j'.
      pose proof (off_range (k s)).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
    -
      assert (Hlt : k s < n).
      { apply tok_nonzero_lt; [lia|]. intro E.
        match goal with Hn : is_numstart _ = true |- _ => rewrite E in Hn; discriminate end. }
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
    -
      assert (Hlt : k s < n).
      { apply tok_nonzero_lt; [lia|]. intro E.
        match goal with Hn : is_atomstart _ = true |- _ => rewrite E in Hn; discriminate end. }
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
  Qed.

  Theorem step_inv : forall l s l' s', step l s l' s' -> Inv l s -> Inv l' s'.
  Proof.
    intros l s l' s' Hst H.
    pose proof (inv_k _ _ H) as Hk. pose proof (inv_W _ _ H) as HW. destruct (inv_sb _ _ H) as [Hsb0 Hsb].
    pose proof (inv_depth _ _ H) as Hd. pose proof (inv_scopes _ _ H) as Hsc. pose proof (inv_kind _ _ H) as Hkind.
    assert (Hmono : forall w, 0 <= w -> Forall (fun sc => 1 <= snd sc < W s + w) (scopes s)).
    { intros w Hw. eapply Forall_impl; [|exact Hsc]. cbn beta; intros; lia. }
    inversion Hst; subst; clear Hst; ss.
    -
      eapply value_step_inv; eauto; ss; lia.
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_quote in *; lia).
      match goal with Hso : string_ok _ _ |- _ => destruct Hso as (j & Hc & Hdd) end.
      destruct (tok_string (k s)) as (j' & Hc' & Hj1 & Hj2); [lia|assumption|].
      assert (j = j') by (eapply closes_det; eauto). subst j'.
      pose proof (off_range (k s)).
      constructor; ss; [lia | lia | split; lia | | | ].
      + destruct Hd as [Hd1 Hd2]. split; [rewrite Hd1; lia|lia].
      + constructor; [ss; lia|]. apply Hmono; lia.
      + eauto.
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_colon in *; lia).
      pose proof (off_add (k s) 1).
      eapply value_step_inv; eauto; ss; lia.
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_comma in *; lia).
      assert (Hlt2 : k s + 1 < n) by (apply tok_nonzero_lt; [lia|]; unfold c_quote in *; lia).
      match goal with Hso : string_ok _ _ |- _ => destruct Hso as (j & Hc & Hdd) end.
      destruct (tok_string (k s + 1)) as (j' & Hc' & Hj1 & Hj2); [lia|assumption|].
      assert (j = j') by (eapply closes_det; eauto). subst j'.
      pose proof (off_add (k s) 1). replace (k s + 1 + 1) with (k s + 2) in * by lia.
      pose proof (off_range (k s)).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | exact Hkind].
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_rbrace in *; lia).
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | ].
      destruct Hkind as (ti & rest & E). rewrite E. discriminate.
    -
      match goal with E : scopes s = _ |- _ => rewrite E in * end. ss.
      constructor; ss; [lia | lia | split; lia | | constructor | reflexivity].
      unfold MAXDEPTH in *. lia.
    -
      match goal with E : scopes s = _ |- _ => rewrite E in * end. ss.
      constructor; ss; [lia | lia | split; lia | | | eauto].
      + unfold MAXDEPTH in *. lia.
      + inversion Hsc; assumption.
    -
      match goal with E : scopes s = _ |- _ => rewrite E in * end. ss.
      constructor; ss; [lia | lia | split; lia | | | eauto].
      + unfold MAXDEPTH in *. lia.
      + inversion Hsc; assumption.
    -
      constructor; ss; [lia | lia | split; lia | | | eauto].
      + destruct Hd as [Hd1 Hd2]. split; [rewrite Hd1; lia|lia].
      + constructor; [ss; lia|]. apply Hmono; lia.
    -
      eapply value_step_inv; eauto; ss; lia.
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_comma in *; lia).
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | exact Hsc | exact Hkind].
    -
      assert (Hlt : k s < n) by (apply tok_nonzero_lt; [lia|]; unfold c_rbrack in *; lia).
      pose proof (off_add (k s) 1).
      constructor; ss; [lia | lia | split; lia | exact Hd | apply Hmono; lia | ].
      destruct Hkind as (ti & rest & E). rewrite E. discriminate.
  Qed.

  Definition bonus (l : label) : Z := match l with ArrBegin | ScopeEnd => 1 | _ => 0 end.
  Definition mu (l : label) (s : st) : Z := 2 * (n - k s) + bonus l.

  Lemma mu_nonneg : forall l s, Inv l s -> 0 <= mu l s.
  Proof. intros l s H. pose proof (inv_k _ _ H). unfold mu. destruct l; cbn [bonus]; lia. Qed.

  Lemma value_step_mu : forall after s l' s', value_step after s l' s' -> bonus after = 0 -> mu l' s' < 2 * (n - k s).
  Proof. intros after s l' s' Hv Hb. inversion Hv; subst; unfold mu; cbn [bonus k]; try rewrite Hb; lia. Qed.

  Theorem step_mu : forall l s l' s', step l s l' s' -> mu l' s' < mu l s.
  Proof.
    intros l s l' s' Hst. inversion Hst; subst; clear Hst;
      try (match goal with Hv : value_step _ _ _ _ |- _ =>
             apply value_step_mu in Hv; [unfold mu at 2; cbn [bonus k] in *; lia|reflexivity] end);
      unfold mu; cbn [bonus k]; lia.
  Qed.

  Lemma mu_s0 : mu DocStart s0 = 2 * n.
  Proof. unfold mu, s0; cbn [bonus k]; lia. Qed.

End Stage2.
