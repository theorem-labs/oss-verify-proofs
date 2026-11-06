(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjTape.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record ghost : Type := mkG { gT : Z -> Z; gS : Z -> Z; gC : list Z }.

Definition frameT (Wv : Z) (T T' : Z -> Z) : Prop := forall x, 0 <= x < Wv -> T' x = T x.
Definition frameTx (Wv ex : Z) (T T' : Z -> Z) : Prop := forall x, 0 <= x < Wv -> x <> ex -> T' x = T x.
Definition frameS (sn : Z) (Sb Sb' : Z -> Z) : Prop := forall y, 0 <= y < sn -> Sb' y = Sb y.

Definition wrote_str (Sb' : Z -> Z) (o d : Z) : Prop := le32 Sb' o = d /\ Sb' (o + 4 + d) = 0.

Lemma frameT_refl : forall Wv T, frameT Wv T T.  Proof. intros Wv T x _. reflexivity. Qed.
Lemma frameS_refl : forall sn Sb, frameS sn Sb Sb.  Proof. intros sn Sb x _. reflexivity. Qed.
Lemma frameT_le : forall W1 W2 T T', W1 <= W2 -> frameT W2 T T' -> frameT W1 T T'.
Proof. intros W1 W2 T T' Hle H x Hx. apply H. lia. Qed.

Section TapeInv.
  Variables (bs idxs : list Z).
  Hypothesis HS : S1OUT bs idxs.
  Hypothesis Hlen : blen bs + 3 < 2^32.
  Variable CK : Z -> Z -> Prop.

  Local Abbreviation tok := (SjStage2.tok bs idxs).
  Local Abbreviation Inv := (SjStage2.Inv bs idxs).
  Local Abbreviation step := (SjStage2.step bs idxs).
  Local Abbreviation string_ok := (SjStage2.string_ok bs idxs).
  Local Abbreviation elemD T Sb sn := (elem T Sb sn CK).
  Local Abbreviation fieldD T Sb sn d := (field T Sb sn (elem T Sb sn CK d)).

  Fixpoint pend (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) {struct sc} : Prop :=
    match sc, cs with
    | [], [] => x = 1
    | (isarr, t) :: sc', c :: cs' =>
        1 <= t < x /\
        (if isarr : bool then tiles (elemD T Sb sn d) (t + 1) x (c - 1)
         else tiles (fieldD T Sb sn d) (t + 1) (x - 1) (c - 1) /\ is_str T Sb sn (x - 1)) /\
        pend T Sb sn sc' cs' t (Datatypes.S d)
    | _, _ => False
    end.

  Definition vdone (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) : Prop :=
    match sc, cs with
    | (isarr, t) :: sc', c :: cs' =>
        1 <= t < x /\
        (if isarr : bool then tiles (elemD T Sb sn d) (t + 1) x c else tiles (fieldD T Sb sn d) (t + 1) x c) /\
        pend T Sb sn sc' cs' t (Datatypes.S d)
    | _, _ => False
    end.

  Definition vafter (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) : Prop :=
    match sc with
    | [] => cs = [] /\ elemD T Sb sn d 1 x
    | _ :: _ => vdone T Sb sn sc cs x d
    end.

  Definition closed (T Sb : Z -> Z) (sn : Z) (sc : list (bool * Z)) (cs : list Z) (x : Z) (d : nat) : Prop :=
    match sc, cs with
    | (isarr, t) :: sc', c :: cs' => elemD T Sb sn (Datatypes.S d) t x /\ pend T Sb sn sc' cs' t (Datatypes.S d)
    | _, _ => False
    end.

  Definition TInv (l : label) (s : st) (g : ghost) : Prop :=
    exists d : nat, (d + length (scopes s) = TAPE_MAX_DEPTH)%nat /\
      match l with
      | DocStart | ObjBegin | ArrBegin | ObjField | ArrValue => pend (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d
      | ObjCont | ArrCont | DocEnd => vafter (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d
      | ScopeEnd => closed (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d
      end.

  Lemma TInv_s0 : forall T Sb, TInv DocStart s0 (mkG T Sb []).
  Proof. intros T Sb. exists TAPE_MAX_DEPTH. split; [unfold s0; cbn [scopes length]; apply Nat.add_0_r|]. unfold s0; cbn [pend scopes gC W]. reflexivity. Qed.

  Section Transport.
    Variables (T T' Sb Sb' : Z -> Z) (sn sn' : Z).
    Hypothesis HSb : frameS sn Sb Sb'.
    Hypothesis Hsn : sn <= sn'.

    Lemma tiles_elem_ext : forall d a e c, 0 <= a -> (forall y, a <= y < e -> T' y = T y) ->
      tiles (elemD T Sb sn d) a e c -> tiles (elemD T' Sb' sn' d) a e c.
    Proof using HSb Hsn.
      intros d a e c Ha HT Ht. eapply tiles_impl; [| |exact Ht]; [|apply elem_lt].
      intros p q Hp Hq Hel. eapply elem_ext; [exact HSb|exact Hsn| |exact Hel]. intros y Hy. apply HT. lia.
    Qed.

    Lemma tiles_field_ext : forall d a e c, 0 <= a -> (forall y, a <= y < e -> T' y = T y) ->
      tiles (fieldD T Sb sn d) a e c -> tiles (fieldD T' Sb' sn' d) a e c.
    Proof using HSb Hsn.
      intros d a e c Ha HT Ht. eapply tiles_impl; [| |exact Ht]; [|apply field_lt; apply elem_lt].
      intros p q Hp Hq [Hs Hel]. pose proof (elem_lt _ _ _ _ _ _ _ Hel). split.
      - eapply is_str_ext; [exact HSb|exact Hsn| |exact Hs]. apply HT. lia.
      - eapply elem_ext; [exact HSb|exact Hsn| |exact Hel]. intros y Hy. apply HT. lia.
    Qed.

    Lemma pend_ext : forall sc cs x d, (forall y, 0 <= y < x -> T' y = T y) ->
      pend T Sb sn sc cs x d -> pend T' Sb' sn' sc cs x d.
    Proof using HSb Hsn.
      induction sc as [|[isarr t] sc IH]; intros cs x d HT H; destruct cs as [|c cs]; cbn [pend] in *; try exact H.
      destruct H as (Ht & Hlev & Hrest). split; [exact Ht|]. split.
      - destruct isarr.
        + apply tiles_elem_ext; [lia| |exact Hlev]. intros y Hy. apply HT. lia.
        + destruct Hlev as [Htl Hk].
          pose proof (tiles_le _ (field_lt T Sb sn _ (elem_lt T Sb sn CK d)) _ _ _ Htl).
          split; [apply tiles_field_ext; [lia| |exact Htl]; intros y Hy; apply HT; lia|].
          eapply is_str_ext; [exact HSb|exact Hsn| |exact Hk]. apply HT. lia.
      - apply IH; [|exact Hrest]. intros y Hy. apply HT. lia.
    Qed.

  End Transport.

  Lemma pend_value : forall T Sb sn sc cs x x' d,
    pend T Sb sn sc cs x d -> elemD T Sb sn d x x' -> vafter T Sb sn sc cs x' d.
  Proof.
    intros T Sb sn sc cs x x' d H Hel. pose proof (elem_lt _ _ _ _ _ _ _ Hel) as Hlt.
    destruct sc as [|[isarr t] sc]; destruct cs as [|c cs]; cbn [pend] in H; try contradiction.
    - subst x. cbn. split; [reflexivity|exact Hel].
    - destruct H as (Ht & Hlev & Hrest). cbn [vafter vdone]. split; [lia|]. split; [|exact Hrest].
      destruct isarr.
      + replace c with (c - 1 + 1) by lia. eapply tiles_snoc; [exact Hlev|exact Hel].
      + destruct Hlev as [Htl Hk]. replace c with (c - 1 + 1) by lia. eapply tiles_snoc; [exact Htl|].
        split; [exact Hk|]. replace (x - 1 + 1) with x by lia. exact Hel.
  Qed.

  Lemma pend_count : forall T Sb sn isarr t sc c cs x d,
    pend T Sb sn ((isarr, t) :: sc) (c :: cs) x d -> 1 <= c <= x - t.
  Proof.
    intros T Sb sn isarr t sc c cs x d (Ht & Hlev & _). destruct isarr.
    - pose proof (tiles_le _ (elem_lt T Sb sn CK d) _ _ _ Hlev). lia.
    - destruct Hlev as [Htl _]. pose proof (tiles_le _ (field_lt T Sb sn _ (elem_lt T Sb sn CK d)) _ _ _ Htl). lia.
  Qed.

  Lemma vdone_count : forall T Sb sn isarr t sc c cs x d,
    vdone T Sb sn ((isarr, t) :: sc) (c :: cs) x d -> 0 <= c <= x - t - 1.
  Proof.
    intros T Sb sn isarr t sc c cs x d (Ht & Hlev & _). destruct isarr.
    - pose proof (tiles_le _ (elem_lt T Sb sn CK d) _ _ _ Hlev). lia.
    - pose proof (tiles_le _ (field_lt T Sb sn _ (elem_lt T Sb sn CK d)) _ _ _ Hlev). lia.
  Qed.

  Definition num_word (w : Z) : Prop := w = tword t_i64 0 \/ w = tword t_u64 0 \/ w = tword t_dbl 0.
  Definition atom_word (w : Z) : Prop := w = tword t_true 0 \/ w = tword t_false 0 \/ w = tword t_null 0.

  Inductive tvalue_step (after : label) (s : st) (g : ghost) : label -> st -> ghost -> Prop :=
  | tv_obj_empty : forall T' Sb' cv, tok (k s) = c_lbrace -> tok (k s + 1) = c_rbrace ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = cword t_obj (W s + 2) cv -> CK 0 cv -> T' (W s + 1) = tword t_obj_end (W s) ->
      tvalue_step after s g after (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tv_obj : forall T' Sb', tok (k s) = c_lbrace -> tok (k s + 1) <> c_rbrace ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tvalue_step after s g ObjBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tv_arr_empty : forall T' Sb' cv, tok (k s) = c_lbrack -> tok (k s + 1) = c_rbrack ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = cword t_arr (W s + 2) cv -> CK 0 cv -> T' (W s + 1) = tword t_arr_end (W s) ->
      tvalue_step after s g after (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tv_arr : forall T' Sb', tok (k s) = c_lbrack -> tok (k s + 1) <> c_rbrack ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tvalue_step after s g ArrBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tv_string : forall T' Sb' d, tok (k s) = c_quote -> string_ok (k s) d ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = tword t_str (sb s) -> wrote_str Sb' (sb s) d ->
      tvalue_step after s g after (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s)) (mkG T' Sb' (gC g))
  | tv_number : forall T' Sb', is_numstart (tok (k s)) = true ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' -> num_word (T' (W s)) ->
      tvalue_step after s g after (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tv_atom : forall T' Sb', is_atomstart (tok (k s)) = true ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' -> atom_word (T' (W s)) ->
      tvalue_step after s g after (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) (mkG T' Sb' (gC g)).

  Inductive tstep : label -> st -> ghost -> label -> st -> ghost -> Prop :=
  | tst_doc : forall s g l' s' g', tvalue_step DocEnd s g l' s' g' -> tstep DocStart s g l' s' g'
  | tst_obj_begin : forall s g T' Sb' d,
      depth s + 1 < MAXDEPTH -> tok (k s) = c_quote -> string_ok (k s) d ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s + 1) = tword t_str (sb s) -> wrote_str Sb' (sb s) d ->
      tstep ObjBegin s g ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s))
            (mkG T' Sb' (1 :: gC g))
  | tst_obj_field : forall s g l' s' g',
      tok (k s) = c_colon ->
      tvalue_step ObjCont (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) g l' s' g' -> tstep ObjField s g l' s' g'
  | tst_obj_cont_comma : forall s g T' Sb' d c cs,
      tok (k s) = c_comma -> tok (k s + 1) = c_quote -> string_ok (k s + 1) d ->
      frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = tword t_str (sb s) -> wrote_str Sb' (sb s) d -> gC g = c :: cs ->
      tstep ObjCont s g ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s)) (mkG T' Sb' ((c + 1) :: cs))
  | tst_obj_cont_end : forall s g T' Sb' ti rest c cs cv,
      tok (k s) = c_rbrace -> scopes s = (false, ti) :: rest -> gC g = c :: cs ->
      frameTx (W s) ti (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = tword t_obj_end ti -> T' ti = cword t_obj (W s + 1) cv -> CK c cv ->
      tstep ObjCont s g ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) (mkG T' Sb' (gC g))
  | tst_scope_end_doc : forall s g T' Sb' sc,
      scopes s = [sc] -> frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tstep ScopeEnd s g DocEnd (mkst (k s) (depth s - 1) (W s) (sb s) []) (mkG T' Sb' (tl (gC g)))
  | tst_scope_end_arr : forall s g T' Sb' sc ti rest,
      scopes s = sc :: (true, ti) :: rest -> frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tstep ScopeEnd s g ArrCont (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest)) (mkG T' Sb' (tl (gC g)))
  | tst_scope_end_obj : forall s g T' Sb' sc ti rest,
      scopes s = sc :: (false, ti) :: rest -> frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tstep ScopeEnd s g ObjCont (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest)) (mkG T' Sb' (tl (gC g)))
  | tst_arr_begin : forall s g T' Sb',
      depth s + 1 < MAXDEPTH -> frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      tstep ArrBegin s g ArrValue (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s)) (mkG T' Sb' (1 :: gC g))
  | tst_arr_value : forall s g l' s' g', tvalue_step ArrCont s g l' s' g' -> tstep ArrValue s g l' s' g'
  | tst_arr_cont_comma : forall s g T' Sb' c cs,
      tok (k s) = c_comma -> frameT (W s) (gT g) T' -> frameS (sb s) (gS g) Sb' -> gC g = c :: cs ->
      tstep ArrCont s g ArrValue (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) (mkG T' Sb' ((c + 1) :: cs))
  | tst_arr_cont_end : forall s g T' Sb' ti rest c cs cv,
      tok (k s) = c_rbrack -> scopes s = (true, ti) :: rest -> gC g = c :: cs ->
      frameTx (W s) ti (gT g) T' -> frameS (sb s) (gS g) Sb' ->
      T' (W s) = tword t_arr_end ti -> T' ti = cword t_arr (W s + 1) cv -> CK c cv ->
      tstep ArrCont s g ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) (mkG T' Sb' (gC g)).

  Lemma tvalue_step_step : forall after s g l' s' g', tvalue_step after s g l' s' g' -> value_step bs idxs after s l' s'.
  Proof.
    intros after s g l' s' g' H. destruct H.
    - apply v_obj_empty; assumption.
    - apply v_obj; assumption.
    - apply v_arr_empty; assumption.
    - apply v_arr; assumption.
    - eapply v_string; eassumption.
    - apply v_number; assumption.
    - apply v_atom; assumption.
  Qed.

  Theorem tstep_step : forall l s g l' s' g', tstep l s g l' s' g' -> step l s l' s'.
  Proof.
    intros l s g l' s' g' H. destruct H.
    - apply st_doc. eapply tvalue_step_step; eassumption.
    - eapply st_obj_begin; eassumption.
    - apply st_obj_field; [assumption|]. eapply tvalue_step_step; eassumption.
    - eapply st_obj_cont_comma; eassumption.
    - apply st_obj_cont_end; assumption.
    - eapply st_scope_end_doc; eassumption.
    - eapply st_scope_end_arr; eassumption.
    - eapply st_scope_end_obj; eassumption.
    - apply st_arr_begin; assumption.
    - apply st_arr_value. eapply tvalue_step_step; eassumption.
    - apply st_arr_cont_comma; assumption.
    - apply st_arr_cont_end; assumption.
  Qed.

  Lemma string_ok_nonneg : forall t d, string_ok t d -> 0 <= d.
  Proof. intros t d (j & _ & H). lia. Qed.

  Lemma wrote_is_str : forall T' Sb' i sbv d, 0 <= sbv -> 0 <= d -> T' i = tword t_str sbv -> wrote_str Sb' sbv d ->
    is_str T' Sb' (sbv + d + 5) i.
  Proof.
    intros T' Sb' i sbv d H0 Hd HT [Hl Hn]. exists sbv, d. split; [exact HT|]. unfold str_at. repeat split; try lia; assumption.
  Qed.

  Lemma tvalue_step_inv : forall after s g l' s' g' d,
    tvalue_step after s g l' s' g' ->
    1 <= W s -> 0 <= sb s -> (1 <= d)%nat -> (d + length (scopes s) = TAPE_MAX_DEPTH)%nat ->
    pend (gT g) (gS g) (sb s) (scopes s) (gC g) (W s) d ->
    (l' = after /\ vafter (gT g') (gS g') (sb s') (scopes s') (gC g') (W s') d /\ scopes s' = scopes s) \/
    ((l' = ObjBegin \/ l' = ArrBegin) /\ pend (gT g') (gS g') (sb s') (scopes s') (gC g') (W s') d /\ scopes s' = scopes s).
  Proof.
    intros after s g l' s' g' d Hv HW Hsb Hd Hdep Hp.
    destruct d as [|d0]; [lia|].
    destruct Hv as [T' Sb' cv _ _ FT FS H1 Hck H2|T' Sb' _ _ FT FS|T' Sb' cv _ _ FT FS H1 Hck H2|T' Sb' _ _ FT FS
                   |T' Sb' dd _ Hso FT FS H1 Hw|T' Sb' _ FT FS Hn|T' Sb' _ FT FS Ha]; cbn [gT gS gC W sb scopes].
    -   left. split; [reflexivity|]. split; [|reflexivity].
      eapply pend_value; [eapply pend_ext; [exact FS|lia|exact FT|exact Hp]|].
      replace (W s + 2) with (W s + 1 + 1) by lia. eapply (elem_object _ _ _ _ d0 (W s) (W s + 1) 0 cv); [exact Hck| | |apply tiles_nil].
      + replace (W s + 1 + 1) with (W s + 2) by lia. exact H1.
      + exact H2.
    -   right. split; [left; reflexivity|]. split; [|reflexivity].
      eapply pend_ext; [exact FS|lia|exact FT|exact Hp].
    -   left. split; [reflexivity|]. split; [|reflexivity].
      eapply pend_value; [eapply pend_ext; [exact FS|lia|exact FT|exact Hp]|].
      replace (W s + 2) with (W s + 1 + 1) by lia. eapply (elem_array _ _ _ _ d0 (W s) (W s + 1) 0 cv); [exact Hck| | |apply tiles_nil].
      + replace (W s + 1 + 1) with (W s + 2) by lia. exact H1.
      + exact H2.
    -   right. split; [right; reflexivity|]. split; [|reflexivity].
      eapply pend_ext; [exact FS|lia|exact FT|exact Hp].
    -   left. split; [reflexivity|]. split; [|reflexivity].
      pose proof (string_ok_nonneg _ _ Hso) as Hdd.
      eapply pend_value; [eapply pend_ext; [exact FS| |exact FT|exact Hp]; lia|].
      apply elem_scalar. right. right. split; [reflexivity|]. apply wrote_is_str; assumption.
    -   left. split; [reflexivity|]. split; [|reflexivity].
      eapply pend_value; [eapply pend_ext; [exact FS|lia|exact FT|exact Hp]|].
      apply elem_scalar. right. left. split; [reflexivity|exact Hn].
    -   left. split; [reflexivity|]. split; [|reflexivity].
      eapply pend_value; [eapply pend_ext; [exact FS|lia|exact FT|exact Hp]|].
      apply elem_scalar. left. split; [reflexivity|exact Ha].
  Qed.

  Lemma depth_budget : forall l s d, Inv l s -> (d + length (scopes s) = TAPE_MAX_DEPTH)%nat -> (1 <= d)%nat.
  Proof.
    intros l s d H Hd. destruct (inv_depth _ _ _ _ H) as [E Hlt]. unfold MAXDEPTH, TAPE_MAX_DEPTH in *. lia.
  Qed.

  Theorem tstep_inv : forall l s g l' s' g', Inv l s -> TInv l s g -> tstep l s g l' s' g' -> TInv l' s' g'.
  Proof.
    intros l s g l' s' g' HI (d & Hdep & HT) Hst.
    pose proof (inv_W _ _ _ _ HI) as HW. destruct (inv_sb _ _ _ _ HI) as [Hsb0 _].
    pose proof (depth_budget _ _ _ HI Hdep) as Hd1. pose proof (inv_kind _ _ _ _ HI) as Hkind.
    destruct Hst as [s g l' s' g' Hv|s g T' Sb' dd Hdp _ Hso FT FS H1 Hw|s g l' s' g' _ Hv|s g T' Sb' dd c cs _ _ Hso FT FS H1 Hw Hc
                    |s g T' Sb' ti rest c cs cv _ Hsc Hc FT FS H1 H2 Hck|s g T' Sb' sc Hsc FT FS|s g T' Sb' sc ti rest Hsc FT FS
                    |s g T' Sb' sc ti rest Hsc FT FS|s g T' Sb' Hdp FT FS|s g l' s' g' Hv|s g T' Sb' c cs _ FT FS Hc
                    |s g T' Sb' ti rest c cs cv _ Hsc Hc FT FS H1 H2 Hck]; cbn [TInv] in HT.
    -
      destruct (tvalue_step_inv _ _ _ _ _ _ d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; try assumption; try lia;
        exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      pose proof (string_ok_nonneg _ _ Hso) as Hdd.
      destruct d as [|d0]; [lia|]. exists d0. cbn [scopes W sb gT gS gC length]. split; [lia|].
      cbn [pend]. split; [lia|]. split.
      + split; [replace (W s + 2 - 1) with (W s + 1) by lia; replace (1 - 1) with 0 by lia; apply tiles_nil|].
        replace (W s + 2 - 1) with (W s + 1) by lia. apply wrote_is_str; assumption.
      + eapply pend_ext; [exact FS| |exact FT|exact HT]. lia.
    -
      set (s1 := mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)) in *.
      destruct (tvalue_step_inv ObjCont s1 g l' s' g' d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; subst s1; cbn [W sb scopes] in *;
        try assumption; try lia; exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      pose proof (string_ok_nonneg _ _ Hso) as Hdd.
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      destruct Hkind as (ti & rest & Esc). rewrite Esc in *. rewrite Hc in HT. cbn [vafter vdone] in HT.
      destruct HT as (Ht & Htl & Hrest). cbn [pend]. split; [lia|]. split.
      + replace (W s + 1 - 1) with (W s) by lia. replace (c + 1 - 1) with c by lia. split.
        * eapply tiles_field_ext; [exact FS| | |intros y Hy; apply FT; lia|exact Htl]; lia.
        * apply wrote_is_str; assumption.
      + eapply pend_ext; [exact FS| | |exact Hrest]; [lia|]. intros y Hy. apply FT. lia.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      rewrite Hsc, Hc in *. cbn [vafter vdone] in HT. destruct HT as (Ht & Htl & Hrest). cbn [closed]. split.
      + eapply (elem_object _ _ _ _ d ti (W s) c cv); [exact Hck|exact H2|exact H1|].
        eapply tiles_field_ext; [exact FS| | |intros y Hy; apply FT; lia|exact Htl]; lia.
      + eapply pend_ext; [exact FS| | |exact Hrest]; [lia|]. intros y Hy. apply FT; lia.
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|c cs] eqn:Ec; cbn [closed] in HT; [contradiction|].
      destruct HT as (Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      destruct cs as [|c2 cs]; cbn [pend] in Hrest; [|contradiction]. subst t. cbn [vafter]. split; [reflexivity|].
      eapply elem_ext; [exact FS|lia| |exact Hel]. intros y Hy. apply FT. lia.
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|c cs] eqn:Ec; cbn [closed] in HT; [contradiction|].
      destruct HT as (Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      pose proof (elem_lt _ _ _ _ _ _ _ Hel) as Hlt.
      assert (Hrest' : pend T' Sb' (sb s) ((true, ti) :: rest) cs t (Datatypes.S d)).
      { eapply pend_ext; [exact FS|lia| |exact Hrest]. intros y Hy. apply FT. lia. }
      assert (Hel' : elemD T' Sb' (sb s) (Datatypes.S d) t (W s)).
      { eapply elem_ext; [exact FS|lia| |exact Hel]. intros y Hy. apply FT.
        destruct cs as [|c2 cs2]; cbn [pend] in Hrest; [contradiction|]. lia. }
      exact (pend_value _ _ _ _ _ _ _ _ Hrest' Hel').
    -
      rewrite Hsc in *. destruct sc as [isarr t]. destruct (gC g) as [|c cs] eqn:Ec; cbn [closed] in HT; [contradiction|].
      destruct HT as (Hel & Hrest). exists (Datatypes.S d). cbn [scopes W sb gT gS gC length tl] in *. split; [lia|].
      pose proof (elem_lt _ _ _ _ _ _ _ Hel) as Hlt.
      assert (Hrest' : pend T' Sb' (sb s) ((false, ti) :: rest) cs t (Datatypes.S d)).
      { eapply pend_ext; [exact FS|lia| |exact Hrest]. intros y Hy. apply FT. lia. }
      assert (Hel' : elemD T' Sb' (sb s) (Datatypes.S d) t (W s)).
      { eapply elem_ext; [exact FS|lia| |exact Hel]. intros y Hy. apply FT.
        destruct cs as [|c2 cs2]; cbn [pend] in Hrest; [contradiction|]. lia. }
      exact (pend_value _ _ _ _ _ _ _ _ Hrest' Hel').
    -
      destruct d as [|d0]; [lia|]. exists d0. cbn [scopes W sb gT gS gC length]. split; [lia|].
      cbn [pend]. split; [lia|]. split.
      + replace (1 - 1) with 0 by lia. apply tiles_nil.
      + eapply pend_ext; [exact FS| |exact FT|exact HT]. lia.
    -
      destruct (tvalue_step_inv _ _ _ _ _ _ d Hv) as [(-> & Hr & Es)|([-> | ->] & Hr & Es)]; try assumption; try lia;
        exists d; (split; [rewrite Es; exact Hdep|]); cbn; exact Hr.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      destruct Hkind as (ti & rest & Esc). rewrite Esc in *. rewrite Hc in HT. cbn [vafter vdone] in HT.
      destruct HT as (Ht & Htl & Hrest). cbn [pend]. split; [lia|]. split.
      + replace (c + 1 - 1) with c by lia.
        eapply tiles_elem_ext; [exact FS| | |intros y Hy; apply FT; lia|exact Htl]; lia.
      + eapply pend_ext; [exact FS| | |exact Hrest]; [lia|]. intros y Hy. apply FT. lia.
    -
      exists d. cbn [scopes W sb gT gS gC]. split; [exact Hdep|].
      rewrite Hsc, Hc in *. cbn [vafter vdone] in HT. destruct HT as (Ht & Htl & Hrest). cbn [closed]. split.
      + eapply (elem_array _ _ _ _ d ti (W s) c cv); [exact Hck|exact H2|exact H1|].
        eapply tiles_elem_ext; [exact FS| | |intros y Hy; apply FT; lia|exact Htl]; lia.
      + eapply pend_ext; [exact FS| | |exact Hrest]; [lia|]. intros y Hy. apply FT; lia.
  Qed.

  Theorem docend_tape_wf : forall s g T',
    Inv DocEnd s -> TInv DocEnd s g ->
    (forall x, 1 <= x < W s -> T' x = gT g x) -> T' (W s) = tword t_root 0 -> T' 0 = tword t_root (W s + 1) ->
    tape_wf T' (gS g) (sb s) CK (W s + 1).
  Proof.
    intros s g T' HI (d & Hdep & HT) HF H1 H0.
    pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_k _ _ _ _ HI) as Hk. destruct (inv_sb _ _ _ _ HI) as [Hsb0 Hsb].
    pose proof (inv_kind _ _ _ _ HI) as Hkind. cbn [kind_ok] in Hkind. rewrite Hkind in *. cbn [vafter length] in *.
    destruct HT as [_ Hel]. pose proof (elem_lt _ _ _ _ _ _ _ Hel) as Hlt.
    pose proof (n_le_len _ _ HS) as Hn. pose proof (off_range _ _ HS (k s) Hk) as Ho. cbn [slackW slackS] in *.
    unfold tape_wf. replace (W s + 1 - 1) with (W s) by lia.
    split; [lia|]. split; [lia|]. split; [exact H0|]. split; [exact H1|].
    replace d with TAPE_MAX_DEPTH in Hel by lia.
    eapply (elem_ext (gT g) T' (gS g) (gS g) (sb s) (sb s)); [apply frameS_refl|lia| |exact Hel]. intros y Hy. apply HF. lia.
  Qed.

  Lemma tinv_count_pending : forall l s g c cs, Inv l s -> TInv l s g ->
    (l = ObjField \/ l = ArrValue) -> gC g = c :: cs -> 1 <= c <= W s.
  Proof.
    intros l s g c cs HI (d & _ & HT) Hl Hc. pose proof (inv_kind _ _ _ _ HI) as Hkind.
    destruct Hl as [-> | ->]; cbn [kind_ok TInv] in *; destruct Hkind as (ti & rest & E); rewrite E, Hc in HT;
      pose proof (pend_count _ _ _ _ _ _ _ _ _ _ HT); destruct HT as (? & _); lia.
  Qed.

  Lemma tinv_count_done : forall l s g c cs, Inv l s -> TInv l s g ->
    (l = ObjCont \/ l = ArrCont) -> gC g = c :: cs -> 0 <= c <= W s.
  Proof.
    intros l s g c cs HI (d & _ & HT) Hl Hc. pose proof (inv_kind _ _ _ _ HI) as Hkind.
    destruct Hl as [-> | ->]; cbn [kind_ok TInv] in *; destruct Hkind as (ti & rest & E); rewrite E, Hc in HT; cbn [vafter] in HT;
      pose proof (vdone_count _ _ _ _ _ _ _ _ _ _ HT); destruct HT as (? & _); lia.
  Qed.

  Lemma pend_length : forall T Sb sn sc cs x d, pend T Sb sn sc cs x d -> length cs = length sc.
  Proof.
    intros T Sb sn sc. induction sc as [|[isarr t] sc IH]; intros [|c cs] x d H; cbn [pend] in H; try contradiction; [reflexivity|].
    destruct H as (_ & _ & H). cbn [length]. f_equal. eapply IH; exact H.
  Qed.
End TapeInv.
