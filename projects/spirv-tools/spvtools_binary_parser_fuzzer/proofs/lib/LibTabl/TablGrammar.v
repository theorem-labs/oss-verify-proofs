(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition zsub {A} (f c : Z) (l : list A) : list A := firstn (Z.to_nat c) (skipn (Z.to_nat f) l).

Definition span (f c : Z) : list Z := zsub f c SPANS.

Definition i_opcode (r : Z * Z * Z * Z * Z) : Z := let '(op, _, _, _, _) := r in op.
Definition i_first  (r : Z * Z * Z * Z * Z) : Z := let '(_, f, _, _, _) := r in f.
Definition i_count  (r : Z * Z * Z * Z * Z) : Z := let '(_, _, c, _, _) := r in c.
Definition i_nfirst (r : Z * Z * Z * Z * Z) : Z := let '(_, _, _, nf, _) := r in nf.
Definition i_ncount (r : Z * Z * Z * Z * Z) : Z := let '(_, _, _, _, nc) := r in nc.
Definition i_span (r : Z * Z * Z * Z * Z) : list Z := span (i_first r) (i_count r).

Definition v_value (r : Z * Z * Z) : Z := let '(v, _, _) := r in v.
Definition v_first (r : Z * Z * Z) : Z := let '(_, f, _) := r in f.
Definition v_count (r : Z * Z * Z) : Z := let '(_, _, c) := r in c.
Definition v_span (r : Z * Z * Z) : list Z := span (v_first r) (v_count r).

Fixpoint find_ix {A} (p : A -> bool) (l : list A) (i : Z) : option (Z * A) :=
  match l with
  | [] => None
  | x :: l' => if p x then Some (i, x) else find_ix p l' (i + 1)
  end.

Definition find_insn (op : Z) : option (Z * (Z * Z * Z * Z * Z)) :=
  find_ix (fun r => i_opcode r =? op) INSN 0.

Definition kind_range (K : list (Z * Z * Z)) (t : Z) : Z * Z :=
  match find (fun k => v_value k =? t) K with
  | Some (_, f, c) => (f, c)
  | None => (0, 0)
  end.

Definition find_byvalue (K T : list (Z * Z * Z)) (t v : Z) : option (Z * (Z * Z * Z)) :=
  let '(f, c) := kind_range K t in
  find_ix (fun r => v_value r =? v) (zsub f c T) (Z.max 0 f).

Definition find_opnd (t v : Z) := find_byvalue OPND_KIND OPND t v.
Definition find_ext  (e v : Z) := find_byvalue EXT_KIND EXT e v.

Definition tg_op (op : Z) : option (list Z) :=
  match find_insn op with Some (_, r) => Some (i_span r) | None => None end.
Definition tg_operand (t v : Z) : option (list Z) :=
  match find_opnd t v with Some (_, r) => Some (v_span r) | None => None end.
Definition tg_ext (e v : Z) : option (list Z) :=
  match find_ext e v with Some (_, r) => Some (v_span r) | None => None end.
Definition tg_specop (op : Z) : bool := existsb (Z.eqb op) SPECOPS.

Definition TG : grammar := GRAMMAR tg_op tg_operand tg_ext tg_specop MAXLEN.

Lemma find_ix_some : forall {A} (p : A -> bool) l i j x,
  find_ix p l i = Some (j, x) -> In x l /\ p x = true /\ i <= j /\ nth_error l (Z.to_nat (j - i)) = Some x.
Proof.
  intros A p l. induction l as [|y l IH]; intros i j x H; cbn in H; [discriminate|].
  destruct (p y) eqn:Hp.
  - injection H as <- <-. split; [left; reflexivity|]. split; [exact Hp|]. split; [lia|].
    rewrite Z.sub_diag. reflexivity.
  - destruct (IH _ _ _ H) as (Hin & Hpx & Hij & Hn). split; [right; exact Hin|]. split; [exact Hpx|]. split; [lia|].
    replace (Z.to_nat (j - i)) with (S (Z.to_nat (j - (i + 1)))) by lia. cbn. exact Hn.
Qed.

Lemma In_zsub : forall {A} f c (l : list A) x, In x (zsub f c l) -> In x l.
Proof.
  intros A f c l x H. unfold zsub in H.
  rewrite <- (firstn_skipn (Z.to_nat f) l). apply in_or_app. right.
  rewrite <- (firstn_skipn (Z.to_nat c) (skipn (Z.to_nat f) l)). apply in_or_app. left. exact H.
Qed.

Lemma In_span : forall f c t, In t (span f c) -> In t SPANS.
Proof. intros f c t. apply In_zsub. Qed.

Lemma length_zsub_le : forall {A} f c (l : list A), 0 <= c -> HRep.Zlength (zsub f c l) <= c.
Proof.
  intros A f c l Hc. unfold HRep.Zlength, zsub. rewrite length_firstn. lia.
Qed.

Lemma find_ix_none : forall {A} (p : A -> bool) l i,
  (forall y, In y l -> p y = false) -> find_ix p l i = None.
Proof.
  intros A p l. induction l as [|y l IH]; intros i H; cbn; [reflexivity|].
  rewrite (H y (or_introl eq_refl)). apply IH. intros z Hz. apply H. right. exact Hz.
Qed.

Lemma find_ix_hit : forall {A} (p : A -> bool) l n y i,
  nth_error l n = Some y -> p y = true ->
  (forall m z, (m < n)%nat -> nth_error l m = Some z -> p z = false) ->
  find_ix p l i = Some (i + Z.of_nat n, y).
Proof.
  intros A p l. induction l as [|z l IH]; intros n y i Hn Hp Hb.
  - destruct n; discriminate.
  - destruct n as [|n].
    + cbn in Hn. injection Hn as ->. cbn. rewrite Hp. f_equal. f_equal. lia.
    + cbn in Hn. cbn. rewrite (Hb 0%nat z ltac:(lia) eq_refl).
      rewrite (IH n y (i + 1) Hn Hp). 2:{ intros m w Hm Hw. apply (Hb (S m) w ltac:(lia)). cbn. exact Hw. }
      f_equal. f_equal. lia.
Qed.

Lemma find_ix_fun : forall {A} (p q : A -> bool) l i j x y,
  find_ix p l i = Some (j, x) -> find_ix q l i = Some (j, y) -> x = y.
Proof.
  intros A p q l i j x y Hp Hq.
  destruct (find_ix_some _ _ _ _ _ Hp) as (_ & _ & _ & Hx). destruct (find_ix_some _ _ _ _ _ Hq) as (_ & _ & _ & Hy).
  rewrite Hx in Hy. injection Hy as ->. reflexivity.
Qed.

Lemma find_insn_fun : forall op op' i r r',
  find_insn op = Some (i, r) -> find_insn op' = Some (i, r') -> r = r' /\ op = op'.
Proof.
  intros op op' i r r' H H'. pose proof (find_ix_fun _ _ _ _ _ _ _ H H') as E. subst r'.
  destruct (find_ix_some _ _ _ _ _ H) as (_ & P & _). destruct (find_ix_some _ _ _ _ _ H') as (_ & P' & _).
  apply Z.eqb_eq in P. apply Z.eqb_eq in P'. split; [reflexivity | congruence].
Qed.

Definition seed_freeb (l : list Z) : bool := forallb (fun t => negb (zw_seed t)) l.
Definition op_list_okb (l : list Z) : bool :=
  seed_freeb (removelast l) && forallb (fun t => negb (t =? OT_OPTIONAL_TYPED_LITERAL_INTEGER)) l.

Fixpoint list_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && list_eqb a' b'
  | _, _ => false
  end.

Definition grammar_okb : bool :=
  match tg_op OP_TYPE_INT with Some l => list_eqb l [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_LITERAL_INTEGER] | None => false end
  && match tg_op OP_TYPE_FLOAT with Some l => list_eqb l [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_OPTIONAL_FPENCODING] | None => false end
  && forallb (fun r => op_list_okb (i_span r) && (0 <=? i_count r) && (i_count r <=? MAXLEN)) INSN
  && forallb (fun op => match tg_op op with Some l => seed_freeb (skipn 2 l) | None => true end) SPECOPS
  && forallb (fun r => seed_freeb (v_span r) && (0 <=? v_count r) && (v_count r <=? MAXLEN)) OPND
  && forallb (fun r => seed_freeb (v_span r) && (0 <=? v_count r) && (v_count r <=? MAXLEN)) EXT
  && forallb (fun t => (0 <=? t) && (t <? 2 ^ 31)) SPANS
  && (1 <=? MAXLEN) && (MAXLEN <=? 1024).

Lemma grammar_okb_true : grammar_okb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma list_eqb_eq : forall a b, list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [Hx Hr]. apply Z.eqb_eq in Hx. subst. f_equal. apply IH, Hr.
Qed.

Lemma seed_freeb_sound : forall l, seed_freeb l = true -> seed_free l.
Proof.
  intros l H t Ht. unfold seed_freeb in H. rewrite forallb_forall in H.
  specialize (H t Ht). destruct (zw_seed t); [discriminate|reflexivity].
Qed.

Lemma op_list_okb_sound : forall l, op_list_okb l = true -> op_list_ok l.
Proof.
  intros l H. unfold op_list_okb in H. apply andb_prop in H. destruct H as [H1 H2]. split.
  - apply seed_freeb_sound, H1.
  - intros t Ht. rewrite forallb_forall in H2. specialize (H2 t Ht).
    destruct (t =? OT_OPTIONAL_TYPED_LITERAL_INTEGER) eqn:E; [discriminate|]. apply Z.eqb_neq in E. exact E.
Qed.

Lemma tg_op_row : forall op l, tg_op op = Some l ->
  exists i r, find_insn op = Some (i, r) /\ In r INSN /\ i_opcode r = op /\ l = i_span r.
Proof.
  intros op l H. unfold tg_op in H. destruct (find_insn op) as [[i r]|] eqn:E; [|discriminate].
  injection H as <-. exists i, r. split; [reflexivity|].
  destruct (find_ix_some _ _ _ _ _ E) as (Hin & Hp & _). apply Z.eqb_eq in Hp. auto.
Qed.

Lemma find_byvalue_row : forall K T t v i r, find_byvalue K T t v = Some (i, r) ->
  In r T /\ v_value r = v
  /\ Z.max 0 (fst (kind_range K t)) <= i < Z.max 0 (fst (kind_range K t)) + snd (kind_range K t)
  /\ nth_error T (Z.to_nat i) = Some r.
Proof.
  intros K T t v i r H. unfold find_byvalue in H. destruct (kind_range K t) as [f c] eqn:Ek. cbn [fst snd].
  destruct (find_ix_some _ _ _ _ _ H) as (Hin & Hp & Hfi & Hn). apply Z.eqb_eq in Hp.
  split; [exact (In_zsub _ _ _ _ Hin)|]. split; [exact Hp|].
  assert (Hlt : (Z.to_nat (i - Z.max 0 f) < length (zsub f c T))%nat).
  { apply nth_error_Some. rewrite Hn. discriminate. }
  unfold zsub in Hlt, Hn. rewrite length_firstn in Hlt.
  split; [lia|].
  rewrite nth_error_firstn in Hn.
  destruct (Z.to_nat (i - Z.max 0 f) <? Z.to_nat c)%nat; [|discriminate].
  rewrite nth_error_skipn in Hn. replace (Z.to_nat f + Z.to_nat (i - Z.max 0 f))%nat with (Z.to_nat i) in Hn by lia. exact Hn.
Qed.

Lemma find_byvalue_ix_fun : forall K T t t' v v' i r r',
  find_byvalue K T t v = Some (i, r) -> find_byvalue K T t' v' = Some (i, r') -> r = r' /\ v = v'.
Proof.
  intros K T t t' v v' i r r' H H'.
  destruct (find_byvalue_row _ _ _ _ _ _ H) as (_ & Hv & _ & Hn). destruct (find_byvalue_row _ _ _ _ _ _ H') as (_ & Hv' & _ & Hn').
  rewrite Hn in Hn'. injection Hn' as ->. split; [reflexivity | congruence].
Qed.

Lemma tg_operand_row : forall t v l, tg_operand t v = Some l ->
  exists i r, find_opnd t v = Some (i, r) /\ In r OPND /\ v_value r = v /\ l = v_span r.
Proof.
  intros t v l H. unfold tg_operand in H. destruct (find_opnd t v) as [[i r]|] eqn:E; [|discriminate].
  injection H as <-. exists i, r. split; [reflexivity|].
  destruct (find_byvalue_row _ _ _ _ _ _ E) as (Hin & Hv & _). auto.
Qed.

Lemma tg_ext_row : forall e v l, tg_ext e v = Some l ->
  exists i r, find_ext e v = Some (i, r) /\ In r EXT /\ v_value r = v /\ l = v_span r.
Proof.
  intros e v l H. unfold tg_ext in H. destruct (find_ext e v) as [[i r]|] eqn:E; [|discriminate].
  injection H as <-. exists i, r. split; [reflexivity|].
  destruct (find_byvalue_row _ _ _ _ _ _ E) as (Hin & Hv & _). auto.
Qed.

Theorem TG_ok : grammar_ok TG.
Proof.
  pose proof grammar_okb_true as H. unfold grammar_okb in H.
  apply andb_prop in H as [H C0]. apply andb_prop in H as [H C1]. apply andb_prop in H as [H C2].
  apply andb_prop in H as [H C3]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C5].
  apply andb_prop in H as [H C6]. apply andb_prop in H as [H C7].

  rewrite forallb_forall in C6, C5, C4, C3, C2.
  assert (RNG : forall t, In t SPANS -> 0 <= t < 2 ^ 31).
  { intros t Ht. specialize (C2 t Ht). apply andb_prop in C2. destruct C2 as [A B].
    apply Z.leb_le in A. apply Z.ltb_lt in B. lia. }
  constructor; cbn [g_op g_operand g_ext g_specop g_maxlen TG].
  - intros l Hl. rewrite Hl in H. apply list_eqb_eq in H. exact H.
  - intros l Hl. rewrite Hl in C7. apply list_eqb_eq in C7. exact C7.
  - intros op l Hl. destruct (tg_op_row _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C6 r Hin). apply andb_prop in C6. destruct C6 as [C6 _]. apply andb_prop in C6. destruct C6 as [C6 _].
    apply op_list_okb_sound, C6.
  - intros op l Hs Hl. unfold tg_specop in Hs. rewrite existsb_exists in Hs. destruct Hs as (x & Hx & E).
    apply Z.eqb_eq in E. subst x. specialize (C5 op Hx). rewrite Hl in C5. apply seed_freeb_sound, C5.
  - intros t v l Hl. destruct (tg_operand_row _ _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C4 r Hin). apply andb_prop in C4. destruct C4 as [C4 _]. apply andb_prop in C4. destruct C4 as [C4 _].
    apply seed_freeb_sound, C4.
  - intros e v l Hl. destruct (tg_ext_row _ _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C3 r Hin). apply andb_prop in C3. destruct C3 as [C3 _]. apply andb_prop in C3. destruct C3 as [C3 _].
    apply seed_freeb_sound, C3.
  - intros op l Hl. destruct (tg_op_row _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C6 r Hin). apply andb_prop in C6. destruct C6 as [C6 B]. apply andb_prop in C6. destruct C6 as [_ A].
    apply Z.leb_le in A. apply Z.leb_le in B. unfold i_span, span. eapply Z.le_trans; [apply length_zsub_le; lia|exact B].
  - intros t v l Hl. destruct (tg_operand_row _ _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C4 r Hin). apply andb_prop in C4. destruct C4 as [C4 B]. apply andb_prop in C4. destruct C4 as [_ A].
    apply Z.leb_le in A. apply Z.leb_le in B. unfold v_span, span. eapply Z.le_trans; [apply length_zsub_le; lia|exact B].
  - intros e v l Hl. destruct (tg_ext_row _ _ _ Hl) as (i & r & _ & Hin & _ & ->).
    specialize (C3 r Hin). apply andb_prop in C3. destruct C3 as [C3 B]. apply andb_prop in C3. destruct C3 as [_ A].
    apply Z.leb_le in A. apply Z.leb_le in B. unfold v_span, span. eapply Z.le_trans; [apply length_zsub_le; lia|exact B].
  - intros l t [(op & Hl)|[(a & v & Hl)|(e & v & Hl)]] Ht.
    + destruct (tg_op_row _ _ Hl) as (i & r & _ & _ & _ & ->). apply RNG. eapply In_span, Ht.
    + destruct (tg_operand_row _ _ _ Hl) as (i & r & _ & _ & _ & ->). apply RNG. eapply In_span, Ht.
    + destruct (tg_ext_row _ _ _ Hl) as (i & r & _ & _ & _ & ->). apply RNG. eapply In_span, Ht.
  - apply Z.leb_le in C1. apply Z.leb_le in C0. lia.
Qed.

Definition TG_GENTYPE : list Z :=
  [19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 322; 327;
   4163; 4190; 4417; 4456; 4472; 5076; 5115; 5281; 5288; 5313; 5341; 5358; 5370; 5371; 6199].
Definition tg_generates_type (op : Z) : bool := existsb (Z.eqb op) TG_GENTYPE.
