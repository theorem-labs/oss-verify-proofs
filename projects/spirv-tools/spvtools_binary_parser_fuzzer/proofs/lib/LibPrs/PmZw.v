(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require list_basics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma Zlen_app : forall {T} (a b : list T), Zlen (a ++ b) = Zlen a + Zlen b.
Proof. intros T a b. unfold Zlen. rewrite length_app. lia. Qed.
Lemma Zlen_cons : forall {T} (x : T) l, Zlen (x :: l) = Zlen l + 1.
Proof. intros T x l. unfold Zlen. cbn [length]. lia. Qed.
Lemma Zlen_nil : forall {T}, Zlen (@nil T) = 0.
Proof. intros T. reflexivity. Qed.
Lemma Zlen_nonneg : forall {T} (l : list T), 0 <= Zlen l.
Proof. intros T l. unfold Zlen. lia. Qed.
Lemma Zlen_removelast : forall (l : list Z), l <> [] -> Zlen (removelast l) = Zlen l - 1.
Proof.
  intros l Hl. pose proof (app_removelast_last 0 Hl) as E. apply (f_equal (@length Z)) in E.
  rewrite length_app in E. cbn [length] in E. unfold Zlen. lia.
Qed.

Ltac unfold_OT := unfold OT_NONE, OT_ID, OT_TYPE_ID, OT_RESULT_ID, OT_LITERAL_INTEGER, OT_SPEC_CONSTANT_OP_NUMBER, OT_TYPED_LITERAL_NUMBER,
  OT_FPENCODING, OT_OPTIONAL_ID, OT_OPTIONAL_LITERAL_INTEGER, OT_OPTIONAL_TYPED_LITERAL_INTEGER, OT_OPTIONAL_FPENCODING, OT_VARIABLE_ID,
  OT_VARIABLE_LITERAL_INTEGER, OT_VARIABLE_LITERAL_INTEGER_ID, OT_VARIABLE_ID_LITERAL_INTEGER, OT_OPTIONAL_CAPABILITY, OT_VARIABLE_CAPABILITY in *.

Lemma expand_cases : forall t,
  (t = OT_VARIABLE_ID /\ expand t = Some [OT_VARIABLE_ID; OT_OPTIONAL_ID])
  \/ (t = OT_VARIABLE_LITERAL_INTEGER /\ expand t = Some [OT_VARIABLE_LITERAL_INTEGER; OT_OPTIONAL_LITERAL_INTEGER])
  \/ (t = OT_VARIABLE_LITERAL_INTEGER_ID /\ expand t = Some [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID; OT_OPTIONAL_TYPED_LITERAL_INTEGER])
  \/ (t = OT_VARIABLE_ID_LITERAL_INTEGER /\ expand t = Some [OT_VARIABLE_ID_LITERAL_INTEGER; OT_LITERAL_INTEGER; OT_OPTIONAL_ID])
  \/ (t = OT_VARIABLE_CAPABILITY /\ expand t = Some [OT_VARIABLE_CAPABILITY; OT_OPTIONAL_CAPABILITY])
  \/ expand t = None.
Proof.
  intros t. unfold expand.
  destruct (Z.eqb_spec t OT_VARIABLE_ID) as [->|N1]; [left; split; reflexivity|].
  destruct (Z.eqb_spec t OT_VARIABLE_LITERAL_INTEGER) as [->|N2]; [right; left; split; reflexivity|].
  destruct (Z.eqb_spec t OT_VARIABLE_LITERAL_INTEGER_ID) as [->|N3]; [right; right; left; split; reflexivity|].
  destruct (Z.eqb_spec t OT_VARIABLE_ID_LITERAL_INTEGER) as [->|N4]; [right; right; right; left; split; reflexivity|].
  destruct (Z.eqb_spec t OT_VARIABLE_CAPABILITY) as [->|N5]; [right; right; right; right; left; split; reflexivity|].
  right; right; right; right; right. reflexivity.
Qed.

Lemma expand_shape : forall t e, expand t = Some e ->
  exists rest r, e = rest ++ [r] /\ Zlen rest <= 2 /\ zw_seed r = zw_type r
  /\ Forall (fun x => 0 <= x < 2 ^ 31) e
  /\ (rest = [t] \/ (t = OT_VARIABLE_LITERAL_INTEGER_ID /\ rest = [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID] /\ r = OT_OPTIONAL_TYPED_LITERAL_INTEGER)
      \/ (t = OT_VARIABLE_ID_LITERAL_INTEGER /\ rest = [OT_VARIABLE_ID_LITERAL_INTEGER; OT_LITERAL_INTEGER])).
Proof.
  intros t e He.
  destruct (expand_cases t) as [[-> E]|[[-> E]|[[-> E]|[[-> E]|[[-> E]|E]]]]]; rewrite E in He; try discriminate; injection He as <-.
  - exists [OT_VARIABLE_ID], OT_OPTIONAL_ID. refine (conj eq_refl (conj _ (conj eq_refl (conj _ _)))); [unfold Zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | repeat apply Forall_cons; try apply Forall_nil; unfold_OT; lia | left; reflexivity].
  - exists [OT_VARIABLE_LITERAL_INTEGER], OT_OPTIONAL_LITERAL_INTEGER. refine (conj eq_refl (conj _ (conj eq_refl (conj _ _)))); [unfold Zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | repeat apply Forall_cons; try apply Forall_nil; unfold_OT; lia | left; reflexivity].
  - exists [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID], OT_OPTIONAL_TYPED_LITERAL_INTEGER. refine (conj eq_refl (conj _ (conj eq_refl (conj _ _)))); [unfold Zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | repeat apply Forall_cons; try apply Forall_nil; unfold_OT; lia | right; left; repeat split; reflexivity].
  - exists [OT_VARIABLE_ID_LITERAL_INTEGER; OT_LITERAL_INTEGER], OT_OPTIONAL_ID. refine (conj eq_refl (conj _ (conj eq_refl (conj _ _)))); [unfold Zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | repeat apply Forall_cons; try apply Forall_nil; unfold_OT; lia | right; right; split; reflexivity].
  - exists [OT_VARIABLE_CAPABILITY], OT_OPTIONAL_CAPABILITY. refine (conj eq_refl (conj _ (conj eq_refl (conj _ _)))); [unfold Zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | repeat apply Forall_cons; try apply Forall_nil; unfold_OT; lia | left; reflexivity].
Qed.

Lemma take_first_noexp : forall xs, expand (last xs 0) = None -> take_first xs = (last xs 0, removelast xs).
Proof. intros xs E. unfold take_first. rewrite E. reflexivity. Qed.
Lemma take_first_exp : forall xs e, expand (last xs 0) = Some e -> take_first xs = (last e 0, removelast xs ++ removelast e).
Proof. intros xs e E. unfold take_first. rewrite E. reflexivity. Qed.

Lemma take_first_len : forall xs, xs <> [] -> Zlen (snd (take_first xs)) <= Zlen xs + 1 /\ Zlen xs - 1 <= Zlen (snd (take_first xs)).
Proof.
  intros xs Hne. destruct (expand (last xs 0)) as [e|] eqn:E.
  - rewrite (take_first_exp xs e E). cbn [snd]. destruct (expand_shape _ _ E) as (rest & r & -> & Hr & _).
    rewrite removelast_last, Zlen_app, Zlen_removelast by exact Hne.
    pose proof (Zlen_nonneg rest). lia.
  - rewrite (take_first_noexp xs E). cbn [snd]. rewrite Zlen_removelast by exact Hne. lia.
Qed.

Lemma Forall_removelast : forall {T} (P : T -> Prop) l, Forall P l -> Forall P (removelast l).
Proof.
  intros T P l H. destruct l as [|x l']; [constructor|].
  rewrite (app_removelast_last (l:=x :: l') x) in H by discriminate. apply Forall_app in H. tauto.
Qed.
Lemma Forall_last : forall (P : Z -> Prop) l d, Forall P l -> P d -> P (last l d).
Proof.
  intros P l d H Hd. destruct l as [|x l']; [exact Hd|].
  rewrite (app_removelast_last (l:=x :: l') d) in H by discriminate. apply Forall_app in H. destruct H as [_ H]. inversion H. assumption.
Qed.

Lemma take_first_range : forall xs, Forall (fun x => 0 <= x < 2 ^ 31) xs ->
  0 <= fst (take_first xs) < 2 ^ 31 /\ Forall (fun x => 0 <= x < 2 ^ 31) (snd (take_first xs)).
Proof.
  intros xs F. destruct (expand (last xs 0)) as [e|] eqn:E.
  - rewrite (take_first_exp xs e E). cbn [fst snd]. destruct (expand_shape _ _ E) as (rest & r & Ee & Hr & _ & Fe & _).
    split; [apply (Forall_last _ e 0 Fe); lia|]. apply Forall_app. split; [apply Forall_removelast; exact F | apply Forall_removelast; exact Fe].
  - rewrite (take_first_noexp xs E). cbn [fst snd]. split; [apply (Forall_last _ xs 0 F); lia | apply Forall_removelast; exact F].
Qed.

Lemma seed_free_app : forall a b, seed_free a -> seed_free b -> seed_free (a ++ b).
Proof. intros a b Ha Hb t Ht. apply in_app_iff in Ht. destruct Ht; [apply Ha | apply Hb]; assumption. Qed.
Lemma seed_free_nil : seed_free [].
Proof. intros t []. Qed.

Lemma seed_free_sub : forall a b, seed_free (a ++ b) -> seed_free a /\ seed_free b.
Proof. intros a b H. split; intros t Ht; apply H; apply in_app_iff; tauto. Qed.
Lemma seed_free_cons_inv : forall x l, seed_free (x :: l) -> zw_seed x = false /\ seed_free l.
Proof. intros x l H. split; [apply H; left; reflexivity | intros t Ht; apply H; right; exact Ht]. Qed.

Lemma zw_stack_ok_intro : forall bot top, seed_free top ->
  (bot = [] \/ bot = [OT_TYPED_LITERAL_NUMBER] \/ bot = [OT_SPEC_CONSTANT_OP_NUMBER]
   \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID] \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID]) ->
  zw_stack_ok (bot ++ top).
Proof. intros bot top Ht Hb. exists bot, top. split; [reflexivity|]. split; [exact Ht|]. destruct Hb as [H|[H|[H|[H|H]]]]; subst; tauto. Qed.

Lemma zw_seed_of_type : forall t, zw_type t = true -> zw_seed t = true.
Proof. intros t H. unfold zw_seed. rewrite H. reflexivity. Qed.

Lemma zw_take_push : forall xs l, zw_stack_ok xs -> xs <> [] -> seed_free l -> zw_stack_ok (snd (take_first xs) ++ l).
Proof.
  intros xs l (bot & top & -> & Htop & Hbot) Hne Hl.
  destruct top as [|u top'] using rev_ind.
  -
    rewrite app_nil_r in *. clear Htop.
    destruct Hbot as [->|[->|[->|[->|[->|[-> _]]]]]]; [exfalso; exact (Hne eq_refl) | | | | |];
      unfold take_first; cbn [last removelast]; unfold expand, OT_TYPED_LITERAL_NUMBER, OT_SPEC_CONSTANT_OP_NUMBER, OT_VARIABLE_LITERAL_INTEGER_ID, OT_ID,
        OT_OPTIONAL_TYPED_LITERAL_INTEGER, OT_VARIABLE_ID, OT_VARIABLE_LITERAL_INTEGER, OT_VARIABLE_ID_LITERAL_INTEGER, OT_VARIABLE_CAPABILITY; cbn.
    + apply (zw_stack_ok_intro [] l Hl). tauto.
    + apply (zw_stack_ok_intro [] l Hl). tauto.
    + change (54 :: 1 :: l) with ([OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID] ++ l). apply (zw_stack_ok_intro _ l Hl). tauto.
    + change (54 :: l) with ([OT_VARIABLE_LITERAL_INTEGER_ID] ++ l). apply (zw_stack_ok_intro _ l Hl). tauto.
    + change (54 :: 1 :: l) with ([OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID] ++ l). apply (zw_stack_ok_intro _ l Hl). tauto.
  -
    destruct (seed_free_sub _ _ Htop) as [Htop' Hu]. pose proof (proj1 (seed_free_cons_inv _ _ Hu)) as Hus.
    assert (Hbot' : bot = [] \/ bot = [OT_TYPED_LITERAL_NUMBER] \/ bot = [OT_SPEC_CONSTANT_OP_NUMBER]
                    \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID] \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID]).
    { destruct Hbot as [H|[H|[H|[H|[H|[H Habs]]]]]]; try tauto. exfalso. destruct top'; discriminate. }
    rewrite app_assoc. destruct (expand u) as [e|] eqn:E.
    + rewrite (take_first_exp _ e) by (rewrite last_last; exact E). cbn [snd].
      rewrite removelast_last.
      destruct (expand_shape _ _ E) as (rest & r & -> & _ & _ & _ & Hrest).
      rewrite removelast_last.
      rewrite <- !app_assoc. apply zw_stack_ok_intro; [| exact Hbot'].
      apply seed_free_app; [exact Htop'|]. apply seed_free_app; [| exact Hl].
      destruct Hrest as [->|[(-> & -> & _)|(-> & ->)]].
      * intros t [<-|[]]. exact Hus.
      * exfalso. cbv in Hus. discriminate.
      * intros t [<-|[<-|[]]]; [exact Hus | reflexivity].
    + rewrite (take_first_noexp _) by (rewrite last_last; exact E). cbn [snd].
      rewrite removelast_last.
      rewrite <- app_assoc. apply zw_stack_ok_intro; [| exact Hbot']. apply seed_free_app; assumption.
Qed.

Lemma expand_zw : forall u e, expand u = Some e -> zw_type (last e 0) = true -> u = OT_VARIABLE_LITERAL_INTEGER_ID.
Proof.
  intros u e E Hz.
  destruct (expand_cases u) as [[-> E2]|[[-> E2]|[[-> E2]|[[-> E2]|[[-> E2]|E2]]]]]; rewrite E2 in E; try discriminate;
    injection E as <-; cbv in Hz; try discriminate; reflexivity.
Qed.

Lemma zw_take_zero : forall xs, zw_stack_ok xs -> xs <> [] -> zw_type (fst (take_first xs)) = true ->
  zw_next xs = 1 /\ zw_next (snd (take_first xs)) = 0.
Proof.
  intros xs (bot & top & -> & Htop & Hbot) Hne Hzw.
  destruct top as [|u top'] using rev_ind.
  - rewrite app_nil_r in *.
    destruct Hbot as [->|[->|[->|[->|[->|[-> _]]]]]]; [exfalso; exact (Hne eq_refl) | | | | |];
      revert Hzw; unfold take_first, zw_next; cbn [last removelast]; unfold expand, zw_seed, zw_type, OT_TYPED_LITERAL_NUMBER, OT_SPEC_CONSTANT_OP_NUMBER, OT_VARIABLE_LITERAL_INTEGER_ID, OT_ID,
        OT_OPTIONAL_TYPED_LITERAL_INTEGER, OT_VARIABLE_ID, OT_VARIABLE_LITERAL_INTEGER, OT_VARIABLE_ID_LITERAL_INTEGER, OT_VARIABLE_CAPABILITY; cbn; intros Hzw;
      first [discriminate Hzw | split; reflexivity].
  - destruct (seed_free_sub _ _ Htop) as [Htop' Hu]. pose proof (proj1 (seed_free_cons_inv _ _ Hu)) as Hus.
    exfalso. revert Hzw. rewrite app_assoc. destruct (expand u) as [e|] eqn:E.
    + rewrite (take_first_exp _ e) by (rewrite last_last; exact E). cbn [fst].
      intros Hzw. pose proof (expand_zw u e E Hzw) as ->. cbv in Hus. discriminate.
    + rewrite (take_first_noexp _) by (rewrite last_last; exact E). cbn [fst].
      rewrite last_last. intros Hzw. pose proof (zw_seed_of_type u Hzw). congruence.
Qed.

Lemma push_types_split : forall l xs, exists l', push_types l xs = xs ++ l' /\ Zlen l' <= Zlen l /\ (forall t, In t l' -> In t l).
Proof.
  intros l xs. unfold push_types. eexists. split; [reflexivity|]. split.
  - unfold Zlen. pose proof (list_basics.list.length_filter (fun t : Z => Is_true (negb (t =? OT_NONE))) (rev l)) as Hf.
    rewrite length_rev in Hf. lia.
  - intros t Ht. apply base.list_elem_of_In in Ht. apply list_basics.list.list_elem_of_filter in Ht. destruct Ht as [_ Ht].
    apply base.list_elem_of_In in Ht. apply in_rev in Ht. exact Ht.
Qed.
Lemma push_types_facts : forall l xs, seed_free l -> Forall (fun x => 0 <= x < 2 ^ 31) l ->
  exists l', push_types l xs = xs ++ l' /\ Zlen l' <= Zlen l /\ seed_free l' /\ Forall (fun x => 0 <= x < 2 ^ 31) l'.
Proof.
  intros l xs Hs Hr. destruct (push_types_split l xs) as (l' & E & Hlen & Hin). exists l'.
  split; [exact E|]. split; [exact Hlen|]. split.
  - intros t Ht. exact (Hs t (Hin t Ht)).
  - apply Forall_forall. intros t Ht. exact (proj1 (Forall_forall _ _) Hr t (Hin t Ht)).
Qed.

Lemma zw_next_range : forall xs, 0 <= zw_next xs <= 1.
Proof. intros xs. unfold zw_next. destruct (zw_seed _); lia. Qed.

Definition lits (ys : list Z) : Prop := Forall (fun x => x = OT_RESULT_ID \/ x = OT_LITERAL_INTEGER) ys.
Definition nty (op : Z) (xs : list Z) (d : Z) : Prop :=
  (op = OP_TYPE_INT \/ op = OP_TYPE_FLOAT) ->
  4 <= d \/ exists ys, ((op = OP_TYPE_INT /\ xs = ys) \/ (op = OP_TYPE_FLOAT /\ xs = OT_OPTIONAL_FPENCODING :: ys))
                       /\ lits ys /\ 3 <= Zlen xs + (d - 1).

Lemma nty_other : forall op xs d, op <> OP_TYPE_INT -> op <> OP_TYPE_FLOAT -> nty op xs d.
Proof. intros op xs d H1 H2 [H|H]; exfalso; [exact (H1 H) | exact (H2 H)]. Qed.

Lemma nty_init_int : forall d, 1 <= d -> nty OP_TYPE_INT (push_types [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_LITERAL_INTEGER] []) d.
Proof.
  intros d Hd _. right. exists [OT_LITERAL_INTEGER; OT_LITERAL_INTEGER; OT_RESULT_ID]. split; [left; split; reflexivity|].
  split; [unfold lits; apply Forall_cons; [right; reflexivity|]; apply Forall_cons; [right; reflexivity|]; apply Forall_cons; [left; reflexivity|]; apply Forall_nil
        | match goal with |- context [Zlen ?l] => let v := eval vm_compute in (Zlen l) in replace (Zlen l) with v by (vm_compute; reflexivity) end; lia].
Qed.
Lemma nty_init_float : forall d, 1 <= d -> nty OP_TYPE_FLOAT (push_types [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_OPTIONAL_FPENCODING] []) d.
Proof.
  intros d Hd _. right. exists [OT_LITERAL_INTEGER; OT_RESULT_ID]. split; [right; split; reflexivity|].
  split; [unfold lits; apply Forall_cons; [right; reflexivity|]; apply Forall_cons; [left; reflexivity|]; apply Forall_nil
        | match goal with |- context [Zlen ?l] => let v := eval vm_compute in (Zlen l) in replace (Zlen l) with v by (vm_compute; reflexivity) end; lia].
Qed.

Lemma lits_snoc_inv : forall ys x, lits (ys ++ [x]) -> lits ys /\ (x = OT_RESULT_ID \/ x = OT_LITERAL_INTEGER).
Proof. intros ys x H. unfold lits in *. rewrite Forall_app in H. destruct H as [H1 H2]. split; [exact H1 | exact (Forall_inv H2)]. Qed.

Lemma nty_step : forall op xs0 (l' : list Z) nw d,
  xs0 <> [] -> nty op xs0 d ->
  (1 <= nw \/ (nw = 0 /\ zw_type (fst (take_first xs0)) = true /\ l' = [])) ->
  (l' = [] \/ (fst (take_first xs0) <> OT_RESULT_ID /\ fst (take_first xs0) <> OT_LITERAL_INTEGER)) ->
  nty op (snd (take_first xs0) ++ l') (d + nw).
Proof.
  intros op xs0 l' nw d Hne H Hnw Hl' Hop. destruct (H Hop) as [H4|(ys & Hf & Hl & Hc)]; [left; destruct Hnw as [Hnw|(Hnw & _)]; lia|].
  destruct ys as [|x ys'] using rev_ind.
  - destruct Hf as [[-> ->]|[-> ->]]; [exfalso; exact (Hne eq_refl)|].
    left. rewrite Zlen_cons, Zlen_nil in Hc. change (take_first [OT_OPTIONAL_FPENCODING]) with (OT_OPTIONAL_FPENCODING, @nil Z) in Hnw. cbn [fst] in Hnw.
    destruct Hnw as [Hnw|(_ & Hz & _)]; [lia | cbv in Hz; discriminate].
  - destruct (lits_snoc_inv _ _ Hl) as [Hl1 Hx].
    assert (Hlast : last xs0 0 = x /\ removelast xs0 = (if op =? OP_TYPE_INT then ys' else OT_OPTIONAL_FPENCODING :: ys')).
    { destruct Hf as [[-> ->]|[-> ->]].
      - rewrite last_last, removelast_last. split; reflexivity.
      - change (OT_OPTIONAL_FPENCODING :: ys' ++ [x]) with ((OT_OPTIONAL_FPENCODING :: ys') ++ [x]). rewrite last_last, removelast_last. split; reflexivity. }
    destruct Hlast as [HL HR].
    assert (E : expand x = None) by (destruct Hx as [-> | ->]; reflexivity).
    rewrite (take_first_noexp xs0) in Hnw, Hl' |- * by (rewrite HL; exact E). rewrite HL in Hnw, Hl' |- *. cbn [fst snd] in Hnw, Hl' |- *.
    assert (Hz : zw_type x = false) by (destruct Hx as [-> | ->]; reflexivity).
    destruct Hnw as [Hnw|(_ & Hz' & _)]; [| rewrite Hz in Hz'; discriminate].
    destruct Hl' as [-> | [N1 N2]]; [| exfalso; destruct Hx as [-> | ->]; [exact (N1 eq_refl) | exact (N2 eq_refl)]].
    rewrite app_nil_r, HR. right. exists ys'.
    assert (Hlen : Zlen xs0 = Zlen ys' + (if op =? OP_TYPE_INT then 1 else 2)).
    { destruct Hf as [[-> ->]|[-> ->]]; cbn [OP_TYPE_INT OP_TYPE_FLOAT Z.eqb Pos.eqb]; rewrite ?Zlen_cons, Zlen_app, Zlen_cons, Zlen_nil; lia. }
    destruct Hf as [[-> E0]|[-> E0]]; cbn [OP_TYPE_INT OP_TYPE_FLOAT Z.eqb Pos.eqb] in Hlen |- *.
    + split; [left; split; reflexivity|]. split; [exact Hl1 | lia].
    + split; [right; split; reflexivity|]. split; [exact Hl1 | rewrite Zlen_cons; lia].
Qed.

Lemma nty_exit : forall op xs d,
  nty op xs d -> (op = OP_TYPE_INT \/ op = OP_TYPE_FLOAT) ->
  (xs = [] \/ (xs <> [] /\ 42 <= last xs 0)) ->
  (op = OP_TYPE_INT -> 4 <= d) /\ 3 <= d.
Proof.
  intros op xs d H Hop Hex. destruct (H Hop) as [H4|(ys & Hf & Hl & Hc)]; [split; lia|].
  destruct ys as [|x ys'] using rev_ind.
  - destruct Hf as [[-> ->]|[-> ->]]; rewrite ?Zlen_cons, Zlen_nil in Hc; [split; lia|]. split; [intros E; cbv in E; discriminate | lia].
  - destruct (lits_snoc_inv _ _ Hl) as [_ Hx]. exfalso.
    assert (HL : xs <> [] /\ last xs 0 = x).
    { destruct Hf as [[-> ->]|[-> ->]].
      - split; [destruct ys'; discriminate | apply last_last].
      - change (OT_OPTIONAL_FPENCODING :: ys' ++ [x]) with ((OT_OPTIONAL_FPENCODING :: ys') ++ [x]). split; [discriminate | apply last_last]. }
    destruct HL as [Hne HL]. destruct Hex as [-> | [_ H42]]; [exact (Hne eq_refl)|]. rewrite HL in H42.
    destruct Hx as [-> | ->]; cbv in H42; apply H42; reflexivity.
Qed.

Definition ridc (xs : list Z) : Z := Z.of_nat (count_occ Z.eq_dec xs OT_RESULT_ID).

Lemma ridc_app : forall a b, ridc (a ++ b) = ridc a + ridc b.
Proof. intros a b. unfold ridc. rewrite count_occ_app. lia. Qed.
Lemma ridc_nil : ridc [] = 0.
Proof. reflexivity. Qed.
Lemma ridc_cons : forall x l, ridc (x :: l) = (if Z.eq_dec x OT_RESULT_ID then 1 else 0) + ridc l.
Proof. intros x l. unfold ridc. cbn [count_occ]. destruct (Z.eq_dec x OT_RESULT_ID); destruct (Z.eq_dec OT_RESULT_ID x); try congruence; lia. Qed.
Lemma ridc_nonneg : forall l, 0 <= ridc l.
Proof. intros l. unfold ridc. apply Nat2Z.is_nonneg. Qed.
Lemma ridc_notin : forall l, ~ In OT_RESULT_ID l -> ridc l = 0.
Proof. intros l H. unfold ridc. rewrite (count_occ_not_In Z.eq_dec l OT_RESULT_ID) in H. lia. Qed.
Lemma ridc_snoc : forall l x, ridc (l ++ [x]) = ridc l + (if Z.eq_dec x OT_RESULT_ID then 1 else 0).
Proof. intros l x. rewrite ridc_app, ridc_cons, ridc_nil. lia. Qed.
Lemma ridc_le1_of_count : forall l, (count_occ Z.eq_dec l OT_RESULT_ID <= 1)%nat -> ridc l <= 1.
Proof. intros l H. unfold ridc. lia. Qed.
Lemma ridc_rev : forall l, ridc (rev l) = ridc l.
Proof. intros l. unfold ridc. rewrite count_occ_rev. reflexivity. Qed.
Lemma bfilter_nil : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)), base.filter P (@nil Z) = [].
Proof. intros. reflexivity. Qed.
Lemma bfilter_cons : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) x l,
  base.filter P (x :: l) = if base.decide (P x) then x :: base.filter P l else base.filter P l.
Proof. intros. reflexivity. Qed.
Lemma ridc_filter_le : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) l, ridc (base.filter P l) <= ridc l.
Proof.
  intros P H l. induction l as [|x l IH]; [rewrite bfilter_nil; lia|]. rewrite bfilter_cons.
  destruct (base.decide (P x)); rewrite ?ridc_cons; destruct (Z.eq_dec x OT_RESULT_ID); lia.
Qed.
Lemma ridc_push_types_nil : forall l, ridc (push_types l []) <= ridc l.
Proof. intros l. unfold push_types. cbn [app]. etransitivity; [apply ridc_filter_le|]. rewrite ridc_rev. lia. Qed.

Lemma ridc_take_first : forall xs, xs <> [] ->
  ridc (snd (take_first xs)) + (if Z.eq_dec (fst (take_first xs)) OT_RESULT_ID then 1 else 0) <= ridc xs.
Proof.
  intros xs Hne. destruct xs as [|u r _] using rev_ind; [exfalso; exact (Hne eq_refl)|].
  destruct (expand u) as [e|] eqn:E.
  - rewrite (take_first_exp _ e) by (rewrite last_last; exact E). cbn [fst snd]. rewrite removelast_last, ridc_app, ridc_snoc.
    destruct (expand_cases u) as [[-> E2]|[[-> E2]|[[-> E2]|[[-> E2]|[[-> E2]|E2]]]]]; rewrite E2 in E; try discriminate;
      injection E; intros <-; cbn [removelast last app]; rewrite ?ridc_cons, ?ridc_nil; unfold_OT; repeat destruct (Z.eq_dec _ _); try lia.
  - rewrite (take_first_noexp _) by (rewrite last_last; exact E). cbn [fst snd]. rewrite removelast_last, last_last, ridc_snoc. pose proof (ridc_nonneg r). lia.
Qed.

Lemma take_first_snoc_rid : forall ys, take_first (ys ++ [OT_RESULT_ID]) = (OT_RESULT_ID, ys).
Proof. intros ys. rewrite take_first_noexp by (rewrite last_last; reflexivity). rewrite last_last, removelast_last. reflexivity. Qed.

