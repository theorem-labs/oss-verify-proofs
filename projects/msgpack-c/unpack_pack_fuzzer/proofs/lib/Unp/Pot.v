(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module Pot.

Definition UNIT : Z := 48.
Definition Q0 : Z := 2 ^ 27.
Definition BIG_CHUNK : Z := 65544.
Definition BIG_PAIRS : Z := 683.

Definition objs_rest (l : level) : Z :=
  match lv_t l with
  | CT_ARRAY_ITEM => lv_rest l
  | CT_MAP_KEY => 2 * lv_rest l
  | CT_MAP_VALUE => 2 * lv_rest l - 1
  end.
Fixpoint objs_sum (ls : list level) : Z := match ls with [] => 0 | l :: ls' => objs_rest l + objs_sum ls' end.
Definition debt (ls : list level) : Z := UNIT * objs_sum ls - UNIT * Z.of_nat (length ls).
Definition pot (ls : list level) : Z := Q0 - debt ls.

Lemma objs_sum_app : forall a b, objs_sum (a ++ b) = objs_sum a + objs_sum b.
Proof. induction a as [|x a IH]; intros b; cbn [app objs_sum]; [lia| rewrite IH; lia]. Qed.

Lemma objs_rest_range : forall l, level_valid l -> 1 <= objs_rest l <= 2 * LIMIT.
Proof. intros l (V1 & V2 & V3 & _). unfold objs_rest. destruct (lv_t l); unfold LIMIT in *; lia. Qed.

Lemma objs_sum_range : forall ls, Forall level_valid ls -> Z.of_nat (length ls) <= objs_sum ls <= 2 * LIMIT * Z.of_nat (length ls).
Proof.
  induction ls as [|l ls IH]; intros F; [cbn; lia|]. inversion F as [|x y Vl Fl]; subst.
  pose proof (objs_rest_range l Vl) as R. specialize (IH Fl). cbn [objs_sum length]. rewrite Nat2Z.inj_succ. unfold LIMIT in *. lia.
Qed.

Lemma debt_range : forall ls, Forall level_valid ls -> Z.of_nat (length ls) <= LIMIT -> 0 <= debt ls <= UNIT * (2 * LIMIT - 1) * LIMIT.
Proof.
  intros ls F D. pose proof (objs_sum_range ls F) as R. unfold debt, UNIT, LIMIT in *. nia.
Qed.
Lemma pot_range : forall ls, Forall level_valid ls -> Z.of_nat (length ls) <= LIMIT -> 0 <= pot ls <= Q0.
Proof.
  intros ls F D. pose proof (debt_range ls F D) as R. unfold pot, Q0, UNIT, LIMIT in *.
  change (2 ^ 27) with 134217728. lia.
Qed.
Lemma pot_nil : pot [] = Q0.
Proof. reflexivity. Qed.

Definition objs_of (t : ctype) (n : Z) : Z := per t * n.
Lemma objs_rest_new : forall t n P, t <> CT_MAP_VALUE -> objs_rest (new_level t n P) = objs_of t n.
Proof. intros t n P H. unfold objs_rest, new_level, objs_of, per. cbn [lv_t lv_rest]. destruct t; [lia| lia| congruence]. Qed.
Lemma pot_push : forall ls t n P, t <> CT_MAP_VALUE -> pot (push_level ls t n P) = pot ls - (UNIT * objs_of t n - UNIT).
Proof.
  intros ls t n P H. unfold pot, debt, push_level. rewrite objs_sum_app, length_app. cbn [objs_sum length].
  rewrite (objs_rest_new t n P H), Nat2Z.inj_add. change (Z.of_nat 1) with 1. lia.
Qed.

Lemma objs_rest_ret : forall l l', consume_top l = CS_Ret l' -> objs_rest l' = objs_rest l - 1.
Proof.
  intros [t n r P] l' H. unfold consume_top in H. cbn [lv_t lv_rest lv_n lv_P] in H. unfold objs_rest. destruct t; cbn [lv_t lv_rest].
  - destruct (r =? 1); [discriminate|]. injection H as <-. cbn [lv_t lv_rest]. lia.
  - injection H as <-. cbn [lv_t lv_rest]. lia.
  - destruct (r =? 1); [discriminate|]. injection H as <-. cbn [lv_t lv_rest]. lia.
Qed.
Lemma pot_ret : forall ls l l', consume_top l = CS_Ret l' -> pot (ls ++ [l']) = pot (ls ++ [l]) + UNIT.
Proof.
  intros ls l l' H. unfold pot, debt. rewrite !objs_sum_app, !length_app. cbn [objs_sum length]. rewrite (objs_rest_ret l l' H). lia.
Qed.

Lemma objs_rest_pop : forall l, consume_top l = CS_Pop -> objs_rest l = 1.
Proof.
  intros l H. destruct (consume_top_pop l H) as [R T]. unfold objs_rest. destruct (lv_t l); [lia| congruence| lia].
Qed.
Lemma pot_pop : forall ls l, consume_top l = CS_Pop -> pot ls = pot (ls ++ [l]).
Proof.
  intros ls l H. unfold pot, debt. rewrite objs_sum_app, length_app. cbn [objs_sum length]. rewrite (objs_rest_pop l H), Nat2Z.inj_add.
  change (Z.of_nat 1) with 1. lia.
Qed.

Lemma big_map_pays : forall n h, BIG_PAIRS <= n -> 1 <= h -> BIG_CHUNK <= UNIT * h + (UNIT * objs_of CT_MAP_KEY n - UNIT).
Proof. intros n h Hn Hh. unfold BIG_CHUNK, BIG_PAIRS, UNIT, objs_of, per in *. lia. Qed.

Lemma element_pays : forall k, 1 <= k -> UNIT <= UNIT * k.
Proof. intros k H. unfold UNIT. lia. Qed.

Definition pk10_tree (o : obj) : Z := 10 * Z.of_nat (obj_size o) + Cost.obj_bodies o.
Definition pk10_trees (l : list obj) : Z := 10 * Z.of_nat (objs_size l) + Cost.objs_bodies l.

Lemma pk10_trees_nil : pk10_trees [] = 0. Proof. reflexivity. Qed.
Lemma pk10_trees_cons1 : forall o, pk10_trees [o] = pk10_tree o.
Proof.
  intros o. unfold pk10_trees, pk10_tree, objs_size, Cost.objs_bodies. cbn [map list_sum fold_right].
  rewrite Nat.add_0_r. lia.
Qed.
Lemma objs_size_app : forall l1 l2, objs_size (l1 ++ l2) = (objs_size l1 + objs_size l2)%nat.
Proof. intros l1 l2. unfold objs_size. rewrite map_app, list_sum_app. reflexivity. Qed.
Lemma objs_bodies_app : forall l1 l2, Cost.objs_bodies (l1 ++ l2) = Cost.objs_bodies l1 + Cost.objs_bodies l2.
Proof.
  induction l1 as [|o l IH]; intros l2; [change (Cost.objs_bodies l2 = 0 + Cost.objs_bodies l2); lia|].
  change (Cost.obj_bodies o + Cost.objs_bodies (l ++ l2) = (Cost.obj_bodies o + Cost.objs_bodies l) + Cost.objs_bodies l2). rewrite IH. lia.
Qed.
Lemma pk10_trees_app : forall l1 l2, pk10_trees (l1 ++ l2) = pk10_trees l1 + pk10_trees l2.
Proof. intros l1 l2. unfold pk10_trees. rewrite objs_size_app, objs_bodies_app, Nat2Z.inj_add. lia. Qed.
Lemma pk10_tree_arr : forall p kids, pk10_tree (OArr p kids) = 10 + pk10_trees kids.
Proof. intros p kids. unfold pk10_tree, pk10_trees. rewrite obj_size_arr, Cost.obj_bodies_arr, Nat2Z.inj_succ. lia. Qed.
Lemma pk10_tree_map : forall p kids, pk10_tree (OMap p kids) = 10 + pk10_trees kids.
Proof. intros p kids. unfold pk10_tree, pk10_trees. rewrite obj_size_map, Cost.obj_bodies_map, Nat2Z.inj_succ. lia. Qed.
Lemma pk10_tree_ge : forall m z o, tree_wf m z o -> 10 <= pk10_tree o.
Proof. intros m z o W. unfold pk10_tree. pose proof (Cost.obj_bodies_wf_nonneg m z o W). pose proof (Acct.obj_size_pos o). lia. Qed.
Lemma pk10_tree_scalar : forall o, match o with OArr _ _ | OMap _ _ | OStr _ _ | OBin _ _ | OExt _ _ => False | _ => True end -> pk10_tree o = 10.
Proof. intros o H. destruct o; try contradiction; reflexivity. Qed.
Lemma pk10_tree_str : forall p n, pk10_tree (OStr p n) = 10 + n. Proof. intros. unfold pk10_tree; cbn. lia. Qed.
Lemma pk10_tree_bin : forall p n, pk10_tree (OBin p n) = 10 + n. Proof. intros. unfold pk10_tree; cbn. lia. Qed.
Lemma pk10_tree_ext : forall p n, pk10_tree (OExt p n) = 10 + (n + 1). Proof. intros. unfold pk10_tree; cbn. lia. Qed.

Lemma container_kids_pk : forall m z a c, tree_at m z a c -> (obj_type c = T_ARRAY \/ obj_type c = T_MAP) ->
  exists K, (forall i o', nth_error K i = Some o' -> tree_at m z (obj_ptr c + OBJ_SIZE * Z.of_nat i) o') /\
            pk10_tree c = 10 + pk10_trees K /\
            ((obj_type c = T_ARRAY /\ Z.of_nat (length K) = obj_count c) \/ (obj_type c = T_MAP /\ Nat.Even (length K) /\ Z.of_nat (length K) / 2 = obj_count c)).
Proof.
  intros m z a c [A W] TY. destruct c; cbn [obj_type] in TY; try (exfalso; destruct TY as [TY|TY]; discriminate).
  - exists kids. apply obj_at_arr in A. destruct A as (_ & _ & _ & K1). apply tree_wf_arr in W. destruct W as (_ & _ & _ & T1).
    split; [intros i o' Hn; cbn [obj_ptr]; exact (Acct.objs_at_nth m z kids p i o' K1 T1 Hn)|].
    split; [apply pk10_tree_arr|]. left; split; reflexivity.
  - exists kids. apply obj_at_map in A. destruct A as (_ & _ & _ & K1). apply tree_wf_map in W. destruct W as (E1 & _ & _ & _ & T1).
    split; [intros i o' Hn; cbn [obj_ptr]; exact (Acct.objs_at_nth m z kids p i o' K1 T1 Hn)|].
    split; [apply pk10_tree_map|]. right; split; [reflexivity|]; split; [apply even_len_spec; exact E1| reflexivity].
Qed.

Definition kids_pk (m : bmem) (z : zoneg) (ls : list level) (S : Z) : Prop :=
  exists oss, Forall2 (Acct.kids_at m z) ls oss /\ S = Acct.zsum (map pk10_trees oss).

Lemma kids_pk_nil : forall m z, kids_pk m z [] 0.
Proof. intros m z. exists []. split; [constructor| reflexivity]. Qed.
Lemma kids_pk_nil_inv : forall m z S, kids_pk m z [] S -> S = 0.
Proof. intros m z S (oss & F & ->). inversion F. reflexivity. Qed.
Lemma kids_pk_nonneg : forall m z ls S, kids_pk m z ls S -> 0 <= S.
Proof.
  intros m z ls S (oss & F & ->). apply Acct.zsum_nonneg. apply Forall_map.
  induction F as [|l os ls' oss' [Hlen Hk] F IH]; constructor; [| exact IH].
  unfold pk10_trees. assert (0 <= Cost.objs_bodies os); [| lia].
  clear Hlen. revert Hk. generalize (Acct.kid_addr l). intros ka Hk.
  assert (W : forall o, In o os -> exists a, tree_at m z a o).
  { intros o Ho. apply In_nth_error in Ho as (i & Hi). exists (ka i). exact (Hk i o Hi). }
  clear Hk. induction os as [|o os IHo]; [cbn; lia|]. cbn [Cost.objs_bodies fold_right]. fold (Cost.objs_bodies os).
  destruct (W o (or_introl eq_refl)) as (a & _ & Wo). pose proof (Cost.obj_bodies_wf_nonneg m z o Wo).
  specialize (IHo (fun o' H' => W o' (or_intror H'))). lia.
Qed.

Lemma kids_pk_frame : forall m m' z z' ls S,
  (forall l i o, In l ls -> Z.of_nat i < lv_k l -> tree_at m z (Acct.kid_addr l i) o -> tree_at m' z' (Acct.kid_addr l i) o) ->
  kids_pk m z ls S -> kids_pk m' z' ls S.
Proof.
  intros m m' z z' ls S FW (oss & F & ->). exists oss. split; [| reflexivity].
  induction F as [|l os ls' oss' [Hlen Hk] F IH]; constructor.
  - split; [exact Hlen|]. intros i o Hn. apply FW; [now left| |now apply Hk]. pose proof (Acct.nth_error_lt os i o Hn). lia.
  - apply IH. intros l0 i o Hl0 Hi Ht. apply FW; [now right| exact Hi| exact Ht].
Qed.

Lemma kids_pk_push : forall m z ls S l, kids_pk m z ls S -> lv_k l = 0 -> kids_pk m z (ls ++ [l]) S.
Proof.
  intros m z ls S l (oss & F & ->) Hk. exists (oss ++ [[]]). split.
  - apply Forall2_app; [exact F|]. constructor; [|constructor]. split; [cbn; lia|]. intros [|i] o Hn; discriminate.
  - rewrite map_app, Acct.zsum_app. cbn [map Acct.zsum fold_right]. rewrite pk10_trees_nil. lia.
Qed.

Lemma kids_pk_ret : forall m z ls l l' S o, consume_top l = CS_Ret l' -> level_valid l ->
  kids_pk m z (ls ++ [l]) S -> tree_at m z (lv_slot l) o -> kids_pk m z (ls ++ [l']) (S + pk10_tree o).
Proof.
  intros m z ls l l' S o Hc V (oss & F & ->) Ht.
  destruct (consume_top_ret l l' Hc V) as (_ & HP & _ & HK & _).
  destruct (Acct.Forall2_snoc_inv _ ls l oss F) as (oss1 & os & -> & F1 & [Hlen Hk]).
  exists (oss1 ++ [os ++ [o]]). split.
  - apply Forall2_app; [exact F1|]. constructor; [|constructor]. split.
    + rewrite length_app. cbn [length]. rewrite HK. lia.
    + intros i o' Hn. unfold Acct.kid_addr. rewrite HP. destruct (Nat.lt_ge_cases i (length os)) as [Hi|Hi].
      * rewrite nth_error_app1 in Hn by exact Hi. exact (Hk i o' Hn).
      * rewrite nth_error_app2 in Hn by exact Hi. destruct (i - length os)%nat as [|k] eqn:E; cbn in Hn; [|destruct k; discriminate].
        injection Hn as <-. replace (Z.of_nat i) with (lv_k l) by lia. unfold lv_slot in Ht. exact Ht.
  - rewrite !map_app, !Acct.zsum_app. cbn [map Acct.zsum fold_right]. rewrite pk10_trees_app, pk10_trees_cons1. lia.
Qed.

Lemma kids_pk_pop_core : forall m z ls l S o c K, consume_top l = CS_Pop -> level_valid l ->
  kids_pk m z (ls ++ [l]) S -> tree_at m z (lv_slot l) o ->
  (forall i o', nth_error K i = Some o' -> tree_at m z (lv_P l + OBJ_SIZE * Z.of_nat i) o') -> pk10_tree c = 10 + pk10_trees K ->
  Z.of_nat (length K) = lv_k l + 1 ->
  exists S1, kids_pk m z ls S1 /\ S + pk10_tree o + 10 = S1 + pk10_tree c.
Proof.
  intros m z ls l S o c K Hc V (oss & F & ->) Ht HK COST HKlen.
  destruct (Acct.Forall2_snoc_inv _ ls l oss F) as (oss1 & os & -> & F1 & [Hlen Hk]).
  assert (HKeq : K = os ++ [o]).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length K)) as [Hi|Hi].
    - destruct (nth_error K i) as [x|] eqn:E; [|exfalso; apply (proj2 (nth_error_Some K i) Hi); exact E].
      pose proof (HK i x E) as Tx.
      destruct (Nat.lt_ge_cases i (length os)) as [Hi2|Hi2].
      + rewrite nth_error_app1 by exact Hi2. destruct (nth_error os i) as [y|] eqn:E2; [|exfalso; apply (proj2 (nth_error_Some os i) Hi2); exact E2].
        f_equal. pose proof (Hk i y E2) as Ty. unfold Acct.kid_addr in Ty. exact (Acct.tree_at_unique _ _ _ _ _ Tx Ty).
      + rewrite nth_error_app2 by exact Hi2. replace (i - length os)%nat with 0%nat by lia. cbn. f_equal.
        replace (Z.of_nat i) with (lv_k l) in Tx by lia. unfold lv_slot in Ht. exact (Acct.tree_at_unique _ _ _ _ _ Tx Ht).
    - destruct (nth_error K i) eqn:E; [exfalso; pose proof (Acct.nth_error_lt _ _ _ E); lia|].
      destruct (nth_error (os ++ [o]) i) eqn:E2; [exfalso; pose proof (Acct.nth_error_lt _ _ _ E2) as L2; rewrite length_app in L2; cbn in L2; lia| reflexivity]. }
  subst K. rewrite pk10_trees_app, pk10_trees_cons1 in COST.
  exists (Acct.zsum (map pk10_trees oss1)). split; [exists oss1; split; [exact F1| reflexivity]|].
  rewrite map_app, Acct.zsum_app. cbn [map Acct.zsum fold_right]. lia.
Qed.

Lemma pop_kids_len : forall l c (K : list obj), level_valid l -> consume_top l = CS_Pop ->
  obj_type c = container_type (lv_t l) -> obj_count c = lv_n l ->
  ((obj_type c = T_ARRAY /\ Z.of_nat (length K) = obj_count c) \/ (obj_type c = T_MAP /\ Nat.Even (length K) /\ Z.of_nat (length K) / 2 = obj_count c)) ->
  Z.of_nat (length K) = lv_k l + 1.
Proof.
  intros l c K V Hc TY CNT LEN. destruct (consume_top_pop l Hc) as [R1 NK]. pose proof (pop_full l V R1 NK) as FULL.
  unfold lv_bytes in FULL. unfold lv_k in *. rewrite TY in LEN. destruct (lv_t l); cbn [container_type per] in LEN, FULL |- *.
  - destruct LEN as [[_ L]|[X0 _]]; [|discriminate]. rewrite CNT in L. unfold OBJ_SIZE in FULL. lia.
  - exfalso. apply NK. reflexivity.
  - destruct LEN as [[X0 _]|(_ & EV & L)]; [discriminate|]. rewrite CNT in L. unfold OBJ_SIZE in FULL.
    destruct EV as [q Hq]. rewrite Hq in L |- *. rewrite Nat2Z.inj_mul in L |- *. change (Z.of_nat 2) with 2 in *.
    rewrite Z.mul_comm, Z.div_mul in L by lia. lia.
Qed.
Lemma kids_pk_pop : forall m z ls l S o hdr c, consume_top l = CS_Pop -> level_valid l ->
  kids_pk m z (ls ++ [l]) S -> tree_at m z (lv_slot l) o ->
  tree_at m z hdr c -> obj_type c = container_type (lv_t l) -> obj_count c = lv_n l -> obj_ptr c = lv_P l ->
  exists S1, kids_pk m z ls S1 /\ S + pk10_tree o + 10 = S1 + pk10_tree c.
Proof.
  intros m z ls l S o hdr c Hc V KP Ht Tc TY CNT PTR.
  assert (TY2 : obj_type c = T_ARRAY \/ obj_type c = T_MAP) by (rewrite TY; destruct (lv_t l); cbn; auto).
  destruct (container_kids_pk m z hdr c Tc TY2) as (K & HK & COST & LEN). rewrite PTR in HK.
  exact (kids_pk_pop_core m z ls l S o c K Hc V KP Ht HK COST (pop_kids_len l c K V Hc TY CNT LEN)).
Qed.

Lemma kids_pk_pop_k : forall m z ls l S o c, consume_top l = CS_Pop -> level_valid l ->
  kids_pk m z (ls ++ [l]) S -> tree_at m z (lv_slot l) o ->
  tree_wf m z c -> match c with OArr p kids | OMap p kids => objs_at m p kids | _ => True end ->
  obj_type c = container_type (lv_t l) -> obj_count c = lv_n l -> obj_ptr c = lv_P l ->
  exists S1, kids_pk m z ls S1 /\ S + pk10_tree o + 10 = S1 + pk10_tree c.
Proof.
  intros m z ls l S o c Hc V KP Ht TW KA TY CNT PTR.
  assert (KIDS : exists K, (forall i o', nth_error K i = Some o' -> tree_at m z (lv_P l + OBJ_SIZE * Z.of_nat i) o') /\ pk10_tree c = 10 + pk10_trees K /\
            ((obj_type c = T_ARRAY /\ Z.of_nat (length K) = obj_count c) \/ (obj_type c = T_MAP /\ Nat.Even (length K) /\ Z.of_nat (length K) / 2 = obj_count c))).
  { destruct c; cbn [obj_type] in TY; try (exfalso; destruct (lv_t l); cbn in TY; discriminate TY).
    - exists kids. cbn [obj_ptr] in PTR. subst p. apply tree_wf_arr in TW. destruct TW as (_ & _ & _ & T1).
      split; [intros i o' Hn; exact (Acct.objs_at_nth m z kids _ i o' KA T1 Hn)|]. split; [apply pk10_tree_arr|]. left; split; reflexivity.
    - exists kids. cbn [obj_ptr] in PTR. subst p. apply tree_wf_map in TW. destruct TW as (E1 & _ & _ & _ & T1).
      split; [intros i o' Hn; exact (Acct.objs_at_nth m z kids _ i o' KA T1 Hn)|]. split; [apply pk10_tree_map|].
      right; split; [reflexivity|]; split; [apply even_len_spec; exact E1| reflexivity]. }
  destruct KIDS as (K & HK & COST & LEN).
  exact (kids_pk_pop_core m z ls l S o c K Hc V KP Ht HK COST (pop_kids_len l c K V Hc TY CNT LEN)).
Qed.

Definition pot_val (ls : list level) (S pend : Z) : Z := pot ls + 4 * (10 * Z.of_nat (length ls) + S + pend).

Lemma pot_val_nil : forall p, pot_val [] 0 p = Q0 + 4 * p.
Proof. intros p. unfold pot_val. rewrite pot_nil. cbn [length]. lia. Qed.
Lemma pot_val_nonneg : forall ls S p, Forall level_valid ls -> Z.of_nat (length ls) <= LIMIT -> 0 <= S -> 0 <= p -> 0 <= pot_val ls S p.
Proof. intros ls S p F D HS Hp. pose proof (pot_range ls F D). unfold pot_val. lia. Qed.

Lemma pot_val_push : forall ls t n P S, t <> CT_MAP_VALUE ->
  pot_val (push_level ls t n P) S 0 = pot_val ls S 0 + 4 * 10 + UNIT - UNIT * objs_of t n.
Proof.
  intros ls t n P S H. unfold pot_val. rewrite (pot_push ls t n P H). unfold push_level. rewrite length_app. cbn [length].
  rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. lia.
Qed.

Lemma pot_val_item : forall ls S p, pot_val ls S p = pot_val ls S 0 + 4 * p.
Proof. intros. unfold pot_val. lia. Qed.

Lemma pot_val_ret : forall ls l l' S p, consume_top l = CS_Ret l' -> pot_val (ls ++ [l']) (S + p) 0 = pot_val (ls ++ [l]) S p + UNIT.
Proof. intros ls l l' S p H. unfold pot_val. rewrite (pot_ret ls l l' H), !length_app. cbn [length]. lia. Qed.

Lemma pot_val_pop : forall ls l S S1 po pc, consume_top l = CS_Pop -> S + po + 10 = S1 + pc -> pot_val ls S1 pc = pot_val (ls ++ [l]) S po.
Proof.
  intros ls l S S1 po pc H EQ. unfold pot_val. rewrite <- (pot_pop ls l H), length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. lia.
Qed.

Lemma big_map_pays88 : forall M h, 32762 <= M -> 2 <= h -> BIG_CHUNK <= 88 * h + (2 * M - UNIT) - 4 * 10.
Proof. intros M h HM Hh. unfold BIG_CHUNK, UNIT. lia. Qed.
Lemma body_pays88 : forall n, 0 <= n -> 4 * (10 + n) + UNIT <= 88 * (1 + n).
Proof. intros n H. unfold UNIT. lia. Qed.

End Pot.
