(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Cost Steps StepsX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma u8_at_inj : forall m a v v', u8_at m a v -> u8_at m a v' -> v = v'.
Proof. intros m a v v' H H'. unfold u8_at in *. congruence. Qed.

Lemma enc64_inj_neg : forall i i', - 2 ^ 64 <= i < 0 -> - 2 ^ 64 <= i' < 0 -> enc64 i = enc64 i' -> i = i'.
Proof.
  intros i i' Hi Hi' E. unfold enc64 in E.
  replace (i mod 2 ^ 64) with (i + 2 ^ 64) in E by (symmetry; rewrite <- (Z_mod_plus_full i 1 (2 ^ 64)); apply Z.mod_small; lia).
  replace (i' mod 2 ^ 64) with (i' + 2 ^ 64) in E by (symmetry; rewrite <- (Z_mod_plus_full i' 1 (2 ^ 64)); apply Z.mod_small; lia).
  lia.
Qed.

Lemma even_half_inj : forall (a b : nat), Nat.Even a -> Nat.Even b -> Z.of_nat a / 2 = Z.of_nat b / 2 -> a = b.
Proof.
  intros a b [p ->] [q ->] E. rewrite !Nat2Z.inj_mul in E. change (Z.of_nat 2) with 2 in E.
  rewrite !(Z.mul_comm 2), !Z.div_mul in E by lia. lia.
Qed.

Lemma objs_at_unique : forall m z l,
  (forall o, In o l -> forall a o', tree_wf m z o -> tree_wf m z o' -> obj_at m a o -> obj_at m a o' -> o = o') ->
  forall p l', length l = length l' -> trees_wf m z l -> trees_wf m z l' -> objs_at m p l -> objs_at m p l' -> l = l'.
Proof.
  intros m z l IH. induction l as [|x l IHl]; intros p [|x' l'] Hlen W W' A A'; try discriminate; [reflexivity|].
  cbn in Hlen, W, W', A, A'. destruct W as [Wx Wl], W' as [Wx' Wl'], A as [Ax Al], A' as [Ax' Al'].
  f_equal.
  - apply (IH x ltac:(now left) p x' Wx Wx' Ax Ax').
  - apply (IHl ltac:(intros o Ho; apply IH; now right) (p + OBJ_SIZE) l' ltac:(lia) Wl Wl' Al Al').
Qed.

Lemma obj_at_unique : forall m z o a o', tree_wf m z o -> tree_wf m z o' -> obj_at m a o -> obj_at m a o' -> o = o'.
Proof.
  intros m z. apply (obj_ind_size (fun o => forall a o', tree_wf m z o -> tree_wf m z o' -> obj_at m a o -> obj_at m a o' -> o = o')).
  intros o IH a o' W W' A A'.
  assert (TY : obj_type o = obj_type o').
  { destruct o; destruct o'; cbn [obj_at] in A, A'; exact (u32_at_inj m a _ _ (proj1 A) (proj1 A')). }
  destruct o; destruct o'; cbn [obj_type] in TY; try discriminate; try reflexivity; cbn [obj_at] in A, A'.
  - f_equal. destruct A as [_ A], A' as [_ A']. pose proof (u8_at_inj m _ _ _ A A') as E. destruct b, b0; cbn in E; congruence.
  - f_equal. exact (u64_at_inj m _ _ _ (proj2 A) (proj2 A')).
  - f_equal. cbn [tree_wf] in W, W'. apply (enc64_inj_neg i i0 W W'). exact (u64_at_inj m _ _ _ (proj2 A) (proj2 A')).
  - f_equal. exact (u64_at_inj m _ _ _ (proj2 A) (proj2 A')).
  - f_equal. exact (u64_at_inj m _ _ _ (proj2 A) (proj2 A')).
  - destruct A as (_ & A1 & A2), A' as (_ & A1' & A2'). f_equal; [exact (u64_at_inj m _ _ _ A2 A2') | exact (u32_at_inj m _ _ _ A1 A1')].
  - destruct A as (_ & A1 & A2), A' as (_ & A1' & A2'). f_equal; [exact (u64_at_inj m _ _ _ A2 A2') | exact (u32_at_inj m _ _ _ A1 A1')].
  - destruct A as (_ & A1 & A2), A' as (_ & A1' & A2'). f_equal; [exact (u64_at_inj m _ _ _ A2 A2') | exact (u32_at_inj m _ _ _ A1 A1')].
  -   apply obj_at_arr in A. apply obj_at_arr in A'. destruct A as (_ & C1 & P1 & K1), A' as (_ & C2 & P2 & K2).
    pose proof (u64_at_inj m _ _ _ P1 P2) as <-. pose proof (u32_at_inj m _ _ _ C1 C2) as EL. apply Nat2Z.inj in EL.
    apply tree_wf_arr in W. apply tree_wf_arr in W'. destruct W as (_ & _ & _ & T1), W' as (_ & _ & _ & T2).
    f_equal. apply (objs_at_unique m z kids) with (p := p); try assumption.
    intros o Ho a0 o' Wo Wo' Ao Ao'. apply (IH o ltac:(rewrite obj_size_arr; pose proof (in_kids_size o kids Ho); lia) a0 o' Wo Wo' Ao Ao').
  -   apply obj_at_map in A. apply obj_at_map in A'. destruct A as (_ & C1 & P1 & K1), A' as (_ & C2 & P2 & K2).
    pose proof (u64_at_inj m _ _ _ P1 P2) as <-. pose proof (u32_at_inj m _ _ _ C1 C2) as EL.
    apply tree_wf_map in W. apply tree_wf_map in W'. destruct W as (E1 & _ & _ & _ & T1), W' as (E2 & _ & _ & _ & T2).
    apply even_len_spec in E1. apply even_len_spec in E2. pose proof (even_half_inj _ _ E1 E2 EL) as HL.
    f_equal. apply (objs_at_unique m z kids) with (p := p); try assumption.
    intros o Ho a0 o' Wo Wo' Ao Ao'. apply (IH o ltac:(rewrite obj_size_map; pose proof (in_kids_size o kids Ho); lia) a0 o' Wo Wo' Ao Ao').
Qed.

Lemma tree_at_unique : forall m z a o o', tree_at m z a o -> tree_at m z a o' -> o = o'.
Proof. intros m z a o o' [A W] [A' W']. exact (obj_at_unique m z o a o' W W' A A'). Qed.

Lemma objs_at_nth : forall m z l p i o, objs_at m p l -> trees_wf m z l -> nth_error l i = Some o ->
  tree_at m z (p + OBJ_SIZE * Z.of_nat i) o.
Proof.
  intros m z l. induction l as [|x l IH]; intros p i o A W Hn; [destruct i; discriminate|].
  cbn in A, W. destruct A as [Ax Al], W as [Wx Wl]. destruct i as [|i]; cbn in Hn.
  - injection Hn as <-. rewrite Z.mul_0_r, Z.add_0_r. split; assumption.
  - replace (p + OBJ_SIZE * Z.of_nat (S i)) with (p + OBJ_SIZE + OBJ_SIZE * Z.of_nat i) by lia. apply IH; assumption.
Qed.

Lemma container_kids : forall m z a c, tree_at m z a c -> (obj_type c = T_ARRAY \/ obj_type c = T_MAP) ->
  exists K, (forall i o', nth_error K i = Some o' -> tree_at m z (obj_ptr c + OBJ_SIZE * Z.of_nat i) o') /\
            tree_cost c = 1 + trees_cost K /\ obj_depth c = S (objs_depth K) /\
            ((obj_type c = T_ARRAY /\ Z.of_nat (length K) = obj_count c) \/ (obj_type c = T_MAP /\ Nat.Even (length K) /\ Z.of_nat (length K) / 2 = obj_count c)) /\
            Forall (fun o' => tree_wf m z o') K.
Proof.
  intros m z a c [A W] TY. destruct c; cbn [obj_type] in TY; try (exfalso; destruct TY as [TY|TY]; discriminate).
  - exists kids. apply obj_at_arr in A. destruct A as (_ & _ & _ & K1). apply tree_wf_arr in W. destruct W as (_ & _ & _ & T1).
    split; [intros i o' Hn; cbn [obj_ptr]; exact (objs_at_nth m z kids p i o' K1 T1 Hn)|].
    split; [apply tree_cost_arr|]. split; [apply obj_depth_arr|]. split; [left; split; reflexivity|]. apply Forall_forall. apply trees_wf_forall. exact T1.
  - exists kids. apply obj_at_map in A. destruct A as (_ & _ & _ & K1). apply tree_wf_map in W. destruct W as (E1 & _ & _ & _ & T1).
    split; [intros i o' Hn; cbn [obj_ptr]; exact (objs_at_nth m z kids p i o' K1 T1 Hn)|].
    split; [apply tree_cost_map|]. split; [apply obj_depth_map|]. split; [right; split; [reflexivity|]; split; [apply even_len_spec; exact E1| reflexivity]|].
    apply Forall_forall. apply trees_wf_forall. exact T1.
Qed.

Definition kid_addr (l : level) (i : nat) : Z := lv_P l + OBJ_SIZE * Z.of_nat i.

Definition kids_at (m : bmem) (z : zoneg) (l : level) (os : list obj) : Prop :=
  Z.of_nat (length os) = lv_k l /\ forall i o, nth_error os i = Some o -> tree_at m z (kid_addr l i) o.
Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Definition acct_ok (m : bmem) (z : zoneg) (ls : list level) (X : Z) : Prop :=
  exists oss, Forall2 (kids_at m z) ls oss /\
    Z.of_nat (length ls) + zsum (map trees_cost oss) <= X /\
    (forall j os, nth_error oss j = Some os -> (objs_depth os + j + 1 <= 1001)%nat) /\
    Forall (fun os => 0 <= trees_cost os) oss.

Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof.
  induction l1 as [|x l IH]; intros l2; [change (zsum l2 = 0 + zsum l2); lia|].
  change (x + zsum (l ++ l2) = (x + zsum l) + zsum l2). rewrite IH. lia.
Qed.
Lemma zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= zsum l.
Proof. induction l as [|x l IH]; intros H; [change (0 <= 0); lia|]. change (0 <= x + zsum l). inversion H; subst. specialize (IH ltac:(assumption)). lia. Qed.
Lemma trees_cost_nil : trees_cost [] = 0. Proof. reflexivity. Qed.
Lemma trees_cost_cons1 : forall o, trees_cost [o] = tree_cost o.
Proof. intros o. unfold trees_cost, tree_cost, objs_size, objs_bodies. cbn. lia. Qed.
Lemma objs_depth_nil : objs_depth [] = 0%nat. Proof. reflexivity. Qed.
Lemma objs_depth_cons1 : forall o, objs_depth [o] = obj_depth o. Proof. intros o. cbn. lia. Qed.
Lemma Forall2_length' : forall {A B} (P : A -> B -> Prop) l1 l2, Forall2 P l1 l2 -> length l1 = length l2.
Proof. intros A B P l1 l2 H. induction H; cbn; congruence. Qed.
Lemma Forall2_app_inv_l' : forall {A B} (P : A -> B -> Prop) l1 l2 r, Forall2 P (l1 ++ l2) r ->
  exists r1 r2, r = r1 ++ r2 /\ Forall2 P l1 r1 /\ Forall2 P l2 r2.
Proof. intros A B P l1 l2 r H. destruct (Forall2_app_inv_l l1 l2 H) as (r1 & r2 & H1 & H2 & ->). exists r1, r2. auto. Qed.
Lemma Forall2_snoc_inv : forall {A B} (P : A -> B -> Prop) ls l oss, Forall2 P (ls ++ [l]) oss ->
  exists oss1 os, oss = oss1 ++ [os] /\ Forall2 P ls oss1 /\ P l os.
Proof.
  intros A B P ls l oss H. destruct (Forall2_app_inv_l' P ls [l] oss H) as (r1 & r2 & -> & H1 & H2).
  inversion H2 as [|a b l1 l2 Hab Hnil]; subst. inversion Hnil; subst. exists r1, b. auto.
Qed.
Lemma tree_cost_wf_nonneg : forall m z o, tree_wf m z o -> 0 <= tree_cost o.
Proof. intros m z o W. unfold tree_cost. pose proof (obj_bodies_wf_nonneg m z o W). lia. Qed.
Lemma obj_size_pos : forall o, (1 <= obj_size o)%nat.
Proof. intros o. destruct o; cbn; lia. Qed.
Lemma tree_cost_pos : forall m z o, tree_wf m z o -> 1 <= tree_cost o.
Proof. intros m z o W. unfold tree_cost. pose proof (obj_bodies_wf_nonneg m z o W). pose proof (obj_size_pos o). lia. Qed.

Lemma acct_nil : forall m z X, 0 <= X -> acct_ok m z [] X.
Proof. intros m z X HX. exists []. split; [constructor|]. cbn. split; [lia|]. split; [intros [|j] os H; discriminate| constructor]. Qed.

Lemma acct_mono : forall m z ls X X', acct_ok m z ls X -> X <= X' -> acct_ok m z ls X'.
Proof. intros m z ls X X' (oss & F & B & D & N) HX. exists oss. repeat split; auto. lia. Qed.

Lemma acct_levels_bound : forall m z ls X, acct_ok m z ls X -> Z.of_nat (length ls) <= X.
Proof.
  intros m z ls X (oss & F & B & D & N). pose proof (zsum_nonneg (map trees_cost oss) ltac:(apply Forall_map; exact N)). lia.
Qed.

Lemma nth_error_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply (proj1 (nth_error_Some l i)). rewrite H. discriminate. Qed.

Lemma acct_frame : forall m m' z z' ls X,
  (forall l i o, In l ls -> Z.of_nat i < lv_k l -> tree_at m z (kid_addr l i) o -> tree_at m' z' (kid_addr l i) o) ->
  acct_ok m z ls X -> acct_ok m' z' ls X.
Proof.
  intros m m' z z' ls X FW (oss & F & B & D & N). exists oss. split; [|auto].
  clear B D N. induction F as [|l os ls' oss' [Hlen Hk] F IH]; constructor.
  - split; [exact Hlen|]. intros i o Hn. apply FW; [now left| |now apply Hk]. pose proof (nth_error_lt os i o Hn). lia.
  - apply IH. intros l0 i o Hl0 Hi Ht. apply FW; [now right|exact Hi|exact Ht].
Qed.

Lemma acct_kid_cells : forall m z ls l i o, completed_wf m z ls -> In l ls -> Z.of_nat i < lv_k l -> tree_at m z (kid_addr l i) o ->
  forall c, In c (obj_cells (kid_addr l i) o) -> cell_ok z ls c.
Proof.
  intros m z ls l i o CW Hl Hi Ht c Hc. destruct (CW l Hl (Z.of_nat i) ltac:(lia)) as (o' & Ht' & Hc').
  unfold kid_addr in *. pose proof (tree_at_unique _ _ _ _ _ Ht Ht') as <-. apply Hc'. exact Hc.
Qed.

Lemma acct_frame_st : forall m m' z z' ls X,
  zone_valid z -> readable_mono m m' -> zone_grows z z' -> stores_ok z ls m m' -> completed_wf m z ls ->
  acct_ok m z ls X -> acct_ok m' z' ls X.
Proof.
  intros m m' z z' ls X V R G S CW A. eapply acct_frame; [|exact A]. intros l i o Hl Hi Ht.
  eapply tree_at_frame; [exact R | exact G | | exact Ht]. intros c Hcc. eapply stores_ok_agree; [exact V | exact S |].
  exact (acct_kid_cells m z ls l i o CW Hl Hi Ht c Hcc).
Qed.

Lemma acct_frame_in : forall m m' z z' ls hs X,
  zone_valid z -> readable_mono_in z m m' -> zone_grows z z' -> Forall (fun h => store_ok z ls (fst h) (snd h)) hs -> zkept z hs m m' ->
  completed_wf m z ls -> acct_ok m z ls X -> acct_ok m' z' ls X.
Proof.
  intros m m' z z' ls hs X V R G S K CW A. eapply acct_frame; [|exact A]. intros l i o Hl Hi Ht.
  eapply tree_at_frame_in; [exact R | exact G | | exact Ht]. intros c Hcc. eapply zkept_agree_cell; [exact V | exact S | exact K |].
  exact (acct_kid_cells m z ls l i o CW Hl Hi Ht c Hcc).
Qed.

Lemma acct_push : forall m z ls X l, acct_ok m z ls X -> lv_k l = 0 -> (length ls <= 1000)%nat -> acct_ok m z (ls ++ [l]) (X + 1).
Proof.
  intros m z ls X l (oss & F & B & D & N) Hk HL. exists (oss ++ [[]]). split; [|split; [|split]].
  - apply Forall2_app; [exact F|]. constructor; [|constructor]. split; [cbn; lia|]. intros [|i] o Hn; discriminate.
  - rewrite length_app, map_app, zsum_app. cbn [length map zsum fold_right]. rewrite trees_cost_nil. lia.
  - intros j os Hn. destruct (Nat.lt_ge_cases j (length oss)) as [Hj|Hj].
    + apply D. rewrite nth_error_app1 in Hn by exact Hj. exact Hn.
    + rewrite nth_error_app2 in Hn by exact Hj. destruct (j - length oss)%nat as [|k] eqn:E; cbn in Hn; [|destruct k; discriminate].
      injection Hn as <-. rewrite objs_depth_nil. pose proof (Forall2_length' _ _ _ F). lia.
  - apply Forall_app. split; [exact N|]. constructor; [rewrite trees_cost_nil; lia| constructor].
Qed.

Lemma acct_ret : forall m z ls l l' X o,
  consume_top l = CS_Ret l' -> level_valid l ->
  acct_ok m z (ls ++ [l]) X -> tree_at m z (lv_slot l) o -> 0 <= tree_cost o ->
  (obj_depth o + length (ls ++ [l]) <= 1001)%nat ->
  acct_ok m z (ls ++ [l']) (X + tree_cost o).
Proof.
  intros m z ls l l' X o Hc V A Ht Hnn Hd.
  destruct (consume_top_ret l l' Hc V) as (_ & HP & _ & HK & _).
  destruct A as (oss & F & B & D & N). destruct (Forall2_snoc_inv _ ls l oss F) as (oss1 & os & -> & F1 & [Hlen Hk]).
  exists (oss1 ++ [os ++ [o]]). split; [|split; [|split]].
  - apply Forall2_app; [exact F1|]. constructor; [|constructor]. split.
    + rewrite length_app. cbn [length]. rewrite HK. lia.
    + intros i o' Hn. unfold kid_addr. rewrite HP. destruct (Nat.lt_ge_cases i (length os)) as [Hi|Hi].
      * rewrite nth_error_app1 in Hn by exact Hi. exact (Hk i o' Hn).
      * rewrite nth_error_app2 in Hn by exact Hi. destruct (i - length os)%nat as [|k] eqn:E; cbn in Hn; [|destruct k; discriminate].
        injection Hn as <-. replace (Z.of_nat i) with (lv_k l) by lia. unfold lv_slot in Ht. exact Ht.
  - rewrite !length_app, !map_app, !zsum_app in *. cbn [length map zsum fold_right] in *. rewrite trees_cost_app, trees_cost_cons1. lia.
  - intros j os' Hn. destruct (Nat.lt_ge_cases j (length oss1)) as [Hj|Hj].
    + apply D. rewrite nth_error_app1 in Hn |- * by exact Hj. exact Hn.
    + rewrite nth_error_app2 in Hn by exact Hj. destruct (j - length oss1)%nat as [|k] eqn:E; cbn in Hn; [|destruct k; discriminate].
      injection Hn as <-. rewrite objs_depth_app, objs_depth_cons1.
      pose proof (D (length oss1) os ltac:(rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity)) as D1.
      pose proof (Forall2_length' _ _ _ F1) as L1. rewrite length_app in Hd. cbn [length] in Hd. lia.
  - apply Forall_app in N. destruct N as [N1 N2]. inversion N2; subst. apply Forall_app. split; [exact N1|]. constructor; [|constructor].
    rewrite trees_cost_app, trees_cost_cons1. lia.
Qed.

Lemma acct_pop : forall m z ls l X o hdr c,
  consume_top l = CS_Pop -> level_valid l ->
  acct_ok m z (ls ++ [l]) X -> tree_at m z (lv_slot l) o -> (obj_depth o + length (ls ++ [l]) <= 1001)%nat ->
  tree_at m z hdr c -> obj_type c = container_type (lv_t l) -> obj_count c = lv_n l -> obj_ptr c = lv_P l ->
  acct_ok m z ls (X + tree_cost o - tree_cost c) /\ (obj_depth c + length ls <= 1001)%nat /\ 1 <= tree_cost c /\
  tree_cost c <= X + tree_cost o - Z.of_nat (length ls).
Proof.
  intros m z ls l X o hdr c Hc V A Ht Hd Tc TY CNT PTR.
  destruct (consume_top_pop l Hc) as [R1 NK]. pose proof (pop_full l V R1 NK) as FULL.
  destruct A as (oss & F & B & D & N). destruct (Forall2_snoc_inv _ ls l oss F) as (oss1 & os & -> & F1 & [Hlen Hk]).
  assert (TY2 : obj_type c = T_ARRAY \/ obj_type c = T_MAP) by (rewrite TY; destruct (lv_t l); cbn; auto).
  destruct (container_kids m z hdr c Tc TY2) as (K & HK & COST & DEPTH & LEN & WF).

  assert (HKlen : Z.of_nat (length K) = lv_k l + 1).
  { unfold lv_bytes in FULL. unfold lv_k in *. rewrite TY in LEN. destruct (lv_t l); cbn [container_type per] in LEN, FULL |- *.
    - destruct LEN as [[_ L]|[X0 _]]; [|discriminate]. rewrite CNT in L. unfold OBJ_SIZE in FULL. lia.
    - exfalso. apply NK. reflexivity.
    - destruct LEN as [[X0 _]|(_ & EV & L)]; [discriminate|]. rewrite CNT in L. unfold OBJ_SIZE in FULL.
      destruct EV as [q Hq]. rewrite Hq in L |- *. rewrite Nat2Z.inj_mul in L |- *. change (Z.of_nat 2) with 2 in *.
      rewrite Z.mul_comm, Z.div_mul in L by lia. lia. }

  assert (HKeq : K = os ++ [o]).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length K)) as [Hi|Hi].
    - destruct (nth_error K i) as [x|] eqn:E; [|exfalso; apply (proj2 (nth_error_Some K i) Hi); exact E].
      pose proof (HK i x E) as Tx. rewrite PTR in Tx.
      destruct (Nat.lt_ge_cases i (length os)) as [Hi2|Hi2].
      + rewrite nth_error_app1 by exact Hi2. destruct (nth_error os i) as [y|] eqn:E2; [|exfalso; apply (proj2 (nth_error_Some os i) Hi2); exact E2].
        f_equal. pose proof (Hk i y E2) as Ty. unfold kid_addr in Ty. exact (tree_at_unique _ _ _ _ _ Tx Ty).
      + rewrite nth_error_app2 by exact Hi2. replace (i - length os)%nat with 0%nat by lia. cbn. f_equal.
        replace (Z.of_nat i) with (lv_k l) in Tx by lia. unfold lv_slot in Ht. exact (tree_at_unique _ _ _ _ _ Tx Ht).
    - destruct (nth_error K i) eqn:E; [exfalso; pose proof (nth_error_lt _ _ _ E); lia|].
      destruct (nth_error (os ++ [o]) i) eqn:E2; [exfalso; pose proof (nth_error_lt _ _ _ E2) as L2; rewrite length_app in L2; cbn in L2; lia| reflexivity]. }
  subst K. rewrite trees_cost_app, trees_cost_cons1 in COST. rewrite objs_depth_app, objs_depth_cons1 in DEPTH.
  pose proof (D (length oss1) os ltac:(rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity)) as D1.
  pose proof (Forall2_length' _ _ _ F1) as L1. rewrite length_app in Hd. cbn [length] in Hd.
  rewrite !length_app, !map_app, !zsum_app in B. cbn [length map zsum fold_right] in B.
  apply Forall_app in N. destruct N as [N1 N2]. inversion N2; subst.
  pose proof (zsum_nonneg (map trees_cost oss1) ltac:(apply Forall_map; exact N1)) as NN.
  pose proof (tree_cost_wf_nonneg m z o (proj2 Ht)) as NO.
  split; [|split; [lia|split; [lia|lia]]].
  exists oss1. split; [exact F1|]. split; [lia|]. split; [|exact N1].
  intros j os' Hn. apply D. rewrite nth_error_app1; [exact Hn|]. exact (nth_error_lt _ _ _ Hn).
Qed.

Definition just_acct (m : bmem) (g : unpg) (cur : Z) (o : obj) : Prop :=
  acct_ok m (u_zone g) (u_levels g) (cur - u_data g - tree_cost o) /\ (obj_depth o + length (u_levels g) <= 1001)%nat.

Lemma tree_cost_scalar : forall o, match o with OArr _ _ | OMap _ _ | OStr _ _ | OBin _ _ | OExt _ _ => False | _ => True end -> tree_cost o = 1.
Proof. intros o H. destruct o; try contradiction; reflexivity. Qed.
Lemma tree_cost_str : forall p n, tree_cost (OStr p n) = 1 + n. Proof. intros. unfold tree_cost; cbn. lia. Qed.
Lemma tree_cost_bin : forall p n, tree_cost (OBin p n) = 1 + n. Proof. intros. unfold tree_cost; cbn. lia. Qed.
Lemma tree_cost_ext : forall p n, tree_cost (OExt p n) = 1 + (n + 1). Proof. intros. unfold tree_cost; cbn. lia. Qed.
Lemma tree_cost_arr0 : forall p, tree_cost (OArr p []) = 1. Proof. reflexivity. Qed.
Lemma tree_cost_map0 : forall p, tree_cost (OMap p []) = 1. Proof. reflexivity. Qed.
Lemma obj_depth_scalar : forall o, match o with OArr _ (_ :: _) | OMap _ (_ :: _) => False | _ => True end -> obj_depth o = 1%nat.
Proof. intros o H. destruct o; try reflexivity; destruct kids; try contradiction; reflexivity. Qed.

Lemma just_acct_intro : forall m g cur0 cur o,
  acct_ok m (u_zone g) (u_levels g) (cur0 - u_data g) -> cur0 + tree_cost o <= cur ->
  obj_depth o = 1%nat -> (length (u_levels g) <= 1000)%nat ->
  just_acct m g cur o.
Proof.
  intros m g cur0 cur o A Hc Hd HL. split; [| rewrite Hd; lia]. eapply acct_mono; [exact A| lia].
Qed.
Lemma u_D_length : forall g, u_D g <= LIMIT -> (length (u_levels g) <= 1000)%nat.
Proof. intros g H. unfold u_D, LIMIT in H. lia. Qed.

Lemma just_int_acct : forall m z ls a ty u, u32_at m a ty -> u64_at m (a + 8) u -> (ty = T_POSINT \/ ty = T_NEGINT) -> 0 <= u < 2^64 ->
  exists o, tree_at m z a o /\ (forall c, In c (tl (obj_cells a o)) -> cell_ok z ls c) /\ tree_cost o = 1 /\ obj_depth o = 1%nat.
Proof.
  intros m z ls a ty u H1 H2 [-> | ->] Hu.
  - exists (OPos u). pose proof (just_pos m z ls a u H1 H2 Hu) as [J1 J2]. split; [exact J1|]. split; [exact J2|]. split; reflexivity.
  - exists (ONeg (u - 2^64)). pose proof (just_negu m z ls a u H1 H2 Hu) as [J1 J2]. split; [exact J1|]. split; [exact J2|]. split; reflexivity.
Qed.
