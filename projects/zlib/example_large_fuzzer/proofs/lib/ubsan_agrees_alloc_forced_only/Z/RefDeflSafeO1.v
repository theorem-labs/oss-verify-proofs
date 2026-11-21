(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lek (FC DP : arr) (a b : Z) : Prop :=
  arr_get FC a < arr_get FC b \/ (arr_get FC a = arr_get FC b /\ arr_get DP a <= arr_get DP b).

Lemma lek_total : forall FC DP a b, lek FC DP a b \/ lek FC DP b a.
Proof. intros. unfold lek. lia. Qed.
Lemma lek_trans : forall FC DP a b c, lek FC DP a b -> lek FC DP b c -> lek FC DP a c.
Proof. intros. unfold lek in *. lia. Qed.
Lemma lek_refl : forall FC DP a, lek FC DP a a.
Proof. intros. unfold lek. lia. Qed.
Lemma lek_freq : forall FC DP a b, lek FC DP a b -> arr_get FC a <= arr_get FC b.
Proof. intros. unfold lek in *. lia. Qed.

(* [comment removed for export] *)
Lemma smaller_lek : forall s t n m, smaller s t n m = true <-> lek (tree_fc s t) (ds_depth s) n m.
Proof.
  intros s t n m. unfold smaller, lek, Freq, depth_get.
  rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.
Lemma smaller_false_lek : forall s t n m, smaller s t n m = false -> lek (tree_fc s t) (ds_depth s) m n.
Proof.
  intros s t n m H. destruct (lek_total (tree_fc s t) (ds_depth s) n m) as [X|X]; [|exact X].
  apply smaller_lek in X. congruence.
Qed.

(* [comment removed for export] *)
Lemma heap_set_tree_fc : forall s i v t, tree_fc (heap_set s i v) t = tree_fc s t.
Proof. intros s i v [| |]; destruct s; reflexivity. Qed.
Lemma heap_set_depth : forall s i v, ds_depth (heap_set s i v) = ds_depth s.
Proof. intros; destruct s; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition heap_prop (FC DP HP : arr) (hl k : Z) : Prop :=
  forall i, 2 <= i <= hl -> k < i / 2 -> lek FC DP (arr_get HP (i / 2)) (arr_get HP i).

Lemma div2_facts : forall i, 2 <= i -> 1 <= i / 2 < i /\ (i = 2 * (i / 2) \/ i = 2 * (i / 2) + 1).
Proof. intros. Z.to_euclidean_division_equations. lia. Qed.
Lemma div2_of_child : forall h, 0 <= h -> (2 * h) / 2 = h /\ (2 * h + 1) / 2 = h.
Proof. intros. Z.to_euclidean_division_equations. lia. Qed.

(* [comment removed for export] *)
Lemma heap_root_min : forall FC DP HP hl, heap_prop FC DP HP hl 0 ->
  forall i, 1 <= i <= hl -> lek FC DP (arr_get HP 1) (arr_get HP i).
Proof.
  intros FC DP HP hl HPr i Hi. remember (Z.to_nat i) as n eqn:En. revert i Hi En.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros i Hi En.
  destruct (Z.eq_dec i 1) as [->|Ne]; [apply lek_refl|].
  pose proof (div2_facts i ltac:(lia)) as [D1 D2].
  apply (lek_trans FC DP _ (arr_get HP (i / 2))); [apply (IH (Z.to_nat (i / 2))); lia|]. apply HPr; lia.
Qed.

Lemma heap_prop_vacuous : forall FC DP HP hl k, 0 <= hl -> hl / 2 <= k -> heap_prop FC DP HP hl k.
Proof. intros FC DP HP hl k Hhl Hk i Hi Hki. exfalso. Z.to_euclidean_division_equations. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SiftDown.
Variable FC : arr.
Variable DP : arr.
Local Notation LE := (lek FC DP).

(* [comment removed for export] *)
Definition sift_inv (HP : arr) (hl k h : Z) (v : Z) : Prop :=
  (forall i, 2 <= i <= hl -> k <= i / 2 -> i <> h -> i / 2 <> h -> LE (arr_get HP (i / 2)) (arr_get HP i))
  /\ (forall i, 2 <= i <= hl -> i / 2 = h -> k < h -> LE (arr_get HP (h / 2)) (arr_get HP i))
  /\ (k < h -> LE (arr_get HP (h / 2)) v).

Lemma pqdownheap_loop_order : forall f s t v k h j s' k',
  tree_fc s t = FC -> ds_depth s = DP ->
  pqdownheap_loop f s t v h j = (s', k') -> j = 2 * h ->
  1 <= k <= h -> h <= ds_heap_len s -> ds_heap_len s < arr_len (ds_heap s) -> ds_heap_len s < 2 ^ Z.of_nat f * h ->
  sift_inv (ds_heap s) (ds_heap_len s) k h v ->
  heap_prop FC DP (arr_set (ds_heap s') k' v) (ds_heap_len s) (k - 1)
  /\ 1 <= k' <= ds_heap_len s /\ arr_len (ds_heap s') = arr_len (ds_heap s).
Proof.
  induction f as [|f IH]; intros s t v k h j s' k' EFC EDP H Hj Hk Hh Hlen Hfuel (V1 & V2 & V3).
  { exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia. }
  assert (SM : forall a b, smaller s t a b = true <-> LE a b) by (intros; rewrite smaller_lek, EFC, EDP; tauto).
  assert (SMf : forall a b, smaller s t a b = false -> LE b a) by (intros a b X; pose proof (smaller_false_lek s t a b X) as Y; rewrite EFC, EDP in Y; exact Y).
  pose proof (div2_of_child h ltac:(lia)) as [C1 C2].
  assert (Hh2 : 0 <= h / 2 < h) by (Z.to_euclidean_division_equations; lia).
  rewrite pqdownheap_loop_S in H. subst j.
  destruct (Z.leb_spec (2 * h) (ds_heap_len s)) as [Hch|Hnoch].
  - cbv zeta in H. set (j' := if (2 * h <? ds_heap_len s) && smaller s t (heap_get s (2 * h + 1)) (heap_get s (2 * h)) then 2 * h + 1 else 2 * h) in H.
    assert (Hj' : (j' = 2 * h \/ (j' = 2 * h + 1 /\ 2 * h + 1 <= ds_heap_len s)) /\ j' / 2 = h).
    { subst j'. destruct (Z.ltb_spec (2 * h) (ds_heap_len s)); cbn [andb].
      - destruct (smaller s t (heap_get s (2 * h + 1)) (heap_get s (2 * h))); [split; [right; lia| exact C2]| split; [left; lia| exact C1]].
      - split; [left; lia| exact C1]. }
    destruct Hj' as [Hj'1 Hj'2].
    assert (MIN : forall i, 2 <= i <= ds_heap_len s -> i / 2 = h -> LE (arr_get (ds_heap s) j') (arr_get (ds_heap s) i)).
    { intros i Hi Hih. assert (Hi2 : i = 2 * h \/ i = 2 * h + 1) by (Z.to_euclidean_division_equations; lia).
      subst j'. unfold heap_get. destruct (Z.ltb_spec (2 * h) (ds_heap_len s)); cbn [andb].
      - destruct (smaller s t (arr_get (ds_heap s) (2 * h + 1)) (arr_get (ds_heap s) (2 * h))) eqn:Es.
        + destruct Hi2 as [-> | ->]; [apply SM; exact Es | apply lek_refl].
        + destruct Hi2 as [-> | ->]; [apply lek_refl | apply SMf; exact Es].
      - destruct Hi2 as [-> | ->]; [apply lek_refl| lia]. }
    clearbody j'.
    destruct (smaller s t v (heap_get s j')) eqn:Hs; try rewrite Hs in H; cbv beta iota in H.
    + (* [comment removed for export] *)
      injection H as <- <-. split; [| split; [lia | reflexivity]].
      intros i Hi Hki. pose proof (div2_facts i ltac:(lia)) as [Di1 Di2].
      rewrite !arr_get_set. unfold arr_inb.
      replace ((0 <=? h) && (h <? arr_len (ds_heap s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      destruct (Z.eqb_spec h i) as [<-|Nih]; cbn [andb].
      { replace (h =? h / 2) with false by (symmetry; apply Z.eqb_neq; lia). apply V3. lia. }
      destruct (Z.eqb_spec h (i / 2)) as [Eih|Nih2]; cbn [andb].
      { apply (lek_trans FC DP _ (arr_get (ds_heap s) j')); [apply SM; exact Hs | apply MIN; lia]. }
      apply V1; lia.
    + (* [comment removed for export] *)
      assert (LEN1 : arr_len (ds_heap (heap_set s h (heap_get s j'))) = arr_len (ds_heap s)) by (rewrite ds_heap_heap_set, arr_len_set; reflexivity).
      destruct (IH (heap_set s h (heap_get s j')) t v k j' (Z.shiftl j' 1) s' k'
                   ltac:(rewrite heap_set_tree_fc; exact EFC) ltac:(rewrite heap_set_depth; exact EDP) H
                   ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) ltac:(lia) ltac:(rewrite ds_heap_len_heap_set; lia)
                   ltac:(rewrite ds_heap_len_heap_set, LEN1; lia)
                   ltac:(rewrite ds_heap_len_heap_set; rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia; lia)) as (HPr & K' & L').
      * rewrite ds_heap_len_heap_set, ds_heap_heap_set. unfold heap_get.
        assert (G : forall i, arr_get (arr_set (ds_heap s) h (arr_get (ds_heap s) j')) i = if h =? i then arr_get (ds_heap s) j' else arr_get (ds_heap s) i).
        { intros i. rewrite arr_get_set. unfold arr_inb.
          replace ((0 <=? h) && (h <? arr_len (ds_heap s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          rewrite Bool.andb_true_r. reflexivity. }
        split; [|split].
        -- intros i Hi Hki Nij Nij2. pose proof (div2_facts i ltac:(lia)) as [Di1 Di2]. rewrite !G.
           destruct (Z.eqb_spec h i) as [<-|Nih].
           { replace (h =? h / 2) with false by (symmetry; apply Z.eqb_neq; lia). apply V2; lia. }
           destruct (Z.eqb_spec h (i / 2)) as [Eih|Nih2]; [apply MIN; lia|]. apply V1; lia.
        -- intros i Hi Hij Hkj. pose proof (div2_facts i ltac:(lia)) as [Di1 Di2]. rewrite !G, Hj'2, Z.eqb_refl.
           replace (h =? i) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- Hij. apply V1; lia.
        -- intros Hkj. rewrite G, Hj'2, Z.eqb_refl. apply SMf. exact Hs.
      * rewrite ds_heap_len_heap_set in HPr, K'. rewrite LEN1 in L'. split; [exact HPr | split; [exact K' | exact L']].
  - (* [comment removed for export] *)
    injection H as <- <-. split; [| split; [lia | reflexivity]].
    intros i Hi Hki. pose proof (div2_facts i ltac:(lia)) as [Di1 Di2].
    rewrite !arr_get_set. unfold arr_inb.
    replace ((0 <=? h) && (h <? arr_len (ds_heap s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    destruct (Z.eqb_spec h i) as [<-|Nih]; cbn [andb].
    { replace (h =? h / 2) with false by (symmetry; apply Z.eqb_neq; lia). apply V3. lia. }
    assert (i / 2 <> h) by lia. replace (h =? i / 2) with false by (symmetry; apply Z.eqb_neq; lia). apply V1; lia.
Qed.

(* [comment removed for export] *)
Lemma pqdownheap_order : forall s t k,
  tree_fc s t = FC -> ds_depth s = DP ->
  1 <= k <= ds_heap_len s -> ds_heap_len s < arr_len (ds_heap s) -> ds_heap_len s <= 572 ->
  heap_prop FC DP (ds_heap s) (ds_heap_len s) k ->
  heap_prop FC DP (ds_heap (pqdownheap s t k)) (ds_heap_len s) (k - 1).
Proof.
  intros s t k EFC EDP Hk Hlen Hhl HPr. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:E.
  destruct (pqdownheap_loop_order 32 s t (heap_get s k) k k (Z.shiftl k 1) s' k' EFC EDP E ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)
              ltac:(lia) ltac:(lia) Hlen ltac:(change (2 ^ Z.of_nat 32) with 4294967296; lia)) as (HPr' & K' & L').
  - split; [|split]; [| intros; lia | intros; lia]. intros i Hi Hki Nik Nik2. apply HPr; lia.
  - rewrite ds_heap_heap_set. exact HPr'.
Qed.
End SiftDown.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Heapify.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).

Lemma loop3_order : forall f n FC DL HP HL HM DP BC OL SL MC,
  Z.of_nat f = n -> 0 <= n <= HL -> HL <= 572 -> arr_len HP = 573 ->
  heap_prop FC DP HP HL n ->
  heap_prop FC DP (ds_heap (build_tree_loop3 f (U FC DL HP HL HM DP BC OL SL MC) t n)) HL 0.
Proof.
  induction f as [|f IH]; intros n FC DL HP HL HM DP BC OL SL MC Hf Hn HHL LHP HPr.
  - cbn [build_tree_loop3]. rewrite bt_heap. replace n with 0 in HPr by lia. exact HPr.
  - cbn [build_tree_loop3]. destruct (Z.leb_spec 1 n) as [C|C]; [|exfalso; lia].
    pose proof (pqdownheap_order FC DP (U FC DL HP HL HM DP BC OL SL MC) t n) as PO.
    rewrite bt_tree_fc, bt_depth, bt_heap_len, bt_heap in PO. specialize (PO eq_refl eq_refl ltac:(lia) ltac:(lia) HHL HPr).
    pose proof (pqdownheap_shape (U FC DL HP HL HM DP BC OL SL MC) t n) as SH.
    pose proof (pqdownheap_len (U FC DL HP HL HM DP BC OL SL MC) t n) as LN. rewrite bt_heap in LN.
    rewrite SH, bt_set_heap. apply IH; [lia | lia | lia | rewrite LN; exact LHP | exact PO].
Qed.
End Heapify.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zsum_balance : forall g g' lo n a b,
  lo <= a < lo + Z.of_nat n -> lo <= b < lo + Z.of_nat n -> a <> b ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> i <> b -> g i = g' i) ->
  g a + g b = g' a + g' b ->
  zsum g lo n = zsum g' lo n.
Proof.
  intros g g' lo n a b Ha Hb Nab H E.
  rewrite (zsum_ext g (fun i => g' i + (g i - g' i))) by (intros; lia). rewrite zsum_add.
  rewrite (zsum_two (fun i => g i - g' i) lo n a b Ha Hb Nab) by (intros i Hi Na Nb; rewrite (H i Hi Na Nb); lia). lia.
Qed.

Lemma zsum_balance1 : forall g g' lo n a,
  lo <= a < lo + Z.of_nat n -> (forall i, lo <= i < lo + Z.of_nat n -> i <> a -> g i = g' i) -> g a = g' a ->
  zsum g lo n = zsum g' lo n.
Proof. intros. apply zsum_ext. intros i Hi. destruct (Z.eq_dec i a) as [->|N]; [assumption | apply H0; assumption]. Qed.

Section Sums.
Variable f : Z -> Z.

(* [comment removed for export] *)
Definition hsum (HP : arr) (hl h v : Z) : Z := zsum (fun i => if i =? h then f v else f (arr_get HP i)) 1 (Z.to_nat hl).

Lemma pqdownheap_loop_sum : forall fuel s t v k j s' k' hl,
  pqdownheap_loop fuel s t v k j = (s', k') -> j = 2 * k -> hl = ds_heap_len s ->
  1 <= k <= hl -> hl < arr_len (ds_heap s) ->
  hsum (ds_heap s') hl k' v = hsum (ds_heap s) hl k v /\ 1 <= k' <= hl.
Proof.
  induction fuel as [|fuel IH]; intros s t v k j s' k' hl H Hj Hhl Hk Hlen.
  - rewrite pqdownheap_loop_0 in H. injection H as <- <-. split; [reflexivity | exact Hk].
  - rewrite pqdownheap_loop_S in H. subst j. rewrite <- Hhl in H.
    destruct (Z.leb_spec (2 * k) hl) as [C|C].
    2:{ injection H as <- <-. split; [reflexivity | exact Hk]. }
    cbv zeta in H.
    set (j' := if (2 * k <? hl) && smaller s t (heap_get s (2 * k + 1)) (heap_get s (2 * k)) then 2 * k + 1 else 2 * k) in H.
    assert (Hj' : 2 * k <= j' <= hl) by (subst j'; destruct (Z.ltb_spec (2 * k) hl); cbn [andb]; [destruct (smaller s t (heap_get s (2 * k + 1)) (heap_get s (2 * k)))|]; lia).
    clearbody j'.
    destruct (smaller s t v (heap_get s j')); [injection H as <- <-; split; [reflexivity | exact Hk]|].
    destruct (IH (heap_set s k (heap_get s j')) t v j' (Z.shiftl j' 1) s' k' hl H ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)
                 ltac:(rewrite ds_heap_len_heap_set; exact Hhl) ltac:(lia) ltac:(rewrite ds_heap_heap_set, arr_len_set; exact Hlen)) as [S K].
    split; [|exact K]. rewrite S. rewrite ds_heap_heap_set. unfold heap_get, hsum.
    apply (zsum_balance _ _ 1 (Z.to_nat hl) k j'); try lia.
    + intros i Hi Nk Nj. rewrite arr_get_set. replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      replace (i =? j') with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? k) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + rewrite !arr_get_set. unfold arr_inb. rewrite !Z.eqb_refl.
      replace (k =? j') with false by (symmetry; apply Z.eqb_neq; lia). replace (j' =? k) with false by (symmetry; apply Z.eqb_neq; lia).
      replace ((0 <=? k) && (k <? arr_len (ds_heap s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. lia.
Qed.

Lemma pqdownheap_sum : forall s t k, 1 <= k <= ds_heap_len s -> ds_heap_len s < arr_len (ds_heap s) ->
  zsum (fun i => f (arr_get (ds_heap (pqdownheap s t k)) i)) 1 (Z.to_nat (ds_heap_len s))
  = zsum (fun i => f (arr_get (ds_heap s) i)) 1 (Z.to_nat (ds_heap_len s)).
Proof.
  intros s t k Hk Hlen. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:E.
  destruct (pqdownheap_loop_sum 32 s t (heap_get s k) k (Z.shiftl k 1) s' k' (ds_heap_len s) E ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) eq_refl Hk Hlen) as [S K].
  pose proof (pqdownheap_loop_len 32 s t (heap_get s k) k (Z.shiftl k 1) s' k' E) as LEN.
  rewrite ds_heap_heap_set.
  transitivity (hsum (ds_heap s') (ds_heap_len s) k' (heap_get s k)).
  { unfold hsum. apply zsum_ext. intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite LEN.
    replace ((0 <=? k') && (k' <? arr_len (ds_heap s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Bool.andb_true_r, (Z.eqb_sym i k'). destruct (k' =? i); reflexivity. }
  rewrite S. unfold hsum, heap_get. apply zsum_ext. intros i Hi. destruct (Z.eqb_spec i k) as [->|N]; reflexivity.
Qed.
End Sums.
