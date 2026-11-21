(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition live (hl hm i : Z) : Prop := (1 <= i <= hl) \/ (hm <= i < 573).

Definition zone_ok (HP : arr) (hl hm : Z) (V : Z -> Prop) : Prop :=
  exists pos : Z -> Z,
    (forall i, live hl hm i -> V (arr_get HP i) /\ pos (arr_get HP i) = i)
    /\ (forall u, V u -> live hl hm (pos u) /\ arr_get HP (pos u) = u).

Definition zone_hole (HP : arr) (hl hm : Z) (V : Z -> Prop) (k v : Z) : Prop :=
  exists pos : Z -> Z,
    1 <= k <= hl /\ V v
    /\ (forall i, live hl hm i -> i <> k -> V (arr_get HP i) /\ pos (arr_get HP i) = i /\ arr_get HP i <> v)
    /\ (forall u, V u -> u <> v -> live hl hm (pos u) /\ pos u <> k /\ arr_get HP (pos u) = u).

Lemma zone_ok_inj : forall HP hl hm V i j,
  zone_ok HP hl hm V -> live hl hm i -> live hl hm j -> arr_get HP i = arr_get HP j -> i = j.
Proof.
  intros HP hl hm V i j [pos [A B]] Hi Hj E.
  destruct (A i Hi) as [_ Pi]. destruct (A j Hj) as [_ Pj]. rewrite E in Pi. congruence.
Qed.

Lemma zone_ok_mem : forall HP hl hm V i, zone_ok HP hl hm V -> live hl hm i -> V (arr_get HP i).
Proof. intros HP hl hm V i [pos [A B]] Hi. exact (proj1 (A i Hi)). Qed.

Local Ltac inb_true k HP :=
  replace ((0 <=? k) && (k <? arr_len HP)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).

Lemma zone_open : forall HP hl hm V k,
  zone_ok HP hl hm V -> 1 <= k <= hl -> zone_hole HP hl hm V k (arr_get HP k).
Proof.
  intros HP hl hm V k [pos [A B]] Hk. exists pos.
  assert (Lk : live hl hm k) by (left; lia).
  destruct (A k Lk) as [Vk Pk].
  split; [exact Hk|]. split; [exact Vk|]. split.
  - intros i Hi Nik. destruct (A i Hi) as [Vi Pi]. split; [exact Vi|]. split; [exact Pi|].
    intros E. rewrite E, Pk in Pi. exact (Nik (eq_sym Pi)).
  - intros u Hu Nu. destruct (B u Hu) as [L E]. split; [exact L|]. split; [|exact E].
    intros Ek. apply Nu. rewrite <- E, Ek. reflexivity.
Qed.

Lemma zone_move : forall HP hl hm V k v j,
  zone_hole HP hl hm V k v -> 1 <= j <= hl -> j <> k -> 0 <= k < arr_len HP ->
  zone_hole (arr_set HP k (arr_get HP j)) hl hm V j v.
Proof.
  intros HP hl hm V k v j [pos (Hk & Hv & A & B)] Hj Njk HkL.
  assert (Lj : live hl hm j) by (left; lia).
  destruct (A j Lj Njk) as (Vj & Pj & Nvj).
  exists (fun u => if Z.eq_dec u (arr_get HP j) then k else pos u).
  split; [exact Hj|]. split; [exact Hv|]. split.
  - intros i Hi Nij. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec k i) as [<-|Nki].
    + inb_true k HP. cbn [andb]. split; [exact Vj|]. split; [|exact Nvj]. destruct (Z.eq_dec _ _); [reflexivity | congruence].
    + cbn [andb]. destruct (A i Hi ltac:(lia)) as (Vi & Pi & Nvi). split; [exact Vi|]. split; [|exact Nvi].
      destruct (Z.eq_dec (arr_get HP i) (arr_get HP j)) as [E|NE]; [|exact Pi].
      exfalso. rewrite E, Pj in Pi. exact (Nij (eq_sym Pi)).
  - intros u Hu Nu. destruct (B u Hu Nu) as (Lu & Nuk & Eu).
    destruct (Z.eq_dec u (arr_get HP j)) as [E|NE].
    + split; [left; lia|]. split; [congruence|]. rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl.
      inb_true k HP. symmetry. exact E.
    + split; [exact Lu|]. split.
      * intros Ej. apply NE. rewrite <- Eu, Ej. reflexivity.
      * rewrite arr_get_set. unfold arr_inb. destruct (Z.eqb_spec k (pos u)) as [Ek|Nk]; [exfalso; exact (Nuk (eq_sym Ek))|]. cbn [andb]. exact Eu.
Qed.

Lemma zone_close : forall HP hl hm V k v,
  zone_hole HP hl hm V k v -> 0 <= k < arr_len HP -> zone_ok (arr_set HP k v) hl hm V.
Proof.
  intros HP hl hm V k v [pos (Hk & Hv & A & B)] HkL.
  exists (fun u => if Z.eq_dec u v then k else pos u). split.
  - intros i Hi. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec k i) as [<-|Nki].
    + inb_true k HP. cbn [andb]. split; [exact Hv|]. destruct (Z.eq_dec v v); [reflexivity | congruence].
    + cbn [andb]. destruct (A i Hi ltac:(lia)) as (Vi & Pi & Nvi). split; [exact Vi|].
      destruct (Z.eq_dec (arr_get HP i) v) as [E|NE]; [exfalso; exact (Nvi E) | exact Pi].
  - intros u Hu. destruct (Z.eq_dec u v) as [->|NE].
    + split; [left; lia|]. rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl. inb_true k HP. reflexivity.
    + destruct (B u Hu NE) as (Lu & Nuk & Eu).
      split; [exact Lu|]. rewrite arr_get_set. unfold arr_inb.
      destruct (Z.eqb_spec k (pos u)) as [Ek|Nk]; [exfalso; exact (Nuk (eq_sym Ek))|]. cbn [andb]. exact Eu.
Qed.


Lemma ds_heap_heap_set : forall s i v, ds_heap (heap_set s i v) = arr_set (ds_heap s) i v.
Proof. intros s i v. rewrite heap_set_shape, ds_heap_set_heap. reflexivity. Qed.
Lemma ds_heap_len_heap_set : forall s i v, ds_heap_len (heap_set s i v) = ds_heap_len s.
Proof. intros s i v. rewrite heap_set_shape, sh_heap_len. reflexivity. Qed.

Lemma pqdownheap_loop_zone : forall f s t v k j s' k' hm V,
  pqdownheap_loop f s t v k j = (s', k') ->
  zone_hole (ds_heap s) (ds_heap_len s) hm V k v -> j = 2 * k ->
  arr_len (ds_heap s) = 573 -> ds_heap_len s <= 572 ->
  zone_hole (ds_heap s') (ds_heap_len s) hm V k' v /\ 1 <= k' <= ds_heap_len s
  /\ (forall i, ~ (1 <= i <= ds_heap_len s) -> arr_get (ds_heap s') i = arr_get (ds_heap s) i)
  /\ ds_heap_len s' = ds_heap_len s /\ arr_len (ds_heap s') = 573.
Proof.
  induction f as [|f IH]; intros s t v k j s' k' hm V H HZ Hj HL Hhl.
  - rewrite pqdownheap_loop_0 in H. injection H as <- <-.
    pose proof HZ as [pos (Hk & _)]. split; [exact HZ|]. split; [exact Hk|]. split; [intros; reflexivity|]. split; [reflexivity | exact HL].
  - rewrite pqdownheap_loop_S in H. pose proof HZ as [pos (Hk & _)].
    destruct (Z.leb_spec j (ds_heap_len s)) as [Cj|Cj]; [| injection H as <- <-; split; [exact HZ|]; split; [exact Hk|]; split; [intros; reflexivity|]; split; [reflexivity | exact HL]].
    cbv zeta in H.
    set (j' := if (j <? ds_heap_len s) && smaller s t (heap_get s (j + 1)) (heap_get s j) then j + 1 else j) in H.
    assert (Hj' : j <= j' <= ds_heap_len s /\ j' <= j + 1).
    { subst j'. destruct (Z.ltb_spec j (ds_heap_len s)); cbn [andb]; [destruct (smaller s t (heap_get s (j + 1)) (heap_get s j))|]; lia. }
    destruct (smaller s t v (heap_get s j')).
    + injection H as <- <-. split; [exact HZ|]. split; [exact Hk|]. split; [intros; reflexivity|]. split; [reflexivity | exact HL].
    + assert (HZ1 : zone_hole (ds_heap (heap_set s k (heap_get s j'))) (ds_heap_len s) hm V j' v).
      { rewrite ds_heap_heap_set. unfold heap_get. apply (zone_move _ _ _ _ _ _ _ HZ); lia. }
      assert (L1 : arr_len (ds_heap (heap_set s k (heap_get s j'))) = 573) by (rewrite ds_heap_heap_set, arr_len_set; exact HL).
      pose proof (IH (heap_set s k (heap_get s j')) t v j' (Z.shiftl j' 1) s' k' hm V H) as IH'.
      rewrite ds_heap_len_heap_set in IH'.
      destruct (IH' HZ1 ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) L1 Hhl) as (Z1 & K1 & O1 & E1 & L2).
      split; [exact Z1|]. split; [lia|]. split; [| split; [exact E1 | exact L2]].
      intros i Hi. rewrite (O1 i Hi). rewrite ds_heap_heap_set. rewrite arr_get_set.
      destruct (Z.eqb_spec k i) as [<-|Nki]; [exfalso; lia|]. reflexivity.
Qed.

Lemma pqdownheap_zone : forall s t k hm V,
  zone_ok (ds_heap s) (ds_heap_len s) hm V -> 1 <= k <= ds_heap_len s ->
  arr_len (ds_heap s) = 573 -> ds_heap_len s <= 572 ->
  zone_ok (ds_heap (pqdownheap s t k)) (ds_heap_len s) hm V
  /\ (forall i, ~ (1 <= i <= ds_heap_len s) -> arr_get (ds_heap (pqdownheap s t k)) i = arr_get (ds_heap s) i)
  /\ ds_heap_len (pqdownheap s t k) = ds_heap_len s /\ arr_len (ds_heap (pqdownheap s t k)) = 573
  /\ pqdownheap s t k = set_heap s (ds_heap (pqdownheap s t k)).
Proof.
  intros s t k hm V HZ Hk HL Hhl. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:E.
  pose proof (zone_open _ _ _ _ _ HZ Hk) as HZ0. unfold heap_get in E.
  destruct (pqdownheap_loop_zone 32 s t _ k _ s' k' hm V E HZ0 ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) HL Hhl)
    as (Z1 & K1 & O1 & E1 & L1).
  rewrite ds_heap_heap_set, ds_heap_len_heap_set.
  split; [apply (zone_close _ _ _ _ _ _ Z1); lia|].
  split.
  { intros i Hi. rewrite arr_get_set. destruct (Z.eqb_spec k' i) as [<-|N]; [exfalso; lia|]. cbn [andb]. apply O1. exact Hi. }
  split; [exact E1|]. split; [rewrite arr_len_set; exact L1|].
  rewrite (pqdownheap_loop_shape _ _ _ _ _ _ _ _ E) at 1. rewrite heap_set_shape, set_heap_twice, ds_heap_set_heap. reflexivity.
Qed.


Lemma zone_ok_ext : forall HP hl hm (V V' : Z -> Prop),
  (forall u, V u <-> V' u) -> zone_ok HP hl hm V -> zone_ok HP hl hm V'.
Proof.
  intros HP hl hm V V' HE [pos [A B]]. exists pos. split.
  - intros i Hi. destruct (A i Hi) as [Vi Pi]. split; [apply HE; exact Vi | exact Pi].
  - intros u Hu. apply B. apply HE. exact Hu.
Qed.

Lemma zone_ok_empty : forall HP, zone_ok HP 0 573 (fun _ => False).
Proof.
  intros HP. exists (fun _ => 0). split; [| intros u Hu; destruct Hu].
  intros i Hi. exfalso. unfold live in Hi. lia.
Qed.

Lemma zone_push : forall HP hl hm V x,
  zone_ok HP hl hm V -> 0 <= hl -> hl + 1 < hm -> ~ V x -> hl + 1 < arr_len HP ->
  zone_ok (arr_set HP (hl + 1) x) (hl + 1) hm (fun u => V u \/ u = x).
Proof.
  intros HP hl hm V x [pos [A B]] H0 Hh Nx HL.
  exists (fun u => if Z.eq_dec u x then hl + 1 else pos u). split.
  - intros i Hi. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec (hl + 1) i) as [<-|Ni].
    + inb_true (hl + 1) HP. cbn [andb]. split; [right; reflexivity|]. destruct (Z.eq_dec x x); [reflexivity | congruence].
    + cbn [andb]. assert (Li : live hl hm i) by (unfold live in *; lia).
      destruct (A i Li) as [Vi Pi]. split; [left; exact Vi|].
      destruct (Z.eq_dec (arr_get HP i) x) as [E|NE]; [exfalso; apply Nx; rewrite <- E; exact Vi | exact Pi].
  - intros u [Hu | ->].
    + destruct (Z.eq_dec u x) as [->|NE]; [exfalso; exact (Nx Hu)|].
      destruct (B u Hu) as [Lu Eu]. split; [unfold live in *; lia|].
      rewrite arr_get_set. unfold arr_inb. destruct (Z.eqb_spec (hl + 1) (pos u)) as [E|N]; [exfalso; unfold live in Lu; lia|]. cbn [andb]. exact Eu.
    + destruct (Z.eq_dec x x); [|congruence]. split; [left; lia|].
      rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl. inb_true (hl + 1) HP. reflexivity.
Qed.

Lemma zone_ok_single : forall HP hm V u, zone_ok HP 1 hm V -> 573 <= hm -> V u -> u = arr_get HP 1.
Proof.
  intros HP hm V u [pos [A B]] Hhm Hu. destruct (B u Hu) as [Lu Eu]. unfold live in Lu.
  assert (pos u = 1) by lia. rewrite H in Eu. symmetry. exact Eu.
Qed.



Section Loops123.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).

Lemma elems_range : 19 <= E <= 286 /\ 2 * E + 1 <= 573 /\ 2 * E + 1 = tsize t.
Proof. destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES; lia. Qed.

Definition Vscan (FC : arr) (n : Z) : Z -> Prop := fun u => 0 <= u < n /\ arr_get FC u <> 0.

Lemma loop1_step : forall f FC DL HP HL HM DP BC OL SL MC n mc,
  build_tree_loop1 (S f) (U FC DL HP HL HM DP BC OL SL MC) t E n mc =
  if n <? E then
    if negb (arr_get FC n =? 0) then
      build_tree_loop1 f (U FC DL (arr_set HP (HL + 1) n) (HL + 1) HM (arr_set DP n (wrap8 0)) BC OL SL MC) t E (n + 1) n
    else
      build_tree_loop1 f (U FC (arr_set DL n (wrap16 0)) HP HL HM DP BC OL SL MC) t E (n + 1) mc
  else (U FC DL HP HL HM DP BC OL SL MC, mc).
Proof.
  intros. cbn [build_tree_loop1]. autorewrite with btupd. reflexivity.
Qed.

Lemma loop1_spec : forall f n mc FC DL HP HL DP BC OL SL MC,
  Z.of_nat f = E - n -> 0 <= n <= E -> 0 <= HL <= n -> arr_len HP = 573 -> arr_len DL = tsize t ->
  zone_ok HP HL 573 (Vscan FC n) ->
  -1 <= mc < n -> (forall i, 0 <= i < n -> arr_get FC i <> 0 -> i <= mc) -> (0 <= mc -> arr_get FC mc <> 0) ->
  (0 < HL <-> 0 <= mc) ->
  exists HP' HL' DL' DP' mc',
    build_tree_loop1 f (U FC DL HP HL 573 DP BC OL SL MC) t E n mc = (U FC DL' HP' HL' 573 DP' BC OL SL MC, mc')
    /\ HL <= HL' <= E /\ HL' <= HL + (E - n) /\ arr_len HP' = 573 /\ arr_len DL' = tsize t
    /\ zone_ok HP' HL' 573 (Vscan FC E)
    /\ -1 <= mc' < E /\ (forall i, 0 <= i < E -> arr_get FC i <> 0 -> i <= mc') /\ (0 <= mc' -> arr_get FC mc' <> 0)
    /\ (0 < HL' <-> 0 <= mc')
    /\ (forall i, arr_get DL' i = if (n <=? i) && (i <? E) && (arr_get FC i =? 0) then 0 else arr_get DL i)
    /\ (forall i, ~ (HL < i <= HL') -> arr_get HP' i = arr_get HP i)
    /\ (forall i, 0 <= arr_get DP i < 256 -> 0 <= arr_get DP' i < 256) /\ arr_len DP' = arr_len DP.
Proof.
  induction f as [|f IH]; intros n mc FC DL HP HL DP BC OL SL MC Hf Hn HHL LHP LDL HZ Hmc Hmax Hmcz Hiff.
  - exists HP, HL, DL, DP, mc. cbn [build_tree_loop1].
    assert (n = E) by lia. subst n.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact LHP|]. split; [exact LDL|]. split; [exact HZ|].
    split; [lia|]. split; [exact Hmax|]. split; [exact Hmcz|]. split; [exact Hiff|].
    split; [| split; [intros; reflexivity | split; [intros i Hi; exact Hi | reflexivity]]].
    intros i. destruct (Z.leb_spec E i); destruct (Z.ltb_spec i E); cbn [andb]; try reflexivity. lia.
  - rewrite loop1_step. pose proof elems_range as HE.
    replace (n <? E) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (Z.eqb_spec (arr_get FC n) 0) as [Z0|NZ]; cbn [negb].
    +
      destruct (IH (n + 1) mc FC (arr_set DL n (wrap16 0)) HP HL DP BC OL SL MC ltac:(lia) ltac:(lia) ltac:(lia) LHP
                   ltac:(rewrite arr_len_set; exact LDL)) as (HP' & HL' & DL' & DP' & mc' & EQ & REST).
      { apply (zone_ok_ext _ _ _ (Vscan FC n)); [|exact HZ]. intros u. unfold Vscan. split; [intros [A B]; split; [lia | exact B]|].
        intros [A B]. split; [|exact B]. destruct (Z.eq_dec u n) as [->|]; [exfalso; exact (B Z0) | lia]. }
      { lia. } { intros i Hi Hz. destruct (Z.eq_dec i n) as [->|]; [exfalso; exact (Hz Z0)|]. apply Hmax; [lia | exact Hz]. }
      { exact Hmcz. } { exact Hiff. }
      exists HP', HL', DL', DP', mc'. split; [exact EQ|].
      destruct REST as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
      split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
      split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|].
      split.
      { intros i. rewrite A10. rewrite arr_get_set. unfold arr_inb. rewrite LDL.
        destruct (Z.eqb_spec n i) as [<-|Nni].
        - rewrite Z0, Z.eqb_refl. replace (n <=? n) with true by (symmetry; apply Z.leb_le; lia).
          replace (n <? E) with true by (symmetry; apply Z.ltb_lt; lia).
          destruct (n + 1 <=? n) eqn:En; [apply Z.leb_le in En; lia|]. cbn [andb].
          destruct (Z.leb_spec 0 n); destruct (Z.ltb_spec n (tsize t)); cbn [andb]; try reflexivity; try lia.
          all: rewrite ?wrap16_id by lia; first [reflexivity | lia].
        - cbn [andb]. destruct (Z.leb_spec (n + 1) i); destruct (Z.leb_spec n i); cbn [andb]; try reflexivity; lia. }
      split; [exact A11 | exact A12].
    +
      assert (HLn : HL + 1 <= n + 1) by lia.
      destruct (IH (n + 1) n FC DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) BC OL SL MC
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite arr_len_set; exact LHP) LDL) as (HP' & HL' & DL' & DP' & mc' & EQ & REST).
      { apply (zone_ok_ext _ _ _ (fun u => Vscan FC n u \/ u = n)).
        - intros u. unfold Vscan. split.
          + intros [[A B] | ->]; [split; [lia | exact B] | split; [lia | exact NZ]].
          + intros [A B]. destruct (Z.eq_dec u n) as [->|]; [right; reflexivity | left; split; [lia | exact B]].
        - apply zone_push; [exact HZ | lia | lia | unfold Vscan; lia | lia]. }
      { lia. } { intros i Hi Hz. destruct (Z.eq_dec i n) as [->|]; [lia|]. pose proof (Hmax i ltac:(lia) Hz). lia. }
      { intros _. exact NZ. } { lia. }
      exists HP', HL', DL', DP', mc'. split; [exact EQ|].
      destruct REST as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
      split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
      split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|].
      split.
      { intros i. rewrite A10. destruct (Z.leb_spec (n + 1) i); destruct (Z.leb_spec n i); cbn [andb]; try reflexivity; try lia.
        assert (i = n) by lia. subst i. replace (n <? E) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (arr_get FC n =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. }
      split.
      { intros i Hi. rewrite A11 by lia. rewrite arr_get_set. destruct (Z.eqb_spec (HL + 1) i); [lia | reflexivity]. }
      destruct A12 as [A12 A13]. split; [| rewrite A13, arr_len_set; reflexivity].
      intros i Hi. apply A12. rewrite arr_get_set. destruct (_ && _); [rewrite wrap8_id; lia | exact Hi].
Qed.


Lemma loop2_step : forall f FC DL HP HL HM DP BC OL SL MC mc,
  build_tree_loop2 (S f) (U FC DL HP HL HM DP BC OL SL MC) t mc =
  if HL <? 2 then
    let node := if mc <? 2 then mc + 1 else 0 in
    let mc' := if mc <? 2 then mc + 1 else mc in
    build_tree_loop2 f
      (U (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM (arr_set DP node (wrap8 0)) BC
         (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) MC) t mc'
  else (U FC DL HP HL HM DP BC OL SL MC, mc).
Proof.
  intros. cbn [build_tree_loop2]. autorewrite with btupd.
  destruct (HL <? 2); [|reflexivity]. destruct (mc <? 2); autorewrite with btupd; destruct (stree_has t); autorewrite with btupd; reflexivity.
Qed.

Definition ol_forced (Fl : list Z) (OL : Z) : Z := fold_left (fun acc _ => wrap64 (acc - 1)) Fl OL.
Definition sl_forced (Fl : list Z) (SL : Z) : Z :=
  if stree_has t then fold_left (fun acc f => wrap64 (acc - stree_Len t f)) Fl SL else SL.
Definition fc_forced (Fl : list Z) (FC : arr) : arr := fold_left (fun a f => arr_set a f 1) Fl FC.

Lemma loop2_spec : forall FC DL HP HL DP BC OL SL MC mc,
  0 <= HL <= E -> arr_len HP = 573 -> arr_len FC = tsize t ->
  zone_ok HP HL 573 (Vscan FC E) ->
  -1 <= mc < E -> (forall i, 0 <= i < E -> arr_get FC i <> 0 -> i <= mc) -> (0 <= mc -> arr_get FC mc <> 0) ->
  (0 < HL <-> 0 <= mc) ->
  exists Fl HP2 HL2 DP2 mc2,
    build_tree_loop2 2%nat (U FC DL HP HL 573 DP BC OL SL MC) t mc
    = (U (fc_forced Fl FC) DL HP2 HL2 573 DP2 BC (ol_forced Fl OL) (sl_forced Fl SL) MC, mc2)
    /\ 2 <= HL2 <= E /\ HL <= HL2 /\ HL2 = HL + Z.of_nat (length Fl) /\ (length Fl <= 2)%nat /\ NoDup Fl
    /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get FC f = 0 /\ f <= 2)
    /\ arr_len HP2 = 573 /\ arr_len (fc_forced Fl FC) = tsize t
    /\ zone_ok HP2 HL2 573 (Vscan (fc_forced Fl FC) E)
    /\ 0 <= mc2 < E /\ (forall i, 0 <= i < E -> arr_get (fc_forced Fl FC) i <> 0 -> i <= mc2)
    /\ arr_get (fc_forced Fl FC) mc2 <> 0
    /\ (forall i, arr_get (fc_forced Fl FC) i = if existsb (Z.eqb i) Fl then 1 else arr_get FC i)
    /\ (forall i, ~ (HL < i <= HL2) -> arr_get HP2 i = arr_get HP i)
    /\ (forall i, 0 <= arr_get DP i < 256 -> 0 <= arr_get DP2 i < 256) /\ arr_len DP2 = arr_len DP.
Proof.
  intros FC DL HP HL DP BC OL SL MC mc HHL LHP LFC HZ Hmc Hmax Hmcz Hiff.
  pose proof elems_range as HE.
  assert (PUSH : forall FC0 HP0 HL0 node,
            0 <= HL0 -> HL0 + 1 <= E -> arr_len HP0 = 573 -> arr_len FC0 = tsize t ->
            zone_ok HP0 HL0 573 (Vscan FC0 E) -> 0 <= node < E -> arr_get FC0 node = 0 ->
            zone_ok (arr_set HP0 (HL0 + 1) node) (HL0 + 1) 573 (Vscan (arr_set FC0 node (wrap16 1)) E)
            /\ (forall i, arr_get (arr_set FC0 node (wrap16 1)) i = if i =? node then 1 else arr_get FC0 i)).
  { intros FC0 HP0 HL0 node H0 H1 L0 LF0 HZ0 Hnode Fz.
    assert (EG : forall i, arr_get (arr_set FC0 node (wrap16 1)) i = if i =? node then 1 else arr_get FC0 i).
    { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LF0. rewrite (Z.eqb_sym node i).
      destruct (Z.eqb_spec i node) as [->|]; cbn [andb]; [|reflexivity].
      replace ((0 <=? node) && (node <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      reflexivity. }
    split; [|exact EG].
    apply (zone_ok_ext _ _ _ (fun u => Vscan FC0 E u \/ u = node)).
    - intros u. unfold Vscan. rewrite EG. split.
      + intros [[A B] | ->]; [| rewrite Z.eqb_refl; split; lia]. destruct (Z.eqb_spec u node) as [->|]; [split; lia|]. split; [lia | exact B].
      + intros [A B]. destruct (Z.eqb_spec u node) as [->|]; [right; reflexivity | left]. split; [lia | exact B].
    - apply zone_push; [exact HZ0 | lia | lia | unfold Vscan; intros [A B]; exact (B Fz) | lia]. }
  rewrite loop2_step. destruct (Z.ltb_spec HL 2) as [C1|C1].
  2: {
    exists [], HP, HL, DP, mc. unfold sl_forced, ol_forced, fc_forced. cbn [fold_left length Z.of_nat existsb].
    replace (if stree_has t then SL else SL) with SL by (destruct (stree_has t); reflexivity).
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [constructor|].
    split; [intros f Hf; destruct Hf|]. split; [exact LHP|]. split; [exact LFC|]. split; [exact HZ|].
    split; [lia|]. split; [exact Hmax|]. split; [apply Hmcz; lia|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|]. split; [intros i Hi; exact Hi | reflexivity]. }
  cbv zeta.
  set (node1 := if mc <? 2 then mc + 1 else 0). set (mc1 := if mc <? 2 then mc + 1 else mc).
  assert (Hn1 : 0 <= node1 < E /\ node1 <= 2 /\ arr_get FC node1 = 0 /\ 0 <= mc1 < E /\ node1 <= mc1
                /\ (forall i, 0 <= i < E -> arr_get FC i <> 0 -> i <= mc1) /\ (mc1 = node1 \/ arr_get FC mc1 <> 0)).
  { subst node1 mc1. destruct (Z.ltb_spec mc 2) as [Cm|Cm].
    - assert (Fz : arr_get FC (mc + 1) = 0).
      { destruct (Z.eq_dec (arr_get FC (mc + 1)) 0) as [|NZ]; [assumption|]. exfalso. pose proof (Hmax (mc + 1) ltac:(lia) NZ). lia. }
      repeat split; try lia; try (left; reflexivity). all: intros i Hi Hz; pose proof (Hmax i Hi Hz); lia.
    -
      assert (Fz : arr_get FC 0 = 0).
      { destruct (Z.eq_dec (arr_get FC 0) 0) as [|NZ]; [assumption|]. exfalso.
        assert (HL1 : HL = 1) by lia.
        assert (V0 : Vscan FC E 0) by (split; [lia | exact NZ]).
        assert (Vm : Vscan FC E mc) by (split; [lia | apply Hmcz; lia]).
        rewrite HL1 in HZ. pose proof (zone_ok_single _ _ _ _ HZ ltac:(lia) V0). pose proof (zone_ok_single _ _ _ _ HZ ltac:(lia) Vm). lia. }
      repeat split; try lia; try exact Hmax. all: right; apply Hmcz; lia. }
  destruct Hn1 as (N1a & N1b & N1c & M1a & M1b & M1c & M1d).
  destruct (PUSH FC HP HL node1 ltac:(lia) ltac:(lia) LHP LFC HZ ltac:(lia) N1c) as [HZ1 EG1].
  rewrite loop2_step. destruct (Z.ltb_spec (HL + 1) 2) as [C2|C2].
  2: {
    exists [node1], (arr_set HP (HL + 1) node1), (HL + 1), (arr_set DP node1 (wrap8 0)), mc1.
    unfold sl_forced, ol_forced, fc_forced. cbn [fold_left length Z.of_nat existsb].
    rewrite wrap16_id by lia.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [constructor; [intros [] | constructor]|].
    split; [intros f [<-|[]]; split; [lia | split; [exact N1c | lia]]|].
    split; [rewrite arr_len_set; exact LHP|]. split; [rewrite arr_len_set; exact LFC|].
    rewrite <- (wrap16_id 1) by lia. split; [exact HZ1|]. rewrite (wrap16_id 1) in EG1 |- * by lia.
    split; [lia|]. split.
    { intros i Hi Hz. rewrite EG1 in Hz. destruct (Z.eqb_spec i node1) as [->|]; [lia|]. exact (M1c i Hi Hz). }
    split. { rewrite EG1. destruct (Z.eqb_spec mc1 node1); [lia|]. destruct M1d as [|H]; [congruence | exact H]. }
    split. { intros i. rewrite EG1. rewrite Bool.orb_false_r. reflexivity. }
    split. { intros i Hi. rewrite arr_get_set. destruct (Z.eqb_spec (HL + 1) i); [lia | reflexivity]. }
    split; [| rewrite arr_len_set; reflexivity].
    intros i Hi. rewrite arr_get_set. destruct (_ && _); [rewrite wrap8_id; lia | exact Hi]. }
  assert (HL0 : HL = 0) by lia. assert (Hmc0 : mc = -1) by (destruct (Z_lt_le_dec mc 0); [lia | exfalso; lia]).
  assert (En1 : node1 = 0) by (subst node1; rewrite Hmc0; reflexivity).
  assert (Em1 : mc1 = 0) by (subst mc1; rewrite Hmc0; reflexivity).
  rewrite Em1. cbv zeta. cbn [Z.ltb Z.compare Z.add Pos.add].
  change (0 + 1) with 1. rewrite En1 in *.
  assert (Fz1 : arr_get (arr_set FC 0 (wrap16 1)) 1 = 0).
  { rewrite EG1. cbn [Z.eqb]. destruct (Z.eq_dec (arr_get FC 1) 0) as [|NZ]; [assumption|]. exfalso. pose proof (Hmax 1 ltac:(lia) NZ). lia. }
  destruct (PUSH (arr_set FC 0 (wrap16 1)) (arr_set HP (HL + 1) 0) (HL + 1) 1 ltac:(lia) ltac:(lia)
              ltac:(rewrite arr_len_set; exact LHP) ltac:(rewrite arr_len_set; exact LFC) HZ1 ltac:(lia) Fz1) as [HZ2 EG2].
  cbn [build_tree_loop2].
  exists [0; 1], (arr_set (arr_set HP (HL + 1) 0) (HL + 1 + 1) 1), (HL + 1 + 1), (arr_set (arr_set DP 0 (wrap8 0)) 1 (wrap8 0)), 1.
  unfold sl_forced, ol_forced, fc_forced. cbn [fold_left length Z.of_nat existsb].
  rewrite (wrap16_id 1) in HZ2, EG2, EG1, Fz1 |- * by lia.
  split. { destruct (stree_has t); reflexivity. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { constructor; [intros [H|[]]; lia | constructor; [intros [] | constructor]]. }
  split. { intros f [<-|[<-|[]]]; (split; [lia | split; [| lia]]); [exact N1c|]. rewrite EG1 in Fz1. cbn in Fz1. exact Fz1. }
  split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LFC|].
  split; [exact HZ2|].
  split; [lia|]. split.
  { intros i Hi Hz. rewrite EG2, EG1 in Hz. destruct (Z.eqb_spec i 1); [lia|]. destruct (Z.eqb_spec i 0); [lia|]. pose proof (Hmax i Hi Hz). lia. }
  split. { rewrite EG2. cbn. lia. }
  split. { intros i. rewrite EG2, EG1. destruct (Z.eqb_spec i 0) as [E0|N0]; destruct (Z.eqb_spec i 1) as [E1|N1]; cbn [orb]; try reflexivity; lia. }
  split. { intros i Hi. rewrite !arr_get_set. destruct (Z.eqb_spec (HL + 1 + 1) i); [lia|]. destruct (Z.eqb_spec (HL + 1) i); [lia|]. reflexivity. }
  split; [| rewrite !arr_len_set; reflexivity].
  intros i Hi. rewrite !arr_get_set. destruct (_ && _); [rewrite wrap8_id; lia|]. destruct (_ && _); [rewrite wrap8_id; lia | exact Hi].
Qed.


Lemma loop3_spec : forall f n FC DL HP HL HM DP BC OL SL MC V,
  0 <= n <= HL -> HL <= 572 -> HL < HM -> arr_len HP = 573 ->
  zone_ok HP HL HM V ->
  exists HP3,
    build_tree_loop3 f (U FC DL HP HL HM DP BC OL SL MC) t n = U FC DL HP3 HL HM DP BC OL SL MC
    /\ zone_ok HP3 HL HM V /\ arr_len HP3 = 573
    /\ (forall i, ~ (1 <= i <= HL) -> arr_get HP3 i = arr_get HP i).
Proof.
  induction f as [|f IH]; intros n FC DL HP HL HM DP BC OL SL MC V Hn HHL Hlm LHP HZ.
  - exists HP. cbn [build_tree_loop3]. split; [reflexivity|]. split; [exact HZ|]. split; [exact LHP|]. intros; reflexivity.
  - cbn [build_tree_loop3]. destruct (Z.leb_spec 1 n) as [C|C].
    2: { exists HP. split; [reflexivity|]. split; [exact HZ|]. split; [exact LHP|]. intros; reflexivity. }
    set (s0 := U FC DL HP HL HM DP BC OL SL MC).
    destruct (pqdownheap_zone s0 t n HM V) as (Z1 & O1 & L1 & A1 & S1); subst s0; autorewrite with btupd; try assumption; try lia.
    rewrite S1. autorewrite with btupd.
    set (HP1 := ds_heap (pqdownheap (U FC DL HP HL HM DP BC OL SL MC) t n)) in *.
    rewrite ?bt_heap, ?bt_heap_len in O1, Z1, L1.
    destruct (IH (n - 1) FC DL HP1 HL HM DP BC OL SL MC V ltac:(lia) HHL Hlm A1 Z1) as (HP3 & EQ & Z3 & L3 & O3).
    exists HP3. split; [exact EQ|]. split; [exact Z3|]. split; [exact L3|].
    intros i Hi. rewrite (O3 i Hi), (O1 i Hi). rewrite ?bt_heap. reflexivity.
Qed.

End Loops123.
