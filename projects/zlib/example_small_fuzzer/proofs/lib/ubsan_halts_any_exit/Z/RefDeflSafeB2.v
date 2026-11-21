(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.

Module RefDeflSafeB1.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
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

Lemma zone_ok_agree : forall HP HP' hl hm V,
  zone_ok HP hl hm V -> (forall i, live hl hm i -> arr_get HP' i = arr_get HP i) -> zone_ok HP' hl hm V.
Proof.
  intros HP HP' hl hm V [pos [A B]] HE. exists pos. split.
  - intros i Hi. rewrite (HE i Hi). exact (A i Hi).
  - intros u Hu. destruct (B u Hu) as [Lu Eu]. split; [exact Lu|]. rewrite (HE _ Lu). exact Eu.
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
End RefDeflSafeB1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac inb_true k HP :=
  replace ((0 <=? k) && (k <? arr_len HP)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).


Lemma zone_pop : forall HP hl hm V,
  zone_ok HP hl hm V -> 2 <= hl -> hl < hm -> hl < arr_len HP ->
  zone_ok (arr_set HP 1 (arr_get HP hl)) (hl - 1) hm (fun u => V u /\ u <> arr_get HP 1).
Proof.
  intros HP hl hm V [pos [A B]] Hhl Hlm HL.
  assert (L1 : live hl hm 1) by (left; lia). assert (Lh : live hl hm hl) by (left; lia).
  destruct (A 1 L1) as [V1 P1]. destruct (A hl Lh) as [Vh Ph].
  exists (fun u => if Z.eq_dec u (arr_get HP hl) then 1 else pos u). split.
  - intros i Hi. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec 1 i) as [<-|N1].
    + inb_true 1 HP. cbn [andb]. split.
      * split; [exact Vh|]. intros E. rewrite E, P1 in Ph. lia.
      * destruct (Z.eq_dec _ _); [reflexivity | congruence].
    + cbn [andb]. assert (Li : live hl hm i) by (unfold live in *; lia).
      destruct (A i Li) as [Vi Pi]. split.
      * split; [exact Vi|]. intros E. rewrite E, P1 in Pi. exact (N1 Pi).
      * destruct (Z.eq_dec (arr_get HP i) (arr_get HP hl)) as [E|NE]; [|exact Pi].
        exfalso. rewrite E, Ph in Pi. unfold live in Hi. lia.
  - intros u [Hu Nu]. destruct (B u Hu) as [Lu Eu].
    destruct (Z.eq_dec u (arr_get HP hl)) as [->|NE].
    + split; [left; lia|]. rewrite arr_get_set. unfold arr_inb. rewrite Z.eqb_refl. inb_true 1 HP. reflexivity.
    + assert (pos u <> hl) by (intros E; apply NE; rewrite <- Eu, E; reflexivity).
      assert (pos u <> 1) by (intros E; apply Nu; rewrite <- Eu, E; reflexivity).
      split; [unfold live in *; lia|].
      rewrite arr_get_set. unfold arr_inb. destruct (Z.eqb_spec 1 (pos u)); [lia|]. cbn [andb]. exact Eu.
Qed.

Lemma zone_round : forall HP hl hm W n node,
  zone_ok HP hl hm W -> 1 <= hl -> hl + 3 <= hm -> hm <= 573 -> arr_len HP = 573 ->
  ~ W n -> ~ W node -> n <> node ->
  let m := arr_get HP 1 in
  zone_ok (arr_set (arr_set (arr_set HP (hm - 1) n) (hm - 2) m) 1 node) hl (hm - 2)
          (fun u => W u \/ u = n \/ u = node)
  /\ W m.
Proof.
  intros HP hl hm W n node [pos [A B]] Hhl Hhm Hhm' HL Nn Nnode Nnn. cbv zeta.
  assert (L1 : live hl hm 1) by (left; lia). destruct (A 1 L1) as [Vm Pm].
  set (m := arr_get HP 1) in *.
  split; [|exact Vm].
  exists (fun u => if Z.eq_dec u node then 1 else if Z.eq_dec u n then hm - 1 else if Z.eq_dec u m then hm - 2 else pos u).
  assert (G : forall i, arr_get (arr_set (arr_set (arr_set HP (hm - 1) n) (hm - 2) m) 1 node) i
                      = if 1 =? i then node else if hm - 2 =? i then m else if hm - 1 =? i then n else arr_get HP i).
  { intros i. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, HL.
    replace ((0 <=? 1) && (1 <? 573)) with true by reflexivity.
    replace ((0 <=? hm - 2) && (hm - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace ((0 <=? hm - 1) && (hm - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite !Bool.andb_true_r. reflexivity. }
  assert (Nmn : m <> n) by (intros E; apply Nn; rewrite <- E; exact Vm).
  assert (Nmnode : m <> node) by (intros E; apply Nnode; rewrite <- E; exact Vm).
  split.
  - intros i Hi. rewrite G.
    destruct (Z.eqb_spec 1 i) as [<-|N1].
    { split; [right; right; reflexivity|]. destruct (Z.eq_dec node node); [reflexivity | congruence]. }
    destruct (Z.eqb_spec (hm - 2) i) as [<-|N2].
    { split; [left; exact Vm|]. destruct (Z.eq_dec m node); [congruence|]. destruct (Z.eq_dec m n); [congruence|]. destruct (Z.eq_dec m m); [reflexivity | congruence]. }
    destruct (Z.eqb_spec (hm - 1) i) as [<-|N3].
    { split; [right; left; reflexivity|]. destruct (Z.eq_dec n node); [congruence|]. destruct (Z.eq_dec n n); [reflexivity | congruence]. }
    assert (Li : live hl hm i) by (unfold live in *; lia).
    destruct (A i Li) as [Vi Pi]. split; [left; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) node) as [E|_]; [exfalso; apply Nnode; rewrite <- E; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) n) as [E|_]; [exfalso; apply Nn; rewrite <- E; exact Vi|].
    destruct (Z.eq_dec (arr_get HP i) m) as [E|_]; [| exact Pi].
    exfalso. rewrite E, Pm in Pi. exact (N1 Pi).
  - intros u Hu.
    destruct (Z.eq_dec u node) as [->|Nu1].
    { split; [left; lia|]. rewrite G. rewrite Z.eqb_refl. reflexivity. }
    destruct (Z.eq_dec u n) as [->|Nu2].
    { split; [right; lia|]. rewrite G. replace (1 =? hm - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (hm - 2 =? hm - 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
    destruct (Z.eq_dec u m) as [->|Nu3].
    { split; [right; lia|]. rewrite G. replace (1 =? hm - 2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
    destruct Hu as [Hu | [Hu | Hu]]; [| congruence | congruence].
    destruct (B u Hu) as [Lu Eu].
    assert (pos u <> 1) by (intros E; apply Nu3; unfold m; rewrite <- E, Eu; reflexivity).
    split; [unfold live in *; lia|].
    rewrite G. replace (1 =? pos u) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (hm - 2 =? pos u) with false by (symmetry; apply Z.eqb_neq; unfold live in Lu; lia).
    replace (hm - 1 =? pos u) with false by (symmetry; apply Z.eqb_neq; unfold live in Lu; lia).
    exact Eu.
Qed.


Section Loop4.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation U := (bt_upd s t).
Local Notation E := (sd_elems t).

Lemma loop4_unfold : forall f X node,
  build_tree_loop4 (S f) X t node =
  (let n := heap_get X SMALLEST in
   let X1 := pqdownheap (set_heap_len (heap_set X SMALLEST (heap_get X (ds_heap_len X))) (ds_heap_len X - 1)) t SMALLEST in
   let m := heap_get X1 SMALLEST in
   let X2 := heap_set (set_heap_max X1 (ds_heap_max X1 - 1)) (ds_heap_max X1 - 1) n in
   let X3 := heap_set (set_heap_max X2 (ds_heap_max X2 - 1)) (ds_heap_max X2 - 1) m in
   let X4 := set_Freq X3 t node (Freq X3 t n + Freq X3 t m) in
   let X5 := depth_set X4 node ((if depth_get X4 m <=? depth_get X4 n then depth_get X4 n else depth_get X4 m) + 1) in
   let X6 := heap_set (set_Dad (set_Dad X5 t m node) t n node) SMALLEST node in
   let X7 := pqdownheap X6 t SMALLEST in
   if 2 <=? ds_heap_len X7 then build_tree_loop4 f X7 t (node + 1) else X7).
Proof.
  intros f X node. cbv fix beta iota delta [build_tree_loop4]. fold build_tree_loop4.
  generalize pqdownheap. intros pq. cbv zeta. dsred. reflexivity.
Qed.

Lemma loop4_round : forall FC DL HP HL HM DP BC OL SL MC node V,
  zone_ok HP HL HM V -> 2 <= HL -> HL + 2 <= HM -> HM <= 573 ->
  arr_len HP = 573 -> arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len DP = 573 ->
  ~ V node -> 0 <= node < tsize t -> (forall u, V u -> 0 <= u < node) ->
  exists HP4 n m,
    n = arr_get HP 1 /\ V n /\ V m /\ n <> m
    /\ (forall f, build_tree_loop4 (S f) (U FC DL HP HL HM DP BC OL SL MC) t node
         = let s4 := U (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m)))
                       (arr_set (arr_set DL m (wrap16 node)) n (wrap16 node))
                       HP4 (HL - 1) (HM - 2)
                       (arr_set DP node (wrap8 ((if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1)))
                       BC OL SL MC in
           if 2 <=? HL - 1 then build_tree_loop4 f s4 t (node + 1) else s4)
    /\ zone_ok HP4 (HL - 1) (HM - 2) (fun u => V u \/ u = node)
    /\ arr_get HP4 (HM - 1) = n /\ arr_get HP4 (HM - 2) = m
    /\ (forall i, HM <= i -> arr_get HP4 i = arr_get HP i)
    /\ arr_len HP4 = 573
    /\ (forall i, HM <= i < 573 -> arr_get HP i <> n /\ arr_get HP i <> m).
Proof.
  intros FC DL HP HL HM DP BC OL SL MC node V HZ HHL HHM H573 LHP LFC LDL LDP Nnode Hnode Hlt.
  set (n := arr_get HP 1).
  pose proof (zone_pop HP HL HM V HZ HHL ltac:(lia) ltac:(lia)) as HZa. fold n in HZa.
  set (HPa := arr_set HP 1 (arr_get HP HL)) in HZa.
  set (Xa := U FC DL HPa (HL - 1) HM DP BC OL SL MC).
  destruct (pqdownheap_zone Xa t 1 HM (fun u => V u /\ u <> n)) as (Zb & Ob & Lb & Ab & Sb);
    [subst Xa; autorewrite with btupd; first [exact HZa | lia | (subst HPa; rewrite arr_len_set; exact LHP)] ..|].
  subst Xa. autorewrite with btupd in Zb. autorewrite with btupd in Ob. rewrite bt_heap_len in Lb.
  set (HPb := ds_heap (pqdownheap (U FC DL HPa (HL - 1) HM DP BC OL SL MC) t 1)) in *.
  assert (Vn : V n) by (apply (zone_ok_mem _ _ _ _ 1 HZ); left; lia).
  destruct (zone_round HPb (HL - 1) HM (fun u => V u /\ u <> n) n node Zb ltac:(lia) ltac:(lia) H573 Ab
              ltac:(intros [_ X]; exact (X eq_refl)) ltac:(intros [X _]; exact (Nnode X)) ltac:(pose proof (Hlt n Vn); lia))
    as [Zc [Vm Nmn]].
  set (m := arr_get HPb 1) in *.
  set (HPc := arr_set (arr_set (arr_set HPb (HM - 1) n) (HM - 2) m) 1 node) in *.
  set (FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m))).
  set (DL' := arr_set (arr_set DL m (wrap16 node)) n (wrap16 node)).
  set (DP' := arr_set DP node (wrap8 ((if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1))).
  set (Xc := U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC).
  assert (LHPc : arr_len HPc = 573) by (subst HPc; rewrite !arr_len_set; exact Ab).
  destruct (pqdownheap_zone Xc t 1 (HM - 2) (fun u => (V u /\ u <> n) \/ u = n \/ u = node)) as (Zd & Od & Ld & Ad & Sd);
    [subst Xc; autorewrite with btupd; first [exact Zc | lia | exact LHPc] ..|].
  subst Xc. autorewrite with btupd in Zd. autorewrite with btupd in Od. rewrite bt_heap_len in Ld.
  set (HPd := ds_heap (pqdownheap (U FC' DL' HPc (HL - 1) (HM - 2) DP' BC OL SL MC) t 1)) in *.
  exists HPd, n, m.
  split; [reflexivity|]. split; [exact Vn|]. split; [exact Vm|]. split; [intros Emn; exact (Nmn (eq_sym Emn))|].
  split.
  { intros f. rewrite loop4_unfold. unfold SMALLEST. cbv zeta. autorewrite with btupd.
    fold n. fold HPa. rewrite Sb. autorewrite with btupd. fold m.
    replace (HM - 1 - 1) with (HM - 2) by lia.
    fold FC'. fold DP'. fold DL'. fold HPc.
    rewrite Sd. autorewrite with btupd. reflexivity. }
  split.
  { apply (zone_ok_ext _ _ _ (fun u => (V u /\ u <> n) \/ u = n \/ u = node)); [|exact Zd].
    intros u. split.
    - intros [[X _]|[->| ->]]; [left; exact X | left; exact Vn | right; reflexivity].
    - intros [X| ->]; [|right; right; reflexivity]. destruct (Z.eq_dec u n) as [->|]; [right; left; reflexivity | left; split; assumption]. }
  assert (G1 : arr_get HPc (HM - 1) = n).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 2 =? HM - 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 1) && (HM - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  assert (G2 : arr_get HPc (HM - 2) = m).
  { subst HPc. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Ab.
    replace (1 =? HM - 2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
    replace ((0 <=? HM - 2) && (HM - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  split; [rewrite (Od (HM - 1)) by lia; exact G1|].
  split; [rewrite (Od (HM - 2)) by lia; exact G2|].
  split.
  { intros i Hi. rewrite (Od i) by lia. subst HPc. rewrite !arr_get_set.
    replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 2 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (HM - 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  split; [exact Ad|].
  intros i Hi. split.
  - intros En. pose proof (zone_ok_inj _ _ _ _ i 1 HZ ltac:(right; lia) ltac:(left; lia) En). lia.
  - intros Em. assert (Ei : arr_get HPb i = arr_get HP i).
    { rewrite (Ob i) by lia. subst HPa. rewrite arr_get_set. replace (1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite <- Ei in Em. pose proof (zone_ok_inj _ _ _ _ i 1 Zb ltac:(right; lia) ltac:(left; lia) Em). lia.
Qed.


Section WholeLoop.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.

Definition V0 : Z -> Prop := Vscan FC2 E.
Definition Vj (j : Z) : Z -> Prop := fun u => V0 u \/ (E <= u < E + j).

Record INV4 (j : Z) (FCj DLj HPj DPj : arr) : Prop := {
  i4_zone : zone_ok HPj (L - j) (573 - 2 * j) (Vj j);
  i4_dad : forall i, 573 - 2 * j <= i < 573 -> arr_get DLj (arr_get HPj i) = E + (572 - i) / 2;
  i4_old : forall i, 573 - 2 * j <= i < 573 -> E <= arr_get HPj i -> arr_get HPj i < E + (572 - i) / 2;
  i4_fc : forall u, 0 <= u < E -> arr_get FCj u = arr_get FC2 u;
  i4_dl : forall u, 0 <= u < E -> arr_get FC2 u = 0 -> arr_get DLj u = arr_get DL2 u;
  i4_lhp : arr_len HPj = 573;
  i4_lfc : arr_len FCj = tsize t;
  i4_ldl : arr_len DLj = tsize t;
  i4_ldp : arr_len DPj = 573;
  i4_fcr : forall i, 0 <= arr_get FCj i < 65536;
  i4_dpr : forall i, 0 <= arr_get DPj i < 256;
  i4_dlr : forall i, 0 <= arr_get DLj i < 65536 }.

Hypothesis HL : 2 <= L <= E.

Lemma loop4_inv_step : forall j FCj DLj HPj DPj,
  0 <= j -> 2 <= L - j -> INV4 j FCj DLj HPj DPj ->
  exists FC' DL' HP' DP',
    (forall f, build_tree_loop4 (S f) (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
       = let s4 := U FC' DL' HP' (L - (j + 1)) (573 - 2 * (j + 1)) DP' BC OL SL MC in
         if 2 <=? L - (j + 1) then build_tree_loop4 f s4 t (E + (j + 1)) else s4)
    /\ INV4 (j + 1) FC' DL' HP' DP'.
Proof.
  intros j FCj DLj HPj DPj Hj Hr INV. pose proof (elems_range t) as HE.
  destruct INV as [Z0 D0 O0 F0 L0 LHP LFC LDL LDP RFC RDP RDL].
  destruct (loop4_round FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC (E + j) (Vj j) Z0
              ltac:(lia) ltac:(lia) ltac:(lia) LHP LFC LDL LDP)
    as (HP4 & n & m & En & Vn & Vm & Nnm & EQ & Z4 & G1 & G2 & O4 & L4 & D4).
  { unfold Vj, V0, Vscan. lia. } { lia. } { unfold Vj, V0, Vscan. intros u Hu. lia. }
  exists (arr_set FCj (E + j) (wrap16 (arr_get FCj n + arr_get FCj m))),
         (arr_set (arr_set DLj m (wrap16 (E + j))) n (wrap16 (E + j))), HP4,
         (arr_set DPj (E + j) (wrap8 ((if arr_get DPj m <=? arr_get DPj n then arr_get DPj n else arr_get DPj m) + 1))).
  split.
  { intros f. rewrite (EQ f). replace (L - j - 1) with (L - (j + 1)) by lia.
    replace (573 - 2 * j - 2) with (573 - 2 * (j + 1)) by lia. replace (E + j + 1) with (E + (j + 1)) by lia. reflexivity. }
  assert (Vlt : forall u, Vj j u -> 0 <= u < E + j) by (unfold Vj, V0, Vscan; intros u Hu; lia).
  pose proof (Vlt n Vn) as Rn. pose proof (Vlt m Vm) as Rm.
  assert (W16 : wrap16 (E + j) = E + j) by (apply wrap16_id; lia).
  constructor.
  - replace (L - (j + 1)) with (L - j - 1) by lia. replace (573 - 2 * (j + 1)) with (573 - 2 * j - 2) by lia.
    apply (zone_ok_ext _ _ _ (fun u => Vj j u \/ u = E + j)); [|exact Z4].
    unfold Vj. intros u. split; intros HH.
    + destruct HH as [[A|A]|A]; [left; exact A | right; lia | right; lia].
    + destruct HH as [A|A]; [left; left; exact A|]. destruct (Z.eq_dec u (E + j)); [right; lia | left; right; lia].
  - intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LDL. rewrite W16.
    destruct (Z.eq_dec i (573 - 2 * j - 1)) as [->|N1].
    { rewrite G1. rewrite Z.eqb_refl. replace ((0 <=? n) && (n <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. replace (572 - (573 - 2 * j - 1)) with (j * 2) by lia. rewrite Z.div_mul by lia. reflexivity. }
    destruct (Z.eq_dec i (573 - 2 * j - 2)) as [->|N2].
    { rewrite G2. destruct (Z.eqb_spec n m); [exfalso; exact (Nnm ltac:(assumption))|]. cbn [andb]. rewrite Z.eqb_refl.
      replace ((0 <=? m) && (m <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. replace (572 - (573 - 2 * j - 2)) with (1 + j * 2) by lia. rewrite Z.div_add by lia. reflexivity. }
    rewrite O4 by lia. destruct (D4 i ltac:(lia)) as [Nin Nim].
    replace (n =? arr_get HPj i) with false by (symmetry; apply Z.eqb_neq; congruence).
    replace (m =? arr_get HPj i) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [andb].
    apply D0. lia.
  - intros i Hi Hge.
    destruct (Z.eq_dec i (573 - 2 * j - 1)) as [->|N1]; [rewrite G1 in Hge |- *; replace (572 - (573 - 2 * j - 1)) with (j * 2) by lia; rewrite Z.div_mul by lia; lia|].
    destruct (Z.eq_dec i (573 - 2 * j - 2)) as [->|N2]; [rewrite G2 in Hge |- *; replace (572 - (573 - 2 * j - 2)) with (1 + j * 2) by lia; rewrite Z.div_add by lia; change (1 / 2) with 0; lia|].
    rewrite O4 in Hge |- * by lia. apply O0; lia.
  - intros u Hu. rewrite arr_get_set. replace (E + j =? u) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. apply F0. exact Hu.
  - intros u Hu Hz. rewrite !arr_get_set.
    assert (~ Vj j u) by (unfold Vj, V0, Vscan; lia).
    replace (n =? u) with false by (symmetry; apply Z.eqb_neq; congruence).
    replace (m =? u) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [andb]. apply L0; assumption.
  - exact L4.
  - rewrite arr_len_set. exact LFC.
  - rewrite !arr_len_set. exact LDL.
  - rewrite arr_len_set. exact LDP.
  - intros i. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply RFC].
  - intros i. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply RDP].
  - intros i. rewrite !arr_get_set. destruct (_ && _); [apply wrap16_range|]. destruct (_ && _); [apply wrap16_range | apply RDL].
Qed.

Lemma loop4_spec : forall f j FCj DLj HPj DPj,
  0 <= j -> 2 <= L - j -> (Z.of_nat f >= L - j - 1) -> INV4 j FCj DLj HPj DPj ->
  exists FC' DL' HP' DP',
    build_tree_loop4 f (U FCj DLj HPj (L - j) (573 - 2 * j) DPj BC OL SL MC) t (E + j)
    = U FC' DL' HP' 1 (573 - 2 * (L - 1)) DP' BC OL SL MC
    /\ INV4 (L - 1) FC' DL' HP' DP'.
Proof.
  induction f as [|f IH]; intros j FCj DLj HPj DPj Hj Hr Hf INV; [lia|].
  destruct (loop4_inv_step j FCj DLj HPj DPj Hj Hr INV) as (FC' & DL' & HP' & DP' & EQ & INV').
  rewrite (EQ f). cbv zeta.
  destruct (Z.leb_spec 2 (L - (j + 1))) as [C|C].
  - apply (IH (j + 1)); [lia | lia | lia | exact INV'].
  - exists FC', DL', HP', DP'. replace (L - 1) with (j + 1) by lia. split; [| exact INV'].
    replace (L - (j + 1)) with 1 by lia. reflexivity.
Qed.
End WholeLoop.


Record heap_result (FC2 DL2 : arr) (L mc : Z) (FCf DLf HPf DPf : arr) : Prop := {
  hr_L : 2 <= L <= E;
  hr_mc : 0 <= mc < E;
  hr_mc_max : forall u, 0 <= u < E -> arr_get FC2 u <> 0 -> u <= mc;
  hr_mc_in : arr_get FC2 mc <> 0;
  hr_root : arr_get HPf (574 - 2 * L) = E + L - 2;
  hr_top : arr_get HPf 1 = E + L - 2;
  hr_tail : forall i, 574 - 2 * L < i < 573 -> Vj FC2 (L - 1) (arr_get HPf i);
  hr_dad : forall i, 574 - 2 * L < i < 573 -> arr_get DLf (arr_get HPf i) = E + (572 - i) / 2;
  hr_old : forall i, 574 - 2 * L < i < 573 -> E <= arr_get HPf i -> arr_get HPf i < E + (572 - i) / 2;
  hr_inj : forall i k, 574 - 2 * L <= i < 573 -> 574 - 2 * L <= k < 573 -> arr_get HPf i = arr_get HPf k -> i = k;
  hr_cov : forall u, Vj FC2 (L - 1) u -> exists i, 574 - 2 * L <= i < 573 /\ arr_get HPf i = u;
  hr_fc : forall u, 0 <= u < E -> arr_get FCf u = arr_get FC2 u;
  hr_dl0 : forall u, 0 <= u < E -> arr_get FC2 u = 0 -> arr_get DLf u = 0;
  hr_lhp : arr_len HPf = 573;
  hr_lfc : arr_len FCf = tsize t;
  hr_ldl : arr_len DLf = tsize t;
  hr_ldp : arr_len DPf = 573;
  hr_fcr : forall i, 0 <= arr_get FCf i < 65536;
  hr_dpr : forall i, 0 <= arr_get DPf i < 256;
  hr_dlr : forall i, 0 <= arr_get DLf i < 65536 }.

Theorem heap_phase : forall FC DL HP0 HL0 HM0 DP BC OL SL MC0,
  arr_len FC = tsize t -> arr_len DL = tsize t -> arr_len HP0 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= arr_get FC i < 65536) ->
  (forall i, 0 <= arr_get DL i < 65536) ->
  (forall i, 0 <= arr_get DP i < 256) ->
  let s0 := set_heap_max (set_heap_len (U FC DL HP0 HL0 HM0 DP BC OL SL MC0) 0) HEAP_SIZE in
  let '(s1, mc1) := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
  let '(s2, mc) := build_tree_loop2 2%nat s1 t mc1 in
  let s3 := set_max_code s2 t mc in
  let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
  let s5 := build_tree_loop4 573%nat s4 t E in
  let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
  let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
  exists Fl DL2 HP2 DP2 L FCf DLf HPf DPf,
    let FC2 := fc_forced Fl FC in
    s3 = U FC2 DL2 HP2 L 573 DP2 BC (ol_forced Fl OL) (sl_forced t Fl SL) mc
    /\ s7 = U FCf DLf HPf 1 (574 - 2 * L) DPf BC (ol_forced Fl OL) (sl_forced t Fl SL) mc
    /\ heap_result FC2 DL2 L mc FCf DLf HPf DPf
    /\ zone_ok HP2 L 573 (Vscan FC2 E) /\ arr_len HP2 = 573 /\ arr_len DP2 = 573 /\ arr_len DL2 = tsize t
    /\ (forall i, 0 <= arr_get DP2 i < 256) /\ (forall i, 0 <= arr_get FC2 i < 65536) /\ (forall i, 0 <= arr_get DL2 i < 65536)
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get FC f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get FC i)
    /\ (forall i, arr_get DL2 i = if (0 <=? i) && (i <? E) && (arr_get FC i =? 0) then 0 else arr_get DL i).
Proof.
  intros FC DL HP0 HL0 HM0 DP BC OL SL MC0 LFC LDL LHP LDP RFC RDL RDP. pose proof (elems_range t) as HE.
  cbv zeta. autorewrite with btupd. unfold HEAP_SIZE.
  destruct (loop1_spec s t (Z.to_nat E) 0 (-1) FC DL HP0 0 DP BC OL SL MC0 ltac:(lia) ltac:(lia) ltac:(lia) LHP LDL)
    as (HP1 & HL1 & DL1 & DP1 & mc1 & E1 & B1 & B1' & LHP1 & LDL1 & Z1 & M1 & M1' & M1'' & I1 & DLE1 & HPE1 & DPR1 & LDP1).
  { apply (zone_ok_ext _ _ _ (fun _ => False)); [| apply zone_ok_empty]. unfold Vscan. intros u. lia. }
  { lia. } { intros; lia. } { intros; lia. } { lia. }
  rewrite E1.
  destruct (loop2_spec s t FC DL1 HP1 HL1 DP1 BC OL SL MC0 mc1
              ltac:(lia) LHP1 LFC Z1 M1 M1' M1'' I1)
    as (Fl & HP2 & HL2 & DP2 & mc2 & E2 & B2 & B2' & B2'' & LF & ND & FF & LHP2 & LFC2 & Z2 & M2 & M2' & M2'' & FCE2 & HPE2 & DPR2 & LDP2).
  rewrite E2. autorewrite with btupd.
  set (FC2 := fc_forced Fl FC) in *.
  assert (HL2h : 0 <= HL2 / 2 <= HL2) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (loop3_spec s t (Z.to_nat (HL2 / 2)) (HL2 / 2) FC2 DL1 HP2 HL2 573 DP2 BC
              (ol_forced Fl OL) (sl_forced t Fl SL) mc2 (Vscan FC2 E) HL2h ltac:(lia) ltac:(lia) LHP2 Z2)
    as (HP3 & E3 & Z3 & LHP3 & HPE3).
  rewrite E3.
  assert (DPR2' : forall i, 0 <= arr_get DP2 i < 256) by (intros i; apply DPR2; apply DPR1; apply RDP).
  assert (FCR2 : forall i, 0 <= arr_get FC2 i < 65536) by (intros i; rewrite FCE2; destruct (existsb _ _); [lia | apply RFC]).
  assert (DLR1 : forall i, 0 <= arr_get DL1 i < 65536) by (intros i; rewrite DLE1; destruct (_ && _); [lia | apply RDL]).
  assert (INV0 : INV4 FC2 DL1 HL2 0 FC2 DL1 HP3 DP2).
  { constructor; try assumption; try (intros; lia); try (intros; reflexivity); try (rewrite LDP2, LDP1; exact LDP).
    replace (HL2 - 0) with HL2 by lia. replace (573 - 2 * 0) with 573 by lia.
    apply (zone_ok_ext _ _ _ (Vscan FC2 E)); [|exact Z3]. unfold Vj, V0. intros u. split; [intros A; left; exact A | intros [A|A]; [exact A | lia]]. }
  destruct (loop4_spec FC2 DL1 HL2 BC (ol_forced Fl OL) (sl_forced t Fl SL) mc2 ltac:(lia)
              573 0 FC2 DL1 HP3 DP2 ltac:(lia) ltac:(lia) ltac:(lia) INV0)
    as (FCf & DLf & HPf & DPf & E4 & INVf).
  replace (HL2 - 0) with HL2 in E4 by lia. replace (573 - 2 * 0) with 573 in E4 by lia. replace (E + 0) with E in E4 by lia.
  rewrite E4. autorewrite with btupd. unfold SMALLEST.
  destruct INVf as [Zf Df Of Ff Lf LHPf LFCf LDLf LDPf RFCf RDPf RDLf].
  assert (TOP : arr_get HPf 1 = E + HL2 - 2).
  { destruct Zf as [pos [A B]].
    destruct (B (E + HL2 - 2) ltac:(unfold Vj; right; lia)) as [Lr Er]. unfold live in Lr.
    destruct Lr as [Lr|Lr]; [replace (pos (E + HL2 - 2)) with 1 in Er by lia; exact Er|].
    exfalso. pose proof (Of (pos (E + HL2 - 2)) ltac:(lia) ltac:(rewrite Er; lia)) as X. rewrite Er in X.
    assert ((572 - pos (E + HL2 - 2)) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  exists Fl, DL1, HP2, DP2, HL2, FCf, DLf, (arr_set HPf (573 - 2 * (HL2 - 1) - 1) (arr_get HPf 1)), DPf.
  split; [reflexivity|].
  split. { replace (574 - 2 * HL2) with (573 - 2 * (HL2 - 1) - 1) by lia. reflexivity. }
  split.
  { assert (G : forall i, arr_get (arr_set HPf (573 - 2 * (HL2 - 1) - 1) (arr_get HPf 1)) i = if i =? 574 - 2 * HL2 then E + HL2 - 2 else arr_get HPf i).
    { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LHPf, TOP.
      replace (573 - 2 * (HL2 - 1) - 1) with (574 - 2 * HL2) by lia. rewrite (Z.eqb_sym (574 - 2 * HL2) i).
      destruct (Z.eqb_spec i (574 - 2 * HL2)); cbn [andb]; [|reflexivity].
      replace ((0 <=? 574 - 2 * HL2) && (574 - 2 * HL2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
    constructor; try assumption; try lia.
    - rewrite G, Z.eqb_refl. reflexivity.
    - rewrite G. replace (1 =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). exact TOP.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia).
      apply (zone_ok_mem _ _ _ _ i Zf). right. lia.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). apply Df. lia.
    - intros i Hi. rewrite G. replace (i =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). apply Of. lia.
    - intros i k Hi Hk. rewrite !G.
      destruct (Z.eqb_spec i (574 - 2 * HL2)) as [->|Ni]; destruct (Z.eqb_spec k (574 - 2 * HL2)) as [->|Nk]; intros EQ; try lia.
      + exfalso. pose proof (Of k ltac:(lia) ltac:(rewrite <- EQ; lia)) as X. rewrite <- EQ in X.
        assert ((572 - k) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia.
      + exfalso. pose proof (Of i ltac:(lia) ltac:(rewrite EQ; lia)) as X. rewrite EQ in X.
        assert ((572 - i) / 2 < HL2 - 1) by (apply Z.div_lt_upper_bound; lia). lia.
      + exact (zone_ok_inj _ _ _ _ i k Zf ltac:(right; lia) ltac:(right; lia) EQ).
    - intros u Hu. destruct Zf as [pos [A B]]. destruct (B u Hu) as [Lu Eu]. unfold live in Lu.
      destruct Lu as [Lu|Lu].
      + exists (574 - 2 * HL2). split; [lia|]. rewrite G, Z.eqb_refl. rewrite <- TOP. replace 1 with (pos u) by lia. exact Eu.
      + exists (pos u). split; [lia|]. rewrite G. replace (pos u =? 574 - 2 * HL2) with false by (symmetry; apply Z.eqb_neq; lia). exact Eu.
    - intros u Hu Hz. rewrite (Lf u Hu Hz). rewrite DLE1.
      replace (0 <=? u) with true by (symmetry; apply Z.leb_le; lia). replace (u <? E) with true by (symmetry; apply Z.ltb_lt; lia).
      assert (Fz : arr_get FC u = 0).
      { subst FC2. rewrite FCE2 in Hz. destruct (existsb _ _); [lia | exact Hz]. }
      rewrite Fz. reflexivity.
    - rewrite arr_len_set. exact LHPf. }
  split; [exact Z2|]. split; [exact LHP2|]. split; [rewrite LDP2, LDP1; exact LDP|]. split; [exact LDL1|].
  split; [exact DPR2'|]. split; [exact FCR2|]. split; [exact DLR1|].
  split; [exact LF|]. split; [exact ND|]. split; [exact FF|]. split; [exact FCE2 | exact DLE1].
Qed.

End Loop4.
