(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBits.

Module DeflateTaintBT.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition AG (P : Z -> Prop) (a b : arr) : Prop :=
  arr_len a = arr_len b /\ forall i, P i -> arr_get a i = arr_get b i.

Lemma AG_len P a b : AG P a b -> arr_len a = arr_len b.
Proof. intros [L _]; exact L. Qed.
Lemma AG_get P a b i : AG P a b -> P i -> arr_get a i = arr_get b i.
Proof. intros [_ H]; apply H. Qed.
Lemma AG_mono (P Q : Z -> Prop) a b : AG P a b -> (forall i, Q i -> P i) -> AG Q a b.
Proof. intros [L H] PQ. split; [exact L|]. intros i Qi. apply H, PQ, Qi. Qed.

Lemma AG_set P a b i v : AG P a b -> AG P (arr_set a i v) (arr_set b i v).
Proof.
  intros [L H]. split; [rewrite !arr_len_set; exact L|].
  intros j Pj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct ((i =? j) && _); [reflexivity | apply H; exact Pj].
Qed.
Lemma AG_set_ext P a b i v : AG P a b -> 0 <= i < arr_len a -> AG (fun j => P j \/ j = i) (arr_set a i v) (arr_set b i v).
Proof.
  intros [L H] Hi. split; [rewrite !arr_len_set; exact L|].
  intros j Pj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct (Z.eqb_spec i j) as [<-|NE]; cbn [andb].
  - replace ((0 <=? i) && (i <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
  - apply H. destruct Pj as [Pj| ->]; [exact Pj | congruence].
Qed.
Lemma AG_set_out P a b i v1 v2 : AG P a b -> ~ P i -> AG P (arr_set a i v1) (arr_set b i v2).
Proof.
  intros [L H] NP. split; [rewrite !arr_len_set; exact L|].
  intros j Pj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct (Z.eqb_spec i j) as [<-|NE]; cbn [andb]; [exfalso; exact (NP Pj)|]. apply H; exact Pj.
Qed.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma AG_of_aeq P a b : aeq P a b -> AG (fun i => 0 <= i < arr_len a /\ P i) a b.
Proof. intros [L H]. split; [exact L|]. intros i [Hi Pi]. apply H; assumption. Qed.
Lemma aeq_of_AG P a b : AG P a b -> aeq P a b.
Proof. intros [L H]. split; [exact L|]. intros i _ Pi. apply H, Pi. Qed.


Section BT.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation TS := (tsize t).

Lemma E_TS : 19 <= E <= 286 /\ TS = 2 * E + 1 /\ TS <= 573.
Proof. destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia. Qed.

Record HR2 (V D : Z -> Prop) (x1 x2 : deflate_state) : Prop := {
  h_l1 : tree_lens x1;
  h_l2 : tree_lens x2;
  h_fc : AG (fun i => 0 <= i < E \/ V i) (tree_fc x1 t) (tree_fc x2 t);
  h_dl : AG D (tree_dl x1 t) (tree_dl x2 t);
  h_dp : AG V (ds_depth x1) (ds_depth x2);
  h_hl : ds_heap_len x2 = ds_heap_len x1;
  h_hm : ds_heap_max x2 = ds_heap_max x1;
  h_hp : forall j, live (ds_heap_len x1) (ds_heap_max x1) j -> heap_get x2 j = heap_get x1 j /\ V (heap_get x1 j);
  h_V : forall u, V u -> 0 <= u < TS;
  h_ol : ds_opt_len x2 = ds_opt_len x1;
  h_sl : ds_static_len x2 = ds_static_len x1 }.

Section Facts.
  Variable V : Z -> Prop.
Variable D : Z -> Prop.
Variable x1 : deflate_state.
Variable x2 : deflate_state.
  Hypothesis R : HR2 V D x1 x2.

  Lemma hr_Freq u : (0 <= u < E \/ V u) -> Freq x2 t u = Freq x1 t u.
  Proof. intros Hu. unfold Freq. symmetry. exact (AG_get _ _ _ u (h_fc _ _ _ _ R) Hu). Qed.
  Lemma hr_depth u : V u -> depth_get x2 u = depth_get x1 u.
  Proof. intros Hu. unfold depth_get. symmetry. exact (AG_get _ _ _ u (h_dp _ _ _ _ R) Hu). Qed.
  Lemma hr_Dad u : D u -> Dad x2 t u = Dad x1 t u.
  Proof. intros Hu. unfold Dad. symmetry. exact (AG_get _ _ _ u (h_dl _ _ _ _ R) Hu). Qed.
  Lemma hr_Len u : D u -> Len x2 t u = Len x1 t u.
  Proof. intros Hu. unfold Len. symmetry. exact (AG_get _ _ _ u (h_dl _ _ _ _ R) Hu). Qed.
  Lemma hr_heap j : live (ds_heap_len x1) (ds_heap_max x1) j -> heap_get x2 j = heap_get x1 j.
  Proof. intros Hj. exact (proj1 (h_hp _ _ _ _ R j Hj)). Qed.
  Lemma hr_heapV j : live (ds_heap_len x1) (ds_heap_max x1) j -> V (heap_get x1 j).
  Proof. intros Hj. exact (proj2 (h_hp _ _ _ _ R j Hj)). Qed.
  Lemma hr_smaller n m : V n -> V m -> smaller x2 t n m = smaller x1 t n m.
  Proof. intros Hn Hm. unfold smaller. rewrite !hr_Freq, !hr_depth by (first [right; assumption | assumption]). reflexivity. Qed.
  Lemma hr_hpl : arr_len (ds_heap x1) = 573 /\ arr_len (ds_heap x2) = 573.
  Proof.
    pose proof (h_l1 _ _ _ _ R) as L1. pose proof (h_l2 _ _ _ _ R) as L2. unfold tree_lens in L1, L2.
    split; [apply L1 | apply L2].
  Qed.
End Facts.

Lemma hs_max_code s i v : max_code (heap_set s i v) t = max_code s t. Proof. destruct t; reflexivity. Qed.
Lemma hs_opt_len s i v : ds_opt_len (heap_set s i v) = ds_opt_len s. Proof. reflexivity. Qed.
Lemma hs_static_len s i v : ds_static_len (heap_set s i v) = ds_static_len s. Proof. reflexivity. Qed.
Lemma hs_heap_len s i v : ds_heap_len (heap_set s i v) = ds_heap_len s. Proof. reflexivity. Qed.
Lemma hs_heap_max s i v : ds_heap_max (heap_set s i v) = ds_heap_max s. Proof. reflexivity. Qed.
Lemma hs_tree_fc s i v : tree_fc (heap_set s i v) t = tree_fc s t. Proof. destruct t; reflexivity. Qed.
Lemma hs_tree_dl s i v : tree_dl (heap_set s i v) t = tree_dl s t. Proof. destruct t; reflexivity. Qed.
Lemma hs_depth s i v : ds_depth (heap_set s i v) = ds_depth s. Proof. reflexivity. Qed.

Lemma HR2_heap_set V D x1 x2 j w :
  HR2 V D x1 x2 -> 0 <= j < 573 -> V w -> HR2 V D (heap_set x1 j w) (heap_set x2 j w).
Proof.
  intros R Hj Hw. pose proof (hr_hpl _ _ _ _ R) as [L1 L2].
  destruct R as [T1 T2 F DL DP HL HM HP HV OL SL].
  constructor.
  - apply tree_lens_heap_set, T1.
  - apply tree_lens_heap_set, T2.
  - rewrite !hs_tree_fc. exact F.
  - rewrite !hs_tree_dl. exact DL.
  - rewrite !hs_depth. exact DP.
  - rewrite !hs_heap_len. exact HL.
  - rewrite !hs_heap_max. exact HM.
  - intros i Hi. rewrite !hs_heap_len, !hs_heap_max in Hi. rewrite !heap_get_heap_set by lia.
    destruct (Z.eqb_spec j i) as [<-|NE]; [split; [reflexivity | exact Hw] | exact (HP i Hi)].
  - exact HV.
  - rewrite !hs_opt_len. exact OL.
  - rewrite !hs_static_len. exact SL.
Qed.

Lemma pqdownheap_loop_rel : forall f V D x1 x2 v k j,
  HR2 V D x1 x2 -> V v -> 1 <= k -> j = 2 * k -> ds_heap_len x1 <= 572 ->
  snd (pqdownheap_loop f x2 t v k j) = snd (pqdownheap_loop f x1 t v k j)
  /\ HR2 V D (fst (pqdownheap_loop f x1 t v k j)) (fst (pqdownheap_loop f x2 t v k j))
  /\ 1 <= snd (pqdownheap_loop f x1 t v k j) <= Z.max k (ds_heap_len x1)
  /\ ds_heap_len (fst (pqdownheap_loop f x1 t v k j)) = ds_heap_len x1
  /\ ds_heap_max (fst (pqdownheap_loop f x1 t v k j)) = ds_heap_max x1.
Proof.
  induction f as [|f IH]; intros V D x1 x2 v k j R Hv Hk Hj Hhl.
  - cbn [pqdownheap_loop fst snd]. split; [reflexivity|]. split; [exact R|]. split; [lia|]. split; reflexivity.
  - rewrite !pqdownheap_loop_S. rewrite (h_hl _ _ _ _ R).
    destruct (Z.leb_spec j (ds_heap_len x1)) as [Cj|Cj].
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact R|]. split; [lia|]. split; reflexivity. }
    cbv zeta.
    assert (Lj : live (ds_heap_len x1) (ds_heap_max x1) j) by (unfold live; lia).
    assert (Lj1 : j < ds_heap_len x1 -> live (ds_heap_len x1) (ds_heap_max x1) (j + 1)) by (unfold live; lia).
    rewrite (hr_heap _ _ _ _ R j Lj).
    set (j1 := if (j <? ds_heap_len x1) && smaller x1 t (heap_get x1 (j + 1)) (heap_get x1 j) then j + 1 else j).
    set (j2 := if (j <? ds_heap_len x1) && smaller x2 t (heap_get x2 (j + 1)) (heap_get x1 j) then j + 1 else j).
    assert (Ej : j2 = j1).
    { subst j1 j2. destruct (Z.ltb_spec j (ds_heap_len x1)) as [C|C]; cbn [andb]; [|reflexivity].
      rewrite (hr_heap _ _ _ _ R (j + 1) (Lj1 C)).
      rewrite (hr_smaller _ _ _ _ R) by (apply (hr_heapV _ _ _ _ R); auto). reflexivity. }
    rewrite Ej. clear j2 Ej.
    assert (Hj1 : j <= j1 <= ds_heap_len x1 /\ j1 <= j + 1 /\ live (ds_heap_len x1) (ds_heap_max x1) j1).
    { subst j1. destruct (Z.ltb_spec j (ds_heap_len x1)); cbn [andb]; [destruct (smaller _ _ _ _)|]; unfold live; lia. }
    clearbody j1. destruct Hj1 as (Hj1 & Hj1' & Lj').
    rewrite (hr_heap _ _ _ _ R j1 Lj').
    rewrite (hr_smaller _ _ _ _ R) by (first [exact Hv | apply (hr_heapV _ _ _ _ R); exact Lj']).
    destruct (smaller x1 t v (heap_get x1 j1)).
    { cbn [fst snd]. split; [reflexivity|]. split; [exact R|]. split; [lia|]. split; reflexivity. }
    pose proof (HR2_heap_set V D x1 x2 k (heap_get x1 j1) R ltac:(lia) (hr_heapV _ _ _ _ R j1 Lj')) as R1.
    specialize (IH V D (heap_set x1 k (heap_get x1 j1)) (heap_set x2 k (heap_get x1 j1)) v j1 (Z.shiftl j1 1) R1 Hv
                   ltac:(lia) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)).
    rewrite !hs_heap_len, !hs_heap_max in IH. specialize (IH Hhl).
    destruct IH as (I1 & I2 & I3 & I4 & I5).
    split; [exact I1|]. split; [exact I2|].
    split; [lia|]. split; [exact I4 | exact I5].
Qed.

Lemma pqdownheap_rel V D x1 x2 k :
  HR2 V D x1 x2 -> 1 <= k <= ds_heap_len x1 -> ds_heap_len x1 <= 572 ->
  HR2 V D (pqdownheap x1 t k) (pqdownheap x2 t k)
  /\ ds_heap_len (pqdownheap x1 t k) = ds_heap_len x1 /\ ds_heap_max (pqdownheap x1 t k) = ds_heap_max x1.
Proof.
  intros R Hk Hhl. unfold pqdownheap.
  assert (Lk : live (ds_heap_len x1) (ds_heap_max x1) k) by (unfold live; lia).
  rewrite (hr_heap _ _ _ _ R k Lk).
  pose proof (pqdownheap_loop_rel 32 V D x1 x2 (heap_get x1 k) k (Z.shiftl k 1) R (hr_heapV _ _ _ _ R k Lk)
                ltac:(lia) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) Hhl) as (I1 & I2 & I3 & I4 & I5).
  destruct (pqdownheap_loop 32 x1 t (heap_get x1 k) k (Z.shiftl k 1)) as [y1 k1].
  destruct (pqdownheap_loop 32 x2 t (heap_get x1 k) k (Z.shiftl k 1)) as [y2 k2].
  cbn [fst snd] in I1, I2, I3, I4, I5. subst k2.
  split; [| unfold heap_set; dsred; split; [exact I4 | exact I5]].
  apply HR2_heap_set; [exact I2 | lia | exact (hr_heapV _ _ _ _ R k Lk)].
Qed.

Lemma pqdownheap_loop_out_cells : forall f x v k j,
  1 <= k -> j = 2 * k ->
  (forall i, ~ (1 <= i <= ds_heap_len x) -> heap_get (fst (pqdownheap_loop f x t v k j)) i = heap_get x i)
  /\ 1 <= snd (pqdownheap_loop f x t v k j) <= Z.max k (ds_heap_len x).
Proof.
  induction f as [|f IH]; intros x v k j Hk Hj; [cbn [pqdownheap_loop fst snd]; split; [intros; reflexivity | lia]|].
  rewrite pqdownheap_loop_S. destruct (Z.leb_spec j (ds_heap_len x)) as [Cj|Cj]; [| cbn [fst snd]; split; [intros; reflexivity | lia]]. cbv zeta.
  set (j1 := if _ && _ then j + 1 else j).
  assert (Hj1 : j <= j1 <= j + 1 /\ j1 <= ds_heap_len x) by (subst j1; destruct (Z.ltb_spec j (ds_heap_len x)); cbn [andb]; [destruct (smaller _ _ _ _)|]; lia). clearbody j1.
  destruct (smaller x t v (heap_get x j1)); [cbn [fst snd]; split; [intros; reflexivity | lia]|].
  destruct (IH (heap_set x k (heap_get x j1)) v j1 (Z.shiftl j1 1) ltac:(lia) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)) as [O K].
  rewrite hs_heap_len in O, K. split; [| lia].
  intros i Hi. rewrite (O i Hi).
  unfold heap_get, heap_set. dsred. rewrite arr_get_set. destruct (Z.eqb_spec k i) as [<-|N]; [exfalso; lia|]. reflexivity.
Qed.
Lemma pqdownheap_out_cells : forall x k i,
  1 <= k <= ds_heap_len x -> ~ (1 <= i <= ds_heap_len x) -> arr_get (ds_heap (pqdownheap x t k)) i = arr_get (ds_heap x) i.
Proof.
  intros x k i Hk Hi. unfold pqdownheap.
  destruct (pqdownheap_loop_out_cells 32 x (heap_get x k) k (Z.shiftl k 1) ltac:(lia) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)) as [O K].
  destruct (pqdownheap_loop 32 x t (heap_get x k) k (Z.shiftl k 1)) as [y k'] eqn:EL. cbn [fst snd] in O, K.
  unfold heap_get in O |- *. unfold heap_set. dsred. rewrite arr_get_set. destruct (Z.eqb_spec k' i) as [<-|N]; [exfalso; lia | exact (O i Hi)].
Qed.


Section Flat.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Hypothesis TL1 : tree_lens s1.
Hypothesis TL2 : tree_lens s2.
Local Notation U1 := (bt_upd s1 t).
Local Notation U2 := (bt_upd s2 t).

Lemma HR2_U V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 :
  arr_len HP1 = 573 -> arr_len HP2 = 573 -> arr_len DP1 = 573 -> arr_len BC1 = 16 -> arr_len BC2 = 16 ->
  AG (fun i => 0 <= i < E \/ V i) FC1 FC2 -> arr_len FC1 = TS -> AG D DL1 DL2 -> arr_len DL1 = TS -> AG V DP1 DP2 ->
  (forall j, live HL HM j -> arr_get HP2 j = arr_get HP1 j /\ V (arr_get HP1 j)) ->
  (forall u, V u -> 0 <= u < TS) ->
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2).
Proof.
  intros LHP1 LHP2 LDP1 LBC1 LBC2 AFC LFC ADL LDL ADP HH HV.
  pose proof (AG_len _ _ _ AFC) as LFC2. pose proof (AG_len _ _ _ ADL) as LDL2. pose proof (AG_len _ _ _ ADP) as LDP2.
  constructor; autorewrite with btupd; try assumption; try reflexivity.
  - apply bt_tree_lens; try assumption; lia.
  - apply bt_tree_lens; try assumption; lia.
  - intros j Hj. unfold heap_get. autorewrite with btupd. exact (HH j Hj).
Qed.

Lemma HR2_ext V V' D D' x1 x2 :
  HR2 V D x1 x2 -> (forall u, V u <-> V' u) -> (forall u, D u <-> D' u) -> HR2 V' D' x1 x2.
Proof.
  intros R HV HD. destruct R as [T1 T2 F DL DP HL HM HP RV OL SL]. constructor; try assumption.
  - eapply AG_mono; [exact F|]. intros i [Hi|Hi]; [left; exact Hi | right; apply HV; exact Hi].
  - eapply AG_mono; [exact DL|]. intros i Hi; apply HD; exact Hi.
  - eapply AG_mono; [exact DP|]. intros i Hi; apply HV; exact Hi.
  - intros j Hj. destruct (HP j Hj) as [A B]. split; [exact A | apply HV; exact B].
  - intros u Hu. apply RV. apply HV. exact Hu.
Qed.

Section UFacts.
  Variable V : Z -> Prop.
Variable D : Z -> Prop.
Variable FC1 : arr.
Variable DL1 : arr.
Variable HP1 : arr.
Variable DP1 : arr.
Variable BC1 : arr.
Variable FC2 : arr.
Variable DL2 : arr.
Variable HP2 : arr.
Variable DP2 : arr.
Variable BC2 : arr.
Variable HL : Z.
Variable HM : Z.
Variable OL : Z.
Variable SL : Z.
Variable MC1 : Z.
Variable MC2 : Z.
  Hypothesis R : HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2).
  Lemma hu_fc : AG (fun i => 0 <= i < E \/ V i) FC1 FC2.
  Proof. pose proof (h_fc _ _ _ _ R) as X. autorewrite with btupd in X. exact X. Qed.
  Lemma hu_dl : AG D DL1 DL2.
  Proof. pose proof (h_dl _ _ _ _ R) as X. autorewrite with btupd in X. exact X. Qed.
  Lemma hu_dp : AG V DP1 DP2.
  Proof. pose proof (h_dp _ _ _ _ R) as X. autorewrite with btupd in X. exact X. Qed.
  Lemma hu_hp : forall j, live HL HM j -> arr_get HP2 j = arr_get HP1 j /\ V (arr_get HP1 j).
  Proof. pose proof (h_hp _ _ _ _ R) as X. unfold heap_get in X. autorewrite with btupd in X. exact X. Qed.
  Lemma hu_V : forall u, V u -> 0 <= u < TS.
  Proof. exact (h_V _ _ _ _ R). Qed.
  Lemma hu_lens : arr_len FC1 = TS /\ arr_len FC2 = TS /\ arr_len DL1 = TS /\ arr_len DL2 = TS
                  /\ arr_len HP1 = 573 /\ arr_len HP2 = 573 /\ arr_len DP1 = 573 /\ arr_len DP2 = 573
                  /\ arr_len BC1 = 16 /\ arr_len BC2 = 16.
  Proof.
    pose proof (h_l1 _ _ _ _ R) as A. pose proof (h_l2 _ _ _ _ R) as B.
    pose proof (tree_lens_fc _ t A) as A1. pose proof (tree_lens_dl _ t A) as A2.
    pose proof (tree_lens_fc _ t B) as B1. pose proof (tree_lens_dl _ t B) as B2.
    autorewrite with btupd in A1. autorewrite with btupd in A2. autorewrite with btupd in B1. autorewrite with btupd in B2.
    unfold tree_lens in A, B. destruct t; cbn [bt_upd] in A, B; dsred; repeat split; try assumption; tauto.
  Qed.
End UFacts.

Lemma HR2_U_mc V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 MC1' MC2' :
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) ->
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1') (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2').
Proof.
  intros R. pose proof (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
  apply HR2_U; try assumption.
  - exact (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_dl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_dp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
Qed.

Lemma pqdownheap_relU V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 k :
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) ->
  1 <= k <= HL -> HL <= 572 ->
  exists HP1' HP2',
    pqdownheap (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) t k = U1 FC1 DL1 HP1' HL HM DP1 BC1 OL SL MC1
    /\ pqdownheap (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) t k = U2 FC2 DL2 HP2' HL HM DP2 BC2 OL SL MC2
    /\ HR2 V D (U1 FC1 DL1 HP1' HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2' HL HM DP2 BC2 OL SL MC2)
    /\ (forall i, ~ (1 <= i <= HL) -> arr_get HP1' i = arr_get HP1 i)
    /\ arr_len HP1' = 573.
Proof.
  intros R Hk Hhl.
  set (X1 := U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) in *. set (X2 := U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) in *.
  assert (EL1 : ds_heap_len X1 = HL) by (subst X1; apply bt_heap_len).
  assert (EH1 : ds_heap X1 = HP1) by (subst X1; apply bt_heap).
  destruct (pqdownheap_rel V D X1 X2 k R ltac:(rewrite EL1; exact Hk) ltac:(rewrite EL1; exact Hhl)) as (R' & _ & _).
  pose proof (pqdownheap_out_cells X1 k) as O. rewrite EL1, EH1 in O.
  pose proof (pqdownheap_len X1 t k) as L. rewrite EH1 in L.
  assert (E1 : pqdownheap X1 t k = U1 FC1 DL1 (ds_heap (pqdownheap X1 t k)) HL HM DP1 BC1 OL SL MC1).
  { rewrite (pqdownheap_shape X1 t k) at 1. subst X1. rewrite bt_set_heap. reflexivity. }
  assert (E2 : pqdownheap X2 t k = U2 FC2 DL2 (ds_heap (pqdownheap X2 t k)) HL HM DP2 BC2 OL SL MC2).
  { rewrite (pqdownheap_shape X2 t k) at 1. subst X2. rewrite bt_set_heap. reflexivity. }
  exists (ds_heap (pqdownheap X1 t k)), (ds_heap (pqdownheap X2 t k)).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite <- E1, <- E2; exact R'|].
  split; [intros i Hi; apply O; [exact Hk | exact Hi]|].
  rewrite L. subst X1 X2. exact (proj1 (proj2 (proj2 (proj2 (proj2 (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R)))))).
Qed.

Lemma loop3_relU : forall f n V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2,
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) ->
  0 <= n <= HL -> HL <= 572 ->
  exists HP1' HP2',
    build_tree_loop3 f (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) t n = U1 FC1 DL1 HP1' HL HM DP1 BC1 OL SL MC1
    /\ build_tree_loop3 f (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) t n = U2 FC2 DL2 HP2' HL HM DP2 BC2 OL SL MC2
    /\ HR2 V D (U1 FC1 DL1 HP1' HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2' HL HM DP2 BC2 OL SL MC2)
    /\ (forall i, ~ (1 <= i <= HL) -> arr_get HP1' i = arr_get HP1 i).
Proof.
  induction f as [|f IH]; intros n V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 R Hn Hhl.
  - exists HP1, HP2. cbn [build_tree_loop3]. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. intros; reflexivity.
  - cbn [build_tree_loop3]. destruct (Z.leb_spec 1 n) as [C|C].
    + destruct (pqdownheap_relU V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 n R ltac:(lia) Hhl)
        as (HP1a & HP2a & E1 & E2 & Ra & Oa & La).
      rewrite E1, E2.
      destruct (IH (n - 1) V D FC1 DL1 HP1a DP1 BC1 FC2 DL2 HP2a DP2 BC2 HL HM OL SL MC1 MC2 Ra ltac:(lia) Hhl)
        as (HP1b & HP2b & E1b & E2b & Rb & Ob).
      exists HP1b, HP2b. split; [exact E1b|]. split; [exact E2b|]. split; [exact Rb|].
      intros i Hi. rewrite (Ob i Hi). apply Oa. exact Hi.
    + exists HP1, HP2. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. intros; reflexivity.
Qed.

Lemma loop1_relU : forall f n mc V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL OL SL MC1 MC2,
  HR2 V D (U1 FC1 DL1 HP1 HL 573 DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL 573 DP2 BC2 OL SL MC2) ->
  Z.of_nat f = E - n -> 0 <= n <= E -> 0 <= HL <= n -> -1 <= mc < E ->
  exists DL1' HP1' DP1' DL2' HP2' DP2' HL' mc',
    build_tree_loop1 f (U1 FC1 DL1 HP1 HL 573 DP1 BC1 OL SL MC1) t E n mc = (U1 FC1 DL1' HP1' HL' 573 DP1' BC1 OL SL MC1, mc')
    /\ build_tree_loop1 f (U2 FC2 DL2 HP2 HL 573 DP2 BC2 OL SL MC2) t E n mc = (U2 FC2 DL2' HP2' HL' 573 DP2' BC2 OL SL MC2, mc')
    /\ HR2 (fun u => V u \/ (n <= u < E /\ arr_get FC1 u <> 0)) (fun u => D u \/ (n <= u < E /\ arr_get FC1 u = 0))
           (U1 FC1 DL1' HP1' HL' 573 DP1' BC1 OL SL MC1) (U2 FC2 DL2' HP2' HL' 573 DP2' BC2 OL SL MC2)
    /\ HL <= HL' <= HL + (E - n) /\ -1 <= mc' < E.
Proof.
  induction f as [|f IH]; intros n mc V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL OL SL MC1 MC2 R Hf Hn HHL Hmc.
  - exists DL1, HP1, DP1, DL2, HP2, DP2, HL, mc. cbn [build_tree_loop1].
    split; [reflexivity|]. split; [reflexivity|]. split; [| lia].
    apply (HR2_ext _ _ _ _ _ _ R); intros u; split; intros X;
      first [left; exact X | destruct X as [X|[X1 X2]]; [exact X | exfalso; lia]].
  - pose proof (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
    pose proof E_TS as HE.
    rewrite !loop1_step. destruct (Z.ltb_spec n E) as [Cn|Cn]; [|lia].
    rewrite <- (AG_get _ _ _ n (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R)) by (left; lia).
    destruct (Z.eqb_spec (arr_get FC1 n) 0) as [Z0|Z0]; cbn [negb].
    +
      assert (R1 : HR2 V (fun u => D u \/ u = n)
                     (U1 FC1 (arr_set DL1 n (wrap16 0)) HP1 HL 573 DP1 BC1 OL SL MC1)
                     (U2 FC2 (arr_set DL2 n (wrap16 0)) HP2 HL 573 DP2 BC2 OL SL MC2)).
      { apply HR2_U; try assumption; try (rewrite arr_len_set; assumption).
        - exact (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - apply AG_set_ext; [exact (hu_dl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) | lia].
        - exact (hu_dp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R). }
      destruct (IH (n + 1) mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (DL1' & HP1' & DP1' & DL2' & HP2' & DP2' & HL' & mc' & E1 & E2 & R' & B').
      exists DL1', HP1', DP1', DL2', HP2', DP2', HL', mc'. split; [exact E1|]. split; [exact E2|]. split; [| lia].
      apply (HR2_ext _ _ _ _ _ _ R'); intros u; split; intros X.
      * destruct X as [X|[X1 X2]]; [left; exact X | right; split; [lia | exact X2]].
      * destruct X as [X|[X1 X2]]; [left; exact X|]. right. destruct (Z.eq_dec u n) as [->|N]; [exfalso; exact (X2 Z0) | split; [lia | exact X2]].
      * destruct X as [[X| ->]|[X1 X2]]; [left; exact X | right; split; [lia | exact Z0] | right; split; [lia | exact X2]].
      * destruct X as [X|[X1 X2]]; [left; left; exact X|]. destruct (Z.eq_dec u n) as [->|N]; [left; right; reflexivity | right; split; [lia | exact X2]].
    +
      assert (R1 : HR2 (fun u => V u \/ u = n) D
                     (U1 FC1 DL1 (arr_set HP1 (HL + 1) n) (HL + 1) 573 (arr_set DP1 n (wrap8 0)) BC1 OL SL MC1)
                     (U2 FC2 DL2 (arr_set HP2 (HL + 1) n) (HL + 1) 573 (arr_set DP2 n (wrap8 0)) BC2 OL SL MC2)).
      { apply HR2_U; try assumption; try (rewrite arr_len_set; assumption).
        - eapply AG_mono; [exact (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R)|]. intros i [X|[X| ->]]; [left; exact X | right; exact X | left; lia].
        - exact (hu_dl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - apply AG_set_ext; [exact (hu_dp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) | lia].
        - intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite LHP1, LHP2.
          destruct (Z.eqb_spec (HL + 1) j) as [<-|N]; cbn [andb].
          + replace ((0 <=? HL + 1) && (HL + 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
            split; [reflexivity | right; reflexivity].
          + destruct (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R j ltac:(unfold live in *; lia)) as [A B]. split; [exact A | left; exact B].
        - intros u [X| ->]; [exact (hu_V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R u X) | lia]. }
      destruct (IH (n + 1) n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (DL1' & HP1' & DP1' & DL2' & HP2' & DP2' & HL' & mc' & E1 & E2 & R' & B').
      exists DL1', HP1', DP1', DL2', HP2', DP2', HL', mc'. split; [exact E1|]. split; [exact E2|]. split; [| lia].
      apply (HR2_ext _ _ _ _ _ _ R'); intros u; split; intros X.
      * destruct X as [[X| ->]|[X1 X2]]; [left; exact X | right; split; [lia | exact Z0] | right; split; [lia | exact X2]].
      * destruct X as [X|[X1 X2]]; [left; left; exact X|]. destruct (Z.eq_dec u n) as [->|N]; [left; right; reflexivity | right; split; [lia | exact X2]].
      * destruct X as [X|[X1 X2]]; [left; exact X | right; split; [lia | exact X2]].
      * destruct X as [X|[X1 X2]]; [left; exact X|]. right. destruct (Z.eq_dec u n) as [->|N]; [exfalso; exact (Z0 X2) | split; [lia | exact X2]].
Qed.

Lemma loop2_relU : forall f mc V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL OL SL MC1 MC2,
  HR2 V D (U1 FC1 DL1 HP1 HL 573 DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL 573 DP2 BC2 OL SL MC2) ->
  0 <= HL <= E -> -1 <= mc < E ->
  exists FC1' HP1' DP1' FC2' HP2' DP2' HL' OL' SL' mc' (V' : Z -> Prop),
    build_tree_loop2 f (U1 FC1 DL1 HP1 HL 573 DP1 BC1 OL SL MC1) t mc = (U1 FC1' DL1 HP1' HL' 573 DP1' BC1 OL' SL' MC1, mc')
    /\ build_tree_loop2 f (U2 FC2 DL2 HP2 HL 573 DP2 BC2 OL SL MC2) t mc = (U2 FC2' DL2 HP2' HL' 573 DP2' BC2 OL' SL' MC2, mc')
    /\ HR2 V' D (U1 FC1' DL1 HP1' HL' 573 DP1' BC1 OL' SL' MC1) (U2 FC2' DL2 HP2' HL' 573 DP2' BC2 OL' SL' MC2)
    /\ (forall u, V u -> V' u) /\ (forall u, V' u -> V u \/ 0 <= u < E)
    /\ HL <= HL' <= HL + Z.of_nat f /\ (forall i, E <= i -> arr_get FC1' i = arr_get FC1 i).
Proof.
  induction f as [|f IH]; intros mc V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL OL SL MC1 MC2 R HHL Hmc.
  - exists FC1, HP1, DP1, FC2, HP2, DP2, HL, OL, SL, mc, V. cbn [build_tree_loop2].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [intros u Hu; exact Hu|]. split; [intros u Hu; left; exact Hu|].
    split; [lia|]. intros; reflexivity.
  - pose proof (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
    pose proof E_TS as HE.
    rewrite !loop2_step. destruct (Z.ltb_spec HL 2) as [C|C].
    2:{ exists FC1, HP1, DP1, FC2, HP2, DP2, HL, OL, SL, mc, V.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [intros u Hu; exact Hu|]. split; [intros u Hu; left; exact Hu|].
        split; [lia|]. intros; reflexivity. }
    cbv zeta.
    set (node := if mc <? 2 then mc + 1 else 0). set (mc' := if mc <? 2 then mc + 1 else mc).
    assert (Hnode : 0 <= node < E /\ -1 <= mc' < E /\ node <= 2) by (subst node mc'; destruct (Z.ltb_spec mc 2); lia).
    clearbody node mc'.
    set (SL' := if stree_has t then wrap64 (SL - stree_Len t node) else SL). clearbody SL'.
    assert (R1 : HR2 (fun u => V u \/ u = node) D
                   (U1 (arr_set FC1 node (wrap16 1)) DL1 (arr_set HP1 (HL + 1) node) (HL + 1) 573 (arr_set DP1 node (wrap8 0)) BC1 (wrap64 (OL - 1)) SL' MC1)
                   (U2 (arr_set FC2 node (wrap16 1)) DL2 (arr_set HP2 (HL + 1) node) (HL + 1) 573 (arr_set DP2 node (wrap8 0)) BC2 (wrap64 (OL - 1)) SL' MC2)).
    { apply HR2_U; try assumption; try (rewrite arr_len_set; assumption).
      - eapply AG_mono; [apply AG_set; exact (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R)|]. intros i [X|[X| ->]]; [left; exact X | right; exact X | left; lia].
      - exact (hu_dl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
      - apply AG_set_ext; [exact (hu_dp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) | lia].
      - intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite LHP1, LHP2.
        destruct (Z.eqb_spec (HL + 1) j) as [<-|N]; cbn [andb].
        + replace ((0 <=? HL + 1) && (HL + 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          split; [reflexivity | right; reflexivity].
        + destruct (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R j ltac:(unfold live in *; lia)) as [A B]. split; [exact A | left; exact B].
      - intros u [X| ->]; [exact (hu_V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R u X) | lia]. }
    destruct (IH mc' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 ltac:(lia) ltac:(lia))
      as (FC1' & HP1' & DP1' & FC2' & HP2' & DP2' & HL' & OL' & SL'' & mc'' & V' & E1 & E2 & R' & V1 & V2 & B' & FE).
    exists FC1', HP1', DP1', FC2', HP2', DP2', HL', OL', SL'', mc'', V'.
    split; [exact E1|]. split; [exact E2|]. split; [exact R'|].
    split; [intros u Hu; apply V1; left; exact Hu|].
    split; [intros u Hu; destruct (V2 u Hu) as [[X| ->]|X]; [left; exact X | right; lia | right; exact X]|].
    split; [lia|].
    intros i Hi. rewrite (FE i Hi). rewrite arr_get_set. destruct (Z.eqb_spec node i); [lia | reflexivity].
Qed.


Lemma loop4_step_relU V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HM OL SL MC1 MC2 node :
  HR2 V D (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) ->
  2 <= HL -> HL + 2 <= HM -> HM <= 573 -> E <= node -> node + 1 < TS ->
  (forall i, HM <= i < 573 -> D (arr_get HP1 i)) ->
  exists FC1' DL1' HP1' DP1' FC2' DL2' HP2' DP2' n m,
    V n /\ V m
    /\ (forall f, build_tree_loop4 (S f) (U1 FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC1) t node
         = let s4 := U1 FC1' DL1' HP1' (HL - 1) (HM - 2) DP1' BC1 OL SL MC1 in
           if 2 <=? HL - 1 then build_tree_loop4 f s4 t (node + 1) else s4)
    /\ (forall f, build_tree_loop4 (S f) (U2 FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC2) t node
         = let s4 := U2 FC2' DL2' HP2' (HL - 1) (HM - 2) DP2' BC2 OL SL MC2 in
           if 2 <=? HL - 1 then build_tree_loop4 f s4 t (node + 1) else s4)
    /\ HR2 (fun u => V u \/ u = node) (fun u => D u \/ u = m \/ u = n)
           (U1 FC1' DL1' HP1' (HL - 1) (HM - 2) DP1' BC1 OL SL MC1) (U2 FC2' DL2' HP2' (HL - 1) (HM - 2) DP2' BC2 OL SL MC2)
    /\ (forall i, HM - 2 <= i < 573 -> D (arr_get HP1' i) \/ arr_get HP1' i = m \/ arr_get HP1' i = n)
    /\ (forall i, 0 <= i < E -> arr_get FC1' i = arr_get FC1 i).
Proof.
  intros R HHL HHM H573 Hn1 Hn2 TD.
  pose proof (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
  pose proof E_TS as HE.
  pose proof (hu_fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
  pose proof (hu_dp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADP. pose proof (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
  pose proof (hu_V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as HV.
  set (n := arr_get HP1 1).
  destruct (AHP 1 ltac:(unfold live; lia)) as [E2n Vn]. fold n in E2n, Vn.
  destruct (AHP HL ltac:(unfold live; lia)) as [E2l Vl].
  set (HPa1 := arr_set HP1 1 (arr_get HP1 HL)). set (HPa2 := arr_set HP2 1 (arr_get HP1 HL)).
  assert (Ra : HR2 V D (U1 FC1 DL1 HPa1 (HL - 1) HM DP1 BC1 OL SL MC1) (U2 FC2 DL2 HPa2 (HL - 1) HM DP2 BC2 OL SL MC2)).
  { apply HR2_U; try assumption; try (subst HPa1 HPa2; rewrite arr_len_set; assumption).
    intros j Hj. subst HPa1 HPa2. rewrite !arr_get_set. unfold arr_inb. rewrite LHP1, LHP2.
    destruct (Z.eqb_spec 1 j) as [<-|N]; cbn [andb]; [split; [reflexivity | exact Vl]|].
    apply AHP. unfold live in *; lia. }
  destruct (pqdownheap_relU V D FC1 DL1 HPa1 DP1 BC1 FC2 DL2 HPa2 DP2 BC2 (HL - 1) HM OL SL MC1 MC2 1 Ra ltac:(lia) ltac:(lia))
    as (HPb1 & HPb2 & Eb1 & Eb2 & Rb & Ob & Lb).
  pose proof (hu_hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rb) as AHPb.
  set (m := arr_get HPb1 1).
  destruct (AHPb 1 ltac:(unfold live; lia)) as [E2m Vm]. fold m in E2m, Vm.
  pose proof (hu_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rb) as (_ & _ & _ & _ & _ & LHPb2 & _).
  set (fq := arr_get FC1 n + arr_get FC1 m).
  set (dq := (if arr_get DP1 m <=? arr_get DP1 n then arr_get DP1 n else arr_get DP1 m) + 1).
  assert (Efq : arr_get FC2 n + arr_get FC2 m = fq) by (subst fq; rewrite <- !(AG_get _ _ _ _ AFC) by (right; assumption); reflexivity).
  assert (Edq : (if arr_get DP2 m <=? arr_get DP2 n then arr_get DP2 n else arr_get DP2 m) + 1 = dq)
    by (subst dq; rewrite <- !(AG_get _ _ _ _ ADP) by assumption; reflexivity).
  set (FC1' := arr_set FC1 node (wrap16 fq)). set (FC2' := arr_set FC2 node (wrap16 fq)).
  set (DL1' := arr_set (arr_set DL1 m (wrap16 node)) n (wrap16 node)). set (DL2' := arr_set (arr_set DL2 m (wrap16 node)) n (wrap16 node)).
  set (DP1' := arr_set DP1 node (wrap8 dq)). set (DP2' := arr_set DP2 node (wrap8 dq)).
  set (HPc1 := arr_set (arr_set (arr_set HPb1 (HM - 1) n) (HM - 2) m) 1 node).
  set (HPc2 := arr_set (arr_set (arr_set HPb2 (HM - 1) n) (HM - 2) m) 1 node).
  pose proof (HV n Vn) as Rn. pose proof (HV m Vm) as Rm.
  assert (Rc : HR2 (fun u => V u \/ u = node) (fun u => D u \/ u = m \/ u = n)
                 (U1 FC1' DL1' HPc1 (HL - 1) (HM - 2) DP1' BC1 OL SL MC1) (U2 FC2' DL2' HPc2 (HL - 1) (HM - 2) DP2' BC2 OL SL MC2)).
  { apply HR2_U; try assumption; try (subst FC1' FC2' DL1' DL2' DP1' DP2' HPc1 HPc2; rewrite !arr_len_set; first [assumption | lia]).
    - subst FC1' FC2'. eapply AG_mono; [apply AG_set_ext; [exact AFC | lia]|].
      intros i [X|[X| ->]]; [left; left; exact X | left; right; exact X | right; reflexivity].
    - subst DL1' DL2'. eapply AG_mono; [apply AG_set_ext; [apply AG_set_ext; [exact ADL | lia] | rewrite arr_len_set; lia]|].
      intros i [X|[-> | ->]]; [left; left; exact X | left; right; reflexivity | right; reflexivity].
    - subst DP1' DP2'. apply AG_set_ext; [exact ADP | lia].
    - intros j Hj. subst HPc1 HPc2. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Lb, LHPb2.
      destruct (Z.eqb_spec 1 j) as [<-|N1]; cbn [andb].
      { replace ((0 <=? 1) && (1 <? 573)) with true by reflexivity. split; [reflexivity | right; reflexivity]. }
      destruct (Z.eqb_spec (HM - 2) j) as [<-|N2]; cbn [andb].
      { replace ((0 <=? HM - 2) && (HM - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        split; [reflexivity | left; exact Vm]. }
      destruct (Z.eqb_spec (HM - 1) j) as [<-|N3]; cbn [andb].
      { replace ((0 <=? HM - 1) && (HM - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        split; [reflexivity | left; exact Vn]. }
      destruct (AHPb j ltac:(unfold live in *; lia)) as [A B]. split; [exact A | left; exact B].
    - intros u [X| ->]; [exact (HV u X) | lia]. }
  assert (LHPc1 : arr_len HPc1 = 573) by (subst HPc1; rewrite !arr_len_set; exact Lb).
  destruct (pqdownheap_relU _ _ FC1' DL1' HPc1 DP1' BC1 FC2' DL2' HPc2 DP2' BC2 (HL - 1) (HM - 2) OL SL MC1 MC2 1 Rc ltac:(lia) ltac:(lia))
    as (HPd1 & HPd2 & Ed1 & Ed2 & Rd & Od & Ld).
  exists FC1', DL1', HPd1, DP1', FC2', DL2', HPd2, DP2', n, m.
  split; [exact Vn|]. split; [exact Vm|].
  split.
  { intros f. rewrite loop4_unfold. unfold SMALLEST. cbv zeta. autorewrite with btupd.
    fold n. fold HPa1. rewrite Eb1. autorewrite with btupd. fold m.
    replace (HM - 1 - 1) with (HM - 2) by lia.
    fold fq. fold FC1'. fold dq. fold DP1'. fold DL1'. fold HPc1.
    rewrite Ed1. autorewrite with btupd. reflexivity. }
  split.
  { intros f. rewrite loop4_unfold. unfold SMALLEST. cbv zeta. autorewrite with btupd.
    rewrite E2n, E2l. fold HPa2. rewrite Eb2. autorewrite with btupd. rewrite E2m.
    replace (HM - 1 - 1) with (HM - 2) by lia.
    rewrite Efq, Edq. fold FC2'. fold DP2'. fold DL2'. fold HPc2.
    rewrite Ed2. autorewrite with btupd. reflexivity. }
  split; [exact Rd|].
  split.
  { intros i Hi. rewrite (Od i) by lia. subst HPc1. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, Lb.
    destruct (Z.eqb_spec 1 i) as [<-|N1]; [exfalso; lia|]. cbn [andb].
    destruct (Z.eqb_spec (HM - 2) i) as [<-|N2]; cbn [andb].
    { replace ((0 <=? HM - 2) && (HM - 2 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). right; left; reflexivity. }
    destruct (Z.eqb_spec (HM - 1) i) as [<-|N3]; cbn [andb].
    { replace ((0 <=? HM - 1) && (HM - 1 <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). right; right; reflexivity. }
    left. rewrite (Ob i) by lia. subst HPa1. rewrite arr_get_set. destruct (Z.eqb_spec 1 i); [exfalso; lia|]. cbn [andb]. apply TD. lia. }
  intros i Hi. subst FC1'. rewrite arr_get_set. destruct (Z.eqb_spec node i); [exfalso; lia | reflexivity].
Qed.

Lemma loop4_relU : forall f j L V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 OL SL MC1 MC2,
  HR2 V D (U1 FC1 DL1 HP1 (L - j) (573 - 2 * j) DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 (L - j) (573 - 2 * j) DP2 BC2 OL SL MC2) ->
  2 <= L <= E -> 0 <= j <= L - 2 -> (Z.of_nat f >= L - j - 1) ->
  (forall i, 573 - 2 * j <= i < 573 -> D (arr_get HP1 i)) ->
  exists FC1' DL1' HP1' DP1' FC2' DL2' HP2' DP2' (V' D' : Z -> Prop),
    build_tree_loop4 f (U1 FC1 DL1 HP1 (L - j) (573 - 2 * j) DP1 BC1 OL SL MC1) t (E + j) = U1 FC1' DL1' HP1' 1 (573 - 2 * (L - 1)) DP1' BC1 OL SL MC1
    /\ build_tree_loop4 f (U2 FC2 DL2 HP2 (L - j) (573 - 2 * j) DP2 BC2 OL SL MC2) t (E + j) = U2 FC2' DL2' HP2' 1 (573 - 2 * (L - 1)) DP2' BC2 OL SL MC2
    /\ HR2 V' D' (U1 FC1' DL1' HP1' 1 (573 - 2 * (L - 1)) DP1' BC1 OL SL MC1) (U2 FC2' DL2' HP2' 1 (573 - 2 * (L - 1)) DP2' BC2 OL SL MC2)
    /\ (forall i, 573 - 2 * (L - 1) <= i < 573 -> D' (arr_get HP1' i))
    /\ (forall u, V u -> V' u) /\ (forall u, D u -> D' u) /\ (forall u, V' u -> V u \/ E <= u)
    /\ (forall i, 0 <= i < E -> arr_get FC1' i = arr_get FC1 i).
Proof.
  induction f as [|f IH]; intros j L V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 OL SL MC1 MC2 R HL Hj Hf TD; [lia|].
  pose proof E_TS as HE.
  destruct (loop4_step_relU V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 (L - j) (573 - 2 * j) OL SL MC1 MC2 (E + j) R
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) TD)
    as (FC1a & DL1a & HP1a & DP1a & FC2a & DL2a & HP2a & DP2a & n & m & Vn & Vm & EQ1 & EQ2 & Ra & TDa & FE).
  rewrite (EQ1 f), (EQ2 f). cbv zeta.
  destruct (Z.leb_spec 2 (L - j - 1)) as [C|C].
  - replace (L - j - 1) with (L - (j + 1)) in Ra |- * by lia.
    replace (573 - 2 * j - 2) with (573 - 2 * (j + 1)) in Ra, TDa |- * by lia.
    replace (E + j + 1) with (E + (j + 1)) by lia.
    destruct (IH (j + 1) L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ra ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; exact (TDa i Hi)))
      as (FC1' & DL1' & HP1' & DP1' & FC2' & DL2' & HP2' & DP2' & V' & D' & E1 & E2 & R' & TD' & HV1 & HD1 & HV2 & FE').
    exists FC1', DL1', HP1', DP1', FC2', DL2', HP2', DP2', V', D'.
    split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. split; [exact TD'|].
    split; [intros u Hu; apply HV1; left; exact Hu|].
    split; [intros u Hu; apply HD1; left; exact Hu|].
    split; [intros u Hu; destruct (HV2 u Hu) as [[X| ->]|X]; [left; exact X | right; lia | right; exact X]|].
    intros i Hi. rewrite (FE' i Hi). apply FE. exact Hi.
  - exists FC1a, DL1a, HP1a, DP1a, FC2a, DL2a, HP2a, DP2a, (fun u => V u \/ u = E + j), (fun u => D u \/ u = m \/ u = n).
    replace (L - j - 1) with 1 in Ra |- * by lia.
    replace (573 - 2 * j - 2) with (573 - 2 * (L - 1)) in Ra, TDa |- * by lia.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Ra|]. split; [exact TDa|].
    split; [intros u Hu; left; exact Hu|]. split; [intros u Hu; left; exact Hu|].
    split; [intros u [X| ->]; [left; exact X | right; lia]|].
    exact FE.
Qed.

End Flat.
End BT.
End DeflateTaintBT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintTrees.DeflateTaintBT.

Module DeflateTaintBT2.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintTrees.DeflateTaintBT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma AG_set2 P a b i v1 v2 : AG P a b -> (0 <= i < arr_len a -> v1 = v2) -> AG P (arr_set a i v1) (arr_set b i v2).
Proof.
  intros [L H] Hv. split; [rewrite !arr_len_set; exact L|].
  intros j Pj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct (Z.eqb_spec i j) as [<-|NE]; cbn [andb]; [| apply H; exact Pj].
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (arr_len a)); cbn [andb]; try (apply H; exact Pj).
  apply Hv. lia.
Qed.

Section GB.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation TS := (tsize t).
Local Notation ML := (sd_max_length t).
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Hypothesis TL1 : tree_lens s1.
Hypothesis TL2 : tree_lens s2.
Local Notation U1 := (bt_upd s1 t).
Local Notation U2 := (bt_upd s2 t).
Variable FC2r : arr.
Variable DL2r : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Hypothesis HR : heap_result t FC2r DL2r L mc FCf DLf HPf DPf.
Local Notation HM := (RefDeflSafeB3.HM L).

Lemma GB_ranges : 2 <= HM <= 570 /\ 2 <= L <= E /\ 0 <= mc < E /\ 7 <= ML <= 15 /\ 19 <= E <= 286 /\ TS = 2 * E + 1.
Proof.
  pose proof (HM_range t _ _ _ _ _ _ _ _ HR). pose proof (hr_L _ _ _ _ _ _ _ _ _ HR). pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR).
  pose proof (ML_range t _ _ _ _ _ _ _ _ HR). pose proof (E_TS t). lia.
Qed.

Lemma tail_pos : forall u, (E <= u < E + L - 1 \/ (exists p, HM <= p < 573 /\ arr_get HPf p = u)) ->
  exists p, HM <= p < 573 /\ arr_get HPf p = u.
Proof.
  intros u [Hu|Hu]; [| exact Hu].
  destruct (hr_cov _ _ _ _ _ _ _ _ _ HR u ltac:(unfold Vj; right; lia)) as (p & Hp & Ep).
  exists p. unfold RefDeflSafeB3.HM. split; [lia | exact Ep].
Qed.

Variable FCg : arr.
Variable HPg : arr.
Variable DPg : arr.

Lemma HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL DL1' BC1' DL2' BC2' OL' SL' :
  HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
  AG D DL1' DL2' -> arr_len DL1' = TS -> arr_len BC1' = 16 -> arr_len BC2' = 16 ->
  HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc).
Proof.
  intros R ADL LDL LBC1 LBC2.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & _ & _ & LHP1 & LHP2 & LDP1 & LDP2 & _ & _).
  apply (HR2_U t s1 s2 TL1 TL2); try assumption.
  - exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
Qed.


Section Passes.
  Variable V : Z -> Prop.
Variable D : Z -> Prop.
  Hypothesis TD : forall p, HM <= p < 573 -> D (arr_get HPf p).
  Hypothesis DI : forall u, E <= u < E + L - 1 -> D u.

  Lemma tail_live : forall p, HM <= p < 573 -> live 1 HM p.
  Proof. intros p Hp. unfold live. right. exact Hp. Qed.

  Lemma loop1_gb_rel : forall f h ovf DL1 BC1 OL SL DL2 BC2 BC0 OL0 SL0,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    L1I t FC2r L mc FCf DLf HPf DPf s1 BC0 OL0 SL0 h (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) ovf ->
    (Z.of_nat f >= 573 - h) ->
    exists DL1' BC1' OL' SL' DL2' BC2' ovf',
      gen_bitlen_loop1 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc (sd_extra_base t) ML h ovf = (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc, ovf')
      /\ gen_bitlen_loop1 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc (sd_extra_base t) ML h ovf = (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc, ovf')
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)
      /\ AG (fun i => 0 <= i < 16) BC1' BC2'
      /\ L1I t FC2r L mc FCf DLf HPf DPf s1 BC0 OL0 SL0 573 (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) ovf'.
  Proof.
    induction f as [|f IH]; intros h ovf DL1 BC1 OL SL DL2 BC2 BC0 OL0 SL0 R ABC HI Hf.
    - pose proof (l1_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hh.
      exists DL1, BC1, OL, SL, DL2, BC2, ovf. cbn [gen_bitlen_loop1].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [exact ABC|].
      replace 573 with h by lia. exact HI.
    - pose proof (l1_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hh. pose proof GB_ranges as RG.
      rewrite !(GL1_step t mc). unfold HEAP_SIZE.
      destruct (Z.ltb_spec h 573) as [Ch|Ch].
      2:{ exists DL1, BC1, OL, SL, DL2, BC2, ovf. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [exact ABC|].
          replace 573 with h by lia. exact HI. }
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
      pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
      pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
      set (n := arr_get HPf h).
      destruct (AHP h ltac:(apply tail_live; lia)) as [En Vn]. fold n in En.
      destruct (l1_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (DLx & BCx & OLx & SLx & EX & HDL & _).
      pose proof (f_equal (fun x => tree_dl x t) EX) as EDL. cbv beta in EDL. autorewrite with btupd in EDL. subst DLx.
      assert (Edad1 : arr_get DL1 n = E + (572 - h) / 2).
      { rewrite HDL. unfold dl_at. destruct (tid_nd t _ _ _ _ _ _ _ _ HR h ltac:(unfold tail; lia)) as [T P].
        unfold RefDeflSafeB3.nd in T, P. fold n in T, P. rewrite T, P.
        replace (h <? h) with false by (symmetry; apply Z.ltb_irrefl). cbn [andb].
        exact (hr_dad _ _ _ _ _ _ _ _ _ HR h ltac:(unfold RefDeflSafeB3.HM in *; lia)). }
      assert (Hdad : E <= E + (572 - h) / 2 < E + L - 1).
      { split; [pose proof (Z.div_pos (572 - h) 2); lia|].
        assert ((572 - h) / 2 < L - 1) by (apply Z.div_lt_upper_bound; unfold RefDeflSafeB3.HM in *; lia). lia. }
      assert (Edad2 : arr_get DL2 n = arr_get DL1 n) by (symmetry; apply (AG_get _ _ _ _ ADL); apply TD; lia).
      assert (Elen2 : arr_get DL2 (arr_get DL1 n) = arr_get DL1 (arr_get DL1 n)).
      { symmetry. apply (AG_get _ _ _ _ ADL). rewrite Edad1. apply DI. exact Hdad. }
      assert (Efc2 : arr_get FCg n = arr_get FCf n) by (symmetry; apply (AG_get _ _ _ _ AFC); right; exact Vn).
      pose proof (L1_step t _ _ _ _ _ _ _ _ HR s1 BC0 OL0 SL0 h _ ovf HI Ch) as [HI' _].
      rewrite (GB1_flat t mc s1) in HI'. cbv zeta in HI'. rewrite (GB1_flat t mc s1), (GB1_flat t mc s2). cbv zeta.
      rewrite En, Edad2, Elen2, Efc2. fold n in HI' |- *.
      set (bits0 := arr_get DL1 (arr_get DL1 n) + 1) in *.
      set (bits := if ML <? bits0 then ML else bits0) in *.
      set (ovf' := if ML <? bits0 then ovf + 1 else ovf) in *.
      set (DL1' := arr_set DL1 n (wrap16 bits)) in *. set (DL2' := arr_set DL2 n (wrap16 bits)).
      assert (ADL' : AG D DL1' DL2') by (subst DL1' DL2'; apply AG_set; exact ADL).
      assert (LDL1' : arr_len DL1' = TS) by (subst DL1'; rewrite arr_len_set; exact LDL1).
      destruct (Z.ltb_spec mc n) as [Cn|Cn].
      + cbn [fst snd] in HI'.
        assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL SL mc))
          by (apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); assumption).
        destruct (IH (h + 1) ovf' DL1' BC1 OL SL DL2' BC2 BC0 OL0 SL0 R1 ABC HI' ltac:(lia))
          as (DL1f & BC1f & OLf & SLf & DL2f & BC2f & ovff & E1 & E2 & Rf & Af & If).
        exists DL1f, BC1f, OLf, SLf, DL2f, BC2f, ovff. split; [exact E1|]. split; [exact E2|]. split; [exact Rf|]. split; [exact Af | exact If].
      + cbn [fst snd] in HI'.
        set (BC1' := arr_set BC1 bits (wrap16 (arr_get BC1 bits + 1))) in *.
        set (BC2' := arr_set BC2 bits (wrap16 (arr_get BC2 bits + 1))).
        assert (ABC' : AG (fun i => 0 <= i < 16) BC1' BC2').
        { subst BC1' BC2'. apply AG_set2; [exact ABC|]. intros Hb. rewrite (AG_get _ _ _ bits ABC); [reflexivity | rewrite <- LBC1; exact Hb]. }
        set (OL' := wrap64 (OL + arr_get FCf n * (bits + xbits t n))) in *.
        set (SL' := if stree_has t then wrap64 (SL + arr_get FCf n * (stree_Len t n + xbits t n)) else SL) in *.
        assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)).
        { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption; subst BC1' BC2'; rewrite arr_len_set; assumption. }
        destruct (IH (h + 1) ovf' DL1' BC1' OL' SL' DL2' BC2' BC0 OL0 SL0 R1 ABC' HI' ltac:(lia))
          as (DL1f & BC1f & OLf & SLf & DL2f & BC2f & ovff & E1 & E2 & Rf & Af & If).
        exists DL1f, BC1f, OLf, SLf, DL2f, BC2f, ovff. split; [exact E1|]. split; [exact E2|]. split; [exact Rf|]. split; [exact Af | exact If].
  Qed.


  Lemma find_rel : forall f BC1 BC2 DL1 DL2 OL SL b,
    AG (fun i => 0 <= i < 16) BC1 BC2 -> arr_len BC1 = 16 -> b < 16 -> Z.of_nat f <= b + 1 ->
    gen_bitlen_find f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) b = gen_bitlen_find f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) b.
  Proof.
    induction f as [|f IH]; intros BC1 BC2 DL1 DL2 OL SL b ABC LBC Hb Hf; [reflexivity|].
    cbn [gen_bitlen_find]. rewrite !bt_bl_count_get.
    rewrite <- (AG_get _ _ _ b ABC) by lia.
    destruct (arr_get BC1 b =? 0); [| reflexivity]. apply IH; try assumption; lia.
  Qed.

  Lemma loop2_gb_rel : forall f ovf DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    exists BC1' BC2',
      gen_bitlen_loop2 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) ML ovf = U1 FCf DL1 HPf 1 HM DPf BC1' OL SL mc
      /\ gen_bitlen_loop2 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ML ovf = U2 FCg DL2 HPg 1 HM DPg BC2' OL SL mc
      /\ HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1' OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2' OL SL mc)
      /\ AG (fun i => 0 <= i < 16) BC1' BC2'.
  Proof.
    induction f as [|f IH]; intros ovf DL1 BC1 DL2 BC2 OL SL R ABC.
    - exists BC1, BC2. cbn [gen_bitlen_loop2]. split; [reflexivity|]. split; [reflexivity|]. split; [exact R | exact ABC].
    - pose proof GB_ranges as RG.
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (_ & _ & LDL1 & _ & _ & _ & _ & _ & LBC1 & LBC2).
      rewrite (GL2_step t ML f s1), (GL2_step t ML f s2). cbv zeta.
      rewrite (find_rel (Z.to_nat ML) BC1 BC2 DL1 DL2 OL SL (ML - 1) ABC LBC1) by lia.
      set (r := gen_bitlen_find (Z.to_nat ML) (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (ML - 1)). clearbody r.
      assert (ABC' : AG (fun i => 0 <= i < 16) (bl_adj ML BC1 r) (bl_adj ML BC2 r)).
      { unfold bl_adj.
        assert (A1 : AG (fun i => 0 <= i < 16) (arr_set BC1 r (wrap16 (arr_get BC1 r - 1))) (arr_set BC2 r (wrap16 (arr_get BC2 r - 1)))).
        { apply AG_set2; [exact ABC|]. intros Hr. rewrite (AG_get _ _ _ r ABC) by lia. reflexivity. }
        match goal with |- AG _ (arr_set (arr_set ?a1 _ _) _ _) (arr_set (arr_set ?a2 _ _) _ _) =>
          assert (A2 : AG (fun i => 0 <= i < 16) (arr_set a1 (r + 1) (wrap16 (arr_get a1 (r + 1) + 2))) (arr_set a2 (r + 1) (wrap16 (arr_get a2 (r + 1) + 2))));
          [ apply AG_set2; [exact A1|]; intros Hr; rewrite (AG_get _ _ _ (r + 1) A1) by (rewrite arr_len_set in Hr; lia); reflexivity |] end.
        apply AG_set2; [exact A2|]. intros Hr. rewrite (AG_get _ _ _ ML A2) by (rewrite !arr_len_set in Hr; lia). reflexivity. }
      assert (R' : HR2 t V D (U1 FCf DL1 HPf 1 HM DPf (bl_adj ML BC1 r) OL SL mc) (U2 FCg DL2 HPg 1 HM DPg (bl_adj ML BC2 r) OL SL mc)).
      { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption.
        - exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - unfold bl_adj. rewrite !arr_len_set. exact LBC1.
        - unfold bl_adj. rewrite !arr_len_set. exact LBC2. }
      destruct (0 <? ovf - 2).
      + exact (IH (ovf - 2) DL1 _ DL2 _ OL SL R' ABC').
      + exists (bl_adj ML BC1 r), (bl_adj ML BC2 r). split; [reflexivity|]. split; [reflexivity|]. split; [exact R' | exact ABC'].
  Qed.


  Local Notation nleaf := (nleaf t L HPf).

  Lemma loop3i_gb_rel : forall f bits n h DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    (Z.of_nat f >= h - HM) -> HM + 1 <= h <= 573 -> 0 <= n <= nleaf h ->
    exists DL1' OL' DL2' h',
      gen_bitlen_loop3i f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc bits n h = (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc, h')
      /\ gen_bitlen_loop3i f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc bits n h = (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc, h')
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc)
      /\ HM + 1 <= h' <= h /\ nleaf h' = nleaf h - n.
  Proof.
    induction f as [|f IH]; intros bits n h DL1 BC1 DL2 BC2 OL SL R Hf Hh Hn.
    - exists DL1, OL, DL2, h. cbn [gen_bitlen_loop3i].
      assert (n = 0 \/ h = HM) by lia. pose proof (nleaf_base t L HPf) as NB.
      destruct H as [-> | ->]; [| exfalso; lia].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. lia.
    - pose proof GB_ranges as RG.
      rewrite !(GL3i_step t mc). destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
      { exists DL1, OL, DL2, h. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. lia. }
      assert (Hh1 : HM + 1 <= h - 1).
      { destruct (Z_lt_le_dec (HM + 1) h) as [|C0]; [lia|]. exfalso. replace h with (HM + 1) in Hn by lia. rewrite (nleaf_base t L HPf) in Hn. lia. }
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
      pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
      pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
      set (m := arr_get HPf (h - 1)).
      destruct (AHP (h - 1) ltac:(apply tail_live; lia)) as [Em Vm]. fold m in Em.
      assert (Edl : arr_get DL2 m = arr_get DL1 m) by (symmetry; apply (AG_get _ _ _ _ ADL); apply TD; lia).
      assert (Efc : arr_get FCg m = arr_get FCf m) by (symmetry; apply (AG_get _ _ _ _ AFC); right; exact Vm).
      pose proof (nleaf_step t L HPf (h - 1) ltac:(lia)) as NS. replace (h - 1 + 1) with h in NS by lia.
      pose proof (nd_cases t _ _ _ _ _ _ _ _ HR (h - 1) ltac:(unfold tail; lia)) as NC.
      pose proof (leaf_mc t _ _ _ _ _ _ _ _ HR (h - 1) ltac:(unfold tail; lia)) as LM.
      unfold RefDeflSafeB3.nd in NC, LM. fold m in NC, LM.
      rewrite (GB3i_flat t mc s1), (GB3i_flat t mc s2). cbv zeta. rewrite Em, Edl, Efc. fold m.
      destruct (Z.ltb_spec mc m) as [Ci|Cl].
      +
        unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd in NS. fold m in NS.
        replace (m <? E) with false in NS by (symmetry; apply Z.ltb_ge; lia). cbn [zind] in NS.
        destruct (IH bits n (h - 1) DL1 BC1 DL2 BC2 OL SL R ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & h' & E1 & E2 & R' & B1 & B2).
        exists DL1', OL', DL2', h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
      + assert (Lf : RefDeflSafeB3.leafb t HPf (h - 1) = true) by (unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd; apply Z.ltb_lt; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        destruct (Z.eqb_spec (arr_get DL1 m) bits) as [Eb|Nb].
        * destruct (IH bits (n - 1) (h - 1) DL1 BC1 DL2 BC2 OL SL R ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & h' & E1 & E2 & R' & B1 & B2).
          exists DL1', OL', DL2', h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
        * set (DL1' := arr_set DL1 m (wrap16 bits)). set (DL2' := arr_set DL2 m (wrap16 bits)).
          set (OL' := wrap64 (OL + (bits - arr_get DL1 m) * arr_get FCf m)).
          assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc)).
          { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption.
            - subst DL1' DL2'. apply AG_set. exact ADL.
            - subst DL1'. rewrite arr_len_set. exact LDL1. }
          destruct (IH bits (n - 1) (h - 1) DL1' BC1 DL2' BC2 OL' SL R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1f & OLf & DL2f & h' & E1 & E2 & R' & B1 & B2).
          exists DL1f, OLf, DL2f, h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
  Qed.

  Lemma loop3_gb_rel : forall f bits h DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    0 <= bits <= ML -> HM + 1 <= h <= 573 ->
    zsum (arr_get BC1) 1 (Z.to_nat bits) <= nleaf h -> (forall b, 1 <= b <= ML -> 0 <= arr_get BC1 b) ->
    exists DL1' OL' DL2',
      gen_bitlen_loop3 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc bits h = U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc
      /\ gen_bitlen_loop3 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc bits h = U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc).
  Proof.
    induction f as [|f IH]; intros bits h DL1 BC1 DL2 BC2 OL SL R ABC Hbits Hh Hdem Hnn.
    - exists DL1, OL, DL2. cbn [gen_bitlen_loop3]. split; [reflexivity|]. split; [reflexivity | exact R].
    - pose proof GB_ranges as RG.
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (_ & _ & _ & _ & _ & _ & _ & _ & LBC1 & LBC2).
      rewrite !(GL3_step t mc). rewrite !bt_bl_count_get.
      destruct (Z.eqb_spec bits 0) as [B0|B0]; cbn [negb].
      { exists DL1, OL, DL2. split; [reflexivity|]. split; [reflexivity | exact R]. }
      rewrite <- (AG_get _ _ _ bits ABC) by lia.
      assert (Hc : 0 <= arr_get BC1 bits <= nleaf h).
      { pose proof (Hnn bits ltac:(lia)). split; [lia|].
        pose proof (zsum_ge_point (arr_get BC1) 1 (Z.to_nat bits) bits ltac:(intros; apply Hnn; lia) ltac:(lia)). lia. }
      destruct (loop3i_gb_rel 574 bits (arr_get BC1 bits) h DL1 BC1 DL2 BC2 OL SL R ltac:(lia) Hh Hc) as (DL1a & OLa & DL2a & h1 & E1 & E2 & Ra & B1 & B2).
      rewrite E1, E2.
      destruct (IH (bits - 1) h1 DL1a BC1 DL2a BC2 OLa SL Ra ABC ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & E1' & E2' & R'); try assumption.
      { replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) in Hdem by lia. rewrite zsum_snoc in Hdem.
        replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits in Hdem by lia. lia. }
      exists DL1', OL', DL2'. split; [exact E1'|]. split; [exact E2' | exact R'].
  Qed.
End Passes.


Lemma AG_fill0 : forall (a b : arr) n, arr_len a = n -> arr_len b = n ->
  AG (fun i => 0 <= i < n) (arr_fill a 0 n 0) (arr_fill b 0 n 0).
Proof.
  intros a b n La Lb. split; [rewrite !arr_len_fill; congruence|].
  intros i Hi. rewrite !arr_get_fill. unfold arr_inb. rewrite La, Lb.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 n) && ((0 <=? i) && (i <? n))) with true; [reflexivity|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Theorem gen_bitlen_relU : forall V D BC1 BC2 DLg OL SL,
  HR2 t V D (U1 FCf DLf HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DLg HPg 1 HM DPg BC2 OL SL mc) ->
  (forall p, HM < p < 573 -> D (arr_get HPf p)) ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  exists DL1' BC1' OL' SL' DL2' BC2',
    gen_bitlen (U1 FCf DLf HPf 1 HM DPf BC1 OL SL mc) t = U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc
    /\ gen_bitlen (U2 FCg DLg HPg 1 HM DPg BC2 OL SL mc) t = U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc
    /\ HR2 t V (fun u => D u \/ u = arr_get HPf HM) (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)
    /\ AG (fun i => 0 <= i < 16) BC1' BC2'.
Proof.
  intros V D BC1 BC2 DLg OL SL R TD HOL HSL. pose proof GB_ranges as RG.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
  pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
  pose proof (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADP. pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
  pose proof (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as HV.
  set (root := arr_get HPf HM).
  destruct (AHP HM ltac:(unfold live; lia)) as [Er Vr]. fold root in Er, Vr.
  set (D' := fun u => D u \/ u = root).
  assert (TD9 : forall p, HM <= p < 573 -> D' (arr_get HPf p)).
  { intros p Hp. destruct (Z.eq_dec p HM) as [->|N]; [right; reflexivity | left; apply TD; lia]. }
  assert (DI9 : forall u, E <= u < E + L - 1 -> D' u).
  { intros u Hu. destruct (tail_pos u (or_introl Hu)) as (p & Hp & <-). apply TD9. exact Hp. }
  unfold gen_bitlen. autorewrite with btupd. unfold heap_get. autorewrite with btupd. rewrite Er. fold root.
  set (BC1a := arr_fill BC1 0 (MAX_BITS + 1) 0). set (BC2a := arr_fill BC2 0 (MAX_BITS + 1) 0).
  set (DL1a := arr_set DLf root (wrap16 0)). set (DL2a := arr_set DLg root (wrap16 0)).
  assert (ABCa : AG (fun i => 0 <= i < 16) BC1a BC2a) by (subst BC1a BC2a; unfold MAX_BITS; apply (AG_fill0 BC1 BC2 16 LBC1 LBC2)).
  assert (LBC1a : arr_len BC1a = 16) by (subst BC1a; rewrite arr_len_fill; exact LBC1).
  assert (LBC2a : arr_len BC2a = 16) by (subst BC2a; rewrite arr_len_fill; exact LBC2).
  assert (R9 : HR2 t V D' (U1 FCf DL1a HPf 1 HM DPf BC1a OL SL mc) (U2 FCg DL2a HPg 1 HM DPg BC2a OL SL mc)).
  { apply (HR2_U t s1 s2 TL1 TL2); try assumption.
    - subst DL1a DL2a. apply AG_set_ext; [exact ADL | pose proof (HV root Vr); lia].
    - subst DL1a. rewrite arr_len_set. exact LDL1. }
  pose proof (L1_init t _ _ _ _ _ _ _ _ HR s1 BC1 OL SL LBC1 HOL HSL) as I9. fold root in I9. fold BC1a DL1a in I9.
  destruct (loop1_gb_rel V D' TD9 DI9 573 (HM + 1) 0 DL1a BC1a OL SL DL2a BC2a BC1 OL SL R9 ABCa I9 ltac:(lia))
    as (DL1b & BC1b & OLb & SLb & DL2b & BC2b & ovf & E1 & E2 & Rb & ABCb & I10).
  rewrite E1, E2.
  destruct (Z.eqb_spec ovf 0) as [Z0|NZ].
  { exists DL1b, BC1b, OLb, SLb, DL2b, BC2b. split; [reflexivity|]. split; [reflexivity|]. split; [exact Rb | exact ABCb]. }
  destruct (l1_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I10) as (DLx & BCx & OLx & SLx & EX & HDL10 & LDL10 & HBC10 & LBC10 & _).
  pose proof (f_equal (fun x => ds_bl_count x) EX) as EBC. cbv beta in EBC. autorewrite with btupd in EBC. subst BCx.
  pose proof (l1_ovf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I10) as Hovf.
  replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in HBC10, Hovf by lia.
  rewrite (ovf_identity t _ _ _ _ _ _ _ _ HR) in Hovf.
  assert (HI : L2I t L HPf (arr_get BC1b) (2 * NI t L HPf 573)).
  { apply (L2I_ext t _ _ _ _ _ _ _ _ HR (cntL t L HPf)); [exact (L2_init t _ _ _ _ _ _ _ _ HR)|]. intros b Hb. rewrite HBC10 by exact Hb. reflexivity. }
  pose proof (NI_bound t _ _ _ _ _ _ _ _ HR) as NIB.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rb) as (_ & _ & LDL1b & _ & _ & _ & _ & _ & LBC1b & LBC2b).
  destruct (loop2_run t _ _ _ _ _ _ _ _ HR 573 (NI t L HPf 573) s1 FCf DL1b HPf 1 HM DPf BC1b OLb SLb mc ltac:(lia) ltac:(lia) HI LBC1b)
    as (BCr & EQ2 & HI2 & LBCr & _).
  destruct (loop2_gb_rel V D' 573 ovf DL1b BC1b DL2b BC2b OLb SLb Rb ABCb) as (BC1c & BC2c & E1c & E2c & Rc & ABCc).
  rewrite Hovf in E1c. rewrite EQ2 in E1c.
  pose proof (f_equal (fun x => ds_bl_count x) E1c) as EBC. cbv beta in EBC. autorewrite with btupd in EBC. subst BCr.
  rewrite <- Hovf in EQ2. rewrite EQ2, E2c. unfold HEAP_SIZE.
  destruct (loop3_gb_rel V D' TD9 (Z.to_nat ML) ML 573 DL1b BC1c DL2b BC2c OLb SLb Rc ABCc ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & E1' & E2' & R').
  { destruct HI2 as [NN Z0 HI0 _ TOT _ _]. rewrite <- TOT.
    replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
    rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
    pose proof (zsum_nonneg (arr_get BC1c) (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
  { intros b Hb. apply (l2_nn _ _ _ _ _ HI2). lia. }
  exists DL1', BC1c, OL', SLb, DL2', BC2c. split; [exact E1'|]. split; [exact E2'|]. split; [exact R' | exact ABCc].
Qed.


Lemma NC_rel : forall f (b1 b2 nc : arr) code bits,
  (forall i, 0 <= i < 16 -> arr_get b2 i = arr_get b1 i) -> 1 <= bits ->
  gen_codes_loop1 f b2 nc code bits = gen_codes_loop1 f b1 nc code bits.
Proof.
  induction f as [|f IH]; intros b1 b2 nc code bits Hb Hbits; [reflexivity|].
  cbn [gen_codes_loop1]. destruct (Z.leb_spec bits MAX_BITS) as [C|C]; [|reflexivity].
  unfold MAX_BITS in C. rewrite Hb by lia. apply IH; [exact Hb | lia].
Qed.

Lemma gen_codes_loop2_rel : forall V D f nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL n,
  HR2 t V D (U1 a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) ->
  (forall u, 0 <= u < E -> D u) -> 0 <= n ->
  exists a1' a2',
    gen_codes_loop2 f (set_tree_fc (U1 a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) t a1) t nc mc n = U1 a1' DL1 HP1 HL HMx DP1 BC1 OL SL mc
    /\ gen_codes_loop2 f (set_tree_fc (U2 a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) t a2) t nc mc n = U2 a2' DL2 HP2 HL HMx DP2 BC2 OL SL mc
    /\ HR2 t V D (U1 a1' DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 a2' DL2 HP2 HL HMx DP2 BC2 OL SL mc).
Proof.
  intros V D f. induction f as [|f IH]; intros nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL n R DE Hn.
  - exists a1, a2. cbn [gen_codes_loop2]. rewrite !bt_set_tree_fc. split; [reflexivity|]. split; [reflexivity | exact R].
  - pose proof GB_ranges as RG.
    rewrite !loop2_S. destruct (Z.leb_spec n mc) as [C|C].
    2:{ exists a1, a2. rewrite !bt_set_tree_fc. split; [reflexivity|]. split; [reflexivity | exact R]. }
    cbv zeta. rewrite !bt_Len.
    pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL. pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC.
    rewrite <- (AG_get _ _ _ n ADL) by (apply DE; lia).
    destruct (Z.eqb_spec (arr_get DL1 n) 0) as [L0|L0].
    + exact (IH nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL (n + 1) R DE ltac:(lia)).
    + set (v := wrap16 (bi_reverse (arr_get nc (arr_get DL1 n)) (arr_get DL1 n))).
      assert (R1 : HR2 t V D (U1 (arr_set a1 n v) DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 (arr_set a2 n v) DL2 HP2 HL HMx DP2 BC2 OL SL mc)).
      { pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
        apply (HR2_U t s1 s2 TL1 TL2); try assumption; try (rewrite arr_len_set; assumption).
        - apply AG_set. exact AFC.
        - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R). }
      rewrite (bt_set_tree_fc s1 t a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc (arr_set a1 n v)).
      rewrite (bt_set_tree_fc s2 t a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc (arr_set a2 n v)).
      rewrite <- (bt_set_tree_fc s1 t (arr_set a1 n v) DL1 HP1 HL HMx DP1 BC1 OL SL mc (arr_set a1 n v)).
      rewrite <- (bt_set_tree_fc s2 t (arr_set a2 n v) DL2 HP2 HL HMx DP2 BC2 OL SL mc (arr_set a2 n v)).
      exact (IH (arr_set nc (arr_get DL1 n) (wrap16 (arr_get nc (arr_get DL1 n) + 1))) _ DL1 HP1 DP1 BC1 _ DL2 HP2 DP2 BC2 HL HMx OL SL (n + 1) R1 DE ltac:(lia)).
Qed.

Theorem gen_codes_relU : forall V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HMx OL SL,
  HR2 t V D (U1 FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) ->
  (forall u, 0 <= u < E -> D u) -> AG (fun i => 0 <= i < 16) BC1 BC2 ->
  exists FC1' FC2',
    gen_codes (U1 FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) t mc = U1 FC1' DL1 HP1 HL HMx DP1 BC1 OL SL mc
    /\ gen_codes (U2 FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) t mc = U2 FC2' DL2 HP2 HL HMx DP2 BC2 OL SL mc
    /\ HR2 t V D (U1 FC1' DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 FC2' DL2 HP2 HL HMx DP2 BC2 OL SL mc).
Proof.
  intros V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HMx OL SL R DE ABC. pose proof GB_ranges as RG.
  unfold gen_codes. autorewrite with btupd.
  rewrite (NC_rel 16 BC1 BC2) by (first [lia | intros i Hi; symmetry; apply (AG_get _ _ _ i ABC); exact Hi]).
  rewrite <- (bt_set_tree_fc s1 t FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc FC1).
  rewrite <- (bt_set_tree_fc s2 t FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc FC2).
  apply (gen_codes_loop2_rel V D); [exact R | exact DE | lia].
Qed.
End GB.


Section Assemble.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation TS := (tsize t).
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Hypothesis TL1 : tree_lens s1.
Hypothesis TL2 : tree_lens s2.
Local Notation U1 := (bt_upd s1 t).
Local Notation U2 := (bt_upd s2 t).

Lemma U_inj : forall FC DL HP HL HM DP BC OL SL MC FC' DL' HP' HL' HM' DP' BC' OL' SL' MC',
  U1 FC DL HP HL HM DP BC OL SL MC = U1 FC' DL' HP' HL' HM' DP' BC' OL' SL' MC' ->
  FC = FC' /\ DL = DL' /\ HP = HP' /\ HL = HL' /\ HM = HM' /\ DP = DP' /\ BC = BC' /\ OL = OL' /\ SL = SL' /\ MC = MC'.
Proof.
  intros * EQ.
  pose proof (f_equal (fun x => tree_fc x t) EQ) as E1. pose proof (f_equal (fun x => tree_dl x t) EQ) as E2.
  pose proof (f_equal ds_heap EQ) as E3. pose proof (f_equal ds_heap_len EQ) as E4. pose proof (f_equal ds_heap_max EQ) as E5.
  pose proof (f_equal ds_depth EQ) as E6. pose proof (f_equal ds_bl_count EQ) as E7. pose proof (f_equal ds_opt_len EQ) as E8.
  pose proof (f_equal ds_static_len EQ) as E9. pose proof (f_equal (fun x => max_code x t) EQ) as E10.
  cbv beta in E1, E2, E10. autorewrite with btupd in E1. autorewrite with btupd in E2. autorewrite with btupd in E3.
  autorewrite with btupd in E4. autorewrite with btupd in E5. autorewrite with btupd in E6. autorewrite with btupd in E7.
  autorewrite with btupd in E8. autorewrite with btupd in E9. autorewrite with btupd in E10.
  repeat split; assumption.
Qed.

Theorem build_tree_relU : forall FC1 DL1 HP1 DP1 BC1 HL01 HM01 MC1 FC2 DL2 HP2 DP2 BC2 HL02 HM02 MC2 OL SL,
  arr_len FC1 = TS -> arr_len DL1 = TS -> arr_len HP1 = 573 -> arr_len DP1 = 573 -> arr_len BC1 = 16 ->
  arr_len FC2 = TS -> arr_len DL2 = TS -> arr_len HP2 = 573 -> arr_len DP2 = 573 -> arr_len BC2 = 16 ->
  (forall i, 0 <= arr_get FC1 i < 65536) -> (forall i, 0 <= arr_get DL1 i < 65536) -> (forall i, 0 <= arr_get DP1 i < 256) ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  AG (fun i => 0 <= i < E) FC1 FC2 ->
  exists FC1' DL1' HP1' DP1' BC1' FC2' DL2' HP2' DP2' BC2' HMf OLf SLf mc,
    build_tree (U1 FC1 DL1 HP1 HL01 HM01 DP1 BC1 OL SL MC1) t = U1 FC1' DL1' HP1' 1 HMf DP1' BC1' OLf SLf mc
    /\ build_tree (U2 FC2 DL2 HP2 HL02 HM02 DP2 BC2 OL SL MC2) t = U2 FC2' DL2' HP2' 1 HMf DP2' BC2' OLf SLf mc
    /\ AG (fun i => 0 <= i < E) FC1' FC2' /\ AG (fun i => 0 <= i < E) DL1' DL2' /\ AG (fun i => 0 <= i < 16) BC1' BC2'
    /\ 0 <= mc < E
    /\ arr_len FC1' = TS /\ arr_len FC2' = TS /\ arr_len DL1' = TS /\ arr_len DL2' = TS /\ arr_len BC1' = 16 /\ arr_len BC2' = 16
    /\ arr_len HP1' = 573 /\ arr_len HP2' = 573 /\ arr_len DP1' = 573 /\ arr_len DP2' = 573.
Proof.
  intros FC1 DL1 HP1 DP1 BC1 HL01 HM01 MC1 FC2 DL2 HP2 DP2 BC2 HL02 HM02 MC2 OL SL
         LFC1 LDL1 LHP1 LDP1 LBC1 LFC2 LDL2 LHP2 LDP2 LBC2 RFC1 RDL1 RDP1 HOL HSL AFC.
  pose proof (E_TS t) as HE. pose proof (AG_len _ _ _ AFC) as LFC12.
  pose proof (heap_phase s1 t FC1 DL1 HP1 HL01 HM01 DP1 BC1 OL SL MC1 LFC1 LDL1 LHP1 LDP1 RFC1 RDL1 RDP1) as H.
  cbv zeta in H. autorewrite with btupd in H. unfold HEAP_SIZE in H.
  unfold build_tree. autorewrite with btupd. unfold HEAP_SIZE.
  assert (R0 : HR2 t (fun _ => False) (fun _ => False) (U1 FC1 DL1 HP1 0 573 DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 0 573 DP2 BC2 OL SL MC2)).
  { apply (HR2_U t s1 s2 TL1 TL2); try assumption.
    - eapply AG_mono; [exact AFC|]. intros i [Hi|Hi]; [exact Hi | destruct Hi].
    - split; [congruence | intros i Hi; destruct Hi].
    - split; [congruence | intros i Hi; destruct Hi].
    - intros j Hj. exfalso. unfold live in Hj. lia.
    - intros u Hu. destruct Hu. }
  destruct (loop1_relU t s1 s2 TL1 TL2 (Z.to_nat E) 0 (-1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (DL1a & HP1a & DP1a & DL2a & HP2a & DP2a & HLa & mca & E1a & E2a & Ra & Ba & Bmc).
  rewrite E1a, E2a. rewrite E1a in H.
  destruct (loop2_relU t s1 s2 TL1 TL2 2 mca _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ra ltac:(lia) Bmc)
    as (FC1b & HP1b & DP1b & FC2b & HP2b & DP2b & HLb & OLb & SLb & mcb & Vb & E1b & E2b & Rb & Vb1 & Vb2 & Bb & FEb).
  rewrite E1b, E2b. rewrite E1b in H. cbv beta iota in H. autorewrite with btupd in H. autorewrite with btupd.
  destruct H as (Fl & DLx & HPx & DPx & L & FCf & DLf & HPf & DPf & EQ3 & EQ7 & HR & _ & _ & _ & _ & _ & _ & _ & LF & _ & _ & FCE2 & DLE1).
  destruct (U_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ3) as (-> & -> & -> & -> & _ & -> & _ & -> & -> & _).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  pose proof (HR2_U_mc t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mcb mcb Rb) as Rb'. clear Rb.
  assert (HL2h : 0 <= L / 2 <= L) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (loop3_relU t s1 s2 (Z.to_nat (L / 2)) (L / 2) _ _ _ _ _ _ _ _ _ _ _ _ L 573 _ _ _ _ Rb' HL2h ltac:(lia))
    as (HP1c & HP2c & E1c & E2c & Rc & Oc).
  rewrite E1c, E2c. rewrite E1c in EQ7.
  assert (Rc' : HR2 t Vb (fun u => False \/ 0 <= u < E /\ arr_get FC1 u = 0)
                  (U1 (fc_forced Fl FC1) DLx HP1c (L - 0) (573 - 2 * 0) DPx BC1 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)
                  (U2 FC2b DL2a HP2c (L - 0) (573 - 2 * 0) DP2b BC2 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)).
  { replace (L - 0) with L by lia. replace (573 - 2 * 0) with 573 by lia. exact Rc. }
  destruct (loop4_relU t s1 s2 TL1 TL2 573 0 L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rc' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia))
    as (FC1d & DL1d & HP1d & DP1d & FC2d & DL2d & HP2d & DP2d & Vd & Dd & E1d & E2d & Rd & TDd & HV1 & HD1 & HV2 & FEd).
  replace (L - 0) with L in E1d, E2d by lia. replace (573 - 2 * 0) with 573 in E1d, E2d by lia. replace (E + 0) with E in E1d, E2d by lia.
  rewrite E1d, E2d. rewrite E1d in EQ7. autorewrite with btupd in EQ7. autorewrite with btupd.
  unfold SMALLEST in EQ7 |- *.
  replace (573 - 2 * (L - 1) - 1) with (RefDeflSafeB3.HM L) in EQ7 |- * by (unfold RefDeflSafeB3.HM; lia).
  replace (574 - 2 * L) with (RefDeflSafeB3.HM L) in EQ7 by reflexivity.
  pose proof (HM_range t _ _ _ _ _ _ _ _ HR) as RHM.
  pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd 1 ltac:(unfold live; lia)) as [E21 V1]. rewrite E21.
  destruct (U_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ7) as (-> & -> & EHP & _ & _ & -> & _ & _ & _ & _). rewrite EHP.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd) as (LFCd1 & LFCd2 & LDLd1 & LDLd2 & LHPd1 & LHPd2 & LDPd1 & LDPd2 & _ & _).
  set (HPg := arr_set HP2d (RefDeflSafeB3.HM L) (arr_get HP1d 1)).
  assert (R7 : HR2 t Vd Dd (U1 FCf DLf HPf 1 (RefDeflSafeB3.HM L) DPf BC1 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)
                         (U2 FC2d DL2d HPg 1 (RefDeflSafeB3.HM L) DP2d BC2 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)).
  { rewrite <- EHP. subst HPg. apply (HR2_U t s1 s2 TL1 TL2); try assumption; try (rewrite arr_len_set; assumption).
    - exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite LHPd1, LHPd2.
      destruct (Z.eqb_spec (RefDeflSafeB3.HM L) j) as [<-|N]; cbn [andb].
      + replace ((0 <=? RefDeflSafeB3.HM L) && (RefDeflSafeB3.HM L <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        split; [reflexivity | exact V1].
      + apply (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd). unfold live in *. unfold RefDeflSafeB3.HM in *. lia.
    - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd). }
  assert (TD7 : forall p, RefDeflSafeB3.HM L < p < 573 -> Dd (arr_get HPf p)).
  { intros p Hp. rewrite <- EHP. rewrite arr_get_set. destruct (Z.eqb_spec (RefDeflSafeB3.HM L) p); [lia|]. cbn [andb]. apply TDd. unfold RefDeflSafeB3.HM in *. lia. }
  assert (ROL : 0 <= ol_forced Fl OL < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [exact HOL | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl SL < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| exact HSL].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [exact HSL | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_relU t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ HR FC2d HPg DP2d Vd Dd BC1 BC2 DL2d _ _ R7 TD7 ROL RSL)
    as (DL1e & BC1e & OLe & SLe & DL2e & BC2e & EG1 & EG2 & Re & ABCe).
  rewrite EG1, EG2.
  assert (DE : forall u, 0 <= u < E -> Dd u \/ u = arr_get HPf (RefDeflSafeB3.HM L)).
  { intros u Hu. destruct (Z.eq_dec (arr_get FC1 u) 0) as [Z0|NZ].
    - left. apply HD1. right. split; [exact Hu | exact Z0].
    - assert (Vu : Vj t (fc_forced Fl FC1) (L - 1) u).
      { unfold Vj, V0, Vscan. left. split; [exact Hu|]. rewrite FCE2. destruct (existsb _ _); [lia | exact NZ]. }
      destruct (hr_cov _ _ _ _ _ _ _ _ _ HR u Vu) as (p & Hp & Ep).
      destruct (Z.eq_dec p (RefDeflSafeB3.HM L)) as [->|Np]; [right; symmetry; exact Ep|].
      left. rewrite <- Ep. apply TD7. unfold RefDeflSafeB3.HM in *. lia. }
  destruct (gen_codes_relU t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Re DE ABCe) as (FC1g & FC2g & EC1 & EC2 & Rg).
  rewrite EC1, EC2.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  exists FC1g, DL1e, HPf, DPf, BC1e, FC2g, DL2e, HPg, DP2d, BC2e, (RefDeflSafeB3.HM L), OLe, SLe, mcb.
  split; [reflexivity|]. split; [reflexivity|].
  split; [eapply AG_mono; [exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) | intros i Hi; left; exact Hi]|].
  split; [eapply AG_mono; [exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) | intros i Hi; exact (DE i Hi)]|].
  split; [exact ABCe|]. split; [exact Rmc|].
  repeat split; assumption.
Qed.
End Assemble.
End DeflateTaintBT2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintTrees.DeflateTaintBT2.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma aeq_AG_lt (E : Z) a b : aeq (fun i => i < E) a b -> E <= arr_len a -> AG (fun i => 0 <= i < E) a b.
Proof. intros [L H] HE. split; [exact L|]. intros i Hi. apply H; lia. Qed.
Lemma AG_aeq_lt (E : Z) a b : AG (fun i => 0 <= i < E) a b -> aeq (fun i => i < E) a b.
Proof. intros [L H]. split; [exact L|]. intros i Hi Pi. apply H. lia. Qed.

Section Rel.
Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Local Notation RELx := (REL W C B bnd ms pm).

Lemma rel_bt_upd t x1 x2 FC1 FC2 DL1 DL2 HP1 HP2 HL HM DP1 DP2 BC1 BC2 OL SL MC :
  RELx x1 x2 -> AG (fun i => 0 <= i < sd_elems t) FC1 FC2 ->
  RELx (bt_upd x1 t FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC) (bt_upd x2 t FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC).
Proof.
  intros R A. rewrite !bt_upd_setters.
  destruct t; cbn [set_tree_fc set_tree_dl set_max_code sd_elems] in *;
    [apply rel_set_l_max_code | apply rel_set_d_max_code | apply rel_set_bl_max_code];
    apply rel_set_static_len; apply rel_set_opt_len; apply rel_set_bl_count; apply rel_set_depth;
    apply rel_set_heap_max; apply rel_set_heap_len; apply rel_set_heap;
    [apply rel_set_dyn_ltree_dl; apply rel_set_dyn_ltree_fc | apply rel_set_dyn_dtree_dl; apply rel_set_dyn_dtree_fc | apply rel_set_bl_tree_dl; apply rel_set_bl_tree_fc];
    first [exact R | apply AG_aeq_lt; exact A].
Qed.

Lemma rel_fc_AG t x1 x2 : RELx x1 x2 -> tree_lens x1 -> AG (fun i => 0 <= i < sd_elems t) (tree_fc x1 t) (tree_fc x2 t).
Proof.
  intros R TLn. pose proof (tree_lens_fc x1 t TLn) as L.
  destruct t; cbn [tree_fc sd_elems tsize] in *;
    [apply (aeq_AG_lt L_CODES); [exact (r_lfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold L_CODES; lia]
    |apply (aeq_AG_lt D_CODES); [exact (r_dfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold D_CODES; lia]
    |apply (aeq_AG_lt BL_CODES); [exact (r_bfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold BL_CODES; lia]].
Qed.


Record TAG (t : tree_id) (G : Z -> Prop) (x1 x2 : deflate_state) : Prop := {
  tg_fc : AG (fun i => 0 <= i < sd_elems t) (tree_fc x1 t) (tree_fc x2 t);
  tg_dl : AG G (tree_dl x1 t) (tree_dl x2 t);
  tg_mc : max_code x2 t = max_code x1 t }.

Lemma build_tree_stage t x1 x2 :
  RELx x1 x2 -> bt_pre x1 t -> tree_lens x2 ->
  RELx (build_tree x1 t) (build_tree x2 t)
  /\ TAG t (fun i => 0 <= i < sd_elems t) (build_tree x1 t) (build_tree x2 t)
  /\ (forall t' G, t' <> t -> TAG t' G x1 x2 -> TAG t' G (build_tree x1 t) (build_tree x2 t))
  /\ AG (fun i => 0 <= i < 16) (ds_bl_count (build_tree x1 t)) (ds_bl_count (build_tree x2 t))
  /\ 0 <= max_code (build_tree x1 t) t < sd_elems t
  /\ ds_opt_len (build_tree x2 t) = ds_opt_len (build_tree x1 t)
  /\ ds_static_len (build_tree x2 t) = ds_static_len (build_tree x1 t)
  /\ tree_lens (build_tree x1 t) /\ tree_lens (build_tree x2 t)
  /\ (forall t', t' <> t -> tree_fc (build_tree x1 t) t' = tree_fc x1 t' /\ tree_fc (build_tree x2 t) t' = tree_fc x2 t'
                          /\ tree_dl (build_tree x1 t) t' = tree_dl x1 t' /\ tree_dl (build_tree x2 t) t' = tree_dl x2 t').
Proof.
  intros R HP TL2. pose proof (bp_tl _ _ HP) as TL1.
  pose proof (rel_fc_AG t x1 x2 R TL1) as AFC.
  pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  assert (EO : ds_opt_len x2 = ds_opt_len x1) by (symmetry; apply (clean_eq_fieldT ds_opt_len _ _ EC); reflexivity).
  assert (ES : ds_static_len x2 = ds_static_len x1) by (symmetry; apply (clean_eq_fieldT ds_static_len _ _ EC); reflexivity).
  pose proof TL1 as T1'. pose proof TL2 as T2'. unfold tree_lens in T1', T2'.
  destruct (build_tree_relU t x1 x2 TL1 TL2 (tree_fc x1 t) (tree_dl x1 t) (ds_heap x1) (ds_depth x1) (ds_bl_count x1)
              (ds_heap_len x1) (ds_heap_max x1) (max_code x1 t)
              (tree_fc x2 t) (tree_dl x2 t) (ds_heap x2) (ds_depth x2) (ds_bl_count x2)
              (ds_heap_len x2) (ds_heap_max x2) (max_code x2 t) (ds_opt_len x1) (ds_static_len x1)
              (tree_lens_fc _ _ TL1) (tree_lens_dl _ _ TL1) ltac:(tauto) ltac:(tauto) ltac:(tauto)
              (tree_lens_fc _ _ TL2) (tree_lens_dl _ _ TL2) ltac:(tauto) ltac:(tauto) ltac:(tauto)
              (bp_fc _ _ HP) (bp_dl _ _ HP) (bp_depth _ _ HP) (bp_ol _ _ HP) (bp_sl _ _ HP) AFC)
    as (FC1' & DL1' & HP1' & DP1' & BC1' & FC2' & DL2' & HP2' & DP2' & BC2' & HMf & OLf & SLf & mc & E1 & E2 & A1 & A2 & A3 & Hmc & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  rewrite bt_upd_self in E1. rewrite <- EO, <- ES in E2. rewrite bt_upd_self in E2.
  rewrite E1, E2.
  split; [apply rel_bt_upd; [exact R | exact A1]|].
  split; [constructor; autorewrite with btupd; [exact A1 | exact A2 | reflexivity]|].
  split.
  { intros t' G Ht [F D M]. constructor.
    - rewrite !bt_tree_fc_other by exact Ht. exact F.
    - rewrite !bt_tree_dl_other by exact Ht. exact D.
    - rewrite !max_code_bt_other by exact Ht. exact M. }
  autorewrite with btupd. split; [exact A3|]. split; [exact Hmc|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply bt_tree_lens; try assumption; lia|]. split; [apply bt_tree_lens; try assumption; lia|].
  intros t' Ht. rewrite !bt_tree_fc_other, !bt_tree_dl_other by exact Ht. repeat split; reflexivity.
Qed.


Lemma td_cnt_ext : forall f L1 L2 mc n p q k mx mn x,
  0 <= n -> (forall i, 0 <= i <= mc + 1 -> L1 i = L2 i) ->
  td_cnt L1 mc f n p q k mx mn x = td_cnt L2 mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros L1 L2 mc n p q k mx mn x Hn HL; [reflexivity|].
  cbn [td_cnt]. destruct (Z.leb_spec n mc) as [Cn|Cn]; [|reflexivity].
  rewrite (HL (n + 1)) by lia.
  destruct (_ && _); [apply IH; [lia | exact HL]|].
  destruct (tree_counts _ _). rewrite (IH L1 L2) by (first [lia | exact HL]). reflexivity.
Qed.

Lemma TDcnt_ext : forall L1 L2 mc x, (forall i, 0 <= i <= mc + 1 -> L1 i = L2 i) -> TDcnt L1 mc x = TDcnt L2 mc x.
Proof.
  intros L1 L2 mc x HL. unfold TDcnt.
  destruct (Z_lt_le_dec mc (-1)) as [Hm|Hm].
  - unfold cnts0. destruct (L1 0 =? 0); destruct (L2 0 =? 0); replace (Z.to_nat (mc + 1)) with 0%nat by lia; reflexivity.
  - rewrite (HL 0) by lia. unfold cnts0. destruct (L2 0 =? 0); apply td_cnt_ext; first [lia | exact HL].
Qed.

Lemma scan_stage t x1 x2 :
  RELx x1 x2 -> t <> TB -> tree_lens x1 -> tree_lens x2 ->
  TAG t (fun i => 0 <= i < sd_elems t) x1 x2 ->
  0 <= max_code x1 t < sd_elems t ->
  (forall i, 0 <= i <= max_code x1 t -> 0 <= Len x1 t i <= 15) ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get (ds_bl_tree_fc x1) y /\ arr_get (ds_bl_tree_fc x1) y + 2 * (max_code x1 t + 1) < 65536) ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get (ds_bl_tree_fc x2) y /\ arr_get (ds_bl_tree_fc x2) y + 2 * (max_code x1 t + 1) < 65536) ->
  let mc := max_code x1 t in
  let y1 := scan_tree x1 t mc in let y2 := scan_tree x2 t mc in
  exists b1 b2,
    y1 = set_bl_tree_fc (set_Len x1 t (mc + 1) 65535) b1 /\ y2 = set_bl_tree_fc (set_Len x2 t (mc + 1) 65535) b2
    /\ RELx y1 y2
    /\ TAG t (fun i => 0 <= i < sd_elems t \/ i = mc + 1) y1 y2
    /\ (forall t' G, t' <> t -> t' <> TB -> TAG t' G x1 x2 -> TAG t' G y1 y2)
    /\ tree_lens y1 /\ tree_lens y2
    /\ (forall i, 0 <= i <= mc -> Len y1 t i = Len x1 t i) /\ Len y1 t (mc + 1) = 65535
    /\ (forall x, 0 <= x < 19 -> 0 <= arr_get b1 x <= arr_get (ds_bl_tree_fc x1) x + 2 * (mc + 1)
                                /\ 0 <= arr_get b2 x <= arr_get (ds_bl_tree_fc x2) x + 2 * (mc + 1)).
Proof.
  intros R Ht T1 T2 [AF AD EM] Hmc HL15 HB1 HB2 mc y1 y2.
  pose proof (tree_lens_dl x1 t T1) as LD1. pose proof (tree_lens_dl x2 t T2) as LD2.
  assert (HTS : sd_elems t < tsize t /\ 39 <= 573) by (destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia).
  assert (Lb1 : arr_len (ds_bl_tree_fc x1) = 39) by (unfold tree_lens in T1; tauto).
  assert (Lb2 : arr_len (ds_bl_tree_fc x2) = 39) by (unfold tree_lens in T2; tauto).
  assert (HL15' : forall i, 0 <= i <= mc -> 0 <= Len x2 t i <= 15).
  { intros i Hi. unfold Len. rewrite <- (AG_get _ _ _ i AD) by lia. apply HL15. exact Hi. }
  destruct (scan_tree_cnt x1 (ds_bl_tree_fc x1) t mc Ht ltac:(lia) ltac:(rewrite LD1; lia) HL15 ltac:(lia)
              ltac:(intros y Hy; apply (HB1 y Hy)) ltac:(intros y Hy; apply (HB1 y Hy))) as (b1 & EX1 & Lb1' & Gb1 & EL1 & GL1).
  destruct (scan_tree_cnt x2 (ds_bl_tree_fc x2) t mc Ht ltac:(lia) ltac:(rewrite LD2; lia) HL15' ltac:(lia)
              ltac:(intros y Hy; apply (HB2 y Hy)) ltac:(intros y Hy; apply (HB2 y Hy))) as (b2 & EX2 & Lb2' & Gb2 & EL2 & GL2).
  rewrite sbf_self in EX1, EX2. subst y1 y2. rewrite EX1, EX2.
  assert (ADg : AG (fun i => 0 <= i < sd_elems t \/ i = mc + 1) (tree_dl (set_Len x1 t (mc + 1) 65535) t) (tree_dl (set_Len x2 t (mc + 1) 65535) t)).
  { unfold set_Len, set_Dad. destruct t; cbn [tree_dl set_tree_dl sd_elems] in *; dsr; apply AG_set_ext; first [exact AD | lia]. }
  assert (ELg : forall i, 0 <= i <= mc + 1 -> Len (set_Len x1 t (mc + 1) 65535) t i = Len (set_Len x2 t (mc + 1) 65535) t i).
  { intros i Hi. unfold Len. apply (AG_get _ _ _ i ADg). lia. }
  assert (Ab : aeq (fun i => i < BL_CODES) b1 b2).
  { split; [lia|]. intros i Hi Pi. rewrite Gb1, Gb2. unfold BL_CODES in Pi.
    rewrite (aeq_get _ _ _ i (r_bfc _ _ _ _ _ _ _ _ R)) by (first [lia | unfold BL_CODES; lia]).
    rewrite (TDcnt_ext (fun j => Len (set_Len x1 t (mc + 1) 65535) t j) (fun j => Len (set_Len x2 t (mc + 1) 65535) t j) mc i ELg). reflexivity. }
  exists b1, b2. split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply rel_set_bl_tree_fc; [| exact Ab]. unfold set_Len, set_Dad.
    destruct t; cbn [tree_dl set_tree_dl]; [apply rel_set_dyn_ltree_dl | apply rel_set_dyn_dtree_dl | exfalso; exact (Ht eq_refl)]; exact R. }
  split.
  { constructor.
    - rewrite !(sbf_tree_fc _ _ _ Ht), !tree_fc_set_Len. exact AF.
    - rewrite !sbf_tree_dl. exact ADg.
    - rewrite !max_code_sbf, !max_code_set_Len. exact EM. }
  split.
  { intros t' G Ht' HtB [F D M]. constructor.
    - rewrite !(sbf_tree_fc _ _ _ HtB), !tree_fc_set_Len. exact F.
    - rewrite !sbf_tree_dl, !(tree_dl_set_Len_other _ _ _ _ _ Ht'). exact D.
    - rewrite !max_code_sbf, !max_code_set_Len. exact M. }
  split; [apply tree_lens_sbf; [apply tree_lens_set_Len; exact T1 | lia]|].
  split; [apply tree_lens_sbf; [apply tree_lens_set_Len; exact T2 | lia]|].
  split; [intros i Hi; rewrite sbf_Len; apply EL1; exact Hi |]. split; [rewrite sbf_Len; exact GL1|].
  intros x Hx. rewrite Gb1, Gb2.
  pose proof (TDcnt_nonneg (fun i => Len (set_Len x1 t (mc + 1) 65535) t i) mc x).
  pose proof (TDcnt_le (fun i => Len (set_Len x1 t (mc + 1) 65535) t i) mc x ltac:(lia)).
  pose proof (TDcnt_nonneg (fun i => Len (set_Len x2 t (mc + 1) 65535) t i) mc x).
  pose proof (TDcnt_le (fun i => Len (set_Len x2 t (mc + 1) 65535) t i) mc x ltac:(lia)).
  pose proof (HB1 x Hx). pose proof (HB2 x Hx). lia.
Qed.


Lemma mb_rel : forall f x1 x2 mb, (forall c, 0 <= c < 19 -> Len x2 TB c = Len x1 TB c) -> mb <= 18 ->
  build_bl_tree_loop f x2 mb = build_bl_tree_loop f x1 mb.
Proof.
  induction f as [|f IH]; intros x1 x2 mb HL Hmb; [reflexivity|].
  cbn [build_bl_tree_loop]. destruct (Z.leb_spec 3 mb) as [Hc|Hc]; [|reflexivity].
  pose proof (bl_order_bound mb). rewrite HL by lia.
  destruct (negb _); [reflexivity|]. apply IH; [exact HL | lia].
Qed.

Lemma detect_loop1_rel : forall f x1 x2 n m, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) -> 0 <= n ->
  detect_loop1 f x2 n m = detect_loop1 f x1 n m.
Proof.
  induction f as [|f IH]; intros x1 x2 n m HF Hn; [reflexivity|].
  cbn [detect_loop1]. destruct (Z.leb_spec n 31) as [Hc|Hc]; [|reflexivity].
  rewrite HF by lia. destruct (_ && _); [reflexivity|]. apply IH; [exact HF | lia].
Qed.
Lemma detect_loop2_rel : forall f x1 x2 n, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) -> 0 <= n ->
  detect_loop2 f x2 n = detect_loop2 f x1 n.
Proof.
  induction f as [|f IH]; intros x1 x2 n HF Hn; [reflexivity|].
  cbn [detect_loop2]. destruct (Z.ltb_spec n LITERALS) as [Hc|Hc]; [|reflexivity]. unfold LITERALS in Hc.
  rewrite HF by lia. destruct (negb _); [reflexivity|]. apply IH; [exact HF | lia].
Qed.
Lemma detect_rel : forall x1 x2, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) ->
  detect_data_type x2 = detect_data_type x1.
Proof.
  intros x1 x2 HF. unfold detect_data_type.
  rewrite (detect_loop1_rel 32 x1 x2) by (first [exact HF | lia]).
  destruct (detect_loop1 _ _ _ _); [reflexivity|].
  rewrite !HF by lia. rewrite (detect_loop2_rel 224 x1 x2) by (first [exact HF | lia]). reflexivity.
Qed.

Lemma X0_stage s1 s2 : RELx s1 s2 -> tree_lens s1 ->
  RELx (ov_X0 s1) (ov_X0 s2) /\ (exists c, ov_X0 s1 = set_strm s1 c /\ ov_X0 s2 = set_strm s2 c).
Proof.
  intros R T1. pose proof (rel_fc_AG TL s1 s2 R T1) as AF. cbn [sd_elems tree_fc] in AF.
  unfold ov_X0, tfb_X0. rewrite (rel_level _ _ _ _ _ _ _ _ R), (rel_strm _ _ _ _ _ _ _ _ R).
  rewrite (detect_rel s1 s2) by (intros c Hc; unfold Freq; cbn [tree_fc]; symmetry; apply (AG_get _ _ _ c AF); unfold L_CODES; lia).
  destruct (_ && _).
  - split; [apply rel_set_strm; exact R | eexists; split; reflexivity].
  - split; [exact R|]. exists (ds_strm s1). rewrite <- (rel_strm _ _ _ _ _ _ _ _ R) at 2.
    split; [destruct s1; reflexivity | destruct s2; reflexivity].
Qed.

Lemma tree_fc_set_opt_len x v t : tree_fc (set_opt_len x v) t = tree_fc x t. Proof. destruct t; reflexivity. Qed.
Lemma tree_dl_set_opt_len x v t : tree_dl (set_opt_len x v) t = tree_dl x t. Proof. destruct t; reflexivity. Qed.
Lemma max_code_set_opt_len x v t : max_code (set_opt_len x v) t = max_code x t. Proof. destruct t; reflexivity. Qed.
Lemma TAG_set_opt_len t G x1 x2 v1 v2 : TAG t G x1 x2 -> TAG t G (set_opt_len x1 v1) (set_opt_len x2 v2).
Proof. intros [F D M]. constructor; rewrite ?tree_fc_set_opt_len, ?tree_dl_set_opt_len, ?max_code_set_opt_len; assumption. Qed.
Lemma TAG_set_strm t G x1 x2 c1 c2 : TAG t G x1 x2 -> TAG t G (set_strm x1 c1) (set_strm x2 c2).
Proof. intros [F D M]. constructor; rewrite ?tree_fc_set_strm, ?tree_dl_set_strm, ?max_code_set_strm; assumption. Qed.
Lemma TAG_mono t (G G' : Z -> Prop) x1 x2 : TAG t G x1 x2 -> (forall i, G' i -> G i) -> TAG t G' x1 x2.
Proof. intros [F D M] H. constructor; [exact F | eapply AG_mono; [exact D | exact H] | exact M]. Qed.

Record TPR (s1 s2 : deflate_state) : Prop := {
  tr_rel : RELx (ov_X6 s1) (ov_X6 s2);
  tr_L : TAG TL (fun i => 0 <= i < L_CODES \/ i = ds_l_max_code (ov_X6 s1) + 1) (ov_X6 s1) (ov_X6 s2);
  tr_D : TAG TD (fun i => 0 <= i < D_CODES \/ i = ds_d_max_code (ov_X6 s1) + 1) (ov_X6 s1) (ov_X6 s2);
  tr_B : TAG TB (fun i => 0 <= i < BL_CODES) (ov_X6 s1) (ov_X6 s2);
  tr_mb : ov_mb s2 = ov_mb s1 }.

Theorem tree_phase_rel s1 s2 last : RELx s1 s2 -> fb_entry s1 last -> fb_entry s2 last -> TPR s1 s2.
Proof.
  intros R FE1 FE2.
  pose proof (OP s1 last FE1) as OP1. pose proof (OP s2 last FE2) as OP2.
  pose proof (tree_phase s1 OP1) as TP1. pose proof (tree_phase s2 OP2) as TP2.
  pose proof (fe_tl _ _ FE1) as T1. pose proof (fe_tl _ _ FE2) as T2.
  destruct (X0_stage s1 s2 R T1) as [R0 (c & E01 & E02)].
  pose proof (bt_pre_X0 s1 OP1) as BP0. pose proof (bp_tl _ _ (bt_pre_X0 s2 OP2)) as T02.
  destruct (build_tree_stage TL _ _ R0 BP0 T02) as (R1 & GL1 & K1 & _ & ML1 & _ & _ & T11 & T12 & F1).
  change (build_tree (ov_X0 s1) TL) with (ov_X1 s1) in *. change (build_tree (ov_X0 s2) TL) with (ov_X1 s2) in *.
  destruct (build_tree_stage TD _ _ R1 (tp_bp1 _ TP1) T12) as (R2 & GD2 & K2 & _ & MD2 & _ & _ & T21 & T22 & F2).
  change (build_tree (ov_X1 s1) TD) with (ov_X2 s1) in *. change (build_tree (ov_X1 s2) TD) with (ov_X2 s2) in *.
  pose proof (K2 TL _ ltac:(discriminate) GL1) as GL2.
  assert (HB2 : forall x, (x = ov_X2 s1 /\ fb_entry s1 last) \/ (x = ov_X2 s2 /\ fb_entry s2 last) ->
                forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc x) y = 0).
  { intros x Hx y Hy.
    assert (EB : forall s, ds_bl_tree_fc (ov_X2 s) = ds_bl_tree_fc s -> fb_entry s last -> arr_get (ds_bl_tree_fc (ov_X2 s)) y = 0).
    { intros s Es FE. rewrite Es. destruct (fe_hist _ _ FE) as (_ & _ & HB). apply HB. unfold BL_CODES. exact Hy. }
    destruct (F2 TB ltac:(discriminate)) as (A1 & A2 & _). destruct (F1 TB ltac:(discriminate)) as (B1 & B2 & _).
    rewrite !tree_fc_TB in A1, A2, B1, B2.
    destruct Hx as [[-> FE]|[-> FE]]; apply EB; try exact FE.
    - rewrite A1, B1, E01. destruct s1; reflexivity.
    - rewrite A2, B2, E02. destruct s2; reflexivity. }
  pose proof (tp_h3 _ TP1) as EL3. pose proof (tp_lmax _ TP1) as RLm. rewrite <- EL3 in RLm. unfold L_CODES in RLm.
  destruct (scan_stage TL _ _ R2 ltac:(discriminate) T21 T22 GL2 ltac:(rewrite max_code_TL; exact RLm)
              ltac:(rewrite max_code_TL; exact (tp_h4 _ TP1))
              ltac:(intros y Hy; rewrite (HB2 _ (or_introl (conj eq_refl FE1)) y Hy); rewrite max_code_TL; lia)
              ltac:(intros y Hy; rewrite (HB2 _ (or_intror (conj eq_refl FE2)) y Hy); rewrite max_code_TL; lia))
    as (b31 & b32 & EX31 & EX32 & R3 & GL3 & K3 & T31 & T32 & EL31 & GD31 & Hb3).
  rewrite !max_code_TL in *.
  assert (D31 : scan_tree (ov_X2 s1) TL (ds_l_max_code (ov_X2 s1)) = ov_X3 s1) by reflexivity.
  assert (D32 : scan_tree (ov_X2 s2) TL (ds_l_max_code (ov_X2 s1)) = ov_X3 s2).
  { unfold ov_X3. rewrite <- !max_code_TL. rewrite (tg_mc _ _ _ _ GL2). reflexivity. }
  rewrite D31, D32 in *.
  pose proof (K3 TD _ ltac:(discriminate) ltac:(discriminate) GD2) as GD3.
  pose proof (tp_h7 _ TP1) as ED4. pose proof (tp_dmax _ TP1) as RDm. rewrite <- ED4 in RDm. unfold D_CODES in RDm.
  assert (Eb31 : ds_bl_tree_fc (ov_X3 s1) = b31) by (rewrite EX31; apply sbf_get).
  assert (Eb32 : ds_bl_tree_fc (ov_X3 s2) = b32) by (rewrite EX32; apply sbf_get).
  destruct (scan_stage TD _ _ R3 ltac:(discriminate) T31 T32 GD3 ltac:(rewrite max_code_TD; exact RDm)
              ltac:(rewrite max_code_TD; exact (tp_h8 _ TP1))
              ltac:(intros y Hy; rewrite Eb31, max_code_TD; pose proof (Hb3 y Hy); rewrite (HB2 _ (or_introl (conj eq_refl FE1)) y Hy) in *; lia)
              ltac:(intros y Hy; rewrite Eb32, max_code_TD; pose proof (Hb3 y Hy); rewrite (HB2 _ (or_intror (conj eq_refl FE2)) y Hy) in *; lia))
    as (b41 & b42 & EX41 & EX42 & R4 & GD4 & K4 & T41 & T42 & EL41 & GD41 & Hb4).
  rewrite !max_code_TD in *.
  assert (D41 : scan_tree (ov_X3 s1) TD (ds_d_max_code (ov_X3 s1)) = ov_X4 s1) by reflexivity.
  assert (D42 : scan_tree (ov_X3 s2) TD (ds_d_max_code (ov_X3 s1)) = ov_X4 s2).
  { unfold ov_X4. rewrite <- !max_code_TD. rewrite (tg_mc _ _ _ _ GD3). reflexivity. }
  rewrite D41, D42 in *.
  pose proof (K4 TL _ ltac:(discriminate) ltac:(discriminate) GL3) as GL4.
  destruct (build_tree_stage TB _ _ R4 (tp_bp4 _ TP1) T42) as (R5 & GB5 & K5 & _ & MB5 & EO5 & _ & T51 & T52 & F5).
  change (build_tree (ov_X4 s1) TB) with (ov_X5 s1) in *. change (build_tree (ov_X4 s2) TB) with (ov_X5 s2) in *.
  pose proof (K5 TL _ ltac:(discriminate) GL4) as GL5. pose proof (K5 TD _ ltac:(discriminate) GD4) as GD5.
  assert (Emb : ov_mb s2 = ov_mb s1).
  { unfold ov_mb, tfb_mb. apply mb_rel; [| lia]. intros c0 Hc. unfold Len. symmetry. apply (AG_get _ _ _ c0 (tg_dl _ _ _ _ GB5)). cbn. unfold BL_CODES. exact Hc. }
  assert (E62 : ov_X6 s2 = set_opt_len (ov_X5 s2) (wrap64 (ds_opt_len (ov_X5 s1) + 3 * (ov_mb s1 + 1) + 5 + 5 + 4))).
  { unfold ov_X6, tfb_X6. rewrite Emb, EO5. reflexivity. }
  assert (E61 : ov_X6 s1 = set_opt_len (ov_X5 s1) (wrap64 (ds_opt_len (ov_X5 s1) + 3 * (ov_mb s1 + 1) + 5 + 5 + 4))) by reflexivity.
  pose proof (proj1 (tp_h15 _ TP1)) as EL6. pose proof (proj1 (proj2 (tp_h15 _ TP1))) as ED6.
  constructor.
  - rewrite E61, E62. apply rel_set_opt_len. exact R5.
  - rewrite <- EL3. rewrite E61, E62. apply TAG_set_opt_len. exact GL5.
  - rewrite <- ED4. rewrite E61, E62. apply TAG_set_opt_len. exact GD5.
  - rewrite E61, E62. apply TAG_set_opt_len. exact GB5.
  - exact Emb.
Qed.


Lemma sbs_rel cs : forall Bq s1 s2, REL W C Bq bnd ms pm s1 s2 ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (sbs_run s1 cs))) bnd ms pm (sbs_run s1 cs) (sbs_run s2 cs).
Proof.
  induction cs as [|[v l] cs IH]; intros Bq s1 s2 R; cbn [sbs_run].
  - apply rel_Bx_same. exact R.
  - pose proof (send_bits_rel _ _ _ _ _ _ _ _ v l R) as R1.
    pose proof (IH _ _ _ R1) as R2.
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending (send_bits s1 v l))); [exact R2|].
    pose proof (send_bits_pending_mono s1 v l). pose proof (sbs_pending_mono cs (send_bits s1 v l)). lia.
Qed.

Lemma d_code_bound d : 0 <= d_code d < 30.
Proof. unfold d_code. destruct (Z.ltb d 256); apply dist_code_bound. Qed.

Lemma send_loop_pending_mono : forall f s t mc n p q k mx mn, 1 <= mn ->
  ds_pending s <= ds_pending (send_tree_loop f s t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros s t mc n p q k mx mn Hmn; [cbn [send_tree_loop]; lia|].
  rewrite (send_loop_S f) by exact Hmn. destruct (n <=? mc); [|lia]. cbv zeta.
  destruct (_ && _); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:ETC. pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
  pose proof (sbs_pending_mono (st_calls s mn q p (k + 1)) s).
  pose proof (IH (sbs_run s (st_calls s mn q p (k + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' ltac:(lia)). lia.
Qed.

Lemma send_loop_rel : forall f t mc Bq s1 s2 n p q k mx mn,
  REL W C Bq bnd ms pm s1 s2 -> 1 <= mn -> 0 <= n ->
  (forall i, 0 <= i <= mc + 1 -> Len s2 t i = Len s1 t i) ->
  (forall c, 0 <= c < 19 -> Code s2 TB c = Code s1 TB c /\ Len s2 TB c = Len s1 TB c) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s1 t i <= 15) -> (n <= mc -> 0 <= q <= 15) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (send_tree_loop f s1 t mc n p q k mx mn))) bnd ms pm
      (send_tree_loop f s1 t mc n p q k mx mn) (send_tree_loop f s2 t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros t mc Bq s1 s2 n p q k mx mn R Hmn Hn HL HB HL15 Hq.
  - cbn [send_tree_loop]. apply rel_Bx_same. exact R.
  - rewrite !(send_loop_S f) by exact Hmn.
    destruct (Z.leb_spec n mc) as [Cn|Cn]; [| apply rel_Bx_same; exact R]. cbv zeta.
    rewrite (HL (n + 1)) by lia.
    destruct ((k + 1 <? mx) && (q =? Len s1 t (n + 1))).
    + apply IH; try assumption; try lia. intros Hn1. apply HL15. lia.
    + destruct (tree_counts q (Len s1 t (n + 1))) as [mx' mn'] eqn:ETC.
      pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
      assert (Est : st_calls s2 mn q p (k + 1) = st_calls s1 mn q p (k + 1)).
      { unfold st_calls, blc. pose proof (Hq Cn) as Rq.
        destruct (HB q ltac:(lia)) as [-> ->]. unfold REP_3_6, REPZ_3_10, REPZ_11_138.
        destruct (HB 16 ltac:(lia)) as [-> ->]. destruct (HB 17 ltac:(lia)) as [-> ->]. destruct (HB 18 ltac:(lia)) as [-> ->]. reflexivity. }
      rewrite Est.
      pose proof (sbs_rel (st_calls s1 mn q p (k + 1)) Bq s1 s2 R) as R1.
      eapply rel_Bx_merge.
      * apply IH; [exact R1 | lia | lia | | | |].
        -- intros i Hi. rewrite !sbs_Len. apply HL. exact Hi.
        -- intros c0 Hc. rewrite !sbs_Code, !sbs_Len. apply HB. exact Hc.
        -- intros i Hi. rewrite sbs_Len. apply HL15. exact Hi.
        -- intros Hn1. apply HL15. lia.
      * pose proof (sbs_pending_mono (st_calls s1 mn q p (k + 1)) s1).
        pose proof (send_loop_pending_mono f (sbs_run s1 (st_calls s1 mn q p (k + 1))) t mc (n + 1) q (Len s1 t (n + 1)) 0 mx' mn' ltac:(lia)). lia.
Qed.

Lemma send_tree_rel : forall t mc Bq s1 s2,
  REL W C Bq bnd ms pm s1 s2 -> 0 <= mc ->
  (forall i, 0 <= i <= mc + 1 -> Len s2 t i = Len s1 t i) ->
  (forall c, 0 <= c < 19 -> Code s2 TB c = Code s1 TB c /\ Len s2 TB c = Len s1 TB c) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s1 t i <= 15) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (send_tree s1 t mc))) bnd ms pm (send_tree s1 t mc) (send_tree s2 t mc).
Proof.
  intros t mc Bq s1 s2 R Hmc HL HB HL15. unfold send_tree. rewrite (HL 0) by lia.
  destruct (Len s1 t 0 =? 0); (apply send_loop_rel; [exact R | lia | lia | exact HL | exact HB | exact HL15 | intros _; apply HL15; lia]).
Qed.

Lemma send_tree_pending_mono : forall s t mc, ds_pending s <= ds_pending (send_tree s t mc).
Proof. intros. unfold send_tree. destruct (_ =? 0); apply send_loop_pending_mono; lia. Qed.

Lemma bl_calls_rel : forall n s1 s2 r, (forall c, 0 <= c < 19 -> Len s2 TB c = Len s1 TB c) -> 0 <= r ->
  bl_calls s2 r n = bl_calls s1 r n.
Proof.
  induction n as [|n IH]; intros s1 s2 r HB Hr; [reflexivity|]. cbn [bl_calls].
  pose proof (bl_order_bound r). rewrite HB by lia. rewrite (IH s1 s2) by (first [exact HB | lia]). reflexivity.
Qed.

Definition TBL (lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 : arr) : Prop :=
  (forall c, 0 <= c < L_CODES -> arr_get lfc2 c = arr_get lfc1 c /\ arr_get ldl2 c = arr_get ldl1 c)
  /\ (forall d, 0 <= d < D_CODES -> arr_get dfc2 d = arr_get dfc1 d /\ arr_get ddl2 d = arr_get ddl1 d).

Lemma sym_calls_rel : forall s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx,
  TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  sym_buf_get s2 sx = sym_buf_get s1 sx -> sym_buf_get s2 (sx + 1) = sym_buf_get s1 (sx + 1) ->
  sym_buf_get s2 (sx + 1 + 1) = sym_buf_get s1 (sx + 1 + 1) -> 0 <= sym_buf_get s1 (sx + 1 + 1) < 256 ->
  sym_calls s2 lfc2 ldl2 dfc2 ddl2 sx = sym_calls s1 lfc1 ldl1 dfc1 ddl1 sx.
Proof.
  intros * [TL TD] E0 E1 E2 Hlc. unfold sym_calls, sym_dist, sym_d0, sym_d1, sym_lc. rewrite E0, E1, E2.
  cbv zeta. destruct (_ =? 0).
  - destruct (TL (sym_buf_get s1 (sx + 1 + 1)) ltac:(unfold L_CODES; lia)) as [-> ->]. reflexivity.
  - pose proof (length_code_bound (sym_buf_get s1 (sx + 1 + 1))) as LB.
    destruct (TL (arr_get length_code_a (sym_buf_get s1 (sx + 1 + 1)) + LITERALS + 1) ltac:(unfold L_CODES, LITERALS; lia)) as [-> ->].
    match goal with |- context [d_code ?d] => pose proof (d_code_bound d) as DB; destruct (TD (d_code d) ltac:(unfold D_CODES; lia)) as [-> ->] end.
    reflexivity.
Qed.

Lemma cb_loop_pending_mono : forall f s lfc ldl dfc ddl sx, ds_pending s <= ds_pending (compress_block_loop f s lfc ldl dfc ddl sx).
Proof.
  induction f as [|f IH]; intros; [cbn [compress_block_loop]; lia|].
  rewrite cb_loop_S. cbv zeta. pose proof (sbs_pending_mono (sym_calls s lfc ldl dfc ddl sx) s).
  destruct (_ <? _); [| lia].
  pose proof (IH (sbs_run s (sym_calls s lfc ldl dfc ddl sx)) lfc ldl dfc ddl (sx + 1 + 1 + 1)). lia.
Qed.

Lemma cb_loop_rel : forall f Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx,
  REL W C Bq bnd ms pm s1 s2 -> TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  PBB s1 -> 0 <= sx -> sx mod 3 = 0 -> ds_sym_next s1 mod 3 = 0 -> sx < ds_sym_next s1 ->
  0 <= ds_lit_bufsize s1 -> ds_lit_bufsize s1 + ds_sym_next s1 <= arr_len (ds_pending_buf s1) ->
  (forall i, ds_lit_bufsize s1 <= i < ds_lit_bufsize s1 + ds_sym_next s1 -> Bq i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (compress_block_loop f s1 lfc1 ldl1 dfc1 ddl1 sx))) bnd ms pm
      (compress_block_loop f s1 lfc1 ldl1 dfc1 ddl1 sx) (compress_block_loop f s2 lfc2 ldl2 dfc2 ddl2 sx).
Proof.
  induction f as [|f IH]; intros Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx R HT PB Hsx Hm3 Hn3 Hlt Hlbs Hlen HS.
  - cbn [compress_block_loop]. apply rel_Bx_same. exact R.
  - rewrite !cb_loop_S. cbv zeta.
    assert (Hsx2 : sx + 2 < ds_sym_next s1) by (Z.to_euclidean_division_equations; lia).
    assert (EG : forall i, sx <= i <= sx + 2 -> sym_buf_get s2 i = sym_buf_get s1 i).
    { intros i Hi. unfold sym_buf_get. rewrite (rel_lbs _ _ _ _ _ _ _ _ R). symmetry.
      apply (aeq_get _ _ _ _ (r_pb _ _ _ _ _ _ _ _ R)); [lia | apply HS; lia]. }
    assert (Hlc : 0 <= sym_buf_get s1 (sx + 1 + 1) < 256) by (unfold sym_buf_get; apply PB; lia).
    rewrite (sym_calls_rel s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx HT) by (first [apply EG; lia | exact Hlc]).
    set (cs := sym_calls s1 lfc1 ldl1 dfc1 ddl1 sx).
    pose proof (sbs_rel cs Bq s1 s2 R) as R1.
    rewrite !sbs_sym_next. rewrite (rel_sym_next _ _ _ _ _ _ _ _ R).
    destruct (Z.ltb_spec (sx + 1 + 1 + 1) (ds_sym_next s1)) as [Cl|Cl].
    + eapply rel_Bx_merge.
      * apply (IH _ _ _ _ _ _ _ _ _ _ _ _ R1 HT); rewrite ?sbs_sym_next, ?sbs_lit_bufsize, ?sbs_pbl; try assumption; try lia.
        all: try (apply sbs_PBB; exact PB).
        all: try (Z.to_euclidean_division_equations; lia).
        all: intros i Hi; left; apply HS; exact Hi.
      * pose proof (sbs_pending_mono cs s1). pose proof (cb_loop_pending_mono f (sbs_run s1 cs) lfc1 ldl1 dfc1 ddl1 (sx + 1 + 1 + 1)). lia.
    + exact R1.
Qed.

Lemma compress_block_rel : forall Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2,
  REL W C Bq bnd ms pm s1 s2 -> TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  PBB s1 -> ds_sym_next s1 mod 3 = 0 -> 0 <= ds_sym_next s1 ->
  0 <= ds_lit_bufsize s1 -> ds_lit_bufsize s1 + ds_sym_next s1 <= arr_len (ds_pending_buf s1) ->
  (forall i, ds_lit_bufsize s1 <= i < ds_lit_bufsize s1 + ds_sym_next s1 -> Bq i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (compress_block s1 lfc1 ldl1 dfc1 ddl1))) bnd ms pm
      (compress_block s1 lfc1 ldl1 dfc1 ddl1) (compress_block s2 lfc2 ldl2 dfc2 ddl2).
Proof.
  intros * R HT PB Hn3 Hsn Hlbs Hlen HS. unfold compress_block, send_code.
  rewrite (rel_sym_next _ _ _ _ _ _ _ _ R).
  destruct (proj1 HT END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)) as [-> ->].
  destruct (Z.eqb_spec (ds_sym_next s1) 0) as [Z0|NZ]; cbn [negb].
  - apply send_bits_rel. exact R.
  - pose proof (cb_loop_rel (Z.to_nat (ds_sym_next s1)) Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 0 R HT PB
                  ltac:(lia) ltac:(reflexivity) Hn3 ltac:(lia) Hlbs Hlen HS) as R1.
    eapply rel_Bx_merge; [apply send_bits_rel; exact R1|].
    pose proof (cb_loop_pending_mono (Z.to_nat (ds_sym_next s1)) s1 lfc1 ldl1 dfc1 ddl1 0).
    pose proof (send_bits_pending_mono (compress_block_loop (Z.to_nat (ds_sym_next s1)) s1 lfc1 ldl1 dfc1 ddl1 0) (arr_get lfc1 END_BLOCK) (arr_get ldl1 END_BLOCK)). lia.
Qed.

Lemma compress_block_pending_mono s lfc ldl dfc ddl : ds_pending s <= ds_pending (compress_block s lfc ldl dfc ddl).
Proof.
  unfold compress_block, send_code. destruct (negb _).
  - pose proof (cb_loop_pending_mono (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0).
    pose proof (send_bits_pending_mono (compress_block_loop (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0) (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)). lia.
  - pose proof (send_bits_pending_mono s (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)). lia.
Qed.


Lemma aeq_blit2 (P Q : Z -> Prop) d1 d2 sr1 sr2 dofs sofs n :
  aeq P d1 d2 -> aeq Q sr1 sr2 -> 0 <= sofs -> sofs + n <= arr_len sr1 -> (forall k, 0 <= k < n -> Q (sofs + k)) ->
  aeq (fun j => P j \/ dofs <= j < dofs + n) (arr_blit d1 dofs sr1 sofs n) (arr_blit d2 dofs sr2 sofs n).
Proof.
  intros [L H] [LS HS] Hs Hsn SP. split; [rewrite !arr_len_blit; exact L|].
  intros j Hj Pj. rewrite arr_len_blit in Hj. rewrite !arr_get_blit. unfold arr_inb. rewrite <- L.
  replace ((0 <=? j) && (j <? arr_len d1)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec dofs j); destruct (Z.ltb_spec j (dofs + Z.max 0 n)); cbn [andb].
  - apply HS; [lia|]. replace (sofs + (j - dofs)) with (sofs + (j - dofs)) by lia. apply SP. lia.
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
Qed.

Lemma bi_windup_pending_mono s : ds_pending s <= ds_pending (bi_windup s) <= ds_pending s + 2.
Proof. rewrite bi_windup_pending. destruct (_ <? _); [|destruct (_ <? _)]; lia. Qed.

Lemma pend_set_pending s v : ds_pending (set_pending s v) = v. Proof. reflexivity. Qed.
Lemma pend_set_pending_buf s a : ds_pending (set_pending_buf s a) = ds_pending s. Proof. reflexivity. Qed.
Lemma pbuf_set_pending_buf s a : ds_pending_buf (set_pending_buf s a) = a. Proof. reflexivity. Qed.
Lemma window_set_pending_buf s a : ds_window (set_pending_buf s a) = ds_window s. Proof. reflexivity. Qed.

Lemma tr_stored_block_pending s buf len last :
  ds_pending (tr_stored_block s buf len last) = ds_pending (bi_windup (send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3)) + 4 + len.
Proof.
  unfold tr_stored_block. destruct (negb _); [destruct buf|]; rewrite pend_set_pending, ?pend_set_pending_buf, !put_short_pending; lia.
Qed.

Lemma tr_stored_block_rel0 : forall Bq s1 s2 buf len last,
  REL W C Bq bnd ms pm s1 s2 -> 0 <= len -> (buf = None -> len = 0) ->
  (forall off, buf = Some off -> len <> 0 -> 0 <= off /\ off + len <= arr_len (ds_window s1) /\ forall i, off <= i < off + len -> W i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (tr_stored_block s1 buf len last))) bnd ms pm
      (tr_stored_block s1 buf len last) (tr_stored_block s2 buf len last).
Proof.
  intros Bq s1 s2 buf len last R Hlen Hnone Hbuf. rewrite tr_stored_block_pending. unfold tr_stored_block.
  pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl STORED_BLOCK 1 + last) 3 R) as R1.
  pose proof (send_bits_pending_mono s1 (Z.shiftl STORED_BLOCK 1 + last) 3) as P1.
  set (a1 := send_bits s1 _ 3) in *. set (a2 := send_bits s2 _ 3) in *.
  assert (Wa1 : ds_window a1 = ds_window s1) by (subst a1; apply (k_send_bits ds_window true true keeps_window eq_refl)).
  clearbody a1 a2.
  pose proof (bi_windup_rel _ _ _ _ _ _ _ _ R1) as R2. pose proof (bi_windup_pending_mono a1) as P2.
  set (b1 := bi_windup a1) in *. set (b2 := bi_windup a2) in *.
  assert (Wb1 : ds_window b1 = ds_window s1) by (subst b1; rewrite (k_bi_windup ds_window true true keeps_window eq_refl); exact Wa1).
  clearbody b1 b2.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R2 ltac:(lia)) as R2'. clear R1 R2.
  pose proof (put_short_rel _ _ _ _ _ _ _ _ (wrap16 len) R2') as R3.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R3 ltac:(rewrite put_short_pending; lia)) as R3'. clear R3.
  pose proof (put_short_rel _ _ _ _ _ _ _ _ (wrap16 (Z.lnot len)) R3') as R4.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R4 ltac:(rewrite !put_short_pending; lia)) as R4'. clear R4 R3' R2'.
  rewrite !put_short_pending in R4'. replace (ds_pending b1 + 2 + 2) with (ds_pending b1 + 4) in R4' by lia.
  set (c1 := put_short (put_short b1 _) _) in *. set (c2 := put_short (put_short b2 _) _) in *.
  assert (Pc : ds_pending c1 = ds_pending b1 + 4) by (subst c1; rewrite !put_short_pending; lia).
  pose proof (rel_pending _ _ _ _ _ _ _ _ R4') as Epc.
  assert (Ew : aeq W (ds_window c1) (ds_window c2)) by exact (r_win _ _ _ _ _ _ _ _ R4').
  assert (Ew1 : ds_window c1 = ds_window s1).
  { subst c1. rewrite !(k_put_short ds_window true true keeps_window eq_refl), <- Wb1. reflexivity. }
  clearbody c1 c2.
  destruct (Z.eqb_spec len 0) as [L0|L0]; cbn [negb].
  - rewrite Epc, L0, Z.add_0_r. apply rel_set_pending. exact R4'.
  - destruct buf as [off|]; [| exfalso; exact (L0 (Hnone eq_refl))].
    destruct (Hbuf off eq_refl L0) as (Ho & Hol & HW). rewrite !pend_set_pending_buf. rewrite Epc.
    rewrite <- (rel_pending_out _ _ _ _ _ _ _ _ R4') at 1 || idtac.
    replace (ds_window c2) with (ds_window c2) by reflexivity.
    apply rel_set_pending.
    pose proof (aeq_blit2 (Bx Bq (ds_pending s1) (ds_pending b1 + 4)) W _ _ _ _ (ds_pending c1) off len
                  (r_pb _ _ _ _ _ _ _ _ R4') Ew Ho ltac:(rewrite Ew1; exact Hol) ltac:(intros k Hk; apply HW; lia)) as AB.
    eapply rel_set_pending_buf; [exact R4'|].
    eapply aeq_mono; [exact AB|].
    intros i. unfold Bx. rewrite Pc. intros [X|X]; [left; left; exact X |].
    destruct (Z_lt_le_dec i (ds_pending b1 + 4)); [left; right; lia | right; lia].
Qed.


Lemma init_block_rel : forall Bq s1 s2, REL W C Bq bnd ms pm s1 s2 -> REL W C Bq bnd ms pm (init_block s1) (init_block s2).
Proof.
  intros Bq s1 s2 R. unfold init_block, set_Freq. cbn [tree_fc set_tree_fc]. dsr.
  apply rel_set_matches. apply rel_set_sym_next. apply rel_set_static_len. apply rel_set_opt_len.
  apply rel_set_dyn_ltree_fc; [| apply aeq_set_keep; eapply aeq_mono; [apply aeq_fill; exact (r_lfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_bl_tree_fc; [| eapply aeq_mono; [apply aeq_fill; exact (r_bfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_dyn_dtree_fc; [| eapply aeq_mono; [apply aeq_fill; exact (r_dfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_dyn_ltree_fc; [exact R | eapply aeq_mono; [apply aeq_fill; exact (r_lfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
Qed.


Lemma trees8_inv a b : trees8 b = trees8 a ->
  (forall t, tree_fc b t = tree_fc a t /\ tree_dl b t = tree_dl a t) /\ ds_l_max_code b = ds_l_max_code a /\ ds_d_max_code b = ds_d_max_code a.
Proof.
  intros E. unfold trees8 in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8.
  split; [| split; assumption]. intros [| |]; cbn [tree_fc tree_dl]; split; assumption.
Qed.

Lemma trees8_fc a b t : trees8 b = trees8 a -> tree_fc b t = tree_fc a t.
Proof. intros E. exact (proj1 (proj1 (trees8_inv a b E) t)). Qed.
Lemma trees8_dl a b t : trees8 b = trees8 a -> tree_dl b t = tree_dl a t.
Proof. intros E. exact (proj2 (proj1 (trees8_inv a b E) t)). Qed.

Lemma l_max_code_send_bits x v l : ds_l_max_code (send_bits x v l) = ds_l_max_code x.
Proof. exact (proj1 (proj2 (trees8_inv _ _ (trees8_send_bits x v l)))). Qed.
Lemma d_max_code_send_bits x v l : ds_d_max_code (send_bits x v l) = ds_d_max_code x.
Proof. exact (proj2 (proj2 (trees8_inv _ _ (trees8_send_bits x v l)))). Qed.

Definition SYMB (B0 : Z -> Prop) (s : deflate_state) : Prop :=
  forall i, ds_lit_bufsize s <= i < ds_lit_bufsize s + ds_sym_next s -> B0 i.
End Rel.

Definition FLUSH_BLOCK_REL : Prop :=
  forall W C B bnd ms pm s1 s2 last,
    REL W C B bnd ms pm s1 s2 -> fb_entry s1 last -> fb_entry s2 last ->
    SYMB B s1 -> (forall i, i < WHI s1 -> W i) -> ds_block_start s1 <= ds_strstart s1 ->
    let s1' := tr_flush_block s1 (fb_buf s1) (fb_len s1) last in
    let s2' := tr_flush_block s2 (fb_buf s2) (fb_len s2) last in
    REL W C (Bx B 0 (ds_pending s1')) bnd ms pm s1' s2'.

Lemma trees8_dyn a b : trees8 b = trees8 a ->
  ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a
  /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a.
Proof. intros E. unfold trees8 in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8. repeat split; assumption. Qed.

Lemma send_loop_keep : forall f s t mc n p q k mx mn, 1 <= mn ->
  (PBB s -> PBB (send_tree_loop f s t mc n p q k mx mn))
  /\ arr_len (ds_pending_buf (send_tree_loop f s t mc n p q k mx mn)) = arr_len (ds_pending_buf s)
  /\ ds_sym_next (send_tree_loop f s t mc n p q k mx mn) = ds_sym_next s
  /\ ds_lit_bufsize (send_tree_loop f s t mc n p q k mx mn) = ds_lit_bufsize s.
Proof.
  induction f as [|f IH]; intros s t mc n p q k mx mn Hmn; [cbn [send_tree_loop]; split; [intros H; exact H|]; repeat split; reflexivity|].
  rewrite send_loop_S by exact Hmn. destruct (n <=? mc); [| split; [intros H; exact H|]; repeat split; reflexivity]. cbv zeta.
  destruct (_ && _); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:ETC. pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
  destruct (IH (sbs_run s (st_calls s mn q p (k + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' ltac:(lia)) as (A1 & A2 & A3 & A4).
  rewrite A2, A3, A4, sbs_pbl, sbs_sym_next, sbs_lit_bufsize.
  split; [intros PB; apply A1; apply sbs_PBB; exact PB|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma send_tree_keep : forall s t mc,
  (PBB s -> PBB (send_tree s t mc)) /\ arr_len (ds_pending_buf (send_tree s t mc)) = arr_len (ds_pending_buf s)
  /\ ds_sym_next (send_tree s t mc) = ds_sym_next s /\ ds_lit_bufsize (send_tree s t mc) = ds_lit_bufsize s.
Proof. intros. unfold send_tree. destruct (_ =? 0); apply send_loop_keep; lia. Qed.

Section Flush.
Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Variable last : Z.
Hypothesis R : REL W C B bnd ms pm s1 s2.
Hypothesis FE1 : fb_entry s1 last.
Hypothesis FE2 : fb_entry s2 last.
Hypothesis HS : SYMB B s1.
Hypothesis HW : forall i, i < WHI s1 -> W i.
Hypothesis Hbs : ds_block_start s1 <= ds_strstart s1.

Let TP1 : TPF s1 := tree_phase s1 (OP s1 last FE1).
Let TR : TPR W C B bnd ms pm s1 s2 := tree_phase_rel W C B bnd ms pm s1 s2 last R FE1 FE2.
Local Notation X61 := (ov_X6 s1).
Local Notation X62 := (ov_X6 s2).

Lemma X6_facts :
  ds_pending X61 = 0 /\ ds_pending_buf X61 = ds_pending_buf s1 /\ ds_sym_next X61 = ds_sym_next s1
  /\ ds_lit_bufsize X61 = ds_lit_bufsize s1 /\ ds_window X61 = ds_window s1
  /\ PBB X61 /\ ds_sym_next s1 = 3 * nsym s1 /\ 0 <= nsym s1 /\ 128 <= ds_lit_bufsize s1
  /\ arr_len (ds_pending_buf s1) = ds_lit_bufsize s1 * 4 /\ ds_sym_next s1 <= 3 * (ds_lit_bufsize s1 - 1)
  /\ arr_len (ds_window s1) = 2 * ds_w_size s1 /\ 0 <= ds_strstart s1 <= 2 * ds_w_size s1
  /\ 0 <= ds_strstart s1 - ds_block_start s1 < 2 ^ 32 /\ ds_w_size s1 <= 32768.
Proof.
  pose proof (nt_view_facts _ _ (tp_nt6 _ TP1)) as (Epb & Epd & _ & _ & Elbs & Esn & _ & _ & _ & _ & _ & _ & Ewin & _).
  pose proof FE1 as F. destruct F.
  rewrite Epd, Epb, Esn, Elbs, Ewin.
  split; [exact fe_pending|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [unfold PBB; rewrite Epb; exact fe_pbb|]. split; [exact fe_sn|]. split; [lia|]. split; [lia|]. split; [exact fe_pbl|].
  split; [lia|]. split; [exact fe_wl|]. split; [exact fe_str|]. split; [exact fe_diff | lia].
Qed.

Lemma sd_elems_TL : sd_elems TL = L_CODES. Proof. reflexivity. Qed.
Lemma sd_elems_TD : sd_elems TD = D_CODES. Proof. reflexivity. Qed.
Lemma sd_elems_TB : sd_elems TB = BL_CODES. Proof. reflexivity. Qed.
Lemma Code_eq x t i : Code x t i = arr_get (tree_fc x t) i. Proof. reflexivity. Qed.

Lemma tfb_branch_2 X buf len : (tfb_branch X buf len =? 2) = true -> exists off, buf = Some off.
Proof.
  unfold tfb_branch. cbv zeta. destruct buf as [off|]; [intros _; exists off; reflexivity|].
  cbn [is_some]. rewrite andb_false_r.
  match goal with |- ((if ?c then 0 else 1) =? 2) = true -> _ => destruct c end; cbn; intros HH; discriminate HH.
Qed.

Lemma Len_tr a b t i : trees8 b = trees8 a -> Len b t i = Len a t i.
Proof. intros E. unfold Len. rewrite (trees8_dl _ _ t E). reflexivity. Qed.
Lemma Code_tr a b t i : trees8 b = trees8 a -> Code b t i = Code a t i.
Proof. intros E. unfold Code. rewrite (trees8_fc _ _ t E). reflexivity. Qed.

Lemma X6_agree :
  (forall i, 0 <= i <= ds_l_max_code X61 + 1 -> Len X62 TL i = Len X61 TL i)
  /\ (forall i, 0 <= i <= ds_d_max_code X61 + 1 -> Len X62 TD i = Len X61 TD i)
  /\ (forall c, 0 <= c < 19 -> Code X62 TB c = Code X61 TB c /\ Len X62 TB c = Len X61 TB c)
  /\ TBL (tree_fc X61 TL) (tree_dl X61 TL) (tree_fc X61 TD) (tree_dl X61 TD)
         (tree_fc X62 TL) (tree_dl X62 TL) (tree_fc X62 TD) (tree_dl X62 TD)
  /\ ds_l_max_code X62 = ds_l_max_code X61 /\ ds_d_max_code X62 = ds_d_max_code X61
  /\ (forall i, 0 <= i <= ds_l_max_code X61 -> 0 <= Len X61 TL i <= 15)
  /\ (forall i, 0 <= i <= ds_d_max_code X61 -> 0 <= Len X61 TD i <= 15)
  /\ 0 <= ds_l_max_code X61 < L_CODES /\ 0 <= ds_d_max_code X61 < D_CODES /\ 2 <= ov_mb s1 <= 18.
Proof.
  pose proof TR as [R6 [FL DL ML] [FD DD MD] [FB DB MB] Emb].
  pose proof (tp_lmax _ TP1) as RLm. pose proof (tp_dmax _ TP1) as RDm.
  rewrite !max_code_TL in ML. rewrite !max_code_TD in MD.
  rewrite sd_elems_TL in FL. rewrite sd_elems_TD in FD. rewrite sd_elems_TB in FB. unfold TBL.
  split; [intros i Hi; rewrite !Len_eq; symmetry; apply (AG_get _ _ _ i DL); unfold L_CODES in *; lia|].
  split; [intros i Hi; rewrite !Len_eq; symmetry; apply (AG_get _ _ _ i DD); unfold D_CODES in *; lia|].
  split; [intros c Hc; rewrite !Code_eq, !Len_eq; split; symmetry; [apply (AG_get _ _ _ c FB) | apply (AG_get _ _ _ c DB)]; unfold BL_CODES; lia|].
  split.
  { split.
    - intros c Hc. split; symmetry; [apply (AG_get _ _ _ c FL) | apply (AG_get _ _ _ c DL)]; lia.
    - intros d Hd. split; symmetry; [apply (AG_get _ _ _ d FD) | apply (AG_get _ _ _ d DD)]; lia. }
  split; [exact ML|]. split; [exact MD|]. split; [exact (tp_LD _ TP1)|]. split; [exact (tp_DD _ TP1)|].
  split; [exact RLm|]. split; [exact RDm | exact (tp_mb _ TP1)].
Qed.

Lemma emit_rel :
  let buf := fb_buf s1 in let len := fb_len s1 in let mb := ov_mb s1 in let d := tfb_branch X61 buf len in
  REL W C (Bx B 0 (ds_pending (tfb_emit d X61 mb buf len last))) bnd ms pm
      (tfb_emit d X61 mb buf len last) (tfb_emit d X62 mb buf len last).
Proof.
  intros buf len mb d. pose proof TR as [R6 _ _ _ Emb].
  pose proof X6_facts as (P0 & Epb & Esn & Elbs & Ewin & PB6 & Hsn3 & Hns & Hlbs & Hpbl & Hsnb & Hwl & Hstr & Hdiff & Hws).
  pose proof X6_agree as (AL & AD & AB & HT & EML & EMD & L15 & D15 & RLm & RDm & Rmb).
  assert (HSX : forall Bq : Z -> Prop, (forall i, B i -> Bq i) ->
            forall i, ds_lit_bufsize X61 <= i < ds_lit_bufsize X61 + ds_sym_next X61 -> Bq i).
  { intros Bq HBq i Hi. apply HBq. apply HS. rewrite <- Elbs, <- Esn. exact Hi. }
  unfold tfb_emit. replace (Bx B 0) with (Bx B (ds_pending X61)) by (rewrite P0; reflexivity).
  destruct (d =? 2) eqn:Ed.
  {
    destruct (tfb_branch_2 _ _ _ Ed) as [off Eoff].
    apply tr_stored_block_rel0; [exact R6 | subst len; unfold fb_len; apply wrap64_range | intros HH; rewrite Eoff in HH; discriminate HH |].
    intros off' Eo' Hl0. rewrite Eoff in Eo'. injection Eo' as <-.
    subst buf len. unfold fb_buf, fb_len in *. destruct (Z.leb_spec 0 (ds_block_start s1)) as [Hb0|Hb0]; [| discriminate Eoff].
    injection Eoff as Eoff. rewrite wrap32_mod, Z.mod_small in Eoff by lia. subst off.
    rewrite wrap64_mod, Z.mod_small by lia. rewrite Ewin, Hwl.
    split; [lia|]. split; [lia|]. intros i Hi. apply HW. unfold WHI. pose proof (fe_look _ _ FE1). lia. }
  destruct (d =? 0) eqn:Ed0.
  {
    pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl STATIC_TREES 1 + last) 3 R6) as R7.
    eapply rel_Bx_merge.
    - apply (compress_block_rel W C B bnd ms pm (Bx B (ds_pending X61) (ds_pending (send_bits X61 (Z.shiftl STATIC_TREES 1 + last) 3)))); try exact R7.
      + split; intros; split; reflexivity.
      + apply send_bits_PBB. exact PB6.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), Esn, Hsn3. rewrite Z.mul_comm. apply Z_mod_mult.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), Esn. lia.
      + rewrite (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl), Elbs. lia.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl), sb_pbl, Esn, Elbs, Epb. lia.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl).
        apply HSX. intros i Hi. left. exact Hi.
    - pose proof (send_bits_pending_mono X61 (Z.shiftl STATIC_TREES 1 + last) 3).
      pose proof (compress_block_pending_mono (send_bits X61 (Z.shiftl STATIC_TREES 1 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl). lia. }
  cbv zeta. rewrite !l_max_code_send_bits, !d_max_code_send_bits, EML, EMD.
  set (Y1 := send_bits X61 (Z.shiftl DYN_TREES 1 + last) 3). set (Y2 := send_bits X62 (Z.shiftl DYN_TREES 1 + last) 3).
  pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl DYN_TREES 1 + last) 3 R6) as R7. fold Y1 Y2 in R7.
  pose proof (send_bits_pending_mono X61 (Z.shiftl DYN_TREES 1 + last) 3) as M7. fold Y1 in M7.
  assert (T71 : trees8 Y1 = trees8 X61) by (subst Y1; apply trees8_send_bits).
  assert (T72 : trees8 Y2 = trees8 X62) by (subst Y2; apply trees8_send_bits).
  assert (STEP : forall (Bq : Z -> Prop) (a1 a2 : deflate_state) (f : deflate_state -> deflate_state),
            REL W C Bq bnd ms pm a1 a2 ->
            REL W C (Bx Bq (ds_pending a1) (ds_pending (f a1))) bnd ms pm (f a1) (f a2) ->
            True) by (intros; exact I).
  pose proof (l_max_code_send_bits X61 (Z.shiftl DYN_TREES 1 + last) 3) as ELY. fold Y1 in ELY.
  unfold send_all_trees.
  set (lc := ds_l_max_code X61 + 1). set (dc := ds_d_max_code X61 + 1).
  assert (E4 : forall Y, trees8 Y = trees8 X61 \/ trees8 Y = trees8 X62 ->
            send_all_trees_loop 19 (send_bits (send_bits (send_bits Y (lc - 257) 5) (dc - 1) 5) (mb + 1 - 4) 4) (mb + 1) 0
            = sbs_run Y ([(lc - 257, 5); (dc - 1, 5); (mb + 1 - 4, 4)] ++ bl_calls X61 0 (Z.to_nat (mb + 1)))).
  { intros Y TY. rewrite send_all_loop_fuel by lia. rewrite Z.sub_0_r. rewrite sbs_run_app. cbn [sbs_run].
    f_equal. apply bl_calls_rel; [| lia]. intros c Hc.
    rewrite !(Len_tr _ _ _ _ (trees8_send_bits _ _ _)).
    destruct TY as [TY|TY]; rewrite (Len_tr _ _ _ _ TY); [reflexivity | apply AB; exact Hc]. }
  rewrite (E4 Y1 (or_introl T71)), (E4 Y2 (or_intror T72)).
  set (cs4 := [(lc - 257, 5); (dc - 1, 5); (mb + 1 - 4, 4)] ++ bl_calls X61 0 (Z.to_nat (mb + 1))).
  pose proof (sbs_rel W C bnd ms pm cs4 _ _ _ R7) as R8. pose proof (sbs_pending_mono cs4 Y1) as M8.
  assert (T81 : trees8 (sbs_run Y1 cs4) = trees8 X61) by (rewrite trees8_sbs_run; exact T71).
  assert (T82 : trees8 (sbs_run Y2 cs4) = trees8 X62) by (rewrite trees8_sbs_run; exact T72).
  set (Z1 := sbs_run Y1 cs4) in *. set (Z2 := sbs_run Y2 cs4) in *.
  assert (R9 := send_tree_rel W C bnd ms pm TL (lc - 1) _ Z1 Z2 R8 ltac:(subst lc; lia)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T81), (Len_tr _ _ _ _ T82); apply AL; subst lc; lia)
            ltac:(intros c Hc; rewrite (Code_tr _ _ _ _ T81), (Code_tr _ _ _ _ T82), (Len_tr _ _ _ _ T81), (Len_tr _ _ _ _ T82); apply AB; exact Hc)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T81); apply L15; subst lc; lia)).
  pose proof (send_tree_pending_mono Z1 TL (lc - 1)) as M9.
  assert (T91 : trees8 (send_tree Z1 TL (lc - 1)) = trees8 X61) by (rewrite trees8_send_tree; exact T81).
  assert (T92 : trees8 (send_tree Z2 TL (lc - 1)) = trees8 X62) by (rewrite trees8_send_tree; exact T82).
  set (V1 := send_tree Z1 TL (lc - 1)) in *. set (V2 := send_tree Z2 TL (lc - 1)) in *.
  assert (R10 := send_tree_rel W C bnd ms pm TD (dc - 1) _ V1 V2 R9 ltac:(subst dc; lia)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T91), (Len_tr _ _ _ _ T92); apply AD; subst dc; lia)
            ltac:(intros c Hc; rewrite (Code_tr _ _ _ _ T91), (Code_tr _ _ _ _ T92), (Len_tr _ _ _ _ T91), (Len_tr _ _ _ _ T92); apply AB; exact Hc)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T91); apply D15; subst dc; lia)).
  pose proof (send_tree_pending_mono V1 TD (dc - 1)) as M10.
  assert (T101 : trees8 (send_tree V1 TD (dc - 1)) = trees8 X61) by (rewrite trees8_send_tree; exact T91).
  assert (T102 : trees8 (send_tree V2 TD (dc - 1)) = trees8 X62) by (rewrite trees8_send_tree; exact T92).
  set (U1 := send_tree V1 TD (dc - 1)) in *. set (U2 := send_tree V2 TD (dc - 1)) in *.
  destruct (send_tree_keep V1 TD (dc - 1)) as (KU1 & KU2 & KU3 & KU4). fold U1 in KU1, KU2, KU3, KU4.
  destruct (send_tree_keep Z1 TL (lc - 1)) as (KV1 & KV2 & KV3 & KV4). fold V1 in KV1, KV2, KV3, KV4.
  assert (KZ : PBB Z1 /\ arr_len (ds_pending_buf Z1) = arr_len (ds_pending_buf X61) /\ ds_sym_next Z1 = ds_sym_next X61 /\ ds_lit_bufsize Z1 = ds_lit_bufsize X61).
  { subst Z1 Y1. rewrite sbs_pbl, sbs_sym_next, sbs_lit_bufsize, sb_pbl,
      (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl).
    split; [apply sbs_PBB; apply send_bits_PBB; exact PB6 | repeat split; reflexivity]. }
  destruct KZ as (KZ1 & KZ2 & KZ3 & KZ4).
  rewrite <- (tree_fc_TL U1), <- (tree_dl_TL U1), <- (tree_fc_TD U1), <- (tree_dl_TD U1).
  rewrite <- (tree_fc_TL U2), <- (tree_dl_TL U2), <- (tree_fc_TD U2), <- (tree_dl_TD U2).
  rewrite (trees8_fc _ _ TL T101), (trees8_dl _ _ TL T101), (trees8_fc _ _ TD T101), (trees8_dl _ _ TD T101).
  rewrite (trees8_fc _ _ TL T102), (trees8_dl _ _ TL T102), (trees8_fc _ _ TD T102), (trees8_dl _ _ TD T102).
  assert (R10' : REL W C (Bx B (ds_pending X61) (ds_pending U1)) bnd ms pm U1 U2).
  { apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending Y1)); [| lia].
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending Z1)); [| lia].
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending V1)); [| lia]. exact R10. }
  eapply rel_Bx_merge.
  - apply (compress_block_rel W C B bnd ms pm _ U1 U2); try exact R10'; try exact HT.
    + apply KU1, KV1. exact KZ1.
    + rewrite KU3, KV3, KZ3, Esn, Hsn3. rewrite Z.mul_comm. apply Z_mod_mult.
    + rewrite KU3, KV3, KZ3, Esn. lia.
    + rewrite KU4, KV4, KZ4, Elbs. lia.
    + rewrite KU2, KV2, KZ2, KU3, KV3, KZ3, KU4, KV4, KZ4, Esn, Elbs, Epb. lia.
    + rewrite KU3, KV3, KZ3, KU4, KV4, KZ4. apply HSX. intros i Hi. unfold Bx. left. exact Hi.
  - pose proof (compress_block_pending_mono U1 (tree_fc X61 TL) (tree_dl X61 TL) (tree_fc X61 TD) (tree_dl X61 TD)). lia.
Qed.

Lemma keeps_pending : keeps ds_pending false true.
Proof.
  constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end;
  match goal with ss : deflate_state |- _ => destruct ss; reflexivity end.
Qed.
Lemma init_block_pending e : ds_pending (init_block e) = ds_pending e.
Proof. exact (k_init_block ds_pending false true keeps_pending eq_refl e). Qed.

Lemma fin_rel : forall Bq e1 e2, REL W C Bq bnd ms pm e1 e2 ->
  REL W C (Bx Bq (ds_pending e1) (ds_pending (tfb_fin last e1))) bnd ms pm (tfb_fin last e1) (tfb_fin last e2).
Proof.
  intros Bq e1 e2 Re. unfold tfb_fin. cbv zeta.
  pose proof (init_block_rel W C bnd ms pm Bq e1 e2 Re) as Ri.
  pose proof (init_block_pending e1) as Ep.
  destruct (negb (last =? 0)).
  - rewrite <- Ep. apply bi_windup_rel. exact Ri.
  - rewrite <- Ep at 1. apply rel_Bx_same. exact Ri.
Qed.

Lemma fin_pending_mono e : ds_pending e <= ds_pending (tfb_fin last e) <= ds_pending e + 2.
Proof.
  unfold tfb_fin. cbv zeta. destruct (negb (last =? 0)).
  - pose proof (bi_windup_pending_mono (init_block e)). rewrite init_block_pending in H. exact H.
  - rewrite init_block_pending. lia.
Qed.

Lemma send_all_trees_loop_pending_mono f : forall s bc r, ds_pending s <= ds_pending (send_all_trees_loop f s bc r).
Proof.
  induction f as [|f IH]; intros; cbn [send_all_trees_loop]; [lia|].
  destruct (r <? bc); [|lia].
  eapply Z.le_trans; [| apply IH]. apply (proj1 (send_bits_pending_mono _ _ _)).
Qed.

Lemma tfb_emit_pending_mono d X mb buf len : 0 <= len ->
  ds_pending X <= ds_pending (tfb_emit d X mb buf len last).
Proof.
  intros Hlen. unfold tfb_emit. destruct (d =? 2).
  { rewrite tr_stored_block_pending.
    pose proof (send_bits_pending_mono X (Z.shiftl STORED_BLOCK 1 + last) 3).
    pose proof (bi_windup_pending_mono (send_bits X (Z.shiftl STORED_BLOCK 1 + last) 3)). lia. }
  destruct (d =? 0).
  { eapply Z.le_trans; [apply (proj1 (send_bits_pending_mono X (Z.shiftl STATIC_TREES 1 + last) 3))|].
    apply compress_block_pending_mono. }
  cbv zeta. unfold send_all_trees.
  eapply Z.le_trans; [apply (proj1 (send_bits_pending_mono X (Z.shiftl DYN_TREES 1 + last) 3))|].
  eapply Z.le_trans; [| apply compress_block_pending_mono].
  eapply Z.le_trans; [| apply send_tree_pending_mono].
  eapply Z.le_trans; [| apply send_tree_pending_mono].
  eapply Z.le_trans; [| apply send_all_trees_loop_pending_mono].
  eapply Z.le_trans; [| apply (proj1 (send_bits_pending_mono _ _ _))].
  eapply Z.le_trans; [| apply (proj1 (send_bits_pending_mono _ _ _))].
  apply (proj1 (send_bits_pending_mono _ _ _)).
Qed.
End Flush.

Theorem flush_block_rel : FLUSH_BLOCK_REL.
Proof.
  intros W C B bnd ms pm s1 s2 last R FE1 FE2 HS HW Hbs. cbv zeta.
  pose proof (tree_phase_rel W C B bnd ms pm s1 s2 last R FE1 FE2) as [R6 _ _ _ Emb].
  rewrite !tr_flush_block_eq. unfold tfb_pre.
  replace (0 <? ds_level s1) with true by (symmetry; apply Z.ltb_lt; pose proof (fe_level _ _ FE1); lia).
  replace (0 <? ds_level s2) with true by (symmetry; apply Z.ltb_lt; pose proof (fe_level _ _ FE2); lia).
  cbv zeta.
  change (tfb_X5 (tfb_X0 s1)) with (ov_X5 s1). change (tfb_X5 (tfb_X0 s2)) with (ov_X5 s2).
  change (tfb_mb (ov_X5 s1)) with (ov_mb s1). change (tfb_mb (ov_X5 s2)) with (ov_mb s2).
  change (tfb_X6 (ov_X5 s1) (ov_mb s1)) with (ov_X6 s1). change (tfb_X6 (ov_X5 s2) (ov_mb s2)) with (ov_X6 s2).
  rewrite Emb.
  assert (Ebuf : fb_buf s2 = fb_buf s1) by (unfold fb_buf; rewrite (rel_block_start _ _ _ _ _ _ _ _ R); reflexivity).
  assert (Elen : fb_len s2 = fb_len s1) by (unfold fb_len; rewrite (rel_block_start _ _ _ _ _ _ _ _ R), (rel_strstart _ _ _ _ _ _ _ _ R); reflexivity).
  rewrite Ebuf, Elen.
  assert (Ebr : tfb_branch (ov_X6 s2) (fb_buf s1) (fb_len s1) = tfb_branch (ov_X6 s1) (fb_buf s1) (fb_len s1)).
  { unfold tfb_branch. pose proof (r_clean _ _ _ _ _ _ _ _ R6) as EC.
    rewrite (clean_eq_fieldT ds_opt_len _ _ EC), (clean_eq_fieldT ds_static_len _ _ EC), (clean_eq_fieldT ds_strategy _ _ EC) by reflexivity.
    reflexivity. }
  rewrite Ebr.
  pose proof (emit_rel W C B bnd ms pm s1 s2 last R FE1 FE2 HS HW Hbs) as RE. cbv zeta in RE.
  pose proof (fin_rel W C bnd ms pm last _ _ _ RE) as RF.
  eapply rel_Bx_merge; [exact RF|].
  split; [| apply (proj1 (fin_pending_mono _ _))].
  pose proof (proj1 (X6_facts s1 last FE1)) as P0. rewrite <- P0.
  apply tfb_emit_pending_mono. unfold fb_len. apply wrap64_range.
Qed.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require  DeflateTaintBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem flush_block_rel_blk : DeflateTaintBlk.FLUSH_BLOCK_REL.
Proof. exact flush_block_rel. Qed.
