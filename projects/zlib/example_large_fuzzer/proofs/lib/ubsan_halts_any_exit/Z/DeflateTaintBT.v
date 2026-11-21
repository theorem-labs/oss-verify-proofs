(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
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

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


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
