(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState DeflateOverlay OverlayBlock OverlayFacts OverlayLarge.

Module RefDeflSafeO3.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeO2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeO2.RefDeflSafeO1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeO2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GTree.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Variable Wg : Z -> Z.
Local Notation E := (sd_elems t).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.
Hypothesis GF : greedy_facts t FC2 L FCf HPf Wg.

Definition gtree_of : gtree :=
  {| g_lo := HM L; g_hi := 572; g_par := par t L HPf; g_leaf := leafb t HPf; g_code := nd HPf;
     g_wt := fun i => Wg (nd HPf i); g_ext := fun i => 572 - i |}.

Let RHM : 2 <= HM L <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.
Let RE : 19 <= E <= 286 := proj1 (elems_range t).

Lemma round_of : forall i, HM L < i < 573 ->
  let k := (572 - i) / 2 + 1 in 1 <= k <= L - 1 /\ (i = 574 - 2 * k \/ i = 573 - 2 * k) /\ dadid t i = E + k - 1.
Proof. intros i Hi. unfold dadid, RefDeflSafeB3.HM in *. cbv zeta. Z.to_euclidean_division_equations; lia. Qed.

Lemma children_of_round : forall k c, 1 <= k <= L - 1 -> HM L < c < 573 ->
  (par t L HPf c = posof L HPf (E + k - 1) <-> (c = 574 - 2 * k \/ c = 573 - 2 * k)).
Proof.
  intros k c Hk Hc.
  destruct (hr_cov _ _ _ _ _ _ _ _ _ HR (E + k - 1) ltac:(unfold Vj; right; lia)) as (p & Hp & Ep).
  assert (Pp : posof L HPf (E + k - 1) = p) by (rewrite <- Ep; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail, RefDeflSafeB3.HM in *; lia).
  rewrite Pp. rewrite (children_internal _ _ _ _ _ _ _ _ _ HR p c) by (unfold tail, nd, RefDeflSafeB3.HM in *; try lia; rewrite Ep; lia).
  unfold nd. rewrite Ep. lia.
Qed.

Theorem gtree_of_ok : gtree_ok gtree_of.
Proof.
  pose proof GF as [WL WF WN ND NM MIN].
  assert (TAILV : forall i, HM L <= i < 573 -> (0 <= nd HPf i < E /\ arr_get FC2 (nd HPf i) <> 0) \/ (E <= nd HPf i < E + L - 1)).
  { intros i Hi. exact (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)). }
  constructor; cbn [g_lo g_hi g_par g_leaf g_code g_wt g_ext gtree_of]; unfold g_pos; cbn [g_lo g_hi gtree_of].
  - lia.
  - intros i Hi. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (A & B & _). unfold tail in A. lia.
  - intros i Hi. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (_ & _ & _ & D). unfold leafb. apply Z.ltb_ge. exact D.
  - intros p Hp Hl. unfold leafb in Hl. apply Z.ltb_ge in Hl.
    assert (Rnd : E <= nd HPf p < E + L - 1).
    { destruct (Z.eq_dec p (HM L)) as [->|Np].
      - unfold nd, RefDeflSafeB3.HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). lia.
      - destruct (TAILV p ltac:(lia)) as [[A _]|A]; lia. }
    set (k := nd HPf p - E + 1).
    assert (Pp : posof L HPf (E + k - 1) = p) by (subst k; replace (E + (nd HPf p - E + 1) - 1) with (nd HPf p) by lia; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail; lia).
    exists (574 - 2 * k), (573 - 2 * k). unfold RefDeflSafeB3.HM in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite <- Pp; apply (proj2 (children_of_round k (574 - 2 * k) ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia))); left; reflexivity|].
    split; [rewrite <- Pp; apply (proj2 (children_of_round k (573 - 2 * k) ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia))); right; reflexivity|].
    intros c Hc Pc. rewrite <- Pp in Pc. exact (proj1 (children_of_round k c ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia)) Pc).
  - intros i Hi Hl. unfold leafb in Hl. apply Z.ltb_lt in Hl.
    assert (NZ : arr_get FC2 (nd HPf i) <> 0).
    { destruct (Z.eq_dec i (HM L)) as [->|Ni]; [unfold nd, RefDeflSafeB3.HM in Hl; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Hl; lia|].
      destruct (TAILV i ltac:(lia)) as [[_ A]|A]; [exact A | lia]. }
    pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)).
    rewrite (WL (nd HPf i)) by (unfold nd in *; lia). pose proof (WN (nd HPf i)) as X. rewrite (WL (nd HPf i)) in X by (unfold nd in *; lia). lia.
  - intros p a b Hp Hl Ha Hb Nab Pa Pb. unfold leafb in Hl. apply Z.ltb_ge in Hl.
    assert (Rnd : E <= nd HPf p < E + L - 1).
    { destruct (Z.eq_dec p (HM L)) as [->|Np].
      - unfold nd, RefDeflSafeB3.HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). lia.
      - destruct (TAILV p ltac:(lia)) as [[A _]|A]; lia. }
    set (k := nd HPf p - E + 1) in *.
    assert (Pp : posof L HPf (E + k - 1) = p) by (subst k; replace (E + (nd HPf p - E + 1) - 1) with (nd HPf p) by lia; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail; lia).
    rewrite <- Pp in Pa, Pb.
    apply (proj1 (children_of_round k a ltac:(lia) ltac:(lia))) in Pa. apply (proj1 (children_of_round k b ltac:(lia) ltac:(lia))) in Pb.
    replace (nd HPf p) with (E + k - 1) by lia. rewrite (ND k) by lia.
    destruct Pa as [-> | ->]; destruct Pb as [-> | ->]; unfold nd in *; lia.
  - intros i j Hi Hj Li Lj Eq. apply (hr_inj _ _ _ _ _ _ _ _ _ HR i j); unfold RefDeflSafeB3.HM in *; [lia | lia | exact Eq].
  - intros i j Hi Hj Eq. lia.
  - intros i Hi. lia.
  - intros a b Ha Hb Nab Pab.
    destruct (par_spec _ _ _ _ _ _ _ _ _ HR a ltac:(lia)) as (Ta & _ & Nda & Ia).
    pose proof (round_of a ltac:(lia)) as (Ka & Ca & Da). cbv zeta in Ka, Ca, Da. set (k := (572 - a) / 2 + 1) in *.
    assert (Ppar : par t L HPf a = posof L HPf (E + k - 1)).
    { rewrite <- Da, <- Nda. symmetry. apply (posof_nd _ _ _ _ _ _ _ _ _ HR). exact Ta. }
    rewrite Pab in Ppar. pose proof (proj1 (children_of_round k b Ka ltac:(lia)) Ppar) as Cb. lia.
  - intros i Hi Hp. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (_ & B & _). lia.
  -
    intros i x Hi Hx Hext ALIVE.
    pose proof (round_of i ltac:(lia)) as (Ki & Ci & Di). cbv zeta in Ki, Ci, Di. set (k := (572 - i) / 2 + 1) in *. clearbody k.
    assert (AL : nd HPf x < E + k - 1 \/ (nd HPf x = E + k - 1 /\ i = 573 - 2 * k)).
    { destruct ALIVE as [Lx | (c & Hc & Pc & Ec)].
      - left. unfold leafb in Lx. apply Z.ltb_lt in Lx. lia.
      - destruct (par_spec _ _ _ _ _ _ _ _ _ HR c ltac:(lia)) as (Tc & _ & Ndc & Ic). rewrite Pc in Ndc, Tc.
        pose proof (round_of c ltac:(lia)) as (Kc & Cc & Dc). cbv zeta in Kc, Cc, Dc. rewrite Ndc, Dc.
        unfold RefDeflSafeB3.HM in *. Z.to_euclidean_division_equations; lia. }
    destruct AL as [LT | [EQ ->]].
    + destruct Ci as [-> | ->].
      * destruct (Z.eq_dec x (573 - 2 * k)) as [->|Nx]; [apply NM; exact Ki|].
        exact (proj1 (MIN k x Ki ltac:(unfold RefDeflSafeB3.HM in *; lia) LT)).
      * exact (proj2 (MIN k x Ki ltac:(unfold RefDeflSafeB3.HM in *; lia) LT)).
    + rewrite EQ, (ND k Ki). pose proof (WN (arr_get HPf (574 - 2 * k))). unfold nd in *. lia.
Qed.
End GTree.


Section BuildTree.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Hypothesis HP : bt_pre s t.
Hypothesis WB : zsum (fun u => arr_get (tree_fc s t) u) 0 (Z.to_nat E) + 2 < 2 ^ 16.

Theorem build_tree_greedy :
  let s0 := set_heap_max (set_heap_len s 0) HEAP_SIZE in
  let p1 := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
  let p2 := build_tree_loop2 2%nat (fst p1) t (snd p1) in
  let mc := snd p2 in
  let s3 := set_max_code (fst p2) t mc in
  let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
  let s5 := build_tree_loop4 573%nat s4 t E in
  let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
  let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
  exists Fl DL2 L FCf DLf HPf DPf Wg,
    let FC2 := fc_forced Fl (tree_fc s t) in
    s7 = bt_upd s t FCf DLf HPf 1 (574 - 2 * L) DPf (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) mc
    /\ heap_result t FC2 DL2 L mc FCf DLf HPf DPf
    /\ greedy_facts t FC2 L FCf HPf Wg
    /\ gtree_ok (gtree_of t L HPf Wg)
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get (tree_fc s t) f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get (tree_fc s t) i).
Proof.
  pose proof (heap_phase_s s t HP) as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  cbv zeta.
  pose proof E7 as E7'. rewrite E3 in E7'.
  destruct (heap_phase_o s t (tree_fc s t) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (snd (build_tree_loop2 2 (fst (build_tree_loop1 (Z.to_nat E) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t E 0 (-1))) t (snd (build_tree_loop1 (Z.to_nat E) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t E 0 (-1)))))
              Fl DL2 HP2 DP2 L FCf DLf HPf DPf E7' (hr_L _ _ _ _ _ _ _ _ _ HR) Z2 LHP2 LDP2 LDL2 (tree_lens_fc _ _ (bp_tl _ _ HP)) RDP2 RFC2 RDL2 LF FCE
              ltac:(intros i; pose proof (bp_fc _ _ HP i); lia) WB) as [Wg GF].
  exists Fl, DL2, L, FCf, DLf, HPf, DPf, Wg.
  split; [exact E7|]. split; [exact HR|]. split; [exact GF|]. split; [exact (gtree_of_ok t _ DL2 L _ FCf DLf HPf DPf Wg HR GF)|].
  split; [exact LF|]. split; [exact ND|]. split; [exact FF | exact FCE].
Qed.
End BuildTree.
End RefDeflSafeO3.

Module RefDeflSafeO4.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tail3.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Local Notation HM := (HM L).
Local Notation C := (C t L HPf).
Local Notation leafb := (leafb t HPf).
Local Notation nd := (nd HPf).
Local Notation par := (par t L HPf).
Local Notation tail := (tail L).
Local Notation cntL := (cntL t L HPf).
Local Notation NI := (NI t L HPf 573).
Local Notation nleaf := (nleaf t L HPf).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.

Let RHM : 2 <= HM <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RML : 7 <= ML <= 15 /\ E <= 2 ^ ML := ML_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.


Fixpoint Df (f : nat) (i : Z) : Z :=
  match f with
  | O => 0
  | S f' => if i <=? HM then 0 else Df f' (par i) + 1
  end.
Definition D (i : Z) : Z := Df 573 i.

Lemma Df_stable : forall f g i, tail i -> (Z.to_nat (i - HM) < f)%nat -> (Z.to_nat (i - HM) < g)%nat -> Df f i = Df g i.
Proof.
  induction f as [|f IH]; intros g i Hi Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. cbn [Df].
  destruct (Z.leb_spec i HM) as [Le|Gt]; [reflexivity|].
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail in Hi; lia)) as (A & B & _).
  rewrite (IH g (par i) A); [reflexivity | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma Df_S : forall f i, Df (S f) i = if i <=? HM then 0 else Df f (par i) + 1.
Proof. reflexivity. Qed.

Lemma D_root : D HM = 0.
Proof. unfold D. change 573%nat with (S 572). rewrite Df_S. rewrite Z.leb_refl. reflexivity. Qed.

Lemma D_step : forall i, HM < i < 573 -> D i = D (par i) + 1.
Proof.
  intros i Hi. unfold D. change 573%nat with (S 572). rewrite Df_S.
  replace (i <=? HM) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i Hi) as (A & B & _).
  rewrite (Df_stable 572 573 (par i) A); [reflexivity | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma Df_nonneg : forall f i, 0 <= Df f i.
Proof. induction f as [|f IH]; intros i; cbn [Df]; [lia|]. destruct (i <=? HM); [lia|]. pose proof (IH (par i)). lia. Qed.

Lemma D_nonneg : forall i, 0 <= D i.
Proof. intros i. apply Df_nonneg. Qed.

Lemma D_le : forall n i, tail i -> (Z.to_nat (i - HM) <= n)%nat -> D i <= i - HM.
Proof.
  induction n as [|n IH]; intros i Hi Hn.
  - assert (i = HM) by (unfold RefDeflSafeB3.tail in Hi; lia). subst i. rewrite D_root. lia.
  - destruct (Z.eq_dec i HM) as [->|N]; [rewrite D_root; lia|].
    unfold RefDeflSafeB3.tail in Hi. rewrite D_step by lia.
    destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (A & B & _).
    pose proof (IH (par i) A ltac:(unfold RefDeflSafeB3.tail in A; lia)). unfold RefDeflSafeB3.tail in A. lia.
Qed.

Lemma C_min : forall n i, tail i -> (Z.to_nat (i - HM) <= n)%nat -> C i = Z.min (D i) ML.
Proof.
  induction n as [|n IH]; intros i Hi Hn.
  - assert (i = HM) by (unfold RefDeflSafeB3.tail in Hi; lia). subst i. rewrite D_root, (C_root t L HPf). lia.
  - destruct (Z.eq_dec i HM) as [->|N]; [rewrite D_root, (C_root t L HPf); lia|].
    unfold RefDeflSafeB3.tail in Hi. rewrite D_step by lia. rewrite (C_step _ _ _ _ _ _ _ _ _ HR) by lia.
    destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (A & B & _).
    rewrite (IH (par i) A ltac:(unfold RefDeflSafeB3.tail in A; lia)). pose proof (D_nonneg (par i)). lia.
Qed.

Lemma C_min' : forall i, tail i -> C i = Z.min (D i) ML.
Proof. intros i Hi. apply (C_min (Z.to_nat (i - HM))); [exact Hi | lia]. Qed.

Lemma internal_deeper : forall n p, tail p -> leafb p = false -> (Z.to_nat (573 - p) <= n)%nat ->
  exists l, HM < l < 573 /\ leafb l = true /\ D p < D l.
Proof.
  induction n as [|n IH]; intros p Hp Hl Hn; [unfold RefDeflSafeB3.tail in Hp; lia|].
  unfold RefDeflSafeB3.leafb in Hl. apply Z.ltb_ge in Hl.
  destruct (children_pos _ _ _ _ _ _ _ _ _ HR p Hp Hl) as (A & B & Cq).
  set (c := 571 - 2 * (nd p - E)) in *.
  assert (Pc : par c = p) by (apply (proj2 (children_internal _ _ _ _ _ _ _ _ _ HR p c Hp Hl ltac:(lia))); right; reflexivity).
  pose proof (D_step c ltac:(lia)) as Dc. rewrite Pc in Dc.
  destruct (leafb c) eqn:Lc.
  - exists c. split; [lia|]. split; [exact Lc | lia].
  - destruct (IH c ltac:(unfold RefDeflSafeB3.tail; lia) Lc ltac:(lia)) as (l & Hl1 & Hl2 & Hl3).
    exists l. split; [exact Hl1|]. split; [exact Hl2 | lia].
Qed.

Lemma noovf_NI : (forall i, HM < i < 573 -> leafb i = true -> D i <= ML) -> NI = 0.
Proof.
  intros H. unfold RefDeflSafeB3.NI. apply zsum_0. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (C i) ML) as [EQ|NE]; [|reflexivity]. exfalso.
  rewrite C_min' in EQ by (unfold RefDeflSafeB3.tail; lia).
  destruct (internal_deeper (Z.to_nat (573 - i)) i ltac:(unfold RefDeflSafeB3.tail; lia) Li ltac:(lia)) as (l & Hl1 & Hl2 & Hl3).
  pose proof (H l Hl1 Hl2). lia.
Qed.

Lemma NI0_depth : NI = 0 -> forall i, tail i -> D i <= ML.
Proof.
  intros H i Hi.
  destruct (Z_lt_le_dec ML (D i)) as [LT|]; [|assumption]. exfalso.
  assert (UP : forall n j, tail j -> (Z.to_nat (j - HM) <= n)%nat -> ML < D j -> exists a, HM < a < 573 /\ leafb a = false /\ D a = ML).
  { induction n as [|n IH]; intros j Hj Hn Dj.
    - assert (j = HM) by (unfold RefDeflSafeB3.tail in Hj; lia). subst j. rewrite D_root in Dj. lia.
    - destruct (Z.eq_dec j HM) as [->|N]; [rewrite D_root in Dj; lia|].
      unfold RefDeflSafeB3.tail in Hj. rewrite D_step in Dj by lia.
      destruct (par_spec _ _ _ _ _ _ _ _ _ HR j ltac:(lia)) as (A & B & _ & Dg).
      destruct (Z.eq_dec (D (par j)) ML) as [EQ|NE].
      + exists (par j). unfold RefDeflSafeB3.tail in A. split; [| split; [unfold RefDeflSafeB3.leafb; apply Z.ltb_ge; exact Dg | exact EQ]].
        destruct (Z.eq_dec (par j) HM) as [Ep|]; [| lia]. rewrite Ep, D_root in EQ. lia.
      + apply (IH (par j) A ltac:(unfold RefDeflSafeB3.tail in A; lia)). lia. }
  destruct (UP (Z.to_nat (i - HM)) i Hi ltac:(lia) LT) as (a & Ha & La & Da).
  assert (X : zind (negb (leafb a) && (C a =? ML)) <= NI).
  { unfold RefDeflSafeB3.NI. apply (zsum_ge_point (fun i0 => zind (negb (leafb i0) && (C i0 =? ML))) (HM + 1) (Z.to_nat (573 - HM - 1)) a).
    - intros; apply (proj1 (zind_le1 _)).
    - lia. }
  rewrite La, (C_min' a), Da, Z.min_id, Z.eqb_refl in X by (unfold RefDeflSafeB3.tail; lia). cbn in X. lia.
Qed.



Lemma find_agree : forall f X (c : Z -> Z) b,
  (forall j, b - Z.of_nat f < j <= b -> bl_count_get X j = c j) ->
  gen_bitlen_find f X b = rep_find f c b.
Proof.
  induction f as [|f IH]; intros X c b H; cbn [gen_bitlen_find rep_find]; [reflexivity|].
  rewrite H by lia. destruct (c b =? 0); [| reflexivity]. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma adj_rep_step : forall (c : Z -> Z) r b, 1 <= r <= ML - 1 -> adj t c r b = rep_step ML c r b.
Proof.
  intros c r b Hr. unfold adj, rep_step.
  destruct (Z.eqb_spec b ML) as [->|N1].
  - replace (ML =? r) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec (r + 1) ML) as [E1|N2].
    + rewrite <- E1, Z.eqb_refl. lia.
    + replace (ML =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (Z.eqb_spec b (r + 1)) as [->|N2].
    + replace (r + 1 =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + destruct (Z.eqb_spec b r) as [->|]; reflexivity.
Qed.

Lemma rep_iter_S : forall n MLx h, rep_iter (S n) MLx h = rep_iter n MLx (rep_step MLx h (rep_find (Z.to_nat MLx) h (MLx - 1))).
Proof. reflexivity. Qed.

Lemma loop2_exact : forall f k s FC DL HP HL HMx DP BC OL SL MC (c : Z -> Z),
  (Z.of_nat f >= k) -> 1 <= k ->
  L2I t L HPf c (2 * k) -> (forall b, 0 <= b < 16 -> arr_get BC b = c b) -> arr_len BC = 16 ->
  let X := bt_upd s t FC DL HP HL HMx DP BC OL SL MC in
  exists BC',
    gen_bitlen_loop2 f X ML (2 * k) = bt_upd s t FC DL HP HL HMx DP BC' OL SL MC
    /\ (forall b, 0 <= b < 16 -> arr_get BC' b = rep_iter (Z.to_nat k) ML c b)
    /\ L2I t L HPf (rep_iter (Z.to_nat k) ML c) 0 /\ arr_len BC' = 16.
Proof.
  induction f as [|f IH]; intros k s FC DL HP HL HMx DP BC OL SL MC c Hf Hk HI HBC LBC; [lia|]. cbv zeta.
  rewrite (GL2_step t ML). cbv zeta.
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1)).
  destruct (L2_find _ _ _ _ _ _ _ _ _ HR c (2 * k) HI ltac:(lia)) as (r0 & Hr0 & Cr0).
  assert (Hr : r0 <= r <= ML - 1).
  { split; [| apply find_le]. apply find_ge; [lia|]. rewrite bt_bl_count_get. rewrite HBC by lia. exact Cr0. }
  assert (Cr : c r <> 0).
  { pose proof (find_nz (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1) ltac:(subst r; lia)) as X.
    rewrite bt_bl_count_get in X. fold r in X. rewrite HBC in X by lia. exact X. }
  assert (Er : r = rep_find (Z.to_nat ML) c (ML - 1)).
  { subst r. apply find_agree. intros j Hj. rewrite bt_bl_count_get. apply HBC. lia. }
  pose proof (L2_step _ _ _ _ _ _ _ _ _ HR c (2 * k) r HI ltac:(lia) ltac:(lia) Cr) as HI'.
  pose proof (bl_adj_get _ _ _ _ _ _ _ _ _ HR c (2 * k) BC r HI HBC LBC ltac:(lia) Cr ltac:(lia)) as AG.
  set (c1 := rep_step ML c (rep_find (Z.to_nat ML) c (ML - 1))).
  assert (AG1 : forall b, 0 <= b < 16 -> arr_get (bl_adj ML BC r) b = c1 b).
  { intros b Hb. rewrite (AG b Hb). subst c1. rewrite <- Er. apply adj_rep_step. lia. }
  assert (HI1 : L2I t L HPf c1 (2 * k - 2)).
  { apply (L2I_ext _ _ _ _ _ _ _ _ _ HR (adj t c r)); [exact HI'|]. intros b Hb. subst c1. rewrite <- Er. symmetry. apply adj_rep_step. lia. }
  assert (LBC' : arr_len (bl_adj ML BC r) = 16) by (unfold bl_adj; rewrite !arr_len_set; exact LBC).
  replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. rewrite rep_iter_S. fold c1.
  replace (2 * k - 2) with (2 * (k - 1)) in * by lia.
  destruct (Z.ltb_spec 0 (2 * (k - 1))) as [Ck|Ck].
  - destruct (IH (k - 1) s FC DL HP HL HMx DP (bl_adj ML BC r) OL SL MC c1 ltac:(lia) ltac:(lia) HI1 AG1 LBC') as (BC' & EQ & HB & HIf & LBCf).
    exists BC'. split; [exact EQ|]. split; [exact HB|]. split; [exact HIf | exact LBCf].
  - exists (bl_adj ML BC r). split; [reflexivity|].
    replace (Z.to_nat (k - 1)) with 0%nat by lia. cbn [rep_iter].
    replace (2 * (k - 1)) with 0 in HI1 by lia.
    split; [exact AG1|]. split; [exact HI1 | exact LBC'].
Qed.

Lemma KR_kraftZ_gen : forall c : Z -> Z, c 0 = 0 -> (forall b, ML < b < 16 -> c b = 0) -> KR t c = kraftZ ML c.
Proof.
  intros c Z0 HI. unfold KR, kraftZ.
  replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
  rewrite zsum_shift, Z0 by lia. rewrite zsum_split.
  rewrite (zsum_0 _ (0 + 1 + Z.of_nat (Z.to_nat ML))); [| intros b Hb; rewrite HI by lia; lia].
  replace (0 + 1) with 1 by lia. lia.
Qed.

Lemma KR_kraftZ : KR t cntL = kraftZ ML cntL.
Proof. apply KR_kraftZ_gen; [apply (cntL_zero _ _ _ _ _ _ _ _ _ HR); lia | intros; apply (cntL_zero _ _ _ _ _ _ _ _ _ HR); lia]. Qed.

Lemma NI_kraftZ : NI = kraftZ ML cntL - 2 ^ ML.
Proof. rewrite <- KR_kraftZ, (kraft_identity _ _ _ _ _ _ _ _ _ HR). lia. Qed.

Lemma repair_cntL : forall b, repair ML cntL b = rep_iter (Z.to_nat NI) ML cntL b.
Proof. intros b. unfold repair. rewrite NI_kraftZ. reflexivity. Qed.



Definition lcnt (DL : arr) (h b : Z) : Z :=
  zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) h (Z.to_nat (573 - h)).

Lemma lcnt_573 : forall DL b, lcnt DL 573 b = 0.
Proof. intros. unfold lcnt. reflexivity. Qed.

Lemma lcnt_step : forall DL h b, h <= 573 ->
  lcnt DL (h - 1) b = lcnt DL h b + zind (leafb (h - 1) && (arr_get DL (nd (h - 1)) =? b)).
Proof.
  intros DL h b Hh. unfold lcnt. replace (Z.to_nat (573 - (h - 1))) with (S (Z.to_nat (573 - h))) by lia.
  rewrite zsum_shift. replace (h - 1 + 1) with h by lia. lia.
Qed.

Lemma lcnt_ext : forall DL DL' h b, (forall i, h <= i < 573 -> leafb i = true -> arr_get DL' (nd i) = arr_get DL (nd i)) ->
  lcnt DL' h b = lcnt DL h b.
Proof.
  intros DL DL' h b H. unfold lcnt. apply zsum_ext. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [andb]; [|reflexivity]. rewrite H by (try exact Li; lia). reflexivity.
Qed.

Lemma lcnt_zero : forall DL h b, (forall i, h <= i < 573 -> leafb i = true -> arr_get DL (nd i) <> b) -> lcnt DL h b = 0.
Proof.
  intros DL h b H. unfold lcnt. apply zsum_0. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [andb]; [|reflexivity].
  destruct (Z.eqb_spec (arr_get DL (nd i)) b) as [Eb|Nb]; [|reflexivity]. exfalso. apply (H i ltac:(lia) Li Eb).
Qed.

Lemma lcnt_nonneg : forall DL h b, 0 <= lcnt DL h b.
Proof. intros. unfold lcnt. apply zsum_nonneg. intros; apply (proj1 (zind_le1 _)). Qed.

Record RK (DL : arr) (bits n h : Z) (BCf : Z -> Z) : Prop := {
  rk_h : HM + 1 <= h <= 573;
  rk_rng : forall i, h <= i < 573 -> leafb i = true -> bits <= arr_get DL (nd i) <= ML;
  rk_mono : forall p q, h <= q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DL (nd q) <= arr_get DL (nd p);
  rk_above : forall b, bits < b <= ML -> lcnt DL h b = BCf b;
  rk_at : bits <= ML -> lcnt DL h bits = BCf bits - n }.

Lemma loop3i_rank : forall f s DL BC (B : Z) OL SL bits n h BCf,
  (Z.of_nat f >= h - HM) -> HM + 1 <= h <= 573 -> 0 <= n <= nleaf h -> 1 <= bits <= ML ->
  DLI t FC2 L HPf DL -> OL = wrap64 (B + S_opt t FC2 L HPf DL) -> RK DL bits n h BCf ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL' h',
    gen_bitlen_loop3i f X t mc bits n h = (bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc, h')
    /\ HM + 1 <= h' <= h /\ nleaf h' = nleaf h - n
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (B + S_opt t FC2 L HPf DL')
    /\ RK DL' bits 0 h' BCf.
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits n h BCf Hf Hh Hn Hbits HDL HOL HRK; cbv zeta.
  - exists DL, OL, h. cbn [gen_bitlen_loop3i]. assert (n = 0 \/ h = HM) by lia.
    pose proof (nleaf_base t L HPf). destruct H as [-> | ->]; [|exfalso; lia].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact HRK].
  - rewrite (GL3i_step t mc).
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    + exists DL, OL, h. subst n. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact HRK].
    + assert (Hh1 : HM + 1 <= h - 1).
      { destruct (Z_lt_le_dec (HM + 1) h) as [|C0]; [lia|]. exfalso. replace h with (HM + 1) in Hn by lia. rewrite (nleaf_base t L HPf) in Hn. lia. }
      pose proof (elems_range t) as RE. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
      assert (Th : tail (h - 1)) by (unfold RefDeflSafeB3.tail; lia).
      pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as NC. pose proof (leaf_mc _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as LM.
      pose proof (nleaf_step t L HPf (h - 1) ltac:(lia)) as NS. replace (h - 1 + 1) with h in NS by lia.
      rewrite (GB3i_flat t mc). cbv zeta. change (arr_get HPf (h - 1)) with (nd (h - 1)).
      destruct (Z.ltb_spec mc (nd (h - 1))) as [Ci|Cl].
      *
        assert (Lf : leafb (h - 1) = false) by (unfold RefDeflSafeB3.leafb; apply Z.ltb_ge; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        assert (HRK' : RK DL bits n (h - 1) BCf).
        { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
          - lia.
          - intros i Hi Li. destruct (Z.eq_dec i (h - 1)) as [->|Ni]; [rewrite Lf in Li; discriminate|]. apply R2; [lia | exact Li].
          - intros p q Hq Hqp Hp Lp Lq. destruct (Z.eq_dec q (h - 1)) as [->|Nq]; [rewrite Lf in Lq; discriminate|]. apply R3; try assumption; lia.
          - intros b Hb. rewrite lcnt_step, Lf by lia. cbn [andb zind]. rewrite R4 by lia. lia.
          - intros Hb. rewrite lcnt_step, Lf by lia. cbn [andb zind]. rewrite R5 by lia. lia. }
        destruct (IH s DL BC B OL SL bits n (h - 1) BCf ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
        exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
      * assert (Lf : leafb (h - 1) = true) by (unfold RefDeflSafeB3.leafb; apply Z.ltb_lt; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        set (DL1 := if arr_get DL (nd (h - 1)) =? bits then DL else arr_set DL (nd (h - 1)) (wrap16 bits)).
        assert (G1 : arr_get DL1 (nd (h - 1)) = bits).
        { subst DL1. destruct (Z.eqb_spec (arr_get DL (nd (h - 1))) bits) as [Eb|Nb]; [exact Eb|].
          rewrite arr_get_set, Z.eqb_refl. unfold arr_inb. rewrite (dli_len _ _ _ _ _ HDL).
          replace ((0 <=? nd (h - 1)) && (nd (h - 1) <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. apply wrap16_id. pose proof RML. lia. }
        assert (G2 : forall i, h <= i < 573 -> arr_get DL1 (nd i) = arr_get DL (nd i)).
        { intros i Hi. subst DL1. destruct (arr_get DL (nd (h - 1)) =? bits); [reflexivity|].
          rewrite arr_get_set. replace (nd (h - 1) =? nd i) with false; [reflexivity|].
          symmetry. apply Z.eqb_neq. intros EQ. pose proof (hr_inj _ _ _ _ _ _ _ _ _ HR (h - 1) i ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.HM in *; lia) EQ). lia. }
        assert (HRK' : RK DL1 bits (n - 1) (h - 1) BCf).
        { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
          - lia.
          - intros i Hi Li. destruct (Z.eq_dec i (h - 1)) as [->|Ni]; [rewrite G1; lia|]. rewrite G2 by lia. apply R2; [lia | exact Li].
          - intros p q Hq Hqp Hp Lp Lq. rewrite (G2 p) by lia.
            destruct (Z.eq_dec q (h - 1)) as [->|Nq]; [rewrite G1; pose proof (R2 p ltac:(lia) Lp); lia|].
            rewrite (G2 q) by lia. apply R3; try assumption; lia.
          - intros b Hb. rewrite lcnt_step, Lf, G1 by lia. rewrite (lcnt_ext DL DL1 h b) by (intros; apply G2; lia).
            replace (bits =? b) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb zind]. rewrite R4 by lia. lia.
          - intros Hb. rewrite lcnt_step, Lf, G1, Z.eqb_refl by lia. rewrite (lcnt_ext DL DL1 h bits) by (intros; apply G2; lia).
            cbn [andb zind]. rewrite R5 by lia. lia. }
        destruct (Z.eqb_spec (arr_get DL (nd (h - 1))) bits) as [Eb|Nb].
        -- assert (E1 : DL1 = DL) by (subst DL1; first [reflexivity | rewrite (proj2 (Z.eqb_eq _ _) Eb); reflexivity]).
           rewrite E1 in HRK'.
           destruct (IH s DL BC B OL SL bits (n - 1) (h - 1) BCf ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
        -- assert (E1 : DL1 = arr_set DL (nd (h - 1)) (wrap16 bits)) by (subst DL1; first [reflexivity | rewrite (proj2 (Z.eqb_neq _ _) Nb); reflexivity]).
           rewrite E1 in HRK'.
           assert (HDL' : DLI t FC2 L HPf (arr_set DL (nd (h - 1)) (wrap16 bits))).
           { destruct HDL as [A0 B0 Cq D0]. constructor.
             - intros i Hi Li. rewrite arr_get_set. destruct (_ && _); [rewrite wrap16_id by lia; lia | apply A0; assumption].
             - intros u Hu Fu. rewrite arr_get_set. destruct (Z.eqb_spec (nd (h - 1)) u) as [Eu|Nu]; cbn [andb]; [| apply B0; assumption].
               exfalso. rewrite <- Eu in Fu. destruct NC as [[_ X]|X]; [exact (X Fu) | lia].
             - rewrite arr_len_set. exact Cq.
             - intros u. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply D0]. }
           assert (HOL' : wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1))) = wrap64 (B + S_opt t FC2 L HPf (arr_set DL (nd (h - 1)) (wrap16 bits)))).
           { rewrite HOL, wrap64_add_l. rewrite (S_opt_set _ _ _ _ _ _ _ _ _ HR DL (h - 1) bits) by (try lia; try exact Lf; apply (dli_len _ _ _ _ _ HDL)).
             rewrite (hr_fc _ _ _ _ _ _ _ _ _ HR) by lia. f_equal. lia. }
           destruct (IH s (arr_set DL (nd (h - 1)) (wrap16 bits)) BC B (wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1)))) SL bits (n - 1) (h - 1) BCf
                     ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL' HOL' HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
Qed.

Lemma loop3_rank : forall f s DL BC B OL SL bits h BCf,
  (Z.of_nat f >= bits) -> 0 <= bits <= ML -> HM + 1 <= h <= 573 ->
  zsum (arr_get BC) 1 (Z.to_nat bits) <= nleaf h -> (forall b, 1 <= b <= ML -> 0 <= arr_get BC b) ->
  (forall b, 1 <= b <= ML -> arr_get BC b = BCf b) ->
  DLI t FC2 L HPf DL -> OL = wrap64 (B + S_opt t FC2 L HPf DL) -> RK DL (bits + 1) 0 h BCf ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL' h',
    gen_bitlen_loop3 f X t mc bits h = bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (B + S_opt t FC2 L HPf DL')
    /\ RK DL' 1 0 h' BCf /\ nleaf h' = nleaf h - zsum (arr_get BC) 1 (Z.to_nat bits).
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits h BCf Hf Hbits Hh Hdem Hnn HBC HDL HOL HRK; cbv zeta.
  - exists DL, OL, h. cbn [gen_bitlen_loop3]. assert (B0 : bits = 0) by lia. subst bits. cbn in HRK. change (zsum (arr_get BC) 1 (Z.to_nat 0)) with 0.
    split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL|]. split; [exact HRK | lia].
  - rewrite (GL3_step t mc). rewrite bt_bl_count_get.
    destruct (Z.eqb_spec bits 0) as [B0|B0]; cbn [negb].
    + exists DL, OL, h. subst bits. cbn in HRK. change (zsum (arr_get BC) 1 (Z.to_nat 0)) with 0. split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL|]. split; [exact HRK | lia].
    + assert (Hc : 0 <= arr_get BC bits <= nleaf h).
      { pose proof (Hnn bits ltac:(lia)). split; [lia|].
        pose proof (zsum_ge_point (arr_get BC) 1 (Z.to_nat bits) bits ltac:(intros; apply Hnn; lia) ltac:(lia)). lia. }
      assert (HRKi : RK DL bits (arr_get BC bits) h BCf).
      { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
        - exact R1.
        - intros i Hi Li. pose proof (R2 i Hi Li). lia.
        - exact R3.
        - intros b Hb. destruct (Z.eq_dec b (bits + 1)) as [->|Nb]; [rewrite R5 by lia; lia | apply R4; lia].
        - intros _. rewrite HBC by lia. rewrite lcnt_zero; [lia|]. intros i Hi Li. pose proof (R2 i Hi Li). lia. }
      destruct (loop3i_rank 574 s DL BC B OL SL bits (arr_get BC bits) h BCf ltac:(lia) Hh Hc ltac:(lia) HDL HOL HRKi)
        as (DL1 & OL1 & h1 & EQ1 & R1 & R2 & R3 & R4 & R5).
      rewrite EQ1.
      destruct (IH s DL1 BC B OL1 SL (bits - 1) h1 BCf ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & h' & EQ & D' & O' & K' & N'); try assumption.
      { replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) in Hdem by lia. rewrite zsum_snoc in Hdem.
        replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits in Hdem by lia. lia. }
      { replace (bits - 1 + 1) with bits by lia. exact R5. }
      exists DL', OL', h'. split; [exact EQ|]. split; [exact D'|]. split; [exact O'|]. split; [exact K'|].
      rewrite N', R2. replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) by lia. rewrite zsum_snoc.
      replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits by lia. lia.
Qed.



Lemma lcnt_noleaf : forall DL h' b, HM + 1 <= h' <= 573 -> nleaf h' = 0 -> lcnt DL (HM + 1) b = lcnt DL h' b.
Proof.
  intros DL h' b Hh Hn. unfold lcnt.
  replace (Z.to_nat (573 - (HM + 1))) with (Z.to_nat (h' - HM - 1) + Z.to_nat (573 - h'))%nat by lia.
  rewrite zsum_split. replace (HM + 1 + Z.of_nat (Z.to_nat (h' - HM - 1))) with h' by lia.
  assert (A : 0 <= zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) (HM + 1) (Z.to_nat (h' - HM - 1))).
  { apply zsum_nonneg. intros; apply (proj1 (zind_le1 _)). }
  assert (B : zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) (HM + 1) (Z.to_nat (h' - HM - 1)) <= nleaf h').
  { unfold RefDeflSafeB4.nleaf. apply zsum_mono. intros i Hi. destruct (leafb i), (arr_get DL (nd i) =? b); cbn; lia. }
  lia.
Qed.

Lemma noleaf_below : forall h' q, HM + 1 <= h' -> nleaf h' = 0 -> HM < q < h' -> leafb q = true -> False.
Proof.
  intros h' q Hh Hn Hq Lq.
  pose proof (zsum_ge_point (fun i => zind (leafb i)) (HM + 1) (Z.to_nat (h' - HM - 1)) q ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(lia)) as X.
  unfold RefDeflSafeB4.nleaf in Hn. cbv beta in X. rewrite Lq in X. cbn [zind] in X. lia.
Qed.

Theorem gen_bitlen_exact : forall s BC OL SL,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  let s7 := bt_upd s t FCf DLf HPf 1 HM DPf BC OL SL mc in
  exists DL' BC' OL' SL',
    gen_bitlen s7 t = bt_upd s t FCf DL' HPf 1 HM DPf BC' OL' SL' mc
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (OL + S_opt t FC2 L HPf DL') /\ SL' = (if stree_has t then wrap64 (SL + S_stat t FC2 L HPf) else SL)
    /\ arr_len BC' = 16 /\ (forall b, 0 <= b < 16 -> 0 <= arr_get BC' b <= 572)
    /\ (NI = 0 -> forall i, HM < i < 573 -> arr_get DL' (nd i) = D i)
    /\ (forall b, 1 <= b <= ML -> lcnt DL' (HM + 1) b = repair ML cntL b)
    /\ kraftZ ML (fun b => lcnt DL' (HM + 1) b) = 2 ^ ML
    /\ (NI <> 0 -> forall p q, HM < q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DL' (nd q) <= arr_get DL' (nd p)).
Proof.
  intros s BC OL SL LBC HOL HSL. cbv zeta.
  unfold gen_bitlen. autorewrite with btupd.
  set (s9 := bt_upd s t FCf (arr_set DLf (arr_get HPf HM) (wrap16 0)) HPf 1 HM DPf (arr_fill BC 0 (MAX_BITS + 1) 0) OL SL mc) in *.
  pose proof (L1_init _ _ _ _ _ _ _ _ _ HR s BC OL SL LBC HOL HSL) as I0. fold s9 in I0.
  pose proof (L1_run _ _ _ _ _ _ _ _ _ HR 573 s BC OL SL (HM + 1) s9 0 I0 ltac:(lia)) as [I1 G1].
  destruct (gen_bitlen_loop1 573 s9 t mc (sd_extra_base t) ML (HM + 1) 0) as [X10 ovf] eqn:ER1. cbn [fst snd] in I1.
  destruct I1 as [Hh (DL10 & BC10 & OL10 & SL10 & EX & HDL10 & LDL10 & HBC10 & LBC10 & HOL10 & HSL10) Hovf].
  replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in HBC10, HOL10, HSL10, Hovf by lia.
  assert (D10 : DLI t FC2 L HPf DL10) by (apply (DLI_pass1 _ _ _ _ _ _ _ _ _ HR); assumption).
  assert (O10 : OL10 = wrap64 (OL + S_opt t FC2 L HPf DL10)) by (rewrite HOL10, (S_opt_pass1 _ _ _ _ _ _ _ _ _ HR DL10 HDL10); reflexivity).
  assert (S10 : SL10 = (if stree_has t then wrap64 (SL + S_stat t FC2 L HPf) else SL)) by (rewrite HSL10; reflexivity).
  rewrite (ovf_identity _ _ _ _ _ _ _ _ _ HR) in Hovf.
  assert (C10 : forall i, tail i -> arr_get DL10 (nd i) = C i).
  { intros i Hi. rewrite HDL10. unfold dl_at. destruct (tid_nd _ _ _ _ _ _ _ _ _ HR i Hi) as [T P]. rewrite T, P.
    replace (i <? 573) with true by (symmetry; apply Z.ltb_lt; unfold RefDeflSafeB3.tail in Hi; lia). reflexivity. }
  assert (LC10 : forall b, lcnt DL10 (HM + 1) b = cntL b).
  { intros b. unfold lcnt, RefDeflSafeB3.cntL. replace (Z.to_nat (573 - (HM + 1))) with (Z.to_nat (572 - HM)) by lia.
    apply zsum_ext. intros i Hi. unfold w_cnt. rewrite C10 by (unfold RefDeflSafeB3.tail; lia). reflexivity. }
  assert (BCE : forall b, 0 <= b < 16 -> arr_get BC10 b = cntL b) by (intros b Hb; rewrite HBC10 by exact Hb; reflexivity).
  subst X10. destruct (Z.eqb_spec ovf 0) as [Z0|NZ].
  -
    assert (NI0 : NI = 0) by lia.
    exists DL10, BC10, OL10, SL10. split; [reflexivity|]. split; [exact D10|]. split; [exact O10|]. split; [exact S10|]. split; [exact LBC10|].
    split. { intros b Hb. rewrite BCE by exact Hb. pose proof (cnt_bound t L HPf b (HM + 1) (Z.to_nat (572 - HM))). unfold RefDeflSafeB3.cntL. lia. }
    split. { intros _ i Hi. rewrite C10 by (unfold RefDeflSafeB3.tail; lia). rewrite C_min' by (unfold RefDeflSafeB3.tail; lia).
             pose proof (NI0_depth NI0 i ltac:(unfold RefDeflSafeB3.tail; lia)). lia. }
    split. { intros b Hb. rewrite LC10, repair_cntL, NI0. reflexivity. }
    split. { unfold kraftZ. rewrite (zsum_ext (fun b => lcnt DL10 (HM + 1) b * 2 ^ (ML - b)) (fun b => cntL b * 2 ^ (ML - b))) by (intros; rewrite LC10; reflexivity).
             change (zsum (fun b : Z => cntL b * 2 ^ (ML - b)) 1 (Z.to_nat ML)) with (kraftZ ML cntL).
             rewrite <- KR_kraftZ, (kraft_identity _ _ _ _ _ _ _ _ _ HR), NI0. lia. }
    intros X. exfalso. exact (X NI0).
  -
    assert (HI : L2I t L HPf cntL (2 * NI)) by exact (L2_init _ _ _ _ _ _ _ _ _ HR).
    assert (NIB : 1 <= NI <= 570) by (pose proof (NI_bound _ _ _ _ _ _ _ _ _ HR); lia).
    rewrite Hovf.
    destruct (loop2_exact 573 NI s FCf DL10 HPf 1 HM DPf BC10 OL10 SL10 mc cntL ltac:(lia) ltac:(lia) HI BCE LBC10) as (BC' & EQ2 & HB' & HI2 & LBC').
    rewrite EQ2. unfold HEAP_SIZE.
    set (BCf := rep_iter (Z.to_nat NI) ML cntL) in *.
    pose proof HI2 as [NN Z0 HI0 _ TOT _ _].
    destruct (loop3_rank (Z.to_nat ML) s DL10 BC' OL OL10 SL10 ML 573 BCf ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & h' & EQ3 & D' & O' & K' & N'); try assumption.
    { rewrite <- TOT.
      replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
      rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
      rewrite (zsum_ext (arr_get BC') BCf 1 (Z.to_nat ML)) by (intros; apply HB'; lia).
      pose proof (zsum_nonneg BCf (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
    { intros b Hb. rewrite HB' by lia. apply NN. lia. }
    { intros b Hb. apply HB'. lia. }
    { constructor; [lia | intros; lia | intros; lia | intros; lia | intros; lia]. }
    assert (NL : nleaf h' = 0).
    { rewrite N'. rewrite (zsum_ext (arr_get BC') BCf 1 (Z.to_nat ML)) by (intros; apply HB'; lia).
      rewrite <- TOT. replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
      rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
      rewrite (zsum_0 BCf (1 + Z.of_nat (Z.to_nat ML))) by (intros; apply HI0; lia). lia. }
    pose proof (rk_h _ _ _ _ _ K') as Rh'.
    exists DL', BC', OL', SL10. split; [exact EQ3|]. split; [exact D'|]. split; [exact O'|]. split; [exact S10|]. split; [exact LBC'|].
    split. { intros b Hb. rewrite HB' by exact Hb. exact (L2_bound _ _ _ _ _ _ _ _ _ HR BCf 0 b HI2 Hb). }
    split. { intros X. exfalso. lia. }
    assert (HB : forall b, 1 <= b <= ML -> lcnt DL' (HM + 1) b = BCf b).
    { intros b Hb. rewrite (lcnt_noleaf DL' h' b) by (try exact NL; lia).
      destruct (Z.eq_dec b 1) as [->|Nb]; [rewrite (rk_at _ _ _ _ _ K') by lia; lia | apply (rk_above _ _ _ _ _ K'); lia]. }
    split. { intros b Hb. rewrite HB by exact Hb. rewrite repair_cntL. reflexivity. }
    split. { unfold kraftZ. rewrite (zsum_ext (fun b => lcnt DL' (HM + 1) b * 2 ^ (ML - b)) (fun b => BCf b * 2 ^ (ML - b))) by (intros; rewrite HB by lia; reflexivity).
             change (zsum (fun b : Z => BCf b * 2 ^ (ML - b)) 1 (Z.to_nat ML)) with (kraftZ ML BCf).
             rewrite <- (KR_kraftZ_gen BCf Z0 HI0). pose proof (l2_kr _ _ _ _ _ HI2).
             assert (P2 : 2 ^ (ML + 1) = 2 * 2 ^ ML) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia). lia. }
    intros _ p q Hq Hqp Hp Lp Lq.
    assert (h' <= q) by (destruct (Z_lt_le_dec q h') as [C0|C0]; [exfalso; exact (noleaf_below h' q ltac:(lia) NL ltac:(lia) Lq) | exact C0]).
    apply (rk_mono _ _ _ _ _ K'); assumption || lia.
Qed.

End Tail3.
End RefDeflSafeO4.

Module RefDeflSafeO5.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeB6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeO2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeO2.RefDeflSafeO1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeO2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.RefDeflSafeO3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.RefDeflSafeO4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rep_find_ext : forall f (h h' : hist) b, (forall x, h x = h' x) -> rep_find f h b = rep_find f h' b.
Proof. induction f as [|f IH]; intros h h' b E; cbn [rep_find]; [reflexivity|]. rewrite E. destruct (h' b =? 0); [apply IH; exact E | reflexivity]. Qed.

Lemma rep_step_ext : forall ML (h h' : hist) r x, (forall x, h x = h' x) -> rep_step ML h r x = rep_step ML h' r x.
Proof. intros ML h h' r x E. unfold rep_step. rewrite !E. reflexivity. Qed.

Lemma rep_iter_ext : forall n ML (h h' : hist), (forall x, h x = h' x) -> forall x, rep_iter n ML h x = rep_iter n ML h' x.
Proof.
  induction n as [|n IH]; intros ML h h' E x; cbn [rep_iter]; [apply E|].
  apply IH. intros y. rewrite (rep_find_ext _ h h') by exact E. apply rep_step_ext. exact E.
Qed.

Lemma repair_ext : forall ML (h h' : hist), (forall x, h x = h' x) -> forall x, repair ML h x = repair ML h' x.
Proof.
  intros ML h h' E x. unfold repair, kraftZ. rewrite (zsum_ext (fun b => h b * 2 ^ (ML - b)) (fun b => h' b * 2 ^ (ML - b))) by (intros; rewrite E; reflexivity).
  apply rep_iter_ext. exact E.
Qed.

Section ZTree.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Variable Wg : Z -> Z.
Variable DLq : arr.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Local Notation HM := (HM L).
Local Notation C := (C t L HPf).
Local Notation D := (D t L HPf).
Local Notation leafb := (leafb t HPf).
Local Notation nd := (nd HPf).
Local Notation par := (par t L HPf).
Local Notation tail := (tail L).
Local Notation cntL := (cntL t L HPf).
Local Notation NI := (NI t L HPf 573).
Local Notation lcnt := (lcnt t HPf).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.
Hypothesis GF : greedy_facts t FC2 L FCf HPf Wg.
Hypothesis HDLI : DLI t FC2 L HPf DLq.
Hypothesis Hnoovf : NI = 0 -> forall i, HM < i < 573 -> arr_get DLq (nd i) = D i.
Hypothesis Hhist : forall b, 1 <= b <= ML -> lcnt DLq (HM + 1) b = repair ML cntL b.
Hypothesis Hrank : NI <> 0 -> forall p q, HM < q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DLq (nd q) <= arr_get DLq (nd p).
Hypothesis Hkraft : kraftZ ML (fun b => lcnt DLq (HM + 1) b) = 2 ^ ML.

Let RHM : 2 <= HM <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RML : 7 <= ML <= 15 /\ E <= 2 ^ ML := ML_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.

Definition ztree_of : ztree := {| zt_E := E; zt_ML := ML; zt_g := gtree_of t L HPf Wg; zt_len := fun c => arr_get DLq c |}.

Lemma g_depth_fuel_D : forall f g i, tail i -> (Z.to_nat (i - HM) < f)%nat -> (Z.to_nat (i - HM) < g)%nat ->
  g_depth_fuel (gtree_of t L HPf Wg) f i = Df t L HPf g i.
Proof.
  induction f as [|f IH]; intros g i Hi Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  cbn [g_depth_fuel Df g_lo g_par gtree_of].
  destruct (Z.leb_spec i HM) as [Le|Gt]; [reflexivity|].
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail in Hi; lia)) as (A & B & _).
  rewrite (IH g (par i) A); [lia | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma g_depth_D : forall i, tail i -> g_depth (gtree_of t L HPf Wg) i = D i.
Proof.
  intros i Hi. unfold g_depth, RefDeflSafeO4.D. cbn [g_hi g_lo gtree_of].
  apply g_depth_fuel_D; [exact Hi | unfold RefDeflSafeB3.tail in Hi; lia | unfold RefDeflSafeB3.tail in Hi; lia].
Qed.

Lemma leaf_pos : forall i, HM <= i <= 572 -> leafb i = true -> HM < i < 573.
Proof.
  intros i Hi Li. destruct (Z.eq_dec i HM) as [->|N]; [|lia].
  rewrite (root_internal _ _ _ _ _ _ _ _ _ HR) in Li. discriminate.
Qed.

Lemma used_iff : forall c, 0 <= c < E -> (zt_used ztree_of c <-> arr_get FC2 c <> 0).
Proof.
  intros c Hc. unfold zt_used, zt_is_leaf_of, g_pos. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code gtree_of]. split.
  - intros (i & Hi & Li & Ci). pose proof (leaf_pos i Hi Li).
    destruct (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail; lia)) as [[A B]|A]; [rewrite <- Ci; exact B|].
    unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li. lia.
  - intros Fc. destruct (hr_cov _ _ _ _ _ _ _ _ _ HR c ltac:(unfold Vj, V0, Vscan; left; split; [lia | exact Fc])) as (i & Hi & Ei).
    exists i. unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd. rewrite Ei. unfold RefDeflSafeB3.HM in *.
    split; [| split; [apply Z.ltb_lt; lia | reflexivity]].
    destruct (Z.eq_dec i (574 - 2 * L)) as [->|N]; [| lia]. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Ei. lia.
Qed.

Lemma leaf_wt : forall i, HM <= i <= 572 -> leafb i = true -> g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd i) /\ 0 <= nd i < E.
Proof.
  intros i Hi Li. cbn [g_wt gtree_of]. pose proof (leaf_pos i Hi Li) as P.
  unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li.
  destruct (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail; lia)) as [[A B]|A]; [|lia].
  split; [| lia]. apply (gf_wleaf _ _ _ _ _ _ GF). lia.
Qed.

Lemma pos_wt_mono : forall i j, HM < i < 573 -> HM < j < 573 -> i < j -> leafb i = true -> Wg (nd j) <= Wg (nd i).
Proof.
  intros i j Hi Hj Hij Li. pose proof GF as [WL WF WN ND NM MIN].
  pose proof (round_of t L j Hj) as (Kj & Cj & Dj). cbv zeta in Kj, Cj, Dj. set (k := (572 - j) / 2 + 1) in *. clearbody k.
  unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li.
  destruct Cj as [-> | ->].
  - destruct (Z.eq_dec i (573 - 2 * k)) as [->|Ni]; [apply NM; exact Kj|].
    exact (proj1 (MIN k i Kj ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.nd in Li; lia))).
  - exact (proj2 (MIN k i Kj ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.nd in Li; lia))).
Qed.

Lemma g_hist_len : forall b, g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd i)) b = lcnt DLq (HM + 1) b.
Proof.
  intros b. unfold g_hist, RefDeflSafeO4.lcnt. cbn [g_lo g_hi g_leaf gtree_of].
  replace (Z.to_nat (572 - HM + 1)) with (S (Z.to_nat (573 - (HM + 1)))) by lia.
  rewrite zsum_shift, (root_internal _ _ _ _ _ _ _ _ _ HR). cbn [andb zind]. lia.
Qed.

Lemma g_hist_capped : forall b, g_hist (gtree_of t L HPf Wg) (fun i => Z.min (g_depth (gtree_of t L HPf Wg) i) ML) b = cntL b.
Proof.
  intros b. unfold g_hist, RefDeflSafeB3.cntL. cbn [g_lo g_hi g_leaf gtree_of].
  replace (Z.to_nat (572 - HM + 1)) with (S (Z.to_nat (572 - HM))) by lia.
  rewrite zsum_shift, (root_internal _ _ _ _ _ _ _ _ _ HR). cbn [andb zind]. rewrite Z.add_0_l.
  apply zsum_ext. intros i Hi. unfold w_cnt. rewrite g_depth_D, <- (C_min' _ _ _ _ _ _ _ _ _ HR) by (unfold RefDeflSafeB3.tail; lia). reflexivity.
Qed.

Lemma ztree_of_kraft : kraftZ ML (g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd i))) = 2 ^ ML.
Proof.
  rewrite <- Hkraft. unfold kraftZ. apply zsum_ext. intros b Hb. rewrite g_hist_len. reflexivity.
Qed.

Theorem ztree_of_ok : ztree_ok ztree_of.
Proof.
  pose proof GF as [WL WF WN ND NM MIN].
  constructor; cbn [zt_E zt_ML zt_g zt_len ztree_of].
  - exact (gtree_of_ok t FC2 DL2 L mc FCf DLf HPf DPf Wg HR GF).
  - intros i Hi Li. exact (proj2 (leaf_wt i Hi Li)).
  - lia.
  - intros c i (Hi & Li & Ci). cbn [zt_g ztree_of g_leaf g_code gtree_of] in Li, Ci. unfold g_pos in Hi. cbn [zt_g ztree_of g_lo g_hi gtree_of] in Hi.
    rewrite <- Ci. apply (dli_leaf _ _ _ _ _ HDLI); [exact (leaf_pos i Hi Li) | exact Li].
  - intros c Hc NU. apply (dli_zero _ _ _ _ _ HDLI c Hc). destruct (Z.eq_dec (arr_get FC2 c) 0) as [Z0|NZ]; [exact Z0|].
    exfalso. apply NU. apply (proj2 (used_iff c Hc)). exact NZ.
  - intros NOV c i (Hi & Li & Ci). cbn [zt_g ztree_of g_leaf g_code gtree_of] in Li, Ci, NOV. unfold g_pos in Hi, NOV. cbn [zt_g ztree_of g_lo g_hi gtree_of] in Hi, NOV.
    pose proof (leaf_pos i Hi Li) as P. rewrite <- Ci, g_depth_D by (unfold RefDeflSafeB3.tail; lia).
    apply Hnoovf; [| exact P]. apply (noovf_NI _ _ _ _ _ _ _ _ _ HR).
    intros j Hj Lj. rewrite <- g_depth_D by (unfold RefDeflSafeB3.tail; lia). apply NOV; [lia | exact Lj].
  - intros b Hb. cbn [zt_g ztree_of].
    rewrite (repair_ext ML _ cntL g_hist_capped).
    change (fun i : Z => arr_get DLq (g_code (gtree_of t L HPf Wg) i)) with (fun i : Z => arr_get DLq (nd i)).
    rewrite g_hist_len. apply Hhist. exact Hb.
  - intros (i0 & Hi0 & Li0 & Di0) i j Hi Hj Li Lj Wij. unfold g_pos in *. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code g_wt gtree_of] in *.
    pose proof (leaf_pos i0 Hi0 Li0) as P0. pose proof (leaf_pos i Hi Li) as Pi. pose proof (leaf_pos j Hj Lj) as Pj.
    rewrite g_depth_D in Di0 by (unfold RefDeflSafeB3.tail; lia).
    assert (NZ : NI <> 0).
    { intros Z0. pose proof (NI0_depth _ _ _ _ _ _ _ _ _ HR Z0 i0 ltac:(unfold RefDeflSafeB3.tail; lia)). lia. }
    destruct (Z_lt_le_dec j i) as [LT|GE].
    + apply (Hrank NZ i j); try assumption; lia.
    + exfalso. destruct (Z.eq_dec i j) as [->|N]; [lia|].
      pose proof (pos_wt_mono i j Pi Pj ltac:(lia) Li). lia.
Qed.
End ZTree.


Lemma loop2_id : forall X t mc, 2 <= ds_heap_len X -> build_tree_loop2 2%nat X t mc = (X, mc).
Proof.
  intros X t mc H. cbn [build_tree_loop2].
  replace (ds_heap_len X <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma zone_two : forall HP hl (V : Z -> Prop) a b, zone_ok HP hl 573 V -> V a -> V b -> a <> b -> 2 <= hl.
Proof.
  intros HP hl V a b [pos [A B]] Va Vb Nab.
  destruct (B a Va) as [La Ea]. destruct (B b Vb) as [Lb Eb]. unfold live in La, Lb.
  destruct (Z.eq_dec (pos a) (pos b)) as [Ep|Np]; [rewrite Ep in Ea; congruence | lia].
Qed.

Section BuildTree.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Hypothesis HP : bt_pre s t.
Hypothesis WB : zsum (fun u => arr_get (tree_fc s t) u) 0 (Z.to_nat E) + 2 < 2 ^ 16.

Theorem build_tree_ztree :
  exists Fl L mc FCf DLf HPf DPf DL2 Wg DLq FCg BCq OLq SLq,
    let FC2 := fc_forced Fl (tree_fc s t) in
    build_tree s t = bt_upd s t FCg DLq HPf 1 (574 - 2 * L) DPf BCq OLq SLq mc
    /\ tree_dl (build_tree s t) t = DLq /\ max_code (build_tree s t) t = mc
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get (tree_fc s t) f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get (tree_fc s t) i)
    /\ (forall a b, 0 <= a < E -> 0 <= b < E -> a <> b -> arr_get (tree_fc s t) a <> 0 -> arr_get (tree_fc s t) b <> 0 -> Fl = [])
    /\ (exists a b, 0 <= a < E /\ 0 <= b < E /\ a <> b /\ arr_get FC2 a <> 0 /\ arr_get FC2 b <> 0)
    /\ heap_result t FC2 DL2 L mc FCf DLf HPf DPf
    /\ greedy_facts t FC2 L FCf HPf Wg
    /\ DLI t FC2 L HPf DLq
    /\ ztree_ok (ztree_of t L HPf Wg DLq)
    /\ kraftZ ML (g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd HPf i))) = 2 ^ ML
    /\ (forall c, 0 <= c < E -> (zt_used (ztree_of t L HPf Wg DLq) c <-> arr_get FC2 c <> 0))
    /\ (forall i, 574 - 2 * L <= i <= 572 -> leafb t HPf i = true ->
          g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd HPf i) /\ 0 <= nd HPf i < E).
Proof.
  pose proof (elems_range t) as RE.
  pose proof (heap_phase_s s t HP) as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM.
  pose proof E7 as E7'. rewrite E3 in E7'.
  destruct (heap_phase_o s t (tree_fc s t) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) _ Fl DL2 HP2 DP2 L FCf DLf HPf DPf E7' RL Z2 LHP2 LDP2 LDL2
              (tree_lens_fc _ _ (bp_tl _ _ HP)) RDP2 RFC2 RDL2 LF FCE ltac:(intros i; pose proof (bp_fc _ _ HP i); lia) WB) as [Wg GF].
  assert (NOF : forall a b, 0 <= a < E -> 0 <= b < E -> a <> b -> arr_get (tree_fc s t) a <> 0 -> arr_get (tree_fc s t) b <> 0 -> Fl = []).
  { intros a b Ha Hb Nab Fa Fb.
    pose proof (LHP s t HP) as LHP0. pose proof (tree_lens_dl s t (bp_tl _ _ HP)) as LDL0.
    destruct (loop1_spec s t (Z.to_nat E) 0 (-1) (tree_fc s t) (tree_dl s t) (ds_heap s) 0 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)
                ltac:(lia) ltac:(lia) ltac:(lia) LHP0 LDL0)
      as (HP1 & HL1 & DL1 & DP1 & mc1 & E1 & B1 & B1' & LHP1 & LDL1 & Z1 & _).
    { apply (zone_ok_ext _ _ _ (fun _ => False)); [| apply zone_ok_empty]. unfold Vscan. intros u. lia. }
    { lia. } { intros; lia. } { intros; lia. } { lia. }
    pose proof (zone_two HP1 HL1 (Vscan (tree_fc s t) E) a b Z1 ltac:(unfold Vscan; split; [lia | exact Fa]) ltac:(unfold Vscan; split; [lia | exact Fb]) Nab) as HL2.
    assert (S0 : set_heap_max (set_heap_len s 0) HEAP_SIZE = bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) 0 573 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)).
    { rewrite <- (bt_upd_self s t) at 1. autorewrite with btupd. reflexivity. }
    pose proof E3 as E3'. rewrite S0, E1 in E3'. cbn [fst snd] in E3'. rewrite loop2_id in E3' by (rewrite bt_heap_len; exact HL2). cbn [fst snd] in E3'.
    rewrite bt_set_max_code in E3'.
    pose proof (f_equal (fun x => tree_fc x t) E3') as EF. cbv beta in EF. rewrite !bt_tree_fc in EF.
    destruct Fl as [|f l]; [reflexivity|]. exfalso.
    destruct (FF f (or_introl eq_refl)) as (Rf & Zf & _). pose proof (FCE f) as X. rewrite <- EF, Zf in X. cbn [existsb] in X. rewrite Z.eqb_refl in X. cbn in X. lia. }
  assert (TWO : exists a b, 0 <= a < E /\ 0 <= b < E /\ a <> b /\ arr_get (fc_forced Fl (tree_fc s t)) a <> 0 /\ arr_get (fc_forced Fl (tree_fc s t)) b <> 0).
  { pose proof (zone_ok_mem _ _ _ _ 1 Z2 ltac:(unfold live; left; lia)) as M1. pose proof (zone_ok_mem _ _ _ _ 2 Z2 ltac:(unfold live; left; lia)) as M2.
    unfold Vscan in M1, M2. exists (arr_get HP2 1), (arr_get HP2 2).
    split; [lia|]. split; [lia|]. split; [| split; [exact (proj2 M1) | exact (proj2 M2)]].
    intros EQ. pose proof (zone_ok_inj _ _ _ _ 1 2 Z2 ltac:(unfold live; left; lia) ltac:(unfold live; left; lia) EQ). lia. }
  rewrite build_tree_unfold. cbv zeta. rewrite E7.
  set (p1 := build_tree_loop1 (Z.to_nat E) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t E 0 (-1)) in *.
  set (p2 := build_tree_loop2 2 (fst p1) t (snd p1)) in *.
  set (mc := snd p2) in *.
  set (FC := tree_fc s t) in *. set (FC2 := fc_forced Fl FC) in *.
  pose proof (LBC s t HP) as LB.
  assert (ROL : 0 <= ol_forced Fl (ds_opt_len s) < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_ol _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl (ds_static_len s) < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| apply (bp_sl _ _ HP)].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_sl _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_exact t _ _ _ _ _ _ _ _ HR s (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) LB ROL RSL)
    as (DL' & BC' & OL' & SL' & EG & HD & RO & RS & LB' & RBC & NOOVF & HIST & KRF & RANK).
  change (RefDeflSafeB3.HM L) with (574 - 2 * L) in EG. rewrite EG.
  set (X := bt_upd s t FCf DL' HPf 1 (574 - 2 * L) DPf BC' OL' SL' mc).
  assert (TLX : tree_lens X) by (subst X; apply bt_tree_lens; try assumption; [apply (bp_tl _ _ HP) | apply (hr_lfc _ _ _ _ _ _ _ _ _ HR) | apply (dli_len _ _ _ _ _ HD) | apply (hr_lhp _ _ _ _ _ _ _ _ _ HR) | apply (hr_ldp _ _ _ _ _ _ _ _ _ HR)]).
  unfold gen_codes. rewrite <- (stf_self X t).
  destruct (gen_codes_typed (Z.to_nat (mc + 1)) X t (tree_fc X t) (gen_codes_loop1 16 (ds_bl_count (set_tree_fc X t (tree_fc X t))) (arr_make (MAX_BITS + 1) 0) 0 1) mc 0)
    as (FCg & EC & LFCg & RFCg).
  { subst X. rewrite bt_tree_fc. apply (hr_lfc _ _ _ _ _ _ _ _ _ HR). }
  { subst X. rewrite bt_tree_fc. apply (hr_fcr _ _ _ _ _ _ _ _ _ HR). }
  rewrite EC. subst X. rewrite bt_set_tree_fc.
  exists Fl, L, mc, FCf, DLf, HPf, DPf, DL2, Wg, DL', FCg, BC', OL', SL'.
  cbv zeta. fold FC2.
  split; [reflexivity|]. split; [apply bt_tree_dl|]. split; [apply bt_max_code|].
  split; [exact LF|]. split; [exact ND|]. split; [exact FF|]. split; [exact FCE|]. split; [exact NOF|]. split; [exact TWO|].
  split; [exact HR|]. split; [exact GF|]. split; [exact HD|].
  split; [exact (ztree_of_ok t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR GF HD NOOVF HIST RANK)|].
  split; [exact (ztree_of_kraft t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR KRF)|].
  split; [intros c Hc; exact (used_iff t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR c Hc)|].
  intros i Hi Li. exact (leaf_wt t FC2 DL2 L mc FCf DLf HPf DPf Wg HR GF i Hi Li).
Qed.
End BuildTree.
End RefDeflSafeO5.

Module RefDeflSafeO6.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Export OverlayTF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeO2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.RefDeflSafeO3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.RefDeflSafeO5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section OT.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.
Let TP : TPF s := tree_phase s OP.
Let N := nsym s.

Lemma wsum_L : zsum (fun u => arr_get (tree_fc (ov_X0 s) TL) u) 0 (Z.to_nat (sd_elems TL)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc0L _ TP). cbn [sd_elems].
  pose proof (fubini_L s OP (fun _ => 1)) as F. cbv beta in F.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_ltree_fc s) c * 1) (fun u => arr_get (ds_dyn_ltree_fc s) u)) in F by (intros; lia).
  rewrite zsum_const1 in F. pose proof (op_nsym _ OP). pose proof (op_lbs _ OP). unfold L_CODES in *. rewrite F. lia.
Qed.

Lemma wsum_D : zsum (fun u => arr_get (tree_fc (ov_X1 s) TD) u) 0 (Z.to_nat (sd_elems TD)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc1D _ TP). cbn [sd_elems].
  pose proof (fubini_D s OP (fun _ => 1)) as F. cbv beta in F.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_dtree_fc s) c * 1) (fun u => arr_get (ds_dyn_dtree_fc s) u)) in F by (intros; lia).
  pose proof (zsum_mono (fun j => zind (sym_isdist s j) * 1) (fun _ => 1) 0 (Z.to_nat (nsym s)) ltac:(intros; cbv beta; destruct (sym_isdist s _); cbn; lia)) as M.
  rewrite zsum_const1 in M. pose proof (op_nsym _ OP). pose proof (op_lbs _ OP). unfold D_CODES in *. rewrite F. lia.
Qed.

Lemma wsum_B : zsum (fun u => arr_get (tree_fc (ov_X4 s) TB) u) 0 (Z.to_nat (sd_elems TB)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc4B _ TP). cbn [sd_elems].
  pose proof (tp_lmax _ TP) as RL. pose proof (tp_dmax _ TP) as RD. unfold L_CODES, D_CODES in RL, RD.
  pose proof (zsum_bound (fun u => arr_get (ov_BC s) u) 0 (Z.to_nat BL_CODES) 636 ltac:(lia)) as B.
  assert (X : forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat BL_CODES) -> 0 <= arr_get (ov_BC s) i <= 636).
  { intros i Hi. unfold BL_CODES in Hi. rewrite (tp_BC _ TP) by lia.
    pose proof (TDcnt_nonneg (fun j => Len (ov_X6 s) TL j) (ds_l_max_code (ov_X6 s)) i). pose proof (TDcnt_le (fun j => Len (ov_X6 s) TL j) (ds_l_max_code (ov_X6 s)) i ltac:(lia)).
    pose proof (TDcnt_nonneg (fun j => Len (ov_X6 s) TD j) (ds_d_max_code (ov_X6 s)) i). pose proof (TDcnt_le (fun j => Len (ov_X6 s) TD j) (ds_d_max_code (ov_X6 s)) i ltac:(lia)). lia. }
  specialize (B X). unfold BL_CODES in *. lia.
Qed.

Theorem ot_facts : exists zL zD zB FlL FlD FlB,
     tree_facts zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL
  /\ tree_facts zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD
  /\ tree_facts zB 19 7 (fun x => arr_get (ov_BC s) x) FlB
  /\ zt_kraft zL /\ zt_kraft zD /\ zt_kraft zB
  /\ (forall c, zt_len zL c = arr_get (tree_dl (ov_X1 s) TL) c)
  /\ (forall d, zt_len zD d = arr_get (tree_dl (ov_X2 s) TD) d)
  /\ (forall x, zt_len zB x = arr_get (tree_dl (ov_X5 s) TB) x)
  /\ (forall c, c <> ds_l_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TL c = zt_len zL c)
  /\ (forall d, d <> ds_d_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TD d = zt_len zD d)
  /\ (forall x, Len (ov_X6 s) TB x = zt_len zB x)
  /\ Len (ov_X6 s) TL (ds_l_max_code (ov_X6 s) + 1) = 65535
  /\ Len (ov_X6 s) TD (ds_d_max_code (ov_X6 s) + 1) = 65535
  /\ (ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL (ds_l_max_code (ov_X6 s)) <> 0
      /\ forall c, 0 <= c < 286 -> ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL c <> 0 -> c <= ds_l_max_code (ov_X6 s))
  /\ (ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD (ds_d_max_code (ov_X6 s)) <> 0
      /\ forall d, 0 <= d < 30 -> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0 -> d <= ds_d_max_code (ov_X6 s))
  /\ (1 <= nsym s -> FlL = []).
Proof.
  pose proof (op_hist _ OP) as (FHL & FHD & FHB). pose proof (op_nsym _ OP) as RN.
  destruct (build_tree_ztree (ov_X0 s) TL (bt_pre_X0 s OP) wsum_L)
    as (FlL & L1 & mc1 & FCf1 & DLf1 & HPf1 & DPf1 & DL21 & Wg1 & DLq1 & FCg1 & BCq1 & OLq1 & SLq1 & EB1 & EDL1 & EMC1 & LF1 & ND1 & FF1 & FCE1 & NOF1 & TWO1 & HR1 & GF1 & DLI1 & ZOK1 & KRF1 & USED1 & WT1).
  change (build_tree (ov_X0 s) TL) with (ov_X1 s) in EB1, EDL1, EMC1.
  rewrite (tp_fc0L _ TP) in HR1, GF1, DLI1, FF1, FCE1, NOF1, TWO1, USED1, WT1. cbn [sd_elems] in FF1, NOF1, TWO1, USED1, WT1.
  rewrite (tp_mc1 _ TP) in EMC1.
  destruct (build_tree_ztree (ov_X1 s) TD (tp_bp1 _ TP) wsum_D)
    as (FlD & L2 & mc2 & FCf2 & DLf2 & HPf2 & DPf2 & DL22 & Wg2 & DLq2 & FCg2 & BCq2 & OLq2 & SLq2 & EB2 & EDL2 & EMC2 & LF2 & ND2 & FF2 & FCE2 & NOF2 & TWO2 & HR2 & GF2 & DLI2 & ZOK2 & KRF2 & USED2 & WT2).
  change (build_tree (ov_X1 s) TD) with (ov_X2 s) in EB2, EDL2, EMC2.
  rewrite (tp_fc1D _ TP) in HR2, GF2, DLI2, FF2, FCE2, NOF2, TWO2, USED2, WT2. cbn [sd_elems] in FF2, NOF2, TWO2, USED2, WT2.
  rewrite (tp_mc2 _ TP) in EMC2.
  destruct (build_tree_ztree (ov_X4 s) TB (tp_bp4 _ TP) wsum_B)
    as (FlB & L5 & mc5 & FCf5 & DLf5 & HPf5 & DPf5 & DL25 & Wg5 & DLq5 & FCg5 & BCq5 & OLq5 & SLq5 & EB5 & EDL5 & EMC5 & LF5 & ND5 & FF5 & FCE5 & NOF5 & TWO5 & HR5 & GF5 & DLI5 & ZOK5 & KRF5 & USED5 & WT5).
  change (build_tree (ov_X4 s) TB) with (ov_X5 s) in EB5, EDL5, EMC5.
  rewrite (tp_fc4B _ TP) in HR5, GF5, DLI5, FF5, FCE5, NOF5, TWO5, USED5, WT5. cbn [sd_elems] in FF5, NOF5, TWO5, USED5, WT5.
  exists (ztree_of TL L1 HPf1 Wg1 DLq1), (ztree_of TD L2 HPf2 Wg2 DLq2), (ztree_of TB L5 HPf5 Wg5 DLq5), FlL, FlD, FlB.
  assert (PKG : forall t L HPf Wg DLq Fl (F : arr) FC2 DL2 mc FCf DLf DPf,
            heap_result t FC2 DL2 L mc FCf DLf HPf DPf ->
            (length Fl <= 2)%nat -> NoDup Fl -> (forall f, In f Fl -> 0 <= f < sd_elems t /\ arr_get F f = 0 /\ f <= 2) ->
            (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get F i) ->
            (forall a b, 0 <= a < sd_elems t -> 0 <= b < sd_elems t -> a <> b -> arr_get F a <> 0 -> arr_get F b <> 0 -> Fl = []) ->
            (exists a b, 0 <= a < sd_elems t /\ 0 <= b < sd_elems t /\ a <> b /\ arr_get FC2 a <> 0 /\ arr_get FC2 b <> 0) ->
            ztree_ok (ztree_of t L HPf Wg DLq) ->
            (forall c, 0 <= c < sd_elems t -> (zt_used (ztree_of t L HPf Wg DLq) c <-> arr_get FC2 c <> 0)) ->
            (forall i, 574 - 2 * L <= i <= 572 -> leafb t HPf i = true -> g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd HPf i) /\ 0 <= nd HPf i < sd_elems t) ->
            tree_facts (ztree_of t L HPf Wg DLq) (sd_elems t) (sd_max_length t) (fun c => arr_get F c) Fl
            /\ (ffreq (fun c => arr_get F c) Fl mc <> 0 /\ forall c, 0 <= c < sd_elems t -> ffreq (fun c => arr_get F c) Fl c <> 0 -> c <= mc)).
  { intros t L HPf Wg DLq Fl F FC2 DL2 mc FCf DLf DPf HR LF ND FF FCE NOF TWO ZOK USED WT.
    assert (FQ : forall c, ffreq (fun c => arr_get F c) Fl c = arr_get FC2 c) by (intros c; unfold ffreq; rewrite FCE; reflexivity).
    split.
    - constructor.
      + exact ZOK.
      + reflexivity.
      + reflexivity.
      + split; [exact LF|]. split; [exact ND|]. intros f Hf. destruct (FF f Hf) as (A & B & C0). lia.
      + exact NOF.
      + destruct TWO as (a & b' & Ha & Hb & Nab & Fa & Fb). exists a, b'. rewrite !FQ. repeat split; assumption || lia.
      + intros c Hc. rewrite FQ. apply USED. exact Hc.
      + intros i Hi Li. unfold g_pos in Hi. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code RefDeflSafeO3.gtree_of] in Hi, Li |- *.
        unfold RefDeflSafeB3.HM in Hi. destruct (WT i Hi Li) as [A B]. rewrite FQ. split; [exact B|].
        cbn [g_wt RefDeflSafeO3.gtree_of] in A. exact A.
    - split; [rewrite FQ; apply (hr_mc_in _ _ _ _ _ _ _ _ _ HR)|]. intros c Hc. rewrite FQ. apply (hr_mc_max _ _ _ _ _ _ _ _ _ HR). exact Hc. }
  destruct (PKG TL L1 HPf1 Wg1 DLq1 FlL (ds_dyn_ltree_fc s) _ DL21 mc1 FCf1 DLf1 DPf1 HR1 LF1 ND1 FF1 FCE1 NOF1 TWO1 ZOK1 USED1 WT1) as [TF1 MX1].
  destruct (PKG TD L2 HPf2 Wg2 DLq2 FlD (ds_dyn_dtree_fc s) _ DL22 mc2 FCf2 DLf2 DPf2 HR2 LF2 ND2 FF2 FCE2 NOF2 TWO2 ZOK2 USED2 WT2) as [TF2 MX2].
  destruct (PKG TB L5 HPf5 Wg5 DLq5 FlB (ov_BC s) _ DL25 mc5 FCf5 DLf5 DPf5 HR5 LF5 ND5 FF5 FCE5 NOF5 TWO5 ZOK5 USED5 WT5) as [TF5 MX5].
  cbn [sd_elems sd_max_length] in TF1, MX1, TF2, MX2, TF5, MX5.
  split; [exact TF1|]. split; [exact TF2|]. split; [exact TF5|].
  split; [exact KRF1|]. split; [exact KRF2|]. split; [exact KRF5|].
  split; [intros c; cbn [zt_len ztree_of]; rewrite <- EDL1; reflexivity|].
  split; [intros d; cbn [zt_len ztree_of]; rewrite <- EDL2; reflexivity|].
  split; [intros x; cbn [zt_len ztree_of]; rewrite <- EDL5; reflexivity|].
  split; [intros c Hc; cbn [zt_len ztree_of]; rewrite <- EDL1; exact (tp_len1 _ TP c Hc)|].
  split; [intros d Hd; cbn [zt_len ztree_of]; rewrite <- EDL2; exact (tp_len2 _ TP d Hd)|].
  split; [intros x; cbn [zt_len ztree_of]; rewrite <- EDL5; exact (tp_len5 _ TP x)|].
  split; [exact (tp_guard1 _ TP)|]. split; [exact (tp_guard2 _ TP)|].
  split; [rewrite EMC1; exact MX1|]. split; [rewrite EMC2; exact MX2|].
  intros HN. pose proof (sym_codes s OP 0 ltac:(lia)) as (A & _ & _ & Lit & M).
  assert (F0 : arr_get (ds_dyn_ltree_fc s) (sym_lcode s 0) <> 0).
  { rewrite (FHL (sym_lcode s 0)) by exact A.
    pose proof (zsum_ge_point (fun j => zind (sym_lcode s j =? sym_lcode s 0)) 0 (Z.to_nat (nsym s)) 0 ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(lia)) as X.
    cbv beta in X. rewrite Z.eqb_refl in X. cbn [zind] in X. pose proof (zind_le1 (sym_lcode s 0 =? END_BLOCK)). lia. }
  assert (FE : arr_get (ds_dyn_ltree_fc s) END_BLOCK <> 0).
  { rewrite (FHL END_BLOCK) by (unfold END_BLOCK, L_CODES; lia). rewrite Z.eqb_refl. cbn [zind].
    pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? END_BLOCK)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))). lia. }
  assert (NE : sym_lcode s 0 <> END_BLOCK).
  { unfold END_BLOCK. destruct (sym_isdist s 0); [pose proof (M eq_refl) | pose proof (Lit eq_refl)]; lia. }
  unfold L_CODES in A. exact (NOF1 (sym_lcode s 0) END_BLOCK ltac:(unfold L_CODES; lia) ltac:(unfold END_BLOCK, L_CODES; lia) NE F0 FE).
Qed.

End OT.
End RefDeflSafeO6.

Module OverlayScan.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition E1 (r : Z) : Z :=
  if r <=? 3 then r else if r <=? 6 then 1 else 1 + (let u := (r - 7) mod 6 in if u <? 3 then u else 0).
Definition M1 (r : Z) : Z :=
  if r <=? 3 then 0 else if r <=? 6 then 1 else 1 + (r - 7) / 6 + (let u := (r - 7) mod 6 in if 3 <=? u then 1 else 0).
Definition e0 (r : Z) : Z := let u := r mod 138 in if u <? 3 then u else 0.
Definition e17 (r : Z) : Z := let u := r mod 138 in if (3 <=? u) && (u <=? 10) then 1 else 0.
Definition e18 (r : Z) : Z := let u := r mod 138 in r / 138 + (if 11 <=? u then 1 else 0).

Definition RUN (v r x : Z) : Z :=
  if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? REPZ_3_10) + e18 r * zind (x =? REPZ_11_138)
  else E1 r * zind (x =? v) + M1 r * zind (x =? REP_3_6).

Lemma E1_M1_facts : forall r, 1 <= r -> 0 <= E1 r <= r /\ 0 <= M1 r /\ E1 r + 3 * M1 r <= r /\ 4 * M1 r <= r.
Proof.
  intros r Hr. unfold E1, M1.
  destruct (Z.leb_spec r 3); [lia|]. destruct (Z.leb_spec r 6); [lia|].
  pose proof (Z.div_mod (r - 7) 6 ltac:(lia)). pose proof (Z.mod_pos_bound (r - 7) 6 ltac:(lia)).
  set (u := (r - 7) mod 6) in *. set (q := (r - 7) / 6) in *.
  destruct (Z.ltb_spec u 3); destruct (Z.leb_spec 3 u); lia.
Qed.

Lemma e_facts : forall r, 1 <= r -> 0 <= e0 r <= 2 /\ 0 <= e17 r <= 1 /\ 0 <= e18 r /\ e0 r + 3 * e17 r + 11 * e18 r <= r.
Proof.
  intros r Hr. unfold e0, e17, e18.
  pose proof (Z.div_mod r 138 ltac:(lia)). pose proof (Z.mod_pos_bound r 138 ltac:(lia)).
  set (u := r mod 138) in *. set (q := r / 138) in *.
  destruct (Z.ltb_spec u 3); destruct (Z.leb_spec 3 u); destruct (Z.leb_spec u 10); destruct (Z.leb_spec 11 u); cbn [andb]; lia.
Qed.

Lemma mod_div_138 : forall r, 1 <= r <= 276 ->
  (r < 138 /\ r mod 138 = r /\ r / 138 = 0) \/ (r = 138 /\ r mod 138 = 0 /\ r / 138 = 1)
  \/ (138 < r < 276 /\ r mod 138 = r - 138 /\ r / 138 = 1) \/ (r = 276 /\ r mod 138 = 0 /\ r / 138 = 2).
Proof.
  intros r Hr.
  destruct (Z_lt_le_dec r 138) as [A|A].
  - left. rewrite Z.mod_small, Z.div_small by lia. lia.
  - destruct (Z.eq_dec r 138) as [->|B]; [right; left; repeat split; reflexivity|].
    destruct (Z.eq_dec r 276) as [->|C]; [right; right; right; repeat split; reflexivity|].
    right; right; left. split; [lia|]. split.
    + symmetry. apply (Z.mod_unique_pos r 138 1); lia.
    + symmetry. apply (Z.div_unique_pos r 138 1 (r - 138)); lia.
Qed.

Lemma e0_is12 : forall r, 1 <= r <= 276 -> e0 r = is1 r + 2 * is2 r.
Proof.
  intros r Hr. unfold e0, is1, is2, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity].
  - destruct (Z.ltb_spec r 3); destruct (Z.eqb_spec r 1); destruct (Z.eqb_spec r 2); lia.
  - destruct (Z.ltb_spec (r - 138) 3); destruct (Z.eqb_spec (r - 138) 1); destruct (Z.eqb_spec (r - 138) 2); lia.
Qed.

Lemma e17_isa : forall r, 1 <= r <= 276 -> e17 r = isa r.
Proof.
  intros r Hr. unfold e17, isa, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity]; reflexivity.
Qed.

Lemma e18_isb : forall r, 1 <= r <= 276 -> e18 r = isb r + nlong r.
Proof.
  intros r Hr. unfold e18, isb, nlong, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B, C;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity].
  - destruct (Z.leb_spec 11 r); lia.
  - destruct (Z.leb_spec 11 (r - 138)); lia.
Qed.


Fixpoint zr (L : Z -> Z) (i : Z) (n : nat) (cur : Z) : list Z :=
  match n with
  | O => if cur =? 0 then [] else [cur]
  | S k => if L i =? 0 then zr L (i + 1) k (cur + 1)
           else (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) k 0
  end.

Lemma zruns_go_lsum : forall f L n i cur acc, lsum f (zruns_go L i n cur acc) = lsum f acc + lsum f (zr L i n cur).
Proof.
  intros f L. induction n as [|n IH]; intros i cur acc; cbn [zruns_go zr].
  - destruct (cur =? 0); cbn; lia.
  - destruct (L i =? 0); [apply IH|]. rewrite IH, lsum_app. destruct (cur =? 0); cbn; lia.
Qed.

Lemma zruns_lsum : forall f L lo n, lsum f (zruns L lo n) = lsum f (zr L lo n 0).
Proof. intros. unfold zruns. rewrite zruns_go_lsum. cbn. lia. Qed.

Lemma zr_zeros : forall L c m i cur, (forall j, i <= j < i + Z.of_nat c -> L j = 0) ->
  zr L i (c + m) cur = zr L (i + Z.of_nat c) m (cur + Z.of_nat c).
Proof.
  intros L. induction c as [|c IH]; intros m i cur Hz.
  - cbn [Nat.add]. rewrite !Z.add_0_r. reflexivity.
  - cbn [Nat.add zr]. rewrite (proj2 (Z.eqb_eq _ _) (Hz i ltac:(lia))).
    rewrite (IH m (i + 1) (cur + 1)) by (intros; apply Hz; lia). f_equal; lia.
Qed.

Lemma zr_nonzero : forall L m i cur, L i <> 0 -> zr L i (S m) cur = (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) m 0.
Proof. intros L m i cur H. cbn [zr]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma zr_end : forall L i cur, zr L i 0 cur = (if cur =? 0 then [] else [cur]).
Proof. reflexivity. Qed.

Lemma zr_sum : forall L n i cur, 0 <= cur ->
  lsum (fun r => r) (zr L i n cur) = cur + zsum (fun j => zind (L j =? 0)) i n.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc; cbn [zr].
  - cbn [zsum]. destruct (Z.eqb_spec cur 0); cbn; lia.
  - rewrite zsum_shift. cbv beta. destruct (Z.eqb_spec (L i) 0); cbn [zind].
    + rewrite IH by lia. lia.
    + rewrite lsum_app, IH by lia. destruct (Z.eqb_spec cur 0); cbn; lia.
Qed.

Lemma zr_pos : forall L n i cur, 0 <= cur -> forall r, In r (zr L i n cur) -> 1 <= r.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc r Hr; cbn [zr] in Hr.
  - destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
  - destruct (L i =? 0); [exact (IH (i + 1) (cur + 1) ltac:(lia) r Hr)|].
    apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [| exact (IH (i + 1) 0 ltac:(lia) r Hr)].
    destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
Qed.

Lemma zr_length : forall L n i cur, 0 <= cur ->
  Z.of_nat (length (zr L i n cur)) <= zsum (fun j => zind (negb (L j =? 0))) i n + 1.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc; cbn [zr].
  - cbn [zsum]. destruct (cur =? 0); cbn; lia.
  - rewrite zsum_shift. cbv beta. destruct (Z.eqb_spec (L i) 0); cbn [negb zind].
    + pose proof (IH (i + 1) (cur + 1) ltac:(lia)). lia.
    + rewrite length_app, Nat2Z.inj_add. pose proof (IH (i + 1) 0 ltac:(lia)).
      destruct (cur =? 0); cbn [length Z.of_nat Pos.of_succ_nat]; lia.
Qed.

Lemma zr_bound : forall L n i cur, 0 <= cur -> forall r, In r (zr L i n cur) -> r <= cur + Z.of_nat n.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc r Hr; cbn [zr] in Hr.
  - destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
  - destruct (L i =? 0); [pose proof (IH (i + 1) (cur + 1) ltac:(lia) r Hr); lia|].
    apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [| pose proof (IH (i + 1) 0 ltac:(lia) r Hr); lia].
    destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
Qed.

Lemma zr_split : forall f L a b i cur, L (i + Z.of_nat a) <> 0 ->
  lsum f (zr L i (a + S b) cur) = lsum f (zr L i a cur) + lsum f (zr L (i + Z.of_nat a + 1) b 0).
Proof.
  intros f L. induction a as [|a IH]; intros b i cur Hnz.
  - cbn [Nat.add]. rewrite Z.add_0_r in Hnz |- *. rewrite zr_nonzero, lsum_app, zr_end by exact Hnz. reflexivity.
  - cbn [Nat.add zr]. destruct (L i =? 0).
    + rewrite (IH b (i + 1) (cur + 1)) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      f_equal. f_equal. f_equal. lia.
    + rewrite !lsum_app, (IH b (i + 1) 0) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      replace (i + 1 + Z.of_nat a + 1) with (i + Z.of_nat (S a) + 1) by lia. lia.
Qed.

Lemma zruns_sum : forall L lo n, lsum (fun r => r) (zruns L lo n) = zsum (fun j => zind (L j =? 0)) lo n.
Proof. intros. rewrite zruns_lsum, zr_sum by lia. lia. Qed.

Lemma zruns_pos : forall L lo n r, In r (zruns L lo n) -> 1 <= r <= Z.of_nat n.
Proof.
  intros L lo n r Hr. unfold zruns in Hr.
  assert (G : forall m i cur acc B, 0 <= cur -> cur + Z.of_nat m <= B -> (forall x, In x acc -> 1 <= x <= B) ->
             forall x, In x (zruns_go L i m cur acc) -> 1 <= x <= B).
  { induction m as [|m IH]; intros i cur acc B Hc HB Hacc x Hx; cbn [zruns_go] in Hx.
    - destruct (Z.eqb_spec cur 0); [exact (Hacc x Hx)|]. destruct Hx as [<-|Hx]; [lia | exact (Hacc x Hx)].
    - destruct (L i =? 0).
      + exact (IH (i + 1) (cur + 1) acc B ltac:(lia) ltac:(lia) Hacc x Hx).
      + apply (IH (i + 1) 0 (if cur =? 0 then acc else cur :: acc) B ltac:(lia) ltac:(lia)); [| exact Hx].
        intros y Hy. destruct (Z.eqb_spec cur 0); [exact (Hacc y Hy)|]. destruct Hy as [<-|Hy]; [lia | exact (Hacc y Hy)]. }
  exact (G n lo 0 [] (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(intros x Hx; destruct Hx) r Hr).
Qed.

Lemma zruns_length : forall L lo n, Z.of_nat (length (zruns L lo n)) <= zsum (fun j => zind (negb (L j =? 0))) lo n + 1.
Proof.
  intros. pose proof (zr_length L n lo 0 ltac:(lia)).
  assert (E : forall l, Z.of_nat (length l) = lsum (fun _ => 1) l) by (induction l; cbn [length lsum]; lia).
  rewrite E, zruns_lsum, <- E. exact H.
Qed.

Lemma zruns_split : forall f L lo a b, L (lo + Z.of_nat a) <> 0 ->
  lsum f (zruns L lo (a + S b)) = lsum f (zruns L lo a) + lsum f (zruns L (lo + Z.of_nat a + 1) b).
Proof. intros. rewrite !zruns_lsum. apply zr_split. exact H. Qed.


Section Scan.
Variable L : Z -> Z.
Variable mc : Z.
Hypothesis Hmc : 0 <= mc.
Hypothesis HL : forall i, 0 <= i <= mc -> 0 <= L i <= 15.
Hypothesis HG : 15 < L (mc + 1).

Definition TC (n p q k mx mn x : Z) : Z := td_cnt L mc (Z.to_nat (mc + 1 - n)) n p q k mx mn x.

Lemma TC_end : forall n p q k mx mn x, mc < n -> TC n p q k mx mn x = 0.
Proof. intros. unfold TC. replace (Z.to_nat (mc + 1 - n)) with 0%nat by lia. reflexivity. Qed.

Lemma TC_step : forall n p q k mx mn x, n <= mc ->
  TC n p q k mx mn x =
    (if (k + 1 <? mx) && (q =? L (n + 1)) then TC (n + 1) p (L (n + 1)) (k + 1) mx mn x
     else trip_cnt mn q p (k + 1) x + (let '(mx', mn') := tree_counts q (L (n + 1)) in TC (n + 1) q (L (n + 1)) 0 mx' mn' x)).
Proof.
  intros n p q k mx mn x Hn. unfold TC. replace (Z.to_nat (mc + 1 - n)) with (S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  cbn [td_cnt]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
  destruct (_ && _); [reflexivity|]. destruct (tree_counts q (L (n + 1))); reflexivity.
Qed.

Lemma TDcnt_TC : forall x, TDcnt L mc x = (let '(mx, mn) := tree_counts (-1) (L 0) in TC 0 (-1) (L 0) 0 mx mn x).
Proof.
  intros x. unfold TDcnt, TC, cnts0, tree_counts. pose proof (HL 0 ltac:(lia)).
  replace (-1 =? L 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.sub_0_r. reflexivity.
Qed.

Definition TCs (n p x : Z) : Z := let '(mx, mn) := tree_counts p (L n) in TC n p (L n) 0 mx mn x.

Lemma chunk : forall (c : nat) n p v k mx mn x,
  (1 <= c)%nat -> n + Z.of_nat c - 1 <= mc -> (forall i, n <= i < n + Z.of_nat c -> L i = v) ->
  k + Z.of_nat c <= mx -> (k + Z.of_nat c = mx \/ L (n + Z.of_nat c) <> v) ->
  TC n p v k mx mn x = trip_cnt mn v p (k + Z.of_nat c) x + TCs (n + Z.of_nat c) v x.
Proof.
  induction c as [|c IH]; intros n p v k mx mn x Hc Hn Hv Hk Hstop; [lia|].
  rewrite TC_step by lia.
  destruct c as [|c'].
  - cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. replace ((k + 1 <? mx) && (v =? L (n + 1))) with false.
    + unfold TCs. reflexivity.
    + symmetry. destruct Hstop as [E|N]; [apply andb_false_intro1; apply Z.ltb_ge; lia | apply andb_false_intro2; apply Z.eqb_neq; exact (fun H => N (eq_sym H))].
  - assert (E1' : L (n + 1) = v) by (apply Hv; lia).
    replace ((k + 1 <? mx) && (v =? L (n + 1))) with true by (symmetry; apply andb_true_intro; split; [apply Z.ltb_lt; lia | apply Z.eqb_eq; symmetry; exact E1']).
    rewrite E1'. rewrite (IH (n + 1) p v (k + 1) mx mn x ltac:(lia) ltac:(lia)); [| intros; apply Hv; lia | lia | ].
    + f_equal; [f_equal; lia | f_equal; lia].
    + destruct Hstop as [E|N]; [left; lia | right]. replace (n + 1 + Z.of_nat (S c')) with (n + Z.of_nat (S (S c'))) by lia. exact N.
Qed.

Lemma trip_short : forall mn q p k x, k < mn -> trip_cnt mn q p k x = k * zind (x =? q).
Proof. intros. unfold trip_cnt. replace (k <? mn) with true by (symmetry; apply Z.ltb_lt; lia). destruct (x =? q); cbn; lia. Qed.

Lemma trip_rep_new : forall mn q p k x, mn <= k -> q <> 0 -> q <> p -> trip_cnt mn q p k x = zind (x =? q) + zind (x =? REP_3_6).
Proof.
  intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (q =? p) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma trip_rep_same : forall mn q k x, mn <= k -> q <> 0 -> trip_cnt mn q q k x = zind (x =? REP_3_6).
Proof.
  intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma trip_z : forall mn p k x, mn <= k -> trip_cnt mn 0 p k x = if k <=? 10 then zind (x =? REPZ_3_10) else zind (x =? REPZ_11_138).
Proof. intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma run_cont : forall (m : nat) t n v x, 1 <= t <= 6 * Z.of_nat m -> 1 <= v <= 15 ->
  n + t - 1 <= mc -> (forall i, n <= i < n + t -> L i = v) -> L (n + t) <> v -> L n = v ->
  TC n v v 0 6 3 x =
    (t / 6) * zind (x =? REP_3_6) + (let u := t mod 6 in if u =? 0 then 0 else if u <? 3 then u * zind (x =? v) else zind (x =? REP_3_6))
    + TCs (n + t) v x.
Proof.
  induction m as [|m IH]; intros t n v x Ht Hv Hn Hrun Hend Hn0; [lia|].
  destruct (Z_lt_le_dec t 6) as [T6|T6].
  - rewrite (chunk (Z.to_nat t) n v v 0 6 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia. rewrite Z.div_small, Z.mod_small by lia. cbv zeta.
    replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.ltb_spec t 3).
    + rewrite trip_short by lia. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + rewrite trip_rep_same by lia. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
  - rewrite (chunk 6 n v v 0 6 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 6) with 6. rewrite trip_rep_same by lia. change (0 + 6) with 6.
    pose proof (Z.div_mod t 6 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound t 6 ltac:(lia)) as MB.
    assert (D6 : (t - 6) / 6 = t / 6 - 1) by (Z.to_euclidean_division_equations; lia).
    assert (M6 : (t - 6) mod 6 = t mod 6) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec t 6) as [->|N6].
    +
      unfold TCs. change (6 / 6) with 1. change (6 mod 6) with 0. cbn [Z.eqb Pos.eqb]. destruct (x =? REP_3_6); cbn [zind]; lia.
    +
      unfold TCs at 1. rewrite (Hrun (n + 6)) by lia. unfold tree_counts.
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
      rewrite (IH (t - 6) (n + 6) v x ltac:(lia) Hv ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 6 + (t - 6)) with (n + t) by lia; exact Hend | apply Hrun; lia].
      rewrite D6, M6. replace (n + 6 + (t - 6)) with (n + t) by lia. cbv zeta.
      destruct (x =? REP_3_6); destruct (x =? v); destruct (t mod 6 =? 0); destruct (t mod 6 <? 3); cbn [zind]; lia.
Qed.

Lemma run_nz : forall r n p v x, 1 <= r -> 1 <= v <= 15 -> p <> v ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = v) -> L (n + r) <> v -> L n = v ->
  TCs n p x = E1 r * zind (x =? v) + M1 r * zind (x =? REP_3_6) + TCs (n + r) v x.
Proof.
  intros r n p v x Hr Hv Hpv Hn Hrun Hend Hn0.
  unfold TCs at 1. rewrite Hn0. unfold tree_counts.
  replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (p =? v) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold E1, M1.
  destruct (Z_lt_le_dec r 7) as [R7|R7].
  - rewrite (chunk (Z.to_nat r) n p v 0 7 4 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia.
    destruct (Z.leb_spec r 3).
    + rewrite trip_short by lia. replace (r <=? 6) with true by (symmetry; apply Z.leb_le; lia).
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + rewrite trip_rep_new by lia. replace (r <=? 6) with true by (symmetry; apply Z.leb_le; lia).
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
  - rewrite (chunk 7 n p v 0 7 4 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 7) with 7. rewrite trip_rep_new by lia.
    replace (r <=? 3) with false by (symmetry; apply Z.leb_gt; lia). replace (r <=? 6) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Z.eq_dec r 7) as [->|N7].
    + change ((7 - 7) / 6) with 0. change ((7 - 7) mod 6) with 0. cbv zeta. change (0 <? 3) with true. change (3 <=? 0) with false. cbv iota.
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + unfold TCs at 1. rewrite (Hrun (n + 7)) by lia. unfold tree_counts.
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
      rewrite (run_cont (Z.to_nat (r - 7)) (r - 7) (n + 7) v x ltac:(lia) Hv ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 7 + (r - 7)) with (n + r) by lia; exact Hend | apply Hrun; lia].
      replace (n + 7 + (r - 7)) with (n + r) by lia. cbv zeta.
      pose proof (Z.mod_pos_bound (r - 7) 6 ltac:(lia)).
      destruct (Z.eqb_spec ((r - 7) mod 6) 0) as [E0|NE0].
      * rewrite E0. change (0 <? 3) with true. change (3 <=? 0) with false. cbv iota. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
      * destruct (Z.ltb_spec ((r - 7) mod 6) 3).
        -- replace (3 <=? (r - 7) mod 6) with false by (symmetry; apply Z.leb_gt; lia). destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
        -- replace (3 <=? (r - 7) mod 6) with true by (symmetry; apply Z.leb_le; lia). destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
Qed.

Lemma run_z : forall (m : nat) r n p x, 1 <= r <= 138 * Z.of_nat m ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = 0) -> L (n + r) <> 0 -> L n = 0 ->
  TCs n p x = e0 r * zind (x =? 0) + e17 r * zind (x =? REPZ_3_10) + e18 r * zind (x =? REPZ_11_138) + TCs (n + r) 0 x.
Proof.
  induction m as [|m IH]; intros r n p x Hr Hn Hrun Hend Hn0; [lia|].
  unfold TCs at 1. rewrite Hn0. unfold tree_counts. cbn [Z.eqb Pos.eqb].
  unfold e0, e17, e18.
  destruct (Z_lt_le_dec r 138) as [R|R].
  - rewrite (chunk (Z.to_nat r) n p 0 0 138 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia. rewrite Z.mod_small, Z.div_small by lia. cbv zeta. change (0 + r) with r.
    destruct (Z.ltb_spec r 3).
    + rewrite trip_short by lia. replace (3 <=? r) with false by (symmetry; apply Z.leb_gt; lia). replace (11 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
      cbn [andb]. destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
    + rewrite trip_z by lia. replace (3 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      destruct (Z.leb_spec r 10).
      * replace (11 <=? r) with false by (symmetry; apply Z.leb_gt; lia). destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
      * replace (11 <=? r) with true by (symmetry; apply Z.leb_le; lia). destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
  - rewrite (chunk 138 n p 0 0 138 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 138) with 138. rewrite trip_z by lia. change (0 + 138 <=? 10) with false. cbv iota.
    pose proof (Z.mod_pos_bound r 138 ltac:(lia)) as MB.
    assert (D138 : (r - 138) / 138 = r / 138 - 1) by (Z.to_euclidean_division_equations; lia).
    assert (M138 : (r - 138) mod 138 = r mod 138) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec r 138) as [->|N].
    + change (138 mod 138) with 0. change (138 / 138) with 1. cbv zeta. change (0 <? 3) with true. change (3 <=? 0) with false. change (11 <=? 0) with false. cbn [andb].
      destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
    + fold (TCs (n + 138) 0 x).
      rewrite (IH (r - 138) (n + 138) 0 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 138 + (r - 138)) with (n + r) by lia; exact Hend | apply Hrun; lia].
      unfold e0, e17, e18. rewrite D138, M138. replace (n + 138 + (r - 138)) with (n + r) by lia. cbv zeta.
      destruct (r mod 138 <? 3); destruct ((3 <=? r mod 138) && (r mod 138 <=? 10)); destruct (11 <=? r mod 138);
        destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
Qed.

Lemma run_any : forall r n p v x, 1 <= r -> 0 <= v <= 15 -> p <> v ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = v) -> L (n + r) <> v -> L n = v ->
  TCs n p x = RUN v r x + TCs (n + r) v x.
Proof.
  intros r n p v x Hr Hv Hpv Hn Hrun Hend Hn0. unfold RUN.
  destruct (Z.eqb_spec v 0) as [->|Nv].
  - apply (run_z (Z.to_nat r)); try assumption. lia.
  - apply run_nz; try assumption. lia.
Qed.

Fixpoint runlen (v i : Z) (f : nat) : Z :=
  match f with O => 0 | S f' => if L i =? v then 1 + runlen v (i + 1) f' else 0 end.

Lemma runlen_spec : forall f v i, 0 <= runlen v i f <= Z.of_nat f
  /\ (forall j, i <= j < i + runlen v i f -> L j = v)
  /\ (runlen v i f < Z.of_nat f -> L (i + runlen v i f) <> v).
Proof.
  induction f as [|f IH]; intros v i; cbn [runlen].
  - split; [lia|]. split; [intros; lia | intros; lia].
  - destruct (Z.eqb_spec (L i) v) as [E|N].
    + destruct (IH v (i + 1)) as (A & B & C). split; [lia|]. split.
      * intros j Hj. destruct (Z.eq_dec j i) as [->|Nj]; [exact E | apply B; lia].
      * intros Hlt. replace (i + (1 + runlen v (i + 1) f)) with (i + 1 + runlen v (i + 1) f) by lia. apply C. lia.
    + split; [lia|]. split; [intros; lia | intros _; rewrite Z.add_0_r; exact N].
Qed.

Lemma max_run : forall n, 0 <= n <= mc -> exists r, 1 <= r /\ n + r - 1 <= mc
  /\ (forall i, n <= i < n + r -> L i = L n) /\ L (n + r) <> L n.
Proof.
  intros n Hn. destruct (runlen_spec (Z.to_nat (mc + 2 - n)) (L n) n) as (A & B & C).
  set (r := runlen (L n) n (Z.to_nat (mc + 2 - n))) in *.
  assert (R1 : 1 <= r).
  { subst r. replace (Z.to_nat (mc + 2 - n)) with (S (Z.to_nat (mc + 1 - n))) by lia. cbn [runlen]. rewrite Z.eqb_refl.
    pose proof (runlen_spec (Z.to_nat (mc + 1 - n)) (L n) (n + 1)). lia. }
  assert (Rlt : r < Z.of_nat (Z.to_nat (mc + 2 - n))).
  { destruct (Z_lt_le_dec r (Z.of_nat (Z.to_nat (mc + 2 - n)))) as [|Ge]; [assumption|]. exfalso.
    pose proof (B (mc + 1) ltac:(lia)). pose proof (HL n ltac:(lia)). lia. }
  exists r. split; [exact R1|]. split; [lia|]. split; [exact B | exact (C Rlt)].
Qed.

Lemma zsum_run : forall (P : Z -> bool) n r v, 0 <= r -> (forall i, n <= i < n + r -> L i = v) ->
  zsum (fun i => zind (P (L i))) n (Z.to_nat r) = r * zind (P v).
Proof.
  intros P n r v Hr Hrun.
  rewrite (zsum_ext (fun i => zind (P (L i))) (fun _ => zind (P v))) by (intros i Hi; rewrite Hrun by lia; reflexivity).
  destruct (P v); cbn [zind].
  - rewrite zsum_const1. lia.
  - rewrite zsum_0 by (intros; reflexivity). lia.
Qed.

Lemma scan_from : forall (d : nat) n p, Z.of_nat d = mc + 1 - n -> 0 <= n <= mc + 1 -> (n <= mc -> p <> L n) -> -1 <= p <= 15 ->
  (forall j, 1 <= j <= 15 -> TCs n p j <= zsum (fun i => zind (L i =? j)) n d)
  /\ zsum (fun j => TCs n p j) 1 15 + 3 * TCs n p REP_3_6 <= zsum (fun i => zind (negb (L i =? 0))) n d
  /\ 4 * TCs n p REP_3_6 <= zsum (fun i => zind (negb (L i =? 0))) n d
  /\ TCs n p 0 = lsum e0 (zr L n d 0) /\ TCs n p REPZ_3_10 = lsum e17 (zr L n d 0) /\ TCs n p REPZ_11_138 = lsum e18 (zr L n d 0)
  /\ (forall x, 0 <= TCs n p x).
Proof.
  induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf). intros n p Hd Hn Hp Rp.
  unfold REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (Z_lt_le_dec mc n) as [END|GO].
  -
    assert (d = 0%nat) by lia. subst d.
    assert (Z0 : forall x, TCs n p x = 0) by (intros x; unfold TCs; destruct (tree_counts p (L n)); apply TC_end; lia).
    rewrite (zsum_0 (fun j : Z => TCs n p j) 1 15) by (intros; apply Z0).
    rewrite !Z0. cbn [zsum zr Z.eqb lsum]. repeat split; intros; rewrite ?Z0; lia.
  - destruct (max_run n ltac:(lia)) as (r & Hr & Hnr & Hrun & Hend).
    pose proof (HL n ltac:(lia)) as Rv. set (v := L n) in *.
    assert (RA : forall x, TCs n p x = RUN v r x + TCs (n + r) v x).
    { intros x. apply run_any; try assumption; try lia; apply Hp; lia. }
    assert (Hp' : n + r <= mc -> v <> L (n + r)) by (intros _ E; apply Hend; rewrite E; reflexivity).
    destruct (IH (Z.to_nat (mc + 1 - (n + r))) ltac:(lia) (n + r) v ltac:(lia) ltac:(lia) Hp' ltac:(lia)) as (I1 & I2 & I3 & I4a & I4b & I4c & I5).
    replace d with (Z.to_nat r + Z.to_nat (mc + 1 - (n + r)))%nat by lia.
    rewrite !zsum_split. rewrite !Z2Nat.id by lia. replace (n + Z.of_nat (Z.to_nat r)) with (n + r) by lia.
    rewrite (zsum_run (fun y => negb (y =? 0)) n r v) by (try lia; exact Hrun).
    assert (ZR : forall f, lsum f (zr L n (Z.to_nat r + Z.to_nat (mc + 1 - (n + r))) 0) =
                         (if v =? 0 then f r else 0) + lsum f (zr L (n + r) (Z.to_nat (mc + 1 - (n + r))) 0)).
    { intros f. destruct (Z.eqb_spec v 0) as [V0|V0].
      - rewrite zr_zeros by (intros; rewrite Hrun by lia; exact V0). rewrite Z2Nat.id, Z.add_0_l by lia.
        destruct (Z.to_nat (mc + 1 - (n + r))) as [|m] eqn:Em.
        + rewrite !zr_end. rewrite Z.eqb_refl. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia.
        + rewrite (zr_nonzero L m (n + r) r) by (rewrite <- V0; exact Hend). rewrite (zr_nonzero L m (n + r) 0) by (rewrite <- V0; exact Hend).
          replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. cbn [app lsum]. lia.
      - assert (G : forall c m i, (forall j, i <= j < i + Z.of_nat c -> L j <> 0) -> zr L i (c + m) 0 = zr L (i + Z.of_nat c) m 0).
        { induction c as [|c IHc]; intros m i Hnz; [cbn [Nat.add]; rewrite Z.add_0_r; reflexivity|].
          cbn [Nat.add]. rewrite zr_nonzero by (apply Hnz; lia). cbn [Z.eqb app].
          rewrite (IHc m (i + 1)) by (intros; apply Hnz; lia). f_equal. lia. }
        rewrite G by (intros; rewrite Hrun by lia; exact V0). rewrite Z2Nat.id by lia. lia. }
    rewrite !ZR.
    assert (RUNv : forall x, RUN v r x = (if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? 17) + e18 r * zind (x =? 18)
                                        else E1 r * zind (x =? v) + M1 r * zind (x =? 16))) by (intros; reflexivity).
    pose proof (E1_M1_facts r ltac:(lia)) as (F1 & F2 & F3 & F4). pose proof (e_facts r ltac:(lia)) as (G1 & G2 & G3 & G4).
    assert (NN : forall x, 0 <= RUN v r x).
    { intros x. rewrite RUNv. destruct (v =? 0); destruct (x =? 0); destruct (x =? 17); destruct (x =? 18); destruct (x =? v); destruct (x =? 16); cbn [zind]; lia. }
    assert (S4 : forall x, x = 0 \/ x = 17 \/ x = 18 ->
              TCs n p x = (if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? 17) + e18 r * zind (x =? 18) else 0) + TCs (n + r) v x).
    { intros x Hx. rewrite RA, RUNv. destruct (Z.eqb_spec v 0) as [V0|V0]; [reflexivity|].
      replace (x =? v) with false by (symmetry; apply Z.eqb_neq; lia). replace (x =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    +
      intros j Hj. rewrite RA. rewrite zsum_split, Z2Nat.id by lia. rewrite (zsum_run (fun y => y =? j) n r v) by (try lia; exact Hrun).
      pose proof (I1 j Hj). rewrite RUNv. idtac.
      destruct (Z.eqb_spec v 0) as [V0|V0].
      * replace (v =? 0) with true by (symmetry; apply Z.eqb_eq; exact V0). replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (v =? j) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (j =? 17) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 18) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
      * replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact V0). replace (j =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec j v) as [->|Njv]; [rewrite Z.eqb_refl | replace (v =? j) with false by (symmetry; apply Z.eqb_neq; lia)]; cbn [zind]; lia.
    +
      rewrite (zsum_ext (fun j => TCs n p j) (fun j => RUN v r j + TCs (n + r) v j)) by (intros; apply RA). rewrite zsum_add, RA.
      change (zsum (RUN v r) 1 15) with (zsum (fun j => RUN v r j) 1 15). change (zsum (TCs (n + r) v) 1 15) with (zsum (fun j => TCs (n + r) v j) 1 15).
      assert (SR : zsum (fun j => RUN v r j) 1 15 = (if v =? 0 then 0 else E1 r)).
      { destruct (Z.eqb_spec v 0) as [V0|V0].
        - apply zsum_0. intros j Hj. rewrite RUNv; try rewrite V0; cbn [Z.eqb Pos.eqb]. idtac.
          replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 17) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 18) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
        - rewrite (zsum_single (fun j => RUN v r j) 1 15 v); [| lia |].
          + rewrite RUNv. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. idtac. replace (v =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
          + intros j Hj Njv. rewrite RUNv. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). idtac.
            replace (j =? v) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia. }
      rewrite SR, RUNv.
      destruct (Z.eqb_spec v 0) as [V0|V0]; [cbn [Z.eqb Pos.eqb zind negb]; lia|].
      replace (16 =? v) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb Pos.eqb zind negb]. lia.
    +
      rewrite RA, RUNv.
      destruct (Z.eqb_spec v 0) as [V0|V0]; [cbn [Z.eqb Pos.eqb zind negb]; lia|].
      replace (16 =? v) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb Pos.eqb zind negb]. lia.
    + rewrite (S4 0 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + rewrite (S4 17 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + rewrite (S4 18 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + intros x. rewrite RA. pose proof (NN x). pose proof (I5 x). lia.
Qed.

End Scan.


Theorem scan_facts : forall (L : Z -> Z) (mc : Z),
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> 15 < L (mc + 1) ->
  let cnt j := zsum (fun i => zind (L i =? j)) 0 (Z.to_nat (mc + 1)) in
  let nz := zsum (fun i => zind (negb (L i =? 0))) 0 (Z.to_nat (mc + 1)) in
  let runs := zruns L 0 (Z.to_nat (mc + 1)) in
  (forall j, 1 <= j <= 15 -> TDcnt L mc j <= cnt j)
  /\ zsum (TDcnt L mc) 1 15 + 3 * TDcnt L mc REP_3_6 <= nz
  /\ 4 * TDcnt L mc REP_3_6 <= nz
  /\ TDcnt L mc 0 = lsum e0 runs
  /\ TDcnt L mc REPZ_3_10 = lsum e17 runs
  /\ TDcnt L mc REPZ_11_138 = lsum e18 runs
  /\ (forall x, 0 <= TDcnt L mc x).
Proof.
  intros L mc Hmc HL HG. cbv zeta.
  assert (E : forall x, TDcnt L mc x = TCs L mc 0 (-1) x) by (intros x; rewrite (TDcnt_TC L mc Hmc HL x); reflexivity).
  pose proof (HL 0 ltac:(lia)).
  destruct (scan_from L mc HL HG (Z.to_nat (mc + 1)) 0 (-1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  rewrite !zruns_lsum.
  split; [intros j Hj; rewrite E; apply A1; exact Hj|].
  split; [rewrite (zsum_ext (TDcnt L mc) (fun j => TCs L mc 0 (-1) j)) by (intros; apply E); rewrite E; exact A2|].
  split; [rewrite E; exact A3|]. split; [rewrite E; exact A4|]. split; [rewrite E; exact A5|]. split; [rewrite E; exact A6|].
  intros x. rewrite E. apply A7.
Qed.

Corollary scan_zero_runs : forall (L : Z -> Z) (mc : Z),
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> 15 < L (mc + 1) ->
  let runs := zruns L 0 (Z.to_nat (mc + 1)) in
  (forall r, In r runs -> r <= 276) ->
  TDcnt L mc 0 = lsum is1 runs + 2 * lsum is2 runs
  /\ TDcnt L mc REPZ_3_10 = lsum isa runs
  /\ TDcnt L mc REPZ_11_138 = lsum isb runs + lsum nlong runs.
Proof.
  intros L mc Hmc HL HG. cbv zeta. intros H276.
  destruct (scan_facts L mc Hmc HL HG) as (_ & _ & _ & A4 & A5 & A6 & _).
  assert (R : forall r, In r (zruns L 0 (Z.to_nat (mc + 1))) -> 1 <= r <= 276).
  { intros r Hr. pose proof (zruns_pos L 0 _ r Hr). pose proof (H276 r Hr). lia. }
  split; [| split].
  - rewrite A4, <- lsum_scale, <- lsum_add. apply lsum_ext. intros r Hr. rewrite e0_is12 by exact (R r Hr). lia.
  - rewrite A5. apply lsum_ext. intros r Hr. apply e17_isa. exact (R r Hr).
  - rewrite A6, <- lsum_add. apply lsum_ext. intros r Hr. apply e18_isb. exact (R r Hr).
Qed.

Corollary scan_total : forall (L : Z -> Z) (mc : Z),
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> 15 < L (mc + 1) ->
  zsum (TDcnt L mc) 0 19 <= mc + 1.
Proof.
  intros L mc Hmc HL HG.
  destruct (scan_facts L mc Hmc HL HG) as (_ & A2 & _ & A4 & A5 & A6 & A7).
  pose proof (A7 REP_3_6) as P16.
  assert (Z3 : TDcnt L mc 0 + TDcnt L mc REPZ_3_10 + TDcnt L mc REPZ_11_138 <= zsum (fun j => zind (L j =? 0)) 0 (Z.to_nat (mc + 1))).
  { rewrite A4, A5, A6, <- zruns_sum, <- !lsum_add. apply lsum_le. intros r Hr.
    pose proof (zruns_pos L 0 _ r Hr). pose proof (e_facts r ltac:(lia)). lia. }
  assert (TOT : zsum (fun j => zind (L j =? 0)) 0 (Z.to_nat (mc + 1)) + zsum (fun i => zind (negb (L i =? 0))) 0 (Z.to_nat (mc + 1)) = mc + 1).
  { rewrite <- zsum_add. rewrite (zsum_ext _ (fun _ => 1)) by (intros; destruct (L i =? 0); reflexivity). rewrite zsum_const1. lia. }
  change 19%nat with (S (15 + 3))%nat. rewrite zsum_shift, zsum_split.
  change (0 + 1 + Z.of_nat 15) with 16. change (0 + 1) with 1.
  change (zsum (TDcnt L mc) 16 3) with (0 + TDcnt L mc (16 + 0) + TDcnt L mc (16 + 1) + TDcnt L mc (16 + 2)).
  change (16 + 0) with REP_3_6. change (16 + 1) with REPZ_3_10. change (16 + 2) with REPZ_11_138. lia.
Qed.
End OverlayScan.

Module OverlayGlue.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeE3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeO2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.RefDeflSafeO6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.OverlayScan.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma forallb_zrange : forall (f : Z -> bool) lo n, forallb f (zrange lo n) = true ->
  forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
  intros f lo n H i Hi. rewrite forallb_forall in H. apply H. unfold zrange.
  apply in_map_iff. exists (Z.to_nat (i - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma xl_table : forall lc, 0 <= lc < 256 -> xl_of_lcode (arr_get length_code_a lc + LITERALS + 1) = arr_get extra_lbits_a (arr_get length_code_a lc).
Proof.
  pose proof (forallb_zrange (fun lc => xl_of_lcode (arr_get length_code_a lc + LITERALS + 1) =? arr_get extra_lbits_a (arr_get length_code_a lc)) 0 256
                ltac:(vm_compute; reflexivity)) as H.
  intros lc Hlc. apply Z.eqb_eq. apply H. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

Lemma xd_table : forall d, 0 <= d < 30 -> xd_of_dcode d = arr_get extra_dbits_a d.
Proof.
  pose proof (forallb_zrange (fun d => xd_of_dcode d =? arr_get extra_dbits_a d) 0 30 ltac:(vm_compute; reflexivity)) as H.
  intros d Hd. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma sl_table : forall c, 0 <= c < 286 -> sl_of_code c = arr_get static_ltree_dl c.
Proof.
  pose proof (forallb_zrange (fun c => sl_of_code c =? arr_get static_ltree_dl c) 0 286 ltac:(vm_compute; reflexivity)) as H.
  intros c Hc. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma sd_table : forall d, 0 <= d < 30 -> arr_get static_dtree_dl d = 5.
Proof.
  pose proof (forallb_zrange (fun d => arr_get static_dtree_dl d =? 5) 0 30 ltac:(vm_compute; reflexivity)) as H.
  intros d Hd. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma xb_table : forall b, 0 <= b < 19 -> xb_of_bl b = arr_get extra_blbits_a b.
Proof.
  pose proof (forallb_zrange (fun b => xb_of_bl b =? arr_get extra_blbits_a b) 0 19 ltac:(vm_compute; reflexivity)) as H.
  intros b Hb. apply Z.eqb_eq. apply H. cbn. lia.
Qed.


Lemma lsum_zrange : forall f lo n, lsum f (zrange lo n) = zsum f lo n.
Proof.
  intros f lo n. unfold zrange. revert lo. induction n as [|n IH]; intros lo; [reflexivity|].
  cbn [seq map lsum]. rewrite zsum_shift, Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map. rewrite <- (IH (lo + 1)). f_equal. apply map_ext. intros; lia.
Qed.

Lemma countZ_zrange : forall P lo n, countZ P (zrange lo n) = zsum (fun i => zind (P i)) lo n.
Proof. intros. unfold countZ. rewrite lsum_zrange. apply zsum_ext. intros. unfold zind. reflexivity. Qed.

Lemma lmax_filter_zrange : forall (P : Z -> bool) lo n m,
  0 <= lo -> lo <= m < lo + Z.of_nat n -> P m = true -> (forall i, lo <= i < lo + Z.of_nat n -> P i = true -> i <= m) ->
  lmax (fun c => c) (filter P (zrange lo n)) = m.
Proof.
  intros P lo n m Hlo Hm Pm Hmax.
  assert (IN : In m (filter P (zrange lo n))).
  { apply filter_In. split; [| exact Pm]. unfold zrange. apply in_map_iff. exists (Z.to_nat (m - lo)). split; [lia|]. apply in_seq. lia. }
  pose proof (lmax_ge (fun c => c) _ m IN) as A. cbv beta in A.
  destruct (lmax_in (fun c => c) (filter P (zrange lo n)) ltac:(intros E; rewrite E in IN; exact IN)
              ltac:(intros x Hx; apply filter_In in Hx; destruct Hx as [Hx _]; unfold zrange in Hx; apply in_map_iff in Hx; destruct Hx as (k & <- & _); lia)) as (x & Hx & Ex).
  cbv beta in Ex. apply filter_In in Hx. destruct Hx as [Hx Px]. unfold zrange in Hx. apply in_map_iff in Hx. destruct Hx as (k & Ek & Hk). apply in_seq in Hk.
  pose proof (Hmax x ltac:(lia) Px). lia.
Qed.


Definition osym_of (s : deflate_state) (j : Z) : osym :=
  if sym_isdist s j then OPair (sym_lcode s j) (sym_dcode s j) else OLit (sym_lcode s j).

Definition osyms (s : deflate_state) : list osym := map (fun k => osym_of s (Z.of_nat k)) (seq 0 (Z.to_nat (nsym s))).

Lemma ssum_map : forall (f : osym -> Z) (g : nat -> osym) st n,
  ssum f (map g (seq st n)) = zsum (fun j => f (g (Z.to_nat j))) (Z.of_nat st) n.
Proof.
  intros f g st n. revert st. induction n as [|n IH]; intros st; [reflexivity|].
  cbn [seq map ssum]. rewrite zsum_shift, IH, Nat2Z.id. f_equal. f_equal. lia.
Qed.

Lemma ssum_osyms : forall s f, 0 <= nsym s -> ssum f (osyms s) = zsum (fun j => f (osym_of s j)) 0 (Z.to_nat (nsym s)).
Proof.
  intros s f Hn. unfold osyms. rewrite ssum_map. apply zsum_ext. intros j Hj. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma length_osyms : forall s, 0 <= nsym s -> Z.of_nat (length (osyms s)) = nsym s.
Proof. intros. unfold osyms. rewrite length_map, length_seq. lia. Qed.

Section Block.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.
Let N := nsym s.
Let RN : 0 <= N <= ds_lit_bufsize s - 1 := op_nsym _ OP.

Lemma fL_osyms : forall b, ob_syms b = osyms s -> forall c, 0 <= c < 286 -> fL b c = arr_get (ds_dyn_ltree_fc s) c.
Proof.
  intros b Hb c Hc. destruct (op_hist _ OP) as (HL & _ & _). rewrite (HL c) by (unfold L_CODES; lia).
  unfold fL, scount. rewrite Hb, ssum_osyms by lia. unfold END_BLOCK. f_equal.
  apply zsum_ext. intros j Hj. unfold osym_of. destruct (sym_isdist s j); reflexivity.
Qed.

Lemma gD_osyms : forall b, ob_syms b = osyms s -> forall d, 0 <= d < 30 -> gD b d = arr_get (ds_dyn_dtree_fc s) d.
Proof.
  intros b Hb d Hd. destruct (op_hist _ OP) as (_ & HD & _). rewrite (HD d) by (unfold D_CODES; lia).
  unfold gD, scount. rewrite Hb, ssum_osyms by lia.
  apply zsum_ext. intros j Hj. unfold osym_of. destruct (sym_isdist s j); reflexivity.
Qed.

Lemma NSYM_osyms : forall b, ob_syms b = osyms s -> NSYM b = N.
Proof. intros b Hb. unfold NSYM. rewrite Hb. apply length_osyms. lia. Qed.

Lemma dcostS_osym : forall b j, 0 <= j < N ->
  dcostS b (osym_of s j) = (if sym_isdist s j then ob_lenL b (sym_lcode s j) + sym_xl s j + ob_lenD b (sym_dcode s j) + sym_xd s j else ob_lenL b (sym_lcode s j)).
Proof.
  intros b j Hj. pose proof (sym_codes s OP j Hj) as (A & B & C & Lit & M).
  unfold osym_of, dcostS. destruct (sym_isdist s j) eqn:ISD; [|reflexivity].
  destruct (M eq_refl) as (M1 & M2 & M3). unfold sym_xl, sym_xd. rewrite xd_table by (unfold D_CODES in M2; lia).
  unfold sym_lcode in *. unfold sym_isdist in ISD. destruct (sym_dist s (3 * j) =? 0); [discriminate|].
  rewrite xl_table by lia. reflexivity.
Qed.

Lemma dcostS_dcost : forall b (LD DD : arr) j, 0 <= j < N ->
  (forall c, ob_lenL b c = arr_get LD c) -> (forall d, ob_lenD b d = arr_get DD d) ->
  dcostS b (osym_of s j) = dcost LD DD s j.
Proof. intros b LD DD j Hj HL HD. rewrite dcostS_osym by exact Hj. unfold dcost. rewrite <- !HL, <- !HD. reflexivity. Qed.

Lemma scostS_osym : forall j, 0 <= j < N -> scostS (osym_of s j) = scost s j.
Proof.
  intros j Hj. pose proof (sym_codes s OP j Hj) as (A & B & C & Lit & M).
  unfold osym_of, scostS, scost, dcost. unfold L_CODES in A.
  destruct (sym_isdist s j) eqn:ISD.
  - destruct (M eq_refl) as (M1 & M2 & M3). unfold D_CODES in M2. unfold sym_xl, sym_xd.
    rewrite xd_table, sd_table, sl_table by lia.
    unfold sym_lcode in *. unfold sym_isdist in ISD. destruct (sym_dist s (3 * j) =? 0); [discriminate|].
    rewrite xl_table by lia. lia.
  - rewrite sl_table by lia. reflexivity.
Qed.


Let TP : TPF s := tree_phase s OP.

Lemma prefix_from_core :
  (ov_hdr s - 3) + zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N) <= 8 * ds_lit_bufsize s - 10 ->
  forall k, 0 <= k < N -> ov_wpos s k <= ov_rpos s k.
Proof.
  intros CORE k Hk. pose proof (op_biv _ OP) as Rbv.
  unfold ov_wpos, ov_rpos.
  assert (EXk : zsum (dcost (ov_LD s) (ov_DD s) s) 0 (Z.to_nat k) <= 24 * k + zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N)).
  { pose proof (zsum_mono (dcost (ov_LD s) (ov_DD s) s) (fun j => 24 + Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat k) ltac:(intros; cbv beta; lia)) as M.
    rewrite zsum_add in M. change (zsum (fun _ : Z => 24) 0 (Z.to_nat k)) with (zsum (fun i : Z => 24) 0 (Z.to_nat k)) in M.
    assert (C24 : forall m lo, zsum (fun _ : Z => 24) lo m = 24 * Z.of_nat m) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
    rewrite C24, Z2Nat.id in M by lia.
    replace (Z.to_nat N) with (Z.to_nat k + Z.to_nat (N - k))%nat by lia. rewrite zsum_split.
    pose proof (zsum_nonneg (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) (0 + Z.of_nat (Z.to_nat k)) (Z.to_nat (N - k)) ltac:(intros; cbv beta; lia)).
    lia. }
  lia.
Qed.


Lemma bbl_step : forall f X mb, build_bl_tree_loop (S f) X mb =
  (if 3 <=? mb then if negb (Len X TB (arr_get bl_order_a mb) =? 0) then mb else build_bl_tree_loop f X (mb - 1) else mb).
Proof. reflexivity. Qed.

Lemma mb_le_17 : Len (ov_X5 s) TB 15 = 0 -> ov_mb s <= 17.
Proof.
  intros H. rewrite ov_mb_eq. unfold tfb_mb. rewrite bbl_step.
  change (3 <=? 18) with true. change (arr_get bl_order_a 18) with 15. rewrite H. cbn [Z.eqb negb].
  pose proof (build_bl_tree_loop_range 16 (ov_X5 s) (18 - 1) ltac:(lia)). lia.
Qed.



Hypothesis HN : 1 <= N.
Hypothesis HB : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1.

Let lmax := ds_l_max_code (ov_X6 s).
Let dmax := ds_d_max_code (ov_X6 s).
Let LX : Z -> Z := fun i => Len (ov_X6 s) TL i.
Let DX : Z -> Z := fun i => Len (ov_X6 s) TD i.

Definition mkblock (FlD FlB : list Z) : oblock := {|
  ob_syms := osyms s;
  ob_lenL := fun c => arr_get (tree_dl (ov_X1 s) TL) c;
  ob_lenD := fun d => arr_get (tree_dl (ov_X2 s) TD) d;
  ob_forced := FlD;
  ob_BC := fun x => arr_get (ov_BC s) x;
  ob_BD := fun x => arr_get (tree_dl (ov_X5 s) TB) x;
  ob_bforced := FlB;
  ob_blcodes := ov_mb s + 1;
  ob_Hc1 := ov_hdr s - 3 |}.

Lemma zruns_ext : forall (L L' : Z -> Z) lo n, (forall i, lo <= i < lo + Z.of_nat n -> L i = L' i) -> zruns L lo n = zruns L' lo n.
Proof.
  intros L L' lo n H. unfold zruns.
  assert (G : forall m i cur acc, (forall j, i <= j < i + Z.of_nat m -> L j = L' j) -> zruns_go L i m cur acc = zruns_go L' i m cur acc).
  { induction m as [|m IH]; intros i cur acc Hm; cbn [zruns_go]; [reflexivity|].
    rewrite (Hm i) by lia. destruct (L' i =? 0); apply IH; intros; apply Hm; lia. }
  apply G. exact H.
Qed.

Lemma zruns_nil : forall L lo, zruns L lo 0 = [].
Proof. reflexivity. Qed.

Lemma Forall_osyms : Forall (fun x => match x with OLit c => 0 <= c < 256 | OPair lc dc => 257 <= lc <= 285 /\ 0 <= dc <= 29 end) (osyms s).
Proof.
  unfold osyms. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk.
  pose proof (sym_codes s OP (Z.of_nat k) ltac:(lia)) as (A & B & C & Lit & M). unfold L_CODES, D_CODES in *.
  unfold osym_of. destruct (sym_isdist s (Z.of_nat k)).
  - destruct (M eq_refl) as (M1 & M2 & M3). lia.
  - pose proof (Lit eq_refl). lia.
Qed.

Section WithTrees.
Variable zL : ztree.
Variable zD : ztree.
Variable zB : ztree.
Variable FlL : list Z.
Variable FlD : list Z.
Variable FlB : list Z.
Hypothesis TFL : tree_facts zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL.
Hypothesis TFD : tree_facts zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD.
Hypothesis TFB : tree_facts zB 19 7 (fun x => arr_get (ov_BC s) x) FlB.
Hypothesis ZL1 : forall c, zt_len zL c = arr_get (tree_dl (ov_X1 s) TL) c.
Hypothesis ZL2 : forall d, zt_len zD d = arr_get (tree_dl (ov_X2 s) TD) d.
Hypothesis ZL5 : forall x, zt_len zB x = arr_get (tree_dl (ov_X5 s) TB) x.
Hypothesis LK1 : forall c, c <> lmax + 1 -> LX c = zt_len zL c.
Hypothesis LK2 : forall d, d <> dmax + 1 -> DX d = zt_len zD d.
Hypothesis LK5 : forall x, Len (ov_X6 s) TB x = zt_len zB x.
Hypothesis G1 : LX (lmax + 1) = 65535.
Hypothesis G2 : DX (dmax + 1) = 65535.
Hypothesis MXL : ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL lmax <> 0 /\ forall c, 0 <= c < 286 -> ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL c <> 0 -> c <= lmax.
Hypothesis MXD : ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD dmax <> 0 /\ forall d, 0 <= d < 30 -> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0 -> d <= dmax.
Hypothesis NOFL : FlL = [].

Let b := mkblock FlD FlB.
Let RL : 0 <= lmax < 286 := ltac:(pose proof (tp_lmax _ TP); unfold L_CODES in *; exact H).
Let RD : 0 <= dmax < 30 := ltac:(pose proof (tp_dmax _ TP); unfold D_CODES in *; exact H).

Lemma fL_freq : forall c, 0 <= c < 286 -> fL b c = arr_get (ds_dyn_ltree_fc s) c.
Proof. intros c Hc. apply fL_osyms; [reflexivity | exact Hc]. Qed.

Lemma gD_freq : forall d, 0 <= d < 30 -> gD b d = arr_get (ds_dyn_dtree_fc s) d.
Proof. intros d Hd. apply gD_osyms; [reflexivity | exact Hd]. Qed.

Lemma TFL' : tree_facts zL 286 15 (fL b) [].
Proof. rewrite <- NOFL. apply (tree_facts_ext zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c)); [intros c Hc; symmetry; apply fL_freq; exact Hc | exact TFL]. Qed.

Lemma TFD' : tree_facts zD 30 15 (gD b) FlD.
Proof. apply (tree_facts_ext zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d)); [intros d Hd; symmetry; apply gD_freq; exact Hd | exact TFD]. Qed.

Lemma lenL_used : forall c, 0 <= c < 286 -> ob_lenL b c <> 0 -> 0 < fL b c.
Proof.
  intros c Hc Hl. cbn [ob_lenL b mkblock] in Hl.
  destruct (Z.eq_dec (fL b c) 0) as [Z0|NZ]; [| pose proof (fL_freq c Hc); pose proof (op_fc _ OP TL c); rewrite tree_fc_TL in *; lia].
  exfalso. apply Hl. rewrite <- ZL1. apply (zo_len_unused _ (tf_ok _ _ _ _ _ TFL')); [rewrite (tf_E _ _ _ _ _ TFL'); exact Hc|].
  intros U. apply (proj1 (tf_used _ _ _ _ _ TFL' c Hc)) in U. unfold ffreq in U. cbn [existsb] in U. exact (U Z0).
Qed.

Lemma lenD_used : forall d, 0 <= d < 30 -> ob_lenD b d <> 0 -> (0 <? gD b d) || forcedD b d = true.
Proof.
  intros d Hd Hl. cbn [ob_lenD b mkblock] in Hl. unfold forcedD. cbn [ob_forced b mkblock].
  destruct ((0 <? gD b d) || existsb (Z.eqb d) FlD) eqn:X; [reflexivity|]. exfalso.
  apply Bool.orb_false_iff in X. destruct X as [X1 X2]. apply Z.ltb_ge in X1.
  apply Hl. rewrite <- ZL2. apply (zo_len_unused _ (tf_ok _ _ _ _ _ TFD')); [rewrite (tf_E _ _ _ _ _ TFD'); exact Hd|].
  intros U. apply (proj1 (tf_used _ _ _ _ _ TFD' d Hd)) in U. unfold ffreq in U. rewrite X2 in U.
  pose proof (gD_freq d Hd). pose proof (op_fc _ OP TD d). rewrite tree_fc_TD in *. lia.
Qed.

Lemma lmax_ge_256 : 256 <= lmax.
Proof.
  destruct MXL as [_ M]. apply (M 256 ltac:(lia)). rewrite NOFL. unfold ffreq. cbn [existsb].
  destruct (op_hist _ OP) as (FHL & _). rewrite (FHL 256) by (unfold L_CODES; lia). rewrite Z.eqb_refl. cbn [zind].
  pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? 256)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))). unfold END_BLOCK. lia.
Qed.

Lemma LX_ok : forall i, 0 <= i <= lmax -> 0 <= LX i <= 15.
Proof. intros i Hi. exact (tp_LD _ TP i Hi). Qed.
Lemma DX_ok : forall i, 0 <= i <= dmax -> 0 <= DX i <= 15.
Proof. intros i Hi. exact (tp_DD _ TP i Hi). Qed.
Lemma LX_guard : 15 < LX (lmax + 1). Proof. rewrite G1. lia. Qed.
Lemma DX_guard : 15 < DX (dmax + 1). Proof. rewrite G2. lia. Qed.

Lemma BC_split : forall x, 0 <= x < 19 -> ob_BC b x = TDcnt LX lmax x + TDcnt DX dmax x.
Proof. intros x Hx. cbn [ob_BC b mkblock]. exact (tp_BC _ TP x Hx). Qed.

Lemma gl_WB : zsum (ob_BC b) 0 19 <= 316.
Proof.
  rewrite (zsum_ext (ob_BC b) (fun x => TDcnt LX lmax x + TDcnt DX dmax x)) by (intros; apply BC_split; lia).
  rewrite zsum_add. pose proof (scan_total LX lmax ltac:(lia) LX_ok LX_guard). pose proof (scan_total DX dmax ltac:(lia) DX_ok DX_guard).
  change (zsum (fun i : Z => TDcnt LX lmax i) 0 19) with (zsum (TDcnt LX lmax) 0 19). change (zsum (fun i : Z => TDcnt DX dmax i) 0 19) with (zsum (TDcnt DX dmax) 0 19). lia.
Qed.

Lemma gl_blc : 3 <= ob_blcodes b <= 19 /\ (ob_BD b 15 = 0 -> ob_blcodes b <= 18).
Proof.
  cbn [ob_blcodes ob_BD b mkblock]. pose proof (tp_mb _ TP). split; [lia|].
  intros H15. pose proof (mb_le_17 ltac:(unfold Len; exact H15)). lia.
Qed.

Lemma gl_Hc1 : ob_Hc1 b = 14 + 3 * ob_blcodes b + zsum (fun x => ob_BC b x * (ob_BD b x + xb_of_bl x)) 0 19.
Proof.
  cbn [ob_Hc1 ob_blcodes ob_BC ob_BD b mkblock]. unfold ov_hdr.
  rewrite (zsum_ext (fun x => arr_get (ov_BC s) x * (arr_get (ov_BD s) x + arr_get extra_blbits_a x)) (fun x => arr_get (ov_BC s) x * (arr_get (tree_dl (ov_X5 s) TB) x + xb_of_bl x))); [lia|].
  intros x Hx. rewrite xb_table by lia. unfold ov_BD. rewrite <- (tree_dl_TB (ov_X6 s)), <- (Len_eq (ov_X6 s) TB x), (tp_len5 _ TP x). reflexivity.
Qed.


Lemma usedL_count : forall (P : Z -> Z -> bool),
  (forall i, 0 <= i <= lmax -> P i (LX i) = true -> 0 < fL b i /\ P i (ob_lenL b i) = true) ->
  zsum (fun i => zind (P i (LX i))) 0 (Z.to_nat (lmax + 1)) <= countZ (fun c => (0 <? fL b c) && P c (ob_lenL b c)) (zrange 0 286).
Proof.
  intros P HP. rewrite countZ_zrange.
  replace 286%nat with (Z.to_nat (lmax + 1) + Z.to_nat (286 - (lmax + 1)))%nat by lia. rewrite zsum_split.
  pose proof (zsum_nonneg (fun i => zind ((0 <? fL b i) && P i (ob_lenL b i))) (0 + Z.of_nat (Z.to_nat (lmax + 1))) (Z.to_nat (286 - (lmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
  assert (zsum (fun i => zind (P i (LX i))) 0 (Z.to_nat (lmax + 1)) <= zsum (fun i => zind ((0 <? fL b i) && P i (ob_lenL b i))) 0 (Z.to_nat (lmax + 1))); [|lia].
  apply zsum_mono. intros i Hi. destruct (P i (LX i)) eqn:E; [| apply (proj1 (zind_le1 _))].
  destruct (HP i ltac:(lia) E) as [A B]. rewrite B. replace (0 <? fL b i) with true by (symmetry; apply Z.ltb_lt; exact A). cbn. lia.
Qed.

Lemma usedD_count : forall (P : Z -> Z -> bool),
  (forall i, 0 <= i <= dmax -> P i (DX i) = true -> ((0 <? gD b i) || forcedD b i = true) /\ P i (ob_lenD b i) = true) ->
  zsum (fun i => zind (P i (DX i))) 0 (Z.to_nat (dmax + 1)) <= countZ (fun d => ((0 <? gD b d) || forcedD b d) && P d (ob_lenD b d)) (zrange 0 30).
Proof.
  intros P HP. rewrite countZ_zrange.
  replace 30%nat with (Z.to_nat (dmax + 1) + Z.to_nat (30 - (dmax + 1)))%nat by lia. rewrite zsum_split.
  pose proof (zsum_nonneg (fun i => zind (((0 <? gD b i) || forcedD b i) && P i (ob_lenD b i))) (0 + Z.of_nat (Z.to_nat (dmax + 1))) (Z.to_nat (30 - (dmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
  assert (zsum (fun i => zind (P i (DX i))) 0 (Z.to_nat (dmax + 1)) <= zsum (fun i => zind (((0 <? gD b i) || forcedD b i) && P i (ob_lenD b i))) 0 (Z.to_nat (dmax + 1))); [|lia].
  apply zsum_mono. intros i Hi. destruct (P i (DX i)) eqn:E; [| apply (proj1 (zind_le1 _))].
  destruct (HP i ltac:(lia) E) as [A B]. rewrite A, B. cbn. lia.
Qed.

Lemma LX_lenL : forall i, 0 <= i <= lmax -> LX i = ob_lenL b i.
Proof. intros i Hi. cbn [ob_lenL b mkblock]. rewrite <- ZL1. apply LK1. lia. Qed.
Lemma DX_lenD : forall i, 0 <= i <= dmax -> DX i = ob_lenD b i.
Proof. intros i Hi. cbn [ob_lenD b mkblock]. rewrite <- ZL2. apply LK2. lia. Qed.

Lemma gl_sc1 : forall j, 1 <= j <= 15 ->
  ob_BC b j <= countZ (fun c => (0 <? fL b c) && (ob_lenL b c =? j)) (zrange 0 286) + countZ (fun d => ((0 <? gD b d) || forcedD b d) && (ob_lenD b d =? j)) (zrange 0 30).
Proof.
  intros j Hj. rewrite BC_split by lia.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (S1 & _). destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (T1 & _).
  pose proof (S1 j Hj) as A. pose proof (T1 j Hj) as B. cbv zeta in A, B.
  pose proof (usedL_count (fun _ v => v =? j)) as C. cbv beta in C.
  pose proof (usedD_count (fun _ v => v =? j)) as D. cbv beta in D.
  assert (HC : forall i, 0 <= i <= lmax -> (LX i =? j) = true -> 0 < fL b i /\ (ob_lenL b i =? j) = true).
  { intros i Hi E. rewrite <- LX_lenL by exact Hi. split; [| exact E]. apply lenL_used; [lia|]. rewrite <- LX_lenL by exact Hi. apply Z.eqb_eq in E. lia. }
  assert (HD : forall i, 0 <= i <= dmax -> (DX i =? j) = true -> ((0 <? gD b i) || forcedD b i = true) /\ (ob_lenD b i =? j) = true).
  { intros i Hi E. rewrite <- DX_lenD by exact Hi. split; [| exact E]. apply lenD_used; [lia|]. rewrite <- DX_lenD by exact Hi. apply Z.eqb_eq in E. lia. }
  specialize (C HC). specialize (D HD). lia.
Qed.

Lemma nz_le_UV :
  zsum (fun i => zind (negb (LX i =? 0))) 0 (Z.to_nat (lmax + 1)) + zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= vU b + vV b.
Proof.
  unfold vU, vV.
  pose proof (usedL_count (fun _ v => negb (v =? 0))) as C. cbv beta in C.
  assert (HC : forall i, 0 <= i <= lmax -> negb (LX i =? 0) = true -> 0 < fL b i /\ negb (ob_lenL b i =? 0) = true).
  { intros i Hi E. rewrite <- LX_lenL by exact Hi. split; [| exact E]. apply lenL_used; [lia|]. rewrite <- LX_lenL by exact Hi. apply Bool.negb_true_iff in E. apply Z.eqb_neq in E. exact E. }
  specialize (C HC).
  assert (C' : countZ (fun c => (0 <? fL b c) && negb (ob_lenL b c =? 0)) (zrange 0 286) <= countZ (fun c => 0 <? fL b c) (zrange 0 286)).
  { rewrite !countZ_zrange. apply zsum_mono. intros. destruct (0 <? fL b i), (negb _); cbn; lia. }
  assert (D : zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= countZ (fun d => 0 <? gD b d) (zrange 0 30) + Z.of_nat (length (ob_forced b))).
  { rewrite countZ_zrange.
    replace 30%nat with (Z.to_nat (dmax + 1) + Z.to_nat (30 - (dmax + 1)))%nat by lia. rewrite zsum_split.
    pose proof (zsum_nonneg (fun i => zind (0 <? gD b i)) (0 + Z.of_nat (Z.to_nat (dmax + 1))) (Z.to_nat (30 - (dmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
    pose proof (zsum_existsb_le (ob_forced b) 0 (Z.to_nat (dmax + 1))) as F.
    assert (zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= zsum (fun i => zind (0 <? gD b i)) 0 (Z.to_nat (dmax + 1)) + zsum (fun u => zind (existsb (Z.eqb u) (ob_forced b))) 0 (Z.to_nat (dmax + 1))); [|lia].
    rewrite <- zsum_add. apply zsum_mono. intros i Hi. destruct (Z.eqb_spec (DX i) 0) as [E|NE]; cbn [negb]; [pose proof (zind_le1 (0 <? gD b i)); pose proof (zind_le1 (existsb (Z.eqb i) (ob_forced b))); cbn [zind]; lia|].
    pose proof (lenD_used i ltac:(lia) ltac:(rewrite <- DX_lenD by lia; exact NE)) as U. unfold forcedD in U.
    destruct (0 <? gD b i), (existsb (Z.eqb i) (ob_forced b)); cbn in U |- *; lia. }
  lia.
Qed.

Lemma gl_sc23 : zsum (ob_BC b) 1 15 + 3 * ob_BC b 16 <= vU b + vV b /\ 4 * ob_BC b 16 <= vU b + vV b.
Proof.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (_ & S2 & S3 & _). destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (_ & T2 & T3 & _).
  cbv zeta in S2, S3, T2, T3. pose proof nz_le_UV.
  rewrite (zsum_ext (ob_BC b) (fun x => TDcnt LX lmax x + TDcnt DX dmax x) 1 15) by (intros; apply BC_split; lia). rewrite zsum_add.
  change (zsum (fun i : Z => TDcnt LX lmax i) 1 15) with (zsum (TDcnt LX lmax) 1 15). change (zsum (fun i : Z => TDcnt DX dmax i) 1 15) with (zsum (TDcnt DX dmax) 1 15).
  rewrite (BC_split 16) by lia. unfold REP_3_6 in *. lia.
Qed.

Lemma lmaxc_eq : lmaxc b = lmax.
Proof.
  unfold lmaxc. destruct MXL as [M1 M2]. rewrite NOFL in M1, M2. unfold ffreq in M1, M2. cbn [existsb] in M1, M2.
  apply (lmax_filter_zrange (fun c => 0 <? fL b c) 0 286 lmax); [lia | change (0 + Z.of_nat 286) with 286; lia | |].
  - apply Z.ltb_lt. rewrite fL_freq by lia. pose proof (op_fc _ OP TL lmax) as R. rewrite tree_fc_TL in R. lia.
  - intros i Hi Pi. change (0 + Z.of_nat 286) with 286 in Hi. apply Z.ltb_lt in Pi. rewrite fL_freq in Pi by lia. apply M2; lia.
Qed.

Lemma dmaxc_eq : dmaxc b = dmax.
Proof.
  unfold dmaxc. destruct MXD as [M1 M2].
  assert (FE : forall d, 0 <= d < 30 -> ((0 <? gD b d) || forcedD b d = true <-> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0)).
  { intros d Hd. unfold forcedD, ffreq. cbn [ob_forced b mkblock]. rewrite gD_freq by exact Hd. pose proof (op_fc _ OP TD d) as R. rewrite tree_fc_TD in R.
    destruct (existsb (Z.eqb d) FlD); [rewrite Bool.orb_true_r; split; [lia | reflexivity]|]. rewrite Bool.orb_false_r, Z.ltb_lt. lia. }
  apply (lmax_filter_zrange (fun d => (0 <? gD b d) || forcedD b d) 0 30 dmax); [lia | change (0 + Z.of_nat 30) with 30; lia | |].
  - apply (proj2 (FE dmax ltac:(lia))). exact M1.
  - intros i Hi Pi. change (0 + Z.of_nat 30) with 30 in Hi. apply M2; [lia|]. apply (proj1 (FE i ltac:(lia))). exact Pi.
Qed.

Lemma runs_L : forall f, lsum f (zruns LX 0 (Z.to_nat (lmax + 1))) = lsum f (runs1 b) + lsum f (runs2 b)
  /\ (forall r, In r (runs1 b) -> 1 <= r <= 257) /\ (forall r, In r (runs2 b) -> 1 <= r <= 29).
Proof.
  intros f. unfold runs1, runs2. rewrite lmaxc_eq. pose proof lmax_ge_256 as G256.
  assert (E256 : ob_lenL b 256 <> 0).
  { rewrite <- LX_lenL by lia. intros Z0. pose proof (tp_LDu _ TP 256 ltac:(unfold L_CODES; lia)) as U.
    destruct (op_hist _ OP) as (FHL & _). specialize (U ltac:(rewrite (FHL 256) by (unfold L_CODES; lia); rewrite Z.eqb_refl; cbn [zind];
      pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? 256)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))); unfold END_BLOCK; lia)).
    unfold LX in Z0. lia. }
  rewrite (zruns_ext LX (ob_lenL b) 0 (Z.to_nat (lmax + 1))) by (intros; apply LX_lenL; lia).
  replace (Z.to_nat (lmax + 1)) with (256 + S (Z.to_nat (lmax - 256)))%nat by lia.
  rewrite (zruns_split f (ob_lenL b) 0 256 (Z.to_nat (lmax - 256))) by exact E256.
  change 257%nat with (256 + S 0)%nat. rewrite (zruns_split f (ob_lenL b) 0 256 0) by exact E256. rewrite zruns_nil. cbn [lsum].
  change (0 + Z.of_nat 256 + 1) with 257.
  split; [lia|]. split.
  - intros r Hr. change (256 + S 0)%nat with 257%nat in Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
  - intros r Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
Qed.

Lemma runs_D : zruns DX 0 (Z.to_nat (dmax + 1)) = runs3 b /\ (forall r, In r (runs3 b) -> 1 <= r <= 30).
Proof.
  unfold runs3. rewrite dmaxc_eq. split.
  - apply zruns_ext. intros; apply DX_lenD; lia.
  - intros r Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
Qed.

Lemma gl_sc4 : ob_BC b 0 = vR1 b 1 + vR1 b 2 + vR1 b 3 + 2 * (vR2 b 1 + vR2 b 2 + vR2 b 3)
  /\ ob_BC b 17 = vRA b 1 + vRA b 2 + vRA b 3
  /\ ob_BC b 18 = vRB b 1 + vRB b 2 + vRB b 3 + vRLONG b.
Proof.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (_ & _ & _ & S4a & S4b & S4c & _).
  destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (_ & _ & _ & T4a & T4b & T4c & _).
  cbv zeta in S4a, S4b, S4c, T4a, T4b, T4c.
  unfold vR1, vR2, vRA, vRB, vRLONG, runs_of. cbn [Z.eqb Pos.eqb].
  destruct runs_D as [RD3 B3]. rewrite <- RD3 in *.
  pose proof (runs_L e0) as (L0 & B1 & B2). pose proof (proj1 (runs_L e17)) as L17. pose proof (proj1 (runs_L e18)) as L18.
  pose proof (proj1 (runs_L is1)) as Li1. pose proof (proj1 (runs_L is2)) as Li2. pose proof (proj1 (runs_L isa)) as Lia. pose proof (proj1 (runs_L isb)) as Lib. pose proof (proj1 (runs_L nlong)) as Lnl.
  assert (C0 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e0 l = lsum is1 l + 2 * lsum is2 l).
  { intros l Hl. rewrite <- lsum_scale, <- lsum_add. apply lsum_ext. intros r Hr. rewrite e0_is12 by exact (Hl r Hr). lia. }
  assert (C17 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e17 l = lsum isa l).
  { intros l Hl. apply lsum_ext. intros r Hr. apply e17_isa. exact (Hl r Hr). }
  assert (C18 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e18 l = lsum isb l + lsum nlong l).
  { intros l Hl. rewrite <- lsum_add. apply lsum_ext. intros r Hr. apply e18_isb. exact (Hl r Hr). }
  assert (H1 : forall r, In r (runs1 b) -> 1 <= r <= 276) by (intros r Hr; pose proof (B1 r Hr); lia).
  assert (H2 : forall r, In r (runs2 b) -> 1 <= r <= 276) by (intros r Hr; pose proof (B2 r Hr); lia).
  assert (H3 : forall r, In r (zruns DX 0 (Z.to_nat (dmax + 1))) -> 1 <= r <= 276) by (intros r Hr; pose proof (B3 r Hr); lia).
  rewrite (BC_split 0), (BC_split 17), (BC_split 18) by lia.
  unfold REPZ_3_10, REPZ_11_138 in *. rewrite S4a, S4b, S4c, T4a, T4b, T4c.
  rewrite L0, L17, L18. rewrite (C0 _ H1), (C0 _ H2), (C0 _ H3), (C17 _ H1), (C17 _ H2), (C17 _ H3), (C18 _ H1), (C18 _ H2), (C18 _ H3). lia.
Qed.


Hypothesis KZL : zt_kraft zL.
Hypothesis KZD : zt_kraft zD.
Hypothesis KZB : zt_kraft zB.

Lemma gl_TL : exists z, tree_facts z 286 15 (fL b) [] /\ zt_kraft z /\ (forall c, 0 <= c < 286 -> ob_lenL b c = zt_len z c).
Proof. exists zL. split; [exact TFL'|]. split; [exact KZL|]. intros c Hc. cbn [ob_lenL b mkblock]. symmetry. apply ZL1. Qed.

Lemma gl_TD : exists z, tree_facts z 30 15 (gD b) (ob_forced b) /\ zt_kraft z /\ (forall d, 0 <= d < 30 -> ob_lenD b d = zt_len z d).
Proof. exists zD. split; [exact TFD'|]. split; [exact KZD|]. intros d Hd. cbn [ob_lenD b mkblock]. symmetry. apply ZL2. Qed.

Lemma gl_TB : exists z, tree_facts z 19 7 (ob_BC b) (ob_bforced b) /\ zt_kraft z /\ (forall x, 0 <= x < 19 -> ob_BD b x = zt_len z x).
Proof. exists zB. split; [exact TFB|]. split; [exact KZB|]. intros x Hx. cbn [ob_BD b mkblock]. symmetry. apply ZL5. Qed.

Lemma lcode_used : forall j, 0 <= j < N -> 0 <= sym_lcode s j <= lmax /\ sym_lcode s j <> lmax + 1.
Proof.
  intros j Hj. pose proof (sym_codes s OP j Hj) as (A & _). unfold L_CODES in A. destruct MXL as [_ M].
  assert (sym_lcode s j <= lmax); [|lia]. apply M; [lia|]. rewrite NOFL. unfold ffreq. cbn [existsb].
  destruct (op_hist _ OP) as (FHL & _). rewrite (FHL (sym_lcode s j)) by (unfold L_CODES; lia).
  pose proof (zsum_ge_point (fun i => zind (sym_lcode s i =? sym_lcode s j)) 0 (Z.to_nat (nsym s)) j ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(subst N; lia)) as X.
  cbv beta in X. rewrite Z.eqb_refl in X. cbn [zind] in X. pose proof (zind_le1 (sym_lcode s j =? END_BLOCK)). lia.
Qed.

Lemma dcode_used : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= sym_dcode s j <= dmax /\ sym_dcode s j <> dmax + 1.
Proof.
  intros j Hj Hd. pose proof (sym_codes s OP j Hj) as (_ & _ & _ & _ & M). destruct (M Hd) as (_ & A & _). unfold D_CODES in A. destruct MXD as [_ MX].
  assert (sym_dcode s j <= dmax); [|lia]. apply MX; [lia|]. unfold ffreq. destruct (existsb _ _); [lia|].
  destruct (op_hist _ OP) as (_ & FHD & _). rewrite (FHD (sym_dcode s j)) by (unfold D_CODES; lia).
  pose proof (zsum_ge_point (fun i => zind (sym_isdist s i && (sym_dcode s i =? sym_dcode s j))) 0 (Z.to_nat (nsym s)) j ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(subst N; lia)) as X.
  cbv beta in X. rewrite Hd, Z.eqb_refl in X. cbn [zind andb] in X. lia.
Qed.

Lemma dcost_link : forall j, 0 <= j < N -> dcostS b (osym_of s j) = dcost (ov_LD s) (ov_DD s) s j.
Proof.
  intros j Hj. rewrite dcostS_osym by exact Hj. unfold dcost, ov_LD, ov_DD. cbn [ob_lenL ob_lenD b mkblock].
  pose proof (lcode_used j Hj) as [A B].
  rewrite <- (ZL1 (sym_lcode s j)), <- (LK1 (sym_lcode s j)) by exact B. unfold LX, Len. rewrite tree_dl_TL.
  destruct (sym_isdist s j) eqn:Hd; [|reflexivity].
  pose proof (dcode_used j Hj Hd) as [C D].
  rewrite <- (ZL2 (sym_dcode s j)), <- (LK2 (sym_dcode s j)) by exact D. unfold DX, Len. rewrite tree_dl_TD. reflexivity.
Qed.

Lemma gl_dyn : ob_Hc1 b + ssum (dcostS b) (ob_syms b) + ob_lenL b 256 <= ssum scostS (ob_syms b) + 6.
Proof.
  cbn [ob_Hc1 ob_syms b mkblock].
  rewrite !ssum_osyms by lia. fold N.
  rewrite (zsum_ext (fun j => dcostS b (osym_of s j)) (dcost (ov_LD s) (ov_DD s) s)) by (intros; apply dcost_link; lia).
  rewrite (zsum_ext (fun j => scostS (osym_of s j)) (scost s)) by (intros; apply scostS_osym; lia).
  assert (E256 : ob_lenL b 256 = arr_get (ov_LD s) END_BLOCK).
  { cbn [ob_lenL b mkblock]. rewrite <- ZL1, <- LK1 by (pose proof lmax_ge_256; lia). unfold LX, Len, ov_LD, END_BLOCK. rewrite tree_dl_TL. reflexivity. }
  rewrite E256.
  pose proof (tp_opt_ge _ TP) as G. pose proof (data_dyn s OP (ov_LD s) (ov_DD s)) as Dd. fold N in Dd.
  pose proof (tp_stat _ TP) as ST. pose proof (static_by_syms s OP) as SB. fold N in SB.
  pose proof (branch1_lt (ov_X6 s) (fb_buf s) (fb_len s) (tp_opt _ TP) (tp_stat_range _ TP) HB) as LT.
  unfold ov_LD, ov_DD in *.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c))
                    (fun c => arr_get (ds_dyn_ltree_fc s) c * (arr_get (ds_dyn_ltree_dl (ov_X6 s)) c + xbits TL c))) in G
    by (intros; rewrite Len_eq, tree_dl_TL; reflexivity).
  rewrite (zsum_ext (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d))
                    (fun d => arr_get (ds_dyn_dtree_fc s) d * (arr_get (ds_dyn_dtree_dl (ov_X6 s)) d + xbits TD d))) in G
    by (intros; rewrite Len_eq, tree_dl_TD; reflexivity).
  rewrite (zsum_ext (fun x => arr_get (ov_BC s) x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x))
                    (fun x => arr_get (ov_BC s) x * (arr_get (ov_BD s) x + arr_get extra_blbits_a x))) in G
    by (intros; unfold ov_BD; rewrite Len_eq, tree_dl_TB; reflexivity).
  unfold ov_hdr.
  match goal with |- context [zsum ?f 0 19] => set (A := zsum f 0 19) in * end.
  match type of Dd with context [zsum ?f 0 (Z.to_nat L_CODES)] => set (B := zsum f 0 (Z.to_nat L_CODES)) in * end.
  match type of Dd with context [zsum ?f 0 (Z.to_nat D_CODES)] => set (C := zsum f 0 (Z.to_nat D_CODES)) in * end.
  match type of SB with ?x + ?y = _ => set (SBL := x) in *; set (SBD := y) in * end.
  match goal with |- context [zsum (dcost ?u ?v s) 0 (Z.to_nat N)] => set (Dsum := zsum (dcost u v s) 0 (Z.to_nat N)) in * end.
  clearbody A B C SBL SBD Dsum. lia.
Qed.

Lemma gl_EX : vEX b = zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N).
Proof.
  unfold vEX. cbn [ob_syms b mkblock]. rewrite ssum_osyms by lia. fold N. apply zsum_ext. intros j Hj. unfold exS. rewrite dcost_link by lia. reflexivity.
Qed.

Lemma gl_ok : oblock_ok b (ds_lit_bufsize s).
Proof.
  pose proof gl_sc23 as [S2 S3]. pose proof gl_sc4 as (S4a & S4b & S4c).
  constructor.
  - cbn [ob_syms b mkblock]. eapply Forall_impl; [| apply Forall_osyms]. intros [c|lc dc]; cbn; lia.
  - rewrite (NSYM_osyms b) by reflexivity. fold N. lia.
  - pose proof (op_lbs _ OP). lia.
  - exact gl_TL.
  - exact gl_TD.
  - exact gl_TB.
  - exact gl_WB.
  - exact gl_blc.
  - exact gl_Hc1.
  - exact gl_sc1.
  - exact S2.
  - exact S3.
  - exact S4a.
  - exact S4b.
  - exact S4c.
  - exact gl_dyn.
Qed.

End WithTrees.

Theorem block_ok : exists b, oblock_ok b (ds_lit_bufsize s) /\ ob_syms b = osyms s /\ ob_Hc1 b = ov_hdr s - 3
  /\ vEX b = zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N).
Proof.
  destruct (ot_facts s OP) as (zL & zD & zB & FlL & FlD & FlB & TF1 & TF2 & TF5 & K1 & K2 & K5 & ZL1 & ZL2 & ZL5 & LK1 & LK2 & LK5 & G1 & G2 & MX1 & MX2 & NOF).
  specialize (NOF HN).
  exists (mkblock FlD FlB). split; [| split; [reflexivity | split; [reflexivity|]]].
  - apply (gl_ok zL zD zB FlL FlD FlB); assumption.
  - apply (gl_EX zL zD FlL FlD); assumption.
Qed.

Corollary overlay_from_bound :
  (forall b, oblock_ok b (ds_lit_bufsize s) -> ob_Hc1 b + vEX b <= 8 * ds_lit_bufsize s - 10) ->
  forall k, 0 <= k < N -> ov_wpos s k <= ov_rpos s k.
Proof.
  intros BOUND. destruct block_ok as (b & OK & _ & H1 & H2).
  apply prefix_from_core. rewrite <- H1, <- H2. apply BOUND. exact OK.
Qed.

End Block.

Theorem OVERLAY_CORE_from_bound :
  (forall s b, overlay_pre s -> oblock_ok b (ds_lit_bufsize s) -> ob_Hc1 b + vEX b <= 8 * ds_lit_bufsize s - 10) ->
  OVERLAY_CORE.
Proof.
  intros BOUND s OP HB k Hk.
  apply (overlay_from_bound s OP ltac:(lia) HB); [| exact Hk]. intros b OK. apply (BOUND s b OP OK).
Qed.

Lemma lbs_cases : forall s, overlay_pre s -> In (ds_lit_bufsize s) [128; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768].
Proof.
  intros s OP. pose proof (op_lbs _ OP) as R. destruct (op_lbs2 _ OP) as [k Hk]. rewrite Hk in R |- *.
  assert (K : 7 <= k <= 15).
  { destruct (Z_lt_le_dec k 7) as [A|A].
    - exfalso. destruct (Z_lt_le_dec k 0) as [B|B]; [rewrite Z.pow_neg_r in R by lia; lia|].
      pose proof (Z.pow_le_mono_r 2 k 6 ltac:(lia) ltac:(lia)). change (2 ^ 6) with 64 in H. lia.
    - destruct (Z_lt_le_dec 15 k) as [B|B]; [|lia]. exfalso.
      pose proof (Z.pow_le_mono_r 2 16 k ltac:(lia) ltac:(lia)). change (2 ^ 16) with 65536 in H. lia. }
  assert (E : k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) by lia.
  destruct E as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; cbn; tauto.
Qed.

Theorem OVERLAY_CORE_of_bound :
  (forall b lbs, oblock_ok b lbs -> In lbs [128; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768] -> ob_Hc1 b + vEX b <= 8 * lbs - 10) ->
  OVERLAY_CORE.
Proof.
  intros BOUND. apply OVERLAY_CORE_from_bound. intros s b OP OK. apply BOUND; [exact OK | exact (lbs_cases s OP)].
Qed.
End OverlayGlue.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayBlock OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayFacts OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayCoreL.OverlayGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem overlay_core_proof : OVERLAY_CORE.
Proof.
  apply OVERLAY_CORE_from_bound. intros s b OP OK.
  pose proof (op_lbs _ OP) as R.
  exact (overlay_bound_large b (ds_lit_bufsize s) OK ltac:(lia)).
Qed.
