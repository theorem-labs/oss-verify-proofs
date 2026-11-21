(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRows.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayFacts.

Module OverlayHuff4.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fib_nat_step n : fib_nat (S (S n)) = fib_nat (S n) + fib_nat n.
Proof. reflexivity. Qed.
Lemma fib_nat_nonneg n : 0 <= fib_nat n.
Proof. induction n as [n IH] using lt_wf_ind. destruct n as [|[|n]]; [cbn; lia|cbn; lia|]. rewrite fib_nat_step. pose proof (IH n ltac:(lia)). pose proof (IH (S n) ltac:(lia)). lia. Qed.
Lemma fib_step d : 0 <= d -> fib (d + 2) = fib (d + 1) + fib d.
Proof. intros. unfold fib. replace (Z.to_nat (d + 2)) with (S (S (Z.to_nat d))) by lia. replace (Z.to_nat (d + 1)) with (S (Z.to_nat d)) by lia. apply fib_nat_step. Qed.
Lemma fib_nonneg d : 0 <= fib d. Proof. unfold fib. apply fib_nat_nonneg. Qed.
Lemma fib_0 : fib 0 = 0. Proof. reflexivity. Qed.
Lemma fib_1 : fib 1 = 1. Proof. reflexivity. Qed.
Lemma fib_2 : fib 2 = 1. Proof. reflexivity. Qed.

Section GTree.
Variable g : gtree.
Hypothesis G : gtree_ok g.

Notation lo := (g_lo g).
Notation hi := (g_hi g).
Notation par := (g_par g).
Notation leaf := (g_leaf g).
Notation wt := (g_wt g).
Notation ext := (g_ext g).
Notation depth := (g_depth g).
Notation leaves := (leaves g).
Let allpos_in := allpos_in g G. Let nonroot_in := nonroot_in g G. Let leaves_in := leaves_in g G.
Let depth_step := depth_step g G. Let wt_nonneg := wt_nonneg g G.
Let depth_nonneg := depth_nonneg g G. Let depth_root := depth_root g G. Let lohi := lohi g G.
Let root_internal := root_internal g G. Let ext_mono := ext_mono g G. Let leaves_nodup := leaves_nodup g.

Lemma leaf_below x : lo <= x <= hi -> exists l, lo <= l <= hi /\ leaf l = true /\ depth x <= depth l.
Proof.
  intros Hx. remember (Z.to_nat (hi - x)) as n eqn:E. revert x Hx E.
  induction n as [n IH] using lt_wf_ind; intros x Hx E.
  destruct (leaf x) eqn:L; [exists x; repeat split; auto; lia|].
  destruct (go_two g G x Hx L) as (a & b & NE & Ha & Hb & Pa & Pb & _).
  pose proof (go_par_lt g G a Ha). pose proof (depth_step a Ha). rewrite Pa in H0.
  destruct (IH (Z.to_nat (hi - a)) ltac:(lia) a ltac:(lia) eq_refl) as (l & Hl & Ll & Dl).
  exists l. repeat split; auto; lia.
Qed.

Definition Dmax : Z := lmax (fun i => depth i) leaves.

Lemma Dmax_ge i : lo <= i <= hi -> leaf i = true -> depth i <= Dmax.
Proof. intros. unfold Dmax. apply (lmax_ge (fun i => depth i)). apply leaves_in. auto. Qed.
Lemma Dmax_nonneg : 0 <= Dmax.
Proof. unfold Dmax. apply lmax_nonneg. intros x Hx. apply leaves_in in Hx. apply depth_nonneg. tauto. Qed.

Lemma depth_code_ok : code_ok Dmax (fun i => depth i) leaves.
Proof.
  split.
  - intros x Hx. apply leaves_in in Hx. split; [apply depth_nonneg; tauto|apply Dmax_ge; tauto].
  - unfold ksum. rewrite (kraft_eq g G Dmax); [lia|]. intros; apply Dmax_ge; auto.
Qed.

Theorem mono a b : lo <= a <= hi -> leaf a = true -> lo <= b <= hi -> leaf b = true ->
  wt a < wt b -> depth b <= depth a.
Proof.
  intros Ha La Hb Lb W. destruct (Z_le_gt_dec (depth b) (depth a)) as [|GT]; [assumption|exfalso].
  assert (NE : a <> b) by (intros ->; lia).
  assert (Ia : In a leaves) by (apply leaves_in; auto). assert (Ib : In b leaves) by (apply leaves_in; auto).
  pose proof depth_code_ok as [R KS].
  set (sg := upd (upd (fun i => depth i) a (depth b)) b (depth a)).
  pose proof (optimal g G Dmax Dmax_nonneg sg) as OPT.
  assert (OK : code_ok Dmax sg leaves).
  { split.
    - intros x Hx. unfold sg, upd. destruct (x =? b); [apply R; auto|]. destruct (x =? a); [apply R; auto|]. apply R; auto.
    - unfold sg. rewrite ksum_upd; [|apply leaves_nodup|exact Ib]. rewrite ksum_upd; [|apply leaves_nodup|exact Ia].
      unfold upd. replace (b =? a) with false by (symmetry; apply Z.eqb_neq; auto). lia. }
  specialize (OPT OK). unfold sg in OPT.
  rewrite csum_upd in OPT; [|apply leaves_nodup|exact Ib]. rewrite csum_upd in OPT; [|apply leaves_nodup|exact Ia].
  unfold upd in OPT. replace (b =? a) with false in OPT by (symmetry; apply Z.eqb_neq; auto).
  unfold csum in OPT. nia.
Qed.

Theorem depth_spread m c : lo <= m <= hi -> leaf m = true ->
  (forall x, lo <= x <= hi -> leaf x = true -> wt m <= wt x) ->
  lo <= c <= hi -> leaf c = true -> depth c <= depth m + 1.
Proof.
  intros Hm Lm MIN Hc Lc.
  destruct (Z_le_gt_dec (depth c) (depth m + 1)) as [|GT]; [assumption|exfalso].
  assert (NN : leaves <> []) by (intros E; assert (I : In c leaves) by (apply leaves_in; auto); rewrite E in I; exact I).
  destruct (lmax_in (fun i => depth i) leaves NN ltac:(intros x Hx; apply leaves_in in Hx; apply depth_nonneg; tauto)) as (cs & Ics & Dcs).
  apply leaves_in in Ics. destruct Ics as [Hcs Lcs]. fold Dmax in Dcs.
  pose proof (Dmax_ge c Hc Lc). pose proof (Dmax_ge m Hm Lm).
  assert (Hcs' : lo < cs <= hi) by (destruct (Z.eq_dec cs lo) as [->|]; [rewrite root_internal in Lcs; discriminate|lia]).
  destruct (sibling g G cs Hcs') as (ss & Hss & NEs & Pss & ONLY & _ & Wp).
  assert (Dss : depth ss = Dmax) by (rewrite depth_step, Pss, <- depth_step, Dcs by auto; reflexivity).
  assert (Lss : leaf ss = true).
  { destruct (leaf ss) eqn:L; [reflexivity|exfalso].
    destruct (go_two g G ss ltac:(unfold g_pos; lia) L) as (u & v & _ & Hu & _ & Pu & _ & _).
    pose proof (depth_step u Hu). rewrite Pu, Dss in H1.
    pose proof (go_par_lt g G u Hu).
    destruct (leaf_below u ltac:(lia)) as (l & Hl & Ll & Dl). pose proof (Dmax_ge l Hl Ll). lia. }
  assert (NEm1 : m <> cs) by (intros ->; lia). assert (NEm2 : m <> ss) by (intros ->; lia).
  assert (Im : In m leaves) by (apply leaves_in; auto).
  assert (Ics : In cs leaves) by (apply leaves_in; auto). assert (Iss : In ss leaves) by (apply leaves_in; split; [lia|exact Lss]).
  pose proof depth_code_ok as [R KS].
  set (sg := upd (upd (upd (fun i => depth i) cs (depth m + 1)) m (depth m + 1)) ss (Dmax - 1)).
  pose proof (optimal g G Dmax Dmax_nonneg sg) as OPT.
  pose proof (depth_nonneg m Hm) as Dm0.
  assert (OK : code_ok Dmax sg leaves).
  { split.
    - intros x Hx. unfold sg, upd. destruct (x =? ss); [lia|]. destruct (x =? m); [lia|]. destruct (x =? cs); [lia|]. apply R; auto.
    - unfold sg. rewrite ksum_upd; [|apply leaves_nodup|exact Iss]. rewrite ksum_upd; [|apply leaves_nodup|exact Im]. rewrite ksum_upd; [|apply leaves_nodup|exact Ics].
      unfold upd.
      replace (m =? cs) with false by (symmetry; apply Z.eqb_neq; auto).
      replace (ss =? m) with false by (symmetry; apply Z.eqb_neq; auto).
      replace (ss =? cs) with false by (symmetry; apply Z.eqb_neq; auto).
      rewrite Dcs, Dss.
      replace (Dmax - (Dmax - 1)) with (Z.succ (Dmax - Dmax)) by lia. rewrite Z.pow_succ_r by lia.
      replace (Dmax - depth m) with (Z.succ (Dmax - (depth m + 1))) by lia. rewrite Z.pow_succ_r by lia.
      lia. }
  specialize (OPT OK). unfold sg in OPT.
  rewrite csum_upd in OPT; [|apply leaves_nodup|exact Iss]. rewrite csum_upd in OPT; [|apply leaves_nodup|exact Im]. rewrite csum_upd in OPT; [|apply leaves_nodup|exact Ics].
  unfold upd in OPT.
  replace (m =? cs) with false in OPT by (symmetry; apply Z.eqb_neq; auto).
  replace (ss =? m) with false in OPT by (symmetry; apply Z.eqb_neq; auto).
  replace (ss =? cs) with false in OPT by (symmetry; apply Z.eqb_neq; auto).
  rewrite Dcs, Dss in OPT. unfold csum in OPT.
  pose proof (MIN cs Hcs Lcs). pose proof (go_wt_leaf g G ss ltac:(unfold g_pos; lia) Lss). pose proof (wt_nonneg m Hm).
  nia.
Qed.

Lemma sib_ge_children a s c : lo < a <= hi -> lo < s <= hi -> s <> a -> par s = par a ->
  lo < c <= hi -> par c = a -> wt c <= wt s.
Proof.
  intros Ha Hs NE Ps Hc Pc.
  assert (c <> s) by (intros ->; pose proof (go_par_lt g G a Ha); rewrite Pc in Ps; lia).
  pose proof (go_ext_par g G c Hc ltac:(rewrite Pc; lia)) as E1. rewrite Pc in E1.
  assert (ext c <> ext s) by (intros E; apply H; apply (go_ext_inj g G); auto).
  destruct (go_ext_sib g G a s Ha Hs ltac:(auto) ltac:(auto)) as [E|E]; apply ext_mono; auto; lia.
Qed.

Lemma fib_inv x s : lo < x <= hi -> lo < s <= hi -> s <> x -> par s = par x ->
  fib (depth x + 1) * wt x + fib (depth x) * wt s <= g_W g.
Proof.
  intros Hx. remember (Z.to_nat (x - lo)) as n eqn:E. revert x Hx E s.
  induction n as [n IH] using lt_wf_ind; intros x Hx E s Hs NE Ps.
  pose proof (go_par_lt g G x Hx) as P. rewrite (depth_step x Hx).
  destruct (sibling g G x Hx) as (s' & Hs' & NEs' & Ps' & ONLY & _ & Wp).
  assert (s' = s) by (destruct (ONLY s Hs Ps) as [->| ->]; [congruence|reflexivity]). subst s'.
  destruct (Z.eq_dec (par x) lo) as [R|NR].
  -
    rewrite R in Wp. rewrite R. rewrite depth_root. replace (1 + 0 + 1) with 2 by lia. replace (1 + 0) with 1 by lia.
    rewrite fib_1, fib_2. unfold g_W. lia.
  -
    destruct (sibling g G (par x) ltac:(lia)) as (t & Ht & NEt & Pt & _ & _ & _).
    pose proof (IH (Z.to_nat (par x - lo)) ltac:(lia) (par x) ltac:(lia) eq_refl t Ht NEt Pt) as IHp.
    pose proof (sib_ge_children (par x) t x ltac:(lia) Ht NEt Pt Hx eq_refl) as TX.
    pose proof (depth_nonneg (par x) ltac:(lia)) as D0.
    rewrite Wp in IHp.
    replace (1 + depth (par x) + 1) with (depth (par x) + 2) by lia. replace (1 + depth (par x)) with (depth (par x) + 1) by lia.
    rewrite fib_step by lia.
    pose proof (fib_nonneg (depth (par x))). pose proof (fib_nonneg (depth (par x) + 1)).
    pose proof (wt_nonneg x ltac:(lia)). pose proof (wt_nonneg s ltac:(lia)). nia.
Qed.

Theorem fib_bound x : lo <= x <= hi -> fib (depth x + 1) * wt x <= g_W g.
Proof.
  intros Hx. destruct (Z.eq_dec x lo) as [->|NE].
  - rewrite depth_root. replace (0 + 1) with 1 by lia. rewrite fib_1. unfold g_W. lia.
  - destruct (sibling g G x ltac:(lia)) as (s & Hs & NEs & Ps & _).
    pose proof (fib_inv x s ltac:(lia) Hs NEs Ps). pose proof (fib_nonneg (depth x)). pose proof (wt_nonneg s ltac:(lia)). nia.
Qed.

End GTree.
End OverlayHuff4.

Module OverlayTrees.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayHuff4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma fib_mono_nat : forall n m, (n <= m)%nat -> fib_nat n <= fib_nat m.
Proof.
  assert (STEP : forall n, fib_nat n <= fib_nat (S n)).
  { induction n as [n IH] using Wf_nat.lt_wf_ind. destruct n as [|[|n]]; [cbn; lia|cbn; lia|].
    rewrite (fib_nat_step (S n)). pose proof (fib_nat_nonneg (S n)). pose proof (fib_nat_nonneg (S (S n))). lia. }
  intros n m H. induction H; [lia|]. pose proof (STEP m). lia.
Qed.
Lemma fib_mono a c : 0 <= a <= c -> fib a <= fib c.
Proof. intros. unfold fib. apply fib_mono_nat. lia. Qed.
Lemma fib_pos d : 1 <= d -> 1 <= fib d.
Proof. intros. change 1 with (fib 1) at 1. pose proof (fib_mono 1 d ltac:(lia)). exact H0. Qed.

Lemma lsum_map (h : Z -> Z) (f : Z -> Z) (l : list Z) : lsum h (map f l) = lsum (fun x => h (f x)) l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma lsum_support (h : Z -> Z) (S T : list Z) :
  NoDup S -> NoDup T -> (forall x, In x T -> In x S) ->
  lsum (fun x => if existsb (Z.eqb x) T then h x else 0) S = lsum h T.
Proof.
  intros NS. induction T as [|y T IH]; intros NT SUB.
  - cbn. etransitivity; [apply (lsum_ext _ (fun _ => 0)); intros; reflexivity | apply lsum_zero].
  - inversion NT; subst.
    rewrite (lsum_ext _ (fun x => (if x =? y then h y else 0) + (if existsb (Z.eqb x) T then h x else 0))).
    2:{ intros x _. cbn. destruct (Z.eqb_spec x y); cbn; [|reflexivity]. subst.
        replace (existsb (Z.eqb y) T) with false; [lia|]. symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists.
        intros (u & Iu & Eu). apply Z.eqb_eq in Eu. subst. tauto. }
    rewrite lsum_add, IH; [|assumption|intros; apply SUB; right; assumption].
    destruct (lsum_in_split S y (SUB y (or_introl eq_refl)) NS) as (l1 & l2 & E & N1 & N2).
    rewrite E, lsum_app. cbn. rewrite Z.eqb_refl.
    rewrite (lsum_ext _ (fun _ => 0) l1) by (intros x Hx; destruct (Z.eqb_spec x y); [subst; tauto|reflexivity]).
    rewrite (lsum_ext _ (fun _ => 0) l2) by (intros x Hx; destruct (Z.eqb_spec x y); [subst; tauto|reflexivity]).
    rewrite !lsum_zero. lia.
Qed.

Lemma existsb_map_code (code : Z -> Z) (L : list Z) (c : Z) :
  existsb (Z.eqb c) (map code L) = true <-> exists i, In i L /\ code i = c.
Proof.
  rewrite existsb_exists. split.
  - intros (x & Ix & Ex). apply Z.eqb_eq in Ex. subst. apply in_map_iff in Ix. destruct Ix as (i & Ei & Ii). exists i. auto.
  - intros (i & Ii & Ei). exists c. split; [|apply Z.eqb_refl]. apply in_map_iff. exists i. auto.
Qed.


Definition tpos (z : ztree) (c : Z) : Z :=
  match filter (fun i => g_leaf (zt_g z) i && (g_code (zt_g z) i =? c)) (allpos (zt_g z)) with
  | i :: _ => i
  | [] => g_lo (zt_g z)
  end.
Definition tdepth (z : ztree) (c : Z) : Z := g_depth (zt_g z) (tpos z c).

Section TF.
Variable z : ztree.
Variable E : Z.
Variable ML : Z.
Variable F : Z -> Z.
Variable Fl : list Z.
Hypothesis TF : tree_facts z E ML F Fl.

Let g := zt_g z.
Let W := ffreq F Fl.
Let n := Z.to_nat E.

Lemma G : gtree_ok g. Proof. exact (zo_g z (tf_ok z E ML F Fl TF)). Qed.
Let ZOK : ztree_ok z := tf_ok z E ML F Fl TF.

Lemma E_nonneg : 0 <= E.
Proof. destruct (tf_two z E ML F Fl TF) as (a & b & Ha & _). lia. Qed.
Lemma n_E : Z.of_nat n = E. Proof. unfold n. pose proof E_nonneg. lia. Qed.

Lemma leaf_W i : g_pos g i -> g_leaf g i = true -> 0 <= g_code g i < E /\ g_wt g i = W (g_code g i).
Proof. intros Hi Li. exact (tf_wt z E ML F Fl TF i Hi Li). Qed.

Lemma tpos_spec c : 0 <= c < E -> W c <> 0 ->
  g_pos g (tpos z c) /\ g_leaf g (tpos z c) = true /\ g_code g (tpos z c) = c.
Proof.
  intros Hc Wc. apply (proj2 (tf_used z E ML F Fl TF c Hc)) in Wc. destruct Wc as (i & Pi & Li & Ci).
  unfold tpos. fold g. fold g in Pi, Li, Ci.
  destruct (filter (fun j => g_leaf g j && (g_code g j =? c)) (allpos g)) as [|j r] eqn:EF.
  - exfalso. assert (In i (filter (fun j => g_leaf g j && (g_code g j =? c)) (allpos g))).
    { apply filter_In. split; [apply (allpos_in g G); exact Pi|]. rewrite Li, Ci, Z.eqb_refl. reflexivity. }
    rewrite EF in H. exact H.
  - assert (In j (filter (fun j => g_leaf g j && (g_code g j =? c)) (allpos g))) by (rewrite EF; left; reflexivity).
    apply filter_In in H. destruct H as [Aj Bj]. apply (allpos_in g G) in Aj. apply Bool.andb_true_iff in Bj. destruct Bj as [Lj Cj].
    apply Z.eqb_eq in Cj. auto.
Qed.

Lemma tpos_of_leaf i : g_pos g i -> g_leaf g i = true -> tpos z (g_code g i) = i.
Proof.
  intros Hi Li. destruct (leaf_W i Hi Li) as [R Wi].
  assert (Wc : W (g_code g i) <> 0) by (pose proof (go_wt_leaf g G i Hi Li); lia).
  destruct (tpos_spec (g_code g i) R Wc) as (P & L & C).
  exact (go_code_inj g G _ _ P Hi L Li C).
Qed.

Lemma W_cases c : 0 <= c < E -> W c = 0 \/ (1 <= W c /\ g_pos g (tpos z c) /\ g_leaf g (tpos z c) = true /\ g_code g (tpos z c) = c).
Proof.
  intros Hc. destruct (Z.eq_dec (W c) 0) as [Z0|NZ]; [left; exact Z0|right].
  destruct (tpos_spec c Hc NZ) as (P & L & C). destruct (leaf_W _ P L) as [_ Wi]. rewrite C in Wi.
  pose proof (go_wt_leaf g G _ P L). split; [lia|]. split; [exact P|]. split; [exact L|exact C].
Qed.

Lemma W_nonneg c : 0 <= c < E -> 0 <= W c.
Proof. intros Hc. destruct (W_cases c Hc); lia. Qed.

Lemma W_wt c : 0 <= c < E -> W c <> 0 -> g_wt g (tpos z c) = W c.
Proof. intros Hc Wc. destruct (W_cases c Hc) as [|(_ & P & L & C)]; [lia|]. destruct (leaf_W _ P L) as [_ X]. rewrite C in X. exact X. Qed.

Theorem reindex (h : Z -> Z) :
  zsum (fun c => if W c =? 0 then 0 else h c) 0 n = lsum (fun i => h (g_code g i)) (leaves g).
Proof.
  rewrite <- lsum_zsum. rewrite <- (lsum_map h).
  set (T := map (g_code g) (leaves g)).
  assert (NT : NoDup T).
  { unfold T. apply NoDup_map_NoDup_ForallPairs; [|apply (leaves_nodup g)].
    intros i j Ii Ij Eij. apply (leaves_in g G) in Ii. apply (leaves_in g G) in Ij. destruct Ii as [Pi Li], Ij as [Pj Lj].
    exact (go_code_inj g G i j Pi Pj Li Lj Eij). }
  rewrite <- (lsum_support h (rangeZ 0 n) T (rangeZ_nodup 0 n) NT).
  2:{ intros c Ic. unfold T in Ic. apply in_map_iff in Ic. destruct Ic as (i & <- & Ii). apply (leaves_in g G) in Ii. destruct Ii as [Pi Li].
      apply rangeZ_in. destruct (leaf_W i Pi Li) as [R _]. rewrite n_E. lia. }
  apply lsum_ext. intros c Ic. apply rangeZ_in in Ic. rewrite n_E in Ic.
  destruct (W_cases c ltac:(lia)) as [Z0|(W1 & P & L & C)].
  - rewrite Z0, Z.eqb_refl. destruct (existsb (Z.eqb c) T) eqn:X; [|reflexivity]. exfalso.
    apply (existsb_map_code (g_code g) (leaves g) c) in X. destruct X as (i & Ii & Ci). apply (leaves_in g G) in Ii. destruct Ii as [Pi Li].
    destruct (leaf_W i Pi Li) as [_ Wi]. pose proof (go_wt_leaf g G i Pi Li). rewrite Ci in Wi. lia.
  - replace (W c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (existsb (Z.eqb c) T) with true; [reflexivity|]. symmetry. apply (existsb_map_code (g_code g) (leaves g) c).
    exists (tpos z c). split; [|exact C]. apply (leaves_in g G). auto.
Qed.

Theorem sumW : zsum W 0 n = g_W g.
Proof.
  rewrite (W_leaves g G). rewrite (zsum_ext W (fun c => if W c =? 0 then 0 else W c)).
  2:{ intros c _. destruct (Z.eqb_spec (W c) 0); lia. }
  rewrite (reindex W). apply lsum_ext. intros i Ii. apply (leaves_in g G) in Ii. destruct Ii as [Pi Li].
  destruct (leaf_W i Pi Li) as [_ X]. rewrite X. reflexivity.
Qed.

Lemma gW_ge c : 0 <= c < E -> W c <= g_W g.
Proof.
  intros Hc. rewrite <- sumW. apply (zsum_ge_point W 0 n c); [|rewrite n_E; lia]. intros i Hi. apply W_nonneg. rewrite n_E in Hi. lia.
Qed.

Theorem tlen_used c : 0 <= c < E -> W c <> 0 -> 1 <= zt_len z c <= ML.
Proof.
  intros Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). rewrite <- (tf_ML z E ML F Fl TF).
  apply (zo_len_used z ZOK c (tpos z c)). unfold zt_is_leaf_of. auto.
Qed.

Theorem tlen_unused c : 0 <= c < E -> W c = 0 -> zt_len z c = 0.
Proof.
  intros Hc Wc. apply (zo_len_unused z ZOK c); [rewrite (tf_E z E ML F Fl TF); exact Hc|].
  intros U. apply (proj1 (tf_used z E ML F Fl TF c Hc)) in U. exact (U Wc).
Qed.

Theorem tdepth_pos c : 0 <= c < E -> W c <> 0 -> 1 <= tdepth z c.
Proof.
  intros Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). unfold tdepth. fold g.
  apply (depth_pos g G). unfold g_pos in P. destruct (Z.eq_dec (tpos z c) (g_lo g)) as [EQ|]; [|lia].
  exfalso. pose proof (root_internal g G). rewrite <- EQ in H. fold g in L. congruence.
Qed.

Theorem tfib c : 0 <= c < E -> W c <> 0 -> W c * fib (tdepth z c + 1) <= g_W g.
Proof.
  intros Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). rewrite <- (W_wt c Hc Wc). unfold tdepth. fold g.
  pose proof (fib_bound g G (tpos z c) P). lia.
Qed.

Lemma depth_le_of_W D : g_W g < fib (D + 2) -> 0 <= D -> forall i, g_pos g i -> g_leaf g i = true -> g_depth g i <= D.
Proof.
  intros HW HD i Pi Li. pose proof (fib_bound g G i Pi) as FB. pose proof (go_wt_leaf g G i Pi Li).
  destruct (Z_le_gt_dec (g_depth g i) D); [assumption|exfalso].
  pose proof (fib_mono (D + 2) (g_depth g i + 1) ltac:(lia)). pose proof (fib_nonneg (g_depth g i + 1)). nia.
Qed.

Theorem tnoovf : g_W g < fib (ML + 2) -> forall c, 0 <= c < E -> W c <> 0 -> zt_len z c = tdepth z c.
Proof.
  intros HW c Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). unfold tdepth. fold g.
  pose proof (zo_ML z ZOK) as M1. rewrite (tf_ML z E ML F Fl TF) in M1.
  apply (zo_len_noovf z ZOK).
  - intros i Pi Li. rewrite (tf_ML z E ML F Fl TF). apply (depth_le_of_W ML HW ltac:(lia) i Pi Li).
  - unfold zt_is_leaf_of. auto.
Qed.

Theorem tdepth_le D : g_W g < fib (D + 2) -> 0 <= D -> forall c, 0 <= c < E -> W c <> 0 -> tdepth z c <= D.
Proof.
  intros HW HD c Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). unfold tdepth. apply (depth_le_of_W D HW HD _ P L).
Qed.

Theorem tkraft : g_W g < fib (ML + 2) ->
  zsum (fun c => if W c =? 0 then 0 else 2 ^ (ML - zt_len z c)) 0 n = 2 ^ ML.
Proof.
  intros HW. pose proof (zo_ML z ZOK) as M1. rewrite (tf_ML z E ML F Fl TF) in M1.
  rewrite (reindex (fun c => 2 ^ (ML - zt_len z c))).
  rewrite <- (kraft_eq g G ML) by (intros i Pi Li; apply (depth_le_of_W ML HW ltac:(lia) i Pi Li)).
  apply lsum_ext. intros i Ii. apply (leaves_in g G) in Ii. destruct Ii as [Pi Li]. destruct (leaf_W i Pi Li) as [R Wi].
  pose proof (go_wt_leaf g G i Pi Li).
  rewrite (tnoovf HW (g_code g i) R ltac:(lia)). unfold tdepth. fold g. rewrite (tpos_of_leaf i Pi Li). reflexivity.
Qed.


Lemma wt_pos i : g_pos g i -> 1 <= g_wt g i.
Proof.
  intros Hi. remember (Z.to_nat (g_hi g - i)) as k eqn:Ek. revert i Hi Ek.
  induction k as [k IH] using Wf_nat.lt_wf_ind; intros i Hi Ek.
  destruct (g_leaf g i) eqn:Li; [exact (go_wt_leaf g G i Hi Li)|].
  destruct (go_two g G i Hi Li) as (a & b & NE & Ha & Hb & Pa & Pb & _).
  pose proof (go_par_lt g G a Ha). pose proof (go_par_lt g G b Hb). rewrite Pa in *. rewrite Pb in *.
  rewrite (go_wt_sum g G i a b Hi Li Ha Hb NE Pa Pb).
  pose proof (IH (Z.to_nat (g_hi g - a)) ltac:(lia) a ltac:(unfold g_pos; lia) eq_refl).
  pose proof (IH (Z.to_nat (g_hi g - b)) ltac:(lia) b ltac:(unfold g_pos; lia) eq_refl). lia.
Qed.

Lemma depth_fib2 i : g_pos g i -> g_leaf g i = true -> fib (g_depth g i + 2) <= g_W g.
Proof.
  intros Hi Li. pose proof (root_internal g G) as RI.
  assert (NR : g_lo g < i <= g_hi g) by (unfold g_pos in Hi; destruct (Z.eq_dec i (g_lo g)) as [->|]; [congruence|lia]).
  destruct (sibling g G i NR) as (s & Hs & NEs & Ps & _).
  pose proof (fib_inv g G i s NR Hs NEs Ps) as FI.
  pose proof (wt_pos i Hi). pose proof (wt_pos s ltac:(unfold g_pos; lia)).
  pose proof (depth_nonneg g G i Hi). rewrite fib_step by lia.
  pose proof (fib_nonneg (g_depth g i + 1)). pose proof (fib_nonneg (g_depth g i)). nia.
Qed.

Lemma depth_le_of_W2 D : g_W g < fib (D + 3) -> 0 <= D -> forall i, g_pos g i -> g_leaf g i = true -> g_depth g i <= D.
Proof.
  intros HW HD i Pi Li. pose proof (depth_fib2 i Pi Li) as FB.
  destruct (Z_le_gt_dec (g_depth g i) D); [assumption|exfalso].
  pose proof (fib_mono (D + 3) (g_depth g i + 2) ltac:(lia)). lia.
Qed.

Theorem tdepth_le2 D : g_W g < fib (D + 3) -> 0 <= D -> forall c, 0 <= c < E -> W c <> 0 -> tdepth z c <= D.
Proof.
  intros HW HD c Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). unfold tdepth. apply (depth_le_of_W2 D HW HD _ P L).
Qed.

Theorem tnoovf2 : g_W g < fib (ML + 3) -> forall c, 0 <= c < E -> W c <> 0 -> zt_len z c = tdepth z c.
Proof.
  intros HW c Hc Wc. destruct (tpos_spec c Hc Wc) as (P & L & C). unfold tdepth. fold g.
  pose proof (zo_ML z ZOK) as M1. rewrite (tf_ML z E ML F Fl TF) in M1.
  apply (zo_len_noovf z ZOK).
  - intros i Pi Li. rewrite (tf_ML z E ML F Fl TF). apply (depth_le_of_W2 ML HW ltac:(lia) i Pi Li).
  - unfold zt_is_leaf_of. auto.
Qed.

Theorem tkraft2 : g_W g < fib (ML + 3) ->
  zsum (fun c => if W c =? 0 then 0 else 2 ^ (ML - zt_len z c)) 0 n = 2 ^ ML.
Proof.
  intros HW. pose proof (zo_ML z ZOK) as M1. rewrite (tf_ML z E ML F Fl TF) in M1.
  rewrite (reindex (fun c => 2 ^ (ML - zt_len z c))).
  rewrite <- (kraft_eq g G ML) by (intros i Pi Li; apply (depth_le_of_W2 ML HW ltac:(lia) i Pi Li)).
  apply lsum_ext. intros i Ii. apply (leaves_in g G) in Ii. destruct Ii as [Pi Li]. destruct (leaf_W i Pi Li) as [R Wi].
  pose proof (go_wt_leaf g G i Pi Li).
  rewrite (tnoovf2 HW (g_code g i) R ltac:(lia)). unfold tdepth. fold g. rewrite (tpos_of_leaf i Pi Li). reflexivity.
Qed.

Theorem tkraft_depth D : (forall c, 0 <= c < E -> W c <> 0 -> tdepth z c <= D) -> 0 <= D ->
  zsum (fun c => if W c =? 0 then 0 else 2 ^ (D - tdepth z c)) 0 n = 2 ^ D.
Proof.
  intros HD D0. rewrite (reindex (fun c => 2 ^ (D - tdepth z c))).
  rewrite <- (kraft_eq g G D).
  2:{ intros i Pi Li. destruct (leaf_W i Pi Li) as [R Wi]. pose proof (go_wt_leaf g G i Pi Li).
      pose proof (HD (g_code g i) R ltac:(lia)). unfold tdepth in H0. fold g in H0. rewrite (tpos_of_leaf i Pi Li) in H0. exact H0. }
  apply lsum_ext. intros i Ii. apply (leaves_in g G) in Ii. destruct Ii as [Pi Li].
  unfold tdepth. fold g. rewrite (tpos_of_leaf i Pi Li). reflexivity.
Qed.

Theorem tmono a c : 0 <= a < E -> 0 <= c < E -> W a <> 0 -> W a < W c -> tdepth z c <= tdepth z a.
Proof.
  intros Ha Hc Wa Wac. pose proof (W_nonneg a Ha).
  destruct (tpos_spec a Ha Wa) as (Pa & La & Ca). destruct (tpos_spec c Hc ltac:(lia)) as (Pc & Lc & Cc).
  unfold tdepth. fold g. apply (mono g G _ _ Pa La Pc Lc).
  rewrite (W_wt a Ha Wa), (W_wt c Hc ltac:(lia)). exact Wac.
Qed.

Theorem tspread s c : 0 <= s < E -> 0 <= c < E -> W s = 1 -> W c <> 0 -> tdepth z c <= tdepth z s + 1.
Proof.
  intros Hs Hc Ws Wc.
  destruct (tpos_spec s Hs ltac:(lia)) as (Ps & Ls & Cs). destruct (tpos_spec c Hc Wc) as (Pc & Lc & Cc).
  unfold tdepth. fold g. apply (depth_spread g G _ _ Ps Ls); [|exact Pc|exact Lc].
  intros x Px Lx. rewrite (W_wt s Hs ltac:(lia)), Ws. apply (go_wt_leaf g G x Px Lx).
Qed.

Theorem topt (K : Z) (tau : Z -> Z) : 0 <= K ->
  (forall c, 0 <= c < E -> W c <> 0 -> 0 <= tau c <= K) ->
  zsum (fun c => if W c =? 0 then 0 else 2 ^ (K - tau c)) 0 n <= 2 ^ K ->
  zsum (fun c => W c * tdepth z c) 0 n <= zsum (fun c => W c * tau c) 0 n.
Proof.
  intros K0 TR KR.
  rewrite (zsum_ext (fun c => W c * tdepth z c) (fun c => if W c =? 0 then 0 else W c * tdepth z c)) by (intros c _; destruct (Z.eqb_spec (W c) 0); lia).
  rewrite (zsum_ext (fun c => W c * tau c) (fun c => if W c =? 0 then 0 else W c * tau c)) by (intros c _; destruct (Z.eqb_spec (W c) 0); lia).
  rewrite !reindex.
  pose proof (optimal g G K K0 (fun i => tau (g_code g i))) as OPT.
  assert (CO : code_ok K (fun i => tau (g_code g i)) (leaves g)).
  { split.
    - intros i Ii. apply (leaves_in g G) in Ii. destruct Ii as [Pi Li]. destruct (leaf_W i Pi Li) as [R Wi].
      pose proof (go_wt_leaf g G i Pi Li). apply TR; [exact R|lia].
    - unfold ksum. rewrite <- (reindex (fun c => 2 ^ (K - tau c))). exact KR. }
  specialize (OPT CO). unfold csum in OPT.
  etransitivity; [|etransitivity; [exact OPT|]]; apply Z.eq_le_incl; apply lsum_ext; intros i Ii;
    apply (leaves_in g G) in Ii; destruct Ii as [Pi Li]; destruct (leaf_W i Pi Li) as [R Wi];
    unfold tdepth; fold g; rewrite ?(tpos_of_leaf i Pi Li), Wi; reflexivity.
Qed.

Theorem tused_two : 2 <= zsum (fun c => if W c =? 0 then 0 else 1) 0 n.
Proof.
  destruct (tf_two z E ML F Fl TF) as (a & b & Ha & Hb & Nab & Wa & Wb). fold W in Wa, Wb.
  set (f' := fun c => if (c =? a) || (c =? b) then (if W c =? 0 then 0 else 1) else 0).
  transitivity (zsum f' 0 n).
  - rewrite (zsum_two f' 0 n a b); [| rewrite n_E; lia | rewrite n_E; lia | exact Nab | ].
    + unfold f'. rewrite !Z.eqb_refl. cbn [orb].
      replace (b =? a) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb].
      unfold W in *. destruct (Z.eqb_spec (ffreq F Fl a) 0); [lia|]. destruct (Z.eqb_spec (ffreq F Fl b) 0); lia.
    + intros i _ Na Nb. unfold f'. replace (i =? a) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - apply zsum_mono. intros i _. unfold f'. destruct ((i =? a) || (i =? b)); [lia|]. destruct (W i =? 0); lia.
Qed.

Theorem tFl : (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f <= 2 /\ f < E /\ F f = 0).
Proof. exact (tf_Fl z E ML F Fl TF). Qed.

Theorem tW_F c : ~ In c Fl -> W c = F c.
Proof.
  intros NI. unfold W, ffreq. destruct (existsb (Z.eqb c) Fl) eqn:X; [|reflexivity].
  exfalso. apply existsb_In in X. exact (NI X).
Qed.
Theorem tW_forced c : In c Fl -> W c = 1 /\ F c = 0.
Proof.
  intros I. split; [|apply (proj2 (proj2 tFl) c I)]. unfold W, ffreq. replace (existsb (Z.eqb c) Fl) with true; [reflexivity|].
  symmetry. apply existsb_In. exact I.
Qed.

Theorem sumW_F : zsum W 0 n = zsum F 0 n + Z.of_nat (length Fl).
Proof.
  destruct tFl as (LF & ND & FF). unfold W. clear ZOK. clearbody W g n.
  assert (FF' : forall f, In f Fl -> 0 <= f < Z.of_nat n /\ F f = 0) by (intros f Hf; destruct (FF f Hf); rewrite n_E; lia).
  clear FF LF TF. revert ND FF'. induction Fl as [|f r IH]; intros ND FF'.
  - cbn [length]. rewrite (zsum_ext (ffreq F []) F) by reflexivity. lia.
  - inversion ND; subst. cbn [length]. rewrite Nat2Z.inj_succ.
    transitivity (zsum (fun c => (if c =? f then 1 - ffreq F r f else 0) + ffreq F r c) 0 n).
    + apply zsum_ext. intros c _. unfold ffreq. cbn [existsb]. destruct (Z.eqb_spec c f); cbn [orb]; [subst|lia].
      destruct (existsb (Z.eqb f) r) eqn:X; [|lia]. exfalso. apply existsb_In in X. tauto.
    + rewrite zsum_add. rewrite (IH ltac:(assumption) ltac:(intros; apply FF'; right; assumption)).
      rewrite (zsum_single _ 0 n f); [|apply FF'; left; reflexivity|intros i _ Ni; replace (i =? f) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity].
      rewrite Z.eqb_refl. unfold ffreq. destruct (existsb (Z.eqb f) r) eqn:X.
      * exfalso. apply existsb_In in X. tauto.
      * destruct (FF' f (or_introl eq_refl)) as [_ F0]. rewrite F0. lia.
Qed.

End TF.
End OverlayTrees.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayTrees.

Module OverlayDamage.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayHuff4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayTrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma lsum_zsum_swap : forall (F : Z -> Z -> Z) (L : list Z) lo n,
  lsum (fun i => zsum (F i) lo n) L = zsum (fun t => lsum (fun i => F i t) L) lo n.
Proof.
  intros F L lo n. induction L as [|x L IH]; cbn [lsum].
  - symmetry. apply zsum_0. intros; reflexivity.
  - rewrite IH, <- zsum_add. reflexivity.
Qed.

Lemma lsum_sub : forall (f g : Z -> Z) L, lsum (fun i => f i - g i) L = lsum f L - lsum g L.
Proof. intros. induction L; cbn; lia. Qed.

Lemma zsum_thresh : forall a T, 0 <= a <= T -> zsum (fun t => zind (t <=? a)) 1 (Z.to_nat T) = a.
Proof.
  intros a T Ha. replace (Z.to_nat T) with (Z.to_nat a + Z.to_nat (T - a))%nat by lia.
  rewrite zsum_split. rewrite (zsum_ext _ (fun _ => 1)), zsum_const1 by (intros t Ht; replace (t <=? a) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
  rewrite zsum_0 by (intros t Ht; replace (t <=? a) with false by (symmetry; apply Z.leb_gt; lia); reflexivity). lia.
Qed.

Lemma zsum_above : forall c m, 0 <= c -> 0 <= m -> zsum (fun r => zind (c <? r)) 1 (Z.to_nat m) = m - Z.min m c.
Proof.
  intros c m Hc Hm. destruct (Z_lt_le_dec c m) as [A|A].
  - replace (Z.to_nat m) with (Z.to_nat c + Z.to_nat (m - c))%nat by lia. rewrite zsum_split.
    rewrite zsum_0 by (intros r Hr; replace (c <? r) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    rewrite (zsum_ext _ (fun _ => 1)), zsum_const1 by (intros r Hr; replace (c <? r) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity). lia.
  - rewrite zsum_0 by (intros r Hr; replace (c <? r) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity). lia.
Qed.

Definition cnt (P : Z -> bool) (L : list Z) : Z := lsum (fun i => zind (P i)) L.

Lemma cnt_nonneg : forall P L, 0 <= cnt P L.
Proof. intros. unfold cnt. apply lsum_nonneg. intros; apply (proj1 (zind_le1 _)). Qed.

Lemma cnt_le_length : forall P L, cnt P L <= Z.of_nat (length L).
Proof. intros P L. unfold cnt. induction L; cbn [lsum length]; [lia|]. pose proof (zind_le1 (P a)). lia. Qed.

Lemma cnt_mono : forall (P Q : Z -> bool) L, (forall i, In i L -> P i = true -> Q i = true) -> cnt P L <= cnt Q L.
Proof.
  intros P Q L H. unfold cnt. apply lsum_le. intros i Hi. destruct (P i) eqn:E; [rewrite (H i Hi E); cbn; lia | pose proof (zind_le1 (Q i)); cbn; lia].
Qed.

Lemma cnt_ext : forall (P Q : Z -> bool) L, (forall i, In i L -> P i = Q i) -> cnt P L = cnt Q L.
Proof. intros. unfold cnt. apply lsum_ext. intros. rewrite H by assumption. reflexivity. Qed.

Lemma cnt_split : forall (P Q : Z -> bool) L, cnt P L = cnt (fun i => P i && Q i) L + cnt (fun i => P i && negb (Q i)) L.
Proof. intros. unfold cnt. rewrite <- lsum_add. apply lsum_ext. intros. destruct (P x), (Q x); reflexivity. Qed.

Lemma cnt_true : forall L, cnt (fun _ => true) L = Z.of_nat (length L).
Proof. intros. unfold cnt. cbn [zind]. induction L; cbn [lsum length]; lia. Qed.

Lemma cnt_pigeon : forall (P Q : Z -> bool) L, cnt Q L < cnt P L -> exists i, In i L /\ P i = true /\ Q i = false.
Proof.
  intros P Q L. unfold cnt. induction L as [|x L IH]; cbn [lsum]; [lia|]. intros H.
  destruct (P x) eqn:Px; destruct (Q x) eqn:Qx; cbn [zind] in H.
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
  - exists x. split; [left; reflexivity | auto].
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
Qed.

Lemma cnt_nested : forall (P Q : Z -> bool) L,
  (forall i j, In i L -> In j L -> P i = true -> Q i = false -> Q j = true -> P j = true) ->
  cnt (fun i => P i && Q i) L = Z.min (cnt P L) (cnt Q L).
Proof.
  intros P Q L H.
  destruct (forallb (fun i => implb (P i) (Q i)) L) eqn:FA.
  -
    assert (PQ : forall i, In i L -> P i = true -> Q i = true).
    { intros i Hi Pi. rewrite forallb_forall in FA. specialize (FA i Hi). rewrite Pi in FA. exact FA. }
    rewrite (cnt_ext (fun i => P i && Q i) P) by (intros i Hi; destruct (P i) eqn:E; [rewrite (PQ i Hi E); reflexivity | reflexivity]).
    pose proof (cnt_mono P Q L PQ). lia.
  -
    assert (EX : exists i0, In i0 L /\ P i0 = true /\ Q i0 = false).
    { clear - FA. induction L as [|x L IH]; cbn [forallb] in FA; [discriminate|].
      destruct (P x) eqn:Px; destruct (Q x) eqn:Qx; cbn [implb andb] in FA.
      - destruct (IH FA) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
      - exists x. split; [left; reflexivity | auto].
      - destruct (IH FA) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
      - destruct (IH FA) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto]. }
    destruct EX as (i0 & Hi0 & P0 & Q0).
    assert (QP : forall j, In j L -> Q j = true -> P j = true) by (intros j Hj Qj; exact (H i0 j Hi0 Hj P0 Q0 Qj)).
    rewrite (cnt_ext (fun i => P i && Q i) Q) by (intros i Hi; destruct (Q i) eqn:E; [rewrite (QP i Hi E); reflexivity | destruct (P i); reflexivity]).
    pose proof (cnt_mono Q P L QP). lia.
Qed.

Lemma zsum_prefix : forall (p : Z -> bool) T, 0 <= T ->
  (forall t t', 1 <= t -> t <= t' -> t' <= T -> p t' = true -> p t = true) ->
  let c := zsum (fun t => zind (p t)) 1 (Z.to_nat T) in
  0 <= c <= T /\ (1 <= c -> p c = true) /\ (1 <= T -> p 1 = true -> 1 <= c).
Proof.
  intros p T HT. remember (Z.to_nat T) as m eqn:Em.
  assert (ET : T = Z.of_nat m) by lia. subst T. clear HT Em.
  induction m as [|m IH]; intros Hanti; cbv zeta.
  - cbn [zsum]. lia.
  - rewrite zsum_snoc.
    specialize (IH ltac:(intros t t' A B C D; apply (Hanti t t'); lia || assumption)). cbv zeta in IH.
    destruct IH as (A & B & C).
    replace (1 + Z.of_nat m) with (Z.of_nat (S m)) by lia.
    destruct (p (Z.of_nat (S m))) eqn:PT; cbn [zind].
    + assert (ALL : forall t, 1 <= t <= Z.of_nat (S m) -> p t = true) by (intros t Ht; apply (Hanti t (Z.of_nat (S m))); lia || exact PT).
      assert (E : zsum (fun t => zind (p t)) 1 m = Z.of_nat m).
      { rewrite (zsum_ext _ (fun _ => 1)), zsum_const1; [reflexivity|]. intros t Ht. rewrite ALL by lia. reflexivity. }
      rewrite E. split; [lia|]. split; [intros _; replace (Z.of_nat m + 1) with (Z.of_nat (S m)) by lia; exact PT | intros; lia].
    + rewrite Z.add_0_r. split; [lia|]. split; [exact B|]. intros H1 P1.
      destruct m as [|m']; [change (Z.of_nat 1) with 1 in PT; congruence|]. apply C; [lia | exact P1].
Qed.

Lemma zsum_sub : forall f g lo n, zsum f lo n - zsum g lo n = zsum (fun i => f i - g i) lo n.
Proof. intros. induction n; cbn [zsum]; lia. Qed.

Lemma zsum_scale_r : forall c f lo n, zsum (fun i => f i * c) lo n = zsum f lo n * c.
Proof. intros. rewrite (zsum_ext _ (fun i => c * f i)) by (intros; lia). rewrite zsum_scale. lia. Qed.

Lemma zsum_extend : forall f m n, 0 <= m <= n ->
  zsum f 1 (Z.to_nat m) = zsum (fun r => zind (r <=? m) * f r) 1 (Z.to_nat n).
Proof.
  intros f m n H. replace (Z.to_nat n) with (Z.to_nat m + Z.to_nat (n - m))%nat by lia. rewrite zsum_split.
  rewrite (zsum_0 _ (1 + Z.of_nat (Z.to_nat m))) by (intros r Hr; replace (r <=? m) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  rewrite (zsum_ext f (fun r => zind (r <=? m) * f r) 1 (Z.to_nat m)) by (intros r Hr; replace (r <=? m) with true by (symmetry; apply Z.leb_le; lia); cbn [zind]; lia). lia.
Qed.



Definition Lc : Z := 254074700880.
Definition qtab (x : Z) : Z :=
  nth (Z.to_nat x) [254074700880; 254074700880; 127037350440; 84691566960; 50814940176; 31759337610; 19544207760;
                   12098795280; 7472785320; 4619540016; 2854771920; 1764407645; 1090449360] 0.

Lemma qtab_ok : forall x, 1 <= x <= 12 -> fib (x + 1) * qtab x = Lc /\ 0 <= qtab x.
Proof.
  intros x Hx.
  assert (H : forallb (fun x => (fib (x + 1) * qtab x =? Lc) && (0 <=? qtab x)) (map Z.of_nat (seq 1 12)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H x ltac:(apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia])).
  apply Bool.andb_true_iff in H. destruct H as [A B]. apply Z.eqb_eq in A. apply Z.leb_le in B. auto.
Qed.

Lemma Lc_pos : 0 < Lc. Proof. reflexivity. Qed.

Definition hget (h : list Z) (b : Z) : Z := if (1 <=? b) && (b <=? 12) then nth (Z.to_nat (b - 1)) h 0 else 0.
Definition capf (hf : Z -> Z) : hist :=
  fun b => if b <? 1 then 0 else if b <? 7 then hf b else if b =? 7 then zsum hf 7 6 else 0.
Definition cumf (hf : Z -> Z) (u : Z) : Z := zsum hf 1 (Z.to_nat (u - 1)).
Definition rk (c : Z -> Z) (r : Z) : Z := zsum (fun u => zind (c u <? r)) 1 12.
Definition pval (hf : Z -> Z) : Z :=
  let n := zsum hf 1 12 in
  let cd := cumf hf in
  let cl := cumf (repair 7 (capf hf)) in
  zsum (fun r => Z.max 0 (rk cl r - rk cd r) * qtab (rk cd r)) 1 (Z.to_nat n).
Definition pval_fast (h : list Z) : Z :=
  let hf := hget h in
  let n := zsum hf 1 12 in
  let lam := map (repair 7 (capf hf)) (map Z.of_nat (seq 1 12)) in
  let cdl := map (cumf hf) (map Z.of_nat (seq 1 12)) in
  let cll := map (cumf (hget lam)) (map Z.of_nat (seq 1 12)) in
  let rkd := map (rk (hget cdl)) (map Z.of_nat (seq 1 (Z.to_nat n))) in
  let rkl := map (rk (hget cll)) (map Z.of_nat (seq 1 (Z.to_nat n))) in
  zsum (fun r => let dd := nth (Z.to_nat (r - 1)) rkd 0 in Z.max 0 (nth (Z.to_nat (r - 1)) rkl 0 - dd) * qtab dd) 1 (Z.to_nat n).
Definition ptest (rnum rden : Z) (h : list Z) : bool := rden * pval_fast h <=? rnum * Lc.

Fixpoint penum (lev : nat) (b krem nrem : Z) (acc : list Z) (test : list Z -> bool) : bool :=
  match lev with
  | O => if krem =? 0 then test (rev acc) else true
  | S lev' => let unit := 2 ^ (12 - b) in
      if nrem * unit <? krem then true
      else forallb (fun hb => penum lev' (b + 1) (krem - hb * unit) (nrem - hb) (hb :: acc) test)
                   (map Z.of_nat (seq 0 (S (Z.to_nat (Z.min nrem (krem / unit))))))
  end.

Definition dmg_cert (K rnum rden : Z) : bool :=
  (0 <=? rnum) && (1 <=? rden) && penum 12 1 4096 K [] (ptest rnum rden).

Lemma dmg_cert_pos K rnum rden : dmg_cert K rnum rden = true -> 0 <= rnum /\ 1 <= rden.
Proof. unfold dmg_cert. rewrite !Bool.andb_true_iff, Z.leb_le, Z.leb_le. tauto. Qed.



Fixpoint kr (b : Z) (hs : list Z) : Z :=
  match hs with [] => 0 | x :: r => x * 2 ^ (12 - b) + kr (b + 1) r end.

Lemma kr_nonneg : forall hs b, Forall (fun x => 0 <= x) hs -> 0 <= kr b hs.
Proof.
  induction hs as [|x hs IH]; intros b F; cbn [kr]; [lia|]. inversion F; subst.
  pose proof (IH (b + 1) ltac:(assumption)). pose proof (Z.pow_nonneg 2 (12 - b) ltac:(lia)). nia.
Qed.

Lemma kr_le : forall hs b, Forall (fun x => 0 <= x) hs -> b + Z.of_nat (length hs) <= 13 -> kr b hs <= lsum (fun x => x) hs * 2 ^ (12 - b).
Proof.
  induction hs as [|x hs IH]; intros b F Hb; cbn [kr lsum length] in *; [lia|]. inversion F; subst.
  specialize (IH (b + 1) ltac:(assumption) ltac:(lia)).
  assert (P : 2 ^ (12 - (b + 1)) <= 2 ^ (12 - b)) by (apply Z.pow_le_mono_r; lia).
  pose proof (lsum_nonneg (fun x => x) hs ltac:(intros y Hy; cbv beta; eapply (Forall_forall (fun x => 0 <= x) hs); eassumption)).
  pose proof (Z.pow_nonneg 2 (12 - (b + 1)) ltac:(lia)). nia.
Qed.

Lemma penum_sound : forall hs lev b krem nrem acc test,
  penum lev b krem nrem acc test = true -> length hs = lev -> Forall (fun x => 0 <= x) hs -> 1 <= b -> b + Z.of_nat lev <= 13 ->
  kr b hs = krem -> lsum (fun x => x) hs <= nrem -> test (rev acc ++ hs) = true.
Proof.
  induction hs as [|x hs IH]; intros lev b krem nrem acc test E Hlen F Hb Hlev K S; cbn [length] in Hlen; subst lev.
  - cbn [penum kr] in E, K. subst krem. rewrite Z.eqb_refl in E. rewrite app_nil_r. exact E.
  - cbn [penum] in E. cbn [kr] in K. cbn [lsum] in S. apply Forall_cons_iff in F. destruct F as [Fx Fhs].
    pose proof (kr_nonneg hs (b + 1) ltac:(assumption)) as K0.
    pose proof (lsum_nonneg (fun x => x) hs ltac:(intros y Hy; cbv beta; eapply (Forall_forall (fun x => 0 <= x) hs); eassumption)) as S0.
    pose proof (kr_le hs (b + 1) ltac:(assumption) ltac:(lia)) as KL.
    assert (U : 0 < 2 ^ (12 - b)) by (apply Z.pow_pos_nonneg; lia).
    assert (P : 2 ^ (12 - (b + 1)) <= 2 ^ (12 - b)) by (apply Z.pow_le_mono_r; lia).
    replace (nrem * 2 ^ (12 - b) <? krem) with false in E by (symmetry; apply Z.ltb_ge; nia).
    rewrite forallb_forall in E.
    assert (Xle : x <= krem / 2 ^ (12 - b)) by (apply Z.div_le_lower_bound; [lia | nia]).
    specialize (E x ltac:(apply in_map_iff; exists (Z.to_nat x); split; [lia|]; apply in_seq; lia)).
    replace (rev acc ++ x :: hs) with (rev (x :: acc) ++ hs) by (cbn [rev]; rewrite <- app_assoc; reflexivity).
    apply (IH (length hs) (b + 1) (krem - x * 2 ^ (12 - b)) (nrem - x) (x :: acc) test E eq_refl ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma dmg_cert_sound : forall K rnum rden h, dmg_cert K rnum rden = true ->
  length h = 12%nat -> Forall (fun x => 0 <= x) h -> kr 1 h = 4096 -> lsum (fun x => x) h <= K ->
  rden * pval_fast h <= rnum * Lc.
Proof.
  intros K rnum rden h C Hl F HK HS. unfold dmg_cert in C. rewrite !Bool.andb_true_iff in C. destruct C as [[_ _] C].
  pose proof (penum_sound h 12 1 4096 K [] (ptest rnum rden) C Hl F ltac:(lia) ltac:(lia) HK HS) as T.
  cbn [rev app] in T. unfold ptest in T. apply Z.leb_le in T. exact T.
Qed.


Lemma hget_map : forall (f : Z -> Z) n b, 1 <= b <= Z.of_nat n -> (n <= 12)%nat -> hget (map f (map Z.of_nat (seq 1 n))) b = f b.
Proof.
  intros f n b Hb Hn. unfold hget. replace ((1 <=? b) && (b <=? 12)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  rewrite map_map. apply nth_error_nth.
  rewrite nth_error_map, (nth_error_seq 1 n (Z.to_nat (b - 1))). replace (Z.to_nat (b - 1) <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map]. f_equal. f_equal. lia.
Qed.

Lemma cumf_ext : forall f f' u, 1 <= u <= 13 -> (forall b, 1 <= b <= 12 -> f b = f' b) -> cumf f u = cumf f' u.
Proof. intros. unfold cumf. apply zsum_ext. intros. apply H0. lia. Qed.

Lemma rk_ext : forall c c' r, (forall u, 1 <= u <= 12 -> c u = c' u) -> rk c r = rk c' r.
Proof. intros. unfold rk. apply zsum_ext. intros. rewrite H by lia. reflexivity. Qed.

Lemma capf_ext : forall f f' b, (forall x, 1 <= x <= 12 -> f x = f' x) -> capf f b = capf f' b.
Proof.
  intros f f' b H. unfold capf. destruct (Z.ltb_spec b 1); [reflexivity|]. destruct (Z.ltb_spec b 7); [apply H; lia|].
  destruct (Z.eqb_spec b 7); [|reflexivity]. apply zsum_ext. intros; apply H; lia.
Qed.

Lemma d_rep_find_ext : forall n (h h' : hist) b, (forall x, h x = h' x) -> rep_find n h b = rep_find n h' b.
Proof. induction n as [|n IH]; intros h h' b E; cbn [rep_find]; [reflexivity|]. rewrite E. destruct (h' b =? 0); [apply IH; exact E | reflexivity]. Qed.

Lemma d_rep_iter_ext : forall n ML (h h' : hist), (forall x, h x = h' x) -> forall x, rep_iter n ML h x = rep_iter n ML h' x.
Proof.
  induction n as [|n IH]; intros ML h h' E x; cbn [rep_iter]; [apply E|].
  apply IH. intros y. unfold rep_step. rewrite (d_rep_find_ext _ h h') by exact E. rewrite !E. reflexivity.
Qed.

Lemma d_repair_ext : forall ML (h h' : hist), (forall x, h x = h' x) -> forall x, repair ML h x = repair ML h' x.
Proof.
  intros ML h h' E x. unfold repair, kraftZ. rewrite (zsum_ext (fun b => h b * 2 ^ (ML - b)) (fun b => h' b * 2 ^ (ML - b))) by (intros; rewrite E; reflexivity).
  apply d_rep_iter_ext. exact E.
Qed.

Lemma pval_ext : forall f f', (forall b, 1 <= b <= 12 -> f b = f' b) -> pval f = pval f'.
Proof.
  intros f f' E. unfold pval.
  rewrite (zsum_ext f f' 1 12) by (intros; apply E; lia).
  apply zsum_ext. intros r Hr.
  assert (RD : rk (cumf f) r = rk (cumf f') r) by (apply rk_ext; intros; apply cumf_ext; [lia | exact E]).
  assert (RL : rk (cumf (repair 7 (capf f))) r = rk (cumf (repair 7 (capf f'))) r).
  { apply rk_ext. intros u Hu. apply cumf_ext; [lia|]. intros b Hb. apply d_repair_ext. intros x. apply capf_ext. exact E. }
  rewrite RD, RL. reflexivity.
Qed.

Lemma hget_nonneg_sum : forall h, Forall (fun x => 0 <= x) h -> forall b, 0 <= hget h b.
Proof.
  intros h F b. unfold hget. destruct (_ && _); [|lia]. destruct (nth_in_or_default (Z.to_nat (b - 1)) h 0) as [I| ->]; [|lia].
  eapply (Forall_forall (fun x => 0 <= x) h); eassumption.
Qed.

Lemma pval_fast_eq : forall h, Forall (fun x => 0 <= x) h -> pval_fast h = pval (hget h).
Proof.
  intros h F. unfold pval_fast, pval.
  set (hf := hget h). set (n := zsum hf 1 12).
  assert (N0 : 0 <= n) by (subst n; apply zsum_nonneg; intros; apply hget_nonneg_sum; exact F).
  set (lam := map (repair 7 (capf hf)) (map Z.of_nat (seq 1 12))).
  set (cdl := map (cumf hf) (map Z.of_nat (seq 1 12))). set (cll := map (cumf (hget lam)) (map Z.of_nat (seq 1 12))).
  assert (CD : forall r, rk (hget cdl) r = rk (cumf hf) r).
  { intros r. apply rk_ext. intros u Hu. subst cdl. apply hget_map; lia. }
  assert (CL : forall r, rk (hget cll) r = rk (cumf (repair 7 (capf hf))) r).
  { intros r. apply rk_ext. intros u Hu. subst cll. rewrite hget_map by lia. apply cumf_ext; [lia|]. intros b Hb. subst lam. apply hget_map; lia. }
  apply zsum_ext. intros r Hr. cbv zeta.
  assert (NTH : forall (g : Z -> Z), nth (Z.to_nat (r - 1)) (map g (map Z.of_nat (seq 1 (Z.to_nat n)))) 0 = g r).
  { intros g. rewrite map_map. apply nth_error_nth.
    rewrite nth_error_map, (nth_error_seq 1 (Z.to_nat n) (Z.to_nat (r - 1))). replace (Z.to_nat (r - 1) <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map]. f_equal. f_equal. lia. }
  rewrite !NTH, CD, CL. reflexivity.
Qed.

Lemma lsum_seq : forall f n s, lsum f (map Z.of_nat (seq s n)) = zsum f (Z.of_nat s) n.
Proof.
  intros f. induction n as [|n IH]; intros s; [reflexivity|]. cbn [seq map lsum]. rewrite zsum_shift, IH. f_equal. f_equal. lia.
Qed.

Lemma kr_zsum : forall f n s, kr (Z.of_nat s) (map f (map Z.of_nat (seq s n))) = zsum (fun b => f b * 2 ^ (12 - b)) (Z.of_nat s) n.
Proof.
  intros f. induction n as [|n IH]; intros s; [reflexivity|]. cbn [seq map kr]. rewrite zsum_shift. f_equal.
  replace (Z.of_nat s + 1) with (Z.of_nat (S s)) by lia. apply IH.
Qed.

Lemma rep_find_le : forall n (h : hist) b, rep_find n h b <= b.
Proof. induction n as [|n IH]; intros h b; cbn [rep_find]; [lia|]. destruct (h b =? 0); [pose proof (IH h (b - 1)); lia | lia]. Qed.

Lemma d_rep_iter_above : forall n ML (h : hist) b, ML < b -> rep_iter n ML h b = h b.
Proof.
  induction n as [|n IH]; intros ML h b Hb; cbn [rep_iter]; [reflexivity|].
  rewrite IH by exact Hb. unfold rep_step. pose proof (rep_find_le (Z.to_nat ML) h (ML - 1)).
  replace (b =? rep_find (Z.to_nat ML) h (ML - 1)) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (b =? rep_find (Z.to_nat ML) h (ML - 1) + 1) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (b =? ML) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma d_repair_above : forall ML (h : hist) b, ML < b -> repair ML h b = h b.
Proof. intros. unfold repair. apply d_rep_iter_above. assumption. Qed.


Section Damage.
Variable L : list Z.
Variable w : Z -> Z.
Variable d : Z -> Z.
Variable l : Z -> Z.
Definition Wt : Z := lsum w L.
Definition nL : Z := Z.of_nat (length L).
Hypothesis Hw : forall i, In i L -> 1 <= w i.
Hypothesis Hd : forall i, In i L -> 1 <= d i <= 12.
Hypothesis Hl : forall i, In i L -> 1 <= l i <= 12.
Hypothesis Md : forall i j, In i L -> In j L -> w i < w j -> d j <= d i.
Hypothesis Ml : forall i j, In i L -> In j L -> w i < w j -> l j <= l i.
Hypothesis FIB : forall i, In i L -> w i * fib (d i + 1) <= Wt.

Definition mt (t : Z) : Z := cnt (fun i => t <=? w i) L.
Definition cv (v : Z -> Z) (u : Z) : Z := cnt (fun i => v i <? u) L.
Definition dv (v : Z -> Z) (r : Z) : Z := zsum (fun u => zind (cv v u <? r)) 1 12.
Definition Tr (r : Z) : Z := zsum (fun t => zind (r <=? mt t)) 1 (Z.to_nat Wt).

Lemma Wt_ge : forall i, In i L -> w i <= Wt.
Proof. intros i Hi. unfold Wt. apply lsum_ge_member; [| exact Hi]. intros j Hj. pose proof (Hw j Hj). lia. Qed.

Lemma Wt_nonneg : 0 <= Wt.
Proof. unfold Wt. apply lsum_nonneg. intros j Hj. pose proof (Hw j Hj). lia. Qed.

Lemma mt_range : forall t, 0 <= mt t <= nL.
Proof. intros. unfold mt, nL. split; [apply cnt_nonneg | apply cnt_le_length]. Qed.

Lemma cv_nonneg : forall v u, 0 <= cv v u.
Proof. intros. unfold cv. apply cnt_nonneg. Qed.

Lemma weighted_layers : forall v : Z -> Z,
  (forall i, In i L -> 1 <= v i <= 12) -> (forall i j, In i L -> In j L -> w i < w j -> v j <= v i) ->
  lsum (fun i => w i * v i) L = zsum (fun t => zsum (fun r => dv v r) 1 (Z.to_nat (mt t))) 1 (Z.to_nat Wt).
Proof.
  intros v Hv Mv.
  rewrite (lsum_ext (fun i => w i * v i) (fun i => zsum (fun t => zind (t <=? w i) * v i) 1 (Z.to_nat Wt)) L)
    by (intros i Hi; rewrite zsum_scale_r, zsum_thresh by (pose proof (Hw i Hi); pose proof (Wt_ge i Hi); lia); reflexivity).
  rewrite lsum_zsum_swap. apply zsum_ext. intros t Ht.
  rewrite (lsum_ext (fun i => zind (t <=? w i) * v i) (fun i => zsum (fun u => zind ((t <=? w i) && (u <=? v i))) 1 12) L).
  2:{ intros i Hi. rewrite <- (zsum_thresh (v i) 12) at 1 by (pose proof (Hv i Hi); lia). rewrite <- zsum_scale.
      apply zsum_ext. intros u Hu. destruct (t <=? w i), (u <=? v i); reflexivity. }
  rewrite lsum_zsum_swap.
  transitivity (zsum (fun u => mt t - Z.min (mt t) (cv v u)) 1 12).
  - apply zsum_ext. intros u Hu. change (lsum (fun i : Z => zind ((t <=? w i) && (u <=? v i))) L) with (cnt (fun i => (t <=? w i) && (u <=? v i)) L).
    unfold mt, cv. rewrite <- (cnt_nested (fun i => t <=? w i) (fun i => v i <? u) L).
    + rewrite (cnt_split (fun i => t <=? w i) (fun i => v i <? u) L).
      rewrite (cnt_ext (fun i => (t <=? w i) && negb (v i <? u)) (fun i => (t <=? w i) && (u <=? v i))); [lia|].
      intros i Hi. f_equal. destruct (Z.ltb_spec (v i) u); destruct (Z.leb_spec u (v i)); cbn; lia.
    +
      intros i j Hi Hj Pi Qi Qj. apply Z.leb_le in Pi. apply Z.ltb_ge in Qi. apply Z.ltb_lt in Qj. apply Z.leb_le.
      destruct (Z_lt_le_dec (w j) t) as [A|A]; [|exact A]. exfalso. pose proof (Mv j i Hj Hi ltac:(lia)). lia.
  - rewrite (zsum_ext (fun u => mt t - Z.min (mt t) (cv v u)) (fun u => zsum (fun r => zind (cv v u <? r)) 1 (Z.to_nat (mt t)))) by (intros u Hu; rewrite zsum_above by (pose proof (cv_nonneg v u); pose proof (mt_range t); lia); reflexivity).
    unfold dv. apply zsum_swap.
Qed.

Definition er (r : Z) : Z := dv l r - dv d r.

Lemma damage_ranks :
  lsum (fun i => w i * l i) L - lsum (fun i => w i * d i) L = zsum (fun r => er r * Tr r) 1 (Z.to_nat nL).
Proof.
  rewrite (weighted_layers l Hl Ml), (weighted_layers d Hd Md). rewrite zsum_sub.
  rewrite (zsum_ext _ (fun t => zsum (fun r => zind (r <=? mt t) * er r) 1 (Z.to_nat nL))).
  2:{ intros t Ht. rewrite zsum_sub. rewrite (zsum_ext (fun i => dv l i - dv d i) er) by (intros; unfold er; reflexivity). apply zsum_extend. apply mt_range. }
  rewrite zsum_swap. apply zsum_ext. intros r Hr. unfold Tr. rewrite zsum_scale_r. lia.
Qed.

Lemma dv_range : forall v r, 1 <= r -> (forall i, In i L -> 1 <= v i <= 12) -> 1 <= dv v r <= 12.
Proof.
  intros v r Hr Hv. unfold dv.
  assert (C1 : cv v 1 = 0).
  { unfold cv, cnt. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros i Hi. replace (v i <? 1) with false by (symmetry; apply Z.ltb_ge; pose proof (Hv i Hi); lia). reflexivity. }
  change 12%nat with (S 11). rewrite zsum_shift, C1. replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn [zind].
  pose proof (zsum_nonneg (fun u => zind (cv v u <? r)) (1 + 1) 11 ltac:(intros; apply (proj1 (zind_le1 _)))).
  pose proof (zsum_mono (fun u => zind (cv v u <? r)) (fun _ => 1) (1 + 1) 11 ltac:(intros; apply (proj2 (zind_le1 _)))). rewrite zsum_const1 in H0. lia.
Qed.

Lemma Tr_nonneg : forall r, 0 <= Tr r.
Proof. intros. unfold Tr. apply zsum_nonneg. intros; apply (proj1 (zind_le1 _)). Qed.

Lemma Tr_fib : forall r, 1 <= r <= nL -> Tr r * fib (dv d r + 1) <= Wt.
Proof.
  intros r Hr. pose proof Wt_nonneg as W0.
  destruct (zsum_prefix (fun t => r <=? mt t) Wt W0) as (A & B & C).
  { intros t t' H1 H2 H3 P. apply Z.leb_le in P. apply Z.leb_le. pose proof (cnt_mono (fun i => t' <=? w i) (fun i => t <=? w i) L ltac:(intros i Hi X; apply Z.leb_le in X; apply Z.leb_le; lia)). unfold mt in *. lia. }
  fold (Tr r) in A, B, C.
  destruct (Z.eq_dec (Tr r) 0) as [Z0|NZ]; [rewrite Z0; lia|].
  specialize (B ltac:(lia)). apply Z.leb_le in B.
  destruct (zsum_prefix (fun u => cv d u <? r) 12 ltac:(lia)) as (A' & B' & C').
  { intros u u' H1 H2 H3 P. apply Z.ltb_lt in P. apply Z.ltb_lt. pose proof (cnt_mono (fun i => d i <? u) (fun i => d i <? u') L ltac:(intros i Hi X; apply Z.ltb_lt in X; apply Z.ltb_lt; lia)). unfold cv in *. lia. }
  replace (zsum (fun t : Z => zind (cv d t <? r)) 1 (Z.to_nat 12)) with (dv d r) in A', B', C' by reflexivity.
  pose proof (dv_range d r ltac:(lia) Hd) as DR. specialize (B' ltac:(lia)). apply Z.ltb_lt in B'.
  destruct (cnt_pigeon (fun i => Tr r <=? w i) (fun i => d i <? dv d r) L ltac:(unfold mt, cv in *; lia)) as (i & Hi & P & Q).
  apply Z.leb_le in P. apply Z.ltb_ge in Q.
  pose proof (FIB i Hi). pose proof (fib_mono (dv d r + 1) (d i + 1) ltac:(lia)). pose proof (fib_nonneg (dv d r + 1)). nia.
Qed.

Lemma step_rank : forall (q : Z -> Z) (Lc : Z) r, 1 <= r <= nL ->
  (forall x, 1 <= x <= 12 -> fib (x + 1) * q x = Lc /\ 0 <= q x) ->
  Lc * (er r * Tr r) <= Wt * (Z.max 0 (er r) * q (dv d r)).
Proof.
  intros q Lc r Hr Hq.
  pose proof (Tr_nonneg r) as T0. pose proof (Tr_fib r Hr) as TF.
  destruct (Hq (dv d r) (dv_range d r ltac:(lia) Hd)) as [E Q0]. rewrite <- E.
  assert (M0 : 0 <= Z.max 0 (er r) /\ er r <= Z.max 0 (er r)) by lia.
  pose proof (fib_nonneg (dv d r + 1)) as F0.
  generalize dependent TF. generalize dependent T0. generalize dependent Q0. generalize dependent M0. generalize dependent F0.
  generalize (Z.max 0 (er r)) as M. generalize (er r) as e. generalize (Tr r) as t1. generalize (fib (dv d r + 1)) as f1. generalize (q (dv d r)) as q1. generalize Wt as Wv.
  intros Wv q1 f1 t1 e M F0 M0 Q0 T0 TF.
  assert (H1 : e * t1 <= M * t1) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (FQ : 0 <= f1 * q1) by (apply Z.mul_nonneg_nonneg; lia).
  assert (H2 : f1 * q1 * (e * t1) <= f1 * q1 * (M * t1)) by (apply Z.mul_le_mono_nonneg_l; [exact FQ | exact H1]).
  assert (H3 : f1 * q1 * (M * t1) = (t1 * f1) * (M * q1)) by ring.
  assert (MQ : 0 <= M * q1) by (apply Z.mul_nonneg_nonneg; lia).
  assert (H4 : (t1 * f1) * (M * q1) <= Wv * (M * q1)) by (apply Z.mul_le_mono_nonneg_r; [exact MQ | exact TF]).
  lia.
Qed.

Theorem damage_bound : forall (q : Z -> Z) (Lc rnum rden : Z),
  0 < Lc -> (forall x, 1 <= x <= 12 -> fib (x + 1) * q x = Lc /\ 0 <= q x) -> 0 <= rnum -> 1 <= rden ->
  rden * zsum (fun r => Z.max 0 (er r) * q (dv d r)) 1 (Z.to_nat nL) <= rnum * Lc ->
  rden * lsum (fun i => w i * l i) L <= rden * lsum (fun i => w i * d i) L + rnum * Wt.
Proof.
  intros q Lc rnum rden HLc Hq Hrn Hrd CERT. pose proof Wt_nonneg as W0.
  pose proof damage_ranks as DR.
  assert (STEP : Lc * zsum (fun r => er r * Tr r) 1 (Z.to_nat nL) <= Wt * zsum (fun r => Z.max 0 (er r) * q (dv d r)) 1 (Z.to_nat nL)).
  { rewrite <- !zsum_scale. apply zsum_mono. intros r Hr. apply (step_rank q Lc r ltac:(lia) Hq). }
  revert DR STEP CERT W0 HLc Hrd Hrn.
  generalize (zsum (fun r => er r * Tr r) 1 (Z.to_nat nL)) as S1. generalize (zsum (fun r => Z.max 0 (er r) * q (dv d r)) 1 (Z.to_nat nL)) as S2.
  generalize (lsum (fun i => w i * l i) L) as A. generalize (lsum (fun i => w i * d i) L) as B. generalize Wt as Wv.
  intros Wv B A S2 S1 DR STEP CERT W0 HLc Hrd Hrn.
  assert (K1 : rden * (Lc * S1) <= rden * (Wv * S2)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (K2 : Wv * (rden * S2) <= Wv * (rnum * Lc)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (K3 : Lc * (rden * (A - B)) <= Lc * (rnum * Wv)).
  { rewrite DR. replace (Lc * (rden * S1)) with (rden * (Lc * S1)) by ring. replace (Lc * (rnum * Wv)) with (Wv * (rnum * Lc)) by ring.
    replace (rden * (Wv * S2)) with (Wv * (rden * S2)) in K1 by ring. lia. }
  apply Z.mul_le_mono_pos_l in K3; [lia | exact HLc].
Qed.

Definition hd (b : Z) : Z := cnt (fun i => d i =? b) L.

Lemma cv_cum : forall v u, (forall i, In i L -> 1 <= v i <= 12) -> 1 <= u <= 13 ->
  cv v u = zsum (fun b => cnt (fun i => v i =? b) L) 1 (Z.to_nat (u - 1)).
Proof.
  intros v u Hv Hu. unfold cv, cnt. rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (Hv i Hi).
  destruct (Z.ltb_spec (v i) u).
  - rewrite (zsum_single (fun b => zind (v i =? b)) 1 (Z.to_nat (u - 1)) (v i)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros b Hb Nb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - symmetry. apply zsum_0. intros b Hb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma nL_hd : zsum hd 1 12 = nL.
Proof.
  pose proof (cv_cum d 13 Hd ltac:(lia)) as E. change (Z.to_nat (13 - 1)) with 12%nat in E. unfold hd. rewrite <- E.
  unfold cv, nL. rewrite <- cnt_true. apply cnt_ext. intros i Hi. apply Z.ltb_lt. pose proof (Hd i Hi). lia.
Qed.

Theorem damage_cert : forall K rnum rden, dmg_cert K rnum rden = true ->
  (forall i, In i L -> l i <= 7) ->
  (forall b, 1 <= b <= 7 -> cnt (fun i => l i =? b) L = repair 7 (capf hd) b) ->
  lsum (fun i => 2 ^ (12 - d i)) L = 2 ^ 12 -> nL <= K ->
  rden * lsum (fun i => w i * l i) L <= rden * lsum (fun i => w i * d i) L + rnum * Wt.
Proof.
  intros K rnum rden C Hl7 HIST KR HK. pose proof (dmg_cert_pos K rnum rden C) as [R0 R1].
  set (h := map hd (map Z.of_nat (seq 1 12))).
  assert (HH : forall b, 1 <= b <= 12 -> hget h b = hd b) by (intros b Hb; subst h; apply hget_map; lia).
  assert (F : Forall (fun x => 0 <= x) h).
  { subst h. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _). unfold hd. apply cnt_nonneg. }
  assert (KRh : kr 1 h = 4096).
  { subst h. change 1 with (Z.of_nat 1) at 1. rewrite kr_zsum. change (Z.of_nat 1) with 1.
    transitivity (lsum (fun i => 2 ^ (12 - d i)) L); [| rewrite KR; reflexivity].
    unfold hd, cnt. rewrite (zsum_ext _ (fun b => lsum (fun i => zind (d i =? b) * 2 ^ (12 - b)) L)) by (intros; rewrite Z.mul_comm, <- lsum_scale; apply lsum_ext; intros; lia).
    rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (Hd i Hi).
    rewrite (zsum_single (fun b => zind (d i =? b) * 2 ^ (12 - b)) 1 12 (d i)); [rewrite Z.eqb_refl; cbn [zind]; lia | lia |].
    intros b Hb Nb. replace (d i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (SUMh : lsum (fun x => x) h <= K).
  { subst h. rewrite lsum_map, lsum_seq. change (Z.of_nat 1) with 1. change (zsum (fun x : Z => hd x) 1 12) with (zsum hd 1 12). rewrite nL_hd. exact HK. }
  pose proof (dmg_cert_sound K rnum rden h C ltac:(subst h; rewrite !length_map, length_seq; reflexivity) F KRh SUMh) as CERT.
  rewrite (pval_fast_eq h F), (pval_ext (hget h) hd HH) in CERT.
  apply (damage_bound qtab Lc rnum rden Lc_pos qtab_ok R0 R1).
  unfold pval in CERT. rewrite nL_hd in CERT.
  rewrite (zsum_ext (fun r => Z.max 0 (rk (cumf (repair 7 (capf hd))) r - rk (cumf hd) r) * qtab (rk (cumf hd) r))
                    (fun r => Z.max 0 (er r) * qtab (dv d r))) in CERT; [exact CERT|].
  intros r Hr.
  assert (ED : rk (cumf hd) r = dv d r).
  { unfold rk, dv. apply zsum_ext. intros u Hu. unfold cumf, hd. rewrite <- (cv_cum d u Hd) by lia. reflexivity. }
  assert (EL : rk (cumf (repair 7 (capf hd))) r = dv l r).
  { unfold rk, dv. apply zsum_ext. intros u Hu. f_equal. f_equal. unfold cumf. rewrite (cv_cum l u Hl) by lia.
    apply zsum_ext. intros b Hb. destruct (Z_lt_le_dec 7 b) as [B7|B7].
    - rewrite d_repair_above by lia. unfold capf. replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (b <? 7) with false by (symmetry; apply Z.ltb_ge; lia). replace (b =? 7) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold cnt. symmetry. etransitivity; [apply lsum_ext; intros i Hi; replace (l i =? b) with false by (symmetry; apply Z.eqb_neq; pose proof (Hl7 i Hi); lia); reflexivity | apply lsum_zero].
    - symmetry. apply HIST. lia. }
  rewrite ED, EL. unfold er. reflexivity.
Qed.

End Damage.


Section Tree.
Variable z : ztree.
Variable F : Z -> Z.
Variable Fl : list Z.
Hypothesis TF : tree_facts z 19 7 F Fl.
Local Notation g := (zt_g z).
Let GG : gtree_ok g := G z 19 7 F Fl TF.
Let ZOK : ztree_ok z := tf_ok z 19 7 F Fl TF.
Local Notation W := (ffreq F Fl).
Local Notation Lv := (leaves g).
Local Notation wt := (g_wt g).
Local Notation dp := (g_depth g).
Definition ln : Z -> Z := fun i => zt_len z (g_code g i).

Lemma ML7 : zt_ML z = 7. Proof. exact (tf_ML z 19 7 F Fl TF). Qed.

Lemma Lv_in : forall i, In i Lv <-> (g_lo g <= i <= g_hi g /\ g_leaf g i = true).
Proof. intros i. exact (leaves_in g GG i). Qed.

Lemma g_hist_cnt : forall (f : Z -> Z) b, g_hist g f b = cnt (fun i => f i =? b) Lv.
Proof.
  intros f b. unfold g_hist, cnt, leaves, allpos, npos. rewrite lsum_filter, lsum_zsum.
  apply zsum_ext. intros i Hi. destruct (g_leaf g i); reflexivity.
Qed.

Lemma code_sum : forall h : Z -> Z, zsum (fun x => W x * h x) 0 19 = lsum (fun i => wt i * h (g_code g i)) Lv.
Proof.
  intros h. transitivity (zsum (fun c => if W c =? 0 then 0 else W c * h c) 0 (Z.to_nat 19)).
  - apply zsum_ext. intros c Hc. destruct (Z.eqb_spec (W c) 0) as [E|N]; [rewrite E; lia | reflexivity].
  - rewrite (reindex z 19 7 F Fl TF (fun c => W c * h c)). apply lsum_ext. intros i Hi. apply Lv_in in Hi. destruct Hi as [P L].
    destruct (leaf_W z 19 7 F Fl TF i P L) as [_ E]. rewrite E. reflexivity.
Qed.

Theorem bl_damage_tree : forall K rnum rden, dmg_cert K rnum rden = true -> g_W g < fib 14 ->
  zsum (fun x => if W x =? 0 then 0 else 1) 0 19 <= K ->
  rden * zsum (fun x => W x * zt_len z x) 0 19 <= rden * zsum (fun x => W x * tdepth z x) 0 19 + rnum * g_W g.
Proof.
  intros K rnum rden C HW HK. pose proof (dmg_cert_pos K rnum rden C) as [R0 R1].
  rewrite (code_sum (zt_len z)), (code_sum (tdepth z)).
  rewrite (lsum_ext (fun i => wt i * tdepth z (g_code g i)) (fun i => wt i * dp i))
    by (intros i Hi; apply Lv_in in Hi; destruct Hi as [P L]; unfold tdepth; rewrite (tpos_of_leaf z 19 7 F Fl TF i P L); reflexivity).
  change (fun i : Z => wt i * zt_len z (g_code g i)) with (fun i => wt i * ln i).
  assert (WL : g_W g = Wt Lv wt) by (unfold Wt; apply (W_leaves g GG)). rewrite WL.
  assert (NK : nL Lv <= K).
  { unfold nL. rewrite <- HK. change 19%nat with (Z.to_nat 19). rewrite (reindex z 19 7 F Fl TF (fun _ => 1)). clear. induction (leaves g); cbn [lsum length]; lia. }
  assert (Hw : forall i, In i Lv -> 1 <= wt i) by (intros i Hi; apply Lv_in in Hi; destruct Hi as [P L]; exact (go_wt_leaf g GG i P L)).
  assert (D12 : forall i, In i Lv -> 1 <= dp i <= 12).
  { intros i Hi. apply Lv_in in Hi. destruct Hi as [P L]. split.
    - apply (depth_pos g GG). destruct (Z.eq_dec i (g_lo g)) as [->|N]; [rewrite (root_internal g GG) in L; discriminate | lia].
    - apply (depth_le_of_W z 19 7 F Fl TF 12); [exact HW | lia | exact P | exact L]. }
  assert (L7 : forall i, In i Lv -> 1 <= ln i <= 7).
  { intros i Hi. apply Lv_in in Hi. destruct Hi as [P L]. rewrite <- ML7. apply (zo_len_used z ZOK (g_code g i) i). split; [exact P | split; [exact L | reflexivity]]. }
  destruct (existsb (fun i => 7 <? dp i) Lv) eqn:OVF.
  -
    apply existsb_exists in OVF. destruct OVF as (i0 & Hi0 & D0). apply Z.ltb_lt in D0. apply Lv_in in Hi0. destruct Hi0 as [P0 L0].
    assert (OV : exists i, g_pos (zt_g z) i /\ g_leaf (zt_g z) i = true /\ zt_ML z < g_depth (zt_g z) i) by (exists i0; rewrite ML7; auto).
    refine (damage_cert Lv wt dp ln Hw D12 ltac:(intros i Hi; pose proof (L7 i Hi); lia) _ _ _ K rnum rden C _ _ _ NK).
    + intros i j Hi Hj Hij. apply Lv_in in Hi. apply Lv_in in Hj. destruct Hi as [Pi Li], Hj as [Pj Lj]. exact (mono g GG i j Pi Li Pj Lj Hij).
    + intros i j Hi Hj Hij. apply Lv_in in Hi. apply Lv_in in Hj. destruct Hi as [Pi Li], Hj as [Pj Lj]. exact (zo_len_rank z ZOK OV i j Pi Pj Li Lj Hij).
    + intros i Hi. apply Lv_in in Hi. destruct Hi as [Pi Li]. unfold Wt. rewrite <- (W_leaves g GG). pose proof (fib_bound g GG i Pi). lia.
    + intros i Hi. pose proof (L7 i Hi). lia.
    +
      intros b Hb. rewrite <- (g_hist_cnt ln b). unfold ln. rewrite (zo_len_hist z ZOK b) by (rewrite ML7; exact Hb). rewrite ML7.
      apply d_repair_ext. intros x. rewrite (g_hist_cnt (fun i => Z.min (g_depth g i) 7) x). unfold capf, hd.
      destruct (Z.ltb_spec x 1).
      { unfold cnt. etransitivity; [apply lsum_ext; intros i Hi; replace (Z.min (g_depth g i) 7 =? x) with false by (symmetry; apply Z.eqb_neq; pose proof (D12 i Hi); lia); reflexivity | apply lsum_zero]. }
      destruct (Z.ltb_spec x 7).
      { apply cnt_ext. intros i Hi. pose proof (D12 i Hi). destruct (Z.eqb_spec (Z.min (g_depth g i) 7) x), (Z.eqb_spec (g_depth g i) x); try reflexivity; lia. }
      destruct (Z.eqb_spec x 7).
      { subst x. pose proof (cv_cum Lv dp 13 D12 ltac:(lia)) as E13. pose proof (cv_cum Lv dp 7 D12 ltac:(lia)) as E7.
        change (Z.to_nat (13 - 1)) with (6 + 6)%nat in E13. rewrite zsum_split in E13. change (Z.to_nat (7 - 1)) with 6%nat in E7. change (1 + Z.of_nat 6) with 7 in E13.
        rewrite <- E7 in E13. unfold cv in E13, E7 |- *.
        assert (A : cnt (fun i => dp i <? 13) Lv = cnt (fun i => dp i <? 7) Lv + cnt (fun i => Z.min (g_depth g i) 7 =? 7) Lv); [| lia].
        rewrite (cnt_split (fun i => dp i <? 13) (fun i => dp i <? 7) Lv). f_equal; apply cnt_ext; intros i Hi; pose proof (D12 i Hi);
          destruct (Z.ltb_spec (g_depth g i) 13), (Z.ltb_spec (g_depth g i) 7); cbn [andb negb]; try lia;
          first [reflexivity | symmetry; apply Z.eqb_neq; lia | symmetry; apply Z.eqb_eq; lia]. }
      unfold cnt. etransitivity; [apply lsum_ext; intros i Hi; replace (Z.min (g_depth g i) 7 =? x) with false by (symmetry; apply Z.eqb_neq; pose proof (D12 i Hi); lia); reflexivity | apply lsum_zero].
    + exact (kraft_eq g GG 12 ltac:(intros i P L; apply (D12 i); apply Lv_in; auto)).
  -
    assert (NOV : forall j, g_pos g j -> g_leaf g j = true -> g_depth g j <= zt_ML z).
    { intros j Pj Lj. rewrite ML7. destruct (Z_lt_le_dec 7 (g_depth (zt_g z) j)) as [D7|D7]; [|exact D7]. exfalso.
      apply Bool.not_true_iff_false in OVF. apply OVF. apply existsb_exists. exists j. split; [apply Lv_in; auto | apply Z.ltb_lt; exact D7]. }
    assert (EQ : lsum (fun i => wt i * ln i) Lv = lsum (fun i => wt i * dp i) Lv).
    { apply lsum_ext. intros i Hi. unfold ln. apply Lv_in in Hi. destruct Hi as [P L].
      rewrite (zo_len_noovf z ZOK NOV (g_code g i) i); [reflexivity | split; [exact P | split; [exact L | reflexivity]]]. }
    rewrite EQ. pose proof (Wt_nonneg Lv wt Hw). nia.
Qed.
End Tree.

Theorem bl_damage (z : ztree) (F : Z -> Z) (Fl : list Z) (K rnum rden : Z) :
  tree_facts z 19 7 F Fl ->
  dmg_cert K rnum rden = true ->
  g_W (zt_g z) < fib 14 ->
  zsum (fun x => if ffreq F Fl x =? 0 then 0 else 1) 0 19 <= K ->
  rden * zsum (fun x => ffreq F Fl x * zt_len z x) 0 19
  <= rden * zsum (fun x => ffreq F Fl x * tdepth z x) 0 19 + rnum * g_W (zt_g z).
Proof. intros TF C HW HK. exact (bl_damage_tree z F Fl TF K rnum rden C HW HK). Qed.

Lemma dmg_cert_13 : dmg_cert 13 3 8 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma dmg_cert_19 : dmg_cert 19 1 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End OverlayDamage.

Module OverlayRowsOk.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayHuff4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRows.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayFacts.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayTrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require OverlayRows.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayRows.OverlayRuns.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayDamage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition WL (b : oblock) : Z := lsum (fL b) (zrange 0 286).
Definition WD (b : oblock) : Z := vP b + Z.of_nat (length (ob_forced b)).
Definition rho_of (LL : Z) : Z * Z := if LL <=? 9 then (3, 8) else (1, 1).
Definition Kbl_of (LL : Z) : Z := if LL <=? 9 then 13 else 19.

Definition n1_of (b : oblock) : Z := countZ (fun c => usedLb b c && (ob_lenL b c =? 1)) (zrange 0 286).
Definition d1_of (b : oblock) : Z :=
  fold_right (fun c m => if fL b c =? 1 then Z.min (ob_lenL b c) m else m) (ob_lenL b 256) (zrange 0 286).

Record prm_ok (prm : oprm) (lbs : Z) (b : oblock) : Prop := {
  po_lbs : p_lbs prm = lbs;
  po_LL : 1 <= p_LL prm <= 15 /\ lbs + 1 < fib (p_LL prm + 3);
  po_blc : p_blc prm = (if p_LL prm <=? 14 then 18 else 19);
  po_d1 : p_d1 prm = d1_of b;
  po_n1 : p_n1 prm = n1_of b;
  po_rho : (p_rnum prm, p_rden prm) = rho_of (p_LL prm);
  po_dmg : dmg_cert (Kbl_of (p_LL prm)) (fst (rho_of (p_LL prm))) (snd (rho_of (p_LL prm))) = true
}.


Lemma oeval_app b l1 l2 : oeval b (l1 ++ l2) = oeval b l1 + oeval b l2.
Proof. induction l1 as [|[v a] r IH]; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma oeval_scale b c l : oeval b (scale c l) = c * oeval b l.
Proof. unfold scale. induction l as [|[v a] r IH]; [cbn; lia|]. cbn [map oeval]. rewrite IH. lia. Qed.

Lemma oeval_cat {A} b (f : A -> list (ovar * Z)) (L : list A) :
  oeval b (cat (map f L)) = fold_right (fun i acc => oeval b (f i) + acc) 0 L.
Proof. induction L as [|i r IH]; cbn; [reflexivity|]. unfold cat in *. cbn. rewrite oeval_app, IH. reflexivity. Qed.

Fixpoint gsum {A} (f : A -> Z) (L : list A) : Z := match L with [] => 0 | i :: r => f i + gsum f r end.
Lemma oeval_catg {A} b (f : A -> list (ovar * Z)) (L : list A) : oeval b (cat (map f L)) = gsum (fun i => oeval b (f i)) L.
Proof. rewrite oeval_cat. induction L; cbn; [reflexivity|]. rewrite IHL. reflexivity. Qed.
Lemma gsum_lsum f L : gsum f L = lsum f L.
Proof. induction L; cbn; [reflexivity|]. rewrite IHL. reflexivity. Qed.
Lemma gsum_ext {A} (f g : A -> Z) L : (forall i, In i L -> f i = g i) -> gsum f L = gsum g L.
Proof. induction L; cbn; intros; [reflexivity|]. rewrite H, IHL; auto. Qed.
Lemma gsum_add {A} (f g : A -> Z) L : gsum (fun i => f i + g i) L = gsum f L + gsum g L.
Proof. induction L; cbn; [reflexivity|]. rewrite IHL. lia. Qed.
Lemma gsum_scale {A} c (f : A -> Z) L : gsum (fun i => c * f i) L = c * gsum f L.
Proof. induction L; cbn; [lia|]. rewrite IHL. lia. Qed.
Lemma gsum_le {A} (f g : A -> Z) L : (forall i, In i L -> f i <= g i) -> gsum f L <= gsum g L.
Proof. induction L; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHL ltac:(intros; apply H; auto)). lia. Qed.
Lemma gsum_nonneg {A} (f : A -> Z) L : (forall i, In i L -> 0 <= f i) -> 0 <= gsum f L.
Proof. induction L; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHL ltac:(intros; apply H; auto)). lia. Qed.
Lemma gsum_const0 {A} (L : list A) : gsum (fun _ => 0) L = 0.
Proof. induction L; cbn; lia. Qed.
Lemma gsum_app {A} (f : A -> Z) L1 L2 : gsum f (L1 ++ L2) = gsum f L1 + gsum f L2.
Proof. induction L1; cbn; [reflexivity|]. rewrite IHL1. lia. Qed.
Lemma gsum_map {A B} (f : B -> Z) (g : A -> B) L : gsum f (map g L) = gsum (fun i => f (g i)) L.
Proof. induction L; cbn; [reflexivity|]. rewrite IHL. reflexivity. Qed.
Lemma gsum_swap {A B} (F : A -> B -> Z) LA LB : gsum (fun a => gsum (fun c => F a c) LB) LA = gsum (fun c => gsum (fun a => F a c) LA) LB.
Proof.
  induction LA as [|a r IH]; cbn.
  - induction LB; cbn; [reflexivity|lia].
  - rewrite IH. rewrite <- gsum_add. reflexivity.
Qed.
Lemma gsum_pick (f : Z -> Z) (L : list Z) (v : Z) : NoDup L -> In v L ->
  gsum (fun l => if l =? v then f l else 0) L = f v.
Proof.
  intros ND I. rewrite gsum_lsum.
  rewrite (lsum_ext _ (fun l => if l =? v then f v else 0)) by (intros l _; destruct (Z.eqb_spec l v); [subst; reflexivity|reflexivity]).
  destruct (lsum_in_split L v I ND) as (l1 & l2 & E & N1 & N2). rewrite E, lsum_app. cbn. rewrite Z.eqb_refl.
  rewrite (lsum_ext _ (fun _ => 0) l1) by (intros l Hl; destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]).
  rewrite (lsum_ext _ (fun _ => 0) l2) by (intros l Hl; destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]).
  rewrite !lsum_zero. lia.
Qed.
Lemma gsum_miss (f : Z -> Z) (L : list Z) (v : Z) : ~ In v L -> gsum (fun l => if l =? v then f l else 0) L = 0.
Proof. intros N. rewrite gsum_lsum. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros l Hl. destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]. Qed.

Lemma zrange_in lo n x : In x (zrange lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
  unfold zrange. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma zrange_length lo n : length (zrange lo n) = n.
Proof. unfold zrange. rewrite length_map, length_seq. reflexivity. Qed.
Lemma zrange_nodup lo n : NoDup (zrange lo n).
Proof. unfold zrange. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia. Qed.
Lemma ks_in n k : In k (ks n) <-> (k < n)%nat.
Proof. unfold ks. rewrite in_seq. lia. Qed.


Lemma classesL_concat : cat (map (fun k => lc_codes (lcl k)) (ks nLC)) = zrange 0 286.
Proof. vm_compute. reflexivity. Qed.
Lemma classesD_concat : cat (map (fun k => dc_codes (dcl k)) (ks nDC)) = zrange 0 30.
Proof. vm_compute. reflexivity. Qed.
Lemma classesLit_concat : cat (map (fun k => if is_lit k then lc_codes (lcl k) else []) (ks nLC)) = zrange 0 256.
Proof. vm_compute. reflexivity. Qed.
Lemma classesLen_concat : cat (map (fun k => if is_len k then lc_codes (lcl k) else []) (ks nLC)) = zrange 257 29.
Proof. vm_compute. reflexivity. Qed.
Lemma classesEob : forall k, (k < nLC)%nat -> is_eob k = true -> lc_codes (lcl k) = [256].
Proof. intros k Hk E. unfold nLC in Hk. do 11 (destruct k as [|k]; [first [reflexivity | discriminate] |]). lia. Qed.
Lemma classL_SL : forall k c, (k < nLC)%nat -> In c (lc_codes (lcl k)) -> lc_SL (lcl k) = sl_of_code c /\ (is_len k = true -> lc_xl (lcl k) = xl_of_lcode c) /\ 0 <= c < 286
  /\ (is_lit k = true <-> c < 256) /\ (is_len k = true <-> 257 <= c) /\ (is_eob k = true <-> c = 256).
Proof.
  intros k c Hk. unfold nLC in Hk. do 11 (destruct k as [|k]; [cbn; intros H; repeat (destruct H as [<-|H]; [vm_compute; intuition (congruence || lia)|]); destruct H |]). lia.
Qed.
Lemma classD_xd : forall k d, (k < nDC)%nat -> In d (dc_codes (dcl k)) -> dc_xd (dcl k) = xd_of_dcode d /\ 0 <= d < 30 /\ ((k = 0)%nat <-> d <= 3).
Proof.
  intros k d Hk. unfold nDC in Hk. do 14 (destruct k as [|k]; [cbn; intros H; repeat (destruct H as [<-|H]; [vm_compute; intuition (congruence || lia)|]); destruct H |]). lia.
Qed.

Lemma gsum_classesL (f : Z -> Z) : gsum (fun k => lsum f (lc_codes (lcl k))) (ks nLC) = lsum f (zrange 0 286).
Proof. rewrite <- classesL_concat. unfold cat. generalize (ks nLC). induction l; cbn [gsum concat map]; [reflexivity|]. rewrite lsum_app, IHl. reflexivity. Qed.
Lemma gsum_classesD (f : Z -> Z) : gsum (fun k => lsum f (dc_codes (dcl k))) (ks nDC) = lsum f (zrange 0 30).
Proof. rewrite <- classesD_concat. unfold cat. generalize (ks nDC). induction l; cbn [gsum concat map]; [reflexivity|]. rewrite lsum_app, IHl. reflexivity. Qed.
Lemma gsum_classesLit (f : Z -> Z) : gsum (fun k => if is_lit k then lsum f (lc_codes (lcl k)) else 0) (ks nLC) = lsum f (zrange 0 256).
Proof.
  rewrite <- classesLit_concat. unfold cat. generalize (ks nLC). induction l; cbn [gsum concat map]; [reflexivity|].
  rewrite lsum_app, IHl. destruct (is_lit a); reflexivity.
Qed.
Lemma gsum_classesLen (f : Z -> Z) : gsum (fun k => if is_len k then lsum f (lc_codes (lcl k)) else 0) (ks nLC) = lsum f (zrange 257 29).
Proof.
  rewrite <- classesLen_concat. unfold cat. generalize (ks nLC). induction l; cbn [gsum concat map]; [reflexivity|].
  rewrite lsum_app, IHl. destruct (is_len a); reflexivity.
Qed.


Lemma scount_nonneg (P : osym -> bool) l : 0 <= scount P l.
Proof. unfold scount. induction l; cbn; [lia|]. destruct (P a); lia. Qed.
Lemma scount_le_len (P : osym -> bool) l : scount P l <= Z.of_nat (length l).
Proof. unfold scount. induction l; cbn; [lia|]. destruct (P a); lia. Qed.
Lemma ssum_ext f g l : (forall s, In s l -> f s = g s) -> ssum f l = ssum g l.
Proof. induction l; cbn; intros; [reflexivity|]. rewrite H, IHl; auto. Qed.
Lemma ssum_add f g l : ssum (fun s => f s + g s) l = ssum f l + ssum g l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. lia. Qed.
Lemma ssum_le f g l : (forall s, In s l -> f s <= g s) -> ssum f l <= ssum g l.
Proof. induction l; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHl ltac:(intros; apply H; auto)). lia. Qed.
Lemma ssum_scount (P : osym -> bool) (l : list osym) : ssum (fun s => if P s then 1 else 0) l = scount P l.
Proof. reflexivity. Qed.
Lemma lsum_scount (key : osym -> Z) (w : Z -> Z) (S : list Z) (l : list osym) : NoDup S ->
  lsum (fun c => w c * scount (fun s => key s =? c) l) S = ssum (fun s => if existsb (Z.eqb (key s)) S then w (key s) else 0) l.
Proof.
  intros ND. induction l as [|s r IH]; cbn.
  - unfold scount; cbn. induction S; cbn; [reflexivity|]. inversion ND; subst. rewrite IHS; [lia|assumption].
  - unfold scount in *. cbn.
    rewrite (lsum_ext (fun c => w c * ((if key s =? c then 1 else 0) + ssum (fun s0 => if key s0 =? c then 1 else 0) r))
                      (fun c => (if c =? key s then w c else 0) + w c * ssum (fun s0 => if key s0 =? c then 1 else 0) r))
      by (intros c _; rewrite (Z.eqb_sym (key s) c); destruct (c =? key s); lia).
    rewrite lsum_add, IH. rewrite <- gsum_lsum.
    destruct (in_dec Z.eq_dec (key s) S) as [I|NI].
    + rewrite (gsum_pick w S (key s) ND I). replace (existsb (Z.eqb (key s)) S) with true; [lia|].
      symmetry. apply existsb_exists. exists (key s). rewrite Z.eqb_refl. auto.
    + rewrite (gsum_miss w S (key s) NI). replace (existsb (Z.eqb (key s)) S) with false; [lia|].
      symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists. intros (x & Ix & Ex). apply Z.eqb_eq in Ex. subst. tauto.
Qed.

Definition keyL (s : osym) : Z := match s with OLit c => c | OPair lc _ => lc end.
Definition keyD (s : osym) : Z := match s with OLit _ => -1 | OPair _ dc => dc end.

Lemma lsum_sublist (g : Z -> Z) (S F : list Z) : NoDup S -> NoDup F -> (forall x, In x F -> In x S) ->
  lsum (fun d => if existsb (Z.eqb d) F then g d else 0) S = lsum g F.
Proof.
  intros NS. induction F as [|x F IH]; intros NF SUB.
  - cbn. etransitivity; [apply (lsum_ext _ (fun _ => 0)); intros; reflexivity | apply lsum_zero].
  - inversion NF; subst.
    rewrite (lsum_ext _ (fun d => (if d =? x then g d else 0) + (if existsb (Z.eqb d) F then g d else 0))).
    2:{ intros d _. cbn. destruct (Z.eqb_spec d x); cbn; [|reflexivity]. subst.
        replace (existsb (Z.eqb x) F) with false; [lia|]. symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists.
        intros (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. tauto. }
    rewrite lsum_add, IH; [|assumption|intros; apply SUB; right; assumption].
    rewrite <- gsum_lsum, (gsum_pick g S x NS); [cbn [gsum lsum]; rewrite ?gsum_lsum; lia|]. apply SUB. left. reflexivity.
Qed.
Lemma countZ_le_len (Q : Z -> bool) S : countZ Q S <= Z.of_nat (length S).
Proof. unfold countZ. induction S; cbn; [lia|]. destruct (Q a); lia. Qed.
Lemma countZ_nonneg (Q : Z -> bool) S : 0 <= countZ Q S.
Proof. unfold countZ. apply lsum_nonneg. intros; destruct (Q x); lia. Qed.
Lemma Forall_map_iff {A B} (P : B -> Prop) (f : A -> B) (L : list A) : (forall i, In i L -> P (f i)) -> Forall P (map f L).
Proof. intros H. apply Forall_forall. intros y Iy. apply in_map_iff in Iy. destruct Iy as (i & <- & Ii). auto. Qed.
Lemma Forall_cat {A} (P : A -> Prop) (L : list (list A)) : (forall l, In l L -> Forall P l) -> Forall P (cat L).
Proof. intros H. unfold cat. apply Forall_forall. intros x Ix. apply in_concat in Ix. destruct Ix as (l & Il & Ix). pose proof (H l Il). rewrite Forall_forall in H0. auto. Qed.
Lemma Forall_app2 {A} (P : A -> Prop) l1 l2 : Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. intros. apply Forall_app. auto. Qed.

Section Sound.
Variable b : oblock.
Variable lbs : Z.
Hypothesis OK : oblock_ok b lbs.
Notation lenL := (ob_lenL b).
Notation lenD := (ob_lenD b).
Notation BC := (ob_BC b).
Notation BD := (ob_BD b).
Notation syms := (ob_syms b).

Lemma sym_ok_in s : In s syms -> sym_ok s.
Proof. intros I. pose proof (ok_syms b lbs OK) as F. rewrite Forall_forall in F. apply F. exact I. Qed.

Lemma fL_eq c : fL b c = scount (fun s => keyL s =? c) syms + (if c =? 256 then 1 else 0).
Proof.
  unfold fL. f_equal. unfold scount. apply ssum_ext. intros s I. destruct s; reflexivity.
Qed.
Lemma gD_eq d : 0 <= d -> gD b d = scount (fun s => keyD s =? d) syms.
Proof.
  intros Hd. unfold gD, scount. apply ssum_ext. intros s I. destruct s as [c|lc dc]; [|reflexivity]. cbn [keyD].
  replace (-1 =? d) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
Lemma fL_nonneg c : 0 <= fL b c.
Proof. unfold fL. pose proof (scount_nonneg (fun s => match s with OLit c' => c' =? c | OPair lc _ => lc =? c end) syms). destruct (c =? 256); lia. Qed.
Lemma gD_nonneg d : 0 <= gD b d.
Proof. unfold gD. apply scount_nonneg. Qed.
Lemma fL_256 : fL b 256 = 1.
Proof.
  rewrite fL_eq. rewrite Z.eqb_refl.
  enough (scount (fun s => keyL s =? 256) syms = 0) by lia.
  unfold scount. rewrite (ssum_ext _ (fun _ => 0)); [generalize (ob_syms b); intros l; induction l; cbn; lia|].
  intros s I. pose proof (sym_ok_in s I). destruct s as [c'|lc dc]; cbn [keyL sym_ok] in *;
    [destruct (Z.eqb_spec c' 256) | destruct (Z.eqb_spec lc 256)]; try reflexivity; lia.
Qed.
Lemma fL_out c : ~ (0 <= c < 256 \/ 257 <= c <= 285) -> c <> 256 -> fL b c = 0.
Proof.
  intros H1 H2. rewrite fL_eq. replace (c =? 256) with false by (symmetry; apply Z.eqb_neq; auto).
  unfold scount. rewrite (ssum_ext _ (fun _ => 0)); [generalize (ob_syms b); intros l; induction l; cbn; lia|].
  intros s I. pose proof (sym_ok_in s I). destruct s as [c'|lc dc]; cbn [keyL sym_ok] in *;
    [destruct (Z.eqb_spec c' c) | destruct (Z.eqb_spec lc c)]; try reflexivity; lia.
Qed.

Lemma keyL_range s : In s syms -> (0 <= keyL s < 256 /\ exists c, s = OLit c) \/ (257 <= keyL s <= 285 /\ exists lc dc, s = OPair lc dc /\ 0 <= dc <= 29).
Proof. intros I. pose proof (sym_ok_in s I). destruct s; cbn in *; [left; split; [lia|eexists; reflexivity] | right; split; [lia|do 2 eexists; split; [reflexivity|lia]]]. Qed.

Lemma lsum_fL_w (w : Z -> Z) (lo : Z) (n : nat) :
  lsum (fun c => w c * fL b c) (zrange lo n) =
  ssum (fun s => if existsb (Z.eqb (keyL s)) (zrange lo n) then w (keyL s) else 0) syms
  + (if existsb (Z.eqb 256) (zrange lo n) then w 256 else 0).
Proof.
  rewrite (lsum_ext _ (fun c => w c * scount (fun s => keyL s =? c) syms + (if c =? 256 then w c else 0))) by (intros c _; rewrite fL_eq; destruct (c =? 256); lia).
  rewrite lsum_add, (lsum_scount keyL w) by apply zrange_nodup. f_equal.
  rewrite <- gsum_lsum. destruct (in_dec Z.eq_dec 256 (zrange lo n)) as [I|NI].
  - rewrite (gsum_pick w _ 256 (zrange_nodup lo n) I). replace (existsb (Z.eqb 256) (zrange lo n)) with true; [reflexivity|].
    symmetry. apply existsb_exists. exists 256. split; [exact I|reflexivity].
  - rewrite (gsum_miss w _ 256 NI). replace (existsb (Z.eqb 256) (zrange lo n)) with false; [reflexivity|].
    symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists. intros (x & Ix & Ex). apply Z.eqb_eq in Ex. subst. tauto.
Qed.
Lemma existsb_zrange x lo n : existsb (Z.eqb x) (zrange lo n) = ((lo <=? x) && (x <? lo + Z.of_nat n)).
Proof.
  destruct (existsb (Z.eqb x) (zrange lo n)) eqn:E.
  - apply existsb_exists in E. destruct E as (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. apply zrange_in in Iy. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
  - symmetry. apply Bool.not_true_iff_false. intros H. apply Bool.not_true_iff_false in E. apply E. apply existsb_exists. exists x. rewrite Z.eqb_refl. split; [|reflexivity].
    apply zrange_in. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma lsum_gD_w (w : Z -> Z) : lsum (fun d => w d * gD b d) (zrange 0 30) = ssum (fun s => match s with OPair _ dc => w dc | _ => 0 end) syms.
Proof.
  rewrite (lsum_ext _ (fun d => w d * scount (fun s => keyD s =? d) syms)) by (intros d Id; apply zrange_in in Id; rewrite gD_eq by lia; reflexivity).
  rewrite (lsum_scount keyD w) by apply zrange_nodup. apply ssum_ext. intros s I.
  rewrite existsb_zrange. destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyD keyL] in *.
  - reflexivity.
  - replace ((0 <=? dc) && (dc <? 0 + Z.of_nat 30)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma vP_eq : vP b = ssum (fun s => match s with OPair _ _ => 1 | _ => 0 end) syms.
Proof. unfold vP, scount. apply ssum_ext. intros s _. destruct s; reflexivity. Qed.
Lemma vNLIT_eq : vNLIT b = ssum (fun s => match s with OLit _ => 1 | _ => 0 end) syms.
Proof. unfold vNLIT, scount. apply ssum_ext. intros s _. destruct s; reflexivity. Qed.


Lemma WL_eq : WL b = NSYM b + 1.
Proof.
  unfold WL.
  rewrite (lsum_ext (fL b) (fun c => 1 * scount (fun s => keyL s =? c) syms + (if c =? 256 then 1 else 0)) (zrange 0 286)) by (intros; rewrite fL_eq; lia).
  rewrite lsum_add. rewrite (lsum_scount keyL (fun _ => 1)) by apply zrange_nodup.
  rewrite <- gsum_lsum, (gsum_pick (fun _ => 1) _ 256 (zrange_nodup 0 286)) by (apply zrange_in; lia).
  unfold NSYM. enough (ssum (fun s => if existsb (Z.eqb (keyL s)) (zrange 0 286) then 1 else 0) syms = Z.of_nat (length syms)) by lia.
  rewrite (ssum_ext _ (fun _ => 1)); [generalize (ob_syms b); intros l; induction l; [reflexivity|cbn [ssum length]; rewrite Nat2Z.inj_succ; lia]|].
  intros s I. pose proof (sym_ok_in s I).
  replace (existsb (Z.eqb (keyL s)) (zrange 0 286)) with true; [reflexivity|]. symmetry. apply existsb_exists.
  exists (keyL s). rewrite Z.eqb_refl. split; [|reflexivity]. apply zrange_in. destruct s; cbn in *; lia.
Qed.
Lemma zrange_rangeZ lo n : zrange lo n = rangeZ lo n.
Proof.
  unfold zrange. revert lo. induction n as [|n IH]; intros lo; [reflexivity|].
  cbn [seq map rangeZ]. f_equal; [lia|]. rewrite <- seq_shift, map_map. rewrite <- (IH (lo + 1)). apply map_ext. intros; lia.
Qed.
Lemma lsum_zrange f lo n : lsum f (zrange lo n) = zsum f lo n.
Proof. rewrite zrange_rangeZ. apply lsum_zsum. Qed.
Lemma countZ_zsum (P : Z -> bool) lo n : countZ P (zrange lo n) = zsum (fun c => if P c then 1 else 0) lo n.
Proof. unfold countZ. apply lsum_zrange. Qed.
Lemma ffreq_nil F c : ffreq F [] c = F c. Proof. reflexivity. Qed.
Lemma TL_W zL : tree_facts zL 286 15 (fL b) [] -> g_W (zt_g zL) = NSYM b + 1.
Proof.
  intros TF. rewrite <- (sumW zL 286 15 (fL b) [] TF). change (Z.to_nat 286) with 286%nat.
  rewrite <- lsum_zrange. rewrite <- WL_eq. unfold WL. apply lsum_ext. intros; reflexivity.
Qed.
Lemma lenL_used c : 0 <= c < 286 -> 0 < fL b c -> 1 <= lenL c <= 15.
Proof.
  intros Hc U. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). rewrite EL by lia.
  apply (tlen_used zL 286 15 (fL b) [] TF c Hc). rewrite ffreq_nil. lia.
Qed.
Lemma lenL_unused c : 0 <= c < 286 -> fL b c = 0 -> lenL c = 0.
Proof.
  intros Hc U. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). rewrite EL by lia.
  apply (tlen_unused zL 286 15 (fL b) [] TF c Hc). rewrite ffreq_nil. exact U.
Qed.
Lemma forced_facts : NoDup (ob_forced b) /\ (length (ob_forced b) <= 2)%nat /\ (forall d, In d (ob_forced b) -> 0 <= d <= 2 /\ gD b d = 0).
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & _). destruct (tFl zD 30 15 (gD b) (ob_forced b) TF) as (A & B & C).
  split; [exact B|]. split; [exact A|]. intros d Hd. destruct (C d Hd) as (X & Y & W). lia.
Qed.
Lemma forcedD_spec d : forcedD b d = true <-> In d (ob_forced b).
Proof. unfold forcedD. apply existsb_In. Qed.
Lemma ffreqD d : ffreq (gD b) (ob_forced b) d = (if forcedD b d then 1 else gD b d).
Proof. reflexivity. Qed.
Lemma usedDb_W d : usedDb b d = true <-> ffreq (gD b) (ob_forced b) d <> 0.
Proof.
  rewrite ffreqD. unfold usedDb. pose proof (gD_nonneg d). rewrite Bool.orb_true_iff, Z.ltb_lt.
  destruct (forcedD b d); split.
  - intros; lia.
  - intros; right; reflexivity.
  - intros [X|X]; [lia|discriminate].
  - intros; left; lia.
Qed.
Lemma sum_gD : lsum (gD b) (zrange 0 30) = vP b.
Proof.
  rewrite vP_eq, <- (lsum_gD_w (fun _ => 1)). apply lsum_ext. intros; lia.
Qed.
Lemma TD_W zD : tree_facts zD 30 15 (gD b) (ob_forced b) -> g_W (zt_g zD) = WD b.
Proof.
  intros TF. rewrite <- (sumW zD 30 15 (gD b) (ob_forced b) TF). rewrite (sumW_F zD 30 15 (gD b) (ob_forced b) TF).
  change (Z.to_nat 30) with 30%nat. rewrite <- lsum_zrange, sum_gD. reflexivity.
Qed.
Lemma WD_le : WD b <= lbs + 1.
Proof.
  unfold WD. destruct forced_facts as (_ & LF & _). unfold vP.
  pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). pose proof (ok_N b _ OK). unfold NSYM in *. lia.
Qed.
Lemma lenD_used d : 0 <= d < 30 -> usedDb b d = true -> 1 <= lenD d <= 15.
Proof.
  intros Hd U. destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). rewrite EL by lia.
  apply (tlen_used zD 30 15 (gD b) (ob_forced b) TF d Hd). apply usedDb_W. exact U.
Qed.
Lemma lenD_unused d : 0 <= d < 30 -> usedDb b d = false -> lenD d = 0.
Proof.
  intros Hd U. destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). rewrite EL by lia.
  apply (tlen_unused zD 30 15 (gD b) (ob_forced b) TF d Hd).
  destruct (Z.eq_dec (ffreq (gD b) (ob_forced b) d) 0); [assumption|]. apply usedDb_W in n. congruence.
Qed.
Lemma D2 : 2 <= vV b.
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). pose proof (tused_two zD 30 15 (gD b) (ob_forced b) TF) as T.
  change (Z.to_nat 30) with 30%nat in T. unfold vV. destruct forced_facts as (ND & _ & FF).
  rewrite countZ_zsum.
  rewrite (zsum_ext _ (fun d => (if 0 <? gD b d then 1 else 0) + (if existsb (Z.eqb d) (ob_forced b) then 1 else 0))) in T.
  2:{ intros d Hd. rewrite ffreqD. unfold forcedD. pose proof (gD_nonneg d).
      destruct (existsb (Z.eqb d) (ob_forced b)) eqn:X.
      - apply existsb_In in X. destruct (FF d X). replace (0 <? gD b d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      - destruct (Z.ltb_spec 0 (gD b d)); destruct (Z.eqb_spec (gD b d) 0); lia. }
  rewrite zsum_add in T. rewrite <- (lsum_zrange (fun d => if existsb (Z.eqb d) (ob_forced b) then 1 else 0)) in T.
  rewrite (lsum_support (fun _ => 1) (zrange 0 30) (ob_forced b) (zrange_nodup 0 30) ND) in T.
  2:{ intros x Hx. apply zrange_in. destruct (FF x Hx). lia. }
  replace (lsum (fun _ => 1) (ob_forced b)) with (Z.of_nat (length (ob_forced b))) in T; [lia|].
  generalize (ob_forced b). intros l. induction l; [reflexivity|]. cbn [lsum length]. lia.
Qed.
Lemma bforced_facts : NoDup (ob_bforced b) /\ (length (ob_bforced b) <= 2)%nat /\ (forall x, In x (ob_bforced b) -> 0 <= x < 19 /\ BC x = 0).
Proof.
  destruct (ok_TB b lbs OK) as (zB & TF & _ & _). destruct (tFl zB 19 7 BC (ob_bforced b) TF) as (A & B & C).
  split; [exact B|]. split; [exact A|]. intros x Hx. destruct (C x Hx) as (X & Y & W). lia.
Qed.
Lemma BC'_eq x : BC' b x = BC x + (if existsb (Z.eqb x) (ob_bforced b) then 1 else 0).
Proof.
  unfold BC', ffreq. destruct (existsb (Z.eqb x) (ob_bforced b)) eqn:X; [|lia].
  apply existsb_In in X. destruct bforced_facts as (_ & _ & C). destruct (C x X). lia.
Qed.
Lemma BC_nonneg x : 0 <= x < 19 -> 0 <= BC x.
Proof.
  intros Hx. destruct (ok_TB b lbs OK) as (zB & TF & _ & _).
  pose proof (W_nonneg zB 19 7 BC (ob_bforced b) TF x Hx) as P. fold (BC' b) in P. rewrite BC'_eq in P.
  destruct (existsb (Z.eqb x) (ob_bforced b)) eqn:X; [|lia].
  apply existsb_In in X. destruct bforced_facts as (_ & _ & C). destruct (C x X). lia.
Qed.
Lemma BC'_nonneg x : 0 <= x < 19 -> 0 <= BC' b x.
Proof. intros Hx. rewrite BC'_eq. pose proof (BC_nonneg x Hx). destruct (existsb _ _); lia. Qed.
Lemma BC_le_BC' x : BC x <= BC' b x.
Proof. rewrite BC'_eq. destruct (existsb _ _); lia. Qed.
Lemma BD_range x : 0 <= x < 19 -> 0 <= BD x <= 7.
Proof.
  intros Hx. destruct (ok_TB b lbs OK) as (zB & TF & _ & EB). rewrite EB by lia.
  destruct (Z.eq_dec (BC' b x) 0) as [Z0|NZ].
  - rewrite (tlen_unused zB 19 7 BC (ob_bforced b) TF x Hx Z0). lia.
  - pose proof (tlen_used zB 19 7 BC (ob_bforced b) TF x Hx NZ). lia.
Qed.
Lemma BD_unused x : 0 <= x < 19 -> BC' b x = 0 -> BD x = 0.
Proof.
  intros Hx Z0. destruct (ok_TB b lbs OK) as (zB & TF & _ & EB). rewrite EB by lia.
  exact (tlen_unused zB 19 7 BC (ob_bforced b) TF x Hx Z0).
Qed.
Lemma WB'_eq : zsum (BC' b) 0 19 = vWB b + Z.of_nat (length (ob_bforced b)).
Proof.
  destruct (ok_TB b lbs OK) as (zB & TF & _ & _). unfold vWB.
  exact (sumW_F zB 19 7 BC (ob_bforced b) TF).
Qed.
Lemma WB'_le : zsum (BC' b) 0 19 <= vWB b + 2 /\ vWB b <= 316.
Proof. rewrite WB'_eq. destruct bforced_facts as (_ & L & _). pose proof (ok_WB b lbs OK). unfold vWB. lia. Qed.
Lemma d1_of_le c : In c (zrange 0 286) -> fL b c = 1 -> d1_of b <= lenL c.
Proof.
  unfold d1_of. generalize (zrange 0 286). intros S. induction S as [|x S IH]; cbn; intros I F; [destruct I|].
  destruct I as [->|I].
  - rewrite F, Z.eqb_refl. lia.
  - specialize (IH I F). destruct (fL b x =? 1); lia.
Qed.
Lemma d1_of_attained : exists c, In c (zrange 0 286) /\ fL b c = 1 /\ lenL c = d1_of b.
Proof.
  unfold d1_of.
  assert (G : forall S, (exists c, In c S /\ fL b c = 1 /\ lenL c = fold_right (fun c m => if fL b c =? 1 then Z.min (lenL c) m else m) (lenL 256) S)
                      \/ fold_right (fun c m => if fL b c =? 1 then Z.min (lenL c) m else m) (lenL 256) S = lenL 256).
  { induction S as [|x S IH]; cbn; [right; reflexivity|].
    destruct (Z.eqb_spec (fL b x) 1) as [F|F].
    - destruct IH as [(c & Ic & Fc & Lc)|E].
      + destruct (Z_le_gt_dec (lenL x) (fold_right (fun c m => if fL b c =? 1 then Z.min (lenL c) m else m) (lenL 256) S)).
        * left. exists x. repeat split; auto. lia.
        * left. exists c. repeat split; auto. lia.
      + rewrite E. destruct (Z_le_gt_dec (lenL x) (lenL 256)).
        * left. exists x. repeat split; auto. lia.
        * right. lia.
    - destruct IH as [(c & Ic & Fc & Lc)|E]; [left; exists c; repeat split; auto|right; exact E]. }
  destruct (G (zrange 0 286)) as [H|E]; [exact H|].
  exists 256. split; [apply zrange_in; lia|]. split; [apply fL_256|]. symmetry. exact E.
Qed.
Lemma len_le_gen L : 0 <= L -> lbs + 1 < fib (L + 3) -> fib (L + 3) <= fib 18 ->
  forall c, 0 <= c < 286 -> 0 < fL b c -> 1 <= lenL c <= L.
Proof.
  intros L0 FL F18 c Hc U. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). rewrite EL by lia.
  pose proof (TL_W zL TF) as W. pose proof (ok_N b _ OK).
  split; [pose proof (tlen_used zL 286 15 (fL b) [] TF c Hc ltac:(rewrite ffreq_nil; lia)); lia|].
  rewrite (tnoovf2 zL 286 15 (fL b) [] TF ltac:(rewrite W; change (15 + 3) with 18; lia) c Hc ltac:(rewrite ffreq_nil; lia)).
  apply (tdepth_le2 zL 286 15 (fL b) [] TF L); [rewrite W; lia|lia|lia|rewrite ffreq_nil; lia].
Qed.
Lemma d1_range L : 0 <= L -> lbs + 1 < fib (L + 3) -> fib (L + 3) <= fib 18 -> 1 <= d1_of b <= L.
Proof.
  intros L0 FL F18. destruct d1_of_attained as (c & Ic & Fc & Lc). apply zrange_in in Ic.
  pose proof (len_le_gen L L0 FL F18 c ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma n1_range : lbs + 1 < fib 18 -> 0 <= n1_of b <= 2.
Proof.
  intros F18. unfold n1_of. split; [apply countZ_nonneg|].
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). pose proof (TL_W zL TF) as W. pose proof (ok_N b _ OK).
  pose proof (tkraft2 zL 286 15 (fL b) [] TF ltac:(rewrite W; change (15 + 3) with 18; lia)) as K.
  change (Z.to_nat 286) with 286%nat in K. rewrite <- lsum_zrange in K. unfold countZ.
  enough (lsum (fun c => 2 ^ 14 * (if usedLb b c && (lenL c =? 1) then 1 else 0)) (zrange 0 286) <= 2 ^ 15) by (rewrite lsum_scale in H0; lia).
  rewrite <- K. apply lsum_le. intros c Hc. apply zrange_in in Hc. rewrite ffreq_nil. unfold usedLb. pose proof (fL_nonneg c).
  destruct (Z.ltb_spec 0 (fL b c)); destruct (Z.eqb_spec (fL b c) 0); try lia; cbn [andb]; [|lia].
  rewrite <- EL by lia. destruct (Z.eqb_spec (lenL c) 1) as [E1|NE]; [rewrite E1; lia|].
  pose proof (pow2_pos (15 - zt_len zL c)) as P. rewrite <- EL in P by lia.
  pose proof (tlen_used zL 286 15 (fL b) [] TF c ltac:(lia) ltac:(rewrite ffreq_nil; lia)) as TL1. rewrite <- EL in TL1 by lia. lia.
Qed.
Lemma d1_n1 : d1_of b = 1 -> 1 <= n1_of b.
Proof.
  intros D1. destruct d1_of_attained as (c & Ic & Fc & Lc). unfold n1_of, countZ.
  pose proof (lsum_ge_member (fun c0 => if usedLb b c0 && (lenL c0 =? 1) then 1 else 0) (zrange 0 286) c ltac:(intros y _; cbv beta; destruct (usedLb b y && (lenL y =? 1)); lia) Ic) as G.
  cbv beta in G. unfold usedLb in G at 1. rewrite Fc, Lc, D1 in G. change (if (0 <? 1) && (1 =? 1) then 1 else 0) with 1 in G. unfold n1_of, countZ. lia.
Qed.
Lemma n1_d1 : lbs + 1 < fib 18 -> n1_of b = 2 -> d1_of b = 1.
Proof.
  intros F18 N2. pose proof (d1_range 15 ltac:(lia) ltac:(change (15 + 3) with 18; lia) ltac:(change (15+3) with 18; lia)) as DR.
  enough (lenL 256 = 1) by (pose proof (d1_of_le 256 ltac:(apply zrange_in; lia) fL_256); lia).
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). pose proof (TL_W zL TF) as W. pose proof (ok_N b _ OK).
  pose proof (tkraft2 zL 286 15 (fL b) [] TF ltac:(rewrite W; change (15 + 3) with 18; lia)) as K.
  change (Z.to_nat 286) with 286%nat in K. rewrite <- lsum_zrange in K.
  set (one := fun c => if usedLb b c && (lenL c =? 1) then 1 else 0).
  set (rest := fun c => if usedLb b c && negb (lenL c =? 1) then 2 ^ (15 - lenL c) else 0).
  assert (E : forall c, In c (zrange 0 286) -> (if ffreq (fL b) [] c =? 0 then 0 else 2 ^ (15 - zt_len zL c)) = 2 ^ 14 * one c + rest c).
  { intros c Hc. apply zrange_in in Hc. rewrite ffreq_nil. unfold one, rest, usedLb. pose proof (fL_nonneg c). rewrite <- EL by lia.
    destruct (Z.ltb_spec 0 (fL b c)); destruct (Z.eqb_spec (fL b c) 0); try lia; cbn [andb negb]; [|lia].
    destruct (Z.eqb_spec (lenL c) 1) as [E1|NE]; cbn [negb]; [rewrite E1; lia|lia]. }
  rewrite (lsum_ext _ _ _ E), lsum_add, lsum_scale in K. fold (countZ (fun c => usedLb b c && (lenL c =? 1)) (zrange 0 286)) in K.
  change (lsum one (zrange 0 286)) with (n1_of b) in K. rewrite N2 in K.
  assert (R0 : forall c, In c (zrange 0 286) -> 0 <= rest c).
  { intros c Hc. apply zrange_in in Hc. unfold rest, usedLb. pose proof (fL_nonneg c).
    destruct (Z.ltb_spec 0 (fL b c)); cbn [andb]; [|lia]. destruct (negb (lenL c =? 1)); [|lia].
    pose proof (lenL_used c ltac:(lia) ltac:(lia)). apply Z.lt_le_incl, pow2_pos. lia. }
  assert (RZ : lsum rest (zrange 0 286) = 0) by (pose proof (lsum_nonneg rest (zrange 0 286) R0); lia).
  pose proof (lsum_ge_member rest (zrange 0 286) 256 R0 ltac:(apply zrange_in; lia)) as G.
  unfold rest in G at 1. unfold usedLb in G. rewrite fL_256 in G. cbn [Z.ltb andb] in G.
  pose proof (lenL_used 256 ltac:(lia) ltac:(rewrite fL_256; lia)).
  destruct (Z.eqb_spec (lenL 256) 1) as [E1|NE]; [exact E1|]. cbn [negb] in G. replace ((0 <? 1) && true) with true in G by reflexivity.
  pose proof (pow2_pos (15 - lenL 256) ltac:(lia)). lia.
Qed.

Variable prm : oprm.
Hypothesis PRM : prm_ok prm lbs b.
Local Notation LL := (p_LL prm).
Local Notation Ls := (lens prm).



Lemma LL_facts : 1 <= LL <= 15 /\ lbs + 1 < fib (LL + 3) /\ fib (LL + 3) <= fib 18 /\ NSYM b + 1 <= lbs.
Proof.
  destruct (po_LL prm _ b PRM) as [R1 R2]. pose proof (ok_N b _ OK).
  pose proof (fib_mono (p_LL prm + 3) 18 ltac:(lia)). lia.
Qed.


Lemma TL_noovf zL : tree_facts zL 286 15 (fL b) [] -> g_W (zt_g zL) < fib (15 + 3).
Proof. intros TF. rewrite (TL_W zL TF). pose proof LL_facts. change (15 + 3) with 18. lia. Qed.

Lemma lenL_depth zL c : tree_facts zL 286 15 (fL b) [] -> (forall c, 0 <= c < 286 -> lenL c = zt_len zL c) ->
  0 <= c < 286 -> 0 < fL b c -> lenL c = tdepth zL c.
Proof.
  intros TF EL Hc U. rewrite EL by lia. apply (tnoovf2 zL 286 15 (fL b) [] TF (TL_noovf zL TF) c Hc). rewrite ffreq_nil. lia.
Qed.
Lemma kraftL : lsum (fun c => if usedLb b c then 2 ^ (15 - lenL c) else 0) (zrange 0 286) = 2 ^ 15.
Proof.
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL).
  rewrite <- (tkraft2 zL 286 15 (fL b) [] TF (TL_noovf zL TF)). change (Z.to_nat 286) with 286%nat. rewrite lsum_zrange.
  apply zsum_ext. intros c Hc. rewrite ffreq_nil. unfold usedLb. pose proof (fL_nonneg c).
  destruct (Z.ltb_spec 0 (fL b c)); destruct (Z.eqb_spec (fL b c) 0); try lia. rewrite EL by lia. reflexivity.
Qed.
Lemma fibL c : 0 <= c < 286 -> 0 < fL b c -> fL b c * fib (lenL c + 1) <= WL b.
Proof.
  intros Hc U. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL).
  rewrite (lenL_depth zL c TF EL Hc U). rewrite WL_eq, <- (TL_W zL TF).
  pose proof (tfib zL 286 15 (fL b) [] TF c Hc) as X. rewrite ffreq_nil in X. apply X. lia.
Qed.
Lemma monoL a c : 0 <= a < 286 -> 0 <= c < 286 -> 0 < fL b a -> fL b a < fL b c -> lenL c <= lenL a.
Proof.
  intros Ha Hc Ua LT. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL).
  rewrite (lenL_depth zL a TF EL Ha Ua), (lenL_depth zL c TF EL Hc ltac:(lia)).
  apply (tmono zL 286 15 (fL b) [] TF a c Ha Hc); rewrite !ffreq_nil; lia.
Qed.
Lemma spreadL s c : 0 <= s < 286 -> 0 <= c < 286 -> fL b s = 1 -> 0 < fL b c -> lenL c <= lenL s + 1.
Proof.
  intros Hs Hc Us Uc. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL).
  rewrite (lenL_depth zL s TF EL Hs ltac:(lia)), (lenL_depth zL c TF EL Hc Uc).
  apply (tspread zL 286 15 (fL b) [] TF s c Hs Hc); rewrite !ffreq_nil; lia.
Qed.

Lemma TD_noovf zD : tree_facts zD 30 15 (gD b) (ob_forced b) -> g_W (zt_g zD) < fib (15 + 3).
Proof. intros TF. rewrite (TD_W zD TF). pose proof LL_facts. pose proof WD_le. change (15 + 3) with 18. lia. Qed.

Lemma lenD_depth zD d : tree_facts zD 30 15 (gD b) (ob_forced b) -> (forall d, 0 <= d < 30 -> lenD d = zt_len zD d) ->
  0 <= d < 30 -> usedDb b d = true -> lenD d = tdepth zD d.
Proof.
  intros TF EL Hd U. rewrite EL by lia. apply (tnoovf2 zD 30 15 (gD b) (ob_forced b) TF (TD_noovf zD TF) d Hd). apply usedDb_W. exact U.
Qed.
Lemma kraftD : lsum (fun d => if usedDb b d then 2 ^ (15 - lenD d) else 0) (zrange 0 30) = 2 ^ 15.
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL).
  rewrite <- (tkraft2 zD 30 15 (gD b) (ob_forced b) TF (TD_noovf zD TF)). change (Z.to_nat 30) with 30%nat. rewrite lsum_zrange.
  apply zsum_ext. intros d Hd. destruct (usedDb b d) eqn:U.
  - pose proof (proj1 (usedDb_W d) U). destruct (Z.eqb_spec (ffreq (gD b) (ob_forced b) d) 0); [lia|]. rewrite EL by lia. reflexivity.
  - destruct (Z.eqb_spec (ffreq (gD b) (ob_forced b) d) 0); [reflexivity|]. apply usedDb_W in n. congruence.
Qed.
Lemma gD_max d : usedDb b d = true -> Z.max (gD b d) 1 = ffreq (gD b) (ob_forced b) d.
Proof.
  rewrite ffreqD. unfold usedDb. intros U. destruct (forcedD b d) eqn:Fd.
  - apply forcedD_spec in Fd. destruct forced_facts as (_ & _ & C). destruct (C d Fd). lia.
  - rewrite Bool.orb_false_r in U. apply Z.ltb_lt in U. lia.
Qed.
Lemma fibD d : 0 <= d < 30 -> usedDb b d = true -> Z.max (gD b d) 1 * fib (lenD d + 1) <= WD b.
Proof.
  intros Hd U. destruct (ok_TD b lbs OK) as (zD & TF & _ & EL).
  rewrite (lenD_depth zD d TF EL Hd U), (gD_max d U), <- (TD_W zD TF).
  apply (tfib zD 30 15 (gD b) (ob_forced b) TF d Hd). apply usedDb_W. exact U.
Qed.


Lemma lenL_range c : 0 <= c < 286 -> 0 < fL b c -> 1 <= lenL c <= LL.
Proof.
  intros Hc U. pose proof (lenL_used c Hc U). split; [lia|].
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). rewrite (lenL_depth zL c TF EL Hc U).
  pose proof LL_facts as (R1 & R2 & _ & R4).
  apply (tdepth_le2 zL 286 15 (fL b) [] TF LL); [rewrite (TL_W zL TF); lia|lia|lia|rewrite ffreq_nil; lia].
Qed.

Lemma lenD_range d : 0 <= d < 30 -> usedDb b d = true -> 1 <= lenD d <= LL.
Proof.
  intros Hd U. pose proof (lenD_used d Hd U). split; [lia|].
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). rewrite (lenD_depth zD d TF EL Hd U).
  pose proof LL_facts as (R1 & R2 & _ & R4). pose proof WD_le.
  apply (tdepth_le2 zD 30 15 (gD b) (ob_forced b) TF LL); [rewrite (TD_W zD TF); lia|lia|lia|apply usedDb_W; exact U].
Qed.

Lemma lens_in l : In l Ls <-> 1 <= l <= LL.
Proof. unfold lens. rewrite zrange_in. destruct (po_LL prm _ b PRM). lia. Qed.
Lemma lens_nodup : NoDup Ls. Proof. unfold lens. apply zrange_nodup. Qed.

Definition cntL (k : nat) (l : Z) : Z := countZ (fun c => usedLb b c && (lenL c =? l)) (lc_codes (lcl k)).
Definition wgtL (k : nat) (l : Z) : Z := lsum (fun c => if usedLb b c && (lenL c =? l) then fL b c else 0) (lc_codes (lcl k)).
Definition cntD (k : nat) (m : Z) : Z := countZ (fun d => usedDb b d && (lenD d =? m)) (dc_codes (dcl k)).
Definition wgtD (k : nat) (m : Z) : Z := lsum (fun d => if (0 <? gD b d) && (lenD d =? m) then gD b d else 0) (dc_codes (dcl k)).

Lemma oeval_uL k l : oeval b (uL k l) = cntL k l.
Proof.
  unfold uL. cbn [oeval oval]. unfold vU1, vU2, vU3, cellL, cntL, countZ. rewrite Z.add_0_r, !Z.mul_1_l.
  rewrite <- !lsum_add. apply lsum_ext. intros c _. unfold usedLb.
  pose proof (fL_nonneg c).
  destruct (Z.eqb_spec (fL b c) 1), (Z.eqb_spec (fL b c) 2), (Z.leb_spec 3 (fL b c)), (Z.ltb_spec 0 (fL b c)); cbn; try lia; destruct (lenL c =? l); lia.
Qed.
Lemma oeval_FL k l : oeval b (FL k l) = wgtL k l.
Proof.
  unfold FL. cbn [oeval oval]. unfold vU1, vU2, vF3, cellL, wgtL, countZ. rewrite Z.add_0_r, !Z.mul_1_l.
  rewrite <- (lsum_scale 2). rewrite <- !lsum_add. apply lsum_ext. intros c _. unfold usedLb.
  pose proof (fL_nonneg c).
  destruct (Z.eqb_spec (fL b c) 1), (Z.eqb_spec (fL b c) 2), (Z.leb_spec 3 (fL b c)), (Z.ltb_spec 0 (fL b c)); cbn; try lia; destruct (lenL c =? l); lia.
Qed.

Lemma oeval_vD k m : (k < nDC)%nat -> oeval b (vD k m) = cntD k m.
Proof.
  intros Hk. unfold vD. rewrite oeval_app. cbn [oeval oval]. unfold vV1, vV2, vV3, cellD, cntD, countZ. rewrite Z.add_0_r, !Z.mul_1_l.
  destruct forced_facts as (NDf & LF & FF).
  transitivity (lsum (fun d => if (0 <? gD b d) && (lenD d =? m) then 1 else 0) (dc_codes (dcl k))
                + lsum (fun d => if existsb (Z.eqb d) (ob_forced b) then (if lenD d =? m then 1 else 0) else 0) (dc_codes (dcl k))).
  - f_equal.
    + rewrite <- !lsum_add. apply lsum_ext. intros d _. pose proof (gD_nonneg d).
      destruct (Z.eqb_spec (gD b d) 1), (Z.eqb_spec (gD b d) 2), (Z.leb_spec 3 (gD b d)), (Z.ltb_spec 0 (gD b d)); cbn; try lia; destruct (lenD d =? m); lia.
    + destruct (Nat.eqb_spec k 0) as [->|NZ].
      * cbn [oeval oval]. unfold vVF, countZ. rewrite Z.add_0_r, Z.mul_1_l. symmetry.
        apply lsum_sublist; [apply (zrange_nodup 0 4)|exact NDf|]. intros x Ix. destruct (FF x Ix) as [R _].
        change (dc_codes (dcl 0)) with (zrange 0 4). apply zrange_in. lia.
      * cbn [oeval]. symmetry. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros d Id.
        destruct (classD_xd k d Hk Id) as (_ & _ & K0).
        replace (existsb (Z.eqb d) (ob_forced b)) with false; [reflexivity|]. symmetry. apply Bool.not_true_iff_false.
        rewrite existsb_exists. intros (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. destruct (FF y Iy) as [R _].
        assert (k = 0)%nat by (apply K0; lia). lia.
  - rewrite <- lsum_add. apply lsum_ext. intros d Id. unfold usedDb, forcedD.
    destruct (Z.ltb_spec 0 (gD b d)); cbn.
    + replace (existsb (Z.eqb d) (ob_forced b)) with false; [lia|]. symmetry. apply Bool.not_true_iff_false.
      rewrite existsb_exists. intros (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. destruct (FF y Iy) as [_ G0]. lia.
    + destruct (existsb (Z.eqb d) (ob_forced b)); [|reflexivity]. destruct (lenD d =? m); reflexivity.
Qed.

Lemma oeval_GD k m : oeval b (GD k m) = wgtD k m.
Proof.
  unfold GD. cbn [oeval oval]. unfold vV1, vV2, vG3, cellD, wgtD, countZ. rewrite Z.add_0_r, !Z.mul_1_l.
  rewrite <- (lsum_scale 2). rewrite <- !lsum_add. apply lsum_ext. intros d _. pose proof (gD_nonneg d).
  destruct (Z.eqb_spec (gD b d) 1), (Z.eqb_spec (gD b d) 2), (Z.leb_spec 3 (gD b d)), (Z.ltb_spec 0 (gD b d)); cbn; try lia; destruct (lenD d =? m); lia.
Qed.

Lemma pick_len (S : list Z) (Q : Z -> bool) (len w : Z -> Z) :
  (forall c, In c S -> Q c = true -> In (len c) Ls) ->
  gsum (fun l => lsum (fun c => if Q c && (len c =? l) then w c else 0) S) Ls = lsum (fun c => if Q c then w c else 0) S.
Proof.
  intros H. rewrite <- (gsum_lsum _ S).
  rewrite (gsum_ext (fun l => lsum _ S) (fun l => gsum (fun c => if Q c && (len c =? l) then w c else 0) S)) by (intros; symmetry; apply gsum_lsum).
  rewrite gsum_swap. apply gsum_ext. intros c Ic.
  destruct (Q c) eqn:Qc; cbn.
  - rewrite (gsum_ext _ (fun l => if l =? len c then w c else 0)) by (intros l _; rewrite Z.eqb_sym; reflexivity).
    apply (gsum_pick (fun _ => w c) Ls (len c) lens_nodup). apply H; assumption.
  - clear. induction Ls; cbn; lia.
Qed.

Lemma used_len_in c : In c (zrange 0 286) -> usedLb b c = true -> In (lenL c) Ls.
Proof. intros Ic U. apply zrange_in in Ic. apply Z.ltb_lt in U. apply lens_in. apply lenL_range; lia. Qed.
Lemma usedD_len_in d : In d (zrange 0 30) -> usedDb b d = true -> In (lenD d) Ls.
Proof. intros Id U. apply zrange_in in Id. apply lens_in. apply lenD_range; [lia|exact U]. Qed.
Lemma classL_in k c : (k < nLC)%nat -> In c (lc_codes (lcl k)) -> In c (zrange 0 286).
Proof. intros Hk Ic. destruct (classL_SL k c Hk Ic) as (_ & _ & R & _). apply zrange_in. lia. Qed.
Lemma classD_in k d : (k < nDC)%nat -> In d (dc_codes (dcl k)) -> In d (zrange 0 30).
Proof. intros Hk Id. destruct (classD_xd k d Hk Id) as (_ & R & _). apply zrange_in. lia. Qed.

Lemma sum_cntL k : (k < nLC)%nat -> gsum (fun l => cntL k l) Ls = countZ (usedLb b) (lc_codes (lcl k)).
Proof. intros Hk. unfold cntL, countZ. apply pick_len. intros c Ic U. apply used_len_in; [apply (classL_in k); assumption|assumption]. Qed.
Lemma sum_wgtL k (w : Z -> Z) : (k < nLC)%nat ->
  gsum (fun l => lsum (fun c => if usedLb b c && (lenL c =? l) then w c else 0) (lc_codes (lcl k))) Ls = lsum (fun c => if usedLb b c then w c else 0) (lc_codes (lcl k)).
Proof. intros Hk. apply pick_len. intros c Ic U. apply used_len_in; [apply (classL_in k); assumption|assumption]. Qed.
Lemma sum_cntD k : (k < nDC)%nat -> gsum (fun m => cntD k m) Ls = countZ (usedDb b) (dc_codes (dcl k)).
Proof. intros Hk. unfold cntD, countZ. apply pick_len. intros d Id U. apply usedD_len_in; [apply (classD_in k); assumption|assumption]. Qed.
Lemma sum_wgtD k (w : Z -> Z) : (k < nDC)%nat ->
  gsum (fun m => lsum (fun d => if usedDb b d && (lenD d =? m) then w d else 0) (dc_codes (dcl k))) Ls = lsum (fun d => if usedDb b d then w d else 0) (dc_codes (dcl k)).
Proof. intros Hk. apply pick_len. intros d Id U. apply usedD_len_in; [apply (classD_in k); assumption|assumption]. Qed.

Lemma used_fL c : (if usedLb b c then fL b c else 0) = fL b c.
Proof. unfold usedLb. pose proof (fL_nonneg c). destruct (Z.ltb_spec 0 (fL b c)); lia. Qed.
Lemma usedD_gD d : 0 <= d < 30 -> (if usedDb b d then gD b d else 0) = gD b d.
Proof.
  intros Hd. unfold usedDb. pose proof (gD_nonneg d). destruct (Z.ltb_spec 0 (gD b d)); cbn; [reflexivity|].
  destruct (forcedD b d); lia.
Qed.
Lemma wgtD_used k m d : In d (dc_codes (dcl k)) -> (k < nDC)%nat ->
  (if (0 <? gD b d) && (lenD d =? m) then gD b d else 0) = (if usedDb b d && (lenD d =? m) then gD b d else 0).
Proof.
  intros. unfold usedDb. pose proof (gD_nonneg d). destruct (Z.ltb_spec 0 (gD b d)); cbn; [reflexivity|].
  destruct (forcedD b d && (lenD d =? m)); lia.
Qed.



Lemma oholds_le l r : oeval b l <= r -> oholds b (mk l Le r). Proof. exact (fun H => H). Qed.
Lemma oholds_ge l r : oeval b l >= r -> oholds b (mk l Ge r). Proof. exact (fun H => H). Qed.
Lemma oholds_eq l r : oeval b l = r -> oholds b (mk l Eq r). Proof. exact (fun H => H). Qed.

Lemma oeval_cat_uL k : oeval b (cat (map (uL k) Ls)) = gsum (fun l => cntL k l) Ls.
Proof. rewrite oeval_catg. apply gsum_ext. intros. apply oeval_uL. Qed.
Lemma oeval_cat_vD k : (k < nDC)%nat -> oeval b (cat (map (vD k) Ls)) = gsum (fun m => cntD k m) Ls.
Proof. intros. rewrite oeval_catg. apply gsum_ext. intros. apply oeval_vD. assumption. Qed.

Lemma rows_class_sound : Forall (oholds b) (rows_class prm).
Proof.
  unfold rows_class. apply Forall_app2; [|apply Forall_app2].
  - apply Forall_map_iff. intros k Hk. apply ks_in in Hk.
    destruct (is_eob k) eqn:E.
    + apply oholds_eq. rewrite oeval_cat_uL, (sum_cntL k Hk). rewrite (classesEob k Hk E). cbn.
      unfold countZ. cbn. unfold usedLb. rewrite fL_256. reflexivity.
    + apply oholds_le. rewrite oeval_cat_uL, (sum_cntL k Hk). apply countZ_le_len.
  - apply Forall_map_iff. intros k Hk. apply ks_in in Hk. apply oholds_le.
    rewrite (oeval_cat_vD k Hk), (sum_cntD k Hk). apply countZ_le_len.
  - apply Forall_cat. intros l Il. apply in_map_iff in Il. destruct Il as (k & <- & Hk). apply ks_in in Hk.
    destruct (is_eob k) eqn:E; [|constructor].
    apply Forall_cat. intros r Ir. apply in_map_iff in Ir. destruct Ir as (l & <- & Il).
    pose proof (classesEob k Hk E) as CE.
    repeat constructor; cbn [oholds mk oeval oval]; unfold vU2, vU3, cellL; rewrite CE; cbn; rewrite fL_256; reflexivity.
Qed.

Lemma sum_usedD : gsum (fun k => gsum (fun m => cntD k m) Ls) (ks nDC) = vV b.
Proof.
  rewrite (gsum_ext _ (fun k => countZ (usedDb b) (dc_codes (dcl k)))).
  2:{ intros k Hk. apply ks_in in Hk. apply sum_cntD. exact Hk. }
  unfold countZ. rewrite (gsum_classesD (fun c => if usedDb b c then 1 else 0)).
  unfold vV, countZ. destruct forced_facts as (NDf & LF & FF).
  rewrite (lsum_ext (fun c => if usedDb b c then 1 else 0) (fun c => (if 0 <? gD b c then 1 else 0) + (if existsb (Z.eqb c) (ob_forced b) then 1 else 0)) (zrange 0 30)).
  2:{ intros d Id. unfold usedDb, forcedD. pose proof (gD_nonneg d). destruct (Z.ltb_spec 0 (gD b d)); cbn.
      - replace (existsb (Z.eqb d) (ob_forced b)) with false; [lia|]. symmetry. apply Bool.not_true_iff_false.
        rewrite existsb_exists. intros (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. destruct (FF y Iy). lia.
      - destruct (existsb (Z.eqb d) (ob_forced b)); reflexivity. }
  rewrite lsum_add. rewrite (lsum_sublist (fun _ => 1) (zrange 0 30) (ob_forced b) (zrange_nodup 0 30) NDf).
  2:{ intros x Ix. destruct (FF x Ix). apply zrange_in. lia. }
  f_equal. clear. induction (ob_forced b); [reflexivity|]. cbn [lsum length]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma rows_dmin_sound : Forall (oholds b) (rows_dmin prm).
Proof.
  unfold rows_dmin. constructor; [|constructor; [|constructor]].
  - apply oholds_ge. rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => gsum (fun m => cntD k m) Ls)) by (intros k Hk; apply oeval_cat_vD; apply ks_in; exact Hk).
    rewrite sum_usedD. pose proof (D2). lia.
  - apply oholds_le. destruct forced_facts as (NDf & LF & FF).
    transitivity (gsum (fun m => vVF b m) Ls).
    { apply Z.eq_le_incl. generalize Ls. intros LS. induction LS as [|m LS IH]; [reflexivity|]. cbn [map oeval gsum]. cbn [oval]. rewrite IH. lia. }
    unfold vVF, countZ.
    transitivity (lsum (fun d => if true then 1 else 0) (ob_forced b)).
    + rewrite <- (pick_len (ob_forced b) (fun _ => true) (fun d => lenD d) (fun _ => 1)).
      * apply Z.eq_le_incl. apply gsum_ext. intros. apply lsum_ext. intros. reflexivity.
      * intros d Id _. destruct (FF d Id). apply usedD_len_in; [apply zrange_in; lia|]. unfold usedDb. rewrite (proj2 (forcedD_spec d) Id). apply Bool.orb_true_r.
    + transitivity (Z.of_nat (length (ob_forced b))); [|lia]. apply Z.eq_le_incl.
      change (lsum (fun _ => 1) (ob_forced b) = Z.of_nat (length (ob_forced b))). clear.
      induction (ob_forced b) as [|x F IH]; [reflexivity|]. cbn [lsum length]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma Zdiv_cap f F W : 0 < F -> 0 <= f -> f * F <= W -> f <= W / F.
Proof. intros. apply Z.div_le_lower_bound; lia. Qed.

Lemma rows_cells_sound : Forall (oholds b) (rows_cells prm).
Proof.
  pose proof (ok_N b _ OK) as HN. pose proof (po_lbs prm _ b PRM) as PL.
  unfold rows_cells. apply Forall_app2.
  - apply Forall_cat. intros rs Irs. apply in_map_iff in Irs. destruct Irs as (k & <- & Hk). apply ks_in in Hk.
    apply Forall_cat. intros r Ir. apply in_map_iff in Ir. destruct Ir as (l & <- & Il).
    apply Forall_app2.
    + constructor; [|constructor; [|constructor]].
      * apply oholds_ge. cbn [oeval oval mk]. unfold vF3, vU3, cellL, countZ. rewrite Z.add_0_r, Z.mul_1_l.
        enough (3 * lsum (fun c => if (3 <=? fL b c) && (lenL c =? l) then 1 else 0) (lc_codes (lcl k)) <= lsum (fun c => if (3 <=? fL b c) && (lenL c =? l) then fL b c else 0) (lc_codes (lcl k))) by lia.
        rewrite <- lsum_scale. apply lsum_le. intros c _. destruct (Z.leb_spec 3 (fL b c)); cbn; [|lia]. destruct (lenL c =? l); lia.
      * apply oholds_le. cbn [oeval oval mk]. unfold vF3, vU3, cellL, countZ. rewrite Z.add_0_r, Z.mul_1_l.
        enough (lsum (fun c => if (3 <=? fL b c) && (lenL c =? l) then fL b c else 0) (lc_codes (lcl k)) <= capL prm l * lsum (fun c => if (3 <=? fL b c) && (lenL c =? l) then 1 else 0) (lc_codes (lcl k))) by lia.
        rewrite <- lsum_scale. apply lsum_le. intros c Ic. destruct (Z.leb_spec 3 (fL b c)); cbn; [|lia].
        destruct (Z.eqb_spec (lenL c) l); [|lia]. rewrite Z.mul_1_r. unfold capL. rewrite PL.
        destruct (classL_SL k c Hk Ic) as (_ & _ & Rc & _).
        pose proof (fibL c Rc ltac:(lia)) as F. rewrite WL_eq, e in F.
        apply Zdiv_cap; [|lia|lia]. pose proof (fib_mono 1 (l + 1)). pose proof (lens_in l). rewrite fib_1 in H0. apply H1 in Il. lia.
    + destruct (Z.ltb_spec (capL prm l) 2); [|constructor]. constructor; [|constructor].
      apply oholds_eq. cbn [oeval oval mk]. unfold vU2, cellL, countZ. rewrite Z.add_0_r, Z.mul_1_l.
      etransitivity; [apply (lsum_ext _ (fun _ => 0))|apply lsum_zero]. intros c Ic.
      destruct (Z.eqb_spec (fL b c) 2); cbn; [|reflexivity]. destruct (Z.eqb_spec (lenL c) l); [exfalso|reflexivity].
      destruct (classL_SL k c Hk Ic) as (_ & _ & Rc & _).
      pose proof (fibL c Rc ltac:(lia)) as F. rewrite WL_eq, e, e0 in F.
      unfold capL in H. rewrite PL in H.
      pose proof (fib_mono 1 (l + 1)). pose proof (lens_in l). rewrite fib_1 in H0. apply H1 in Il.
      assert (2 <= lbs / fib (l + 1)) by (apply Z.div_le_lower_bound; lia). lia.
  - apply Forall_cat. intros rs Irs. apply in_map_iff in Irs. destruct Irs as (k & <- & Hk). apply ks_in in Hk.
    apply Forall_cat. intros r Ir. apply in_map_iff in Ir. destruct Ir as (m & <- & Im).
    assert (WDle : WD b <= lbs + 1).
    { unfold WD. destruct forced_facts as (_ & LF & _). unfold vP.
      pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). unfold NSYM in *. lia. }
    apply Forall_app2.
    + constructor; [|constructor; [|constructor]].
      * apply oholds_ge. cbn [oeval oval mk]. unfold vG3, vV3, cellD, countZ. rewrite Z.add_0_r, Z.mul_1_l.
        enough (3 * lsum (fun d => if (3 <=? gD b d) && (lenD d =? m) then 1 else 0) (dc_codes (dcl k)) <= lsum (fun d => if (3 <=? gD b d) && (lenD d =? m) then gD b d else 0) (dc_codes (dcl k))) by lia.
        rewrite <- lsum_scale. apply lsum_le. intros d _. destruct (Z.leb_spec 3 (gD b d)); cbn; [|lia]. destruct (lenD d =? m); lia.
      * apply oholds_le. cbn [oeval oval mk]. unfold vG3, vV3, cellD, countZ. rewrite Z.add_0_r, Z.mul_1_l.
        enough (lsum (fun d => if (3 <=? gD b d) && (lenD d =? m) then gD b d else 0) (dc_codes (dcl k)) <= capD prm m * lsum (fun d => if (3 <=? gD b d) && (lenD d =? m) then 1 else 0) (dc_codes (dcl k))) by lia.
        rewrite <- lsum_scale. apply lsum_le. intros d Id. destruct (Z.leb_spec 3 (gD b d)); cbn; [|lia].
        destruct (Z.eqb_spec (lenD d) m); [|lia]. rewrite Z.mul_1_r. unfold capD. rewrite PL.
        destruct (classD_xd k d Hk Id) as (_ & Rd & _).
        assert (U : usedDb b d = true) by (unfold usedDb; destruct (Z.ltb_spec 0 (gD b d)); [reflexivity|lia]).
        pose proof (fibD d Rd U) as F. rewrite e in F. rewrite Z.max_l in F by lia.
        apply Zdiv_cap; [|lia|lia]. pose proof (fib_mono 1 (m + 1)). pose proof (lens_in m). rewrite fib_1 in H0. apply H1 in Im. lia.
    + destruct (Z.ltb_spec (capD prm m) 2); [|constructor]. constructor; [|constructor].
      apply oholds_eq. cbn [oeval oval mk]. unfold vV2, cellD, countZ. rewrite Z.add_0_r, Z.mul_1_l.
      etransitivity; [apply (lsum_ext _ (fun _ => 0))|apply lsum_zero]. intros d Id.
      destruct (Z.eqb_spec (gD b d) 2); cbn; [|reflexivity]. destruct (Z.eqb_spec (lenD d) m); [exfalso|reflexivity].
      destruct (classD_xd k d Hk Id) as (_ & Rd & _).
      assert (U : usedDb b d = true) by (unfold usedDb; destruct (Z.ltb_spec 0 (gD b d)); [reflexivity|lia]).
      pose proof (fibD d Rd U) as F. rewrite e, e0 in F. rewrite Z.max_l in F by lia.
      unfold capD in H. rewrite PL in H.
      pose proof (fib_mono 1 (m + 1)). pose proof (lens_in m). rewrite fib_1 in H0. apply H1 in Im.
      assert (2 <= (lbs + 1) / fib (m + 1)) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma rows_kraft_sound : Forall (oholds b) (rows_kraft prm).
Proof.
  unfold rows_kraft. constructor; [|constructor; [|constructor]].
  - apply oholds_eq. rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => lsum (fun c => if usedLb b c then 2 ^ (15 - lenL c) else 0) (lc_codes (lcl k)))).
    2:{ intros k Hk. apply ks_in in Hk. rewrite oeval_catg.
        rewrite (gsum_ext _ (fun l => lsum (fun c => if usedLb b c && (lenL c =? l) then 2 ^ (15 - lenL c) else 0) (lc_codes (lcl k)))).
        - apply sum_wgtL. exact Hk.
        - intros l Il. rewrite oeval_scale, oeval_uL. unfold cntL, countZ. rewrite <- lsum_scale. apply lsum_ext.
          intros c _. destruct (usedLb b c); cbn; [|lia]. destruct (Z.eqb_spec (lenL c) l); [subst; lia|lia]. }
    rewrite gsum_classesL. apply (kraftL).
  - apply oholds_eq. rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => lsum (fun d => if usedDb b d then 2 ^ (15 - lenD d) else 0) (dc_codes (dcl k)))).
    2:{ intros k Hk. apply ks_in in Hk. rewrite oeval_catg.
        rewrite (gsum_ext _ (fun m => lsum (fun d => if usedDb b d && (lenD d =? m) then 2 ^ (15 - lenD d) else 0) (dc_codes (dcl k)))).
        - apply sum_wgtD. exact Hk.
        - intros m Im. rewrite oeval_scale, (oeval_vD k m Hk). unfold cntD, countZ. rewrite <- lsum_scale. apply lsum_ext.
          intros d _. destruct (usedDb b d); cbn; [|lia]. destruct (Z.eqb_spec (lenD d) m); [subst; lia|lia]. }
    rewrite gsum_classesD. apply (kraftD).
Qed.

Lemma gsum_FL_len (w : nat -> Z -> Z) :
  gsum (fun k => if is_len k then gsum (fun l => oeval b (scale (w k l) (FL k l))) Ls else 0) (ks nLC)
  = gsum (fun k => if is_len k then lsum (fun c => w k (lenL c) * fL b c) (lc_codes (lcl k)) else 0) (ks nLC).
Proof.
  apply gsum_ext. intros k Hk. apply ks_in in Hk. destruct (is_len k); [|reflexivity].
  rewrite (gsum_ext _ (fun l => lsum (fun c => if usedLb b c && (lenL c =? l) then w k (lenL c) * fL b c else 0) (lc_codes (lcl k)))).
  2:{ intros l _. rewrite oeval_scale, oeval_FL. unfold wgtL. rewrite <- lsum_scale. apply lsum_ext. intros c _.
      destruct (usedLb b c); cbn; [|lia]. destruct (Z.eqb_spec (lenL c) l); [subst; lia|lia]. }
  rewrite (sum_wgtL k (fun c => w k (lenL c) * fL b c) Hk). apply lsum_ext. intros c _.
  unfold usedLb. pose proof (fL_nonneg c). destruct (Z.ltb_spec 0 (fL b c)); [reflexivity|]. replace (fL b c) with 0 by lia. lia.
Qed.

Lemma gsum_FL_sel (sel : nat -> bool) (w : nat -> Z -> Z) :
  gsum (fun k => if sel k then gsum (fun l => oeval b (scale (w k l) (FL k l))) Ls else 0) (ks nLC)
  = gsum (fun k => if sel k then lsum (fun c => w k (lenL c) * fL b c) (lc_codes (lcl k)) else 0) (ks nLC).
Proof.
  apply gsum_ext. intros k Hk. apply ks_in in Hk. destruct (sel k); [|reflexivity].
  rewrite (gsum_ext _ (fun l => lsum (fun c => if usedLb b c && (lenL c =? l) then w k (lenL c) * fL b c else 0) (lc_codes (lcl k)))).
  2:{ intros l _. rewrite oeval_scale, oeval_FL. unfold wgtL. rewrite <- lsum_scale. apply lsum_ext. intros c _.
      destruct (usedLb b c); cbn; [|lia]. destruct (Z.eqb_spec (lenL c) l); [subst; lia|lia]. }
  rewrite (sum_wgtL k (fun c => w k (lenL c) * fL b c) Hk). apply lsum_ext. intros c _.
  unfold usedLb. pose proof (fL_nonneg c). destruct (Z.ltb_spec 0 (fL b c)); [reflexivity|]. replace (fL b c) with 0 by lia. lia.
Qed.
Lemma gsum_GD_w (w : nat -> Z -> Z) :
  gsum (fun k => gsum (fun m => oeval b (scale (w k m) (GD k m))) Ls) (ks nDC)
  = gsum (fun k => lsum (fun d => w k (lenD d) * gD b d) (dc_codes (dcl k))) (ks nDC).
Proof.
  apply gsum_ext. intros k Hk. apply ks_in in Hk.
  rewrite (gsum_ext _ (fun m => lsum (fun d => if usedDb b d && (lenD d =? m) then w k (lenD d) * gD b d else 0) (dc_codes (dcl k)))).
  2:{ intros m _. rewrite oeval_scale, oeval_GD. unfold wgtD. rewrite <- lsum_scale. apply lsum_ext. intros d Id.
      rewrite (wgtD_used k m d Id Hk). destruct (usedDb b d); cbn; [|lia]. destruct (Z.eqb_spec (lenD d) m); [subst; lia|lia]. }
  rewrite (sum_wgtD k (fun d => w k (lenD d) * gD b d) Hk). apply lsum_ext. intros d Id.
  destruct (classD_xd k d Hk Id) as (_ & Rd & _). pose proof (usedD_gD d Rd).
  destruct (usedDb b d); [reflexivity|]. replace (gD b d) with 0 by lia. lia.
Qed.

Lemma cat_FL_as_scale (sel : nat -> bool) :
  oeval b (cat (map (fun k => if sel k then cat (map (FL k) Ls) else []) (ks nLC)))
  = gsum (fun k => if sel k then lsum (fun c => 1 * fL b c) (lc_codes (lcl k)) else 0) (ks nLC).
Proof.
  rewrite oeval_catg. rewrite <- (gsum_FL_sel sel (fun _ _ => 1)). apply gsum_ext. intros k _.
  destruct (sel k); [|reflexivity]. rewrite oeval_catg. apply gsum_ext. intros l _. rewrite oeval_scale. lia.
Qed.

Lemma rows_defs_sound : Forall (oholds b) (rows_defs prm).
Proof.
  unfold rows_defs.
  assert (HP : oeval b (cat (map (fun k => if is_len k then cat (map (FL k) Ls) else []) (ks nLC))) = vP b).
  { rewrite cat_FL_as_scale.
    rewrite (gsum_classesLen (fun c => 1 * fL b c)). rewrite lsum_fL_w. rewrite (existsb_zrange 256).
    replace ((257 <=? 256) && (256 <? 257 + Z.of_nat 29)) with false by reflexivity.
    rewrite vP_eq, Z.add_0_r. apply ssum_ext. intros s I. rewrite existsb_zrange.
    destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyL] in *;
      [replace ((257 <=? c) && (c <? 257 + Z.of_nat 29)) with false; [reflexivity|symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia]
      |replace ((257 <=? lc) && (lc <? 257 + Z.of_nat 29)) with true; [reflexivity|symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia]]. }
  assert (HL : oeval b (cat (map (fun k => if is_lit k then cat (map (FL k) Ls) else []) (ks nLC))) = vNLIT b).
  { rewrite cat_FL_as_scale. rewrite (gsum_classesLit (fun c => 1 * fL b c)). rewrite lsum_fL_w. rewrite (existsb_zrange 256).
    replace ((0 <=? 256) && (256 <? 0 + Z.of_nat 256)) with false by reflexivity.
    rewrite vNLIT_eq, Z.add_0_r. apply ssum_ext. intros s I. rewrite existsb_zrange.
    destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyL] in *;
      [replace ((0 <=? c) && (c <? 0 + Z.of_nat 256)) with true; [reflexivity|symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia]
      |replace ((0 <=? lc) && (lc <? 0 + Z.of_nat 256)) with false; [reflexivity|symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia]]. }
  constructor. { apply oholds_eq. rewrite oeval_app, HP. cbn [oeval oval]. lia. }
  constructor. { apply oholds_eq. rewrite oeval_app, HL. cbn [oeval oval]. lia. }
  constructor. { apply oholds_eq. cbn [oeval oval]. rewrite vP_eq, vNLIT_eq. unfold NSYM.
                 enough (ssum (fun s => match s with OPair _ _ => 1 | _ => 0 end) syms + ssum (fun s => match s with OLit _ => 1 | _ => 0 end) syms = Z.of_nat (length syms)) by lia.
                 rewrite <- ssum_add. clear. induction (ob_syms b) as [|x r IH]; [reflexivity|]. cbn [ssum length]. rewrite Nat2Z.inj_succ, <- IH. destruct x; lia. }
  constructor. { apply oholds_eq. rewrite oeval_app. cbn [oeval oval].
                 rewrite oeval_catg. rewrite (gsum_ext _ (fun k => gsum (fun m => oeval b (scale 1 (GD k m))) Ls)).
                 2:{ intros k _. rewrite oeval_catg. apply gsum_ext. intros. rewrite oeval_scale. lia. }
                 rewrite (gsum_GD_w (fun _ _ => 1)). rewrite (gsum_classesD (fun d => 1 * gD b d)). rewrite lsum_gD_w, vP_eq.
                 enough (ssum (fun s => match s with OLit _ => 0 | OPair _ _ => 1 end) syms = ssum (fun s => match s with OLit _ => 0 | OPair _ _ => 1 end) syms) by lia. reflexivity. }
  constructor. { apply oholds_le. cbn [oeval oval]. pose proof (ok_N b _ OK). rewrite (po_lbs prm _ b PRM). lia. }
  constructor. { apply oholds_eq. rewrite oeval_app. cbn [oeval oval]. rewrite oeval_catg.
                 rewrite (gsum_ext _ (fun k => countZ (usedLb b) (lc_codes (lcl k)))) by (intros k Hk; apply ks_in in Hk; rewrite oeval_cat_uL; apply sum_cntL; exact Hk).
                 unfold countZ. rewrite gsum_classesL. unfold vU, countZ, usedLb. lia. }
  constructor. { apply oholds_eq. rewrite oeval_app. cbn [oeval oval]. rewrite oeval_catg.
                 rewrite (gsum_ext _ (fun k => if is_lit k then lsum (fun c => if usedLb b c then 1 else 0) (lc_codes (lcl k)) else 0)).
                 2:{ intros k Hk. apply ks_in in Hk. destruct (is_lit k); [|reflexivity]. rewrite oeval_cat_uL. apply sum_cntL. exact Hk. }
                 rewrite gsum_classesLit. unfold vNLITC, countZ, usedLb. lia. }
  constructor. { apply oholds_eq. rewrite oeval_app. cbn [oeval oval]. rewrite oeval_catg.
                 rewrite (gsum_ext _ (fun k => if is_len k then lsum (fun c => if usedLb b c then 1 else 0) (lc_codes (lcl k)) else 0)).
                 2:{ intros k Hk. apply ks_in in Hk. destruct (is_len k); [|reflexivity]. rewrite oeval_cat_uL. apply sum_cntL. exact Hk. }
                 rewrite gsum_classesLen. unfold vNLENC, countZ, usedLb. lia. }
  constructor. { apply oholds_eq. rewrite oeval_app. cbn [oeval oval]. rewrite oeval_catg.
                 rewrite (gsum_ext _ (fun k => gsum (fun m => cntD k m) Ls)) by (intros k Hk; apply oeval_cat_vD; apply ks_in; exact Hk).
                 rewrite sum_usedD. lia. }
  constructor; [|constructor].
  apply oholds_eq. rewrite !oeval_app. cbn [oeval oval].
  rewrite oeval_catg. rewrite (gsum_ext _ (fun k => if true then gsum (fun l => oeval b (scale (lc_SL (lcl k) - l) (FL k l))) Ls else 0)) by (intros; rewrite oeval_catg; reflexivity).
  rewrite (gsum_FL_sel (fun _ => true) (fun k l => lc_SL (lcl k) - l)).
  rewrite (gsum_ext _ (fun k => lsum (fun c => (sl_of_code c - lenL c) * fL b c) (lc_codes (lcl k)))).
  2:{ intros k Hk. apply ks_in in Hk. cbv iota beta. apply lsum_ext. intros c Ic. destruct (classL_SL k c Hk Ic) as (-> & _). reflexivity. }
  rewrite (gsum_classesL (fun c => (sl_of_code c - lenL c) * fL b c)). rewrite (lsum_fL_w (fun c => sl_of_code c - lenL c)).
  rewrite oeval_catg. rewrite (gsum_ext _ (fun k => gsum (fun m => oeval b (scale (5 - m) (GD k m))) Ls)) by (intros; rewrite oeval_catg; reflexivity).
  rewrite (gsum_GD_w (fun _ m => 5 - m)). rewrite (gsum_classesD (fun d => (5 - lenD d) * gD b d)). rewrite (lsum_gD_w (fun d => 5 - lenD d)).
  rewrite (existsb_zrange 256).
  replace (if (0 <=? 256) && (256 <? 0 + Z.of_nat 286) then sl_of_code 256 - lenL 256 else 0) with (7 - lenL 256) by reflexivity.
  unfold vSV. rewrite Z.add_0_r.
  enough (ssum (fun s => scostS s - dcostS b s) syms =
          ssum (fun s => if existsb (Z.eqb (keyL s)) (zrange 0 286) then sl_of_code (keyL s) - lenL (keyL s) else 0) syms
          + ssum (fun s => match s with OLit _ => 0 | OPair _ dc => 5 - lenD dc end) syms) by lia.
  rewrite <- ssum_add. apply ssum_ext. intros s I. rewrite existsb_zrange.
  destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyL scostS dcostS] in *;
    [replace ((0 <=? c) && (c <? 0 + Z.of_nat 286)) with true; [lia|symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia]
    |replace ((0 <=? lc) && (lc <? 0 + Z.of_nat 286)) with true; [lia|symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia]].
Qed.




Lemma oeval_U1row l : oeval b (map (fun k => (OU1 k l, 1)) (ks nLC)) = countZ (fun c => (fL b c =? 1) && (lenL c =? l)) (zrange 0 286).
Proof.
  transitivity (gsum (fun k => countZ (fun c => (fL b c =? 1) && (lenL c =? l)) (lc_codes (lcl k))) (ks nLC)).
  - generalize (ks nLC). intros K. induction K as [|k K IH]; [reflexivity|]. cbn [map oeval gsum oval]. rewrite IH. unfold vU1, cellL. lia.
  - unfold countZ. apply gsum_classesL.
Qed.

Lemma rows_case_sound : Forall (oholds b) (rows_case prm).
Proof.
  unfold rows_case. rewrite (po_d1 prm _ b PRM), (po_n1 prm _ b PRM).
  destruct d1_of_attained as (s0 & Is0 & Fs0 & Ls0). pose proof Is0 as Rs0. apply zrange_in in Rs0.
  apply Forall_app2.
  - apply Forall_cat. intros rs Irs. apply in_map_iff in Irs. destruct Irs as (l & <- & Il).
    destruct (Z.ltb_spec l (d1_of b)) as [LT|GE].
    + constructor; [|constructor]. apply oholds_eq. rewrite oeval_U1row. unfold countZ.
      etransitivity; [apply (lsum_ext _ (fun _ => 0))|apply lsum_zero]. intros c Ic.
      destruct (Z.eqb_spec (fL b c) 1); cbn; [|reflexivity]. destruct (Z.eqb_spec (lenL c) l); [|reflexivity].
      pose proof (d1_of_le c Ic e). lia.
    + destruct (Z.eqb_spec l (d1_of b)) as [EQ|NE].
      * constructor; [|constructor]. apply oholds_ge. rewrite oeval_U1row. unfold countZ.
        pose proof (lsum_ge_member (fun c => if (fL b c =? 1) && (lenL c =? l) then 1 else 0) (zrange 0 286) s0
                      ltac:(intros y _; cbn beta; destruct ((fL b y =? 1) && (lenL y =? l)); lia) Is0). cbn beta in H.
        rewrite Fs0, Ls0, <- EQ, !Z.eqb_refl in H. change (if true && true then 1 else 0) with 1 in H. lia.
      * destruct (Z.eqb_spec l (d1_of b + 1)) as [EQ1|NE1].
        -- apply Forall_cat. intros rs Irs. apply in_map_iff in Irs. destruct Irs as (k & <- & Hk). apply ks_in in Hk.
           constructor; [|constructor; [|constructor]]; apply oholds_eq; cbn [oeval oval]; unfold vU2, vU3, cellL, countZ; rewrite Z.add_0_r, Z.mul_1_l;
             (etransitivity; [apply (lsum_ext _ (fun _ => 0))|apply lsum_zero]); intros c Ic;
             destruct (classL_SL k c Hk Ic) as (_ & _ & Rc & _);
             [destruct (Z.eqb_spec (fL b c) 2) | destruct (Z.leb_spec 3 (fL b c))]; cbn; try reflexivity;
             destruct (Z.eqb_spec (lenL c) l); try reflexivity; exfalso;
             pose proof (monoL s0 c ltac:(lia) Rc ltac:(lia) ltac:(lia)); lia.
        --
           apply Forall_cat. intros rs Irs. apply in_map_iff in Irs. destruct Irs as (k & <- & Hk). apply ks_in in Hk.
           assert (NONE : forall c, In c (lc_codes (lcl k)) -> 0 < fL b c -> lenL c <> l).
           { intros c Ic U. destruct (classL_SL k c Hk Ic) as (_ & _ & Rc & _).
             pose proof (spreadL s0 c ltac:(lia) Rc Fs0 U). lia. }
           constructor; [|constructor; [|constructor; [|constructor]]]; apply oholds_eq; cbn [oeval oval]; unfold vU1, vU2, vU3, cellL, countZ; rewrite Z.add_0_r, Z.mul_1_l;
             (etransitivity; [apply (lsum_ext _ (fun _ => 0))|apply lsum_zero]); intros c Ic;
             [destruct (Z.eqb_spec (fL b c) 1) | destruct (Z.eqb_spec (fL b c) 2) | destruct (Z.leb_spec 3 (fL b c))]; cbn; try reflexivity;
             destruct (Z.eqb_spec (lenL c) l); try reflexivity; exfalso; apply (NONE c Ic); lia.
  - constructor; [|constructor]. apply oholds_eq. rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => cntL k 1)) by (intros; apply oeval_uL).
    unfold n1_of, cntL, countZ. apply gsum_classesL.
Qed.

Lemma ssum_swap_g {A} (F : A -> osym -> Z) (L : list A) (l : list osym) :
  gsum (fun a => ssum (fun s => F a s) l) L = ssum (fun s => gsum (fun a => F a s) L) l.
Proof.
  induction L as [|a r IH]; cbn.
  - induction l; cbn; [reflexivity|lia].
  - rewrite IH, <- ssum_add. reflexivity.
Qed.
Lemma ssum_nonneg f l : (forall s, In s l -> 0 <= f s) -> 0 <= ssum f l.
Proof. induction l; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHl ltac:(intros; apply H; auto)). lia. Qed.
Lemma gsum_ge_member {A} (f : A -> Z) (L : list A) (x : A) : (forall y, In y L -> 0 <= f y) -> In x L -> f x <= gsum f L.
Proof.
  induction L as [|y r IH]; cbn; intros P I; [destruct I|]. destruct I as [->|I].
  - pose proof (gsum_nonneg f r ltac:(intros; apply P; auto)). lia.
  - pose proof (P y (or_introl eq_refl)). specialize (IH ltac:(intros; apply P; auto) I). lia.
Qed.

Lemma oeval_PIsum (g : Z -> ovar) (h : Z -> osym -> bool) (S : list Z) :
  (forall c, oval b (g c) = scount (h c) syms) ->
  oeval b (map (fun c => (g c, 1)) S) = ssum (fun s => gsum (fun c => if h c s then 1 else 0) S) syms.
Proof.
  intros E. rewrite <- ssum_swap_g. induction S as [|c r IH]; [reflexivity|]. cbn [map oeval gsum]. rewrite IH, E. unfold scount. lia.
Qed.

Lemma pairA_count a : 1 <= a ->
  gsum (fun k => if is_len k then lsum (fun c => (if lenL c + lc_xl (lcl k) =? a then 1 else 0) * fL b c) (lc_codes (lcl k)) else 0) (ks nLC)
  = scount (fun s => pairA b s =? a) syms.
Proof.
  intros Ha.
  rewrite (gsum_ext _ (fun k => if is_len k then lsum (fun c => (if lenL c + xl_of_lcode c =? a then 1 else 0) * fL b c) (lc_codes (lcl k)) else 0)).
  2:{ intros k Hk. apply ks_in in Hk. destruct (is_len k) eqn:L; [|reflexivity]. apply lsum_ext. intros c Ic.
      destruct (classL_SL k c Hk Ic) as (_ & X & _). rewrite (X L). reflexivity. }
  rewrite (gsum_classesLen (fun c => (if lenL c + xl_of_lcode c =? a then 1 else 0) * fL b c)).
  rewrite (lsum_fL_w (fun c => if lenL c + xl_of_lcode c =? a then 1 else 0)). rewrite (existsb_zrange 256).
  replace ((257 <=? 256) && (256 <? 257 + Z.of_nat 29)) with false by reflexivity. rewrite Z.add_0_r.
  unfold scount. apply ssum_ext. intros s I. rewrite existsb_zrange.
  destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyL pairA] in *.
  - replace ((257 <=? c) && (c <? 257 + Z.of_nat 29)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
    destruct (Z.eqb_spec (-1) a); [lia|reflexivity].
  - replace ((257 <=? lc) && (lc <? 257 + Z.of_nat 29)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). reflexivity.
Qed.

Lemma pairB_count c : 0 <= c ->
  gsum (fun k => lsum (fun d => (if lenD d + dc_xd (dcl k) =? c then 1 else 0) * gD b d) (dc_codes (dcl k))) (ks nDC)
  = scount (fun s => pairB b s =? c) syms.
Proof.
  intros Hc.
  rewrite (gsum_ext _ (fun k => lsum (fun d => (if lenD d + xd_of_dcode d =? c then 1 else 0) * gD b d) (dc_codes (dcl k)))).
  2:{ intros k Hk. apply ks_in in Hk. apply lsum_ext. intros d Id. destruct (classD_xd k d Hk Id) as (-> & _). reflexivity. }
  rewrite (gsum_classesD (fun d => (if lenD d + xd_of_dcode d =? c then 1 else 0) * gD b d)).
  rewrite (lsum_gD_w (fun d => if lenD d + xd_of_dcode d =? c then 1 else 0)).
  unfold scount. apply ssum_ext. intros s I. destruct (keyL_range s I) as [(R & c' & ->)|(R & lc & dc & -> & Rd)]; cbn [pairB].
  - destruct (Z.eqb_spec (-1) c); [lia|reflexivity].
  - reflexivity.
Qed.

Lemma gsum_catmap {A B} (f : B -> Z) (g : A -> list B) (L : list A) : gsum f (cat (map g L)) = gsum (fun a => gsum f (g a)) L.
Proof. unfold cat. induction L; cbn; [reflexivity|]. rewrite gsum_app, IHL. reflexivity. Qed.

Lemma ssum_ge_member f l x : (forall s, In s l -> 0 <= f s) -> In x l -> f x <= ssum f l.
Proof.
  induction l as [|y r IH]; cbn; intros P I; [destruct I|]. destruct I as [->|I].
  - pose proof (ssum_nonneg f r ltac:(intros; apply P; auto)). lia.
  - pose proof (P y (or_introl eq_refl)). specialize (IH ltac:(intros; apply P; auto) I). lia.
Qed.
Lemma in_syms_fL s : In s syms -> 1 <= fL b (keyL s).
Proof.
  intros I. rewrite fL_eq. pose proof (ssum_ge_member (fun s' => if keyL s' =? keyL s then 1 else 0) syms s ltac:(intros s0 _; cbv beta; destruct (keyL s0 =? keyL s); lia) I) as X.
  cbv beta in X. rewrite Z.eqb_refl in X. unfold scount. destruct (keyL s =? 256); lia.
Qed.
Lemma in_syms_gD lc dc : In (OPair lc dc) syms -> 1 <= gD b dc.
Proof.
  intros I. pose proof (sym_ok_in _ I) as SO. cbn in SO. rewrite gD_eq by lia.
  pose proof (ssum_ge_member (fun s' => if keyD s' =? dc then 1 else 0) syms (OPair lc dc) ltac:(intros s0 _; cbv beta; destruct (keyD s0 =? dc); lia) I) as X.
  cbv beta in X. cbn [keyD] in X. rewrite Z.eqb_refl in X. unfold scount. lia.
Qed.
Lemma ssum_scale c f l : ssum (fun s => c * f s) l = c * ssum f l.
Proof. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.
Lemma oeval_PI_pairs (h : Z * Z -> Z) (L : list (Z * Z)) :
  oeval b (map (fun ac => (OPI (fst ac) (snd ac), h ac)) L)
  = ssum (fun s => gsum (fun ac => if (pairA b s =? fst ac) && (pairB b s =? snd ac) then h ac else 0) L) syms.
Proof.
  rewrite <- ssum_swap_g. induction L as [|ac r IH]; [reflexivity|]. cbn [map oeval gsum oval]. rewrite IH. f_equal.
  unfold vPI, scount. rewrite <- ssum_scale. apply ssum_ext. intros s _. destruct (_ && _); lia.
Qed.
Lemma pairs_sum (f : Z * Z -> Z) : gsum f (pairsAB prm) = gsum (fun a => gsum (fun c => f (a, c)) (filter (fun c => 24 <? a + c) (Bs prm))) (As prm).
Proof. unfold pairsAB. rewrite gsum_catmap. apply gsum_ext. intros a _. rewrite gsum_map. reflexivity. Qed.

Lemma rows_ex_sound : Forall (oholds b) (rows_ex prm).
Proof.
  unfold rows_ex. apply Forall_app2; [|apply Forall_app2].
  - apply Forall_map_iff. intros a Ia. unfold As in Ia. apply zrange_in in Ia. apply oholds_le. rewrite oeval_app.
    rewrite (oeval_PIsum (fun c => OPI a c) (fun c s => (pairA b s =? a) && (pairB b s =? c))) by (intros; reflexivity).
    rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => if is_len k then gsum (fun l => oeval b (scale (if l + lc_xl (lcl k) =? a then -1 else 0) (FL k l))) Ls else 0)).
    2:{ intros k _. destruct (is_len k); cbn [andb].
        - rewrite oeval_catg. apply gsum_ext. intros l _. destruct (l + lc_xl (lcl k) =? a); [reflexivity|]. rewrite oeval_scale. cbn. lia.
        - rewrite oeval_catg. rewrite (gsum_ext _ (fun _ => 0)) by reflexivity. apply gsum_const0. }
    rewrite (gsum_FL_sel is_len (fun k l => if l + lc_xl (lcl k) =? a then -1 else 0)).
    rewrite (gsum_ext _ (fun k => -1 * (if is_len k then lsum (fun c => (if lenL c + lc_xl (lcl k) =? a then 1 else 0) * fL b c) (lc_codes (lcl k)) else 0))).
    2:{ intros k _. destruct (is_len k); [|lia]. rewrite <- lsum_scale. apply lsum_ext. intros. destruct (_ =? a); lia. }
    rewrite gsum_scale, (pairA_count a) by lia.
    enough (ssum (fun s => gsum (fun c => if (pairA b s =? a) && (pairB b s =? c) then 1 else 0) (filter (fun c => 24 <? a + c) (Bs prm))) syms
            <= scount (fun s => pairA b s =? a) syms) by lia.
    unfold scount. apply ssum_le. intros s I. destruct (Z.eqb_spec (pairA b s) a); cbn.
    +
      transitivity (gsum (fun c => if c =? pairB b s then 1 else 0) (filter (fun c => 24 <? a + c) (Bs prm))).
      * apply Z.eq_le_incl. apply gsum_ext. intros. rewrite Z.eqb_sym. reflexivity.
      * destruct (in_dec Z.eq_dec (pairB b s) (filter (fun c => 24 <? a + c) (Bs prm))) as [IN|NI].
        -- rewrite (gsum_pick (fun _ => 1)); [lia|apply NoDup_filter; unfold Bs; apply zrange_nodup|exact IN].
        -- rewrite (gsum_miss (fun _ => 1)) by exact NI. lia.
    + rewrite ?(gsum_ext _ (fun _ => 0)) by reflexivity. rewrite ?gsum_const0. apply gsum_nonneg || lia. all: try (intros; lia).
  - apply Forall_map_iff. intros c Ic. unfold Bs in Ic. apply zrange_in in Ic. apply oholds_le. rewrite oeval_app.
    rewrite (oeval_PIsum (fun a => OPI a c) (fun a s => (pairA b s =? a) && (pairB b s =? c))) by (intros; reflexivity).
    rewrite oeval_catg.
    rewrite (gsum_ext _ (fun k => gsum (fun m => oeval b (scale (if m + dc_xd (dcl k) =? c then -1 else 0) (GD k m))) Ls)).
    2:{ intros k _. rewrite oeval_catg. apply gsum_ext. intros m _. destruct (m + dc_xd (dcl k) =? c); [reflexivity|]. rewrite oeval_scale. cbn [oeval]. lia. }
    rewrite (gsum_GD_w (fun k m => if m + dc_xd (dcl k) =? c then -1 else 0)).
    rewrite (gsum_ext _ (fun k => -1 * lsum (fun d => (if lenD d + dc_xd (dcl k) =? c then 1 else 0) * gD b d) (dc_codes (dcl k)))).
    2:{ intros k _. rewrite <- lsum_scale. apply lsum_ext. intros. destruct (_ =? c); lia. }
    rewrite gsum_scale, (pairB_count c) by lia.
    enough (ssum (fun s => gsum (fun a => if (pairA b s =? a) && (pairB b s =? c) then 1 else 0) (filter (fun a => 24 <? a + c) (As prm))) syms
            <= scount (fun s => pairB b s =? c) syms) by lia.
    unfold scount. apply ssum_le. intros s I. destruct (Z.eqb_spec (pairB b s) c); cbn.
    + transitivity (gsum (fun a => if a =? pairA b s then 1 else 0) (filter (fun a => 24 <? a + c) (As prm))).
      * apply Z.eq_le_incl. apply gsum_ext. intros. rewrite Z.eqb_sym, Bool.andb_true_r. reflexivity.
      * destruct (in_dec Z.eq_dec (pairA b s) (filter (fun a => 24 <? a + c) (As prm))) as [IN|NI].
        -- rewrite (gsum_pick (fun _ => 1)); [lia|apply NoDup_filter; unfold As; apply zrange_nodup|exact IN].
        -- rewrite (gsum_miss (fun _ => 1)) by exact NI. lia.
    + rewrite (gsum_ext _ (fun _ => 0)) by (intros; rewrite Bool.andb_false_r; reflexivity). rewrite gsum_const0. lia.
  - constructor; [|constructor]. apply oholds_le. cbn [oeval oval]. rewrite Z.mul_1_l.
    rewrite (oeval_PI_pairs (fun ac => - (fst ac + snd ac - 24))).
    enough (vEX b <= ssum (fun s => gsum (fun ac => if (pairA b s =? fst ac) && (pairB b s =? snd ac) then fst ac + snd ac - 24 else 0) (pairsAB prm)) syms).
    { match goal with |- vEX b + ssum ?f syms <= 0 =>
        match type of H with vEX b <= ssum ?g syms =>
          enough (E : ssum f syms = -1 * ssum g syms) by lia end end.
      rewrite <- ssum_scale. apply ssum_ext. intros s _. rewrite <- gsum_scale. apply gsum_ext. intros. destruct (_ && _); lia. }
    unfold vEX. apply ssum_le. intros s I. unfold exS. rewrite pairs_sum.
    pose proof LL_facts as (RL & _ & _ & _).
    destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [dcostS pairA pairB keyL] in *.
    +
      pose proof (in_syms_fL _ I) as U. cbn [keyL] in U. pose proof (lenL_range c ltac:(lia) ltac:(lia)).
      rewrite (gsum_ext _ (fun _ => 0)).
      2:{ intros a Ia. unfold As in Ia. apply zrange_in in Ia. rewrite (gsum_ext _ (fun _ => 0)); [apply gsum_const0|].
          intros x _. cbn [fst snd]. replace (-1 =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite gsum_const0. lia.
    +
      pose proof (in_syms_fL _ I) as U. cbn [keyL] in U. pose proof (lenL_range lc ltac:(lia) ltac:(lia)) as RA.
      pose proof (in_syms_gD _ _ I) as UD.
      pose proof (lenD_range dc ltac:(lia) ltac:(unfold usedDb; rewrite (proj2 (Z.ltb_lt 0 (gD b dc))) by lia; reflexivity)) as RB.
      assert (XL : 0 <= xl_of_lcode lc <= 5).
      { unfold xl_of_lcode. clear - R. assert (Hn : (Z.to_nat (lc - 257) < 29)%nat) by lia.
        generalize dependent (Z.to_nat (lc - 257)). intros n Hn.
        do 29 (destruct n as [|n]; [cbn; lia|]). lia. }
      assert (XD : 0 <= xd_of_dcode dc <= 13).
      { unfold xd_of_dcode. clear - Rd. assert (Hn : (Z.to_nat dc < 30)%nat) by lia.
        generalize dependent (Z.to_nat dc). intros n Hn.
        do 30 (destruct n as [|n]; [cbn; lia|]). lia. }
      set (A := lenL lc + xl_of_lcode lc) in *. set (B := lenD dc + xd_of_dcode dc) in *.
      rewrite (gsum_ext _ (fun a => if a =? A then gsum (fun c0 => if c0 =? B then A + c0 - 24 else 0) (filter (fun c0 => 24 <? a + c0) (Bs prm)) else 0)).
      2:{ intros a _. destruct (Z.eqb_spec a A) as [->|NE].
          - apply gsum_ext. intros x _. cbn [fst snd]. rewrite Z.eqb_refl, (Z.eqb_sym B x). cbn [andb]. reflexivity.
          - rewrite (gsum_ext _ (fun _ => 0)); [apply gsum_const0|]. intros x _. cbn [fst snd].
            replace (A =? a) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite (gsum_pick (fun a => gsum (fun c0 => if c0 =? B then A + c0 - 24 else 0) (filter (fun c0 => 24 <? a + c0) (Bs prm))) (As prm) A).
      2:{ unfold As. apply zrange_nodup. }
      2:{ unfold As. apply zrange_in. lia. }
      cbv beta. destruct (Z_lt_le_dec 24 (A + B)).
      * rewrite (gsum_pick (fun c0 => A + c0 - 24) _ B); [lia| apply NoDup_filter; unfold Bs; apply zrange_nodup |].
        apply filter_In. split; [unfold Bs; apply zrange_in; lia|]. apply Z.ltb_lt. lia.
      * rewrite (gsum_miss (fun c0 => A + c0 - 24) _ B); [lia|]. intros IN. apply filter_In in IN. destruct IN as [_ X]. apply Z.ltb_lt in X. lia.
Qed.

Lemma vV_used : vV b = countZ (usedDb b) (zrange 0 30).
Proof.
  rewrite <- sum_usedD. rewrite (gsum_ext _ (fun k => countZ (usedDb b) (dc_codes (dcl k)))).
  2:{ intros k Hk. apply ks_in in Hk. apply sum_cntD. exact Hk. }
  unfold countZ. apply (gsum_classesD (fun c => if usedDb b c then 1 else 0)).
Qed.

Lemma rows_bc_sound : Forall (oholds b) (rows_bc prm).
Proof.
  unfold rows_bc. apply Forall_app2.
  - apply Forall_map_iff. intros j Ij. apply zrange_in in Ij. apply oholds_le. cbn [oeval oval]. unfold vBC. rewrite Z.mul_1_l.
    pose proof (ok_sc1 b lbs OK j ltac:(lia)) as S1. pose proof LL_facts as (RL & _).
    destruct (Z.leb_spec j (p_LL prm)).
    + rewrite oeval_app, !oeval_catg.
      rewrite (gsum_ext _ (fun k => -1 * cntL k j) (ks nLC)) by (intros k _; rewrite oeval_scale, oeval_uL; reflexivity).
      rewrite (gsum_ext _ (fun k => -1 * cntD k j) (ks nDC)) by (intros k Hk; apply ks_in in Hk; rewrite oeval_scale, oeval_vD by exact Hk; reflexivity).
      rewrite !gsum_scale. unfold cntL, cntD, countZ in *.
      rewrite (gsum_classesL (fun c => if usedLb b c && (lenL c =? j) then 1 else 0)).
      rewrite (gsum_classesD (fun d => if usedDb b d && (lenD d =? j) then 1 else 0)). lia.
    + cbn [oeval]. enough (countZ (fun c => usedLb b c && (lenL c =? j)) (zrange 0 286) = 0 /\ countZ (fun d => usedDb b d && (lenD d =? j)) (zrange 0 30) = 0) by lia.
      unfold countZ. split; (rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]); intros c Hc; apply zrange_in in Hc.
      * unfold usedLb. destruct (Z.ltb_spec 0 (fL b c)); [|reflexivity]. pose proof (lenL_range c ltac:(lia) ltac:(lia)).
        replace (lenL c =? j) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * destruct (usedDb b c) eqn:U; [|reflexivity]. pose proof (lenD_range c ltac:(lia) U).
        replace (lenD c =? j) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - constructor; [|constructor; [|constructor]]; apply oholds_le.
    + rewrite oeval_app. cbn [oeval oval]. unfold vBC.
      replace (oeval b (map (fun j => (OBC j, 1)) (zrange 1 15))) with (zsum BC 1 15).
      2:{ symmetry. rewrite <- (lsum_zrange BC 1 15). generalize (zrange 1 15). intros l. induction l; [reflexivity|]. cbn [map oeval oval lsum]. unfold vBC. rewrite IHl. lia. }
      pose proof (ok_sc2 b lbs OK). lia.
    + cbn [oeval oval]. unfold vBC. pose proof (ok_sc3 b lbs OK). lia.
Qed.

Lemma run_pieces r : 1 <= r -> is1 r + is2 r + isa r + isb r = 1.
Proof.
  intros Hr. unfold is1, is2, isa, isb, rem138.
  destruct (Z.ltb_spec 138 r); [destruct (Z.eqb_spec (r - 138) 1); destruct (Z.eqb_spec (r - 138) 2) | destruct (Z.eqb_spec r 1); destruct (Z.eqb_spec r 2)];
    try lia; cbn [andb];
    repeat match goal with |- context [?a <=? ?c] => destruct (Z.leb_spec a c); cbn [andb] end; lia.
Qed.
Lemma run_lo r : 1 <= r <= 276 -> is1 r + 2 * is2 r + 3 * isa r + 11 * isb r + 138 * nlong r <= r.
Proof.
  intros Hr. unfold is1, is2, isa, isb, nlong, rem138.
  destruct (Z.ltb_spec 138 r); [destruct (Z.eqb_spec (r - 138) 1); destruct (Z.eqb_spec (r - 138) 2) | destruct (Z.eqb_spec r 1); destruct (Z.eqb_spec r 2)];
    try lia; cbn [andb];
    repeat match goal with |- context [?a <=? ?c] => destruct (Z.leb_spec a c); cbn [andb] end; lia.
Qed.
Lemma run_hi r : 1 <= r <= 276 -> r <= is1 r + 2 * is2 r + 10 * isa r + 138 * isb r + 138 * nlong r.
Proof.
  intros Hr. unfold is1, is2, isa, isb, nlong, rem138.
  destruct (Z.ltb_spec 138 r); [destruct (Z.eqb_spec (r - 138) 1); destruct (Z.eqb_spec (r - 138) 2) | destruct (Z.eqb_spec r 1); destruct (Z.eqb_spec r 2)];
    try lia; cbn [andb];
    repeat match goal with |- context [?a <=? ?c] => destruct (Z.leb_spec a c); cbn [andb] end; lia.
Qed.
Lemma nlong_short r : 1 <= r <= 138 -> nlong r = 0.
Proof. intros. unfold nlong. destruct (Z.ltb_spec 138 r); lia. Qed.
Lemma nlong_nonneg r : 0 <= nlong r. Proof. unfold nlong. destruct (_ <? _); lia. Qed.

Lemma zruns_0 L lo : zruns L lo 0 = [].
Proof. reflexivity. Qed.
Lemma length_lsum (l : list Z) : Z.of_nat (length l) = lsum (fun _ => 1) l.
Proof. induction l; [reflexivity|]. cbn [length lsum]. lia. Qed.

Lemma lmaxc_spec : 256 <= lmaxc b < 286 /\ 0 < fL b (lmaxc b) /\ (forall c, 0 <= c < 286 -> 0 < fL b c -> c <= lmaxc b).
Proof.
  unfold lmaxc. set (Fu := filter (fun c => 0 <? fL b c) (zrange 0 286)).
  assert (IN : forall c, In c Fu <-> 0 <= c < 286 /\ 0 < fL b c).
  { intros c. unfold Fu. rewrite filter_In, zrange_in, Z.ltb_lt. simpl. tauto. }
  assert (I256 : In 256 Fu) by (apply IN; rewrite fL_256; lia).
  destruct (lmax_in (fun c => c) Fu ltac:(intros E; rewrite E in I256; exact I256) ltac:(intros x Hx; apply IN in Hx; lia)) as (x & Ix & Ex).
  pose proof (lmax_ge (fun c => c) Fu 256 I256). apply IN in Ix. rewrite <- Ex. cbv beta in *.
  split; [lia|]. split; [tauto|]. intros c Hc U. pose proof (lmax_ge (fun c => c) Fu c ltac:(apply IN; lia)). cbv beta in *. lia.
Qed.
Lemma dmaxc_spec : 0 <= dmaxc b < 30 /\ usedDb b (dmaxc b) = true /\ (forall d, 0 <= d < 30 -> usedDb b d = true -> d <= dmaxc b).
Proof.
  unfold dmaxc. set (Fu := filter (fun d => (0 <? gD b d) || forcedD b d) (zrange 0 30)).
  assert (IN : forall d, In d Fu <-> 0 <= d < 30 /\ usedDb b d = true).
  { intros d. unfold Fu, usedDb. rewrite filter_In, zrange_in. simpl. tauto. }
  assert (NE : Fu <> []).
  { intros E. pose proof D2 as V2. rewrite vV_used in V2. unfold countZ in V2.
    rewrite (lsum_ext _ (fun _ => 0)) in V2; [rewrite lsum_zero in V2; lia|]. intros d Hd.
    destruct (usedDb b d) eqn:U; [|reflexivity]. exfalso. assert (In d Fu) by (apply IN; apply zrange_in in Hd; split; [lia|exact U]). rewrite E in H. exact H. }
  destruct (lmax_in (fun d => d) Fu NE ltac:(intros x Hx; apply IN in Hx; lia)) as (x & Ix & Ex).
  apply IN in Ix. rewrite <- Ex. cbv beta in *. split; [lia|]. split; [tauto|]. intros d Hd U. pose proof (lmax_ge (fun d => d) Fu d ltac:(apply IN; auto)). cbv beta in *. lia.
Qed.

Lemma lenL_nz c : 0 <= c < 286 -> (lenL c =? 0) = negb (usedLb b c).
Proof.
  intros Hc. unfold usedLb. pose proof (fL_nonneg c). destruct (Z.ltb_spec 0 (fL b c)); cbn.
  - pose proof (lenL_used c Hc ltac:(lia)). apply Z.eqb_neq. lia.
  - apply Z.eqb_eq. apply lenL_unused; lia.
Qed.
Lemma lenD_nz d : 0 <= d < 30 -> (lenD d =? 0) = negb (usedDb b d).
Proof.
  intros Hd. destruct (usedDb b d) eqn:U; cbn.
  - pose proof (lenD_used d Hd U). apply Z.eqb_neq. lia.
  - apply Z.eqb_eq. apply lenD_unused; auto.
Qed.

Lemma runs1_facts :
  lsum (fun _ => 1) (runs1 b) <= vNLITC b + 1
  /\ lsum (fun r => r) (runs1 b) = 256 - vNLITC b
  /\ (forall r, In r (runs1 b) -> 1 <= r <= 257).
Proof.
  unfold runs1.
  assert (E256 : lenL (0 + Z.of_nat 256) <> 0).
  { change (0 + Z.of_nat 256) with 256. pose proof (lenL_used 256 ltac:(lia) ltac:(rewrite fL_256; lia)). lia. }
  assert (SPLIT : forall f, lsum f (zruns lenL 0 257) = lsum f (zruns lenL 0 256)).
  { intros f. change 257%nat with (256 + 1)%nat. rewrite (zruns_split f lenL 0 256 0 E256), zruns_0. cbn [lsum]. lia. }
  assert (NZ : zsum (fun j => zind (negb (lenL j =? 0))) 0 256 = vNLITC b).
  { unfold vNLITC. rewrite countZ_zsum. apply zsum_ext. intros j Hj. rewrite lenL_nz by lia. unfold usedLb, zind. destruct (0 <? fL b j); reflexivity. }
  split; [|split].
  - rewrite SPLIT, <- length_lsum. pose proof (zruns_length lenL 0 256). lia.
  - rewrite SPLIT, zruns_sum. rewrite <- (Z.add_0_l (zsum _ 0 256)).
    transitivity (zsum (fun j => 1 - zind (negb (lenL j =? 0))) 0 256).
    + apply zsum_ext. intros j _. unfold zind. destruct (lenL j =? 0); reflexivity.
    + rewrite (zsum_ext (fun j => 1 - zind (negb (lenL j =? 0))) (fun j => (fun _ => 1) j + (-1) * zind (negb (lenL j =? 0)))) by (intros; lia).
      rewrite zsum_add, zsum_scale, zsum_const1, NZ. lia.
  - intros r Hr. pose proof (zruns_pos lenL 0 257 r Hr). lia.
Qed.

Lemma runs2_facts :
  lsum (fun _ => 1) (runs2 b) <= vNLENC b
  /\ lsum (fun r => r) (runs2 b) = (lmaxc b - 256) - vNLENC b
  /\ (forall r, In r (runs2 b) -> 1 <= r <= 29).
Proof.
  unfold runs2. destruct lmaxc_spec as (RM & UM & MAX).
  assert (NZ : forall n, (lmaxc b - 256 <= Z.of_nat n <= 29)%Z -> zsum (fun j => zind (negb (lenL j =? 0))) 257 n = vNLENC b).
  { intros n Hn. unfold vNLENC. rewrite countZ_zsum.
    replace 29%nat with (n + (29 - n))%nat by lia. rewrite zsum_split.
    rewrite (zsum_0 _ (257 + Z.of_nat n)).
    2:{ intros j Hj. pose proof (fL_nonneg j). destruct (Z.ltb_spec 0 (fL b j)); [|reflexivity]. exfalso. pose proof (MAX j ltac:(lia) ltac:(lia)). lia. }
    rewrite Z.add_0_r. apply zsum_ext. intros j Hj. rewrite lenL_nz by lia. unfold usedLb, zind. destruct (0 <? fL b j); reflexivity. }
  destruct (Z_lt_le_dec 256 (lmaxc b)) as [GT|LE].
  -
    set (n := Z.to_nat (lmaxc b - 257)).
    assert (EN : Z.to_nat (lmaxc b - 256) = (n + 1)%nat) by lia.
    assert (EM : lenL (257 + Z.of_nat n) <> 0).
    { replace (257 + Z.of_nat n) with (lmaxc b) by lia. pose proof (lenL_used (lmaxc b) ltac:(lia) UM). lia. }
    assert (SPLIT : forall f, lsum f (zruns lenL 257 (Z.to_nat (lmaxc b - 256))) = lsum f (zruns lenL 257 n)).
    { intros f. rewrite EN. rewrite (zruns_split f lenL 257 n 0 EM), zruns_0. cbn [lsum]. lia. }
    split; [|split].
    + rewrite SPLIT, <- length_lsum. pose proof (zruns_length lenL 257 n).
      pose proof (NZ (n + 1)%nat ltac:(lia)) as X. rewrite Nat.add_1_r, zsum_snoc in X.
      replace (lenL (257 + Z.of_nat n) =? 0) with false in X by (symmetry; apply Z.eqb_neq; exact EM). cbn [negb zind] in X. lia.
    + rewrite SPLIT, zruns_sum. pose proof (NZ (n + 1)%nat ltac:(lia)) as X. rewrite Nat.add_1_r, zsum_snoc in X.
      replace (lenL (257 + Z.of_nat n) =? 0) with false in X by (symmetry; apply Z.eqb_neq; exact EM). cbn [negb zind] in X.
      transitivity (zsum (fun j => 1 + (-1) * zind (negb (lenL j =? 0))) 257 n); [apply zsum_ext; intros; unfold zind; destruct (lenL _ =? 0); reflexivity|].
      rewrite zsum_add, zsum_scale, zsum_const1. lia.
    + intros r Hr. pose proof (zruns_pos lenL 257 _ r Hr). lia.
  -
    replace (Z.to_nat (lmaxc b - 256)) with 0%nat by lia. rewrite zruns_0. cbn [lsum].
    pose proof (NZ 0%nat ltac:(lia)) as X. cbn [zsum] in X. split; [lia|]. split; [lia|]. intros r F; destruct F.
Qed.

Lemma runs3_facts :
  lsum (fun _ => 1) (runs3 b) <= vV b
  /\ lsum (fun r => r) (runs3 b) = (dmaxc b + 1) - vV b
  /\ (forall r, In r (runs3 b) -> 1 <= r <= 30).
Proof.
  unfold runs3. destruct dmaxc_spec as (RM & UM & MAX).
  set (n := Z.to_nat (dmaxc b)).
  assert (EN : Z.to_nat (dmaxc b + 1) = (n + 1)%nat) by lia.
  assert (EM : lenD (0 + Z.of_nat n) <> 0).
  { replace (0 + Z.of_nat n) with (dmaxc b) by lia. pose proof (lenD_used (dmaxc b) ltac:(lia) UM). lia. }
  assert (SPLIT : forall f, lsum f (zruns lenD 0 (Z.to_nat (dmaxc b + 1))) = lsum f (zruns lenD 0 n)).
  { intros f. rewrite EN. rewrite (zruns_split f lenD 0 n 0 EM), zruns_0. cbn [lsum]. lia. }
  assert (NZ : zsum (fun j => zind (negb (lenD j =? 0))) 0 (n + 1) = vV b).
  { rewrite vV_used, countZ_zsum. replace 30%nat with ((n + 1) + (29 - n))%nat by lia. rewrite (zsum_split _ 0 (n + 1) (29 - n)).
    rewrite (zsum_0 _ (0 + Z.of_nat (n + 1))).
    2:{ intros j Hj. destruct (usedDb b j) eqn:U; [|reflexivity]. exfalso. pose proof (MAX j ltac:(lia) U). lia. }
    rewrite Z.add_0_r. apply zsum_ext. intros j Hj. rewrite lenD_nz by lia. unfold zind. destruct (usedDb b j); reflexivity. }
  rewrite Nat.add_1_r, zsum_snoc in NZ.
  replace (lenD (0 + Z.of_nat n) =? 0) with false in NZ by (symmetry; apply Z.eqb_neq; exact EM). cbn [negb zind] in NZ.
  split; [|split].
  - rewrite SPLIT, <- length_lsum. pose proof (zruns_length lenD 0 n). lia.
  - rewrite SPLIT, zruns_sum.
    transitivity (zsum (fun j => 1 + (-1) * zind (negb (lenD j =? 0))) 0 n); [apply zsum_ext; intros; unfold zind; destruct (lenD _ =? 0); reflexivity|].
    rewrite zsum_add, zsum_scale, zsum_const1. lia.
  - intros r Hr. pose proof (zruns_pos lenD 0 _ r Hr). lia.
Qed.

Lemma pieces_count (l : list Z) : (forall r, In r l -> 1 <= r) ->
  lsum is1 l + lsum is2 l + lsum isa l + lsum isb l = lsum (fun _ => 1) l.
Proof. intros H. rewrite <- !lsum_add. apply lsum_ext. intros r Hr. apply run_pieces. apply H. exact Hr. Qed.
Lemma pieces_lo (l : list Z) : (forall r, In r l -> 1 <= r <= 276) ->
  lsum is1 l + 2 * lsum is2 l + 3 * lsum isa l + 11 * lsum isb l + 138 * lsum nlong l <= lsum (fun r => r) l.
Proof. intros H. rewrite <- !lsum_scale, <- !lsum_add. apply lsum_le. intros r Hr. pose proof (run_lo r (H r Hr)). lia. Qed.
Lemma pieces_hi (l : list Z) : (forall r, In r l -> 1 <= r <= 276) ->
  lsum (fun r => r) l <= lsum is1 l + 2 * lsum is2 l + 10 * lsum isa l + 138 * lsum isb l + 138 * lsum nlong l.
Proof. intros H. rewrite <- !lsum_scale, <- !lsum_add. apply lsum_le. intros r Hr. pose proof (run_hi r (H r Hr)). lia. Qed.
Lemma nlong_zero (l : list Z) : (forall r, In r l -> 1 <= r <= 138) -> lsum nlong l = 0.
Proof. intros H. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros r Hr. apply nlong_short. auto. Qed.

Lemma reg1 : vR1 b 1 + vR2 b 1 + vRA b 1 + vRB b 1 <= vNLITC b + 1
  /\ vR1 b 1 + 2 * vR2 b 1 + 3 * vRA b 1 + 11 * vRB b 1 + 138 * vRLONG b <= 256 - vNLITC b
  /\ 256 - vNLITC b <= vR1 b 1 + 2 * vR2 b 1 + 10 * vRA b 1 + 138 * vRB b 1 + 138 * vRLONG b
  /\ 0 <= vRLONG b.
Proof.
  destruct runs1_facts as (A1 & A2 & A3). destruct runs2_facts as (B1 & B2 & B3). destruct runs3_facts as (C1 & C2 & C3).
  pose proof (pieces_count (runs1 b) ltac:(intros r Hr; pose proof (A3 r Hr); lia)) as P1.
  pose proof (pieces_lo (runs1 b) ltac:(intros r Hr; pose proof (A3 r Hr); lia)) as L1.
  pose proof (pieces_hi (runs1 b) ltac:(intros r Hr; pose proof (A3 r Hr); lia)) as H1.
  pose proof (nlong_zero (runs2 b) ltac:(intros r Hr; pose proof (B3 r Hr); lia)) as N2.
  pose proof (nlong_zero (runs3 b) ltac:(intros r Hr; pose proof (C3 r Hr); lia)) as N3.
  pose proof (lsum_nonneg nlong (runs1 b) ltac:(intros; apply nlong_nonneg)) as N1.
  assert (R1 : runs_of b 1 = runs1 b) by reflexivity.
  unfold vR1, vR2, vRA, vRB, vRLONG. rewrite R1. lia.
Qed.
Lemma reg2 : vR1 b 2 + vR2 b 2 + vRA b 2 + vRB b 2 <= vNLENC b
  /\ vR1 b 2 + 2 * vR2 b 2 + 3 * vRA b 2 + 11 * vRB b 2 + vNLENC b <= 29.
Proof.
  destruct runs2_facts as (B1 & B2 & B3). destruct lmaxc_spec as (RM & _).
  pose proof (pieces_count (runs2 b) ltac:(intros r Hr; pose proof (B3 r Hr); lia)) as P2.
  pose proof (pieces_lo (runs2 b) ltac:(intros r Hr; pose proof (B3 r Hr); lia)) as L2.
  pose proof (lsum_nonneg nlong (runs2 b) ltac:(intros; apply nlong_nonneg)) as N2.
  assert (R2 : runs_of b 2 = runs2 b) by reflexivity.
  unfold vR1, vR2, vRA, vRB. rewrite R2. lia.
Qed.
Lemma reg3 : vR1 b 3 + vR2 b 3 + vRA b 3 + vRB b 3 <= vV b
  /\ vR1 b 3 + 2 * vR2 b 3 + 3 * vRA b 3 + 11 * vRB b 3 + vV b <= 30.
Proof.
  destruct runs3_facts as (C1 & C2 & C3). destruct dmaxc_spec as (RD & _).
  pose proof (pieces_count (runs3 b) ltac:(intros r Hr; pose proof (C3 r Hr); lia)) as P3.
  pose proof (pieces_lo (runs3 b) ltac:(intros r Hr; pose proof (C3 r Hr); lia)) as L3.
  pose proof (lsum_nonneg nlong (runs3 b) ltac:(intros; apply nlong_nonneg)) as N3.
  assert (R3 : runs_of b 3 = runs3 b) by reflexivity.
  unfold vR1, vR2, vRA, vRB. rewrite R3. lia.
Qed.

Lemma rows_runs_sound : Forall (oholds b) rows_runs.
Proof.
  unfold rows_runs.
  pose proof reg1 as (A1 & A2 & A3 & A4). pose proof reg2 as (B1 & B2). pose proof reg3 as (C1 & C2).
  pose proof (ok_sc4a b lbs OK) as S4a. pose proof (ok_sc4b b lbs OK) as S4b. pose proof (ok_sc4c b lbs OK) as S4c.
  assert (WBrow : oeval b (map (fun x => (OBC x, 1)) (zrange 0 19)) = zsum BC 0 19).
  { rewrite <- (lsum_zrange BC 0 19). generalize (zrange 0 19). intros l. induction l; [reflexivity|]. cbn [map oeval oval lsum]. unfold vBC. rewrite IHl. lia. }
  repeat apply Forall_cons; try apply Forall_nil;
    first [apply oholds_le | apply oholds_ge | apply oholds_eq]; rewrite ?oeval_app; cbn [oeval oval];
    unfold vBC, vWB; rewrite ?WBrow; lia.
Qed.



Lemma tmax_ge tau k : 0 <= tmax tau /\ nth k tau 0 <= tmax tau.
Proof.
  revert k. induction tau as [|t r IH]; intros k; cbn [tmax fold_right nth].
  - destruct k; cbn; lia.
  - fold (tmax r). destruct k as [|k]; [pose proof (IH 0%nat); lia|]. pose proof (IH k). lia.
Qed.

Lemma oeval_mapBC (c : Z -> Z) : oeval b (map (fun x => (OBC x, c x)) (zrange 0 19)) = zsum (fun x => c x * BC x) 0 19.
Proof.
  rewrite <- (lsum_zrange (fun x => c x * BC x) 0 19). generalize (zrange 0 19). intros l.
  induction l; [reflexivity|]. cbn [map oeval oval lsum]. unfold vBC. rewrite IHl. reflexivity.
Qed.

Lemma WB_nonneg : 0 <= vWB b.
Proof. unfold vWB. apply zsum_nonneg. intros; apply BC_nonneg; lia. Qed.
Lemma zsum_WB (f : Z -> Z) : (forall x, f x = BC x) -> zsum f 0 19 = vWB b.
Proof. intros E. unfold vWB. apply zsum_ext. intros; apply E. Qed.

Lemma bl_used_count : zsum (fun x => if BC' b x =? 0 then 0 else 1) 0 19 <= Kbl_of LL.
Proof.
  unfold Kbl_of. pose proof LL_facts as (RL & _). destruct (Z.leb_spec LL 9).
  - change 19%nat with (10 + (6 + 3))%nat. rewrite !zsum_split.
    rewrite (zsum_0 _ (0 + Z.of_nat 10) 6).
    2:{ intros x Hx. rewrite BC'_eq. destruct bforced_facts as (_ & _ & FF).
        replace (existsb (Z.eqb x) (ob_bforced b)) with false.
        2:{ symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_In in X. destruct (ok_TB b lbs OK) as (zB & TF & _).
            destruct (tFl zB 19 7 BC (ob_bforced b) TF) as (_ & _ & C). destruct (C x X). lia. }
        pose proof (ok_sc1 b lbs OK x ltac:(lia)) as S1. pose proof (BC_nonneg x ltac:(lia)) as S0.
        enough (CC : countZ (fun c => usedLb b c && (lenL c =? x)) (zrange 0 286) = 0 /\ countZ (fun d => usedDb b d && (lenD d =? x)) (zrange 0 30) = 0).
        { destruct CC as [C1 C2]. rewrite C1, C2 in S1. replace (BC x) with 0 by lia. reflexivity. }
        unfold countZ. split; (rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]); intros c Hc; apply zrange_in in Hc.
        * unfold usedLb. destruct (Z.ltb_spec 0 (fL b c)); [|reflexivity]. pose proof (lenL_range c ltac:(lia) ltac:(lia)).
          replace (lenL c =? x) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        * destruct (usedDb b c) eqn:U; [|reflexivity]. pose proof (lenD_range c ltac:(lia) U).
          replace (lenD c =? x) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    pose proof (zsum_mono (fun x => if BC' b x =? 0 then 0 else 1) (fun _ => 1) 0 10 ltac:(intros; cbv beta; destruct (_ =? 0); lia)).
    pose proof (zsum_mono (fun x => if BC' b x =? 0 then 0 else 1) (fun _ => 1) (0 + Z.of_nat 10 + Z.of_nat 6) 3 ltac:(intros; cbv beta; destruct (_ =? 0); lia)).
    rewrite !zsum_const1 in *. lia.
  - pose proof (zsum_mono (fun x => if BC' b x =? 0 then 0 else 1) (fun _ => 1) 0 19 ltac:(intros; cbv beta; destruct (_ =? 0); lia)).
    rewrite zsum_const1 in H0. lia.
Qed.

Lemma row_tpl_sound tau : tpl_okb tau = true -> oholds b (row_tpl prm tau).
Proof.
  intros TOK. unfold tpl_okb in TOK. apply andb_prop in TOK. destruct TOK as [T1 T2].
  rewrite forallb_forall in T1. apply Z.leb_le in T2.
  assert (TR : forall x, 0 <= x < 19 -> 1 <= nth (Z.to_nat x) tau 0 <= KT).
  { intros x Hx. specialize (T1 x ltac:(apply zrange_in; lia)). apply andb_prop in T1. destruct T1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia. }
  pose (tauf := fun x => nth (Z.to_nat x) tau 0).
  unfold row_tpl. apply oholds_le. cbn [oeval oval]. rewrite (oeval_mapBC (fun x => - (p_rden prm * nth (Z.to_nat x) tau 0 + p_rnum prm))).
  pose proof (po_rho prm _ b PRM) as RHO. pose proof (po_dmg prm _ b PRM) as DMG.
  destruct (rho_of (p_LL prm)) as [rnum rden] eqn:ERHO. cbn [fst snd] in DMG.
  assert (Ern : p_rnum prm = rnum) by congruence. assert (Erd : p_rden prm = rden) by congruence. rewrite Ern, Erd in *. clear RHO Ern Erd.
  pose proof (dmg_cert_pos _ _ _ DMG) as [Rn Rd].
  destruct (ok_TB b lbs OK) as (zB & TF & _ & EB).
  pose proof (WB'_le) as [W1 W2]. pose proof WB'_eq as WE.
  assert (GW : g_W (zt_g zB) = zsum (BC' b) 0 19) by (symmetry; exact (sumW zB 19 7 BC (ob_bforced b) TF)).
  pose proof (bl_damage zB BC (ob_bforced b) (Kbl_of LL) rnum rden TF DMG ltac:(rewrite GW; change (fib 14) with 377; lia) bl_used_count) as D.
  fold (BC' b) in D. rewrite GW in D.
  pose proof (topt zB 19 7 BC (ob_bforced b) TF KT tauf ltac:(unfold KT; lia) ltac:(intros c Hc _; pose proof (TR c Hc); unfold tauf; lia)) as O.
  fold (BC' b) in O. change (Z.to_nat 19) with 19%nat in *.
  specialize (O ltac:(etransitivity; [|exact T2]; apply zsum_mono; intros x Hx; cbv beta; unfold tauf; pose proof (pow2_pos (KT - nth (Z.to_nat x) tau 0) ltac:(pose proof (TR x ltac:(lia)); lia)); destruct (_ =? 0); lia)).
  assert (B1 : vB b <= zsum (fun x => BC' b x * zt_len zB x) 0 19).
  { unfold vB. apply zsum_mono. intros x Hx. rewrite <- EB by lia. pose proof (BC_le_BC' x). pose proof (BD_range x ltac:(lia)). pose proof (BC_nonneg x ltac:(lia)). nia. }
  assert (B2 : zsum (fun x => BC' b x * tauf x) 0 19 <= zsum (fun x => tauf x * BC x) 0 19 + 2 * tmax tau).
  { rewrite (zsum_ext (fun x => BC' b x * tauf x) (fun x => tauf x * BC x + tauf x * (BC' b x - BC x))) by (intros; lia).
    rewrite zsum_add.
    pose proof (zsum_mono (fun x => tauf x * (BC' b x - BC x)) (fun x => tmax tau * (BC' b x - BC x)) 0 19
      ltac:(intros x Hx; cbv beta; pose proof (BC_le_BC' x); pose proof (tmax_ge tau (Z.to_nat x)); unfold tauf; nia)).
    rewrite zsum_scale in H.
    rewrite (zsum_ext (fun x => BC' b x - BC x) (fun x => BC' b x + (-1) * BC x)) in H by (intros; lia).
    rewrite zsum_add, zsum_scale in H. rewrite (zsum_WB BC) in H by reflexivity. pose proof (tmax_ge tau 0) as [T0 _].
    assert (M2 : tmax tau * (zsum (BC' b) 0 19 + -1 * vWB b) <= tmax tau * 2) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  rewrite (zsum_ext (fun x => - (rden * nth (Z.to_nat x) tau 0 + rnum) * BC x) (fun x => (- rden) * (tauf x * BC x) + (- rnum) * BC x)) by (intros; unfold tauf; lia).
  rewrite zsum_add, !zsum_scale. rewrite ?(zsum_WB BC), ?(zsum_WB (fun x => BC x)) by reflexivity. pose proof (tmax_ge tau 0) as [T0 _].
  assert (M1 : rden * vB b <= rden * zsum (fun x => BC' b x * zt_len zB x) 0 19) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M3 : rden * zsum (fun x => BC' b x * tdepth zB x) 0 19 <= rden * (zsum (fun x => tauf x * BC x) 0 19 + 2 * tmax tau)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M4 : rnum * zsum (BC' b) 0 19 <= rnum * (vWB b + 2)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Lemma rows_tpl_sound T : forallb tpl_okb T = true -> Forall (oholds b) (map (row_tpl prm) T).
Proof. intros H. apply Forall_map_iff. rewrite forallb_forall in H. intros tau I. apply row_tpl_sound. apply H. exact I. Qed.

Lemma xb_sum : zsum (fun x => BC x * (BD x + xb_of_bl x)) 0 19 = vB b + 2 * BC 16 + 3 * BC 17 + 7 * BC 18.
Proof.
  rewrite (zsum_ext _ (fun x => BC x * BD x + BC x * xb_of_bl x)) by (intros; lia). rewrite zsum_add. unfold vB.
  enough (E : zsum (fun x => BC x * xb_of_bl x) 0 19 = 2 * BC 16 + 3 * BC 17 + 7 * BC 18) by lia.
  change 19%nat with (16 + 3)%nat. rewrite zsum_split. rewrite (zsum_0 _ 0 16).
  2:{ intros x Hx. unfold xb_of_bl. replace (x =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (x =? 17) with false by (symmetry; apply Z.eqb_neq; lia). replace (x =? 18) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
  cbn [zsum Z.of_nat Pos.of_succ_nat Pos.succ]. unfold xb_of_bl.
  change (0 + 16 + 0) with 16. change (0 + 16 + 1) with 17. change (0 + 16 + 2) with 18. cbn [Z.eqb Pos.eqb]. lia.
Qed.

Lemma Hc1_bounds : 0 <= ob_Hc1 b /\ ob_Hc1 b = 14 + 3 * ob_blcodes b + vB b + 2 * BC 16 + 3 * BC 17 + 7 * BC 18 /\ 0 <= vB b <= 7 * vWB b.
Proof.
  pose proof (ok_Hc1 b lbs OK) as E. rewrite xb_sum in E. pose proof (ok_blc b lbs OK) as [BL _].
  pose proof (BC_nonneg 16 ltac:(lia)). pose proof (BC_nonneg 17 ltac:(lia)). pose proof (BC_nonneg 18 ltac:(lia)).
  assert (0 <= vB b <= 7 * vWB b).
  { unfold vB, vWB. rewrite <- zsum_scale. split.
    - apply zsum_nonneg. intros x Hx. pose proof (BC_nonneg x ltac:(lia)). pose proof (BD_range x ltac:(lia)). nia.
    - apply zsum_mono. intros x Hx. pose proof (BC_nonneg x ltac:(lia)). pose proof (BD_range x ltac:(lia)). nia. }
  lia.
Qed.

Lemma rows_hdr_sound : Forall (oholds b) (rows_hdr prm).
Proof.
  unfold rows_hdr. pose proof Hc1_bounds as (H0 & HE & HB). pose proof (ok_blc b lbs OK) as [BL B15].
  constructor; [|constructor; [|constructor]]; apply oholds_le; cbn [oeval oval]; unfold vH, vBC.
  - rewrite (po_blc prm _ b PRM). pose proof LL_facts as (RL & _).
    destruct (Z.leb_spec (p_LL prm) 14); [|lia].
    enough (BD 15 = 0) by (specialize (B15 H1); lia).
    apply BD_unused; [lia|]. rewrite BC'_eq.
    replace (existsb (Z.eqb 15) (ob_bforced b)) with false.
    2:{ symmetry. apply Bool.not_true_iff_false. intros X. apply existsb_In in X. destruct (ok_TB b lbs OK) as (zB & TF & _).
        destruct (tFl zB 19 7 BC (ob_bforced b) TF) as (_ & _ & C). destruct (C 15 X). lia. }
    pose proof (ok_sc1 b lbs OK 15 ltac:(lia)) as S1. pose proof (BC_nonneg 15 ltac:(lia)).
    enough (countZ (fun c => usedLb b c && (lenL c =? 15)) (zrange 0 286) = 0 /\ countZ (fun d => usedDb b d && (lenD d =? 15)) (zrange 0 30) = 0) by lia.
    unfold countZ. split; (rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]); intros c Hc; apply zrange_in in Hc.
    + unfold usedLb. destruct (Z.ltb_spec 0 (fL b c)); [|reflexivity]. pose proof (lenL_range c ltac:(lia) ltac:(lia)).
      replace (lenL c =? 15) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + destruct (usedDb b c) eqn:U; [|reflexivity]. pose proof (lenD_range c ltac:(lia) U).
      replace (lenD c =? 15) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - unfold vSV. pose proof (ok_dyn b lbs OK) as DY.
    rewrite (ssum_ext (fun s0 => scostS s0 - dcostS b s0) (fun s0 => scostS s0 + (-1) * dcostS b s0)) by (intros; lia).
    rewrite ssum_add, ssum_scale. lia.
Qed.


Lemma pieces_nonneg (l : list Z) : 0 <= lsum is1 l /\ 0 <= lsum is2 l /\ 0 <= lsum isa l /\ 0 <= lsum isb l
  /\ lsum is1 l <= lsum (fun _ => 1) l /\ lsum is2 l <= lsum (fun _ => 1) l /\ lsum isa l <= lsum (fun _ => 1) l /\ lsum isb l <= lsum (fun _ => 1) l.
Proof.
  unfold is1, is2, isa, isb. repeat split; (apply lsum_nonneg || apply lsum_le); intros; destruct (_ : bool); lia.
Qed.
Lemma var_ok_R r : (0 <= vR1 b r <= 316) /\ (0 <= vR2 b r <= 316) /\ (0 <= vRA b r <= 316) /\ (0 <= vRB b r <= 316).
Proof.
  destruct runs1_facts as (D1 & _). destruct runs2_facts as (D2 & _). destruct runs3_facts as (D3 & _).
  pose proof (pieces_nonneg (runs1 b)) as P1. pose proof (pieces_nonneg (runs2 b)) as P2. pose proof (pieces_nonneg (runs3 b)) as P3.
  assert (NL : vNLITC b <= 256) by (unfold vNLITC; pose proof (countZ_le_len (fun c => 0 <? fL b c) (zrange 0 256)); rewrite ?zrange_length in *; lia).
  assert (NE : vNLENC b <= 29) by (unfold vNLENC; pose proof (countZ_le_len (fun c => 0 <? fL b c) (zrange 257 29)); rewrite ?zrange_length in *; lia).
  assert (NV : vV b <= 32) by (rewrite vV_used; destruct forced_facts as (_ & LF & _); pose proof (countZ_le_len (usedDb b) (zrange 0 30)); rewrite ?zrange_length in *; lia).
  assert (R : runs_of b r = runs1 b \/ runs_of b r = runs2 b \/ runs_of b r = runs3 b).
  { unfold runs_of. destruct (r =? 1); [auto|]. destruct (r =? 2); auto. }
  unfold vR1, vR2, vRA, vRB. destruct R as [R|[R|R]]; rewrite R; lia.
Qed.


Lemma lclass_len k : Z.of_nat (length (lc_codes (lcl k))) <= 144.
Proof.
  enough ((length (lc_codes (lcl k)) <= 144)%nat) by lia.
  unfold lcl. destruct (le_lt_dec 11 k) as [GE|LT].
  - rewrite nth_overflow by (cbn; lia). cbn. lia.
  - do 11 (destruct k as [|k]; [vm_compute; lia|]). lia.
Qed.
Lemma dclass_len k : Z.of_nat (length (dc_codes (dcl k))) <= 4.
Proof.
  enough ((length (dc_codes (dcl k)) <= 4)%nat) by lia.
  unfold dcl. destruct (le_lt_dec 14 k) as [GE|LT].
  - rewrite nth_overflow by (cbn; lia). cbn. lia.
  - do 14 (destruct k as [|k]; [vm_compute; lia|]). lia.
Qed.
Lemma lclass_nil k : (nLC <= k)%nat -> lc_codes (lcl k) = [].
Proof. intros. unfold lcl. rewrite nth_overflow by (cbn; unfold nLC in *; lia). reflexivity. Qed.
Lemma dclass_nil k : (nDC <= k)%nat -> dc_codes (dcl k) = [].
Proof. intros. unfold dcl. rewrite nth_overflow by (cbn; unfold nDC in *; lia). reflexivity. Qed.

Lemma class_fL_le k : lsum (fL b) (lc_codes (lcl k)) <= NSYM b + 1.
Proof.
  destruct (le_lt_dec nLC k) as [GE|LT]; [rewrite lclass_nil by exact GE; cbn; pose proof (ok_N b _ OK); lia|].
  rewrite <- WL_eq. unfold WL. rewrite <- (gsum_classesL (fL b)).
  apply (gsum_ge_member (fun k => lsum (fL b) (lc_codes (lcl k))) (ks nLC) k).
  - intros k' _. apply lsum_nonneg. intros; apply fL_nonneg.
  - apply ks_in. exact LT.
Qed.
Lemma class_gD_le k : lsum (gD b) (dc_codes (dcl k)) <= vP b.
Proof.
  destruct (le_lt_dec nDC k) as [GE|LT]; [rewrite dclass_nil by exact GE; cbn; unfold vP; pose proof (scount_nonneg (fun s => match s with OLit _ => false | OPair _ _ => true end) syms); lia|].
  rewrite <- sum_gD. rewrite <- (gsum_classesD (gD b)).
  apply (gsum_ge_member (fun k => lsum (gD b) (dc_codes (dcl k))) (ks nDC) k).
  - intros k' _. apply lsum_nonneg. intros; apply gD_nonneg.
  - apply ks_in. exact LT.
Qed.

Lemma costs_range s0 : In s0 syms -> 0 <= dcostS b s0 <= 48 /\ 0 <= scostS s0 <= 31 /\ 0 <= exS b s0 <= 24.
Proof.
  intros I. pose proof (in_syms_fL _ I) as U.
  destruct (keyL_range s0 I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [dcostS scostS keyL] in *; unfold exS; cbn [dcostS].
  - pose proof (lenL_used c ltac:(lia) ltac:(lia)). unfold sl_of_code. destruct (Z.ltb_spec c 144); destruct (Z.ltb_spec c 256); destruct (Z.ltb_spec c 280); lia.
  - pose proof (lenL_used lc ltac:(lia) ltac:(lia)). pose proof (in_syms_gD _ _ I) as UD.
    pose proof (lenD_used dc ltac:(lia) ltac:(unfold usedDb; rewrite (proj2 (Z.ltb_lt 0 (gD b dc))) by lia; reflexivity)).
    assert (XL : 0 <= xl_of_lcode lc <= 5).
    { unfold xl_of_lcode. clear - R. assert (Hn : (Z.to_nat (lc - 257) < 29)%nat) by lia.
      generalize dependent (Z.to_nat (lc - 257)). intros n Hn. do 29 (destruct n as [|n]; [cbn; lia|]). lia. }
    assert (XD : 0 <= xd_of_dcode dc <= 13).
    { unfold xd_of_dcode. clear - Rd. assert (Hn : (Z.to_nat dc < 30)%nat) by lia.
      generalize dependent (Z.to_nat dc). intros n Hn. do 30 (destruct n as [|n]; [cbn; lia|]). lia. }
    unfold sl_of_code. destruct (Z.ltb_spec lc 144); destruct (Z.ltb_spec lc 256); destruct (Z.ltb_spec lc 280); lia.
Qed.

Lemma ssum_bound (f : osym -> Z) (lo hi : Z) : (forall s0, In s0 syms -> lo <= f s0 <= hi) -> lo * NSYM b <= ssum f syms <= hi * NSYM b.
Proof.
  intros H. unfold NSYM. induction (ob_syms b) as [|x r IH]; [cbn; lia|].
  cbn [ssum length]. rewrite Nat2Z.inj_succ. pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Lemma var_ok v : vwfb v = true -> 0 <= oval b v <= ubound prm v.
Proof.
  intros WFv. pose proof (ok_N b _ OK) as HN. pose proof (po_lbs prm _ b PRM) as PL. pose proof (ok_lbs b _ OK) as L128.
  pose proof Hc1_bounds as (H0 & HE & HB). pose proof WB'_le as [_ W316].
  assert (BCle : forall x, 0 <= x < 19 -> 0 <= BC x <= vWB b).
  { intros x Hx. pose proof (BC_nonneg x Hx). split; [lia|]. unfold vWB. apply (zsum_ge_point BC 0 19 x); [|lia]. intros i Hi. apply BC_nonneg. lia. }
  destruct v; cbn [oval ubound vwfb] in *.
  - unfold vU1, cellL. pose proof (countZ_nonneg (fun c => (fL b c =? 1) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (countZ_le_len (fun c => (fL b c =? 1) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (lclass_len k). lia.
  - unfold vU2, cellL. pose proof (countZ_nonneg (fun c => (fL b c =? 2) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (countZ_le_len (fun c => (fL b c =? 2) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (lclass_len k). lia.
  - unfold vU3, cellL. pose proof (countZ_nonneg (fun c => (3 <=? fL b c) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (countZ_le_len (fun c => (3 <=? fL b c) && (lenL c =? l)) (lc_codes (lcl k))). pose proof (lclass_len k). lia.
  - unfold vF3. pose proof (class_fL_le k). split.
    + apply lsum_nonneg. intros c _. pose proof (fL_nonneg c). destruct (_ && _); lia.
    + etransitivity; [|etransitivity; [exact H|lia]]. apply lsum_le. intros c _. pose proof (fL_nonneg c). destruct (_ && _); lia.
  - unfold vV1, cellD. pose proof (countZ_nonneg (fun d => (gD b d =? 1) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (countZ_le_len (fun d => (gD b d =? 1) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (dclass_len k). lia.
  - unfold vV2, cellD. pose proof (countZ_nonneg (fun d => (gD b d =? 2) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (countZ_le_len (fun d => (gD b d =? 2) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (dclass_len k). lia.
  - unfold vV3, cellD. pose proof (countZ_nonneg (fun d => (3 <=? gD b d) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (countZ_le_len (fun d => (3 <=? gD b d) && (lenD d =? m)) (dc_codes (dcl k))). pose proof (dclass_len k). lia.
  - unfold vG3. pose proof (class_gD_le k). unfold vP in *. pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). unfold NSYM in *. split.
    + apply lsum_nonneg. intros d _. pose proof (gD_nonneg d). destruct (_ && _); lia.
    + etransitivity; [|etransitivity; [exact H|lia]]. apply lsum_le. intros d _. pose proof (gD_nonneg d). destruct (_ && _); lia.
  - unfold vVF. destruct forced_facts as (_ & LF & _). pose proof (countZ_nonneg (fun d => lenD d =? m) (ob_forced b)). pose proof (countZ_le_len (fun d => lenD d =? m) (ob_forced b)). lia.
  - unfold vP. pose proof (scount_nonneg (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). unfold NSYM in *. lia.
  - unfold vNLIT. pose proof (scount_nonneg (fun s => match s with OLit _ => true | OPair _ _ => false end) syms). pose proof (scount_le_len (fun s => match s with OLit _ => true | OPair _ _ => false end) syms). unfold NSYM in *. lia.
  - unfold NSYM in *. lia.
  - pose proof (ok_dyn b lbs OK) as DY. unfold vSV.
    rewrite (ssum_ext (fun s0 => scostS s0 - dcostS b s0) (fun s0 => scostS s0 + (-1) * dcostS b s0)) by (intros; lia). rewrite ssum_add, ssum_scale.
    pose proof (ssum_bound scostS 0 31 ltac:(intros s0 I0; pose proof (costs_range s0 I0); lia)).
    pose proof (ssum_bound (dcostS b) 0 48 ltac:(intros s0 I0; pose proof (costs_range s0 I0); lia)).
    pose proof (lenL_used 256 ltac:(lia) ltac:(rewrite fL_256; lia)). lia.
  - unfold vEX. pose proof (ssum_bound (exS b) 0 24 ltac:(intros s0 I0; pose proof (costs_range s0 I0); lia)). lia.
  - unfold vH. pose proof (BCle 16 ltac:(lia)). pose proof (BCle 17 ltac:(lia)). pose proof (BCle 18 ltac:(lia)). pose proof (ok_blc b lbs OK) as [BL _].
    change (2 ^ 18) with 262144. lia.
  - unfold vU. pose proof (countZ_nonneg (fun c => 0 <? fL b c) (zrange 0 286)). pose proof (countZ_le_len (fun c => 0 <? fL b c) (zrange 0 286)). rewrite ?zrange_length in *. lia.
  - rewrite vV_used. destruct forced_facts as (_ & LF & _). pose proof (countZ_nonneg (usedDb b) (zrange 0 30)). pose proof (countZ_le_len (usedDb b) (zrange 0 30)). rewrite ?zrange_length in *. lia.
  - unfold vNLITC. pose proof (countZ_nonneg (fun c => 0 <? fL b c) (zrange 0 256)). pose proof (countZ_le_len (fun c => 0 <? fL b c) (zrange 0 256)). rewrite ?zrange_length in *. lia.
  - unfold vNLENC. pose proof (countZ_nonneg (fun c => 0 <? fL b c) (zrange 257 29)). pose proof (countZ_le_len (fun c => 0 <? fL b c) (zrange 257 29)). rewrite ?zrange_length in *. lia.
  - unfold vPI. pose proof (scount_nonneg (fun s => (pairA b s =? a) && (pairB b s =? c)) syms). pose proof (scount_le_len (fun s => (pairA b s =? a) && (pairB b s =? c)) syms). unfold NSYM in *. lia.
  - unfold vBC. apply andb_prop in WFv. destruct WFv as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. pose proof (BCle x ltac:(lia)). lia.
  - pose proof WB_nonneg. lia.
  - lia.
  - pose proof reg1 as (A1 & A2 & A3 & A4). pose proof reg2 as (B1 & B2). pose proof reg3 as (C1 & C2). destruct runs1_facts as (D1 & _). destruct runs2_facts as (D2' & _). destruct runs3_facts as (D3 & _).
    pose proof (var_ok_R r) as X. exact (proj1 X).
  - pose proof (var_ok_R r) as X. exact (proj1 (proj2 X)).
  - pose proof (var_ok_R r) as X. exact (proj1 (proj2 (proj2 X))).
  - pose proof (var_ok_R r) as X. exact (proj2 (proj2 (proj2 X))).
  - pose proof reg1 as (A1 & A2 & A3 & A4). pose proof (var_ok_R 1) as X. lia.
Qed.


Theorem orows_sound T : forallb tpl_okb T = true -> forallb vwfb (all_vars prm) = true -> Forall (oholds b) (orows prm T).
Proof.
  intros HT HV. unfold orows.
  apply Forall_app2; [apply rows_class_sound|]. apply Forall_app2; [apply rows_dmin_sound|].
  apply Forall_app2; [apply rows_cells_sound|]. apply Forall_app2; [apply rows_kraft_sound|].
  apply Forall_app2; [apply rows_defs_sound|]. apply Forall_app2; [apply rows_case_sound|].
  apply Forall_app2; [apply rows_ex_sound|]. apply Forall_app2; [apply rows_bc_sound|].
  apply Forall_app2; [apply rows_runs_sound|]. apply Forall_app2; [apply rows_tpl_sound; exact HT|].
  apply Forall_app2; [apply rows_hdr_sound|].
  apply Forall_map_iff. intros v Iv. apply oholds_le. cbn [oeval]. rewrite forallb_forall in HV. pose proof (var_ok v (HV v Iv)). lia.
Qed.

Lemma index_of_ge v vs : forall i, (Pos.to_nat i <= Pos.to_nat (index_of v vs i))%nat.
Proof. induction vs as [|w r IH]; intros i; cbn [index_of]; [lia|]. destruct (ovar_eqb v w); [lia|]. specialize (IH (Pos.succ i)). rewrite Pos2Nat.inj_succ in IH. lia. Qed.

Lemma index_of_nth v vs : forall i, (Pos.to_nat (index_of v vs i) < Pos.to_nat i + length vs)%nat ->
  nth (Pos.to_nat (index_of v vs i) - Pos.to_nat i) vs OP = v.
Proof.
  induction vs as [|w r IH]; intros i H; cbn [index_of length] in *; [lia|].
  destruct (ovar_eqb v w) eqn:E.
  - apply ovar_eqb_eq in E. subst. rewrite Nat.sub_diag. reflexivity.
  - pose proof (index_of_ge v r (Pos.succ i)) as G. rewrite Pos2Nat.inj_succ in G.
    specialize (IH (Pos.succ i) ltac:(rewrite Pos2Nat.inj_succ; lia)). rewrite Pos2Nat.inj_succ in IH.
    replace (Pos.to_nat (index_of v r (Pos.succ i)) - Pos.to_nat i)%nat with (S (Pos.to_nat (index_of v r (Pos.succ i)) - S (Pos.to_nat i)))%nat by lia.
    cbn [nth]. exact IH.
Qed.

Lemma tr_lin_eval vs l : vars_in (tr_lin vs l) (N.of_nat (length vs)) = true ->
  leval (fun p => oval b (nth (Nat.pred (Pos.to_nat p)) vs OP)) (tr_lin vs l) = oeval b l.
Proof.
  induction l as [|[v a] r IH]; [reflexivity|]. cbn [tr_lin map vars_in leval oeval]. intros H.
  apply andb_prop in H. destruct H as [H1 H2]. apply N.leb_le in H1.
  unfold tr_lin in IH. rewrite (IH H2). f_equal. f_equal. f_equal.
  pose proof (index_of_nth v vs 1%positive ltac:(change (Pos.to_nat 1) with 1%nat; lia)) as X.
  change (Pos.to_nat 1) with 1%nat in X. rewrite <- X at 2. f_equal. lia.
Qed.

Lemma tr_rows_hold vs rows : rows_vars_in (map (tr_row vs) rows) (N.of_nat (length vs)) = true -> Forall (oholds b) rows ->
  Forall (holds (fun p => oval b (nth (Nat.pred (Pos.to_nat p)) vs OP))) (map (tr_row vs) rows).
Proof.
  induction rows as [|[[l c] rhs] rs IH]; intros V F; [constructor|]. cbn [map rows_vars_in tr_row] in *.
  apply andb_prop in V. destruct V as [V1 V2]. inversion F; subst. constructor; [|apply IH; assumption].
  unfold holds. cbn [r_cmp r_lhs r_rhs]. cbn [r_lhs] in V1. rewrite (tr_lin_eval vs l V1). exact H1.
Qed.

Theorem lp_bound T ys D : forallb tpl_okb T = true -> forallb vwfb (all_vars prm) = true ->
  lp_check (to_lp prm T) ys D = true -> vH b + vEX b <= 8 * lbs - 10.
Proof.
  intros HT HV CH.
  pose proof (lp_check_sound (to_lp prm T) ys D (xval prm b) CH) as S.
  unfold lp_check in CH. apply andb_prop in CH. destruct CH as [CH _]. apply andb_prop in CH. destruct CH as [CH _].
  apply andb_prop in CH. destruct CH as [CH _]. apply andb_prop in CH. destruct CH as [CH VO]. apply andb_prop in CH. destruct CH as [_ VR].
  cbn [to_lp lp_nv lp_rows lp_obj lp_bound] in S, VO, VR.
  assert (NN : forall k, (k < length (all_vars prm))%nat -> 0 <= xval prm b (pos_of k)).
  { intros k Hk. unfold xval, pos_of. rewrite SuccNat2Pos.id_succ. cbn [Nat.pred].
    refine (proj1 (var_ok _ _)). rewrite forallb_forall in HV. apply HV. apply nth_In. exact Hk. }
  specialize (S NN).
  specialize (S (tr_rows_hold (all_vars prm) (orows prm T) VR (orows_sound T HT HV))).
  unfold xval in S. rewrite (tr_lin_eval (all_vars prm) (oobj) VO) in S. unfold oobj in S. cbn [oeval oval] in S.
  unfold obound in S. rewrite (po_lbs prm _ b PRM) in S. lia.
Qed.

End Sound.
End OverlayRowsOk.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayRowsOk.

Module OverlayExcess.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayHuff4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayTrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayDamage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma zsum_point : forall (x v : Z) lo n, lo <= x < lo + Z.of_nat n -> zsum (fun b => if b =? x then v else 0) lo n = v.
Proof.
  intros x v lo n Hx. rewrite (zsum_single (fun b => if b =? x then v else 0) lo n x); [rewrite Z.eqb_refl; reflexivity | exact Hx |].
  intros i Hi Ni. replace (i =? x) with false by (symmetry; apply Z.eqb_neq; exact Ni). reflexivity.
Qed.

Lemma zsum_point_out : forall (x v : Z) lo n, ~ (lo <= x < lo + Z.of_nat n) -> zsum (fun b => if b =? x then v else 0) lo n = 0.
Proof. intros x v lo n Hx. apply zsum_0. intros i Hi. replace (i =? x) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Definition sz (l : Z) : Z := 2 ^ (15 - l) - 1.

Lemma pow15_pos : forall l, l <= 15 -> 1 <= 2 ^ (15 - l).
Proof. intros. pose proof (Z.pow_pos_nonneg 2 (15 - l) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma sz_facts : forall l, 1 <= l <= 14 -> 1 <= sz l /\ sz l = 2 * sz (l + 1) + 1 /\ 2 ^ (15 - l) = 2 * 2 ^ (15 - (l + 1)).
Proof.
  intros l Hl. unfold sz. replace (15 - l) with (Z.succ (15 - (l + 1))) by lia. rewrite Z.pow_succ_r by lia.
  pose proof (pow15_pos (l + 1) ltac:(lia)). lia.
Qed.

Lemma find_spec : forall fuel (a : hist) bits u,
  u <= bits -> bits - u < Z.of_nat fuel -> a u <> 0 -> (forall l, u < l <= bits -> a l = 0) ->
  rep_find fuel a bits = u.
Proof.
  induction fuel as [|fuel IH]; intros a bits u Hu Hf Au Z0; [lia|]. cbn [rep_find].
  destruct (Z.eqb_spec (a bits) 0) as [E|NE].
  - assert (u <> bits) by (intros ->; exact (Au E)). apply IH; [lia|lia|exact Au|intros; apply Z0; lia].
  - destruct (Z.eq_dec u bits) as [->|N]; [reflexivity|]. exfalso. apply NE. apply Z0. lia.
Qed.


Definition rstep (a : hist) (u : Z) : hist := rep_step 15 a u.

Lemma rstep_get : forall a u b, 1 <= u <= 14 ->
  rstep a u b = (if b =? 15 then (if u =? 14 then a 15 + 1 else a 15 - 1)
                 else if b =? u then a u - 1 else if b =? u + 1 then a (u + 1) + 2 else a b).
Proof.
  intros a u b Hu. unfold rstep, rep_step.
  destruct (Z.eqb_spec b 15) as [->|N15].
  - replace (15 =? u) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec u 14) as [->|N14]; [change (15 =? 14 + 1) with true; cbn; lia|].
    replace (15 =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (Z.eqb_spec b u) as [->|Nu]; [reflexivity|].
    destruct (Z.eqb_spec b (u + 1)) as [->|Nu1]; [|reflexivity].
    replace (u + 1 =? 15) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Definition levels_ok (a : hist) : Prop := forall b, 0 <= a b /\ ((b < 1 \/ 15 < b) -> a b = 0).

Section Repair15.
Variable c1 : hist.
Variable nl : Z.
Variable K : Z.
Hypothesis C1OK : levels_ok c1.
Hypothesis C1T : zsum c1 1 15 = nl.
Hypothesis C1K : zsum (fun b => c1 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K.
Hypothesis C1C : K + 1 <= c1 15.
Hypothesis HK : 1 <= K.
Hypothesis Hnl : 2 <= nl <= 286.

Let C1N : forall b, 0 <= c1 b := fun b => proj1 (C1OK b).

Definition Rm (a : hist) (v : Z) : Z := zsum (fun l => a l * sz l) (v + 1) (Z.to_nat (14 - v)).
Definition Tc (v : Z) : Z := zsum (fun l => c1 l * sz l) (v + 1) (Z.to_nat (14 - v)).

Record RINV (t : Z) (a : hist) : Prop := {
  ri_ok : levels_ok a;
  ri_tot : zsum a 1 15 = nl;
  ri_kr : zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - t;
  ri_kc : K + 1 - t <= a 15;
  ri_prof : exists v tau, 1 <= v <= 14 /\ 1 <= tau <= c1 v /\ 0 <= Rm a v <= 2 ^ (15 - v) - 2 /\
            (forall b, 1 <= b < v -> a b = c1 b) /\ a v = c1 v - tau /\
            t = Tc v + tau * sz v - Rm a v /\ 2 ^ (15 - v) + 1 <= nl }.

Lemma level_le_tot : forall (a : hist) b, levels_ok a -> zsum a 1 15 = nl -> 1 <= b <= 15 -> a b <= nl.
Proof.
  intros a b OK T Hb. rewrite <- T. apply (zsum_ge_point a 1 15 b); [intros j Hj; apply (proj1 (OK j)) | lia].
Qed.

Lemma kraft_split : forall (a : hist) u, (forall b, 0 <= a b) -> 0 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) ->
  let Q := zsum (fun b => a b * 2 ^ (u - b)) 1 (Z.to_nat u) in
  0 <= Q /\ zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = Q * 2 ^ (15 - u) + a 15.
Proof.
  intros a u B Hu Z0 Q. split.
  { apply zsum_nonneg. intros b Hb. pose proof (B b). pose proof (Z.pow_nonneg 2 (u - b)). nia. }
  replace 15%nat with (Z.to_nat u + (Z.to_nat (14 - u) + 1))%nat at 1 by lia.
  rewrite zsum_split, zsum_split. change (zsum (fun b : Z => a b * 2 ^ (15 - b)) (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u))) 1)
    with (0 + a (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0) * 2 ^ (15 - (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0))).
  rewrite (zsum_0 _ (1 + Z.of_nat (Z.to_nat u)) (Z.to_nat (14 - u))) by (intros l Hl; rewrite Z0 by lia; lia).
  replace (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0) with 15 by lia.
  rewrite Z.sub_diag, Z.pow_0_r.
  enough (E : zsum (fun b => a b * 2 ^ (15 - b)) 1 (Z.to_nat u) = zsum (fun b => 2 ^ (15 - u) * (a b * 2 ^ (u - b))) 1 (Z.to_nat u)) by (rewrite zsum_scale in E; lia).
  apply zsum_ext. intros b Hb. replace (15 - b) with ((15 - u) + (u - b)) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma max_level : forall (a : hist) u, (forall b, 0 <= a b) -> (exists b, 1 <= b <= u /\ 1 <= a b) ->
  exists u', 1 <= u' <= u /\ 1 <= a u' /\ forall l, u' < l <= u -> a l = 0.
Proof.
  intros a u B. remember (Z.to_nat u) as n eqn:En. revert u En. induction n as [|n IH]; intros u En (b & Hb & Ab); [lia|].
  destruct (Z.le_gt_cases 1 (a u)).
  - exists u. split; [lia|]. split; [assumption|]. intros; lia.
  - destruct (IH (u - 1) ltac:(lia)) as (u' & H1 & H2 & H3).
    + exists b. split; [|exact Ab]. destruct (Z.eq_dec b u) as [->|]; lia.
    + exists u'. split; [lia|]. split; [exact H2|]. intros l Hl. destruct (Z.eq_dec l u) as [->|]; [pose proof (B u); lia|apply H3; lia].
Qed.

Lemma deepest_level : forall (a : hist) t u,
  levels_ok a -> zsum a 1 15 = nl -> zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - t ->
  K + 1 - t <= a 15 -> 0 <= t < K -> 0 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) ->
  exists u', 1 <= u' <= u /\ 1 <= a u' /\ (forall l, u' < l <= 14 -> a l = 0) /\ 2 ^ (15 - u') + 1 <= nl.
Proof.
  intros a t u OK T KR KC Ht Hu Z0.
  assert (B0 : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  pose proof (level_le_tot a 15 OK T ltac:(lia)) as A15.
  destruct (max_level a u B0) as (u' & H1 & H2 & H3).
  { destruct (Z.lt_ge_cases 0 (zsum (fun b => zind (1 <=? a b)) 1 (Z.to_nat u))) as [POS|ZE].
    - destruct (zsum_pos_has (fun b => 1 <=? a b) 1 (Z.to_nat u) POS) as (b & Hb & Pb & _).
      apply Z.leb_le in Pb. exists b. split; [lia|exact Pb].
    - exfalso. pose proof (kraft_split a 0 B0 ltac:(lia)) as KS. cbv zeta in KS.
      destruct KS as [_ E].
      { intros l Hl. destruct (Z.le_gt_cases l u); [|apply Z0; lia].
        pose proof (zsum_nonneg (fun b => zind (1 <=? a b)) 1 (Z.to_nat u) ltac:(intros; apply (proj1 (zind_le1 _)))).
        destruct (Z.le_gt_cases 1 (a l)); [|pose proof (B0 l); lia].
        pose proof (zsum_ind_ge1 (fun b => 1 <=? a b) 1 (Z.to_nat u) l ltac:(lia) ltac:(apply Z.leb_le; assumption)). lia. }
      rewrite KR in E. change (Z.to_nat 0) with 0%nat in E. cbn [zsum] in E. change (2 ^ (15 - 0)) with 32768 in E. change (2 ^ 15) with 32768 in E. lia. }
  exists u'. split; [exact H1|]. split; [exact H2|]. split.
  { intros l Hl. destruct (Z.le_gt_cases l u); [apply H3; lia|apply Z0; lia]. }
  pose proof (kraft_split a u' B0 ltac:(lia)) as KS. cbv zeta in KS. destruct KS as [QN E].
  { intros l Hl. destruct (Z.le_gt_cases l u); [apply H3; lia|apply Z0; lia]. }
  rewrite KR in E.
  set (Q := zsum (fun b => a b * 2 ^ (u' - b)) 1 (Z.to_nat u')) in *.
  assert (P : 2 ^ 15 = 2 ^ u' * 2 ^ (15 - u')) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (pow15_pos u' ltac:(lia)) as PP.
  assert (D : (2 ^ u' - Q) * 2 ^ (15 - u') = a 15 - (K - t)) by lia.
  assert (1 <= 2 ^ u' - Q) by nia.
  clearbody Q. nia.
Qed.

Lemma rstep_wsum : forall a u (wgt : Z -> Z) lo n, 1 <= u <= 14 -> 1 <= lo ->
  zsum (fun b => rstep a u b * wgt b) lo n =
  zsum (fun b => a b * wgt b) lo n
  + (if (lo <=? 15) && (15 <? lo + Z.of_nat n) then (if u =? 14 then wgt 15 else - wgt 15) else 0)
  + (if (lo <=? u) && (u <? lo + Z.of_nat n) then - wgt u else 0)
  + (if (lo <=? u + 1) && (u + 1 <? lo + Z.of_nat n) && negb (u =? 14) then 2 * wgt (u + 1) else 0).
Proof.
  intros a u wgt lo n Hu Hlo.
  transitivity (zsum (fun b => a b * wgt b + ((if b =? 15 then (if u =? 14 then wgt 15 else - wgt 15) else 0) + (if b =? u then - wgt u else 0)
                        + (if b =? u + 1 then (if negb (u =? 14) then 2 * wgt (u + 1) else 0) else 0))) lo n).
  { apply zsum_ext. intros b Hb. rewrite rstep_get by assumption.
    destruct (Z.eqb_spec b 15) as [->|N15].
    - replace (15 =? u) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (Z.eqb_spec u 14) as [->|NU]; [change (15 =? 14 + 1) with true; cbn [negb]; lia|].
      replace (15 =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    - destruct (Z.eqb_spec b u) as [->|NU]; [replace (u =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia); lia|].
      destruct (Z.eqb_spec b (u + 1)) as [->|NU1]; [|lia].
      destruct (Z.eqb_spec u 14) as [->|N14]; [exfalso; lia|]. cbn [negb]. lia. }
  rewrite !zsum_add.
  assert (PT : forall x v, zsum (fun b => if b =? x then v else 0) lo n = if (lo <=? x) && (x <? lo + Z.of_nat n) then v else 0).
  { intros x v. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + Z.of_nat n)); cbn [andb];
      first [apply zsum_point; lia | apply zsum_point_out; lia]. }
  rewrite !PT. destruct (u =? 14); cbn [negb]; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r;
    destruct ((lo <=? u + 1) && (u + 1 <? lo + Z.of_nat n)); lia.
Qed.

Lemma rstep_ok : forall a u, levels_ok a -> 1 <= u <= 14 -> 1 <= a u -> (u = 14 \/ 1 <= a 15) ->
  zsum a 1 15 = nl ->
  levels_ok (rstep a u) /\ zsum (rstep a u) 1 15 = nl /\
  zsum (fun b => rstep a u b * 2 ^ (15 - b)) 1 15 = zsum (fun b => a b * 2 ^ (15 - b)) 1 15 - 1.
Proof.
  intros a u OK Hu Au A15 T.
  assert (B : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  assert (NN : forall b, 0 <= rstep a u b).
  { intros b. rewrite rstep_get by assumption. pose proof (B b). pose proof (B 15). pose proof (B (u + 1)). pose proof (B u).
    destruct (b =? 15); [destruct (Z.eqb_spec u 14); lia|]. destruct (b =? u); [lia|]. destruct (b =? u + 1); lia. }
  assert (T' : zsum (rstep a u) 1 15 = nl).
  { pose proof (rstep_wsum a u (fun _ => 1) 1 15 Hu ltac:(lia)) as W.
    rewrite (zsum_ext (fun b => rstep a u b * 1) (rstep a u)) in W by (intros; lia).
    rewrite (zsum_ext (fun b => a b * 1) a) in W by (intros; lia).
    rewrite W, T. change (Z.of_nat 15) with 15.
    replace ((1 <=? 15) && (15 <? 1 + 15)) with true by reflexivity.
    replace ((1 <=? u) && (u <? 1 + 15)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb]; [rewrite Bool.andb_false_r; lia|].
    replace ((1 <=? u + 1) && (u + 1 <? 1 + 15) && true) with true by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    lia. }
  split; [|split; [exact T'|]].
  - intros b. split; [apply NN|]. intros Hb. rewrite rstep_get by assumption. pose proof (proj2 (OK b) Hb).
    destruct (Z.eqb_spec b 15); [lia|]. destruct (Z.eqb_spec b u); [lia|]. destruct (Z.eqb_spec b (u + 1)); lia.
  - rewrite (rstep_wsum a u (fun b => 2 ^ (15 - b)) 1 15 Hu ltac:(lia)). change (Z.of_nat 15) with 15.
    replace ((1 <=? 15) && (15 <? 1 + 15)) with true by reflexivity.
    replace ((1 <=? u) && (u <? 1 + 15)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    change (2 ^ (15 - 15)) with 1.
    destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb]; [rewrite Bool.andb_false_r; change (2 ^ (15 - 14)) with 2; lia|].
    replace ((1 <=? u + 1) && (u + 1 <? 1 + 15) && true) with true by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & _ & P). lia.
Qed.

Lemma Rm_nonneg : forall a v, (forall b, 0 <= a b) -> 1 <= v <= 14 -> 0 <= Rm a v.
Proof. intros a v B Hv. unfold Rm. apply zsum_nonneg. intros l Hl. pose proof (B l). pose proof (sz_facts l ltac:(lia)). nia. Qed.

Lemma Rm_zero : forall a v, (forall b, 0 <= a b) -> 1 <= v <= 14 -> Rm a v = 0 -> forall l, v < l <= 14 -> a l = 0.
Proof.
  intros a v B Hv R l Hl. unfold Rm in R.
  pose proof (zsum_ge_point (fun l => a l * sz l) (v + 1) (Z.to_nat (14 - v)) l
                ltac:(intros j Hj; pose proof (B j); pose proof (sz_facts j ltac:(lia)); nia) ltac:(lia)) as X.
  cbv beta in X. pose proof (B l). pose proof (sz_facts l ltac:(lia)). nia.
Qed.

Lemma Rm_of_zero : forall a v, 1 <= v <= 14 -> (forall l, v < l <= 14 -> a l = 0) -> Rm a v = 0.
Proof. intros a v Hv Z0. unfold Rm. apply zsum_0. intros l Hl. rewrite Z0 by lia. lia. Qed.

Lemma Rm_inner : forall a u v, 1 <= u <= 14 -> 1 <= v < u -> Rm (rstep a u) v = Rm a v - 1.
Proof.
  intros a u v Hu Hv. unfold Rm. rewrite (rstep_wsum a u sz (v + 1) (Z.to_nat (14 - v)) Hu ltac:(lia)).
  replace ((v + 1 <=? 15) && (15 <? v + 1 + Z.of_nat (Z.to_nat (14 - v)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((v + 1 <=? u) && (u <? v + 1 + Z.of_nat (Z.to_nat (14 - v)))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb].
  - rewrite Bool.andb_false_r. unfold sz. change (2 ^ (15 - 14)) with 2. lia.
  - replace ((v + 1 <=? u + 1) && (u + 1 <? v + 1 + Z.of_nat (Z.to_nat (14 - v))) && true) with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & E & _). lia.
Qed.

Lemma Rm_touch : forall a u, 1 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) -> Rm (rstep a u) u = sz u - 1.
Proof.
  intros a u Hu Z0. unfold Rm. rewrite (rstep_wsum a u sz (u + 1) (Z.to_nat (14 - u)) Hu ltac:(lia)).
  fold (Rm a u). rewrite (Rm_of_zero a u) by (lia || exact Z0).
  replace ((u + 1 <=? 15) && (15 <? u + 1 + Z.of_nat (Z.to_nat (14 - u)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((u + 1 <=? u) && (u <? u + 1 + Z.of_nat (Z.to_nat (14 - u)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.leb_gt; lia).
  destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb].
  - rewrite Bool.andb_false_r. unfold sz. change (2 ^ (15 - 14)) with 2. lia.
  - replace ((u + 1 <=? u + 1) && (u + 1 <? u + 1 + Z.of_nat (Z.to_nat (14 - u))) && true) with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & E & _). lia.
Qed.

Lemma Tc_split : forall u v, 1 <= u -> u < v <= 14 -> (forall l, u < l < v -> c1 l = 0) -> Tc u = c1 v * sz v + Tc v.
Proof.
  intros u v Hu Hv Z0. unfold Tc.
  replace (Z.to_nat (14 - u)) with (Z.to_nat (v - 1 - u) + S (Z.to_nat (14 - v)))%nat by lia.
  rewrite zsum_split, zsum_shift.
  rewrite (zsum_0 _ (u + 1) (Z.to_nat (v - 1 - u))) by (intros l Hl; rewrite Z0 by lia; lia).
  replace (u + 1 + Z.of_nat (Z.to_nat (v - 1 - u))) with v by lia. lia.
Qed.

Lemma Tc_14_zero : forall u, 1 <= u <= 14 -> (forall l, u < l <= 14 -> c1 l = 0) -> Tc u = 0.
Proof. intros u Hu Z0. unfold Tc. apply zsum_0. intros l Hl. rewrite Z0 by lia. lia. Qed.

Lemma Tc_nonneg : forall v, 1 <= v <= 14 -> 0 <= Tc v.
Proof. intros v Hv. unfold Tc. apply zsum_nonneg. intros l Hl. pose proof (C1N l). pose proof (sz_facts l ltac:(lia)). nia. Qed.

Definition rnext (a : hist) : hist := rstep a (rep_find (Z.to_nat 15) a (15 - 1)).

Lemma rinv_step : forall t a, RINV t a -> t < K -> RINV (t + 1) (rnext a).
Proof.
  intros t a [OK T KR KC (v & tau & Hv & Ht & HR & LOW & AV & ET & NB)] TK. unfold rnext. change (15 - 1) with 14.
  assert (B0 : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  assert (T0 : 0 <= t).
  { pose proof (Rm_nonneg a v B0 ltac:(lia)). pose proof (Tc_nonneg v ltac:(lia)). pose proof (pow15_pos v ltac:(lia)). unfold sz in *. nia. }
  assert (A15 : 1 <= a 15) by lia.
  destruct (Z.lt_ge_cases 0 (Rm a v)) as [RP|RZ].
  -
    assert (EX : exists b, 1 <= b <= 14 /\ 1 <= a b /\ v < b).
    { unfold Rm in RP.
      destruct (Z.lt_ge_cases 0 (zsum (fun l => zind (1 <=? a l)) (v + 1) (Z.to_nat (14 - v)))) as [P|Z0].
      - destruct (zsum_pos_has (fun l => 1 <=? a l) (v + 1) (Z.to_nat (14 - v)) P) as (b & Hb & Pb & _).
        apply Z.leb_le in Pb. exists b. lia.
      - exfalso. rewrite (zsum_0 _ (v + 1)) in RP; [lia|].
        intros l Hl. pose proof (zsum_nonneg (fun l => zind (1 <=? a l)) (v + 1) (Z.to_nat (14 - v)) ltac:(intros; apply (proj1 (zind_le1 _)))).
        destruct (Z.le_gt_cases 1 (a l)); [|pose proof (B0 l); replace (a l) with 0 by lia; lia].
        pose proof (zsum_ind_ge1 (fun l => 1 <=? a l) (v + 1) (Z.to_nat (14 - v)) l Hl ltac:(apply Z.leb_le; assumption)). lia. }
    destruct EX as (b & Hb & Ab & Vb).
    destruct (max_level a 14 B0 ltac:(exists b; split; [lia|exact Ab])) as (u & U1 & U2 & U3).
    assert (Vu : v < u) by (destruct (Z.lt_ge_cases v u); [assumption|]; exfalso; pose proof (U3 b ltac:(lia)); lia).
    rewrite (find_spec (Z.to_nat 15) a 14 u) by (first [lia | intros; apply U3; lia]).
    destruct (rstep_ok a u OK ltac:(lia) U2 ltac:(lia) T) as (OK' & T' & KR').
    constructor; [exact OK'|exact T'|rewrite KR', KR; lia| |].
    + rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
    + exists v, tau. rewrite (Rm_inner a u v ltac:(lia) ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros b' Hb'. rewrite rstep_get by lia.
        destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. apply LOW. lia. }
      split; [|split; [lia|exact NB]].
      rewrite rstep_get by lia.
      destruct (Z.eqb_spec v 15); [lia|]. destruct (Z.eqb_spec v u); [lia|]. destruct (Z.eqb_spec v (u + 1)); [lia|]. exact AV.
  -
    assert (RZ0 : Rm a v = 0) by (pose proof (Rm_nonneg a v B0 ltac:(lia)); lia).
    pose proof (Rm_zero a v B0 ltac:(lia) RZ0) as EMP.
    destruct (deepest_level a t v OK T KR KC ltac:(lia) ltac:(lia) EMP) as (u & U1 & U2 & U3 & U4).
    rewrite (find_spec (Z.to_nat 15) a 14 u) by (first [lia | intros; apply U3; lia]).
    destruct (rstep_ok a u OK ltac:(lia) U2 ltac:(lia) T) as (OK' & T' & KR').
    constructor; [exact OK'|exact T'|rewrite KR', KR; lia| |].
    + rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
    + pose proof (Rm_touch a u ltac:(lia) U3) as RT.
      destruct (Z.eq_dec u v) as [->|NE].
      * exists v, (tau + 1). rewrite RT. pose proof (sz_facts v ltac:(lia)) as (S1 & S2 & S3).
        split; [lia|]. split; [lia|]. split; [unfold sz; lia|]. split.
        { intros b' Hb'. rewrite rstep_get by lia.
          destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' v); [lia|]. destruct (Z.eqb_spec b' (v + 1)); [lia|]. apply LOW. lia. }
        split; [|split; [unfold sz in *; lia|exact NB]].
        rewrite rstep_get by lia. destruct (Z.eqb_spec v 15); [lia|]. rewrite Z.eqb_refl. lia.
      * assert (Uv : u < v) by lia.
        assert (AV0 : a v = 0) by (apply U3; lia).
        exists u, 1. rewrite RT. pose proof (sz_facts u ltac:(lia)) as (S1 & S2 & S3).
        split; [lia|]. split; [rewrite <- (LOW u) by lia; lia|]. split; [unfold sz; lia|]. split.
        { intros b' Hb'. rewrite rstep_get by lia.
          destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. apply LOW. lia. }
        split.
        { rewrite rstep_get by lia. destruct (Z.eqb_spec u 15); [lia|]. rewrite Z.eqb_refl. rewrite (LOW u) by lia. lia. }
        split; [|exact U4].
        rewrite (Tc_split u v) by (first [lia | intros l Hl; rewrite <- (LOW l) by lia; apply U3; lia]).
        unfold sz in *. lia.
Qed.

Lemma rinv_first : RINV 1 (rnext c1).
Proof.
  unfold rnext. change (15 - 1) with 14.
  assert (KR : zsum (fun b => c1 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - 0) by (rewrite C1K; lia).
  assert (KC : K + 1 - 0 <= c1 15) by lia.
  destruct (deepest_level c1 0 14 C1OK C1T KR KC ltac:(lia) ltac:(lia) ltac:(intros; lia)) as (u & U1 & U2 & U3 & U4).
  rewrite (find_spec (Z.to_nat 15) c1 14 u) by (first [lia | intros; apply U3; lia]).
  destruct (rstep_ok c1 u C1OK ltac:(lia) U2 ltac:(lia) C1T) as (OK' & T' & KR').
  constructor; [exact OK'|exact T'|rewrite KR', C1K; lia| |].
  - rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
  - exists u, 1. rewrite (Rm_touch c1 u ltac:(lia) U3). pose proof (sz_facts u ltac:(lia)) as (S1 & S2 & S3).
    split; [lia|]. split; [lia|]. split; [unfold sz; lia|]. split.
    { intros b' Hb'. rewrite rstep_get by lia.
      destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. reflexivity. }
    split.
    { rewrite rstep_get by lia. destruct (Z.eqb_spec u 15); [lia|]. rewrite Z.eqb_refl. lia. }
    split; [|exact U4].
    rewrite (Tc_14_zero u) by (first [lia | intros l Hl; apply U3; lia]). unfold sz in *. lia.
Qed.

Lemma rep_iter_rnext : forall n a, rep_iter (S n) 15 a = rep_iter n 15 (rnext a).
Proof. reflexivity. Qed.

Lemma rinv_iter : forall n t a, RINV t a -> t + Z.of_nat n <= K -> RINV (t + Z.of_nat n) (rep_iter n 15 a).
Proof.
  induction n as [|n IH]; intros t a R Hn; [rewrite Z.add_0_r; exact R|].
  rewrite rep_iter_rnext. replace (t + Z.of_nat (S n)) with (t + 1 + Z.of_nat n) by lia. apply IH; [|lia]. apply rinv_step; [exact R|lia].
Qed.

Theorem repair_profile :
  let a2 := repair 15 c1 in
  levels_ok a2 /\ zsum a2 1 15 = nl /\ zsum (fun b => a2 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 /\
  exists v tau, 1 <= v <= 14 /\ 1 <= tau <= c1 v /\ 2 ^ (15 - v) + 1 <= nl /\
    (forall b, 1 <= b < v -> a2 b = c1 b) /\ a2 v = c1 v - tau /\
    Tc v + (tau - 1) * sz v <= K - 1.
Proof.
  cbv zeta.
  assert (EK : kraftZ 15 c1 - 2 ^ 15 = K) by (unfold kraftZ; change (Z.to_nat 15) with 15%nat; rewrite C1K; lia).
  unfold repair. rewrite EK. replace (Z.to_nat K) with (S (Z.to_nat (K - 1))) by lia. rewrite rep_iter_rnext.
  pose proof (rinv_iter (Z.to_nat (K - 1)) 1 _ rinv_first ltac:(lia)) as R.
  replace (1 + Z.of_nat (Z.to_nat (K - 1))) with K in R by lia.
  destruct R as [OK T KR KC (v & tau & Hv & Ht & HR & LOW & AV & ET & NB)].
  split; [exact OK|]. split; [exact T|]. split; [rewrite KR; lia|]. exists v, tau.
  split; [exact Hv|]. split; [exact Ht|]. split; [exact NB|]. split; [exact LOW|]. split; [exact AV|].
  unfold sz in *. lia.
Qed.
End Repair15.


Definition Gs (a : hist) (Lv : Z) : Z := zsum a Lv (Z.to_nat (16 - Lv)).
Definition lev (a : hist) (i : Z) : Z := zsum (fun Lv => zind (i <? Gs a Lv)) 1 15.

Lemma Gs_step : forall a Lv, Lv <= 15 -> Gs a Lv = a Lv + Gs a (Lv + 1).
Proof.
  intros a Lv HL. unfold Gs. replace (Z.to_nat (16 - Lv)) with (S (Z.to_nat (16 - (Lv + 1)))) by lia.
  rewrite zsum_shift. reflexivity.
Qed.
Lemma Gs_16 : forall a, Gs a 16 = 0.
Proof. reflexivity. Qed.
Lemma Gs_mono : forall a Lv Lv', (forall b, 0 <= a b) -> Lv <= Lv' <= 16 -> Gs a Lv' <= Gs a Lv.
Proof.
  intros a Lv Lv' B H. remember (Z.to_nat (Lv' - Lv)) as n eqn:En. revert Lv H En. induction n as [|n IH]; intros Lv H En; [replace Lv with Lv' by lia; lia|].
  rewrite (Gs_step a Lv) by lia. pose proof (B Lv). specialize (IH (Lv + 1) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma Gs_nonneg : forall a Lv, (forall b, 0 <= a b) -> 0 <= Gs a Lv.
Proof. intros a Lv B. unfold Gs. apply zsum_nonneg. intros; apply B. Qed.
Lemma Gs_1 : forall a, Gs a 1 = zsum a 1 15.
Proof. reflexivity. Qed.

Lemma lev_eq : forall a i b, (forall b, 0 <= a b) -> 1 <= b <= 15 -> Gs a (b + 1) <= i < Gs a b -> lev a i = b.
Proof.
  intros a i b B Hb Hi. unfold lev.
  replace 15%nat with (Z.to_nat (b - 1) + S (Z.to_nat (15 - b)))%nat by lia. rewrite zsum_split, zsum_shift.
  rewrite (zsum_ext _ (fun _ => 1) 1 (Z.to_nat (b - 1))), zsum_const1.
  2:{ intros Lv HL. pose proof (Gs_mono a Lv b B ltac:(lia)). replace (i <? Gs a Lv) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  replace (1 + Z.of_nat (Z.to_nat (b - 1))) with b by lia.
  replace (i <? Gs a b) with true by (symmetry; apply Z.ltb_lt; lia). cbn [zind].
  rewrite (zsum_0 _ (b + 1)); [lia|].
  intros Lv HL. pose proof (Gs_mono a (b + 1) Lv B ltac:(lia)). replace (i <? Gs a Lv) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma lev_range : forall a i, (forall b, 0 <= a b) -> 0 <= i < Gs a 1 -> 1 <= lev a i <= 15 /\ Gs a (lev a i + 1) <= i < Gs a (lev a i).
Proof.
  intros a i B Hi.
  assert (EX : exists b, 1 <= b <= 15 /\ Gs a (b + 1) <= i < Gs a b).
  { assert (GEN : forall n b, Z.of_nat n = b - 1 -> 1 <= b <= 15 -> Gs a (b + 1) <= i -> exists b', 1 <= b' <= b /\ Gs a (b' + 1) <= i < Gs a b').
    { induction n as [|n IH]; intros b En Hb Hle.
      - exists b. assert (b = 1) by lia. subst b. split; [lia|]. lia.
      - destruct (Z.lt_ge_cases i (Gs a b)); [exists b; split; [lia|lia]|].
        destruct (IH (b - 1) ltac:(lia) ltac:(lia) ltac:(replace (b - 1 + 1) with b by lia; lia)) as (b' & H1 & H2). exists b'. split; [lia|exact H2]. }
    destruct (GEN 14%nat 15 eq_refl ltac:(lia) ltac:(rewrite Gs_16; lia)) as (b' & H1 & H2). exists b'. split; [lia|exact H2]. }
  destruct EX as (b & Hb & Hib). rewrite (lev_eq a i b B Hb Hib). split; [exact Hb|exact Hib].
Qed.

Lemma Gs_cnt : forall (L : list Z) (v : Z -> Z) Lv, (forall i, In i L -> 1 <= v i <= 15) -> 1 <= Lv <= 16 ->
  Gs (fun b => cnt (fun i => v i =? b) L) Lv = cnt (fun i => Lv <=? v i) L.
Proof.
  intros L v Lv Hv HL. unfold Gs, cnt. rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (Hv i Hi).
  destruct (Z.leb_spec Lv (v i)).
  - rewrite (zsum_single (fun b => zind (v i =? b)) Lv (Z.to_nat (16 - Lv)) (v i)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros b Hb Nb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - cbn [zind]. apply zsum_0. intros b Hb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.


Lemma cnt_eq_one : forall (L : list Z) i, NoDup L -> In i L -> cnt (fun k => k =? i) L = 1.
Proof.
  intros L i ND Hi. unfold cnt. induction L as [|x L IH]; [destruct Hi|]. inversion ND; subst. cbn [lsum].
  destruct Hi as [->|Hi].
  - rewrite Z.eqb_refl. cbn [zind]. enough (lsum (fun k => zind (k =? i)) L = 0) by lia.
    etransitivity; [apply lsum_ext | apply lsum_zero]. intros k Hk. replace (k =? i) with false by (symmetry; apply Z.eqb_neq; intros ->; tauto). reflexivity.
  - replace (x =? i) with false by (symmetry; apply Z.eqb_neq; intros ->; tauto). cbn [zind]. rewrite IH by assumption. reflexivity.
Qed.

Lemma cnt_eq_zero : forall (L : list Z) i, ~ In i L -> cnt (fun k => k =? i) L = 0.
Proof.
  intros L i Hi. unfold cnt. etransitivity; [apply lsum_ext | apply lsum_zero]. intros k Hk. replace (k =? i) with false by (symmetry; apply Z.eqb_neq; intros ->; tauto). reflexivity.
Qed.

Lemma cnt_at : forall (P : Z -> bool) (L : list Z) i, NoDup L -> In i L ->
  cnt P L = cnt (fun k => P k && negb (k =? i)) L + zind (P i).
Proof.
  intros P L i ND Hi. rewrite (cnt_split P (fun k => negb (k =? i)) L). f_equal.
  rewrite (cnt_ext (fun k => P k && negb (negb (k =? i))) (fun k => P i && (k =? i)) L).
  2:{ intros k Hk. destruct (Z.eqb_spec k i) as [->|N]; cbn [negb]; [destruct (P i); reflexivity | rewrite !Bool.andb_false_r; reflexivity]. }
  destruct (P i); cbn [zind andb]; [apply cnt_eq_one; assumption|].
  unfold cnt. etransitivity; [apply lsum_ext; intros; reflexivity | apply lsum_zero].
Qed.

Section Ranks.
Variable L : list Z.
Variable w : Z -> Z.
Variable lam : Z -> Z.
Hypothesis ND : NoDup L.
Hypothesis LR : forall i j, In i L -> In j L -> w j < w i -> lam i <= lam j.

Definition before (j i : Z) : bool :=
  (w j <? w i) || ((w j =? w i) && ((lam i <? lam j) || ((lam j =? lam i) && (j <? i)))).
Definition rank (i : Z) : Z := cnt (fun j => before j i) L.
Definition nR : Z := Z.of_nat (length L).

Lemma before_irrefl : forall i, before i i = false.
Proof. intros i. unfold before. rewrite Z.ltb_irrefl, Z.eqb_refl, Z.ltb_irrefl, Z.eqb_refl, Z.ltb_irrefl. reflexivity. Qed.

Lemma before_trans : forall i j k, before i j = true -> before j k = true -> before i k = true.
Proof.
  intros i j k A B. unfold before in *.
  repeat match goal with
  | H : (_ || _) = true |- _ => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H; destruct H as [H ?]
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end;
  apply Bool.orb_true_iff;
  first [ left; apply Z.ltb_lt; lia
        | right; apply Bool.andb_true_iff; split; [apply Z.eqb_eq; lia|]; apply Bool.orb_true_iff;
          first [ left; apply Z.ltb_lt; lia | right; apply Bool.andb_true_iff; split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia] ] ].
Qed.

Lemma before_total : forall i j, i <> j -> before i j = true \/ before j i = true.
Proof.
  intros i j N. unfold before.
  destruct (Z.lt_total (w i) (w j)) as [A|[A|A]].
  - left. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact A.
  - destruct (Z.lt_total (lam i) (lam j)) as [B|[B|B]].
    + right. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact B.
    + destruct (Z.lt_total i j) as [C|[C|C]]; [| lia |].
      * left. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia].
      * right. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia].
    + left. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact B.
  - right. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact A.
Qed.

Lemma before_asym : forall i j, before i j = true -> before j i = false.
Proof.
  intros i j A. destruct (before j i) eqn:B; [|reflexivity]. exfalso.
  pose proof (before_trans i j i A B). rewrite before_irrefl in H. discriminate.
Qed.

Lemma before_w : forall j i, before j i = true -> w j <= w i.
Proof.
  intros j i A. unfold before in A. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; lia|].
  apply Bool.andb_true_iff in A. destruct A as [A _]. apply Z.eqb_eq in A. lia.
Qed.

Lemma before_lam : forall j i, In i L -> In j L -> before j i = true -> lam i <= lam j.
Proof.
  intros j i Hi Hj A. unfold before in A. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; exact (LR i j Hi Hj A)|].
  apply Bool.andb_true_iff in A. destruct A as [_ A]. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; lia|].
  apply Bool.andb_true_iff in A. destruct A as [A _]. apply Z.eqb_eq in A. lia.
Qed.

Lemma rank_range : forall i, In i L -> 0 <= rank i <= nR - 1.
Proof.
  intros i Hi. unfold rank, nR. split; [apply cnt_nonneg|].
  rewrite (cnt_at (fun j => before j i) L i ND Hi). rewrite before_irrefl. cbn [zind].
  pose proof (cnt_le_length (fun k => before k i && negb (k =? i)) L).
  pose proof (cnt_at (fun _ => true) L i ND Hi) as T. rewrite cnt_true in T. cbn [zind andb] in T.
  pose proof (cnt_mono (fun k => before k i && negb (k =? i)) (fun k => negb (k =? i)) L ltac:(intros k Hk X; apply Bool.andb_true_iff in X; tauto)). lia.
Qed.

Lemma rank_lt : forall i j, In i L -> In j L -> before i j = true -> rank i < rank j.
Proof.
  intros i j Hi Hj B. unfold rank.
  rewrite (cnt_at (fun k => before k j) L i ND Hi). rewrite B. cbn [zind].
  pose proof (cnt_mono (fun k => before k i) (fun k => before k j && negb (k =? i)) L) as M.
  specialize (M ltac:(intros k Hk X; apply Bool.andb_true_iff; split; [exact (before_trans k i j X B)|];
                    destruct (Z.eqb_spec k i) as [->|N]; [rewrite before_irrefl in X; discriminate|reflexivity])). lia.
Qed.

Lemma rank_inj : forall i j, In i L -> In j L -> rank i = rank j -> i = j.
Proof.
  intros i j Hi Hj E. destruct (Z.eq_dec i j) as [->|N]; [reflexivity|]. exfalso.
  destruct (before_total i j N) as [B|B]; [pose proof (rank_lt i j Hi Hj B) | pose proof (rank_lt j i Hj Hi B)]; lia.
Qed.

Lemma rank_lt_before : forall i j, In i L -> In j L -> rank j < rank i -> before j i = true.
Proof.
  intros i j Hi Hj R. destruct (Z.eq_dec i j) as [->|N]; [lia|].
  destruct (before_total j i ltac:(congruence)) as [B|B]; [exact B|]. pose proof (rank_lt i j Hi Hj B). lia.
Qed.

Lemma rank_mono_w : forall i j, In i L -> In j L -> rank j < rank i -> w j <= w i.
Proof. intros i j Hi Hj R. apply before_w. apply (rank_lt_before i j Hi Hj R). Qed.

Lemma rank_mono_lam : forall i j, In i L -> In j L -> rank j < rank i -> lam i <= lam j.
Proof. intros i j Hi Hj R. apply (before_lam j i Hi Hj). apply (rank_lt_before i j Hi Hj R). Qed.

Lemma rank_ge_w : forall i j, In i L -> In j L -> rank i <= rank j -> w i <= w j.
Proof.
  intros i j Hi Hj R. destruct (Z.eq_dec (rank i) (rank j)) as [E|N]; [rewrite (rank_inj i j Hi Hj E); lia|].
  apply (rank_mono_w j i Hj Hi). lia.
Qed.

Lemma rank_once : forall r, 0 <= r < nR -> cnt (fun i => rank i =? r) L = 1.
Proof.
  assert (LE1 : forall r, cnt (fun i => rank i =? r) L <= 1).
  { intros r. destruct (Z_lt_le_dec 1 (cnt (fun i => rank i =? r) L)) as [A|A]; [|exact A]. exfalso.
    destruct (cnt_pigeon (fun i => rank i =? r) (fun _ => false) L ltac:(pose proof (cnt_nonneg (fun i => rank i =? r) L); unfold cnt at 1; rewrite (lsum_ext (fun i => zind false) (fun _ => 0)), lsum_zero by (intros; reflexivity); lia)) as (i & Hi & Ri & _).
    apply Z.eqb_eq in Ri. rewrite (cnt_at (fun k => rank k =? r) L i ND Hi) in A. rewrite Ri, Z.eqb_refl in A. cbn [zind] in A.
    destruct (cnt_pigeon (fun k => (rank k =? r) && negb (k =? i)) (fun _ => false) L) as (j & Hj & Rj & _).
    { unfold cnt at 1. rewrite (lsum_ext (fun k => zind false) (fun _ => 0)), lsum_zero by (intros; reflexivity). lia. }
    apply Bool.andb_true_iff in Rj. destruct Rj as [Rj Nj]. apply Z.eqb_eq in Rj. apply Bool.negb_true_iff in Nj. apply Z.eqb_neq in Nj.
    apply Nj. apply (rank_inj j i Hj Hi). lia. }
  assert (SUM : zsum (fun r => cnt (fun i => rank i =? r) L) 0 (Z.to_nat nR) = nR).
  { unfold cnt. rewrite <- lsum_zsum_swap. transitivity (lsum (fun _ => 1) L); [| unfold nR; clear; induction L; cbn [lsum length]; lia].
    apply lsum_ext. intros i Hi.
    pose proof (rank_range i Hi). rewrite (zsum_single (fun r => zind (rank i =? r)) 0 (Z.to_nat nR) (rank i)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros r Hr Nr. replace (rank i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  intros r Hr. destruct (Z.eq_dec (cnt (fun i => rank i =? r) L) 1) as [E|N]; [exact E|]. exfalso.
  pose proof (LE1 r).
  pose proof (zsum_mono (fun r => cnt (fun i => rank i =? r) L) (fun r' => if r' =? r then 0 else 1) 0 (Z.to_nat nR)
                ltac:(intros r' Hr'; cbv beta; destruct (Z.eqb_spec r' r) as [->|Nr]; [lia | apply LE1])) as M.
  rewrite SUM in M.
  pose proof (zsum_mono (fun r' => if r' =? r then 0 else 1) (fun r' => 1 - (if r' =? r then 1 else 0)) 0 (Z.to_nat nR) ltac:(intros r' _; cbv beta; destruct (r' =? r); lia)) as M2.
  rewrite <- zsum_sub, zsum_const1, zsum_point in M2 by lia. lia.
Qed.

Theorem sum_by_rank : forall f : Z -> Z, lsum (fun i => f (rank i)) L = zsum f 0 (Z.to_nat nR).
Proof.
  intros f.
  transitivity (lsum (fun i => zsum (fun r => zind (rank i =? r) * f r) 0 (Z.to_nat nR)) L).
  - apply lsum_ext. intros i Hi. pose proof (rank_range i Hi).
    rewrite (zsum_single (fun r => zind (rank i =? r) * f r) 0 (Z.to_nat nR) (rank i)); [rewrite Z.eqb_refl; cbn [zind]; lia | lia |].
    intros r Hr Nr. replace (rank i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite lsum_zsum_swap. apply zsum_ext. intros r Hr.
    transitivity (f r * cnt (fun i => rank i =? r) L); [| rewrite rank_once by lia; lia].
    unfold cnt. rewrite <- lsum_scale. apply lsum_ext. intros; lia.
Qed.

Definition hlam (b : Z) : Z := cnt (fun j => lam j =? b) L.

Lemma lev_hlam : (forall i, In i L -> 1 <= lam i <= 15) -> forall i, In i L -> lev hlam (rank i) = lam i.
Proof.
  intros Hl i Hi. pose proof (Hl i Hi) as Ri.
  assert (B : forall b, 0 <= hlam b) by (intros; unfold hlam; apply cnt_nonneg).
  apply (lev_eq hlam (rank i) (lam i) B Ri). unfold hlam. rewrite !Gs_cnt by (try exact Hl; lia). split.
  -
    unfold rank. apply cnt_mono. intros j Hj X. apply Z.leb_le in X.
    destruct (Z.eq_dec j i) as [->|N]; [lia|].
    destruct (before_total j i N) as [Bf|Bf]; [exact Bf|]. exfalso. pose proof (before_lam i j Hj Hi Bf). lia.
  -
    unfold rank. rewrite (cnt_at (fun j => lam i <=? lam j) L i ND Hi). rewrite Z.leb_refl. cbn [zind].
    pose proof (cnt_mono (fun j => before j i) (fun k => (lam i <=? lam k) && negb (k =? i)) L) as M.
    specialize (M ltac:(intros k Hk X; apply Bool.andb_true_iff; split; [apply Z.leb_le; exact (before_lam k i Hi Hk X)|];
                      destruct (Z.eqb_spec k i) as [->|Nk]; [rewrite before_irrefl in X; discriminate|reflexivity])). lia.
Qed.

Lemma rank_rarity : forall (kap : Z -> Z) (Wt : Z),
  (forall i, In i L -> 1 <= kap i <= 15) -> (forall i, In i L -> 0 <= w i) ->
  (forall i, In i L -> w i * fib (kap i + 1) <= Wt) ->
  forall i, In i L -> w i * fib (lev (fun b => cnt (fun j => kap j =? b) L) (rank i) + 1) <= Wt.
Proof.
  intros kap Wt Hk Hw FIB i Hi.
  set (hk := fun b => cnt (fun j => kap j =? b) L).
  assert (B : forall b, 0 <= hk b) by (intros; subst hk; apply cnt_nonneg).
  assert (G1 : Gs hk 1 = nR) by (subst hk; rewrite Gs_cnt by (try exact Hk; lia); unfold nR; rewrite <- cnt_true; apply cnt_ext; intros j Hj; symmetry; symmetry; apply Z.leb_le; pose proof (Hk j Hj); lia).
  pose proof (rank_range i Hi) as RR.
  destruct (lev_range hk (rank i) B ltac:(lia)) as (LV & GA & GB).
  set (lv := lev hk (rank i)) in *.
  assert (GB' : cnt (fun j => before j i) L < cnt (fun j => lv <=? kap j) L) by (unfold rank in GB; subst hk; rewrite Gs_cnt in GB by (try exact Hk; lia); exact GB).
  destruct (cnt_pigeon (fun j => lv <=? kap j) (fun j => before j i) L GB') as (j & Hj & Kj & Bj).
  apply Z.leb_le in Kj.
  assert (Wij : w i <= w j).
  { destruct (Z.eq_dec j i) as [->|N]; [lia|]. destruct (before_total j i N) as [Bf|Bf]; [congruence|]. exact (before_w i j Bf). }
  pose proof (FIB j Hj). pose proof (fib_mono (lv + 1) (kap j + 1) ltac:(lia)). pose proof (fib_nonneg (lv + 1)). pose proof (Hw i Hi). nia.
Qed.
End Ranks.


Definition hexL (c L : Z) : Z := if (257 <=? c) && (c <=? 285) then Z.max 0 (L + xl_of_lcode c - 9) else 0.
Definition hexD (d L : Z) : Z := if (0 <=? d) && (d <=? 29) then Z.max 0 (L + xd_of_dcode d - 15) else 0.

Definition ML_l : list Z := [14; 14; 14; 14; 14; 14; 14; 14; 23; 23; 23; 23; 37; 37; 37; 37; 59; 59; 59; 59; 96; 96; 96; 96; 154; 154; 154; 154; 14].
Definition MD_l : list Z := [0; 0; 0; 0; 2; 2; 3; 3; 4; 4; 6; 6; 9; 9; 14; 14; 23; 23; 37; 37; 59; 59; 96; 96; 154; 154; 250; 250; 400; 400].
Definition MofL (c : Z) : Z := if (257 <=? c) && (c <=? 285) then nth (Z.to_nat (c - 257)) ML_l 0 else 0.
Definition MofD (d : Z) : Z := if (0 <=? d) && (d <=? 29) then nth (Z.to_nat d) MD_l 0 else 0.

Lemma forallb_seq : forall (f : Z -> bool) s n, forallb (fun k => f (Z.of_nat k)) (seq s n) = true ->
  forall x, Z.of_nat s <= x < Z.of_nat s + Z.of_nat n -> f x = true.
Proof.
  intros f s n H x Hx. rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma hexL_rarity : forall c L, 1 <= L <= 15 -> 1000 * hexL c L <= MofL c * fib (L + 1).
Proof.
  intros c L HL. unfold hexL, MofL.
  destruct (Z.leb_spec 257 c); destruct (Z.leb_spec c 285); cbn [andb]; try lia.
  pose proof (forallb_seq (fun c => forallb (fun L => 1000 * Z.max 0 (Z.of_nat L + xl_of_lcode c - 9) <=? nth (Z.to_nat (c - 257)) ML_l 0 * fib (Z.of_nat L + 1)) (seq 1 15)) 257 29
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as X. cbv beta in X.
  rewrite forallb_forall in X. specialize (X (Z.to_nat L) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in X by lia. apply Z.leb_le in X. exact X.
Qed.

Lemma hexD_rarity : forall d L, 1 <= L <= 15 -> 1000 * hexD d L <= MofD d * fib (L + 1).
Proof.
  intros d L HL. unfold hexD, MofD.
  destruct (Z.leb_spec 0 d); destruct (Z.leb_spec d 29); cbn [andb]; try lia.
  pose proof (forallb_seq (fun d => forallb (fun L => 1000 * Z.max 0 (Z.of_nat L + xd_of_dcode d - 15) <=? nth (Z.to_nat d) MD_l 0 * fib (Z.of_nat L + 1)) (seq 1 15)) 0 30
                ltac:(vm_compute; reflexivity) d ltac:(lia)) as X. cbv beta in X.
  rewrite forallb_forall in X. specialize (X (Z.to_nat L) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in X by lia. apply Z.leb_le in X. exact X.
Qed.

Lemma MofL_nonneg : forall c, 0 <= MofL c.
Proof.
  intros c. unfold MofL. destruct (Z.leb_spec 257 c); destruct (Z.leb_spec c 285); cbn [andb]; try lia.
  pose proof (forallb_seq (fun c => 0 <=? nth (Z.to_nat (c - 257)) ML_l 0) 257 29 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X. apply Z.leb_le in X. exact X.
Qed.
Lemma MofD_nonneg : forall d, 0 <= MofD d.
Proof.
  intros d. unfold MofD. destruct (Z.leb_spec 0 d); destruct (Z.leb_spec d 29); cbn [andb]; try lia.
  pose proof (forallb_seq (fun d => 0 <=? nth (Z.to_nat d) MD_l 0) 0 30 ltac:(vm_compute; reflexivity) d ltac:(lia)) as X. apply Z.leb_le in X. exact X.
Qed.

Lemma MofL_sum : zsum MofL 0 (Z.to_nat 286) = 1602.
Proof. vm_compute. reflexivity. Qed.
Lemma MofD_sum : zsum MofD 0 (Z.to_nat 30) = 2114.
Proof. vm_compute. reflexivity. Qed.

Lemma hexL_facts : forall c L L', 0 <= hexL c L /\ (L <= L' -> hexL c L <= hexL c L') /\ hexL c L' <= hexL c L + Z.max 0 (L' - L).
Proof. intros. unfold hexL. destruct (_ && _); lia. Qed.
Lemma hexD_facts : forall d L L', 0 <= hexD d L /\ (L <= L' -> hexD d L <= hexD d L') /\ hexD d L' <= hexD d L + Z.max 0 (L' - L).
Proof. intros. unfold hexD. destruct (_ && _); lia. Qed.

Lemma slack540 : forall L, 7 <= L <= 14 -> 540 * (15 - L) <= fib (L + 1) * sz L.
Proof.
  intros L HL. unfold sz.
  pose proof (forallb_seq (fun L => 540 * (15 - L) <=? fib (L + 1) * (2 ^ (15 - L) - 1)) 7 8 ltac:(vm_compute; reflexivity) L ltac:(lia)) as X.
  apply Z.leb_le in X. exact X.
Qed.


Lemma ar_HR1 : forall W M h fb F, 0 <= W -> 0 <= M -> 1000 * h <= M * fb -> W * fb <= F -> 1000 * (W * h) <= M * F.
Proof.
  intros W M h fb F HW HM H1 H2. transitivity (W * (M * fb)).
  - replace (1000 * (W * h)) with (W * (1000 * h)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HW|exact H1].
  - replace (W * (M * fb)) with (M * (W * fb)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HM|exact H2].
Qed.

Lemma ar_X2 : forall W D fb S F, 0 <= W -> 0 <= S -> 540 * D <= fb * S -> W * fb <= F -> 540 * (W * D) <= F * S.
Proof.
  intros W D fb S F HW HS H1 H2. transitivity (W * (fb * S)).
  - replace (540 * (W * D)) with (W * (540 * D)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HW|exact H1].
  - replace (W * (fb * S)) with ((W * fb) * S) by lia. apply Z.mul_le_mono_nonneg_r; [exact HS|exact H2].
Qed.

Lemma ar_touched : forall W F h1 h2 M S L1 L2,
  0 <= W -> 0 <= h1 -> 1000 * (W * h1) <= M * F -> 540 * (W * (15 - L1)) <= F * S ->
  h2 <= h1 + Z.max 0 (L2 - L1) -> L2 <= 15 -> L1 <= 14 ->
  540000 * (W * h2) <= 540 * (M * F) + 1000 * F * S.
Proof.
  intros W F h1 h2 M S L1 L2 HW Hh1 X1 X2 LIP HL2 HL1.
  assert (A : W * h2 <= W * (h1 + (15 - L1))) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma ar_low : forall W F h2 h15 M, 0 <= W -> h2 <= h15 -> 1000 * (W * h15) <= M * F ->
  540000 * (W * h2) <= 540 * (M * F) + 1000 * F * 0.
Proof. intros W F h2 h15 M HW Hh X1. assert (A : W * h2 <= W * h15) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.

Lemma ar_plain : forall W F h M, 1000 * (W * h) <= M * F -> 540000 * (W * h) <= 540 * (M * F) + 1000 * F * 0.
Proof. intros. lia. Qed.

Lemma ar_total : forall T tau s K c15 nl, 0 <= T -> T + (tau - 1) * s <= K - 1 -> s <= nl - 2 -> 1 <= s -> 1 <= tau ->
  K + 1 <= c15 -> c15 <= nl -> 0 <= T + tau * s <= 2 * nl.
Proof. intros. nia. Qed.

Lemma lev_ext : forall (a a' : hist) i, (forall b, 1 <= b <= 15 -> a b = a' b) -> lev a i = lev a' i.
Proof.
  intros a a' i E. unfold lev. apply zsum_ext. intros Lv HL. f_equal. f_equal. unfold Gs. apply zsum_ext. intros b Hb. apply E. lia.
Qed.

Lemma Gs_prefix : forall (a : hist) Lv, 1 <= Lv <= 16 -> Gs a Lv = Gs a 1 - zsum a 1 (Z.to_nat (Lv - 1)).
Proof.
  intros a Lv HL. unfold Gs. replace (Z.to_nat (16 - 1)) with (Z.to_nat (Lv - 1) + Z.to_nat (16 - Lv))%nat by lia.
  rewrite zsum_split. replace (1 + Z.of_nat (Z.to_nat (Lv - 1))) with Lv by lia. lia.
Qed.

Lemma block_sum : forall (a1 : hist) (nl v tau : Z),
  (forall b, 0 <= a1 b) -> Gs a1 1 = nl -> 1 <= v <= 14 -> 0 <= tau <= a1 v ->
  zsum (fun i => if (Gs a1 15 <=? i) && (i <? Gs a1 (v + 1) + tau) then sz (lev a1 i) else 0) 0 (Z.to_nat nl)
  = zsum (fun l => a1 l * sz l) (v + 1) (Z.to_nat (14 - v)) + tau * sz v.
Proof.
  intros a1 nl v tau B G1 Hv Ht.
  pose proof (Gs_mono a1 1 v B ltac:(lia)) as M1. pose proof (Gs_mono a1 (v + 1) 15 B ltac:(lia)) as M2.
  pose proof (Gs_step a1 v ltac:(lia)) as SV. pose proof (Gs_nonneg a1 15 B) as P15.
  set (A := Gs a1 15) in *. set (Bv := Gs a1 (v + 1)) in *.
  replace (Z.to_nat nl) with (Z.to_nat A + (Z.to_nat (Bv - A) + (Z.to_nat tau + Z.to_nat (nl - Bv - tau))))%nat by lia.
  rewrite !zsum_split.
  rewrite (zsum_0 _ 0 (Z.to_nat A)) by (intros i Hi; replace (A <=? i) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  replace (0 + Z.of_nat (Z.to_nat A)) with A by lia.
  replace (A + Z.of_nat (Z.to_nat (Bv - A))) with Bv by lia.
  replace (Bv + Z.of_nat (Z.to_nat tau)) with (Bv + tau) by lia.
  rewrite (zsum_0 _ (Bv + tau) (Z.to_nat (nl - Bv - tau))) by (intros i Hi; replace (i <? Bv + tau) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r; reflexivity).
  rewrite (zsum_ext _ (fun _ => sz v) Bv (Z.to_nat tau)).
  2:{ intros i Hi. replace ((A <=? i) && (i <? Bv + tau)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite (lev_eq a1 i v B ltac:(lia)) by (subst Bv; lia). reflexivity. }
  assert (CS : forall m lo c, zsum (fun _ => c) lo m = Z.of_nat m * c) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
  rewrite CS. replace (Z.of_nat (Z.to_nat tau)) with tau by lia.
  enough (FB : forall n m, Z.of_nat n = 15 - m -> v + 1 <= m <= 15 ->
            zsum (fun i => if (A <=? i) && (i <? Bv + tau) then sz (lev a1 i) else 0) A (Z.to_nat (Gs a1 m - A))
            = zsum (fun l => a1 l * sz l) m n).
  { rewrite <- (FB (Z.to_nat (14 - v)) (v + 1)) by lia. subst Bv. lia. }
  induction n as [|n IH]; intros m En Hm.
  - assert (m = 15) by lia. subst m. subst A. rewrite Z.sub_diag. reflexivity.
  - rewrite zsum_shift.
    pose proof (Gs_step a1 m ltac:(lia)) as SM. pose proof (Gs_mono a1 (v + 1) m B ltac:(lia)) as MM. pose proof (Gs_mono a1 (m + 1) 15 B ltac:(lia)) as MM2.
    pose proof (B m) as Bm.
    replace (Z.to_nat (Gs a1 m - A)) with (Z.to_nat (Gs a1 (m + 1) - A) + Z.to_nat (a1 m))%nat by (subst A; lia).
    rewrite zsum_split. rewrite (IH (m + 1)) by lia.
    replace (A + Z.of_nat (Z.to_nat (Gs a1 (m + 1) - A))) with (Gs a1 (m + 1)) by (subst A; lia).
    rewrite (zsum_ext _ (fun _ => sz m) (Gs a1 (m + 1)) (Z.to_nat (a1 m))).
    2:{ intros i Hi. replace ((A <=? i) && (i <? Bv + tau)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; subst A Bv; lia).
        rewrite (lev_eq a1 i m B ltac:(lia)) by lia. reflexivity. }
    rewrite CS. replace (Z.of_nat (Z.to_nat (a1 m))) with (a1 m) by lia. lia.
Qed.


Section TreeX.
Variable z : ztree.
Variable E : Z.
Variable F : Z -> Z.
Variable Fl : list Z.
Variable hex : Z -> Z -> Z.
Variable M : Z -> Z.
Variable SM : Z.
Hypothesis TF : tree_facts z E 15 F Fl.
Hypothesis HE : E <= 286.
Hypothesis HW : g_W (zt_g z) < fib 24.
Hypothesis HEXF : forall c L L', 0 <= hex c L /\ (L <= L' -> hex c L <= hex c L') /\ hex c L' <= hex c L + Z.max 0 (L' - L).
Hypothesis HEXR : forall c L, 1 <= L <= 15 -> 1000 * hex c L <= M c * fib (L + 1).
Hypothesis M0 : forall c, 0 <= M c.
Hypothesis MS : zsum M 0 (Z.to_nat E) = SM.

Local Notation g := (zt_g z).
Let GG : gtree_ok g := G z E 15 F Fl TF.
Let ZOK : ztree_ok z := tf_ok z E 15 F Fl TF.
Local Notation W := (ffreq F Fl).
Local Notation Lv := (leaves g).
Local Notation wt := (g_wt g).
Local Notation dp := (g_depth g).
Definition kap (i : Z) : Z := Z.min (dp i) 15.
Definition lnz (i : Z) : Z := zt_len z (g_code g i).
Local Notation cd := (g_code g).

Lemma ML15 : zt_ML z = 15. Proof. exact (tf_ML z E 15 F Fl TF). Qed.
Lemma Lv_in' : forall i, In i Lv <-> (g_lo g <= i <= g_hi g /\ g_leaf g i = true).
Proof. intros i. exact (leaves_in g GG i). Qed.
Lemma E0 : 0 <= E. Proof. exact (E_nonneg z E 15 F Fl TF). Qed.

Lemma leaf_facts : forall i, In i Lv -> 1 <= wt i /\ 1 <= dp i <= 22 /\ 1 <= lnz i <= 15 /\ 0 <= cd i < E /\ wt i = W (cd i).
Proof.
  intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L].
  destruct (leaf_W z E 15 F Fl TF i P L) as [C Wc].
  split; [exact (go_wt_leaf g GG i P L)|]. split.
  - split; [| apply (depth_le_of_W z E 15 F Fl TF 22); [exact HW | lia | exact P | exact L]].
    apply (depth_pos g GG). destruct (Z.eq_dec i (g_lo g)) as [->|N]; [rewrite (root_internal g GG) in L; discriminate | lia].
  - split; [| auto]. unfold lnz. rewrite <- ML15. apply (zo_len_used z ZOK (g_code g i) i). split; [exact P | split; [exact L | reflexivity]].
Qed.

Lemma nLv : 2 <= Z.of_nat (length Lv) <= E.
Proof.
  pose proof (tused_two z E 15 F Fl TF) as T2. rewrite (reindex z E 15 F Fl TF (fun _ => 1)) in T2.
  pose proof E0.
  assert (LEN : lsum (fun _ : Z => 1) Lv = Z.of_nat (length Lv)) by (clear; induction (leaves g); cbn [lsum length]; lia).
  rewrite LEN in T2. split; [exact T2|].
  rewrite <- LEN, <- (reindex z E 15 F Fl TF (fun _ => 1)).
  pose proof (zsum_mono (fun c => if W c =? 0 then 0 else 1) (fun _ => 1) 0 (Z.to_nat E) ltac:(intros; cbv beta; destruct (_ =? 0); lia)). rewrite zsum_const1 in H0. lia.
Qed.

Lemma code_sumX : forall h : Z -> Z -> Z, zsum (fun c => W c * h c (zt_len z c)) 0 (Z.to_nat E) = lsum (fun i => wt i * h (cd i) (lnz i)) Lv.
Proof.
  intros h. transitivity (zsum (fun c => if W c =? 0 then 0 else W c * h c (zt_len z c)) 0 (Z.to_nat E)).
  - apply zsum_ext. intros c Hc. destruct (Z.eqb_spec (W c) 0) as [Ez|N]; [rewrite Ez; lia | reflexivity].
  - rewrite (reindex z E 15 F Fl TF (fun c => W c * h c (zt_len z c))). apply lsum_ext. intros i Hi.
    destruct (leaf_facts i Hi) as (_ & _ & _ & _ & Wc). rewrite Wc. reflexivity.
Qed.

Lemma M_sum : lsum (fun i => M (cd i)) Lv <= SM.
Proof.
  rewrite <- MS, <- (reindex z E 15 F Fl TF M). apply zsum_mono. intros c Hc. pose proof (M0 c). destruct (_ =? 0); lia.
Qed.

Lemma HR1 : forall Wc c L Fz, 0 <= Wc -> 1 <= L <= 15 -> Wc * fib (L + 1) <= Fz -> 1000 * (Wc * hex c L) <= M c * Fz.
Proof. intros Wc c L Fz W0 HL WF. apply (ar_HR1 Wc (M c) (hex c L) (fib (L + 1)) Fz W0 (M0 c) (HEXR c L HL) WF). Qed.

Lemma bound_from_leaves : forall (extra : Z -> Z) (X : Z),
  (forall i, In i Lv -> 540000 * (wt i * hex (cd i) (lnz i)) <= 540 * (M (cd i) * g_W g) + 1000 * g_W g * extra i) ->
  (forall i, In i Lv -> 0 <= extra i) -> lsum extra Lv <= X -> 0 <= X <= 2 * E ->
  540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  intros extra X PL EN ES XB. rewrite (code_sumX hex).
  pose proof (W_leaves g GG) as WL. pose proof (lsum_nonneg wt Lv ltac:(intros j Hj; pose proof (leaf_facts j Hj); lia)) as W0. rewrite <- WL in W0.
  transitivity (lsum (fun i => 540 * g_W g * M (cd i) + 1000 * g_W g * extra i) Lv).
  - rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (PL i Hi). lia.
  - rewrite lsum_add, !lsum_scale. pose proof M_sum. nia.
Qed.

Definition c1h (b : Z) : Z := cnt (fun j => kap j =? b) Lv.
Definition Kx : Z := zsum (fun b => c1h b * 2 ^ (15 - b)) 1 15 - 2 ^ 15.

Lemma kap_range : forall i, In i Lv -> 1 <= kap i <= 15.
Proof. intros i Hi. pose proof (leaf_facts i Hi). unfold kap. lia. Qed.

Lemma c1h_ok : levels_ok c1h /\ zsum c1h 1 15 = Z.of_nat (length Lv) /\ (forall b, 0 <= c1h b).
Proof.
  assert (B : forall b, 0 <= c1h b) by (intros; unfold c1h; apply cnt_nonneg).
  split; [|split; [|exact B]].
  - intros b. split; [apply B|]. intros Hb. unfold c1h, cnt.
    etransitivity; [apply lsum_ext; intros j Hj; replace (kap j =? b) with false by (symmetry; apply Z.eqb_neq; pose proof (kap_range j Hj); lia); reflexivity | apply lsum_zero].
  - unfold c1h. rewrite <- (Gs_1 (fun b => cnt (fun j : Z => kap j =? b) Lv)). rewrite (Gs_cnt Lv kap 1 kap_range ltac:(lia)).
    rewrite <- cnt_true. apply cnt_ext. intros j Hj. pose proof (kap_range j Hj). symmetry. symmetry. apply Z.leb_le. lia.
Qed.

Lemma Kx_ok : forall i0, In i0 Lv -> 15 < dp i0 -> 1 <= Kx /\ Kx + 1 <= c1h 15.
Proof.
  intros i0 Hi0 D0.
  assert (KRb : zsum (fun b => c1h b * 2 ^ (15 - b)) 1 15 = lsum (fun i => 2 ^ (15 - kap i)) Lv).
  { unfold c1h, cnt. rewrite (zsum_ext _ (fun b => lsum (fun i => zind (kap i =? b) * 2 ^ (15 - b)) Lv)) by (intros; rewrite Z.mul_comm, <- lsum_scale; apply lsum_ext; intros; lia).
    rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (kap_range i Hi).
    rewrite (zsum_single (fun b => zind (kap i =? b) * 2 ^ (15 - b)) 1 15 (kap i)); [rewrite Z.eqb_refl; cbn [zind]; lia | lia |].
    intros b Hb Nb. replace (kap i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof (kraft_eq g GG 22 ltac:(intros i P L; pose proof (leaf_facts i ltac:(apply Lv_in'; auto)); lia)) as KR22.
  assert (MC : cnt (fun i => 15 <? dp i) Lv <= c1h 15).
  { unfold c1h. apply cnt_mono. intros i Hi X. apply Z.ltb_lt in X. apply Z.eqb_eq. unfold kap. lia. }
  assert (M1 : 1 <= cnt (fun i => 15 <? dp i) Lv).
  { unfold cnt. pose proof (lsum_ge_member (fun i => zind (15 <? dp i)) Lv i0 ltac:(intros; apply (proj1 (zind_le1 _))) Hi0) as X.
    cbv beta in X. replace (15 <? dp i0) with true in X by (symmetry; apply Z.ltb_lt; exact D0). cbn [zind] in X. exact X. }
  assert (E7 : 128 * lsum (fun i => 2 ^ (15 - kap i)) Lv = lsum (fun i => 2 ^ (22 - dp i)) Lv + lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv).
  { rewrite <- lsum_scale, <- lsum_add. apply lsum_ext. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _). unfold kap.
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind].
    - rewrite Z.min_r by lia. change (2 ^ (15 - 15)) with 1. lia.
    - rewrite Z.min_l by lia. replace (22 - dp i) with (7 + (15 - dp i)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 7) with 128. lia. }
  rewrite KR22 in E7. change (2 ^ 22) with (128 * 2 ^ 15) in E7.
  assert (LO : 64 * cnt (fun i => 15 <? dp i) Lv <= lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv).
  { unfold cnt. rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _).
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind]; [|lia].
    assert (P6 : 2 ^ (22 - dp i) <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2 ^ 6) with 64 in P6. lia. }
  assert (HI : lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv <= 127 * cnt (fun i => 15 <? dp i) Lv).
  { unfold cnt. rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _).
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind]; [|lia]. pose proof (pow15_pos (dp i - 7) ltac:(lia)) as PP. replace (15 - (dp i - 7)) with (22 - dp i) in PP by lia. lia. }
  unfold Kx. rewrite KRb.
  revert E7 LO HI M1 MC. generalize (lsum (fun i => 2 ^ (15 - kap i)) Lv) as S1. generalize (lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv) as S2.
  generalize (cnt (fun i => 15 <? dp i) Lv) as m. generalize (c1h 15) as c15. intros. lia.
Qed.

Lemma per_leaf : forall (a2 : hist) (v tau n : Z) (r L1 L2 Wi c Fz : Z),
  (forall b, 0 <= c1h b) -> (forall b, 0 <= a2 b) ->
  Gs c1h 1 = n -> Gs a2 1 = n -> 7 <= v <= 14 -> 1 <= tau <= c1h v ->
  (forall Lx, 1 <= Lx <= v -> Gs a2 Lx = Gs c1h Lx) -> Gs a2 (v + 1) = Gs c1h (v + 1) + tau ->
  0 <= r < n -> L1 = lev c1h r -> L2 = lev a2 r -> 1 <= Wi -> 1 <= L2 <= 15 ->
  Wi * fib (L1 + 1) <= Fz ->
  540000 * (Wi * hex c L2)
    <= 540 * (M c * Fz) + 1000 * Fz * (if (Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau) then sz L1 else 0).
Proof.
  intros a2 v tau n r L1 L2 Wi c Fz B1 B2 G11 G21 Hv Ht GEQ GV1 RR EL1 EL2 HWi HL2 RRY.
  pose proof (lev_range a2 r B2 ltac:(rewrite G21; lia)) as [L2R [G2a G2b]]. rewrite <- EL2 in L2R, G2a, G2b.
  pose proof (lev_range c1h r B1 ltac:(rewrite G11; lia)) as [L1R [G1a G1b]]. rewrite <- EL1 in L1R, G1a, G1b.
  pose proof (Gs_mono c1h (v + 1) 15 B1 ltac:(lia)) as M15. pose proof (Gs_step c1h v ltac:(lia)) as SV.
  pose proof (fun (HLx : 1 <= L1 + 1 <= v) => Gs_mono c1h (L1 + 1) v B1 ltac:(lia)) as MA.
  pose proof (fun (HLx : v + 1 <= L2 <= 16) => Gs_mono a2 (v + 1) L2 B2 HLx) as MB.
  pose proof (fun (HLx : 1 <= L2 <= v) => GEQ L2 HLx) as GE2.
  pose proof (fun (HLx : 1 <= L2 + 1 <= v) => GEQ (L2 + 1) HLx) as GE2'.
  pose proof (lev_eq c1h r 15 B1 ltac:(lia)) as LE15. rewrite Gs_16 in LE15. rewrite <- EL1 in LE15.
  pose proof (lev_eq c1h r L2 B1) as LE2. rewrite <- EL1 in LE2.
  pose proof (HR1 Wi c) as HRp. pose proof (proj1 (proj2 (HEXF c L2 15))) as HM.
  pose proof (proj2 (proj2 (HEXF c L1 L2))) as LIP. pose proof (proj1 (HEXF c L1 0)) as HN1.
  destruct (Z.lt_ge_cases r (Gs c1h 15)) as [LOWR|HIR].
  - replace (Gs c1h 15 <=? r) with false by (symmetry; apply Z.leb_gt; exact LOWR). cbn [andb].
    assert (E1 : L1 = 15) by (apply LE15; lia).
    apply (ar_low Wi Fz (hex c L2) (hex c 15) (M c) ltac:(lia) ltac:(apply HM; lia)).
    apply HRp; [lia|lia|]. rewrite <- E1. exact RRY.
  - destruct (Z.lt_ge_cases r (Gs c1h (v + 1) + tau)) as [TOU|UNT].
    + replace ((Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; exact HIR|apply Z.ltb_lt; exact TOU]).
      assert (L114 : L1 <= 14) by (destruct (Z.eq_dec L1 15) as [E1|NE]; [rewrite E1 in G1b; lia|lia]).
      assert (L1v : v <= L1) by (destruct (Z.lt_ge_cases L1 v) as [LT|GE]; [specialize (MA ltac:(lia)); lia|exact GE]).
      pose proof (HRp L1 Fz ltac:(lia) ltac:(lia) RRY) as X1.
      assert (X2 : 540 * (Wi * (15 - L1)) <= Fz * sz L1).
      { apply (ar_X2 Wi (15 - L1) (fib (L1 + 1)) (sz L1) Fz ltac:(lia)); [| apply slack540; lia | exact RRY]. pose proof (sz_facts L1 ltac:(lia)). lia. }
      exact (ar_touched Wi Fz (hex c L1) (hex c L2) (M c) (sz L1) L1 L2 ltac:(lia) HN1 X1 X2 LIP ltac:(lia) L114).
    + replace (r <? Gs c1h (v + 1) + tau) with false by (symmetry; apply Z.ltb_ge; exact UNT). rewrite Bool.andb_false_r.
      assert (L2v : L2 <= v) by (destruct (Z.lt_ge_cases v L2) as [LT|GE]; [specialize (MB ltac:(lia)); lia|exact GE]).
      assert (E12 : L1 = L2).
      { apply LE2; [lia|]. rewrite <- (GE2 ltac:(lia)). split; [|exact G2b].
        destruct (Z.eq_dec L2 v) as [E2|NE]; [rewrite E2; lia|]. rewrite <- (GE2' ltac:(lia)). exact G2a. }
      apply (ar_plain Wi Fz (hex c L2) (M c)). apply HRp; [lia|exact HL2|]. rewrite <- E12. exact RRY.
Qed.

Lemma excess_ov : forall i0, In i0 Lv -> 15 < dp i0 ->
  540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  intros i0 Hi0 D0. pose proof nLv as NL.
  assert (W0 : forall i, In i Lv -> 0 <= wt i) by (intros i Hi; pose proof (leaf_facts i Hi); lia).
  assert (FIBd : forall i, In i Lv -> wt i * fib (dp i + 1) <= g_W g).
  { intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L]. pose proof (fib_bound g GG i P). lia. }
  assert (OV : exists i, g_pos g i /\ g_leaf g i = true /\ zt_ML z < g_depth g i).
  { exists i0. rewrite ML15. apply Lv_in' in Hi0. destruct Hi0 as [P L]. auto. }
  destruct c1h_ok as (C1OK & C1T & B1). destruct (Kx_ok i0 Hi0 D0) as [K1 KC].
  destruct (repair_profile c1h (Z.of_nat (length Lv)) Kx C1OK C1T ltac:(unfold Kx; lia) KC K1 ltac:(lia)) as (OK2 & T2 & KR2 & v & tau & Hv & Ht & NB & LOW & AV & STEPS).
  remember (repair 15 c1h) as a2 eqn:Ea2.
  assert (B2 : forall b, 0 <= a2 b) by (intros b; apply (proj1 (OK2 b))).
  assert (HL : forall b, 1 <= b <= 15 -> cnt (fun j => lnz j =? b) Lv = a2 b).
  { intros b Hb. rewrite Ea2. unfold lnz. rewrite <- (g_hist_cnt z (fun i => zt_len z (g_code g i)) b). rewrite (zo_len_hist z ZOK b) by (rewrite ML15; exact Hb).
    rewrite ML15. apply d_repair_ext. intros x. rewrite (g_hist_cnt z). reflexivity. }
  assert (LR : forall i j, In i Lv -> In j Lv -> wt j < wt i -> lnz i <= lnz j).
  { intros i j Hi Hj Wij. apply Lv_in' in Hi. apply Lv_in' in Hj. destruct Hi as [Pi Li], Hj as [Pj Lj]. unfold lnz. exact (zo_len_rank z ZOK OV j i Pj Pi Lj Li Wij). }
  pose proof (leaves_nodup g) as ND.
  assert (NR : nR Lv = Z.of_nat (length Lv)) by reflexivity.
  assert (G11 : Gs c1h 1 = Z.of_nat (length Lv)) by (rewrite Gs_1; exact C1T).
  assert (G21 : Gs a2 1 = Z.of_nat (length Lv)) by (rewrite Gs_1; exact T2).
  assert (GEQ : forall Lx, 1 <= Lx <= v -> Gs a2 Lx = Gs c1h Lx).
  { intros Lx HLx. rewrite (Gs_prefix a2 Lx), (Gs_prefix c1h Lx) by lia. rewrite G11, G21.
    rewrite (zsum_ext a2 c1h); [reflexivity|]. intros b Hb. apply LOW. lia. }
  assert (GV1 : Gs a2 (v + 1) = Gs c1h (v + 1) + tau).
  { rewrite (Gs_prefix a2 (v + 1)), (Gs_prefix c1h (v + 1)) by lia. rewrite G11, G21.
    replace (Z.to_nat (v + 1 - 1)) with (S (Z.to_nat (v - 1)))%nat by lia. rewrite !zsum_snoc.
    replace (1 + Z.of_nat (Z.to_nat (v - 1))) with v by lia. rewrite AV.
    rewrite (zsum_ext a2 c1h) by (intros b Hb; apply LOW; lia). lia. }
  pose proof (Gs_mono c1h (v + 1) 15 B1 ltac:(lia)) as M15. pose proof (Gs_nonneg c1h 15 B1) as P15.
  pose proof (Gs_mono c1h 1 v B1 ltac:(lia)) as M1v. rewrite G11 in M1v.
  pose proof (Gs_step c1h v ltac:(lia)) as SV.
  assert (V7 : 7 <= v).
  { destruct (Z.lt_ge_cases v 7) as [LT|GE]; [|exact GE]. exfalso.
    assert (P9 : 2 ^ 9 <= 2 ^ (15 - v)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in P9. lia. }
  apply (bound_from_leaves (fun i => if (Gs c1h 15 <=? rank Lv wt lnz i) && (rank Lv wt lnz i <? Gs c1h (v + 1) + tau) then sz (lev c1h (rank Lv wt lnz i)) else 0)
           (Tc c1h v + tau * sz v)).
  -
    intros i Hi. pose proof (leaf_facts i Hi) as (Wi & Di & Li & Ci & Wc).
    pose proof (rank_range Lv wt lnz ND i Hi) as RR. rewrite NR in RR.
    pose proof (rank_rarity Lv wt lnz ND kap (g_W g) kap_range W0
                  ltac:(intros j Hj; pose proof (FIBd j Hj); pose proof (Z.mul_le_mono_nonneg_l (fib (kap j + 1)) (fib (dp j + 1)) (wt j) (W0 j Hj) (fib_mono (kap j + 1) (dp j + 1) ltac:(pose proof (kap_range j Hj); unfold kap in *; lia))); lia) i Hi) as RRY.
    pose proof (lev_hlam Lv wt lnz ND LR ltac:(intros j Hj; pose proof (leaf_facts j Hj); lia) i Hi) as EL2. unfold hlam in EL2.
    rewrite (lev_ext (fun b => cnt (fun j => lnz j =? b) Lv) a2) in EL2 by exact HL.
    apply (per_leaf a2 v tau (Z.of_nat (length Lv)) (rank Lv wt lnz i) (lev c1h (rank Lv wt lnz i)) (lnz i) (wt i) (cd i) (g_W g) B1 B2 G11 G21 ltac:(lia) Ht GEQ GV1 ltac:(lia) eq_refl (eq_sym EL2) Wi Li RRY).
  -
    intros i Hi. destruct (_ && _); [|lia]. pose proof (rank_range Lv wt lnz ND i Hi) as RR. rewrite NR in RR.
    pose proof (lev_range c1h (rank Lv wt lnz i) B1 ltac:(rewrite G11; lia)) as [LR1 _].
    destruct (Z.eq_dec (lev c1h (rank Lv wt lnz i)) 15) as [E15|N15]; [rewrite E15; unfold sz; cbn; lia|].
    pose proof (sz_facts (lev c1h (rank Lv wt lnz i)) ltac:(lia)). lia.
  -
    rewrite (sum_by_rank Lv wt lnz ND (fun r => if (Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau) then sz (lev c1h r) else 0)).
    rewrite NR, <- G11. rewrite (block_sum c1h (Gs c1h 1) v tau B1 eq_refl ltac:(lia) ltac:(lia)). unfold Tc. lia.
  -
    pose proof (Tc_nonneg c1h (Z.of_nat (length Lv)) Kx C1OK C1T ltac:(unfold Kx; lia) K1 ltac:(lia) v ltac:(lia)) as T0.
    assert (SZ : sz v <= Z.of_nat (length Lv) - 2) by (unfold sz; lia). pose proof (proj1 (sz_facts v ltac:(lia))) as SP.
    assert (C15 : c1h 15 <= Z.of_nat (length Lv)) by (rewrite <- C1T; apply (zsum_ge_point c1h 1 15 15); [intros; apply B1 | lia]).
    pose proof (ar_total (Tc c1h v) tau (sz v) Kx (c1h 15) (Z.of_nat (length Lv)) T0 STEPS SZ SP ltac:(lia) KC C15). lia.
Qed.

Theorem tree_excess_gen : 540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  pose proof nLv as NL.
  assert (W0 : forall i, In i Lv -> 0 <= wt i) by (intros i Hi; pose proof (leaf_facts i Hi); lia).
  assert (FIBd : forall i, In i Lv -> wt i * fib (dp i + 1) <= g_W g).
  { intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L]. pose proof (fib_bound g GG i P). lia. }
  destruct (existsb (fun i => 15 <? dp i) Lv) eqn:OVF.
  - apply existsb_exists in OVF. destruct OVF as (i0 & Hi0 & D0). apply Z.ltb_lt in D0. exact (excess_ov i0 Hi0 D0).
  -
    assert (NOV : forall j, g_pos g j -> g_leaf g j = true -> g_depth g j <= zt_ML z).
    { intros j Pj Lj. rewrite ML15. destruct (Z_lt_le_dec 15 (g_depth g j)) as [D15|D15]; [|exact D15]. exfalso.
      apply Bool.not_true_iff_false in OVF. apply OVF. apply existsb_exists. exists j. split; [apply Lv_in'; auto | apply Z.ltb_lt; exact D15]. }
    apply (bound_from_leaves (fun _ => 0) 0); [| intros; lia | rewrite lsum_zero; lia | pose proof E0; lia].
    intros i Hi. pose proof (leaf_facts i Hi) as (Wi & Di & Li & Ci & Wc).
    assert (EQ : lnz i = dp i).
    { unfold lnz. apply Lv_in' in Hi. destruct Hi as [P L]. exact (zo_len_noovf z ZOK NOV (g_code g i) i ltac:(split; [exact P | split; [exact L | reflexivity]])). }
    rewrite EQ. apply (ar_plain (wt i) (g_W g) (hex (cd i) (dp i)) (M (cd i))).
    apply HR1; [lia| lia |]. exact (FIBd i Hi).
Qed.
End TreeX.

Theorem tree_excess_L (z : ztree) (F : Z -> Z) (Fl : list Z) :
  tree_facts z 286 15 F Fl -> g_W (zt_g z) < fib 24 ->
  540000 * zsum (fun c => ffreq F Fl c * hexL c (zt_len z c)) 0 (Z.to_nat 286)
  <= g_W (zt_g z) * (540 * 1602 + 2000 * 286).
Proof.
  intros TF HW. exact (tree_excess_gen z 286 F Fl hexL MofL 1602 TF ltac:(lia) HW hexL_facts hexL_rarity MofL_nonneg MofL_sum).
Qed.

Theorem tree_excess_D (z : ztree) (F : Z -> Z) (Fl : list Z) :
  tree_facts z 30 15 F Fl -> g_W (zt_g z) < fib 24 ->
  540000 * zsum (fun d => ffreq F Fl d * hexD d (zt_len z d)) 0 (Z.to_nat 30)
  <= g_W (zt_g z) * (540 * 2114 + 2000 * 30).
Proof.
  intros TF HW. exact (tree_excess_gen z 30 F Fl hexD MofD 2114 TF ltac:(lia) HW hexD_facts hexD_rarity MofD_nonneg MofD_sum).
Qed.
End OverlayExcess.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.OverlayLarge.OverlayExcess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Large.
Variable b : oblock.
Variable lbs : Z.
Hypothesis OK : oblock_ok b lbs.
Hypothesis LBS : 1456 <= lbs <= 32768.

Notation lenL := (ob_lenL b).
Notation lenD := (ob_lenD b).
Notation BC := (ob_BC b).
Notation BD := (ob_BD b).
Notation syms := (ob_syms b).

Lemma Hc1_crude : 0 <= ob_Hc1 b <= 4495.
Proof.
  pose proof (ok_Hc1 b lbs OK) as E. pose proof (ok_blc b lbs OK) as [BL _]. pose proof (ok_WB b lbs OK) as WB.
  assert (S1 : 0 <= zsum (fun x => BC x * (BD x + xb_of_bl x)) 0 19 <= 14 * zsum BC 0 19).
  { rewrite <- zsum_scale. split.
    - apply zsum_nonneg. intros x Hx. pose proof (BC_nonneg b lbs OK x ltac:(lia)). pose proof (BD_range b lbs OK x ltac:(lia)).
      assert (0 <= xb_of_bl x <= 7) by (unfold xb_of_bl; destruct (x =? 16); [lia|]; destruct (x =? 17); [lia|]; destruct (x =? 18); lia). nia.
    - apply zsum_mono. intros x Hx. pose proof (BC_nonneg b lbs OK x ltac:(lia)). pose proof (BD_range b lbs OK x ltac:(lia)).
      assert (0 <= xb_of_bl x <= 7) by (unfold xb_of_bl; destruct (x =? 16); [lia|]; destruct (x =? 17); [lia|]; destruct (x =? 18); lia). nia. }
  lia.
Qed.

Lemma exS_split s0 : In s0 syms ->
  exS b s0 <= match s0 with OLit _ => 0 | OPair lc dc => hexL lc (lenL lc) + hexD dc (lenD dc) end.
Proof.
  intros I. pose proof (sym_ok_in b lbs OK s0 I) as SO. unfold exS. destruct s0 as [c|lc dc]; cbn [dcostS]; cbn in SO.
  - pose proof (in_syms_fL b _ I) as U. cbn [keyL] in U. pose proof (lenL_used b lbs OK c ltac:(lia) ltac:(lia)). lia.
  - unfold hexL, hexD.
    replace ((257 <=? lc) && (lc <=? 285)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    replace ((0 <=? dc) && (dc <=? 29)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    lia.
Qed.

Lemma EX_split : vEX b <= lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286) + lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30).
Proof.
  unfold vEX. rewrite (lsum_fL_w b lbs (fun c => hexL c (lenL c)) 0 286), (lsum_gD_w b lbs OK (fun d => hexD d (lenD d))).
  replace (existsb (Z.eqb 256) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists 256; split; [apply zrange_in; lia|reflexivity]).
  replace (hexL 256 (lenL 256)) with 0 by reflexivity. rewrite Z.add_0_r, <- ssum_add.
  apply ssum_le. intros s0 I. pose proof (exS_split s0 I) as X. pose proof (sym_ok_in b lbs OK s0 I) as SO.
  destruct s0 as [c|lc dc]; cbn [keyL]; cbn in SO.
  - replace (existsb (Z.eqb c) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists c; split; [apply zrange_in; lia|apply Z.eqb_refl]).
    unfold hexL. replace ((257 <=? c) && (c <=? 285)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). lia.
  - replace (existsb (Z.eqb lc) (zrange 0 286)) with true by (symmetry; apply existsb_exists; exists lc; split; [apply zrange_in; lia|apply Z.eqb_refl]).
    lia.
Qed.

Lemma EXL_bound : 540000 * lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286) <= (NSYM b + 1) * (540 * 1602 + 2000 * 286).
Proof.
  destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). pose proof (TL_W b lbs OK zL TF) as W. pose proof (ok_N b lbs OK).
  pose proof (tree_excess_L zL (fL b) [] TF ltac:(rewrite W; change (fib 24) with 46368; lia)) as X. rewrite W in X.
  change (Z.to_nat 286) with 286%nat in X. rewrite <- lsum_zrange in X.
  rewrite (lsum_ext (fun c => ffreq (fL b) [] c * hexL c (zt_len zL c)) (fun c => hexL c (lenL c) * fL b c)) in X; [exact X|].
  intros c Hc. apply zrange_in in Hc. rewrite ffreq_nil. rewrite <- EL by lia. lia.
Qed.

Lemma hexD_nonneg d L : 0 <= hexD d L.
Proof. unfold hexD. destruct (_ && _); lia. Qed.

Lemma EXD_bound : 540000 * lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30) <= (NSYM b + 2) * (540 * 2114 + 2000 * 30).
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). pose proof (TD_W b lbs OK zD TF) as W. pose proof (WD_le b lbs OK) as WDle. pose proof (ok_N b lbs OK).
  assert (WDle2 : WD b <= NSYM b + 2).
  { unfold WD. destruct (forced_facts b lbs OK) as (_ & LF & _). unfold vP.
    pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). unfold NSYM. lia. }
  pose proof (tree_excess_D zD (gD b) (ob_forced b) TF ltac:(rewrite W; change (fib 24) with 46368; lia)) as X. rewrite W in X.
  change (Z.to_nat 30) with 30%nat in X. rewrite <- lsum_zrange in X.
  assert (Y : lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30) <= lsum (fun d => ffreq (gD b) (ob_forced b) d * hexD d (zt_len zD d)) (zrange 0 30)).
  { apply lsum_le. intros d Hd. apply zrange_in in Hd. rewrite <- EL by lia. rewrite ffreqD.
    pose proof (hexD_nonneg d (lenD d)). pose proof (gD_nonneg b d).
    destruct (forcedD b d) eqn:Fd; [|lia]. apply (forcedD_spec b) in Fd. destruct (forced_facts b lbs OK) as (_ & _ & FF). destruct (FF d Fd). nia. }
  assert (0 <= WD b) by (unfold WD; unfold vP; pose proof (scount_nonneg (fun s => match s with OLit _ => false | OPair _ _ => true end) syms); lia).
  nia.
Qed.

Theorem overlay_bound_large : vH b + vEX b <= 8 * lbs - 10.
Proof.
  pose proof Hc1_crude as [H0 H1]. pose proof EX_split as E. pose proof EXL_bound as XL. pose proof EXD_bound as XD.
  pose proof (ok_N b lbs OK) as N. unfold vH.
  set (A := lsum (fun c => hexL c (lenL c) * fL b c) (zrange 0 286)) in *.
  set (B := lsum (fun d => hexD d (lenD d) * gD b d) (zrange 0 30)) in *.
  clearbody A B. nia.
Qed.

End Large.
