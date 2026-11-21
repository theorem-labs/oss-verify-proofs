(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayTF.
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

Lemma W_cases c : 0 <= c < E -> W c = 0 \/ (1 <= W c /\ g_pos g (tpos z c) /\ g_leaf g (tpos z c) = true /\ g_code g (tpos z c) = c).
Proof.
  intros Hc. destruct (Z.eq_dec (W c) 0) as [Z0|NZ]; [left; exact Z0|right].
  destruct (tpos_spec c Hc NZ) as (P & L & C). destruct (leaf_W _ P L) as [_ Wi]. rewrite C in Wi.
  pose proof (go_wt_leaf g G _ P L). split; [lia|]. split; [exact P|]. split; [exact L|exact C].
Qed.

Lemma W_nonneg c : 0 <= c < E -> 0 <= W c.
Proof. intros Hc. destruct (W_cases c Hc); lia. Qed.

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

Lemma depth_le_of_W D : g_W g < fib (D + 2) -> 0 <= D -> forall i, g_pos g i -> g_leaf g i = true -> g_depth g i <= D.
Proof.
  intros HW HD i Pi Li. pose proof (fib_bound g G i Pi) as FB. pose proof (go_wt_leaf g G i Pi Li).
  destruct (Z_le_gt_dec (g_depth g i) D); [assumption|exfalso].
  pose proof (fib_mono (D + 2) (g_depth g i + 1) ltac:(lia)). pose proof (fib_nonneg (g_depth g i + 1)). nia.
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
