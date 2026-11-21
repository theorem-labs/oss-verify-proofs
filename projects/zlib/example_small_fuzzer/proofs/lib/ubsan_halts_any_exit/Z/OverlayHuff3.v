(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lsum_perm f l l' : Permutation l l' -> lsum f l = lsum f l'.
Proof. induction 1; cbn; lia. Qed.

Lemma lmax_lub sg F M : 0 <= M -> (forall x, In x F -> sg x <= M) -> lmax sg F <= M.
Proof. induction F as [|y r IH]; cbn; intros HM H; [lia|]. pose proof (H y (or_introl eq_refl)). specialize (IH HM ltac:(intros; apply H; tauto)). lia. Qed.

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
Notation allpos := (allpos g).
Notation nonroot := (nonroot g).
Notation leaves := (leaves g).
Notation internals := (internals g).
Let allpos_in := allpos_in g G. Let nonroot_in := nonroot_in g G. Let leaves_in := leaves_in g G.
Let internals_in := internals_in g G. Let depth_step := depth_step g G. Let wt_nonneg := wt_nonneg g G.
Let depth_nonneg := depth_nonneg g G. Let depth_root := depth_root g G. Let lohi := lohi g G.
Let root_internal := root_internal g G. Let ext_mono := ext_mono g G.
Let allpos_nodup := allpos_nodup g. Let nonroot_nodup := nonroot_nodup g. Let leaves_nodup := leaves_nodup g.

Definition born (x : Z) : Z :=
  if leaf x then 0 else 1 + lmax (fun c => if par c =? x then ext c else 0) nonroot.

Definition alive (T x : Z) : bool := (born x <=? T) && ((x =? lo) || (T <=? ext x)).
Definition forest (T : Z) : list Z := filter (alive T) allpos.
Definition rest (T : Z) : Z := lsum (fun p => if negb (leaf p) && (T <? born p) then wt p else 0) allpos.
Definition Tend : Z := born lo.

Lemma sibling a : lo < a <= hi ->
  exists b, lo < b <= hi /\ b <> a /\ par b = par a /\
            (forall c, lo < c <= hi -> par c = par a -> c = a \/ c = b) /\
            (ext a = ext b + 1 \/ ext b = ext a + 1) /\ wt (par a) = wt a + wt b.
Proof.
  intros Ha. pose proof (go_par_lt g G a Ha) as P. pose proof (go_par_int g G a Ha) as I.
  destruct (go_two g G (par a) ltac:(unfold g_pos; lia) I) as (u & v & NE & Hu & Hv & Pu & Pv & ONLY).
  assert (W := go_wt_sum g G (par a) u v ltac:(unfold g_pos; lia) I Hu Hv NE Pu Pv).
  destruct (ONLY a Ha eq_refl) as [E|E].
  - subst u. exists v. split; [exact Hv|]. split; [congruence|]. split; [congruence|]. split.
    { intros c Hc Pc. destruct (ONLY c Hc ltac:(congruence)); auto. }
    split; [|congruence]. apply (go_ext_sib g G); auto; congruence.
  - subst v. exists u. split; [exact Hu|]. split; [congruence|]. split; [congruence|]. split.
    { intros c Hc Pc. destruct (ONLY c Hc ltac:(congruence)); auto. }
    split; [apply (go_ext_sib g G); auto; congruence|]. lia.
Qed.

Lemma born_leaf x : leaf x = true -> born x = 0.
Proof. intros L. unfold born. rewrite L. reflexivity. Qed.

Lemma born_child c : lo < c <= hi -> ext c + 1 <= born (par c).
Proof.
  intros Hc. unfold born. rewrite (go_par_int g G c Hc).
  pose proof (lmax_ge (fun c0 => if par c0 =? par c then ext c0 else 0) nonroot c ltac:(apply nonroot_in; exact Hc)).
  cbn in H. rewrite Z.eqb_refl in H. lia.
Qed.

Lemma born_int x a b : lo <= x <= hi -> leaf x = false -> lo < a <= hi -> lo < b <= hi -> a <> b -> par a = x -> par b = x ->
  born x = 1 + Z.max (ext a) (ext b).
Proof.
  intros Hx L Ha Hb NE Pa Pb. unfold born. rewrite L.
  destruct (go_two g G x Hx L) as (u & v & NE' & Hu & Hv & Pu & Pv & ONLY).
  assert (forall c, lo < c <= hi -> par c = x -> ext c <= Z.max (ext a) (ext b)).
  { intros c Hc Pc. destruct (ONLY c Hc Pc) as [->| ->]; destruct (ONLY a Ha Pa) as [E1|E1]; destruct (ONLY b Hb Pb) as [E2|E2]; subst; try lia; congruence. }
  apply Z.le_antisymm.
  - enough (lmax (fun c : Z => if par c =? x then ext c else 0) nonroot <= Z.max (ext a) (ext b)) by lia.
    apply lmax_lub. { pose proof (go_ext_nonneg g G a Ha). lia. }
    intros c Hc. apply nonroot_in in Hc. destruct (Z.eqb_spec (par c) x); [apply H; assumption|]. pose proof (go_ext_nonneg g G a Ha). lia.
  - pose proof (lmax_ge (fun c : Z => if par c =? x then ext c else 0) nonroot a ltac:(apply nonroot_in; exact Ha)).
    pose proof (lmax_ge (fun c : Z => if par c =? x then ext c else 0) nonroot b ltac:(apply nonroot_in; exact Hb)).
    cbn in H0, H1. rewrite Pa, Z.eqb_refl in H0. rewrite Pb, Z.eqb_refl in H1. lia.
Qed.

Lemma born_le_ext x : lo < x <= hi -> born x <= ext x.
Proof.
  intros Hx. destruct (leaf x) eqn:L; [rewrite born_leaf by assumption; apply (go_ext_nonneg g G); assumption|].
  destruct (go_two g G x ltac:(unfold g_pos; lia) L) as (a & b & NE & Ha & Hb & Pa & Pb & _).
  rewrite (born_int x a b ltac:(lia) L Ha Hb NE Pa Pb).
  pose proof (go_ext_par g G a Ha ltac:(rewrite Pa; lia)). pose proof (go_ext_par g G b Hb ltac:(rewrite Pb; lia)).
  rewrite Pa in H. rewrite Pb in H0. lia.
Qed.

Lemma born_nonneg x : lo <= x <= hi -> 0 <= born x.
Proof.
  intros Hx. unfold born. destruct (leaf x); [lia|].
  enough (0 <= lmax (fun c : Z => if par c =? x then ext c else 0) nonroot) by lia.
  apply lmax_nonneg. intros c Hc. apply nonroot_in in Hc. destruct (par c =? x); [apply (go_ext_nonneg g G); assumption|lia].
Qed.

Lemma ext_lt_Tend x : lo < x <= hi -> ext x < Tend.
Proof.
  intros Hx. remember (Z.to_nat (x - lo)) as n eqn:E. revert x Hx E.
  induction n as [n IH] using lt_wf_ind; intros x Hx E.
  pose proof (born_child x Hx). pose proof (go_par_lt g G x Hx).
  destruct (Z.eq_dec (par x) lo) as [EQ|NE].
  - unfold Tend. rewrite <- EQ. lia.
  - pose proof (born_le_ext (par x) ltac:(lia)).
    assert (ext (par x) < Tend) by (apply (IH (Z.to_nat (par x - lo))); lia). lia.
Qed.

Lemma born_le_Tend x : lo <= x <= hi -> born x <= Tend.
Proof.
  intros Hx. destruct (Z.eq_dec x lo) as [->|NE]; [unfold Tend; lia|].
  pose proof (born_le_ext x ltac:(lia)). pose proof (ext_lt_Tend x ltac:(lia)). lia.
Qed.

Lemma born_internal_pos x : lo <= x <= hi -> leaf x = false -> 1 <= born x.
Proof.
  intros Hx L. destruct (go_two g G x Hx L) as (a & b & NE & Ha & Hb & Pa & Pb & _).
  pose proof (born_child a Ha). rewrite Pa in H. pose proof (go_ext_nonneg g G a Ha). lia.
Qed.

Lemma Tend_pos : 1 <= Tend.
Proof. unfold Tend. apply born_internal_pos; [pose proof lohi; lia | exact root_internal]. Qed.

Lemma forest_in T x : In x (forest T) <-> (lo <= x <= hi /\ alive T x = true).
Proof. unfold forest. rewrite filter_In, allpos_in by assumption. tauto. Qed.

Lemma forest_nodup T : NoDup (forest T). Proof. unfold forest. apply NoDup_filter, allpos_nodup. Qed.


Lemma forest_0_in x : In x (forest 0) <-> In x leaves.
Proof.
  rewrite forest_in, leaves_in. unfold alive.
  split.
  - intros [Hx A]. split; [exact Hx|]. destruct (leaf x) eqn:L; [reflexivity|exfalso].
    pose proof (born_internal_pos x Hx L). destruct (Z.leb_spec (born x) 0); [lia|discriminate].
  - intros [Hx L]. split; [exact Hx|]. rewrite (born_leaf x L). cbn.
    destruct (Z.eqb_spec x lo); [reflexivity|]. cbn. apply Z.leb_le. apply (go_ext_nonneg g G). lia.
Qed.

Lemma forest_end_in x : In x (forest Tend) <-> x = lo.
Proof.
  rewrite forest_in. unfold alive. split.
  - intros [Hx A]. apply andb_prop in A. destruct A as [_ A]. apply orb_prop in A.
    destruct A as [A|A]; [apply Z.eqb_eq in A; exact A|]. apply Z.leb_le in A.
    destruct (Z.eq_dec x lo); [assumption|]. pose proof (ext_lt_Tend x ltac:(lia)). lia.
  - intros ->. pose proof lohi. split; [lia|]. rewrite Z.eqb_refl. cbn.
    rewrite (proj2 (Z.leb_le _ _)); [reflexivity|]. unfold Tend; lia.
Qed.

Lemma rest_0 : rest 0 = lsum wt internals.
Proof.
  unfold rest, OverlayHuff2.internals. rewrite lsum_filter. apply lsum_ext.
  intros p Hp. apply allpos_in in Hp. destruct (leaf p) eqn:L; cbn; [reflexivity|].
  pose proof (born_internal_pos p Hp L). destruct (Z.ltb_spec 0 (born p)); [reflexivity|lia].
Qed.

Lemma rest_end : rest Tend = 0.
Proof.
  unfold rest. apply lsum_ind0. intros p Hp. apply allpos_in in Hp.
  pose proof (born_le_Tend p Hp). destruct (leaf p); cbn; [reflexivity|]. apply Z.ltb_ge. lia.
Qed.

Lemma alive_idle T x : 0 <= T -> (forall y, lo < y <= hi -> ext y <> T) -> lo <= x <= hi ->
  alive (T + 1) x = alive T x.
Proof.
  intros T0 NONE Hx. unfold alive.
  assert (born x <> T + 1).
  { intros E. destruct (leaf x) eqn:L; [rewrite born_leaf in E by assumption; lia|].
    destruct (go_two g G x Hx L) as (a & b & NEab & Ha & Hb & Pa & Pb & _).
    rewrite (born_int x a b Hx L Ha Hb NEab Pa Pb) in E.
    destruct (Z_le_gt_dec (ext a) (ext b)); [apply (NONE b Hb); lia | apply (NONE a Ha); lia]. }
  replace (born x <=? T + 1) with (born x <=? T)
    by (destruct (Z.leb_spec (born x) (T + 1)), (Z.leb_spec (born x) T); try reflexivity; lia).
  destruct (Z.eqb_spec x lo) as [->|NE]; [reflexivity|]. cbn.
  pose proof (NONE x ltac:(lia)).
  replace (T + 1 <=? ext x) with (T <=? ext x)
    by (destruct (Z.leb_spec (T + 1) (ext x)), (Z.leb_spec T (ext x)); try reflexivity; lia).
  reflexivity.
Qed.

Lemma forest_idle T : 0 <= T -> (forall x, lo < x <= hi -> ext x <> T) ->
  forall x, In x (forest (T + 1)) <-> In x (forest T).
Proof.
  intros T0 NONE x. rewrite !forest_in. split; intros [Hx A]; split; auto.
  - rewrite <- (alive_idle T x T0 NONE Hx). exact A.
  - rewrite (alive_idle T x T0 NONE Hx). exact A.
Qed.

Lemma rest_idle T : 0 <= T -> (forall x, lo < x <= hi -> ext x <> T) -> rest (T + 1) = rest T.
Proof.
  intros T0 NONE. unfold rest. apply lsum_ext. intros p Hp. apply allpos_in in Hp.
  destruct (leaf p) eqn:L; cbn; [reflexivity|].
  enough (born p <> T + 1) by (destruct (Z.ltb_spec (T + 1) (born p)), (Z.ltb_spec T (born p)); try reflexivity; lia).
  intros E. destruct (go_two g G p Hp L) as (a & b & NEab & Ha & Hb & Pa & Pb & _).
  rewrite (born_int p a b Hp L Ha Hb NEab Pa Pb) in E.
  destruct (Z_le_gt_dec (ext a) (ext b)); [apply (NONE b Hb); lia | apply (NONE a Ha); lia].
Qed.

Section Round.
Variable T : Z.
Variable a : Z.
Variable b : Z.
Hypothesis Ha : lo < a <= hi.
Hypothesis Hb : lo < b <= hi.
Hypothesis NEab : a <> b.
Hypothesis Pab : par b = par a.
Hypothesis Ea : ext a = T.
Hypothesis Eb : ext b = T + 1.
Hypothesis ONLY : forall c, lo < c <= hi -> par c = par a -> c = a \/ c = b.

Let p := par a.
Lemma p_range : lo <= p < a. Proof. unfold p. apply (go_par_lt g G). exact Ha. Qed.
Lemma p_int : leaf p = false. Proof. unfold p. apply (go_par_int g G). exact Ha. Qed.
Lemma born_p : born p = T + 2.
Proof. unfold p. pose proof p_range. rewrite (born_int (par a) a b ltac:(lia) p_int Ha Hb NEab eq_refl Pab). lia. Qed.
Lemma T0 : 0 <= T. Proof. rewrite <- Ea. apply (go_ext_nonneg g G). exact Ha. Qed.

Lemma ext_T_is_a x : lo < x <= hi -> ext x = T -> x = a.
Proof. intros Hx E. apply (go_ext_inj g G); auto. lia. Qed.
Lemma ext_T1_is_b x : lo < x <= hi -> ext x = T + 1 -> x = b.
Proof. intros Hx E. apply (go_ext_inj g G); auto. lia. Qed.

Lemma born_T1_none x : lo <= x <= hi -> born x <> T + 1.
Proof.
  intros Hx E. destruct (leaf x) eqn:L; [rewrite born_leaf in E by assumption; pose proof T0; lia|].
  destruct (go_two g G x Hx L) as (u & v & NE & Hu & Hv & Pu & Pv & _).
  rewrite (born_int x u v Hx L Hu Hv NE Pu Pv) in E.
  assert (ext u = T \/ ext v = T) by lia.
  assert (XP : x = p).
  { destruct H as [H|H]; [pose proof (ext_T_is_a u Hu H) as U; subst u | pose proof (ext_T_is_a v Hv H) as U; subst v]; unfold p; congruence. }
  rewrite <- (born_int x u v Hx L Hu Hv NE Pu Pv) in E. rewrite XP, born_p in E. lia.
Qed.

Lemma born_T2_only x : lo <= x <= hi -> born x = T + 2 -> x = p.
Proof.
  intros Hx E. destruct (leaf x) eqn:L; [rewrite born_leaf in E by assumption; pose proof T0; lia|].
  destruct (go_two g G x Hx L) as (u & v & NE & Hu & Hv & Pu & Pv & _).
  rewrite (born_int x u v Hx L Hu Hv NE Pu Pv) in E.
  assert (ext u = T + 1 \/ ext v = T + 1) by lia.
  destruct H as [H|H]; [pose proof (ext_T1_is_b u Hu H) as U; subst u | pose proof (ext_T1_is_b v Hv H) as U; subst v]; unfold p; congruence.
Qed.

Lemma a_in : In a (forest T).
Proof.
  apply forest_in. split; [lia|]. unfold alive. pose proof (born_le_ext a Ha).
  rewrite (proj2 (Z.leb_le _ _)) by lia. cbn. destruct (a =? lo); [reflexivity|]. cbn. apply Z.leb_le. lia.
Qed.
Lemma b_in : In b (forest T).
Proof.
  apply forest_in. split; [lia|]. unfold alive. pose proof (born_le_ext b Hb). pose proof (born_T1_none b ltac:(lia)).
  rewrite (proj2 (Z.leb_le _ _)) by lia. cbn. destruct (b =? lo); [reflexivity|]. cbn. apply Z.leb_le. lia.
Qed.
Lemma p_notin : ~ In p (forest T).
Proof. rewrite forest_in. unfold alive. rewrite born_p. intros [_ A]. destruct (Z.leb_spec (T + 2) T); [lia|discriminate]. Qed.
Lemma root_notin : ~ In lo (forest T).
Proof.
  rewrite forest_in. unfold alive. intros [_ A]. apply andb_prop in A. destruct A as [A _]. apply Z.leb_le in A.
  fold Tend in A. pose proof (ext_lt_Tend b Hb). lia.
Qed.

Lemma ab_lightest x : In x (forest T) -> x <> a -> x <> b -> wt a <= wt x /\ wt b <= wt x.
Proof.
  intros Ix Nxa Nxb. pose proof Ix as Ix'. apply forest_in in Ix. destruct Ix as [Hx A].
  assert (Nxl : x <> lo) by (intros ->; exact (root_notin Ix')).
  unfold alive in A. apply andb_prop in A. destruct A as [A1 A2]. apply orb_prop in A2.
  destruct A2 as [A2|A2]; [apply Z.eqb_eq in A2; congruence|]. apply Z.leb_le in A1. apply Z.leb_le in A2.
  assert (Hx' : lo < x <= hi) by lia.
  assert (EX : ext x <> T) by (intros E; apply Nxa; apply ext_T_is_a; auto).
  assert (EX1 : ext x <> T + 1) by (intros E; apply Nxb; apply ext_T1_is_b; auto).
  assert (ALIVE : forall t, t = ext a \/ t = ext b -> leaf x = true \/ exists c, lo < c <= hi /\ par c = x /\ ext c < t).
  { intros t Ht. destruct (leaf x) eqn:L; [left; reflexivity|right].
    destruct (go_two g G x Hx L) as (u & v & NE & Hu & Hv & Pu & Pv & _).
    rewrite (born_int x u v Hx L Hu Hv NE Pu Pv) in A1.
    exists u. split; [exact Hu|]. split; [exact Pu|]. lia. }
  split.
  - apply (go_greedy g G a x Ha Hx'); [lia|]. apply ALIVE. left; reflexivity.
  - apply (go_greedy g G b x Hb Hx'); [lia|]. apply ALIVE. right; reflexivity.
Qed.

Lemma forest_T2 x : In x (forest (T + 2)) <-> In x (p :: remove Z.eq_dec a (remove Z.eq_dec b (forest T))).
Proof.
  cbn. rewrite forest_in. split.
  - intros [Hx A]. unfold alive in A. apply andb_prop in A. destruct A as [A1 A2]. apply Z.leb_le in A1.
    destruct (Z.eq_dec p x) as [E|NE]; [left; exact E|right].
    assert (born x <= T).
    { pose proof (born_T1_none x Hx). destruct (Z.eq_dec (born x) (T + 2)); [exfalso; apply NE; symmetry; apply born_T2_only; auto|]. lia. }
    apply in_in_remove. { intros ->. apply orb_prop in A2. destruct A2 as [A2|A2]; [apply Z.eqb_eq in A2; lia|apply Z.leb_le in A2; lia]. }
    apply in_in_remove. { intros ->. apply orb_prop in A2. destruct A2 as [A2|A2]; [apply Z.eqb_eq in A2; lia|apply Z.leb_le in A2; lia]. }
    apply forest_in. split; [exact Hx|]. unfold alive. rewrite (proj2 (Z.leb_le _ _) H). cbn.
    apply orb_prop in A2. destruct A2 as [A2|A2]; [rewrite A2; reflexivity|]. apply Z.leb_le in A2.
    destruct (x =? lo); [reflexivity|]. cbn. apply Z.leb_le. lia.
  - intros [<-|I].
    + pose proof p_range. split; [lia|]. unfold alive. rewrite born_p, Z.leb_refl. cbn.
      destruct (Z.eqb_spec p lo) as [|NE]; [reflexivity|cbn]. apply Z.leb_le.
      pose proof (go_ext_par g G b Hb ltac:(rewrite Pab; fold p; lia)). rewrite Pab in H0. fold p in H0. lia.
    + apply in_remove in I. destruct I as [I Nxa]. apply in_remove in I. destruct I as [I Nxb].
      apply forest_in in I. destruct I as [Hx A]. split; [exact Hx|]. unfold alive in A |- *.
      apply andb_prop in A. destruct A as [A1 A2]. apply Z.leb_le in A1. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn.
      apply orb_prop in A2. destruct A2 as [A2|A2]; [rewrite A2; reflexivity|]. apply Z.leb_le in A2.
      destruct (Z.eqb_spec x lo); [reflexivity|cbn]. apply Z.leb_le.
      assert (ext x <> T) by (intros E; apply Nxa, ext_T_is_a; auto; lia).
      assert (ext x <> T + 1) by (intros E; apply Nxb, ext_T1_is_b; auto; lia). lia.
Qed.

Lemma rest_T2 : rest T = rest (T + 2) + wt p.
Proof.
  unfold rest. pose proof p_range.
  set (f2 := fun p0 : Z => if negb (leaf p0) && (T + 2 <? born p0) then wt p0 else 0).
  transitivity (lsum (fun q => if q =? p then wt p else f2 q) allpos).
  - apply lsum_ext. intros q Hq. apply allpos_in in Hq.
    destruct (Z.eqb_spec q p) as [->|NE].
    + rewrite p_int, born_p. cbn. destruct (Z.ltb_spec T (T + 2)); [reflexivity|lia].
    + unfold f2. destruct (leaf q); cbn; [reflexivity|].
      pose proof (born_T1_none q Hq).
      assert (born q <> T + 2) by (intros E; apply NE; apply born_T2_only; auto).
      destruct (Z.ltb_spec T (born q)), (Z.ltb_spec (T + 2) (born q)); try reflexivity; lia.
  - rewrite lsum_upd; [|apply allpos_nodup|apply allpos_in; lia].
    unfold f2 at 2. rewrite born_p. destruct (Z.ltb_spec (T + 2) (T + 2)); [lia|]. rewrite andb_false_r. lia.
Qed.
End Round.

Variable K : Z.
Hypothesis Kpos : 0 <= K.

Definition Q (T : Z) : Prop := forall sg, code_ok K sg (forest T) -> rest T <= csum wt sg (forest T).

Definition mid (T : Z) : Prop :=
  exists a b, lo < a <= hi /\ lo < b <= hi /\ a <> b /\ par b = par a /\ ext a = T - 1 /\ ext b = T.

Lemma Q_end : Q Tend.
Proof.
  intros sg [R KS]. rewrite rest_end.
  unfold csum. apply lsum_nonneg. intros x Ix. apply forest_end_in in Ix. subst x.
  pose proof (wt_nonneg lo ltac:(pose proof lohi; lia)). pose proof (R lo ltac:(apply forest_end_in; reflexivity)). nia.
Qed.

Lemma Q_transport T T' : (forall x, In x (forest T') <-> In x (forest T)) -> rest T' = rest T -> Q T' -> Q T.
Proof.
  intros SAME RE QT sg OK.
  assert (PERM : Permutation (forest T) (forest T')) by (apply NoDup_Permutation; [apply forest_nodup|apply forest_nodup|intros; symmetry; apply SAME]).
  rewrite <- RE. unfold csum. rewrite (lsum_perm _ _ _ PERM). apply QT.
  destruct OK as [R KS]. split; [intros x Ix; apply R; apply SAME; exact Ix|]. unfold ksum in *. rewrite <- (lsum_perm _ _ _ PERM). exact KS.
Qed.

Theorem Q_all : forall n T, 0 <= T <= Tend -> (Z.to_nat (Tend - T) <= n)%nat -> ~ mid T -> Q T.
Proof.
  induction n as [n IH] using lt_wf_ind. intros T HT Hn NM.
  destruct (Z.eq_dec T Tend) as [->|NE]; [apply Q_end|].
  pose proof lohi as LH.
  destruct (Z_lt_le_dec 0 (zsum (fun x => zind (ext x =? T)) (lo + 1) (Z.to_nat (hi - lo)))) as [SOME|NONE].
  - apply zsum_pos_has in SOME. destruct SOME as (a & Ha' & Ea & _). apply Z.eqb_eq in Ea.
    assert (Ha : lo < a <= hi) by lia.
    destruct (sibling a Ha) as (b & Hb & NEba & Pab & ONLY & SIB & W).
    destruct SIB as [SIB|SIB]; [exfalso; apply NM; exists b, a; repeat split; auto; lia|].
    assert (Eb : ext b = T + 1) by lia.
    assert (NEab : a <> b) by auto.
    assert (HT2 : T + 2 <= Tend) by (pose proof (ext_lt_Tend b Hb); lia).
    assert (Q2 : Q (T + 2)).
    { apply (IH (Z.to_nat (Tend - (T + 2)))); [lia|lia|lia|].
      intros (u & v & Hu & Hv & NEuv & Puv & Eu & Ev).
      assert (u = b) by (apply (go_ext_inj g G); auto; lia). subst u.
      destruct (ONLY v Hv ltac:(congruence)) as [-> | ->]; lia. }
    intros sg OK.
    pose proof (ab_lightest T a b Ha Hb NEab Ea Eb) as LIGHT.
    pose proof (p_notin T a b Ha Hb NEab Pab Ea Eb) as PN.
    destruct (exch K Kpos wt (forest T) a b (par a) sg (forest_nodup T)
                (a_in T a Ha Ea) (b_in T a b Ha Hb NEab Pab Ea Eb) NEab PN
                ltac:(intros x Ix; apply wt_nonneg; apply forest_in in Ix; tauto)
                LIGHT ltac:(lia) OK) as (sg' & OK' & C').
    rewrite (rest_T2 T a b Ha Hb NEab Pab Ea Eb).
    set (F2 := par a :: remove Z.eq_dec a (remove Z.eq_dec b (forest T))) in *.
    assert (ND2 : NoDup F2).
    { constructor; [|apply NoDup_remove_elt, NoDup_remove_elt, forest_nodup].
      intros I. apply in_remove in I. destruct I as [I _]. apply in_remove in I. destruct I as [I _]. exact (PN I). }
    assert (PERM : Permutation F2 (forest (T + 2))).
    { apply NoDup_Permutation; [exact ND2|apply forest_nodup|]. intros x. symmetry. apply (forest_T2 T a b Ha Hb NEab Pab Ea Eb). }
    assert (R2 : rest (T + 2) <= csum wt sg' F2).
    { unfold csum. rewrite (lsum_perm _ _ _ PERM). apply Q2.
      destruct OK' as [R' KS']. split; [intros x Ix; apply R'; eapply Permutation_in; [apply Permutation_sym; exact PERM|exact Ix]|].
      unfold ksum in *. rewrite <- (lsum_perm _ _ _ PERM). exact KS'. }
    lia.
  -
    assert (NONE' : forall x, lo < x <= hi -> ext x <> T).
    { intros x Hx E. pose proof (zsum_ind_ge1 (fun x => ext x =? T) (lo + 1) (Z.to_nat (hi - lo)) x ltac:(lia) ltac:(apply Z.eqb_eq; exact E)). lia. }
    apply (Q_transport T (T + 1)).
    + apply forest_idle; [lia|exact NONE'].
    + apply rest_idle; [lia|exact NONE'].
    + apply (IH (Z.to_nat (Tend - (T + 1)))); [lia|lia|lia|].
      intros (u & v & Hu & Hv & NEuv & Puv & Eu & Ev). apply (NONE' u Hu). lia.
Qed.

Theorem optimal : forall sg, code_ok K sg leaves ->
  lsum (fun i => wt i * depth i) leaves <= csum wt sg leaves.
Proof.
  intros sg OK. rewrite (cost_internal g G). rewrite <- rest_0.
  assert (PERM : Permutation leaves (forest 0)).
  { apply NoDup_Permutation; [apply leaves_nodup|apply forest_nodup|]. intros x. symmetry. apply forest_0_in. }
  unfold csum. rewrite (lsum_perm _ _ _ PERM).
  apply (Q_all (Z.to_nat Tend) 0); [pose proof Tend_pos; lia|lia| |].
  - intros (u & v & Hu & Hv & _ & _ & Eu & _). pose proof (go_ext_nonneg g G u Hu). lia.
  - destruct OK as [R KS]. split; [intros x Ix; apply R; eapply Permutation_in; [apply Permutation_sym; exact PERM|exact Ix]|].
    unfold ksum in *. rewrite <- (lsum_perm _ _ _ PERM). exact KS.
Qed.

End GTree.
