(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The block conjuncts of the post of sup_instance_verb's walk on image B, as one list lemma: blocks are (start, size)
   pairs; L0 .. L5 are the live blocks at the walk's points, O / O1 / O3 / O5 the recorder's blocks there. *)
From Stdlib Require Import ZArith List Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv.
Local Open Scope Z_scope.

Lemma sivb_blocks_post : forall (L0 L1 L2 L3 L5 O Fr O1 O3 O5 : list (Z * Z)) (p1 n1 p2 n2 pa q na old : Z),
  NoDup L0 ->
  (forall x, In x O -> In x L0) ->
  Permutation L0 (L1 ++ Fr) -> (forall x, In x Fr -> In x O) -> (forall x, In x O1 <-> In x O /\ ~ In x Fr) ->
  Permutation L2 ((p1, n1) :: L1) -> Forall (fun qk => iv_apart p1 n1 (fst qk) (snd qk)) L1 -> 0 < n1 ->
  Permutation L3 ((p2, n2) :: L2) -> Forall (fun qk => iv_apart p2 n2 (fst qk) (snd qk)) L2 -> 0 < n2 ->
  (forall x, In x O3 <-> In x O1 \/ x = (p1, n1) \/ x = (p2, n2)) ->
  (forall x y, In x L3 -> In y L3 -> fst x = fst y -> x = y) ->
  (old = 0 \/ exists x, In x O3 /\ fst x = old) -> (forall x, In x L0 -> 0 < fst x) ->
  (forall x, In x L3 -> fst x <> old -> x <> (pa, na) /\ x <> (q, na)) ->
  (forall x, In x L5 <-> (In x L3 /\ fst x <> old) \/ x = (pa, na) \/ x = (q, na)) ->
  (forall x, In x O5 <-> (In x O3 /\ fst x <> old) \/ x = (pa, na)) ->
  pa <> q ->
  (forall x y, In x L5 -> In y L5 -> fst x = fst y -> x = y) ->
  (forall x y, In x L5 -> In y L5 -> x <> y -> iv_apart (fst x) (snd x) (fst y) (snd y)) ->
  (forall x, In x O5 -> In x O \/ ~ In x L0) /\
  In (q, na) L5 /\
  (forall x, In x L0 -> ~ In x O -> x <> (q, na)) /\
  ~ In q (map fst O5) /\
  (forall x, In x L0 -> ~ In x O -> In x L5 /\ iv_apart (fst x) (snd x) q na) /\
  (forall x, In x L5 -> (In x L0 /\ ~ In x O) \/ In x O5 \/ x = (q, na)).
Proof.
  intros L0 L1 L2 L3 L5 O Fr O1 O3 O5 p1 n1 p2 n2 pa q na old
    Hnd0 HOL0 HP1 HFrO HO1 HP2 HA1 Hn1 HP3 HA2 Hn2 HO3 HU3 Hold Hpos Hnew HL5 HO5 Hpq HU5 HA5.
  assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  (* L1 and Fr split L0, which has no duplicates *)
  assert (Hdisj : forall x, In x L1 -> ~ In x Fr).
  { assert (Hnd : NoDup (L1 ++ Fr)) by exact (Permutation_NoDup HP1 Hnd0).
    clear - Hnd. revert Hnd. induction L1 as [|a l IH]; intros Hnd x Hx HF; [destruct Hx|].
    simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hnin Hnd'].
    destruct Hx as [<-|Hx].
    - apply Hnin, in_or_app. right. exact HF.
    - exact (IH Hnd' x Hx HF). }
  assert (H10 : forall x, In x L1 -> In x L0).
  { intros x Hx. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left. exact Hx. }
  assert (H01 : forall x, In x L0 -> In x L1 \/ In x Fr).
  { intros x Hx. apply in_app_or. exact (Permutation_in _ HP1 Hx). }
  assert (H12 : forall x, In x L1 -> In x L2).
  { intros x Hx. apply (Permutation_in _ (Permutation_sym HP2)). right. exact Hx. }
  assert (Hp1L2 : In (p1, n1) L2).
  { apply (Permutation_in _ (Permutation_sym HP2)). left. reflexivity. }
  assert (H21 : forall x, In x L2 -> x = (p1, n1) \/ In x L1).
  { intros x Hx. destruct (Permutation_in _ HP2 Hx) as [<-|Hx']; [left; reflexivity|right; exact Hx']. }
  assert (H23 : forall x, In x L2 -> In x L3).
  { intros x Hx. apply (Permutation_in _ (Permutation_sym HP3)). right. exact Hx. }
  assert (Hp2L3 : In (p2, n2) L3).
  { apply (Permutation_in _ (Permutation_sym HP3)). left. reflexivity. }
  assert (H32 : forall x, In x L3 -> x = (p2, n2) \/ In x L2).
  { intros x Hx. destruct (Permutation_in _ HP3 Hx) as [<-|Hx']; [left; reflexivity|right; exact Hx']. }
  (* the two new blocks are apart from every block before them, so neither is one of those *)
  assert (Hp1nL1 : ~ In (p1, n1) L1).
  { intro Hx. pose proof (proj1 (Forall_forall _ _) HA1 _ Hx) as Ha. unfold iv_apart in Ha. simpl in Ha. lia. }
  assert (Hp2nL2 : ~ In (p2, n2) L2).
  { intro Hx. pose proof (proj1 (Forall_forall _ _) HA2 _ Hx) as Ha. unfold iv_apart in Ha. simpl in Ha. lia. }
  assert (Hp2nL1 : ~ In (p2, n2) L1) by (intro Hx; exact (Hp2nL2 (H12 _ Hx))).
  assert (HO1L1 : forall x, In x O1 -> In x L1 /\ In x O).
  { intros x Hx. apply HO1 in Hx as [HxO HxF]. split; [|exact HxO].
    destruct (H01 x (HOL0 x HxO)) as [H|H]; [exact H|contradiction]. }
  assert (HO3L3 : forall x, In x O3 -> In x L3).
  { intros x Hx. apply HO3 in Hx as [Hx|[->| ->]].
    - apply H23, H12. exact (proj1 (HO1L1 x Hx)).
    - apply H23. exact Hp1L2.
    - exact Hp2L3. }
  assert (Hfree : forall x, In x L0 -> ~ In x O -> In x L1).
  { intros x Hx HxO. destruct (H01 x Hx) as [H|H]; [exact H|]. exfalso. apply HxO, HFrO, H. }
  (* a block of L0 the recorder does not own is still live at the third point, and its start is not old *)
  assert (K : forall x, In x L0 -> ~ In x O -> In x L3 /\ fst x <> old).
  { intros x Hx HxO. pose proof (Hfree x Hx HxO) as HxL1.
    split; [apply H23, H12, HxL1|].
    destruct Hold as [-> | [y [HyO3 Hyold]]].
    - pose proof (Hpos x Hx). lia.
    - intro Hxold. assert (Hxy : x = y).
      { apply HU3; [apply H23, H12, HxL1 | apply HO3L3, HyO3 | congruence]. }
      subst y. apply HO3 in HyO3 as [Hy|[Hy|Hy]].
      + apply HxO. exact (proj2 (HO1L1 x Hy)).
      + subst x. exact (Hp1nL1 HxL1).
      + subst x. exact (Hp2nL1 HxL1). }
  split; [|split; [|split; [|split; [|split]]]].
  - intros x Hx. apply HO5 in Hx as [[Hx3 Hxo]| ->].
    + apply HO3 in Hx3 as [Hx1|[->| ->]].
      * left. exact (proj2 (HO1L1 x Hx1)).
      * destruct (in_dec Hdec (p1, n1) O) as [H|H]; [left; exact H|right].
        intro HL0. exact (Hp1nL1 (Hfree _ HL0 H)).
      * destruct (in_dec Hdec (p2, n2) O) as [H|H]; [left; exact H|right].
        intro HL0. exact (Hp2nL1 (Hfree _ HL0 H)).
    + destruct (in_dec Hdec (pa, na) O) as [H|H]; [left; exact H|right].
      intro HL0. destruct (K _ HL0 H) as [H3 Ho]. exact (proj1 (Hnew _ H3 Ho) eq_refl).
  - apply HL5. right. right. reflexivity.
  - intros x Hx HxO. destruct (K x Hx HxO) as [H3 Ho]. exact (proj2 (Hnew x H3 Ho)).
  - intro Hq. apply in_map_iff in Hq as [y [Hyq Hy]].
    apply HO5 in Hy as [[Hy3 Hyo]| ->].
    + assert (Hyq' : y = (q, na)).
      { apply HU5.
        - apply HL5. left. split; [apply HO3L3, Hy3|exact Hyo].
        - apply HL5. right. right. reflexivity.
        - simpl. exact Hyq. }
      exact (proj2 (Hnew y (HO3L3 y Hy3) Hyo) Hyq').
    + apply Hpq. simpl in Hyq. exact Hyq.
  - intros x Hx HxO. destruct (K x Hx HxO) as [H3 Ho].
    assert (Hx5 : In x L5) by (apply HL5; left; split; assumption).
    split; [exact Hx5|].
    exact (HA5 x (q, na) Hx5 ltac:(apply HL5; right; right; reflexivity) (proj2 (Hnew x H3 Ho))).
  - intros x Hx. apply HL5 in Hx as [[Hx3 Hxo]|[->| ->]].
    + destruct (H32 x Hx3) as [->|Hx2].
      * right. left. apply HO5. left. split; [apply HO3; right; right; reflexivity|exact Hxo].
      * destruct (H21 x Hx2) as [->|Hx1].
        -- right. left. apply HO5. left. split; [apply HO3; right; left; reflexivity|exact Hxo].
        -- destruct (in_dec Hdec x O) as [HxO|HxO].
           ++ right. left. apply HO5. left. split; [|exact Hxo].
              apply HO3. left. apply HO1. split; [exact HxO|exact (Hdisj x Hx1)].
           ++ left. split; [exact (H10 x Hx1)|exact HxO].
    + right. left. apply HO5. right. reflexivity.
    + right. right. reflexivity.
Qed.
