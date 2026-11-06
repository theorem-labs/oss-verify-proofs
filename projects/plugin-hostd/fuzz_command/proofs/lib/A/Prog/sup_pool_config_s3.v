(* Modified by Theorem Labs, 2026-10: the block bookkeeping of sup_pool_config's ASan walk (plugin-hostd/fuzz_command): from
   the blocks at the entry, the ones record() freed, the two copies the call made and answer's post, the live-block and
   owned-block conjuncts of the post of lib/A/Prog/sup_pool_config_c.v:100-111. Pure list reasoning. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Local Open Scope Z_scope.

(* rs is the allocator's rounded size (req_size); SEP: two different live blocks do not overlap *)
Definition spc_sep (rs : Z -> Z) (bl : list (Z * Z)) : Prop :=
forall b m p n, In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) -> b + rs m <= p \/ p + rs n <= b.
Definition spc_pos (bl : list (Z * Z)) : Prop := forall b m, In (b, m) bl -> 0 < b /\ 0 <= m.

Lemma spc_fb_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros x y. decide equality; apply Z.eq_dec. Defined.

Lemma spc_fb_in_dec : forall (pn : Z * Z) l, {In pn l} + {~ In pn l}.
Proof. intros pn l. exact (in_dec spc_fb_pair_dec pn l). Defined.

(* two live blocks with the same start are the same block *)
Lemma spc_fb_same : forall (rs : Z -> Z) bl a k m, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) -> spc_sep rs bl -> spc_pos bl ->
In (a, k) bl -> In (a, m) bl -> (a, k) = (a, m).
Proof.
intros rs bl a k m Hrs S P Hk Hm. destruct (spc_fb_pair_dec (a, k) (a, m)) as [E|E]; [exact E|].
exfalso. destruct (P a k Hk) as [_ Pk]. destruct (P a m Hm) as [_ Pm].
destruct (Hrs k Pk). destruct (Hrs m Pm). destruct (S a k a m Hk Hm E); lia.
Qed.

(* two different live blocks do not overlap, by their requested sizes *)
Lemma spc_fb_apart : forall (rs : Z -> Z) bl b m p n, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) -> spc_sep rs bl -> spc_pos bl ->
In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) -> b + m <= p \/ p + n <= b.
Proof.
intros rs bl b m p n Hrs S P Hb Hp E. destruct (P b m Hb) as [_ Pm]. destruct (P p n Hp) as [_ Pn].
destruct (Hrs m Pm). destruct (Hrs n Pn). destruct (S b m p n Hb Hp E); lia.
Qed.

Lemma spc_final_blocks : forall (rs : Z -> Z) (bl0 blA bl' O F O0 O' : list (Z * Z)) (b1 b2 : Z * Z) (old p1 p2 n : Z),
(forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
(* the recorder's blocks at the entry are live; record() freed F, all of them the recorder's *)
(forall pn, In pn O -> In pn bl0) ->
(forall pn, In pn F -> In pn O) ->
(forall pn, In pn O0 <-> In pn O /\ ~ In pn F) ->
(* the blocks at answer's entry: the entry's less F, and the two copies b1 (xstrdup), b2 (arg_i), each fresh when made *)
(forall pn, In pn blA <-> (In pn bl0 /\ ~ In pn F) \/ pn = b1 \/ pn = b2) ->
~ (In b1 bl0 /\ ~ In b1 F) -> ~ (In b2 bl0 /\ ~ In b2 F) -> b2 <> b1 ->
spc_sep rs blA -> spc_pos blA ->
(* answer's post: the old answer old (0 or the start of one of the recorder's blocks O0 ++ [b1; b2]) freed, two copies
   (p1, n), (p2, n), none of them a block of blA other than the freed old answer *)
(old = 0 \/ exists m, In (old, m) (O0 ++ [b1; b2])) ->
(forall pn, In pn bl' <-> (In pn blA /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn blA -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn O' <-> (In pn (O0 ++ [b1; b2]) /\ fst pn <> old) \/ pn = (p1, n)) ->
spc_sep rs bl' -> spc_pos bl' ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In (p2, n) bl' /\
(forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
~ In p2 (map fst O') /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl' /\ (fst pn + snd pn <= p2 \/ p2 + n <= fst pn)) /\
(forall pn, In pn bl' -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)).
Proof.
intros rs bl0 blA bl' O F O0 O' b1 b2 old p1 p2 n Hrs HOb HFO HO0 HA Hb1 Hb2 Hb12 SA PA Hold HB' Hp12A Hp12 HO'
  SB PB.
assert (InA : forall pn, In pn bl0 -> ~ In pn F -> In pn blA)
  by (intros pn H1 H2; apply (proj2 (HA pn)); left; split; assumption).
assert (A1 : In b1 blA) by (apply (proj2 (HA b1)); right; left; reflexivity).
assert (A2 : In b2 blA) by (apply (proj2 (HA b2)); right; right; reflexivity).
assert (OA : forall pn, In pn (O0 ++ [b1; b2]) -> In pn blA).
{ intros pn H. apply in_app_or in H. destruct H as [H|[H|[H|[]]]].
  - apply (proj1 (HO0 pn)) in H. destruct H as [H1 H2]. apply InA; [exact (HOb _ H1) | exact H2].
  - subst pn. exact A1.
  - subst pn. exact A2. }
assert (NF : forall pn, ~ (In pn bl0 /\ ~ In pn F) -> In pn bl0 -> In pn F).
{ intros pn H H0. destruct (spc_fb_in_dec pn F) as [Hf|Hf]; [exact Hf | exfalso; apply H; split; assumption]. }
assert (Hn2 : In (p2, n) bl') by (apply (proj2 (HB' (p2, n))); right; right; reflexivity).
(* a block of blA with the old answer's start is one of the recorder's (O0 ++ [b1; b2]) *)
assert (OLDR : forall a k, In (a, k) blA -> a = old -> In (a, k) (O0 ++ [b1; b2])).
{ intros a k Hk Ea. subst a. destruct Hold as [Ho | (m & Hm)].
  - destruct (PA old k Hk) as [Pa _]. lia.
  - pose proof (spc_fb_same rs blA old k m Hrs SA PA Hk (OA _ Hm)) as Ek. rewrite Ek. exact Hm. }
(* a block live at the entry and kept by record() is not one of the recorder's blocks O0 ++ [b1; b2] unless in O *)
assert (KEPTR : forall pn, In pn bl0 -> ~ In pn O -> ~ In pn (O0 ++ [b1; b2])).
{ intros pn H0 HnO Hm. assert (HnF : ~ In pn F) by (intros Hf; exact (HnO (HFO _ Hf))).
  apply in_app_or in Hm. destruct Hm as [Hm|[Hm|[Hm|[]]]].
  - exact (HnO (proj1 (proj1 (HO0 _) Hm))).
  - apply Hb1. rewrite Hm. split; assumption.
  - apply Hb2. rewrite Hm. split; assumption. }
split.
{ intros pn Hpn. apply (proj1 (HO' pn)) in Hpn. destruct Hpn as [[Hpn _] | ->].
  - apply in_app_or in Hpn. destruct Hpn as [Hpn|[<-|[<-|[]]]].
    + left. exact (proj1 (proj1 (HO0 pn) Hpn)).
    + destruct (spc_fb_in_dec b1 bl0) as [Hi|Hi]; [left; exact (HFO _ (NF b1 Hb1 Hi)) | right; exact Hi].
    + destruct (spc_fb_in_dec b2 bl0) as [Hi|Hi]; [left; exact (HFO _ (NF b2 Hb2 Hi)) | right; exact Hi].
  - destruct (spc_fb_in_dec (p1, n) bl0) as [Hi|Hi]; [|right; exact Hi].
    destruct (spc_fb_in_dec (p1, n) F) as [Hf|Hf]; [left; exact (HFO _ Hf)|].
    pose proof (InA _ Hi Hf) as HiA.
    destruct (Z.eq_dec p1 old) as [Eo|Eo].
    + pose proof (OLDR p1 n HiA Eo) as Hr. destruct (spc_fb_in_dec (p1, n) O) as [HO|HO]; [left; exact HO|].
      exfalso. exact (KEPTR _ Hi HO Hr).
    + exfalso. exact (proj1 (Hp12A _ HiA Eo) eq_refl). }
split; [exact Hn2|].
split.
{ intros pn H0 HnO E. subst pn.
  assert (HnF : ~ In (p2, n) F) by (intros Hf; exact (HnO (HFO _ Hf))).
  pose proof (InA _ H0 HnF) as HiA.
  destruct (Z.eq_dec p2 old) as [Eo|Eo].
  - exact (KEPTR _ H0 HnO (OLDR p2 n HiA Eo)).
  - exact (proj2 (Hp12A _ HiA Eo) eq_refl). }
split.
{ intros Hm. apply in_map_iff in Hm. destruct Hm as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
  apply (proj1 (HO' (p2, k))) in Hk. destruct Hk as [[Hk Hne] | Hk].
  - assert (HkA : In (p2, k) blA) by exact (OA _ Hk).
    assert (HkB : In (p2, k) bl') by (apply (proj2 (HB' (p2, k))); left; split; [exact HkA | exact Hne]).
    pose proof (spc_fb_same rs bl' p2 k n Hrs SB PB HkB Hn2) as E. rewrite E in HkA.
    exact (proj2 (Hp12A _ HkA Hne) eq_refl).
  - injection Hk as E1 E2. exact (Hp12 (eq_sym E1)). }
split.
{ intros pn H0 HnO.
  assert (HnF : ~ In pn F) by (intros Hf; exact (HnO (HFO _ Hf))).
  assert (HpA : In pn blA) by exact (InA pn H0 HnF).
  assert (Hold' : fst pn <> old).
  { intros E. destruct pn as [a k]. cbn [fst] in E. exact (KEPTR _ H0 HnO (OLDR a k HpA E)). }
  assert (HpB : In pn bl') by (apply (proj2 (HB' pn)); left; split; assumption).
  split; [exact HpB|].
  destruct pn as [a k]. cbn [fst snd].
  apply (spc_fb_apart rs bl' a k p2 n Hrs SB PB HpB Hn2).
  exact (proj2 (Hp12A _ HpA Hold')). }
intros pn Hpn. apply (proj1 (HB' pn)) in Hpn. destruct Hpn as [[HpA Hne] | [-> | ->]].
- apply (proj1 (HA pn)) in HpA. destruct HpA as [[H0 HnF] | [-> | ->]].
  + destruct (spc_fb_in_dec pn O) as [Hi|Hi]; [right; left | left; split; assumption].
    apply (proj2 (HO' pn)). left. split; [|exact Hne]. apply in_or_app. left. apply (proj2 (HO0 pn)).
    split; assumption.
  + right; left. apply (proj2 (HO' b1)). left. split; [|exact Hne]. apply in_or_app. right. left. reflexivity.
  + right; left. apply (proj2 (HO' b2)). left. split; [|exact Hne]. apply in_or_app. right. right. left. reflexivity.
- right; left. apply (proj2 (HO' (p1, n))). right. reflexivity.
- right; right. reflexivity.
Qed.
