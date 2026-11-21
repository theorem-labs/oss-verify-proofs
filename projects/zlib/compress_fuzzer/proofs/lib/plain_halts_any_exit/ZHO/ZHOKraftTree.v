(** * ZHOKraftTree — a Kraft-valid length assignment is realizable as a
      cover whose weighted cost is at most the assignment's cost.

    OWNER: huffman-opt.  Bridge B of the cost-optimality architecture
    (STRATEGY-MEMO §3 L2): Théry's [cover_min] compares the built tree
    against COVERS; the adversary code [C] arrives as a Kraft-valid
    LENGTH function.  This file turns the latter into the former.

    METHOD (items induction, measure Sum (l_j + 1)):
    items are (btree, budget) pairs, budgets in [0,15], integer Kraft
    [Sum 2^(15-l_j) <= 2^15].  The potential
       Phi(items) = Sum_j (weight_tree f T_j + sum_leaves f T_j * l_j)
    never increases:
      - Kraft < 2^15  => bump the max-budget item L -> L-1 (all terms are
        multiples of 2^(15-L) and the sum is k*2^(15-L) with k < 2^L, so
        k+1 <= 2^L keeps Kraft <= 2^15); Phi strictly helps (l decreases).
      - Kraft = 2^15  => at least TWO items sit at the max budget L
        (mod-2^(16-L) parity: the count of max-budget terms is even), and
        L >= 1 when there are >= 2 items; merge them: the merged item
        (node a b, L-1) preserves Kraft exactly and preserves Phi exactly
        (weight_tree(node a b) + sl*(L-1) = sum of the two old terms).
    Exit: a single item (T, l) with weight_tree f T <= Phi <= Phi(entry)
    = Sum_s f(s) * C(s); every merge is a [cover_node] step, so
    [cover (map fst items0) T].

    TRUST BOUNDARY: pure Gallina over the vendored Huffman library
    (coq-community/huffman, LGPL-2.1-or-later) + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Import BTree WeightTree Cover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Section ZHOKraftTree.

Variable f : Z -> nat.

(** ** Items: (tree, budget) pairs *)

Definition kraftI (items : list (btree Z * Z)) : Z :=
  fold_right (fun tl acc => acc + 2 ^ (15 - snd tl)) 0 items.
Definition phiI (items : list (btree Z * Z)) : nat :=
  fold_right (fun tl acc =>
    (acc + (weight_tree f (fst tl)
            + sum_leaves f (fst tl) * Z.to_nat (snd tl)))%nat) 0%nat items.
Definition measureI (items : list (btree Z * Z)) : nat :=
  fold_right (fun tl acc => (acc + Z.to_nat (snd tl) + 1)%nat) 0%nat items.
Definition maxB (items : list (btree Z * Z)) : Z :=
  fold_right (fun tl m => Z.max (snd tl) m) 0 items.

Lemma kraftI_cons : forall x l, kraftI (x :: l) = kraftI l + 2 ^ (15 - snd x).
Proof. reflexivity. Qed.
Lemma phiI_cons : forall x l,
  phiI (x :: l)
  = (phiI l + (weight_tree f (fst x)
               + sum_leaves f (fst x) * Z.to_nat (snd x)))%nat.
Proof. reflexivity. Qed.
Lemma measureI_cons : forall x l,
  measureI (x :: l) = (measureI l + Z.to_nat (snd x) + 1)%nat.
Proof. reflexivity. Qed.
Lemma maxB_cons : forall x l, maxB (x :: l) = Z.max (snd x) (maxB l).
Proof. reflexivity. Qed.

Lemma kraftI_perm : forall l1 l2, Permutation l1 l2 -> kraftI l1 = kraftI l2.
Proof. induction 1; rewrite ?kraftI_cons; lia. Qed.
Lemma phiI_perm : forall l1 l2, Permutation l1 l2 -> phiI l1 = phiI l2.
Proof. induction 1; rewrite ?phiI_cons; lia. Qed.
Lemma measureI_perm : forall l1 l2,
  Permutation l1 l2 -> measureI l1 = measureI l2.
Proof. induction 1; rewrite ?measureI_cons; lia. Qed.

Lemma kraftI_nonneg : forall items, 0 <= kraftI items.
Proof.
  induction items as [|x l IH]; [cbn; lia|].
  rewrite kraftI_cons.
  pose proof (Z.pow_nonneg 2 (15 - snd x) ltac:(lia)). lia.
Qed.

Lemma maxB_nonneg : forall items, 0 <= maxB items.
Proof.
  induction items as [|x l IH]; [cbn; lia|]. rewrite maxB_cons. lia.
Qed.

Lemma maxB_ub : forall items tl, In tl items -> snd tl <= maxB items.
Proof.
  induction items as [|x l IH]; intros tl Hin; [destruct Hin|].
  rewrite maxB_cons. destruct Hin as [->|Hin]; [lia|].
  pose proof (IH tl Hin). lia.
Qed.

(** pick an item attaining the max, as a permutation split *)
Lemma maxB_pick : forall items,
  items <> [] -> (forall tl, In tl items -> 0 <= snd tl) ->
  exists tl rest, Permutation items (tl :: rest) /\ snd tl = maxB items.
Proof.
  induction items as [|x l IH]; intros Hne Hb; [congruence|].
  destruct l as [|y l'].
  - exists x, []. split; [apply Permutation_refl|].
    rewrite maxB_cons. cbn [maxB fold_right].
    pose proof (Hb x (or_introl eq_refl)). lia.
  - destruct (IH ltac:(congruence)
                (fun tl Hin => Hb tl (or_intror Hin)))
      as (tl & rest & Hp & Hs).
    destruct (Z.le_gt_cases (maxB (y :: l')) (snd x)) as [Hle|Hgt].
    + exists x, (y :: l'). split; [apply Permutation_refl|].
      rewrite maxB_cons. lia.
    + exists tl, (x :: rest). split.
      * eapply Permutation_trans; [apply perm_skip; exact Hp|].
        apply perm_swap.
      * rewrite maxB_cons. lia.
Qed.

(** pick an item at budget [L], or none has it *)
Lemma pick_at : forall (L : Z) (l : list (btree Z * Z)),
  (exists tl rest, Permutation l (tl :: rest) /\ snd tl = L)
  \/ (forall tl, In tl l -> snd tl <> L).
Proof.
  intros L. induction l as [|x l' IH].
  - right. intros tl [].
  - destruct (Z.eqb_spec (snd x) L) as [He|Hne].
    + left. exists x, l'. split; [apply Permutation_refl | exact He].
    + destruct IH as [(tl & rest & Hp & Hs)|Hnone].
      * left. exists tl, (x :: rest). split; [|exact Hs].
        eapply Permutation_trans; [apply perm_skip; exact Hp|].
        apply perm_swap.
      * right. intros tl [->|Hin]; [exact Hne | exact (Hnone tl Hin)].
Qed.

Lemma pow2_div : forall a b, 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof.
  intros a b Hab. exists (2 ^ (b - a)).
  rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma kraftI_div : forall d items,
  (forall tl, In tl items -> (2 ^ d | 2 ^ (15 - snd tl))) ->
  (2 ^ d | kraftI items).
Proof.
  intros d. induction items as [|x l IH]; intros Hall.
  - cbn. apply Z.divide_0_r.
  - rewrite kraftI_cons. apply Z.divide_add_r.
    + apply IH. intros tl Hin. apply Hall. right. exact Hin.
    + apply Hall. left. reflexivity.
Qed.

(** ** The main items induction *)

Lemma items_main : forall n items,
  (measureI items <= n)%nat -> items <> [] ->
  (forall tl, In tl items -> 0 <= snd tl <= 15) ->
  kraftI items <= 2 ^ 15 ->
  exists T, cover (map fst items) T /\ (weight_tree f T <= phiI items)%nat.
Proof.
  induction n as [|n IHn]; intros items Hm Hne Hb Hk.
  - exfalso. destruct items as [|x l]; [congruence|].
    rewrite measureI_cons in Hm. lia.
  - destruct items as [|x l]; [congruence|].
    destruct l as [|y rest0].
    + (* singleton *)
      exists (fst x). split; [cbn; apply cover_one|].
      rewrite phiI_cons. lia.
    + (* >= 2 items *)
      set (items := x :: y :: rest0) in *.
      set (L := maxB items).
      assert (HL15 : L <= 15).
      { destruct (maxB_pick items ltac:(unfold items; congruence)
                    (fun tl Hin => proj1 (Hb tl Hin)))
          as (tl & r & Hp & Hs).
        assert (Hin : In tl items).
        { eapply Permutation_in; [apply Permutation_sym; exact Hp|].
          left. reflexivity. }
        pose proof (Hb tl Hin). unfold L. lia. }
      assert (HL1 : 1 <= L).
      { destruct (Z.le_gt_cases 1 L) as [|HL0]; [assumption|].
        exfalso.
        pose proof (maxB_nonneg items) as Hnn.
        assert (HxL : snd x = 0).
        { pose proof (maxB_ub items x (or_introl eq_refl)).
          pose proof (proj1 (Hb x (or_introl eq_refl))). unfold L in *. lia. }
        assert (HyL : snd y = 0).
        { pose proof (maxB_ub items y (or_intror (or_introl eq_refl))).
          pose proof (proj1 (Hb y (or_intror (or_introl eq_refl)))).
          unfold L in *. lia. }
        unfold items in Hk. rewrite !kraftI_cons, HxL, HyL in Hk.
        replace (15 - 0) with 15 in Hk by lia.
        pose proof (kraftI_nonneg rest0). lia. }
      assert (Hpos : 0 < 2 ^ (15 - L))
        by (apply Z.pow_pos_nonneg; lia).
      assert (Hsplit : 2 ^ 15 = 2 ^ L * 2 ^ (15 - L))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hdiv : (2 ^ (15 - L) | kraftI items)).
      { apply kraftI_div. intros tl Hin.
        apply pow2_div.
        pose proof (maxB_ub items tl Hin). pose proof (Hb tl Hin).
        unfold L in *. lia. }
      destruct (maxB_pick items ltac:(unfold items; congruence)
                  (fun tl Hin => proj1 (Hb tl Hin)))
        as (tlA & restA & HpA & HsA).
      fold L in HsA.
      assert (HbA : forall tl, In tl (tlA :: restA) -> 0 <= snd tl <= 15).
      { intros tl Hin. apply Hb.
        eapply Permutation_in; [apply Permutation_sym; exact HpA | exact Hin]. }
      assert (HL16 : 2 ^ (16 - L) = 2 * 2 ^ (15 - L)).
      { replace (16 - L) with (1 + (15 - L)) by lia.
        rewrite Z.pow_add_r by lia. lia. }
      destruct (proj1 (Z.le_lteq (kraftI items) (2 ^ 15)) Hk) as [Hlt|Heq].
      * (* BUMP: replace tlA's budget by L-1 *)
        destruct Hdiv as [k Hk2].
        assert (Hknn : 0 <= k).
        { pose proof (kraftI_nonneg items). nia. }
        assert (HkL : k < 2 ^ L) by nia.
        set (newit := (fst tlA, L - 1) :: restA).
        assert (Hknew : kraftI newit <= 2 ^ 15).
        { unfold newit. rewrite kraftI_cons. cbn [snd].
          replace (15 - (L - 1)) with (16 - L) by lia.
          rewrite HL16.
          assert (EkA : kraftI items = kraftI restA + 2 ^ (15 - L)).
          { rewrite (kraftI_perm items (tlA :: restA) HpA).
            rewrite kraftI_cons, HsA. reflexivity. }
          nia. }
        assert (Hmnew : (measureI newit <= n)%nat).
        { unfold newit.
          rewrite (measureI_perm items (tlA :: restA) HpA) in Hm.
          rewrite measureI_cons in Hm. rewrite measureI_cons. cbn [snd].
          lia. }
        assert (Hbnew : forall tl, In tl newit -> 0 <= snd tl <= 15).
        { intros tl [<-|Hin]; cbn [snd]; [lia|].
          apply HbA. right. exact Hin. }
        destruct (IHn newit Hmnew ltac:(unfold newit; congruence) Hbnew Hknew)
          as (T & Hcov & Hwt).
        exists T. split.
        -- eapply cover_permutation; [exact Hcov|].
           unfold newit. cbn [map fst].
           change (fst tlA :: map fst restA) with (map fst (tlA :: restA)).
           apply Permutation_map. apply Permutation_sym. exact HpA.
        -- rewrite (phiI_perm items (tlA :: restA) HpA).
           rewrite phiI_cons. unfold newit in Hwt.
           rewrite phiI_cons in Hwt. cbn [fst snd] in Hwt.
           assert (Hz : (Z.to_nat (L - 1) <= Z.to_nat L)%nat) by lia.
           pose proof (Nat.mul_le_mono_l _ _ (sum_leaves f (fst tlA)) Hz).
           rewrite HsA. lia.
      * (* MERGE: two items at the max budget *)
        destruct (pick_at L restA) as [(tlB & rest' & HpB & HsB)|Hnone].
        2:{ (* no second max: parity contradiction *)
          exfalso.
          assert (HdivR : (2 ^ (16 - L) | kraftI restA)).
          { apply kraftI_div. intros tl Hin.
            apply pow2_div.
            assert (Hin' : In tl items).
            { eapply Permutation_in; [apply Permutation_sym; exact HpA|].
              right. exact Hin. }
            pose proof (maxB_ub items tl Hin').
            pose proof (Hnone tl Hin). pose proof (Hb tl Hin').
            unfold L in *. lia. }
          destruct HdivR as [m Hm2].
          assert (EkA : kraftI items = kraftI restA + 2 ^ (15 - L)).
          { rewrite (kraftI_perm items (tlA :: restA) HpA).
            rewrite kraftI_cons, HsA. reflexivity. }
          (* 2^15 = m*2^(16-L) + 2^(15-L)  =>  2^L = 2m + 1: even = odd *)
          rewrite EkA, Hm2, HL16 in Heq.
          assert (H2L : 2 ^ L = 2 * m + 1) by nia.
          assert (Heven : (2 | 2 ^ L)).
          { apply pow2_div with (a := 1) (b := L); lia. }
          destruct Heven as [q Hq]. lia. }
        assert (Hp2 : Permutation items (tlA :: tlB :: rest')).
        { eapply Permutation_trans; [exact HpA|].
          apply perm_skip. exact HpB. }
        set (newit := (node (fst tlA) (fst tlB), L - 1) :: rest').
        assert (HbB : In tlB items).
        { eapply Permutation_in; [apply Permutation_sym; exact Hp2|].
          right. left. reflexivity. }
        assert (EkA2 : kraftI items
                       = kraftI rest' + 2 ^ (15 - L) + 2 ^ (15 - L)).
        { rewrite (kraftI_perm items (tlA :: tlB :: rest') Hp2).
          rewrite !kraftI_cons, HsA, HsB. lia. }
        assert (Hknew : kraftI newit <= 2 ^ 15).
        { unfold newit. rewrite kraftI_cons. cbn [snd].
          replace (15 - (L - 1)) with (16 - L) by lia.
          rewrite HL16. lia. }
        assert (Hmnew : (measureI newit <= n)%nat).
        { unfold newit.
          rewrite (measureI_perm items (tlA :: tlB :: rest') Hp2) in Hm.
          rewrite !measureI_cons in Hm. rewrite measureI_cons. cbn [snd].
          lia. }
        assert (Hbnew : forall tl, In tl newit -> 0 <= snd tl <= 15).
        { intros tl [<-|Hin]; cbn [snd]; [lia|].
          apply Hb.
          eapply Permutation_in; [apply Permutation_sym; exact Hp2|].
          right. right. exact Hin. }
        destruct (IHn newit Hmnew ltac:(unfold newit; congruence) Hbnew Hknew)
          as (T & Hcov & Hwt).
        exists T. split.
        -- eapply cover_node with (t1 := fst tlA) (t2 := fst tlB)
             (l2 := map fst rest').
           ++ change (fst tlA :: fst tlB :: map fst rest')
                with (map fst (tlA :: tlB :: rest')).
              apply Permutation_map. exact Hp2.
           ++ exact Hcov.
        -- rewrite (phiI_perm items (tlA :: tlB :: rest') Hp2).
           rewrite !phiI_cons. unfold newit in Hwt.
           rewrite phiI_cons in Hwt. cbn [fst snd] in Hwt.
           cbn [weight_tree sum_leaves] in Hwt.
           assert (HzL : Z.to_nat L = S (Z.to_nat (L - 1))) by lia.
           rewrite HsA, HsB, HzL.
           rewrite !Nat.mul_succ_r in *. lia.
Qed.

(** ** Instantiation plumbing *)

Lemma mapfst_map : forall (C : Z -> Z) syms,
  map fst (map (fun s => (leaf s, C s)) syms) = map (@leaf Z) syms.
Proof. induction syms as [|a l IH]; cbn; congruence. Qed.

Lemma kraftI_map : forall (C : Z -> Z) syms,
  kraftI (map (fun s => (leaf s, C s)) syms)
  = fold_right (fun s acc => acc + 2 ^ (15 - C s)) 0 syms.
Proof.
  induction syms as [|a l IH]; [reflexivity|].
  cbn [map]. rewrite kraftI_cons, IH. reflexivity.
Qed.

Lemma phiI_map : forall (C : Z -> Z) syms,
  phiI (map (fun s => (leaf s, C s)) syms)
  = fold_right (fun s acc => (acc + f s * Z.to_nat (C s))%nat) 0%nat syms.
Proof.
  induction syms as [|a l IH]; [reflexivity|].
  cbn [map]. rewrite phiI_cons, IH.
  cbn [fst snd weight_tree sum_leaves fold_right].
  lia.
Qed.

Lemma measureI_map_ne : forall (C : Z -> Z) syms,
  syms <> [] -> map (fun s => (leaf s, C s)) syms <> [].
Proof. intros C [|a l]; cbn; congruence. Qed.

(** the exported seam (consumed by ZHOMain):
    [syms] may contain duplicates; no [NoDup] is required. *)
Theorem kraft_cover_bound : forall (syms : list Z) (C : Z -> Z),
  syms <> [] ->
  (forall s, In s syms -> 1 <= C s <= 15) ->
  fold_right (fun s acc => acc + 2 ^ (15 - C s)) 0 syms <= 2 ^ 15 ->
  exists T : btree Z,
    cover (map (@leaf Z) syms) T
    /\ (weight_tree f T
        <= fold_right (fun s acc => acc + f s * Z.to_nat (C s)) 0%nat syms)%nat.
Proof.
  intros syms C Hne Hr Hk.
  set (items := map (fun s => (leaf s, C s)) syms).
  assert (Hb : forall tl, In tl items -> 0 <= snd tl <= 15).
  { intros tl Hin. unfold items in Hin.
    apply in_map_iff in Hin. destruct Hin as (s & <- & Hs).
    cbn [snd]. pose proof (Hr s Hs). lia. }
  destruct (items_main (measureI items) items (Nat.le_refl _)
              (measureI_map_ne C syms Hne) Hb
              ltac:(unfold items; rewrite kraftI_map; exact Hk))
    as (T & Hcov & Hwt).
  exists T. split.
  - rewrite <- (mapfst_map C syms). exact Hcov.
  - rewrite <- (phiI_map C syms). exact Hwt.
Qed.

End ZHOKraftTree.
