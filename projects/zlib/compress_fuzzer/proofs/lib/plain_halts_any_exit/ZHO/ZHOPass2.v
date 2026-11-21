(** * ZHOPass2 — pass 2 assigns the adjusted histogram MONOTONICALLY in
      window position.  L4 piece (P2).

    OWNER: huffman-opt.  BtPass2 (landed) proves the exit HISTOGRAM is
    exactly [blc2]; the L4 assembly additionally needs the ORDER: pass 2
    walks positions descending while [bits] only decreases, so among LEAF
    positions, ascending position means ascending final length.  Combined
    with ZHOFib's FIB-B (ascending position = descending freq), the leaf
    (freq, len) pairs in position order are exactly a monotone pairing,
    which ZHOLayer's rearrangement/layer lemmas consume.

    Proof: BtPass2's own walk (Pass2Inv, pass2_step_skip/take/group,
    pass2_walk, pass2_exit — crib them; this bed file re-runs the walk
    with the invariant extended by the pairwise clause on the processed
    region).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus3 BtCensus4 BtPass1 BtPass2.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Section ZHOPass2.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hmf0 : 0 <= hmaxf.
Variables (t2 : Tree) (blc2 : zarr).
Hypothesis Hrng2 : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
                   1 <= t_len t2 (hp3 p) <= M.
Hypothesis Hnn2 : forall b, 0 <= blc2 b.
Hypothesis Htot :
  BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
  = BtPass2.bsumr blc2 (Z.to_nat M) 1.

(** ** Local helpers *)

Lemma zp2_setlen_other : forall t m v x,
  x <> m -> t_len (t_setlen t m v) x = t_len t x.
Proof.
  intros t m v x H. unfold t_len, t_setlen. cbn [tr_dl].
  apply zset_other. exact H.
Qed.

Lemma zp2_bsumr_S : forall k b,
  BtPass2.bsumr blc2 (S k) b = blc2 b + BtPass2.bsumr blc2 k (b + 1).
Proof. reflexivity. Qed.

Lemma zp2_ind_member : forall (f : Z -> bool) lo n p,
  lo <= p < lo + Z.of_nat n -> f p = true ->
  1 <= wsum (fun i => ind (f i)) lo n.
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intros lo p Hp Hf.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp. cbn [wsum]. cbv beta.
    assert (Hnn : 0 <= wsum (fun i => ind (f i)) (lo + 1) k).
    { apply wsum_nonneg. intros i _. destruct (f i); cbn [ind]; lia. }
    destruct (Z.eq_dec p lo) as [->|Hne].
    + rewrite Hf. cbn [ind]. lia.
    + pose proof (IH (lo + 1) p ltac:(lia) Hf).
      destruct (f lo); cbn [ind]; lia.
Qed.

(** the ORDER clause carried through the walk *)
Definition zp2_mono (h : Z) (t : Tree) : Prop :=
  forall p q, h <= p -> p <= q -> q < HEAP_SIZE ->
    hp3 p <= maxc1 -> hp3 q <= maxc1 ->
    t_len t (hp3 p) <= t_len t (hp3 q).

Lemma zp2_mono_entry : zp2_mono HEAP_SIZE t2.
Proof. intros p q Hp Hpq Hq _ _. lia. Qed.

Lemma zp2_mono_skip : forall h t,
  maxc1 < hp3 (h - 1) -> zp2_mono h t -> zp2_mono (h - 1) t.
Proof.
  intros h t Hm Hmono p q Hp Hpq Hq Hlp Hlq.
  destruct (Z.eq_dec p (h - 1)) as [->|Hne]; [lia|].
  apply Hmono; try lia; assumption.
Qed.

Lemma zp2_mono_take : forall bits n h t t',
  BtPass2.Pass2Inv maxc1 M hp3 hmaxf t2 blc2 bits n h t ->
  1 <= n ->
  hp3 (h - 1) <= maxc1 ->
  hmaxf + 2 <= h ->
  ((t' = t /\ t_len t (hp3 (h - 1)) = bits)
   \/ t' = t_setlen t (hp3 (h - 1)) bits) ->
  zp2_mono h t -> zp2_mono (h - 1) t'.
Proof.
  intros bits n h t t' Hinv Hn Hm Hh2 Hcase Hmono.
  pose proof (BtPass2.q2_bits _ _ _ _ _ _ _ _ _ _ Hinv) as Hb.
  pose proof (BtPass2.q2_h _ _ _ _ _ _ _ _ _ _ Hinv) as Hhr.
  set (m := hp3 (h - 1)) in *.
  assert (Hlen' : t_len t' m = bits).
  { destruct Hcase as [[-> Hd]| ->]; [exact Hd|].
    unfold t_len, t_setlen. cbn [tr_dl]. rewrite zset_same.
    unfold u16. apply Z.mod_small. unfold MAX_BL_BITS, MAX_BITS in *. lia. }
  assert (Hoth : forall p, hmaxf <= p < HEAP_SIZE -> p <> h - 1 ->
                 t_len t' (hp3 p) = t_len t (hp3 p)).
  { intros p Hp Hne.
    destruct Hcase as [[-> _]| ->]; [reflexivity|].
    apply zp2_setlen_other.
    apply (BtPass1.pk_distinct _ _ _ _ _ _ _ Hpk); [lia | lia | exact Hne]. }
  intros p q Hp Hpq Hq Hlp Hlq.
  destruct (Z.eq_dec p (h - 1)) as [->|Hnep].
  - destruct (Z.eq_dec q (h - 1)) as [->|Hneq].
    + lia.
    + rewrite (Hoth q ltac:(lia) Hneq).
      fold m. rewrite Hlen'.
      assert (Hqr : h <= q < HEAP_SIZE) by lia.
      pose proof (BtPass2.q2_rng _ _ _ _ _ _ _ _ _ _ Hinv q Hqr Hlq) as Hr.
      lia.
  - assert (Hpge : h <= p) by lia.
    assert (Hqne : q <> h - 1) by lia.
    rewrite (Hoth p ltac:(lia) Hnep), (Hoth q ltac:(lia) Hqne).
    apply Hmono; try lia; assumption.
Qed.

(** the joint walk: landed invariant + the order clause *)
Lemma zp2_walk : forall fuel bits n h t ol,
  (h - hmaxf) + bits + 1 <= Z.of_nat fuel ->
  BtPass2.Pass2Inv maxc1 M hp3 hmaxf t2 blc2 bits n h t ->
  zp2_mono h t ->
  match gb_pass2 fuel hp3 maxc1 t blc2 bits n h ol with
  | (t3, _) => exists h',
      BtPass2.Pass2Inv maxc1 M hp3 hmaxf t2 blc2 1 0 h' t3
      /\ zp2_mono h' t3
  end.
Proof.
  induction fuel as [|f IH]; intros bits n h t ol Hf Hinv Hmono.
  - pose proof (BtPass2.q2_h _ _ _ _ _ _ _ _ _ _ Hinv).
    pose proof (BtPass2.q2_bits _ _ _ _ _ _ _ _ _ _ Hinv).
    cbn [Z.of_nat] in Hf. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    pose proof (BtPass2.q2_h _ _ _ _ _ _ _ _ _ _ Hinv) as Hhr.
    pose proof (BtPass2.q2_bits _ _ _ _ _ _ _ _ _ _ Hinv) as Hbr.
    pose proof (BtPass2.q2_n _ _ _ _ _ _ _ _ _ _ Hinv) as Hnr.
    cbn [gb_pass2].
    destruct (Z.eqb n 0) eqn:En.
    + apply Z.eqb_eq in En. subst n.
      destruct (Z.leb bits 1) eqn:Eb.
      * apply Z.leb_le in Eb.
        exists h. split; [|exact Hmono].
        assert (E1 : bits = 1) by lia. subst bits. exact Hinv.
      * apply Z.leb_gt in Eb.
        apply IH; [lia| |exact Hmono].
        apply (BtPass2.pass2_step_group _ _ _ _ _ _ Hnn2 _ _ _ Hinv
                 ltac:(lia)).
    + apply Z.eqb_neq in En.
      assert (Hn1 : 1 <= n) by lia.
      pose proof (BtPass2.pass2_leaf_below _ _ _ _ _ _ _ _ Hpk _ _ Hnn2 Htot
                    _ _ _ _ Hinv Hn1) as Hh2.
      destruct (Z.ltb maxc1 (hp3 (h - 1))) eqn:Em.
      * apply Z.ltb_lt in Em.
        apply IH; [lia| |].
        -- apply (BtPass2.pass2_step_skip _ _ _ _ _ _ _ _ Hpk _ _ Hnn2 Htot
                    _ _ _ _ Hinv Hn1 Em).
        -- apply zp2_mono_skip; assumption.
      * apply Z.ltb_ge in Em.
        destruct (Z.eqb (t_len t (hp3 (h - 1))) bits) eqn:El.
        -- apply Z.eqb_eq in El.
           apply IH; [lia| |].
           ++ apply (BtPass2.pass2_step_take _ _ _ _ _ _ _ _ Hpk HM _ _
                       _ _ _ _ _ Hinv Hn1 Em (or_introl (conj eq_refl El))).
           ++ apply (zp2_mono_take bits n h t t Hinv Hn1 Em Hh2
                       (or_introl (conj eq_refl El)) Hmono).
        -- apply IH; [lia| |].
           ++ apply (BtPass2.pass2_step_take _ _ _ _ _ _ _ _ Hpk HM _ _
                       _ _ _ _ _ Hinv Hn1 Em (or_intror eq_refl)).
           ++ apply (zp2_mono_take bits n h t
                       (t_setlen t (hp3 (h - 1)) bits) Hinv Hn1 Em Hh2
                       (or_intror eq_refl) Hmono).
Qed.

Theorem zho_pass2_order : forall ol t3 ol2,
  gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
           hp3 maxc1 t2 blc2 M (blc2 M) HEAP_SIZE ol = (t3, ol2) ->
  (* the exit histogram is blc2 (BtPass2's fact, re-exported) *)
  (forall b, 1 <= b <= M ->
     BtPass2.hist maxc1 hp3 t3 b (hmaxf + 1)
       (Z.to_nat (HEAP_SIZE - (hmaxf + 1))) = blc2 b)
  (* the ORDER: among leaf positions, ascending position = ascending len *)
  /\ (forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
        hp3 p <= maxc1 -> hp3 q <= maxc1 ->
        t_len t3 (hp3 p) <= t_len t3 (hp3 q))
  (* leaf range *)
  /\ (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
        1 <= t_len t3 (hp3 p) <= M)
  (* internals and outside-window slots keep their pass-1 lens *)
  /\ (forall p, hmaxf <= p < HEAP_SIZE -> maxc1 < hp3 p ->
        t_len t3 (hp3 p) = t_len t2 (hp3 p))
  /\ (forall y, pcount hp3 hmaxf y = 0 -> tr_dl t3 y = tr_dl t2 y).
Proof.
  intros ol t3 ol2 Egp.
  assert (Hfu : (HEAP_SIZE - hmaxf) + M + 1
                <= Z.of_nat (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)).
  { rewrite !Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id
      by (unfold HEAP_SIZE, MAX_BITS; lia).
    unfold HEAP_SIZE, MAX_BITS in *. lia. }
  pose proof (zp2_walk (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                M (blc2 M) HEAP_SIZE t2 ol Hfu
                (BtPass2.pass2_entry _ _ _ _ _ _ _ _ Hpk HM _ _ Hnn2)
                zp2_mono_entry) as Hw.
  rewrite Egp in Hw.
  cbv beta iota in Hw.
  destruct Hw as (h' & Hinv & Hmono).
  pose proof (BtPass2.q2_h _ _ _ _ _ _ _ _ _ _ Hinv) as Hh'.
  (* the unvisited prefix holds no leaves *)
  assert (Hpre0 : wsum (fun p => ind (hp3 p <=? maxc1)) (hmaxf + 1)
                    (Z.to_nat (h' - (hmaxf + 1))) = 0).
  { pose proof (BtPass2.q2_bal _ _ _ _ _ _ _ _ _ _ Hinv) as Hbal.
    pose proof Htot as Ht.
    unfold BtPass2.lcnt in Hbal, Ht.
    replace (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
      with (Z.to_nat (h' - (hmaxf + 1)) + Z.to_nat (HEAP_SIZE - h'))%nat in Ht
      by (rewrite <- Z2Nat.inj_add by lia; f_equal; lia).
    rewrite BtPass2.wsum_app in Ht.
    rewrite Z2Nat.id in Ht by lia.
    replace (hmaxf + 1 + (h' - (hmaxf + 1))) with h' in Ht by lia.
    replace (Z.to_nat M) with (S (Z.to_nat (M - 1))) in Ht
      by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
    rewrite zp2_bsumr_S in Ht.
    replace (1 + 1) with 2 in Hbal by lia.
    replace (1 + 1) with 2 in Ht by lia.
    lia. }
  assert (Hnoleaf : forall p, hmaxf + 1 <= p < h' -> (hp3 p <=? maxc1) = false).
  { intros p Hp.
    destruct (Z.leb (hp3 p) maxc1) eqn:E; [|reflexivity].
    exfalso.
    pose proof (zp2_ind_member (fun i => hp3 i <=? maxc1) (hmaxf + 1)
                  (Z.to_nat (h' - (hmaxf + 1))) p
                  ltac:(rewrite Z2Nat.id by lia; lia) E) as Hm1.
    lia. }
  pose proof (BtPass2.pass2_exit _ _ _ _ _ _ _ _ Hpk HM _ _ Hrng2 Htot _ _
                Hinv) as (Hhist & Hrng3 & Hint3 & Hout3).
  split; [|split; [|split; [|split]]].
  - exact Hhist.
  - intros p q Hp Hpq Hq Hlp Hlq.
    destruct (Z.le_gt_cases h' p) as [Hge|Hlt].
    + apply Hmono; try lia; assumption.
    + exfalso.
      pose proof (Hnoleaf p ltac:(lia)) as Hf.
      apply Z.leb_gt in Hf. lia.
  - exact Hrng3.
  - exact Hint3.
  - exact Hout3.
Qed.

End ZHOPass2.
