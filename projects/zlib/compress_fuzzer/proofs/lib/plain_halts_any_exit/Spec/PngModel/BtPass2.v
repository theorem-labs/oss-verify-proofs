(** * BtPass2 — the recompute pass distributes the ADJUSTED histogram exactly.

    OWNER: an earlier development run.

    On the overflow branch [gen_bitlen] runs [gb_pass2]: walk the parked
    window BACKWARDS (h descends = increasing frequency = longest codes
    first), assigning length [bits] to the next [blc bits] leaves, stepping
    [bits] down as each group fills.  What the Kraft face needs is EXACTNESS:
    the final leaf-length histogram IS [blc2] — that is [BlcOf] for
    [gen_codes], and it carries [zksum blc2 = 2^M] (BtAdjust) onto the
    lengths themselves.

    The one subtle premise is the LEAF BALANCE: the loop is fuelled, not
    guarded, and it descends [h] only while leaves remain to be found, so
    "总 leaves in the window = sum of the histogram" is what keeps the cursor
    above [heap_max].  The balance holds because [gb_adjust] moves counts
    between levels without changing their sum (BtAdjust's pointwise value
    lemma), and pass 1 counted every leaf once (BtLevels). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtPass1 BtLevels GenBitlen.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Window split *)

Lemma wsum_app : forall f lo j k,
  wsum f lo (j + k) = wsum f lo j + wsum f (lo + Z.of_nat j) k.
Proof.
  intros f lo j; revert lo.
  induction j as [|j IH]; intros lo k.
  - cbn [Nat.add wsum]. cbn [Z.of_nat]. rewrite Z.add_0_r. lia.
  - cbn [Nat.add]. rewrite !(wsum_split_first f lo).
    rewrite IH. rewrite Nat2Z.inj_succ. 
    replace (lo + Z.succ (Z.of_nat j)) with (lo + 1 + Z.of_nat j) by lia.
    lia.
Qed.

(** ** Right-open histogram sums, [b .. b+k) *)

Section Pass2.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hmf0 : 0 <= hmaxf.
Variables (t2 : Tree) (blc2 : zarr).
Hypothesis Hrng2 : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
                   1 <= t_len t2 (hp3 p) <= M.
Hypothesis Hnn2 : forall b, 0 <= blc2 b.

Fixpoint bsumr (k : nat) (b : Z) : Z :=
  match k with
  | O => 0
  | S k' => blc2 b + bsumr k' (b + 1)
  end.

Lemma bsumr_split : forall j k b,
  bsumr (j + k) b = bsumr j b + bsumr k (b + Z.of_nat j).
Proof.
  induction j as [|j IH]; intros k b.
  - cbn [Nat.add bsumr]. cbn [Z.of_nat]. rewrite Z.add_0_r. lia.
  - cbn [Nat.add bsumr]. rewrite IH, Nat2Z.inj_succ.
    replace (b + Z.succ (Z.of_nat j)) with (b + 1 + Z.of_nat j) by lia.
    lia.
Qed.

Lemma bsumr_is_wsum : forall k b, bsumr k b = wsum blc2 b k.
Proof.
  induction k as [|k IH]; intro b; cbn [bsumr wsum]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bsumr_nonneg : forall k b, 0 <= bsumr k b.
Proof.
  induction k as [|k IH]; intro b; cbn [bsumr]; [lia|].
  pose proof (Hnn2 b). pose proof (IH (b + 1)). lia.
Qed.

(** Leaf count and leaf-length histogram over a window. *)
Definition lcnt (t : Tree) (lo : Z) (n : nat) : Z :=
  wsum (fun p => ind (hp3 p <=? maxc1)) lo n.

Definition hist (t : Tree) (b lo : Z) (n : nat) : Z :=
  wsum (fun p => ind ((hp3 p <=? maxc1) && (Z.eqb (t_len t (hp3 p)) b)))
       lo n.

(** ** The walk invariant *)

Record Pass2Inv (bits n h : Z) (t : Tree) : Prop :=
mkPass2Inv {
  q2_bits : 1 <= bits <= M;
  q2_n    : 0 <= n <= blc2 bits;
  q2_h    : hmaxf + 1 <= h <= HEAP_SIZE;
  q2_hi   : forall b, bits < b <= M ->
            hist t b h (Z.to_nat (HEAP_SIZE - h)) = blc2 b;
  q2_at   : hist t bits h (Z.to_nat (HEAP_SIZE - h)) = blc2 bits - n;
  q2_rng  : forall p, h <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
            bits <= t_len t (hp3 p) <= M;
  q2_bal  : lcnt t h (Z.to_nat (HEAP_SIZE - h))
            = bsumr (Z.to_nat (M - bits)) (bits + 1) + (blc2 bits - n);
  q2_lo   : forall p, hmaxf <= p < h ->
            t_len t (hp3 p) = t_len t2 (hp3 p);
  q2_int  : forall p, hmaxf <= p < HEAP_SIZE -> maxc1 < hp3 p ->
            t_len t (hp3 p) = t_len t2 (hp3 p);
  q2_out  : forall y, pcount hp3 hmaxf y = 0 -> tr_dl t y = tr_dl t2 y
}.

(** Total leaf balance at entry, taken as a hypothesis: BtLevels supplies
    "pass-1's histogram counts every leaf once" and BtAdjust's pointwise
    value shows the adjust conserves the sum.  Spelled over the FULL window
    below the root, which is where every leaf lives. *)
Hypothesis Htot :
  lcnt t2 (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
  = bsumr (Z.to_nat M) 1.

Lemma pass2_entry :
  Pass2Inv M (blc2 M) HEAP_SIZE t2.
Proof.
  constructor.
  - lia.
  - pose proof (Hnn2 M). lia.
  - pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk). lia.
  - intros b Hb. lia.
  - replace (HEAP_SIZE - HEAP_SIZE) with 0 by lia.
    cbn [Z.to_nat]. unfold hist. cbn [wsum]. lia.
  - intros p Hp Hl. lia.
  - replace (HEAP_SIZE - HEAP_SIZE) with 0 by lia.
    replace (Z.to_nat (M - M)) with O by lia.
    cbn [Z.to_nat bsumr]. unfold lcnt. cbn [wsum]. lia.
  - intros p Hp. reflexivity.
  - intros p Hp Hm. reflexivity.
  - intros y Hy. reflexivity.
Qed.


Lemma wsum_ind_pos : forall (f : Z -> bool) lo n,
  1 <= wsum (fun i => ind (f i)) lo n ->
  exists i, lo <= i < lo + Z.of_nat n /\ f i = true.
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intros lo H; cbn [wsum] in H.
  - lia.
  - destruct (f lo) eqn:E.
    + exists lo. rewrite Nat2Z.inj_succ. split; [lia | exact E].
    + cbn [ind] in H.
      destruct (IH (lo + 1) ltac:(lia)) as [i [Hi Hf]].
      exists i. rewrite Nat2Z.inj_succ. split; [lia | exact Hf].
Qed.

(** With leaves still owed, the cursor sits at least two above the root:
    the total balance says an unvisited leaf exists, and no leaf is the
    root slot. *)
Lemma pass2_leaf_below : forall bits n h t,
  Pass2Inv bits n h t -> 1 <= n ->
  hmaxf + 2 <= h.
Proof.
  intros bits n h t Hinv Hn.
  destruct Hinv as [Hb Hnr Hh Hhi Hat Hrng Hbal Hlo Hint Hout].
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hlt.
  (* split the total leaf count at the cursor *)
  assert (Hsplit : Z.to_nat (HEAP_SIZE - (hmaxf + 1))
                   = (Z.to_nat (h - (hmaxf + 1)) + Z.to_nat (HEAP_SIZE - h))%nat).
  { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
  assert (Hlow : lcnt t2 (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))
                 = bsumr (Z.to_nat (bits - 1)) 1 + n).
  { pose proof Htot as Ht.
    rewrite Hsplit in Ht.
    unfold lcnt in *.
    rewrite wsum_app in Ht.
    rewrite Z2Nat.id in Ht by lia.
    replace (hmaxf + 1 + (h - (hmaxf + 1))) with h in Ht by lia.
    (* the total histogram splits below/at/above [bits] *)
    assert (Hbs : bsumr (Z.to_nat M) 1
                  = bsumr (Z.to_nat (bits - 1)) 1
                    + (blc2 bits + bsumr (Z.to_nat (M - bits)) (bits + 1))).
    { replace (Z.to_nat M)
        with (Z.to_nat (bits - 1) + S (Z.to_nat (M - bits)))%nat
        by (rewrite <- Z2Nat.inj_succ by lia;
            rewrite <- Z2Nat.inj_add by lia; f_equal; lia).
      rewrite bsumr_split.
      rewrite Z2Nat.id by lia.
      replace (1 + (bits - 1)) with bits by lia.
      cbn [bsumr].
      replace (bits + 1) with (bits + 1) by lia.
      lia. }
    unfold lcnt in Hbal. lia. }
  assert (Hpos : 1 <= wsum (fun p => ind (hp3 p <=? maxc1)) (hmaxf + 1)
                        (Z.to_nat (h - (hmaxf + 1)))).
  { unfold lcnt in Hlow.
    pose proof (bsumr_nonneg (Z.to_nat (bits - 1)) 1). lia. }
  destruct (wsum_ind_pos _ _ _ Hpos) as [p [Hp _]].
  rewrite Z2Nat.id in Hp by lia.
  lia.
Qed.


(** ** Window growth and write stability *)

Lemma hist_grow : forall t b h,
  h <= HEAP_SIZE ->
  hist t b (h - 1) (Z.to_nat (HEAP_SIZE - (h - 1)))
  = ind ((hp3 (h - 1) <=? maxc1) && (Z.eqb (t_len t (hp3 (h - 1))) b))
    + hist t b h (Z.to_nat (HEAP_SIZE - h)).
Proof.
  intros t b h Hh. unfold hist.
  replace (Z.to_nat (HEAP_SIZE - (h - 1)))
    with (S (Z.to_nat (HEAP_SIZE - h)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite wsum_split_first.
  replace (h - 1 + 1) with h by lia.
  reflexivity.
Qed.

Lemma lcnt_grow : forall t h,
  h <= HEAP_SIZE ->
  lcnt t (h - 1) (Z.to_nat (HEAP_SIZE - (h - 1)))
  = ind (hp3 (h - 1) <=? maxc1) + lcnt t h (Z.to_nat (HEAP_SIZE - h)).
Proof.
  intros t h Hh. unfold lcnt.
  replace (Z.to_nat (HEAP_SIZE - (h - 1)))
    with (S (Z.to_nat (HEAP_SIZE - h)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite wsum_split_first.
  replace (h - 1 + 1) with h by lia.
  reflexivity.
Qed.

Lemma lcnt_tree_irrel : forall t t' lo n, lcnt t lo n = lcnt t' lo n.
Proof. intros. reflexivity. Qed.

Lemma hist_setlen_out : forall t m v b lo n,
  (forall p, lo <= p < lo + Z.of_nat n -> hp3 p <> m) ->
  hist (t_setlen t m v) b lo n = hist t b lo n.
Proof.
  intros t m v b lo n H. unfold hist.
  apply wsum_ext. intros p Hp.
  rewrite t_len_setlen_other' by (apply H; exact Hp).
  reflexivity.
Qed.

(** A leaf slot is never the root slot. *)
Lemma leaf_not_root : forall p, hmaxf <= p < HEAP_SIZE ->
  hp3 p <= maxc1 -> hmaxf + 1 <= p.
Proof.
  intros p Hp Hl.
  destruct (Z.eq_dec p hmaxf) as [->|Hne]; [|lia].
  rewrite (bp_root _ _ _ _ _ _ _ Hpk) in Hl.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk).
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk).
  lia.
Qed.

(** ** The three steps *)

Lemma pass2_step_skip : forall bits n h t,
  Pass2Inv bits n h t -> 1 <= n -> maxc1 < hp3 (h - 1) ->
  Pass2Inv bits n (h - 1) t.
Proof.
  intros bits n h t Hinv Hn Hm.
  pose proof (pass2_leaf_below bits n h t Hinv Hn) as Hh2.
  destruct Hinv as [Hb Hnr Hh Hhi Hat Hrng Hbal Hlo Hint Hout].
  assert (Elf : (hp3 (h - 1) <=? maxc1) = false)
    by (apply Z.leb_gt; lia).
  constructor; try assumption.
  - lia.
  - intros b Hbr. rewrite hist_grow by lia.
    rewrite Elf. cbn [andb ind]. rewrite (Hhi b Hbr). lia.
  - rewrite hist_grow by lia.
    rewrite Elf. cbn [andb ind]. lia.
  - intros p Hp Hl.
    destruct (Z.eq_dec p (h - 1)) as [->|Hne]; [lia|].
    apply Hrng; [lia | exact Hl].
  - rewrite lcnt_grow by lia.
    rewrite Elf. cbn [ind]. lia.
  - intros p Hp. apply Hlo. lia.
Qed.

Lemma pass2_step_take : forall bits n h t t',
  Pass2Inv bits n h t -> 1 <= n -> hp3 (h - 1) <= maxc1 ->
  ((t' = t /\ t_len t (hp3 (h - 1)) = bits)
   \/ t' = t_setlen t (hp3 (h - 1)) bits) ->
  Pass2Inv bits (n - 1) (h - 1) t'.
Proof.
  intros bits n h t t' Hinv Hn Hm Hcase.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
  destruct Hinv as [Hb Hnr Hh Hhi Hat Hrng Hbal Hlo Hint Hout].
  assert (Hleaf1 : hmaxf + 1 <= h - 1)
    by (apply leaf_not_root; [lia | exact Hm]).
  assert (Elf : (hp3 (h - 1) <=? maxc1) = true)
    by (apply Z.leb_le; lia).
  set (m := hp3 (h - 1)) in *.
  (* the new slot's length is [bits], and nothing else moves *)
  assert (Hlen' : t_len t' m = bits).
  { destruct Hcase as [[-> Hd]| ->]; [exact Hd|].
    rewrite t_len_setlen_same'. unfold u16. apply Z.mod_small. lia. }
  assert (Hoth : forall p, hmaxf <= p < HEAP_SIZE -> p <> h - 1 ->
                 t_len t' (hp3 p) = t_len t (hp3 p)).
  { intros p Hp Hne.
    destruct Hcase as [[-> _]| ->]; [reflexivity|].
    rewrite t_len_setlen_other'; [reflexivity|].
    apply (pk_distinct _ _ _ _ _ _ _ Hpk); lia. }
  assert (Hvalne : forall y, maxc1 < y -> t_len t' y = t_len t y).
  { intros y Hy.
    destruct Hcase as [[-> _]| ->]; [reflexivity|].
    rewrite t_len_setlen_other'; [reflexivity | lia]. }
  constructor; try assumption.
  - lia.
  - lia.
  - intros b Hbr.
    rewrite hist_grow by lia. fold m.
    rewrite Elf, Hlen'.
    replace (Z.eqb bits b) with false
      by (symmetry; apply Z.eqb_neq; lia).
    cbn [andb ind].
    rewrite <- (Hhi b Hbr).
    unfold hist. rewrite Z.add_0_l.
    apply wsum_ext. intros p Hp.
    rewrite Z2Nat.id in Hp by lia.
    rewrite (Hoth p ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite hist_grow by lia. fold m.
    rewrite Elf, Hlen', Z.eqb_refl. cbn [andb ind].
    replace (hist t' bits h (Z.to_nat (HEAP_SIZE - h)))
      with (hist t bits h (Z.to_nat (HEAP_SIZE - h))).
    + rewrite Hat. lia.
    + unfold hist. apply wsum_ext. intros p Hp.
      rewrite Z2Nat.id in Hp by lia.
      rewrite (Hoth p ltac:(lia) ltac:(lia)). reflexivity.
  - intros p Hp Hl.
    destruct (Z.eq_dec p (h - 1)) as [->|Hne].
    + fold m. rewrite Hlen'. lia.
    + rewrite (Hoth p ltac:(lia) Hne). apply Hrng; [lia | exact Hl].
  - rewrite lcnt_grow by lia. fold m.
    rewrite Elf. cbn [ind].
    rewrite (lcnt_tree_irrel t' t). lia.
  - intros p Hp.
    rewrite (Hoth p ltac:(lia) ltac:(lia)).
    apply Hlo. lia.
  - intros p Hp Hup.
    destruct Hcase as [[-> _]| ->]; [apply Hint; assumption|].
    rewrite t_len_setlen_other' by lia.
    apply Hint; assumption.
  - intros y Hy.
    assert (Hym : y <> m).
    { intro He. subst y.
      pose proof (pcount_member hp3 hmaxf (h - 1) ltac:(lia)) as Hmem.
      fold m in Hmem. lia. }
    destruct Hcase as [[-> _]| ->]; [apply Hout; exact Hy|].
    unfold t_setlen. cbn [tr_dl]. rewrite zset_other by exact Hym.
    apply Hout. exact Hy.
Qed.

Lemma pass2_step_group : forall bits h t,
  Pass2Inv bits 0 h t -> 2 <= bits ->
  Pass2Inv (bits - 1) (blc2 (bits - 1)) h t.
Proof.
  intros bits h t Hinv Hb2.
  destruct Hinv as [Hb Hnr Hh Hhi Hat Hrng Hbal Hlo Hint Hout].
  assert (Hzero : hist t (bits - 1) h (Z.to_nat (HEAP_SIZE - h)) = 0).
  { transitivity (wsum (fun _ : Z => 0) h (Z.to_nat (HEAP_SIZE - h)));
      [|apply wsum_zero].
    apply wsum_ext. intros p Hp.
    rewrite Z2Nat.id in Hp by lia.
    destruct (Z.leb (hp3 p) maxc1) eqn:El.
    - apply Z.leb_le in El.
      assert (bits <= t_len t (hp3 p) <= M) by (apply Hrng; [lia | lia]).
      replace (Z.eqb (t_len t (hp3 p)) (bits - 1)) with false
        by (symmetry; apply Z.eqb_neq; lia).
      rewrite andb_false_r. reflexivity.
    - reflexivity. }
  constructor; try assumption.
  - lia.
  - pose proof (Hnn2 (bits - 1)). lia.
  - intros b Hbr.
    destruct (Z.eq_dec b bits) as [->|Hne].
    + rewrite Hat. lia.
    + apply Hhi. lia.
  - rewrite Hzero. lia.
  - intros p Hp Hl.
    assert (bits <= t_len t (hp3 p) <= M) by (apply Hrng; assumption).
    lia.
  - rewrite Hbal.
    replace (Z.to_nat (M - (bits - 1))) with (S (Z.to_nat (M - bits)))
      by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
    cbn [bsumr].
    replace (bits - 1 + 1) with bits by lia.
    lia.
Qed.


(** ** The walk *)

Lemma pass2_walk : forall fuel bits n h t ol,
  (h - hmaxf) + bits + 1 <= Z.of_nat fuel ->
  Pass2Inv bits n h t ->
  match gb_pass2 fuel hp3 maxc1 t blc2 bits n h ol with
  | (t3, _) => exists h', Pass2Inv 1 0 h' t3
  end.
Proof.
  induction fuel as [|f IH]; intros bits n h t ol Hf Hinv.
  - pose proof (q2_h _ _ _ _ Hinv). pose proof (q2_bits _ _ _ _ Hinv).
    cbn [Z.of_nat] in Hf. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    pose proof (q2_h _ _ _ _ Hinv) as Hhr.
    pose proof (q2_bits _ _ _ _ Hinv) as Hbr.
    pose proof (q2_n _ _ _ _ Hinv) as Hnr.
    cbn [gb_pass2].
    destruct (Z.eqb n 0) eqn:En.
    + apply Z.eqb_eq in En. subst n.
      destruct (Z.leb bits 1) eqn:Eb.
      * apply Z.leb_le in Eb.
        assert (E1 : bits = 1) by lia. subst bits.
        exists h. exact Hinv.
      * apply Z.leb_gt in Eb.
        apply IH; [lia|].
        apply pass2_step_group; [exact Hinv | lia].
    + apply Z.eqb_neq in En.
      assert (Hn1 : 1 <= n) by lia.
      destruct (Z.ltb maxc1 (hp3 (h - 1))) eqn:Em.
      * apply Z.ltb_lt in Em.
        apply IH; [lia|].
        apply pass2_step_skip; [exact Hinv | exact Hn1 | exact Em].
      * apply Z.ltb_ge in Em.
        destruct (Z.eqb (t_len t (hp3 (h - 1))) bits) eqn:El.
        -- apply Z.eqb_eq in El.
           apply IH; [lia|].
           apply (pass2_step_take bits n h t t);
             [exact Hinv | exact Hn1 | exact Em | left; auto].
        -- apply IH; [lia|].
           apply (pass2_step_take bits n h t (t_setlen t (hp3 (h - 1)) bits));
             [exact Hinv | exact Hn1 | exact Em | right; reflexivity].
Qed.

(** ** The exit package *)

Lemma pass2_exit : forall h t,
  Pass2Inv 1 0 h t ->
  (forall b, 1 <= b <= M ->
     hist t b (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))) = blc2 b)
  /\ (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
      1 <= t_len t (hp3 p) <= M)
  /\ (forall p, hmaxf <= p < HEAP_SIZE -> maxc1 < hp3 p ->
      t_len t (hp3 p) = t_len t2 (hp3 p))
  /\ (forall y, pcount hp3 hmaxf y = 0 -> tr_dl t y = tr_dl t2 y).
Proof.
  intros h t Hinv.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
  destruct Hinv as [Hb Hnr Hh Hhi Hat Hrng Hbal Hlo Hint Hout].
  (* the unvisited prefix holds no leaves *)
  assert (Hsplit : Z.to_nat (HEAP_SIZE - (hmaxf + 1))
                   = (Z.to_nat (h - (hmaxf + 1)) + Z.to_nat (HEAP_SIZE - h))%nat).
  { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
  assert (Hlow0 : lcnt t2 (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1))) = 0).
  { pose proof Htot as Ht.
    rewrite Hsplit in Ht.
    unfold lcnt in *.
    rewrite wsum_app in Ht.
    rewrite Z2Nat.id in Ht by lia.
    replace (hmaxf + 1 + (h - (hmaxf + 1))) with h in Ht by lia.
    assert (Hbs : bsumr (Z.to_nat M) 1
                  = blc2 1 + bsumr (Z.to_nat (M - 1)) (1 + 1)).
    { replace (Z.to_nat M) with (S (Z.to_nat (M - 1)))
        by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
      cbn [bsumr]. reflexivity. }
    unfold lcnt in Hbal. lia. }
  assert (Hnoleaf : forall p, hmaxf + 1 <= p < h -> (hp3 p <=? maxc1) = false).
  { intros p Hp.
    destruct (Z.leb (hp3 p) maxc1) eqn:E; [|reflexivity].
    exfalso.
    pose proof (wsum_one_point (fun q => ind (hp3 q <=? maxc1))
                  (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1))) p) as HP.
    cbn beta in HP.
    rewrite E in HP. cbn [ind] in HP.
    unfold lcnt in Hlow0.
    assert (1 <= wsum (fun q => ind (hp3 q <=? maxc1)) (hmaxf + 1)
                   (Z.to_nat (h - (hmaxf + 1)))); [|lia].
    apply HP.
    - intros i _. apply ind_0_1.
    - rewrite Z2Nat.id by lia. lia. }
  split; [|split; [|split]].
  - intros b Hbr.
    unfold hist. rewrite Hsplit, wsum_app.
    rewrite Z2Nat.id by lia.
    replace (hmaxf + 1 + (h - (hmaxf + 1))) with h by lia.
    assert (Hlowz : wsum (fun p => ind ((hp3 p <=? maxc1)
                                        && (Z.eqb (t_len t (hp3 p)) b)))
                         (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1))) = 0).
    { transitivity (wsum (fun _ : Z => 0) (hmaxf + 1)
                      (Z.to_nat (h - (hmaxf + 1))));
        [|apply wsum_zero].
      apply wsum_ext. intros p Hp.
      rewrite Z2Nat.id in Hp by lia.
      rewrite (Hnoleaf p ltac:(lia)). reflexivity. }
    rewrite Hlowz.
    destruct (Z.eq_dec b 1) as [->|Hne].
    + unfold hist in Hat. rewrite Hat. lia.
    + unfold hist in Hhi. rewrite (Hhi b ltac:(lia)). lia.
  - intros p Hp Hl.
    destruct (Z_le_gt_dec h p) as [Hhp|Hhp].
    + assert (1 <= t_len t (hp3 p) <= M) by (apply Hrng; [lia | exact Hl]).
      lia.
    + rewrite (Hlo p ltac:(lia)).
      apply Hrng2. lia.
  - exact Hint.
  - exact Hout.
Qed.

End Pass2.

Print Assumptions pass2_entry.
Print Assumptions pass2_walk.
Print Assumptions pass2_exit.
