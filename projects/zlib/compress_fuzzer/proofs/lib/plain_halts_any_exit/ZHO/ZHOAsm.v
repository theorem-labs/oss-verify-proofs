(** * ZHOAsm — the wsum-land bridge from masked cost sums to layer sums.

    OWNER: huffman-opt (fork).  L4 delta grind, leg (beta).

    Everything happens over an abstract window [lo, lo+n) with a leaf
    predicate, a freq profile F that is NON-INCREASING on leaf positions
    (W1), and len profiles; NO lists, NO sorting, NO permutations: the
    "sorted prefix sums" S is defined by REVERSE RANK (za_rr p = number
    of leaf positions >= p), which is a wsum, and every classical fact
    (rank surjectivity, phi = the ranked freq, rearrangement) becomes a
    window-splitting argument.

    TRUST BOUNDARY: pure Gallina over the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin KraftAdjust BtAdjust.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOCT ZHODelta.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** wsum kit additions *)

Lemma za_wsum_split : forall (f : Z -> Z) lo (k n : nat),
  (k <= n)%nat ->
  wsum f lo n = wsum f lo k + wsum f (lo + Z.of_nat k) (n - k).
Proof.
  intros f lo k; revert lo; induction k as [|k IH]; intros lo n Hk.
  - replace (lo + Z.of_nat 0) with lo by (cbn [Z.of_nat]; lia).
    replace (n - 0)%nat with n by lia. cbn [wsum]. lia.
  - destruct n as [|n]; [lia|].
    rewrite (zct_wsum_S f lo n), (zct_wsum_S f lo k).
    rewrite (IH (lo + 1) n ltac:(lia)).
    replace (lo + 1 + Z.of_nat k) with (lo + Z.of_nat (S k))
      by (rewrite Nat2Z.inj_succ; lia).
    replace (S n - S k)%nat with (n - k)%nat by lia.
    lia.
Qed.

Lemma za_wsum_pos_ex : forall (f : Z -> Z) lo n,
  0 < wsum f lo n ->
  exists i, lo <= i < lo + Z.of_nat n /\ 0 < f i.
Proof.
  intros f lo n; revert lo; induction n as [|n IH]; intros lo H.
  - cbn [wsum] in H. lia.
  - rewrite zct_wsum_S in H.
    destruct (Z_lt_le_dec 0 (f lo)) as [Hf|Hf].
    + exists lo. split; [rewrite Nat2Z.inj_succ; lia|exact Hf].
    + destruct (IH (lo + 1) ltac:(lia)) as (i & Hi & Hfi).
      exists i. split; [rewrite Nat2Z.inj_succ; lia|exact Hfi].
Qed.

Lemma za_wsum_const_ind : forall (g : Z -> bool) (c : Z) lo n,
  wsum (fun p => ind (g p) * c) lo n
  = c * wsum (fun p => ind (g p)) lo n.
Proof.
  intros g c lo n; revert lo; induction n as [|n IH]; intro lo;
    [cbn [wsum]; lia|].
  rewrite !zct_wsum_S. cbv beta. rewrite IH. ring.
Qed.

Lemma za_wsum_swap : forall (f : Z -> Z -> Z) lo1 n1 lo2 n2,
  wsum (fun i => wsum (fun j => f i j) lo2 n2) lo1 n1
  = wsum (fun j => wsum (fun i => f i j) lo1 n1) lo2 n2.
Proof.
  intros f lo1 n1; revert lo1; induction n1 as [|n1 IH]; intros lo1 lo2 n2.
  - cbn [wsum]. symmetry. apply zct_wsum_zero.
  - rewrite zct_wsum_S. cbv beta.
    rewrite (IH (lo1 + 1) lo2 n2).
    symmetry.
    apply (zct_wsum_add' (fun j => wsum (fun i => f i j) lo1 (S n1))
             (fun j => f lo1 j)
             (fun j => wsum (fun i => f i j) (lo1 + 1) n1) lo2 n2).
    intros j _. rewrite zct_wsum_S. reflexivity.
Qed.

Lemma za_ind_range_zero : forall (g lo' : Z) (n' : nat),
  g < lo' ->
  wsum (fun j => ind (j <=? g)) lo' n' = 0.
Proof.
  intros g lo' n'; revert lo'; induction n' as [|n' IH]; intros lo' Hg;
    [reflexivity|].
  rewrite zct_wsum_S. cbv beta.
  replace (lo' <=? g) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [ind]. rewrite IH by lia. lia.
Qed.

Lemma za_ind_range_count : forall (n' : nat) (g lo' : Z),
  lo' - 1 <= g <= lo' - 1 + Z.of_nat n' ->
  wsum (fun j => ind (j <=? g)) lo' n' = g - (lo' - 1).
Proof.
  induction n' as [|n' IH]; intros g lo' Hg.
  - cbn [Z.of_nat] in Hg. cbn [wsum]. lia.
  - rewrite zct_wsum_S. cbv beta.
    destruct (Z.leb_spec lo' g) as [Hle|Hgt].
    + cbn [ind]. rewrite (IH g (lo' + 1))
        by (rewrite Nat2Z.inj_succ in Hg; lia).
      lia.
    + cbn [ind]. rewrite za_ind_range_zero by lia. lia.
Qed.

(** ** The ranked window *)

Section ZHOAsmWin.

Variables (lo : Z) (n : nat).
Variable leafb : Z -> bool.
Variable F : Z -> Z.
Hypothesis HFnn : forall p, lo <= p < lo + Z.of_nat n -> leafb p = true ->
                  0 <= F p.
Hypothesis HFmono : forall p q, lo <= p -> p <= q -> q < lo + Z.of_nat n ->
                    leafb p = true -> leafb q = true -> F q <= F p.

(** reverse rank: the number of leaf positions at or after [p] *)
Definition za_rr (p : Z) : Z :=
  wsum (fun q => ind (leafb q)) p (Z.to_nat (lo + Z.of_nat n - p)).

Definition za_NL : Z := za_rr lo.

(** the sum of the [k] smallest leaf freqs = freqs at reverse rank <= k *)
Definition za_S (k : Z) : Z :=
  wsum (fun p => ind (leafb p && (za_rr p <=? k)) * F p) lo n.

Definition za_phi (r : Z) : Z := za_S r - za_S (r - 1).

Lemma za_rr_out : forall p, lo + Z.of_nat n <= p -> za_rr p = 0.
Proof.
  intros p Hp. unfold za_rr.
  replace (Z.to_nat (lo + Z.of_nat n - p)) with O by lia.
  reflexivity.
Qed.

Lemma za_rr_step : forall p, p < lo + Z.of_nat n ->
  za_rr p = ind (leafb p) + za_rr (p + 1).
Proof.
  intros p Hp. unfold za_rr.
  replace (Z.to_nat (lo + Z.of_nat n - p))
    with (S (Z.to_nat (lo + Z.of_nat n - (p + 1)))) by lia.
  rewrite zct_wsum_S. reflexivity.
Qed.

Lemma za_rr_nn : forall p, 0 <= za_rr p.
Proof.
  intro p. unfold za_rr. apply wsum_nonneg.
  intros i _. pose proof (ind_0_1 (leafb i)). lia.
Qed.

Lemma za_rr_mono : forall p q, p <= q -> za_rr q <= za_rr p.
Proof.
  intros p q Hpq.
  destruct (Z_lt_le_dec q (lo + Z.of_nat n)) as [Hq|Hq].
  2: { rewrite (za_rr_out q Hq). apply za_rr_nn. }
  assert (E : za_rr p
              = wsum (fun i => ind (leafb i)) p (Z.to_nat (q - p))
                + za_rr q).
  { unfold za_rr.
    rewrite (za_wsum_split (fun i => ind (leafb i)) p
               (Z.to_nat (q - p)) (Z.to_nat (lo + Z.of_nat n - p))
               ltac:(lia)).
    f_equal.
    replace (p + Z.of_nat (Z.to_nat (q - p))) with q by lia.
    f_equal. lia. }
  rewrite E.
  assert (0 <= wsum (fun i => ind (leafb i)) p (Z.to_nat (q - p)));
    [|lia].
  apply wsum_nonneg. intros i _. pose proof (ind_0_1 (leafb i)). lia.
Qed.

Lemma za_rr_pos : forall p, lo <= p < lo + Z.of_nat n -> leafb p = true ->
  1 <= za_rr p.
Proof.
  intros p Hp Hl. rewrite za_rr_step by lia. rewrite Hl.
  cbn [ind]. pose proof (za_rr_nn (p + 1)). lia.
Qed.

Lemma za_rr_ub : forall p, lo <= p -> za_rr p <= za_NL.
Proof.
  intros p Hp. unfold za_NL. apply za_rr_mono. exact Hp.
Qed.

Lemma za_rr_strict : forall p q, lo <= p < lo + Z.of_nat n -> p < q ->
  leafb p = true ->
  za_rr q + 1 <= za_rr p.
Proof.
  intros p q Hp Hpq Hl.
  rewrite (za_rr_step p) by lia. rewrite Hl. cbn [ind].
  pose proof (za_rr_mono (p + 1) q ltac:(lia)). lia.
Qed.

(** rank surjectivity onto [1, NL] *)
Lemma za_rr_surj_from : forall (k : nat) p,
  Z.to_nat (lo + Z.of_nat n - p) = k -> lo <= p ->
  forall r, 1 <= r <= za_rr p ->
  exists q, p <= q < lo + Z.of_nat n /\ leafb q = true /\ za_rr q = r.
Proof.
  induction k as [|k IH]; intros p Ek Hlo r Hr.
  - rewrite za_rr_out in Hr by lia. lia.
  - pose proof (za_rr_step p ltac:(lia)) as Es.
    destruct (leafb p) eqn:El.
    + cbn [ind] in Es.
      destruct (Z.eqb_spec (za_rr p) r) as [Ee|Hne].
      * exists p. split; [lia|split; [exact El|exact Ee]].
      * destruct (IH (p + 1) ltac:(lia) ltac:(lia) r ltac:(lia))
          as (q & Hq & Hql & Hqr).
        exists q. split; [lia|split; assumption].
    + cbn [ind] in Es.
      destruct (IH (p + 1) ltac:(lia) ltac:(lia) r ltac:(lia))
        as (q & Hq & Hql & Hqr).
      exists q. split; [lia|split; assumption].
Qed.

Lemma za_rr_surj : forall r, 1 <= r <= za_NL ->
  exists q, lo <= q < lo + Z.of_nat n /\ leafb q = true /\ za_rr q = r.
Proof.
  intros r Hr.
  destruct (za_rr_surj_from (Z.to_nat (lo + Z.of_nat n - lo)) lo
              eq_refl ltac:(lia) r Hr) as (q & Hq & Hql & Hqr).
  exists q. auto.
Qed.

(** ** S and phi *)

Lemma za_S_le0 : forall k, k <= 0 -> za_S k = 0.
Proof.
  intros k Hk. unfold za_S.
  rewrite (wsum_ext (fun p => ind (leafb p && (za_rr p <=? k)) * F p)
             (fun _ => 0) lo n); [apply zct_wsum_zero|].
  intros p Hp.
  destruct (leafb p) eqn:El; cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.leb_spec (za_rr p) k) as [Hle|]; cbn [ind]; [|lia].
  exfalso. pose proof (za_rr_pos p Hp El). lia.
Qed.

Lemma za_S_sat : forall k, za_NL <= k -> za_S k = za_S za_NL.
Proof.
  intros k Hk. unfold za_S.
  apply wsum_ext. intros p Hp.
  destruct (leafb p) eqn:El; cbn [andb]; [|reflexivity].
  pose proof (za_rr_ub p ltac:(lia)).
  destruct (Z.leb_spec (za_rr p) k); destruct (Z.leb_spec (za_rr p) za_NL);
    cbn [ind]; try lia.
Qed.

Lemma za_S_mono : forall a b, a <= b -> za_S a <= za_S b.
Proof.
  intros a b Hab. unfold za_S. apply wsum_le.
  intros p Hp. destruct (leafb p) eqn:El; cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.leb_spec (za_rr p) a); destruct (Z.leb_spec (za_rr p) b);
    cbn [ind]; try lia.
  pose proof (HFnn p Hp El). lia.
Qed.

Lemma za_S_nn : forall k, 0 <= za_S k.
Proof.
  intro k. pose proof (za_S_le0 0 ltac:(lia)).
  pose proof (za_S_mono 0 k).
  destruct (Z_lt_le_dec k 0) as [Hk|Hk];
    [rewrite (za_S_le0 k) by lia; lia|].
  pose proof (za_S_mono 0 k ltac:(lia)). lia.
Qed.

Lemma za_phi_split : forall r,
  za_phi r = wsum (fun p => ind (leafb p && (za_rr p =? r)) * F p) lo n.
Proof.
  intro r. unfold za_phi, za_S.
  rewrite (zct_wsum_add'
             (fun p => ind (leafb p && (za_rr p <=? r)) * F p)
             (fun p => ind (leafb p && (za_rr p <=? r - 1)) * F p)
             (fun p => ind (leafb p && (za_rr p =? r)) * F p) lo n);
    [lia|].
  intros i Hi. destruct (leafb i) eqn:El; cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.leb_spec (za_rr i) r);
    destruct (Z.leb_spec (za_rr i) (r - 1));
    destruct (Z.eqb_spec (za_rr i) r); cbn [ind]; lia.
Qed.

Lemma za_phi_nn : forall r, 0 <= za_phi r.
Proof.
  intro r. rewrite za_phi_split. apply wsum_nonneg.
  intros i Hi. destruct (leafb i) eqn:El; cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.eqb_spec (za_rr i) r); cbn [ind];
    [pose proof (HFnn i Hi El); lia|lia].
Qed.

Lemma za_phi_eval : forall p, lo <= p < lo + Z.of_nat n -> leafb p = true ->
  za_phi (za_rr p) = F p.
Proof.
  intros p Hp Hl. rewrite za_phi_split.
  rewrite (za_wsum_split _ lo (Z.to_nat (p - lo)) n ltac:(lia)).
  replace (lo + Z.of_nat (Z.to_nat (p - lo))) with p by lia.
  replace (n - Z.to_nat (p - lo))%nat
    with (S (Z.to_nat (lo + Z.of_nat n - (p + 1)))) by lia.
  rewrite zct_wsum_S. cbv beta.
  assert (EL : wsum (fun q => ind (leafb q && (za_rr q =? za_rr p)) * F q)
                 lo (Z.to_nat (p - lo)) = 0).
  { rewrite (wsum_ext (fun q => ind (leafb q && (za_rr q =? za_rr p)) * F q)
               (fun _ => 0) lo (Z.to_nat (p - lo)));
      [apply zct_wsum_zero|].
    intros q Hq. destruct (leafb q) eqn:Eq; cbn [andb]; [|cbn [ind]; lia].
    destruct (Z.eqb_spec (za_rr q) (za_rr p)) as [Ee|]; cbn [ind]; [|lia].
    exfalso.
    pose proof (za_rr_strict q p ltac:(lia) ltac:(lia) Eq). lia. }
  assert (ER : wsum (fun q => ind (leafb q && (za_rr q =? za_rr p)) * F q)
                 (p + 1) (Z.to_nat (lo + Z.of_nat n - (p + 1))) = 0).
  { rewrite (wsum_ext (fun q => ind (leafb q && (za_rr q =? za_rr p)) * F q)
               (fun _ => 0) (p + 1)
               (Z.to_nat (lo + Z.of_nat n - (p + 1))));
      [apply zct_wsum_zero|].
    intros q Hq. destruct (leafb q) eqn:Eq; cbn [andb]; [|cbn [ind]; lia].
    destruct (Z.eqb_spec (za_rr q) (za_rr p)) as [Ee|]; cbn [ind]; [|lia].
    exfalso.
    pose proof (za_rr_strict p q ltac:(lia) ltac:(lia) Hl). lia. }
  rewrite EL, ER.
  rewrite Hl, Z.eqb_refl. cbn [andb ind]. lia.
Qed.

Lemma za_phi_mono_in : forall a b, 1 <= a -> a <= b -> b <= za_NL ->
  za_phi a <= za_phi b.
Proof.
  intros a b Ha Hab Hb.
  destruct (za_rr_surj a ltac:(lia)) as (pa & Hpa & Hla & Era).
  destruct (za_rr_surj b ltac:(lia)) as (pb & Hpb & Hlb & Erb).
  assert (Hple : pb <= pa).
  { destruct (Z_lt_le_dec pa pb) as [Hlt|]; [|assumption].
    pose proof (za_rr_strict pa pb ltac:(lia) Hlt Hla). lia. }
  rewrite <- Era, <- Erb.
  rewrite (za_phi_eval pa Hpa Hla), (za_phi_eval pb Hpb Hlb).
  apply (HFmono pb pa); [lia|lia|lia|exact Hlb|exact Hla].
Qed.

(** ** The extension beyond NL (so the walk's unconditional phi
    hypotheses hold; never evaluated at ranks <= NL) *)

Definition za_Sx (k : Z) : Z :=
  za_S k + Z.max 0 (k - za_NL) * za_phi za_NL.

Lemma za_NL_nn : 0 <= za_NL.
Proof. apply za_rr_nn. Qed.

Lemma za_Sx_in : forall k, k <= za_NL -> za_Sx k = za_S k.
Proof.
  intros k Hk. unfold za_Sx.
  replace (Z.max 0 (k - za_NL)) with 0 by lia. lia.
Qed.

Lemma za_phix_split : forall r,
  za_Sx r - za_Sx (r - 1)
  = if Z.leb r za_NL then za_phi r else za_phi za_NL.
Proof.
  intro r. unfold za_Sx.
  destruct (Z.leb_spec r za_NL) as [Hr|Hr].
  - replace (Z.max 0 (r - za_NL)) with 0 by lia.
    replace (Z.max 0 (r - 1 - za_NL)) with 0 by lia.
    unfold za_phi. lia.
  - rewrite (za_S_sat r) by lia.
    destruct (Z.leb_spec (r - 1) za_NL) as [Hr1|Hr1].
    + (* r = NL + 1 *)
      assert (Er : r - 1 = za_NL) by lia.
      replace (Z.max 0 (r - za_NL)) with 1 by lia.
      replace (Z.max 0 (r - 1 - za_NL)) with 0 by lia.
      rewrite Er. unfold za_phi. lia.
    + rewrite (za_S_sat (r - 1)) by lia.
      replace (Z.max 0 (r - za_NL)) with (r - za_NL) by lia.
      replace (Z.max 0 (r - 1 - za_NL)) with (r - 1 - za_NL) by lia.
      nia.
Qed.

Lemma za_phix_nn : forall r, 0 <= za_Sx r - za_Sx (r - 1).
Proof.
  intro r. rewrite za_phix_split.
  destruct (Z.leb r za_NL); apply za_phi_nn.
Qed.

Lemma za_phix_mono : forall a b, a <= b ->
  za_Sx a - za_Sx (a - 1) <= za_Sx b - za_Sx (b - 1).
Proof.
  intros a b Hab.
  rewrite !za_phix_split.
  destruct (Z.leb_spec a za_NL) as [Ha|Ha];
    destruct (Z.leb_spec b za_NL) as [Hb|Hb].
  - (* both in: if a < 1, phi a = 0 <= phi b *)
    destruct (Z_lt_le_dec a 1) as [Ha1|Ha1].
    + assert (Ea : za_phi a = 0).
      { unfold za_phi. rewrite !za_S_le0 by lia. lia. }
      rewrite Ea. apply za_phi_nn.
    + apply za_phi_mono_in; lia.
  - destruct (Z_lt_le_dec a 1) as [Ha1|Ha1].
    + assert (Ea : za_phi a = 0).
      { unfold za_phi. rewrite !za_S_le0 by lia. lia. }
      rewrite Ea. apply za_phi_nn.
    + apply za_phi_mono_in; lia.
  - lia.
  - lia.
Qed.

Lemma za_Sx_mono : forall a b, a <= b -> za_Sx a <= za_Sx b.
Proof.
  intros a b Hab. unfold za_Sx.
  pose proof (za_S_mono a b Hab).
  pose proof (za_phi_nn za_NL). nia.
Qed.

(** ** Cardinality of a rank prefix *)

Lemma za_rr_card_from : forall (m : nat) p k,
  Z.to_nat (lo + Z.of_nat n - p) = m -> lo <= p -> 0 <= k ->
  wsum (fun q => ind (leafb q && (za_rr q <=? k))) p m
  = Z.min k (za_rr p).
Proof.
  induction m as [|m IH]; intros p k Em Hlo Hk.
  - cbn [wsum]. rewrite za_rr_out by lia. lia.
  - rewrite zct_wsum_S. cbv beta.
    rewrite (IH (p + 1) k ltac:(lia) ltac:(lia) Hk).
    pose proof (za_rr_step p ltac:(lia)) as Es.
    pose proof (za_rr_nn (p + 1)).
    destruct (leafb p) eqn:El; cbn [andb].
    + cbn [ind] in Es.
      destruct (Z.leb_spec (za_rr p) k) as [Hc|Hc]; cbn [ind]; lia.
    + cbn [ind] in Es. cbn [ind]. lia.
Qed.

Lemma za_rr_card : forall k, 0 <= k <= za_NL ->
  wsum (fun p => ind (leafb p && (za_rr p <=? k))) lo n = k.
Proof.
  intros k Hk.
  pose proof (za_rr_card_from n lo k ltac:(lia) ltac:(lia) ltac:(lia)) as E.
  rewrite E. unfold za_NL in Hk. lia.
Qed.

(** ** The Fubini decomposition of a cost sum by levels *)

Lemma za_fubini : forall (G : Z -> Z),
  (forall p, lo <= p < lo + Z.of_nat n -> leafb p = true ->
     0 <= G p <= 15) ->
  wsum (fun p => ind (leafb p) * F p * G p) lo n
  = wsum (fun j => wsum (fun p => ind (leafb p && (j <=? G p)) * F p) lo n)
      1 15.
Proof.
  intros G HG.
  rewrite <- (za_wsum_swap
                (fun p j => ind (leafb p && (j <=? G p)) * F p) lo n 1 15).
  apply wsum_ext. intros p Hp.
  destruct (leafb p) eqn:El.
  - cbn [andb].
    rewrite (za_wsum_const_ind (fun j => j <=? G p) (F p) 1 15).
    rewrite (za_ind_range_count 15 (G p) 1)
      by (pose proof (HG p Hp El); cbn [Z.of_nat]; lia).
    cbn [ind]. ring.
  - cbn [andb].
    rewrite (wsum_ext (fun j => ind false * F p) (fun _ => 0) 1 15)
      by (intros; cbn [ind]; lia).
    rewrite zct_wsum_zero. cbn [ind]. ring.
Qed.

(** ** The ascending profile pays exactly the layer sum *)

Section AscendingLen.

Variable L3 : Z -> Z.
Hypothesis HL3mono : forall p q, lo <= p -> p <= q -> q < lo + Z.of_nat n ->
  leafb p = true -> leafb q = true -> L3 p <= L3 q.

Lemma za_T3_eq : forall j,
  wsum (fun p => ind (leafb p && (j <=? L3 p)) * F p) lo n
  = za_S (wsum (fun p => ind (leafb p && (j <=? L3 p))) lo n).
Proof.
  intro j.
  set (c := wsum (fun p => ind (leafb p && (j <=? L3 p))) lo n).
  unfold za_S.
  apply wsum_ext. intros p Hp.
  destruct (leafb p) eqn:El; cbn [andb]; [|reflexivity].
  (* iff: j <= L3 p <-> za_rr p <= c *)
  destruct (Z.leb_spec j (L3 p)) as [Hj|Hj];
    destruct (Z.leb_spec (za_rr p) c) as [Hr|Hr]; try reflexivity; exfalso.
  - (* j <= L3 p but rr p > c: show c >= rr p *)
    assert (Hge : za_rr p <= c).
    { unfold c.
      rewrite (za_wsum_split (fun q => ind (leafb q && (j <=? L3 q)))
                 lo (Z.to_nat (p - lo)) n ltac:(lia)).
      replace (lo + Z.of_nat (Z.to_nat (p - lo))) with p by lia.
      assert (H1 : 0 <= wsum (fun q => ind (leafb q && (j <=? L3 q)))
                          lo (Z.to_nat (p - lo))).
      { apply wsum_nonneg. intros i _.
        pose proof (ind_0_1 (leafb i && (j <=? L3 i))). lia. }
      assert (H2 : za_rr p
                   <= wsum (fun q => ind (leafb q && (j <=? L3 q))) p
                        (n - Z.to_nat (p - lo))).
      { unfold za_rr.
        replace (Z.to_nat (lo + Z.of_nat n - p))
          with (n - Z.to_nat (p - lo))%nat by lia.
        apply wsum_le. intros q Hq.
        destruct (leafb q) eqn:Eq; cbn [andb]; [|cbn [ind]; lia].
        replace (j <=? L3 q) with true; [cbn [ind]; lia|].
        symmetry. apply Z.leb_le.
        pose proof (HL3mono p q ltac:(lia) ltac:(lia) ltac:(lia) El Eq).
        lia. }
      lia. }
    lia.
  - (* L3 p < j but rr p <= c: show c <= rr p - 1 *)
    assert (Hle : c + 1 <= za_rr p).
    { assert (Hc2 : c <= za_rr (p + 1)).
      { unfold c.
        rewrite (za_wsum_split (fun q => ind (leafb q && (j <=? L3 q)))
                   lo (Z.to_nat (p + 1 - lo)) n ltac:(lia)).
        replace (lo + Z.of_nat (Z.to_nat (p + 1 - lo))) with (p + 1) by lia.
        assert (H1 : wsum (fun q => ind (leafb q && (j <=? L3 q)))
                       lo (Z.to_nat (p + 1 - lo)) = 0).
        { rewrite (wsum_ext (fun q => ind (leafb q && (j <=? L3 q)))
                     (fun _ => 0) lo (Z.to_nat (p + 1 - lo)));
            [apply zct_wsum_zero|].
          intros q Hq.
          destruct (leafb q) eqn:Eq; cbn [andb]; [|reflexivity].
          replace (j <=? L3 q) with false; [reflexivity|].
          symmetry. apply Z.leb_gt.
          pose proof (HL3mono q p ltac:(lia) ltac:(lia) ltac:(lia) Eq El).
          lia. }
        assert (H2 : wsum (fun q => ind (leafb q && (j <=? L3 q))) (p + 1)
                       (n - Z.to_nat (p + 1 - lo))
                     <= za_rr (p + 1)).
        { unfold za_rr.
          replace (Z.to_nat (lo + Z.of_nat n - (p + 1)))
            with (n - Z.to_nat (p + 1 - lo))%nat by lia.
          apply wsum_le. intros q Hq.
          destruct (leafb q); destruct (j <=? L3 q); cbn [andb ind]; lia. }
        lia. }
      pose proof (za_rr_step p ltac:(lia)) as Es.
      rewrite El in Es. cbn [ind] in Es. lia. }
    lia.
Qed.

End AscendingLen.

(** ** Any profile pays at least the layer sum (rearrangement, wsum form) *)

Section AnyLen.

Variable L2 : Z -> Z.

Lemma za_count_le_NL : forall (g : Z -> bool),
  wsum (fun p => ind (leafb p && g p)) lo n <= za_NL.
Proof.
  intro g.
  unfold za_NL, za_rr.
  replace (Z.to_nat (lo + Z.of_nat n - lo)) with n by lia.
  apply wsum_le. intros p Hp.
  destruct (leafb p); destruct (g p); cbn [andb ind]; lia.
Qed.

Lemma za_count_nn : forall (g : Z -> bool),
  0 <= wsum (fun p => ind (leafb p && g p)) lo n.
Proof.
  intro g. apply wsum_nonneg. intros i _.
  pose proof (ind_0_1 (leafb i && g i)). lia.
Qed.

Lemma za_T2_ge : forall j,
  za_S (wsum (fun p => ind (leafb p && (j <=? L2 p))) lo n)
  <= wsum (fun p => ind (leafb p && (j <=? L2 p)) * F p) lo n.
Proof.
  intro j.
  set (Ab := fun p => leafb p && (j <=? L2 p)).
  change (za_S (wsum (fun p => ind (Ab p)) lo n)
          <= wsum (fun p => ind (Ab p) * F p) lo n).
  set (c := wsum (fun p => ind (Ab p)) lo n).
  assert (HcNL : c <= za_NL)
    by (unfold c, Ab; apply (za_count_le_NL (fun p => j <=? L2 p))).
  assert (Hcnn : 0 <= c)
    by (unfold c, Ab; apply (za_count_nn (fun p => j <=? L2 p))).
  set (Lb := fun p => leafb p && (za_rr p <=? c)).
  set (ALb := fun p => Ab p && negb (za_rr p <=? c)).
  set (LAb := fun p => Lb p && negb (Ab p)).
  assert (Egoal : za_S c = wsum (fun p => ind (Lb p) * F p) lo n)
    by reflexivity.
  (* decompositions *)
  assert (ES1 : wsum (fun p => ind (Ab p) * F p) lo n
                = wsum (fun p => ind (Ab p && (za_rr p <=? c)) * F p) lo n
                  + wsum (fun p => ind (ALb p) * F p) lo n).
  { apply zct_wsum_add'. intros p Hp. unfold ALb.
    destruct (Ab p); destruct (za_rr p <=? c); cbn [andb negb ind]; lia. }
  assert (ES2 : wsum (fun p => ind (Lb p) * F p) lo n
                = wsum (fun p => ind (Ab p && (za_rr p <=? c)) * F p) lo n
                  + wsum (fun p => ind (LAb p) * F p) lo n).
  { apply zct_wsum_add'. intros p Hp. unfold LAb, Lb, Ab.
    destruct (leafb p); destruct (j <=? L2 p); destruct (za_rr p <=? c);
      cbn [andb negb ind]; lia. }
  assert (EC1 : wsum (fun p => ind (Ab p)) lo n
                = wsum (fun p => ind (Ab p && (za_rr p <=? c))) lo n
                  + wsum (fun p => ind (ALb p)) lo n).
  { apply zct_wsum_add'. intros p Hp. unfold ALb.
    destruct (Ab p); destruct (za_rr p <=? c); cbn [andb negb ind]; lia. }
  assert (EC2 : wsum (fun p => ind (Lb p)) lo n
                = wsum (fun p => ind (Ab p && (za_rr p <=? c))) lo n
                  + wsum (fun p => ind (LAb p)) lo n).
  { apply zct_wsum_add'. intros p Hp. unfold LAb, Lb, Ab.
    destruct (leafb p); destruct (j <=? L2 p); destruct (za_rr p <=? c);
      cbn [andb negb ind]; lia. }
  assert (Ecard : wsum (fun p => ind (Lb p)) lo n = c).
  { unfold Lb. apply za_rr_card. lia. }
  assert (Ecnt : wsum (fun p => ind (ALb p)) lo n
                 = wsum (fun p => ind (LAb p)) lo n).
  { fold c in EC1. lia. }
  (* pointwise phi bounds *)
  assert (HAL : forall p, lo <= p < lo + Z.of_nat n ->
            ind (ALb p) * za_phi (c + 1) <= ind (ALb p) * F p).
  { intros p Hp. unfold ALb, Ab.
    destruct (leafb p) eqn:El; cbn [andb]; [|cbn [negb ind]; lia].
    destruct (j <=? L2 p); cbn [andb]; [|cbn [negb ind]; lia].
    destruct (Z.leb_spec (za_rr p) c) as [Hr|Hr]; cbn [negb ind]; [lia|].
    rewrite <- (za_phi_eval p Hp El).
    pose proof (za_rr_ub p ltac:(lia)).
    pose proof (za_phi_mono_in (c + 1) (za_rr p) ltac:(lia) ltac:(lia)
                  ltac:(lia)).
    lia. }
  assert (HLA : forall p, lo <= p < lo + Z.of_nat n ->
            ind (LAb p) * F p <= ind (LAb p) * za_phi c).
  { intros p Hp. unfold LAb, Lb.
    destruct (leafb p) eqn:El; cbn [andb]; [|cbn [negb ind]; lia].
    destruct (Z.leb_spec (za_rr p) c) as [Hr|Hr]; cbn [andb];
      [|cbn [negb ind]; lia].
    destruct (negb (Ab p)); cbn [ind]; [|lia].
    rewrite <- (za_phi_eval p Hp El).
    pose proof (za_rr_pos p Hp El).
    pose proof (za_phi_mono_in (za_rr p) c ltac:(lia) ltac:(lia)
                  ltac:(lia)).
    lia. }
  assert (HgeAL : za_phi (c + 1) * wsum (fun p => ind (ALb p)) lo n
                  <= wsum (fun p => ind (ALb p) * F p) lo n).
  { rewrite <- (za_wsum_const_ind ALb (za_phi (c + 1)) lo n).
    apply wsum_le. intros p Hp. exact (HAL p Hp). }
  assert (HleLA : wsum (fun p => ind (LAb p) * F p) lo n
                  <= za_phi c * wsum (fun p => ind (LAb p)) lo n).
  { rewrite <- (za_wsum_const_ind LAb (za_phi c) lo n).
    apply wsum_le. intros p Hp. exact (HLA p Hp). }
  set (t := wsum (fun p => ind (ALb p)) lo n) in *.
  assert (Htnn : 0 <= t).
  { unfold t. apply wsum_nonneg. intros i _.
    pose proof (ind_0_1 (ALb i)). lia. }
  destruct (Z_lt_le_dec 0 t) as [Htpos|Ht0].
  - destruct (za_wsum_pos_ex (fun p => ind (ALb p)) lo n Htpos)
      as (p0 & Hp0 & Hind0).
    assert (Hw : c + 1 <= za_NL).
    { revert Hind0. unfold ALb, Ab.
      destruct (leafb p0) eqn:El0; cbn [andb]; [|cbn [ind]; lia].
      destruct (j <=? L2 p0); cbn [andb]; [|cbn [ind]; lia].
      destruct (Z.leb_spec (za_rr p0) c) as [Hr0|Hr0]; cbn [negb ind];
        intro; [lia|].
      pose proof (za_rr_ub p0 ltac:(lia)). lia. }
    assert (Hphis : za_phi c <= za_phi (c + 1)).
    { destruct (Z_lt_le_dec c 1) as [Hc1|Hc1].
      - assert (Ec : za_phi c = 0).
        { unfold za_phi. rewrite !za_S_le0 by lia. lia. }
        rewrite Ec. apply za_phi_nn.
      - apply za_phi_mono_in; lia. }
    rewrite Egoal, ES2.
    replace (wsum (fun p => ind (Ab p && (za_rr p <=? c)) * F p) lo n
             + wsum (fun p => ind (LAb p) * F p) lo n)
      with (wsum (fun p => ind (Ab p) * F p) lo n
            - wsum (fun p => ind (ALb p) * F p) lo n
            + wsum (fun p => ind (LAb p) * F p) lo n) by lia.
    rewrite <- Ecnt in HleLA.
    nia.
  - assert (Et0 : t = 0) by lia.
    rewrite Egoal, ES2.
    replace (wsum (fun p => ind (Ab p && (za_rr p <=? c)) * F p) lo n
             + wsum (fun p => ind (LAb p) * F p) lo n)
      with (wsum (fun p => ind (Ab p) * F p) lo n
            - wsum (fun p => ind (ALb p) * F p) lo n
            + wsum (fun p => ind (LAb p) * F p) lo n) by lia.
    rewrite <- Ecnt in HleLA.
    nia.
Qed.

(** ** The Fibonacci cap transported to ranks (pigeonhole) *)

Lemma za_cap : forall (CAPF : Z -> Z) lv r,
  (forall p, lo <= p < lo + Z.of_nat n -> leafb p = true ->
     lv <= L2 p -> F p <= CAPF lv) ->
  1 <= r ->
  r <= wsum (fun p => ind (leafb p && (lv <=? L2 p))) lo n ->
  za_phi r <= CAPF lv.
Proof.
  intros CAPF lv r Hcap Hr1 Hrc.
  set (c := wsum (fun p => ind (leafb p && (lv <=? L2 p))) lo n) in *.
  assert (HcNL : c <= za_NL)
    by (unfold c; apply (za_count_le_NL (fun p => lv <=? L2 p))).
  destruct (za_rr_surj r ltac:(lia)) as (pr & Hpr & Hlr & Err).
  rewrite <- Err.
  rewrite (za_phi_eval pr Hpr Hlr).
  assert (Hsplit : c = wsum (fun q => ind (leafb q && (lv <=? L2 q))) lo
                         (Z.to_nat (pr + 1 - lo))
                       + wsum (fun q => ind (leafb q && (lv <=? L2 q)))
                           (pr + 1) (n - Z.to_nat (pr + 1 - lo))).
  { unfold c.
    rewrite (za_wsum_split (fun q => ind (leafb q && (lv <=? L2 q)))
               lo (Z.to_nat (pr + 1 - lo)) n ltac:(lia)).
    replace (lo + Z.of_nat (Z.to_nat (pr + 1 - lo))) with (pr + 1) by lia.
    reflexivity. }
  assert (Hright : wsum (fun q => ind (leafb q && (lv <=? L2 q))) (pr + 1)
                     (n - Z.to_nat (pr + 1 - lo))
                   <= za_rr (pr + 1)).
  { unfold za_rr.
    replace (Z.to_nat (lo + Z.of_nat n - (pr + 1)))
      with (n - Z.to_nat (pr + 1 - lo))%nat by lia.
    apply wsum_le. intros q Hq.
    destruct (leafb q); destruct (lv <=? L2 q); cbn [andb ind]; lia. }
  assert (Hrr1 : za_rr (pr + 1) = r - 1).
  { pose proof (za_rr_step pr ltac:(lia)) as Es.
    rewrite Hlr in Es. cbn [ind] in Es. lia. }
  assert (Hleft : 0 < wsum (fun q => ind (leafb q && (lv <=? L2 q))) lo
                        (Z.to_nat (pr + 1 - lo))) by lia.
  destruct (za_wsum_pos_ex (fun q => ind (leafb q && (lv <=? L2 q)))
              lo (Z.to_nat (pr + 1 - lo)) Hleft)
    as (q0 & Hq0 & Hq0i).
  revert Hq0i.
  destruct (leafb q0) eqn:Eq0; cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.leb_spec lv (L2 q0)) as [Hq0l|]; cbn [ind]; intro; [|lia].
  eapply Z.le_trans.
  - apply (HFmono q0 pr); [lia|lia|lia|exact Eq0|exact Hlr].
  - apply (Hcap q0); [lia|exact Eq0|exact Hq0l].
Qed.

End AnyLen.

End ZHOAsmWin.
