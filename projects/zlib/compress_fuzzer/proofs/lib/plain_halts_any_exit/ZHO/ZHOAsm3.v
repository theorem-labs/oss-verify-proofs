(** * ZHOAsm3 — the L4 delta assembly (leg gamma).

    OWNER: huffman-opt (fork).

    Instantiates the abstract window bridge (ZHOAsm), the census
    (ZHOAsm2) and the cone walk (ZHODelta) at the repaired
    zho_adjust_delta premise set, producing the certificate that the two
    arithmetic closers (12288 generic / 2048 at elems <= 30) consume.

    TRUST BOUNDARY: pure Gallina over the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin BtCensus2 BtCensus3 BtCensus4 BtPass2
  KraftAdjust BtAdjust.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOCT ZHODelta ZHOAsm ZHOAsm2 ZHOPass2 ZHOFib.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** gb_adjust is the iterated cone body *)

Lemma zha_adjust_iter : forall (k f : nat) (blc : zarr),
  (1 <= k)%nat -> (k <= f)%nat ->
  gb_adjust f 15 blc (2 * Z.of_nat k) = zd_iter k blc.
Proof.
  induction k as [|k IH]; intros f blc Hk Hf; [lia|].
  destruct f as [|f]; [lia|].
  destruct k as [|k].
  - rewrite gb_adjust_unfold_last by (cbn [Z.of_nat]; lia).
    reflexivity.
  - rewrite gb_adjust_unfold_step by (rewrite !Nat2Z.inj_succ; lia).
    replace (2 * Z.of_nat (S (S k)) - 2) with (2 * Z.of_nat (S k))
      by (rewrite !Nat2Z.inj_succ; lia).
    rewrite (IH f (gba_body 15 blc) ltac:(lia) ltac:(lia)).
    symmetry. apply zd_iter_S_in.
Qed.

(** ** zksum, split at the top level *)

Lemma zha_zko_wsum : forall (x : zarr) (k a : nat),
  zksum_over 15 x (seq a k)
  = wsum (fun j => x j * 2 ^ (15 - j)) (Z.of_nat a) k.
Proof.
  intros x k; induction k as [|k IH]; intro a; [reflexivity|].
  cbn [seq]. rewrite zksum_over_cons. rewrite (IH (S a)).
  rewrite zct_wsum_S. cbv beta.
  replace (Z.of_nat a + 1) with (Z.of_nat (S a))
    by (rewrite Nat2Z.inj_succ; lia).
  reflexivity.
Qed.

Lemma zha_zksum_wsum : forall (x : zarr),
  zksum 15 x = wsum (fun j => x j * 2 ^ (15 - j)) 1 14 + x 15.
Proof.
  intro x. unfold zksum.
  change (Z.to_nat 15) with 15%nat.
  rewrite (zha_zko_wsum x 15 1).
  change (Z.of_nat 1) with 1.
  rewrite wsum_split_last. cbv beta.
  replace (1 + Z.of_nat 14) with 15 by (cbn [Z.of_nat]; lia).
  replace (15 - 15) with 0 by lia.
  rewrite Z.pow_0_r. lia.
Qed.

Lemma zha_fib_step : forall n, fibZ n <= fibZ (S n).
Proof.
  intro n. destruct n as [|m]; [cbn; lia|].
  rewrite fibZ_SS. pose proof (fibZ_nonneg m). lia.
Qed.

Lemma zha_fib_mono : forall a b, (a <= b)%nat -> fibZ a <= fibZ b.
Proof.
  intros a b Hab. induction Hab as [|b Hab IH]; [lia|].
  pose proof (zha_fib_step b). lia.
Qed.

Section ZHOAssembly.

Variables (elems maxc1 : Z) (tE tL t2 t3 : Tree) (hp3 : zarr)
          (hmaxf ndf : Z) (blc1 blc2 : zarr) (ov ol1 ol2 v K : Z).
Hypothesis Hpk : BtParked elems maxc1 tE tL hp3 hmaxf ndf.
Hypothesis Hel : 0 < elems <= L_CODES.
Hypothesis Hmc : maxc1 < elems.
Hypothesis Hmf0 : 0 <= hmaxf.
Hypothesis Hfnn : forall n, 0 <= n < elems -> 0 <= t_freq tE n.
Hypothesis Hmass : wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
                     0 (Z.to_nat elems) <= 16384.
Hypothesis Hp1len : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  t_len t2 (hp3 p) = Z.min (t_len t2 (t_dad tL (hp3 p)) + 1) 15.
Hypothesis Hp1root : t_len t2 (ndf - 1) = 0.
Hypothesis Hp1rng : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  1 <= t_len t2 (hp3 p) <= 15.
Hypothesis Hblc : forall b, 0 <= b <= 15 ->
  blc1 b = wsum (fun p => ind ((hp3 p <=? maxc1)
                               && (Z.eqb (t_len t2 (hp3 p)) b)))
             (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
Hypothesis HW1 : forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
  hp3 p <= maxc1 -> hp3 q <= maxc1 ->
  t_freq tE (hp3 q) <= t_freq tE (hp3 p).
Hypothesis HW2 : forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
  fibZ (Z.to_nat (t_len t2 (hp3 p)) + 1) * t_freq tE (hp3 p)
  <= wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
       0 (Z.to_nat elems).
Hypothesis Hov : ov = 2 * v.
Hypothesis Hv1 : 1 <= v.
Hypothesis HKrng : 0 <= K < 2 ^ 15.
Hypothesis Hzk : zksum 15 blc1 = 2 ^ 15 + v.
Hypothesis HvK : v <= blc1 15.
Hypothesis Hz1 : forall b, b < 1 \/ 15 < b -> blc1 b = 0.
Hypothesis Hbnd : forall b, 0 <= blc1 b <= K - 2 * v.
Hypothesis Eblc2 : blc2 = gb_adjust (Z.to_nat ov + 1) 15 blc1 ov.
Hypothesis Ep2 : gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                   hp3 maxc1 t2 blc2 15 (blc2 15) HEAP_SIZE ol1
                 = (t3, ol2).

(** ** the window instantiation *)

Definition zw_lo : Z := hmaxf + 1.
Definition zw_n : nat := Z.to_nat (HEAP_SIZE - (hmaxf + 1)).
Definition zw_leafb (p : Z) : bool := hp3 p <=? maxc1.
Definition zw_F (p : Z) : Z := t_freq tE (hp3 p).

Lemma zw_hi : zw_lo + Z.of_nat zw_n = HEAP_SIZE.
Proof.
  unfold zw_lo, zw_n.
  pose proof (zc_hmaxf_ub elems maxc1 tE tL hp3 hmaxf ndf Hpk). lia.
Qed.

Lemma zw_Fnn : forall p, zw_lo <= p < zw_lo + Z.of_nat zw_n ->
  zw_leafb p = true -> 0 <= zw_F p.
Proof.
  intros p Hp Hl. unfold zw_F.
  rewrite zw_hi in Hp. unfold zw_lo in Hp.
  unfold zw_leafb in Hl. apply Z.leb_le in Hl.
  destruct (zc_class elems maxc1 tE tL hp3 hmaxf ndf Hpk p ltac:(lia))
    as [Hr|Hr]; [|lia].
  apply Hfnn. lia.
Qed.

Lemma zw_Fmono : forall p q, zw_lo <= p -> p <= q ->
  q < zw_lo + Z.of_nat zw_n ->
  zw_leafb p = true -> zw_leafb q = true -> zw_F q <= zw_F p.
Proof.
  intros p q Hp Hpq Hq Hlp Hlq. unfold zw_F.
  rewrite zw_hi in Hq. unfold zw_lo in Hp.
  unfold zw_leafb in Hlp, Hlq.
  apply Z.leb_le in Hlp. apply Z.leb_le in Hlq.
  apply HW1; lia.
Qed.

(** ** masked symbol sums are leaf-window sums *)

Lemma zw_mask : forall (X : Z -> Z),
  wsum (fun s => ind (live_b tE maxc1 s) * X s) 0 (Z.to_nat elems)
  = wsum (fun p => ind (zw_leafb p) * X (hp3 p)) zw_lo zw_n.
Proof.
  intro X.
  pose proof (zc_hmaxf_ub elems maxc1 tE tL hp3 hmaxf ndf Hpk) as Hub.
  (* RHS: expand each leaf term over the value spike *)
  rewrite (wsum_ext (fun p => ind (zw_leafb p) * X (hp3 p))
             (fun p => wsum (fun s => ind ((hp3 p =? s)
                                           && zw_leafb p) * X s)
                         0 (Z.to_nat elems))
             zw_lo zw_n).
  2:{ intros p Hp.
      rewrite zw_hi in Hp. unfold zw_lo in Hp.
      destruct (zw_leafb p) eqn:El.
      - unfold zw_leafb in El. apply Z.leb_le in El.
        destruct (zc_class elems maxc1 tE tL hp3 hmaxf ndf Hpk p
                    ltac:(lia)) as [Hr|Hr]; [|lia].
        rewrite (wsum_ext (fun s => ind ((hp3 p =? s) && true) * X s)
                   (fun s => ind (hp3 p =? s) * X (hp3 p))
                   0 (Z.to_nat elems)).
        2:{ intros s Hs. rewrite andb_true_r.
            destruct (Z.eqb_spec (hp3 p) s) as [->|Hne];
              cbn [ind]; lia. }
        rewrite (za_wsum_const_ind (fun s => hp3 p =? s) (X (hp3 p))
                   0 (Z.to_nat elems)).
        assert (Hpc1 : wsum (fun s => ind (hp3 p =? s)) 0 (Z.to_nat elems)
                       = 1).
        { rewrite (wsum_ext (fun s => ind (hp3 p =? s))
                     (fun s => if Z.eq_dec s (hp3 p) then 1 else 0)
                     0 (Z.to_nat elems)).
          2:{ intros s _.
              destruct (Z.eqb_spec (hp3 p) s) as [->|Hne]; cbn [ind].
              - destruct (Z.eq_dec s s); [reflexivity|congruence].
              - destruct (Z.eq_dec s (hp3 p)); [congruence|reflexivity]. }
          rewrite zct_wsum_spike.
          replace ((0 <=? hp3 p)
                   && (hp3 p <? 0 + Z.of_nat (Z.to_nat elems))) with true
            by (symmetry; apply andb_true_iff;
                split; [apply Z.leb_le; lia
                       |apply Z.ltb_lt; rewrite Z2Nat.id; lia]).
          reflexivity. }
        rewrite Hpc1. cbn [ind]. ring.
      - rewrite (wsum_ext (fun s => ind ((hp3 p =? s) && false) * X s)
                   (fun _ => 0) 0 (Z.to_nat elems))
          by (intros; rewrite andb_false_r; cbn [ind]; lia).
        rewrite zct_wsum_zero. cbn [ind]. ring. }
  rewrite (za_wsum_swap (fun p s => ind ((hp3 p =? s) && zw_leafb p) * X s)
             zw_lo zw_n 0 (Z.to_nat elems)).
  apply wsum_ext. intros s Hs.
  rewrite Z2Nat.id in Hs by lia.
  (* per symbol: the leaf-window count of s is ind (live s) *)
  assert (Hcnt : wsum (fun p => ind ((hp3 p =? s) && zw_leafb p)) zw_lo zw_n
                 = ind (live_b tE maxc1 s)).
  { pose proof (bp_cnt _ _ _ _ _ _ _ Hpk s) as Hc.
    replace ((elems <=? s) && (s <? ndf)) with false in Hc
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    cbn [ind] in Hc.
    rewrite Z.add_0_r in Hc.
    rewrite <- Hc.
    unfold pcount, wcount.
    replace (Z.to_nat (HEAP_SIZE - hmaxf)) with (S zw_n)
      by (unfold zw_n; lia).
    rewrite zct_wsum_S. cbv beta.
    rewrite (zc_root elems maxc1 tE tL hp3 hmaxf ndf Hpk).
    pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hndf.
    replace (ndf - 1 =? s) with false
      by (symmetry; apply Z.eqb_neq; lia).
    cbn [ind]. rewrite Z.add_0_l.
    replace (hmaxf + 1) with zw_lo by reflexivity.
    apply wsum_ext. intros p Hp.
    rewrite zw_hi in Hp.
    destruct (Z.eqb_spec (hp3 p) s) as [Ee|Hne]; cbn [andb];
      [|reflexivity].
    unfold zw_leafb. rewrite Ee.
    destruct (live_b tE maxc1 s) eqn:El.
    - pose proof El as El'.
      unfold live_b in El'.
      apply andb_prop in El' as [El1 _].
      apply andb_prop in El1 as [_ El2].
      rewrite El2. reflexivity.
    - exfalso.
      pose proof (pcount_member hp3 hmaxf p
                    ltac:(unfold zw_lo in Hp; lia)) as Hm.
      rewrite Ee in Hm. rewrite Hc in Hm.
      cbn [ind] in Hm. lia. }
  rewrite (za_wsum_const_ind (fun p => (hp3 p =? s) && zw_leafb p)
             (X s) zw_lo zw_n).
  rewrite Hcnt.
  destruct (live_b tE maxc1 s); cbn [ind]; ring.
Qed.

(** ** fibZ positivity *)

Lemma zha_fib_pos : forall n, (1 <= n)%nat -> 1 <= fibZ n.
Proof.
  intros n Hn.
  induction n as [|n IH]; [lia|].
  destruct n as [|n]; [cbn; lia|].
  rewrite fibZ_SS. pose proof (fibZ_nonneg n).
  assert (1 <= fibZ (S n)) by (apply IH; lia). lia.
Qed.

(** ** bsumr is a wsum *)

Lemma zha_bsumr_wsum : forall (x : zarr) (k : nat) (b : Z),
  BtPass2.bsumr x k b = wsum x b k.
Proof.
  intros x k; induction k as [|k IH]; intro b; [reflexivity|].
  cbn [BtPass2.bsumr]. rewrite zct_wsum_S. rewrite IH. reflexivity.
Qed.

(** ** the adjusted histogram: nonneg, zeros, conservation, iter form *)

Lemma zw_adjust_pack :
  (forall b, 0 <= blc2 b)
  /\ (forall b, b < 1 \/ 15 < b -> blc2 b = blc1 b)
  /\ wsum blc2 1 (Z.to_nat 15) = wsum blc1 1 (Z.to_nat 15)
  /\ blc2 = zd_iter (Z.to_nat v) blc1.
Proof.
  assert (Hfuel : 1 <= v <= Z.of_nat (Z.to_nat ov + 1))
    by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; cbn [Z.of_nat]; lia).
  destruct (adjust_chain (Z.to_nat ov + 1) 15 K blc1 v
              ltac:(lia) HKrng Hfuel Hzk HvK Hz1 Hbnd)
    as (_ & _ & Hnn & Hzo & Hcons).
  assert (Eov : 2 * v = ov) by lia.
  rewrite Eov in Hnn, Hzo, Hcons.
  assert (Eit : blc2 = zd_iter (Z.to_nat v) blc1).
  { rewrite Eblc2.
    rewrite <- (zha_adjust_iter (Z.to_nat v) (Z.to_nat ov + 1) blc1
                  ltac:(lia) ltac:(lia)).
    f_equal. lia. }
  split; [intro b; rewrite Eblc2; apply Hnn|].
  split; [intros b Hb; rewrite Eblc2; apply Hzo; exact Hb|].
  split; [rewrite Eblc2; exact Hcons|].
  exact Eit.
Qed.

(** ** pass 2's order package *)

Lemma zw_pass2_pack :
  (forall b, 1 <= b <= 15 ->
     wsum (fun p => ind ((hp3 p <=? maxc1)
                         && (Z.eqb (t_len t3 (hp3 p)) b))) zw_lo zw_n
     = blc2 b)
  /\ (forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
        hp3 p <= maxc1 -> hp3 q <= maxc1 ->
        t_len t3 (hp3 p) <= t_len t3 (hp3 q))
  /\ (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
        1 <= t_len t3 (hp3 p) <= 15).
Proof.
  destruct zw_adjust_pack as (Hnn2 & _ & Hcons & _).
  assert (Htot : BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1)
                   (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
                 = BtPass2.bsumr blc2 (Z.to_nat 15) 1).
  { unfold BtPass2.lcnt.
    rewrite zha_bsumr_wsum.
    rewrite <- (zc_hist_total elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                  Hpk Hp1rng Hblc).
    change (Z.to_nat 15) with 15%nat in Hcons |- *.
    change (wsum (fun b => blc1 b) 1 15) with (wsum blc1 1 15).
    lia. }
  destruct (zho_pass2_order elems maxc1 15 tE tL hp3 hmaxf ndf
              Hpk ltac:(lia) Hmf0 t2 blc2 Hp1rng Hnn2 Htot
              ol1 t3 ol2 Ep2) as (Hh & Hor & Hrg & _ & _).
  split; [|split].
  - intros b Hb.
    rewrite <- (Hh b Hb). unfold BtPass2.hist. reflexivity.
  - exact Hor.
  - intros p Hp Hl. exact (Hrg p Hp Hl).
Qed.

(** ** counts against a per-level histogram are cge suffix sums *)

Lemma zw_count_cge : forall (L : Z -> Z) (x : zarr),
  (forall p, zw_lo <= p < HEAP_SIZE -> zw_leafb p = true ->
     1 <= L p <= 15) ->
  (forall b, 1 <= b <= 15 ->
     x b = wsum (fun p => ind (zw_leafb p && (Z.eqb (L p) b)))
             zw_lo zw_n) ->
  forall j, 1 <= j <= 15 ->
  wsum (fun p => ind (zw_leafb p && (j <=? L p))) zw_lo zw_n = cge x j.
Proof.
  intros L x Hrng Hhist j Hj.
  unfold cge.
  rewrite (wsum_ext x
             (fun b => wsum (fun p => ind (zw_leafb p && (Z.eqb (L p) b)))
                         zw_lo zw_n)
             j (Z.to_nat (16 - j))).
  2:{ intros b Hb. apply Hhist.
      rewrite Z2Nat.id in Hb by lia. lia. }
  rewrite (za_wsum_swap
             (fun b p => ind (zw_leafb p && (Z.eqb (L p) b)))
             j (Z.to_nat (16 - j)) zw_lo zw_n).
  apply wsum_ext. intros p Hp.
  rewrite zw_hi in Hp.
  destruct (zw_leafb p) eqn:El; cbn [andb].
  2:{ rewrite (wsum_ext (fun b => ind false) (fun _ => 0)
                 j (Z.to_nat (16 - j))) by (intros; reflexivity).
      rewrite zct_wsum_zero. reflexivity. }
  pose proof (Hrng p ltac:(lia) El) as HL.
  rewrite (wsum_ext (fun b => ind (Z.eqb (L p) b))
             (fun b => if Z.eq_dec b (L p) then 1 else 0)
             j (Z.to_nat (16 - j))).
  2:{ intros b _.
      destruct (Z.eqb_spec (L p) b) as [->|Hne]; cbn [ind].
      - destruct (Z.eq_dec b b); [reflexivity|congruence].
      - destruct (Z.eq_dec b (L p)); [congruence|reflexivity]. }
  rewrite zct_wsum_spike.
  rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec j (L p)) as [Hle|Hgt].
  - replace (L p <? j + (16 - j)) with true
      by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - reflexivity.
Qed.

(** ** cge bounds *)

Lemma zw_cge_nn : forall (x : zarr), (forall b, 0 <= x b) ->
  forall j, 0 <= cge x j.
Proof.
  intros x Hx j. unfold cge. apply wsum_nonneg. intros; apply Hx.
Qed.

Lemma zw_cge_le_total : forall (x : zarr), (forall b, 0 <= x b) ->
  forall j, 1 <= j <= 15 ->
  cge x j <= wsum x 1 15.
Proof.
  intros x Hx j Hj.
  unfold cge.
  rewrite (za_wsum_split x 1 (Z.to_nat (j - 1)) 15 ltac:(lia)).
  replace (1 + Z.of_nat (Z.to_nat (j - 1))) with j by lia.
  replace (15 - Z.to_nat (j - 1))%nat with (Z.to_nat (16 - j)) by lia.
  assert (0 <= wsum x 1 (Z.to_nat (j - 1)));
    [apply wsum_nonneg; intros; apply Hx|lia].
Qed.

(** ** the entry histogram total is the leaf census NL *)

Lemma zw_NL_total :
  za_NL zw_lo zw_n zw_leafb = wsum blc1 1 15.
Proof.
  unfold za_NL, za_rr.
  replace (Z.to_nat (zw_lo + Z.of_nat zw_n - zw_lo)) with zw_n by lia.
  change (wsum blc1 1 15) with (wsum (fun b => blc1 b) 1 15).
  rewrite (zc_hist_total elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
             Hpk Hp1rng Hblc).
  reflexivity.
Qed.

(** ** the cost bridge: masked cost delta <= layer delta *)

Definition zw_Sf : Z -> Z := za_Sx zw_lo zw_n zw_leafb zw_F.
Definition zw_L2 (p : Z) : Z := t_len t2 (hp3 p).
Definition zw_L3 (p : Z) : Z := t_len t3 (hp3 p).
Definition zw_CAPF (lv : Z) : Z := 16384 / fibZ (Z.to_nat lv + 1).

Lemma zw_NL_facts :
  cge blc1 1 <= za_NL zw_lo zw_n zw_leafb
  /\ za_NL zw_lo zw_n zw_leafb <= elems
  /\ (forall j, 1 <= j <= 15 -> cge blc1 j <= za_NL zw_lo zw_n zw_leafb)
  /\ (forall j, 1 <= j <= 15 -> cge blc2 j <= za_NL zw_lo zw_n zw_leafb).
Proof.
  destruct zw_adjust_pack as (Hnn2 & _ & Hcons & _).
  pose proof zw_NL_total as HT.
  assert (Hle : za_NL zw_lo zw_n zw_leafb <= elems).
  { rewrite HT.
    change (wsum blc1 1 15) with (wsum (fun b => blc1 b) 1 15).
    rewrite (zc_hist_total elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
               Hpk Hp1rng Hblc).
    exact (zc_leafcount_le elems maxc1 tE tL hp3 hmaxf ndf Hpk Hel Hmc). }
  assert (H1 : forall j, 1 <= j <= 15 ->
            cge blc1 j <= za_NL zw_lo zw_n zw_leafb).
  { intros j Hj. rewrite HT.
    apply zw_cge_le_total; [intro b; pose proof (Hbnd b); lia|exact Hj]. }
  assert (H2 : forall j, 1 <= j <= 15 ->
            cge blc2 j <= za_NL zw_lo zw_n zw_leafb).
  { intros j Hj. rewrite HT.
    change (Z.to_nat 15) with 15%nat in Hcons.
    rewrite <- Hcons.
    apply zw_cge_le_total; [exact Hnn2|exact Hj]. }
  split; [apply H1; lia|].
  split; [exact Hle|].
  split; [exact H1|exact H2].
Qed.

Lemma zw_cost_bridge :
  wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s * t_len t3 s)
    0 (Z.to_nat elems)
  - wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s * t_len t2 s)
    0 (Z.to_nat elems)
  <= layer zw_Sf blc2 - layer zw_Sf blc1.
Proof.
  destruct zw_pass2_pack as (Hh3 & Hor3 & Hrg3).
  destruct zw_NL_facts as (_ & _ & Hc1NL & Hc2NL).
  (* range facts for both length profiles *)
  assert (HL3rng : forall p, zw_lo <= p < zw_lo + Z.of_nat zw_n ->
            zw_leafb p = true -> 0 <= zw_L3 p <= 15).
  { intros p Hp Hl. unfold zw_L3.
    rewrite zw_hi in Hp.
    unfold zw_leafb in Hl. apply Z.leb_le in Hl.
    pose proof (Hrg3 p ltac:(unfold zw_lo in Hp; lia) Hl). lia. }
  assert (HL2rng : forall p, zw_lo <= p < zw_lo + Z.of_nat zw_n ->
            zw_leafb p = true -> 0 <= zw_L2 p <= 15).
  { intros p Hp Hl. unfold zw_L2.
    rewrite zw_hi in Hp.
    pose proof (Hp1rng p ltac:(unfold zw_lo in Hp; lia)). lia. }
  assert (HL3mono : forall p q, zw_lo <= p -> p <= q ->
            q < zw_lo + Z.of_nat zw_n ->
            zw_leafb p = true -> zw_leafb q = true -> zw_L3 p <= zw_L3 q).
  { intros p q Hp Hpq Hq Hlp Hlq. unfold zw_L3.
    rewrite zw_hi in Hq.
    unfold zw_leafb in Hlp, Hlq.
    apply Z.leb_le in Hlp. apply Z.leb_le in Hlq.
    apply Hor3; try lia; assumption. }
  (* to window form *)
  assert (E3 : wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s
                              * t_len t3 s) 0 (Z.to_nat elems)
               = wsum (fun p => ind (zw_leafb p) * zw_F p * zw_L3 p)
                   zw_lo zw_n).
  { rewrite (wsum_ext
               (fun s => ind (live_b tE maxc1 s) * t_freq tE s
                         * t_len t3 s)
               (fun s => ind (live_b tE maxc1 s)
                         * (t_freq tE s * t_len t3 s))
               0 (Z.to_nat elems)) by (intros; ring).
    rewrite (zw_mask (fun s => t_freq tE s * t_len t3 s)).
    apply wsum_ext. intros p _. unfold zw_F, zw_L3. ring. }
  assert (E2 : wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s
                              * t_len t2 s) 0 (Z.to_nat elems)
               = wsum (fun p => ind (zw_leafb p) * zw_F p * zw_L2 p)
                   zw_lo zw_n).
  { rewrite (wsum_ext
               (fun s => ind (live_b tE maxc1 s) * t_freq tE s
                         * t_len t2 s)
               (fun s => ind (live_b tE maxc1 s)
                         * (t_freq tE s * t_len t2 s))
               0 (Z.to_nat elems)) by (intros; ring).
    rewrite (zw_mask (fun s => t_freq tE s * t_len t2 s)).
    apply wsum_ext. intros p _. unfold zw_F, zw_L2. ring. }
  rewrite E3, E2.
  rewrite (za_fubini zw_lo zw_n zw_leafb zw_F zw_L3 HL3rng).
  rewrite (za_fubini zw_lo zw_n zw_leafb zw_F zw_L2 HL2rng).
  (* per-level histograms in the window vocabulary *)
  assert (Hh3' : forall b, 1 <= b <= 15 ->
            blc2 b = wsum (fun p => ind (zw_leafb p && (Z.eqb (zw_L3 p) b)))
                       zw_lo zw_n).
  { intros b Hb. symmetry. exact (Hh3 b Hb). }
  assert (Hh2' : forall b, 1 <= b <= 15 ->
            blc1 b = wsum (fun p => ind (zw_leafb p && (Z.eqb (zw_L2 p) b)))
                       zw_lo zw_n).
  { intros b Hb. exact (Hblc b ltac:(lia)). }
  assert (HL3rng' : forall p, zw_lo <= p < HEAP_SIZE ->
            zw_leafb p = true -> 1 <= zw_L3 p <= 15).
  { intros p Hp Hl. unfold zw_L3.
    unfold zw_leafb in Hl. apply Z.leb_le in Hl.
    pose proof (Hrg3 p ltac:(unfold zw_lo in Hp; lia) Hl). lia. }
  assert (HL2rng' : forall p, zw_lo <= p < HEAP_SIZE ->
            zw_leafb p = true -> 1 <= zw_L2 p <= 15).
  { intros p Hp Hl. unfold zw_L2.
    pose proof (Hp1rng p ltac:(unfold zw_lo in Hp; lia)). lia. }
  (* level sums, both directions *)
  assert (H3eq : wsum (fun j => wsum (fun p => ind (zw_leafb p
                                                    && (j <=? zw_L3 p))
                                               * zw_F p) zw_lo zw_n) 1 15
                 = wsum (fun j => zw_Sf (cge blc2 j)) 1 15).
  { apply wsum_ext. intros j Hj.
    cbn [Z.of_nat] in Hj.
    rewrite (za_T3_eq zw_lo zw_n zw_leafb zw_F zw_L3 HL3mono j).
    rewrite (zw_count_cge zw_L3 blc2 HL3rng' Hh3' j ltac:(lia)).
    unfold zw_Sf.
    rewrite (za_Sx_in zw_lo zw_n zw_leafb zw_F (cge blc2 j)
               (Hc2NL j ltac:(lia))).
    reflexivity. }
  assert (H2ge : wsum (fun j => zw_Sf (cge blc1 j)) 1 15
                 <= wsum (fun j => wsum (fun p => ind (zw_leafb p
                                                       && (j <=? zw_L2 p))
                                                  * zw_F p) zw_lo zw_n)
                      1 15).
  { apply wsum_le. intros j Hj.
    cbn [Z.of_nat] in Hj.
    unfold zw_Sf.
    rewrite (za_Sx_in zw_lo zw_n zw_leafb zw_F (cge blc1 j)
               (Hc1NL j ltac:(lia))).
    rewrite <- (zw_count_cge zw_L2 blc1 HL2rng' Hh2' j ltac:(lia)).
    apply (za_T2_ge zw_lo zw_n zw_leafb zw_F zw_Fnn zw_Fmono zw_L2 j). }
  unfold layer.
  lia.
Qed.

(** ** the walk, instantiated at the entry histogram *)

Lemma zw_walk_pack :
  exists (peels : list Z) (m : nat) (ltr TR : Z) (blcT : zarr),
    (forall lv, In lv peels -> 1 <= lv <= 14)
    /\ zd_sumC peels + Z.of_nat m = v
    /\ layer zw_Sf blc2
       <= layer zw_Sf blc1 + zd_sumP zw_CAPF peels + TR
    /\ 0 <= TR
    /\ ((m = O /\ TR = 0)
        \/ (1 <= ltr <= 14
            /\ 1 <= Z.of_nat m <= 2 ^ (15 - ltr) - 1
            /\ TR <= (15 - ltr) * zw_CAPF ltr
            /\ (Z.of_nat m <= 2 ^ (14 - ltr) -> TR <= zw_CAPF ltr)
            /\ blcT 15 = blc1 15 + Z.of_nat (length peels)
            /\ zksum 15 blcT = 2 ^ 15 + Z.of_nat m
            /\ (forall j, 1 <= j < ltr -> blcT j = blc1 j)
            /\ (forall j, ltr < j <= 14 -> blcT j = 0)
            /\ (forall b, b < 1 \/ 15 < b -> blcT b = 0)
            /\ 1 <= blcT ltr <= blc1 ltr
            /\ wsum blcT 1 15 = wsum blc1 1 15)).
Proof.
  destruct zw_adjust_pack as (Hnn2 & _ & _ & Eit).
  assert (Hpnn : forall r, 0 <= phi zw_Sf r).
  { intro r. unfold phi, zw_Sf.
    exact (za_phix_nn zw_lo zw_n zw_leafb zw_F zw_Fnn r). }
  assert (Hpmono : forall a b, a <= b -> phi zw_Sf a <= phi zw_Sf b).
  { intros a b Hab. unfold phi, zw_Sf.
    exact (za_phix_mono zw_lo zw_n zw_leafb zw_F zw_Fnn zw_Fmono
             a b Hab). }
  assert (Hcap : forall lv r, 1 <= lv <= 14 -> 1 <= r <= cge blc1 lv ->
            phi zw_Sf r <= zw_CAPF lv).
  { intros lv r Hlv Hr.
    destruct zw_NL_facts as (_ & _ & Hc1NL & _).
    assert (HrNL : r <= za_NL zw_lo zw_n zw_leafb)
      by (pose proof (Hc1NL lv ltac:(lia)); lia).
    assert (Ephi : phi zw_Sf r = za_phi zw_lo zw_n zw_leafb zw_F r).
    { unfold phi, zw_Sf, za_phi.
      rewrite (za_Sx_in zw_lo zw_n zw_leafb zw_F r) by lia.
      rewrite (za_Sx_in zw_lo zw_n zw_leafb zw_F (r - 1)) by lia.
      reflexivity. }
    rewrite Ephi.
    assert (Hcnt : cge blc1 lv
                   = wsum (fun p => ind (zw_leafb p && (lv <=? zw_L2 p)))
                       zw_lo zw_n).
    { symmetry. apply (zw_count_cge zw_L2 blc1); [| |lia].
      - intros p Hp Hl. unfold zw_L2.
        pose proof (Hp1rng p ltac:(unfold zw_lo in Hp; lia)). lia.
      - intros b Hb. exact (Hblc b ltac:(lia)). }
    apply (za_cap zw_lo zw_n zw_leafb zw_F zw_Fmono zw_L2 zw_CAPF lv r);
      [|lia|rewrite <- Hcnt; lia].
    intros p Hp Hl HlvL.
    unfold zw_F, zw_CAPF.
    rewrite zw_hi in Hp.
    unfold zw_leafb in Hl. apply Z.leb_le in Hl.
    pose proof (HW2 p ltac:(unfold zw_lo in Hp; lia) Hl) as HF.
    assert (Hmono : fibZ (Z.to_nat lv + 1)
                    <= fibZ (Z.to_nat (zw_L2 p) + 1))
      by (apply zha_fib_mono; unfold zw_L2 in *; lia).
    assert (Hpos : 1 <= fibZ (Z.to_nat lv + 1))
      by (apply zha_fib_pos; lia).
    assert (HFp : 0 <= t_freq tE (hp3 p)).
    { destruct (zc_class elems maxc1 tE tL hp3 hmaxf ndf Hpk p
                  ltac:(unfold zw_lo in Hp; lia)) as [Hr'|Hr']; [|lia].
      apply Hfnn; lia. }
    apply Z.div_le_lower_bound; [lia|].
    unfold zw_L2 in Hmono, HlvL. nia. }
  assert (Hcapnn : forall lv, 1 <= lv <= 14 -> 0 <= zw_CAPF lv).
  { intros lv Hlv. unfold zw_CAPF.
    apply Z.div_pos; [lia|].
    pose proof (zha_fib_pos (Z.to_nat lv + 1) ltac:(lia)). lia. }
  assert (HvE : v <= elems).
  { pose proof (zc_blc_ub elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                  Hpk Hel Hmc Hp1rng Hblc 15 ltac:(lia)). lia. }
  assert (Hbnd' : forall b, 0 <= blc1 b <= 32764 - Z.of_nat (Z.to_nat v)).
  { intro b. rewrite Z2Nat.id by lia.
    unfold L_CODES in *.
    destruct (Z_lt_le_dec b 1) as [Hb|Hb];
      [rewrite (Hz1 b ltac:(lia)); lia|].
    destruct (Z_lt_le_dec 15 b) as [Hb2|Hb2];
      [rewrite (Hz1 b ltac:(lia)); lia|].
    pose proof (zc_blc_ub elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                  Hpk Hel Hmc Hp1rng Hblc b ltac:(lia)).
    pose proof (Hbnd b).
    lia. }
  assert (Hstock' : Z.of_nat (Z.to_nat v) <= blc1 15)
    by (rewrite Z2Nat.id by lia; exact HvK).
  assert (Hzk' : zksum 15 blc1 = 2 ^ 15 + Z.of_nat (Z.to_nat v))
    by (rewrite Z2Nat.id by lia; exact Hzk).
  assert (HL' : (0 < Z.to_nat v)%nat -> gba_bits 15 blc1 <= 14).
  { intros _. unfold gba_bits.
    pose proof (zct_findbits_le (Z.to_nat MAX_BITS + 1) blc1 (15 - 1)).
    lia. }
  assert (Hinv' : forall j, 1 <= j -> (0 < Z.to_nat v)%nat ->
            j <= gba_bits 15 blc1 ->
            blc1 15 + wsum blc1 j (Z.to_nat (15 - j)) <= cge blc1 j).
  { intros j Hj1 Hv0 Hjle.
    pose proof (HL' Hv0) as H14.
    unfold cge.
    replace (Z.to_nat (16 - j)) with (S (Z.to_nat (15 - j))) by lia.
    rewrite wsum_split_last.
    replace (j + Z.of_nat (Z.to_nat (15 - j))) with 15 by lia.
    lia. }
  destruct (zd_walk zw_Sf Hpnn Hpmono (cge blc1) zw_CAPF Hcap Hcapnn
              (Z.to_nat v) (Z.to_nat v) 14 blc1
              ltac:(lia) Hz1 Hbnd' Hstock' Hzk' HL' Hinv')
    as (peels & m & ltr & TR & blcT
        & Hprng & HsC & Hlay & Htnn & Hpkg).
  exists peels, m, ltr, TR, blcT.
  rewrite Z2Nat.id in HsC by lia.
  rewrite <- Eit in Hlay.
  split; [intros lv Hin; exact (proj1 (Hprng lv Hin))|].
  split; [exact HsC|].
  split; [exact Hlay|].
  split; [exact Htnn|].
  destruct Hpkg as [Hl|Hr]; [left; exact Hl|right].
  destruct Hr as (H1 & HL14 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9
                  & H10 & H11).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7
          (conj H8 (conj H9 (conj H10 H11)))))))))).
Qed.

Lemma zw_sum_ratio : forall peels,
  (forall lv, In lv peels -> 1 <= lv <= 14) ->
  15 * zd_sumP zw_CAPF peels <= 452 * zd_sumC peels
  /\ 0 <= zd_sumC peels.
Proof.
  induction peels as [|lv ps IH]; intro Hrng.
  - rewrite (zd_sumP_nil zw_CAPF), zd_sumC_nil. lia.
  - rewrite (zd_sumP_cons zw_CAPF lv ps), (zd_sumC_cons lv ps).
    assert (Hlv : 1 <= lv <= 14) by (apply Hrng; left; reflexivity).
    destruct (IH ltac:(intros lv' Hin'; apply Hrng; right; exact Hin'))
      as (IH1 & IH2).
    assert (Hhead : 15 * ((15 - lv) * zw_CAPF lv)
                    <= 452 * (2 ^ (15 - lv) - 1)
                    /\ 0 <= 2 ^ (15 - lv) - 1).
    { unfold zw_CAPF.
      assert (Hc : lv = 1 \/ lv = 2 \/ lv = 3 \/ lv = 4 \/ lv = 5
                   \/ lv = 6 \/ lv = 7 \/ lv = 8 \/ lv = 9 \/ lv = 10
                   \/ lv = 11 \/ lv = 12 \/ lv = 13 \/ lv = 14) by lia.
      destruct Hc as
        [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]];
        split; reflexivity || (vm_compute; intro Hd; discriminate Hd). }
    lia.
Qed.

(** ** the certificate *)

Lemma zw_core :
  exists (SP SC TRv mz ltr : Z),
    wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s * t_len t3 s)
      0 (Z.to_nat elems)
    <= wsum (fun s => ind (live_b tE maxc1 s) * t_freq tE s * t_len t2 s)
         0 (Z.to_nat elems) + SP + TRv
    /\ 0 <= TRv /\ 0 <= SC /\ 15 * SP <= 452 * SC
    /\ SC + mz = v /\ 0 <= mz /\ v <= elems
    /\ (mz = 0 /\ TRv = 0
        \/ (7 <= ltr <= 14
            /\ 1 <= mz <= 2 ^ (15 - ltr) - 1
            /\ v <= elems - 1
            /\ TRv <= (15 - ltr) * zw_CAPF ltr
            /\ (mz <= 2 ^ (14 - ltr) -> TRv <= zw_CAPF ltr))).
Proof.
  destruct zw_walk_pack
    as (peels & m & ltr & TR & blcT
        & Hprng & HsC & Hlay & Htnn & Hpkg).
  pose proof zw_cost_bridge as HB.
  destruct (zw_sum_ratio peels Hprng) as (Hratio & HSCnn).
  assert (HvE : v <= elems).
  { pose proof (zc_blc_ub elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                  Hpk Hel Hmc Hp1rng Hblc 15 ltac:(lia)). lia. }
  destruct Hpkg as [[Hm0 HTR0]|Htail].
  - exists (zd_sumP zw_CAPF peels), (zd_sumC peels), TR, 0, 0.
    subst m. cbn [Z.of_nat] in HsC.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [exact Hratio|].
    split; [lia|].
    split; [lia|].
    split; [exact HvE|].
    left. split; [reflexivity|exact HTR0].
  - destruct Htail as (Hltr & Hm1 & Htrb & Htrs & HT15 & HTzk & HTlow
                       & HThigh & HTz & HTl & HTcons).
    set (P := Z.of_nat (length peels)).
    assert (HPnn : 0 <= P) by (unfold P; lia).
    (* count: blc1 15 + P <= elems - 1, from conservation *)
    assert (HTnnpt : forall j, 1 <= j <= 14 -> 0 <= blcT j).
    { intros j Hj.
      destruct (Z_lt_le_dec j ltr) as [Hjl|Hjl].
      - rewrite (HTlow j ltac:(lia)). pose proof (Hbnd j). lia.
      - destruct (Z.eq_dec j ltr) as [->|Hne]; [lia|].
        rewrite (HThigh j ltac:(lia)). lia. }
    assert (HK0P : blc1 15 + P <= elems - 1).
    { assert (Esum : wsum blcT 1 15 = wsum blcT 1 14 + blcT 15).
      { replace 15%nat with (S 14%nat) by reflexivity.
        rewrite wsum_split_last.
        replace (1 + Z.of_nat 14) with 15 by (cbn [Z.of_nat]; lia).
        reflexivity. }
      assert (H14 : 1 <= wsum blcT 1 14).
      { rewrite (za_wsum_split blcT 1 (Z.to_nat (ltr - 1)) 14
                   ltac:(lia)).
        replace (1 + Z.of_nat (Z.to_nat (ltr - 1))) with ltr by lia.
        replace (14 - Z.to_nat (ltr - 1))%nat
          with (S (Z.to_nat (14 - ltr))) by lia.
        rewrite zct_wsum_S. cbv beta.
        assert (0 <= wsum blcT 1 (Z.to_nat (ltr - 1))).
        { apply wsum_nonneg. intros i Hi.
          rewrite Z2Nat.id in Hi by lia. apply HTnnpt. lia. }
        assert (0 <= wsum blcT (ltr + 1) (Z.to_nat (14 - ltr))).
        { apply wsum_nonneg. intros i Hi.
          rewrite Z2Nat.id in Hi by lia. apply HTnnpt. lia. }
        lia. }
      assert (HNLe : wsum blc1 1 15 <= elems).
      { destruct zw_NL_facts as (_ & HNL & _ & _).
        pose proof zw_NL_total as HT. lia. }
      lia. }
    (* the shallow-tail exclusion *)
    assert (Hl7 : 7 <= ltr).
    { destruct (Z.le_gt_cases 7 ltr) as [|Hlt]; [assumption|exfalso].
      pose proof (zc_telescope elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                    Hpk Hmc Hp1len Hp1root Hp1rng Hblc
                    (Z.to_nat (ltr - 1)) ltac:(lia)) as Htel.
      rewrite Z2Nat.id in Htel by lia.
      pose proof (zc_level elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                    Hpk Hmc Hp1len Hp1root Hp1rng Hblc ltr
                    ltac:(lia)) as Hlev.
      pose proof (zc_I_pos elems maxc1 tE tL t2 hp3 hmaxf ndf blc1
                    Hpk Hmc Hp1len Hp1root Hblc ltr ltac:(lia)
                    ltac:(lia)) as Hpos.
      rewrite zha_zksum_wsum in HTzk.
      assert (Esh : wsum (fun j => blcT j * 2 ^ (15 - j)) 1
                      (Z.to_nat (ltr - 1))
                    = wsum (fun j => blc1 j * 2 ^ (15 - j)) 1
                        (Z.to_nat (ltr - 1))).
      { apply wsum_ext. intros j Hj.
        rewrite Z2Nat.id in Hj by lia.
        rewrite (HTlow j ltac:(lia)). reflexivity. }
      assert (Esplit : wsum (fun j => blcT j * 2 ^ (15 - j)) 1 14
                       = wsum (fun j => blcT j * 2 ^ (15 - j)) 1
                           (Z.to_nat (ltr - 1))
                         + blcT ltr * 2 ^ (15 - ltr)
                         + wsum (fun j => blcT j * 2 ^ (15 - j))
                             (ltr + 1) (Z.to_nat (14 - ltr))).
      { rewrite (za_wsum_split (fun j => blcT j * 2 ^ (15 - j)) 1
                   (Z.to_nat (ltr - 1)) 14 ltac:(lia)).
        replace (1 + Z.of_nat (Z.to_nat (ltr - 1))) with ltr by lia.
        replace (14 - Z.to_nat (ltr - 1))%nat
          with (S (Z.to_nat (14 - ltr))) by lia.
        rewrite zct_wsum_S. cbv beta. lia. }
      assert (Ehigh : wsum (fun j => blcT j * 2 ^ (15 - j)) (ltr + 1)
                        (Z.to_nat (14 - ltr)) = 0).
      { rewrite (wsum_ext (fun j => blcT j * 2 ^ (15 - j)) (fun _ => 0)
                   (ltr + 1) (Z.to_nat (14 - ltr))).
        - apply zct_wsum_zero.
        - intros j Hj. rewrite Z2Nat.id in Hj by lia.
          rewrite (HThigh j ltac:(lia)). ring. }
      assert (E2G : 2 ^ (15 - (ltr - 1)) = 2 * 2 ^ (15 - ltr)).
      { replace (15 - (ltr - 1)) with (1 + (15 - ltr)) by lia.
        rewrite Z.pow_add_r by lia. lia. }
      assert (HG9 : 2 ^ 9 <= 2 ^ (15 - ltr))
        by (apply Z.pow_le_mono_r; lia).
      assert (HG9' : (2:Z) ^ 9 = 512) by reflexivity.
      (* bounds on both sides of the granularity equation *)
      assert (Hm285 : Z.of_nat m <= elems).
      { pose proof HSCnn. lia. }
      assert (Heq : (blcT ltr - 2 * zc_I maxc1 t2 hp3 hmaxf (ltr - 1))
                      * 2 ^ (15 - ltr)
                    = Z.of_nat m - blc1 15 - P).
      { rewrite Esplit, Esh, Ehigh in HTzk.
        rewrite Htel in HTzk.
        rewrite E2G in HTzk.
        rewrite HT15 in HTzk.
        unfold P. ring_simplify. ring_simplify in HTzk. lia. }
      assert (Hzero : blcT ltr - 2 * zc_I maxc1 t2 hp3 hmaxf (ltr - 1)
                      = 0).
      { assert (Habs : - (2 ^ (15 - ltr)) < Z.of_nat m - blc1 15 - P
                       /\ Z.of_nat m - blc1 15 - P < 2 ^ (15 - ltr)).
        { unfold L_CODES in *. lia. }
        nia. }
      lia. }
    exists (zd_sumP zw_CAPF peels), (zd_sumC peels), TR, (Z.of_nat m),
      ltr.
    split; [lia|].
    split; [exact Htnn|].
    split; [exact HSCnn|].
    split; [exact Hratio|].
    split; [exact HsC|].
    split; [lia|].
    split; [exact HvE|].
    right.
    split; [lia|].
    split; [exact Hm1|].
    split; [lia|].
    split; [exact Htrb|].
    exact Htrs.
Qed.

End ZHOAssembly.
