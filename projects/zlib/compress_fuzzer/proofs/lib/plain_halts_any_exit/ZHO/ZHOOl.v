(** * ZHOOl — the UNCONDITIONAL upper bound on the dynamic counter at the
      huffman dispatch state.

    OWNER: huffman-opt (scope item 1 of the Case-B closure).  What is
    landed (ZReproG6G.dispatch_counters) bounds the dynamic EMISSION by
    OL + 6 — the LOWER direction.  Case B needs the UPPER: the counter
    itself is at most the dynamic body cost plus the tree description,
    all at the BUILT trees.  This is the same three-build accounting
    (gen_bitlen's opt_len = sum freq*(len+xbits), BtAccount2 /
    ZReproG6E/F's build_tree_counters) plus ScanBase's two-scan count law,
    assembled in the other direction; the +6 slop absorbs any bl-side
    padding asymmetry (the consumer's certificate has thousands of bits
    of room).

    Abbreviation: [S2P ts] is the dispatch state.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin CbEmit CbFold
  SendItems SendGo ScanCount ScanBase HuffCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  ZReproG6A ZReproG6C ZReproG6D ZReproG6G.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Definition S2P (ts : TSt) : TSt :=
  snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))).

Definition S2M (ts : TSt) : Z :=
  fst (build_bl_tree (build_tree TK_D (build_tree TK_L ts))).

(** the bl-description wsum for tree kind [k], as dispatch_counters spells
    it *)
Definition zho_bldesc (ts : TSt) (k : Z) : Z :=
  wsum (fun sy =>
      hid_zcount sy
        (items_syms (send_tree_items (ts_trees (S2P ts) k)
                       (ts_maxcode (S2P ts) k)))
      * (t_len (ts_trees (S2P ts) TK_BL) sy + extra_blbits sy)) 0 19.

(* ==========================================================================
   Imports beyond the skeleton: the landed accounting/census/kit machinery.
   ========================================================================== *)

(* moved to the top in spirit; Rocq allows late Requires *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtCensus1 BtCensus2 BtCensus4 BtCensus5 BtAccount BtAccount2 BtItem6b BtExports
  BtSized BtTerm BtBlSide BuildTree Huff HuffGenCodes KraftAdjust
  SendGo.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproG6E ZReproG6F
  ZReproG6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* ==========================================================================
   1.  List/count glue for the forced-slot corner: a tree with at most two
       nonzero-frequency symbols gives every in-code symbol length <= 1
       (Kraft equality: 2^(M-1) + 2^(M-1) = 2^M forces both at level 1).
   ========================================================================== *)

(** count_occ of a value present at a position *)
Lemma zho_count_pos : forall (L : list nat) (v : nat),
  In v L -> (1 <= count_occ Nat.eq_dec L v)%nat.
Proof.
  intros L v Hin. apply count_occ_In. exact Hin.
Qed.

(** the level sum of counts is bounded by the number of positions holding
    a value in [1, hi]; with at most two nonzero positions, <= 2 *)
Fixpoint zho_lvlsum (L : list nat) (lo : nat) (n : nat) : nat :=
  match n with
  | O => O
  | S m => (count_occ Nat.eq_dec L lo + zho_lvlsum L (S lo) m)%nat
  end.

Lemma zho_lvlsum_cons : forall x L lo n,
  zho_lvlsum (x :: L) lo n
  = ((if (Nat.leb lo x && Nat.leb x (lo + n - 1) && Nat.ltb 0 n)%bool
      then 1 else 0)
     + zho_lvlsum L lo n)%nat.
Proof.
  intros x L lo n. revert lo.
  induction n as [|m IH]; intro lo; cbn [zho_lvlsum].
  - rewrite Bool.andb_false_r. reflexivity.
  - destruct (Nat.eq_dec lo x) as [->|Hne].
    + rewrite (count_occ_cons_eq Nat.eq_dec L (eq_refl x)).
      rewrite IH.
      replace ((Nat.leb x x && Nat.leb x (x + S m - 1) && Nat.ltb 0 (S m))%bool)
        with true
        by (symmetry; apply Bool.andb_true_iff; split;
            [apply Bool.andb_true_iff; split; apply Nat.leb_le; lia
            |apply Nat.ltb_lt; lia]).
      replace ((Nat.leb (S x) x && Nat.leb x (S x + m - 1) && Nat.ltb 0 m)%bool)
        with false
        by (symmetry; apply Bool.andb_false_iff; left;
            apply Bool.andb_false_iff; left; apply Nat.leb_gt; lia).
      lia.
    + rewrite (count_occ_cons_neq Nat.eq_dec L (not_eq_sym Hne)).
      rewrite IH.
      destruct ((Nat.leb (S lo) x && Nat.leb x (S lo + m - 1) && Nat.ltb 0 m)%bool) eqn:E1;
        destruct ((Nat.leb lo x && Nat.leb x (lo + S m - 1) && Nat.ltb 0 (S m))%bool) eqn:E2;
        try lia.
      * exfalso.
        apply Bool.andb_true_iff in E1 as [E1a E1c].
        apply Bool.andb_true_iff in E1a as [E1a E1b].
        apply Nat.leb_le in E1a. apply Nat.leb_le in E1b.
        apply Nat.ltb_lt in E1c.
        apply Bool.andb_false_iff in E2 as [E2|E2];
          [apply Bool.andb_false_iff in E2 as [E2|E2];
           apply Nat.leb_gt in E2 | apply Nat.ltb_ge in E2]; lia.
      * exfalso.
        apply Bool.andb_true_iff in E2 as [E2a E2c].
        apply Bool.andb_true_iff in E2a as [E2a E2b].
        apply Nat.leb_le in E2a. apply Nat.leb_le in E2b.
        apply Nat.ltb_lt in E2c.
        apply Bool.andb_false_iff in E1 as [E1|E1];
          [apply Bool.andb_false_iff in E1 as [E1|E1];
           apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E1]; lia.
Qed.

Lemma zho_lvlsum_nil : forall lo n, zho_lvlsum [] lo n = 0%nat.
Proof.
  intros lo n; revert lo; induction n as [|m IH]; intro lo;
    cbn [zho_lvlsum count_occ]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma zho_lvlsum_app : forall L1 L2 lo n,
  zho_lvlsum (L1 ++ L2) lo n = (zho_lvlsum L1 lo n + zho_lvlsum L2 lo n)%nat.
Proof.
  intros L1 L2 lo n; revert lo; induction n as [|m IH]; intro lo;
    cbn [zho_lvlsum]; [reflexivity|].
  rewrite IH, (count_occ_app Nat.eq_dec). lia.
Qed.

(** positions with nonzero value, bounded by a two-witness property *)
Lemma zho_nonzero_le2 : forall (f : Z -> nat) (n : nat) (w1 w2 : Z),
  (forall i, (i < n)%nat -> f (Z.of_nat i) <> 0%nat ->
     Z.of_nat i = w1 \/ Z.of_nat i = w2) ->
  (zho_lvlsum (map (fun i => f (Z.of_nat i)) (seq 0 n)) 1 15 <= 2)%nat.
Proof.
  intros f n w1 w2 Hw.
  pose (ivm := fun (w : Z) (m : nat) =>
                 if ((0 <=? w) && (w <? Z.of_nat m))%bool
                 then 1%nat else 0%nat).
  assert (Hiv01 : forall w m, (ivm w m <= 1)%nat).
  { intros w m. unfold ivm.
    destruct (((0 <=? w) && (w <? Z.of_nat m))%bool); lia. }
  assert (Hivmono : forall w m, (ivm w m <= ivm w (S m))%nat).
  { intros w m. unfold ivm.
    destruct (Z.leb_spec 0 w); destruct (Z.ltb_spec w (Z.of_nat m));
      destruct (Z.ltb_spec w (Z.of_nat (S m))); cbn [andb]; lia. }
  assert (Hivnew : forall w m, w = Z.of_nat m -> ivm w m = 0%nat /\ ivm w (S m) = 1%nat).
  { intros w m ->. unfold ivm. split.
    - replace ((0 <=? Z.of_nat m) && (Z.of_nat m <? Z.of_nat m))%bool with false;
        [reflexivity|].
      symmetry. apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
    - replace ((0 <=? Z.of_nat m) && (Z.of_nat m <? Z.of_nat (S m)))%bool with true;
        [reflexivity|].
      symmetry. apply Bool.andb_true_iff. split;
        [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  assert (MAIN : forall m, (m <= n)%nat ->
    (zho_lvlsum (map (fun i => f (Z.of_nat i)) (seq 0 m)) 1 15
     <= ivm w1 m + ivm w2 m)%nat).
  { induction m as [|m IH]; intro Hm.
    - cbn [seq map]. rewrite zho_lvlsum_nil. lia.
    - rewrite seq_S, map_app.
      rewrite zho_lvlsum_app.
      cbn [map].
      rewrite zho_lvlsum_cons, zho_lvlsum_nil.
      replace (0 + m)%nat with m by lia.
      specialize (IH ltac:(lia)).
      set (c := (if (Nat.leb 1 (f (Z.of_nat m))
                     && Nat.leb (f (Z.of_nat m)) (1 + 15 - 1)
                     && Nat.ltb 0 15)%bool then 1 else 0)%nat) in *.
      assert (Hc01 : (c <= 1)%nat).
      { unfold c.
        destruct ((Nat.leb 1 (f (Z.of_nat m))
                   && Nat.leb (f (Z.of_nat m)) (1 + 15 - 1)
                   && Nat.ltb 0 15)%bool); lia. }
      destruct (Nat.eq_dec c 0) as [Ec|Ec].
      + pose proof (Hivmono w1 m). pose proof (Hivmono w2 m). lia.
      + assert (Hfm : f (Z.of_nat m) <> 0%nat).
        { intro E0. unfold c in Ec.
          rewrite E0 in Ec. cbn in Ec. congruence. }
        destruct (Hw m ltac:(lia) Hfm) as [Ew|Ew].
        * destruct (Hivnew w1 m ltac:(lia)) as [E1o E1n].
          pose proof (Hivmono w2 m).
          pose proof (Hiv01 w2 (S m)).
          rewrite E1n. rewrite E1o in IH. lia.
        * destruct (Hivnew w2 m ltac:(lia)) as [E2o E2n].
          pose proof (Hivmono w1 m).
          pose proof (Hiv01 w1 (S m)).
          rewrite E2n. rewrite E2o in IH. lia. }
  pose proof (MAIN n ltac:(lia)) as H.
  pose proof (Hiv01 w1 n). pose proof (Hiv01 w2 n). lia.
Qed.

(** Z-side level sum of histogram counts *)
Fixpoint zho_sumZ (blc : zarr) (a : nat) (nn : nat) : Z :=
  match nn with
  | O => 0
  | S m => blc (Z.of_nat a) + zho_sumZ blc (S a) m
  end.

Lemma zho_sumZ_nonneg : forall (blc : zarr) (a nn : nat),
  (1 <= a)%nat -> (a + nn <= 16)%nat ->
  (forall b, 0 <= b <= 15 -> 0 <= blc b) ->
  0 <= zho_sumZ blc a nn.
Proof.
  intros blc a nn; revert a; induction nn as [|m IH]; intros a Ha Hab Hnn;
    cbn [zho_sumZ]; [lia|].
  assert (0 <= blc (Z.of_nat a)) by (apply Hnn; lia).
  assert (0 <= zho_sumZ blc (S a) m) by (apply IH; try lia; exact Hnn).
  lia.
Qed.

(** the two-leaf length cap, at the build_tree call shape *)
Lemma zho_len_le1 : forall k s t0 hp0 dep0 hlen0 maxc0
                           t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  forall w1 w2,
  (forall x, 0 <= x < sd_elems k -> t_freq t1 x <> 0 -> x = w1 \/ x = w2) ->
  forall v, 0 <= v <= maxc1 ->
  t_len (ts_trees (build_tree k s) k) v <= 1.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hel HM HK Hbl0 E0 E2 Eloop w1 w2 Hw v Hv.
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(lia) E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfrt0]]]].
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hbmc.
  destruct (BtItem6b.build_tree_out k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1
              hlen1 maxc1 ol1 sl1 stf Hel HM HK Hbl0 E0 E2 Eloop)
    as (Hmc' & Hvl & Hblcof & Hzks & Hdead & Hgap & Hlen7).
  set (TFIN := ts_trees (build_tree k s) k) in *.
  set (M := sd_max_length k) in *.
  set (blc := ts_blcount (build_tree k s)) in *.
  set (L := SendGo.tree_lens TFIN maxc1) in *.
  assert (Hvr : 0 <= v < sd_elems k) by lia.
  pose proof (Hlen7 v Hvr) as Hlr.
  destruct (Z.le_gt_cases (t_len TFIN v) 1) as [Hle|Hgt]; [exact Hle|].
  exfalso.
  set (l := t_len TFIN v) in *.
  (* the length value sits in the tree_lens list *)
  assert (HinL : In (Z.to_nat l) L).
  { unfold L, SendGo.tree_lens.
    apply in_map_iff.
    exists (Z.to_nat v). split.
    - rewrite Z2Nat.id by lia. reflexivity.
    - apply in_seq. lia. }
  assert (Hblcl : 1 <= blc l).
  { rewrite (Hblcof l ltac:(unfold MAX_BITS; lia)).
    assert (Hcnt : (1 <= count_occ Nat.eq_dec L (Z.to_nat l))%nat)
      by (apply zho_count_pos; exact HinL).
    assert (Ebl : bl_count L (Z.to_nat l) = count_occ Nat.eq_dec L (Z.to_nat l)).
    { unfold bl_count, count_len.
      destruct (Z.to_nat l) eqn:El; [lia | reflexivity]. }
    rewrite Ebl. lia. }
  (* the two-witness count bound *)
  assert (Hlvl : (zho_lvlsum L 1 15 <= 2)%nat).
  { unfold L, SendGo.tree_lens.
    apply (zho_nonzero_le2 (fun x => Z.to_nat (t_len TFIN x))
             (Z.to_nat (maxc1 + 1)) w1 w2).
    intros i Hi Hnz.
    assert (Hir : 0 <= Z.of_nat i < sd_elems k) by lia.
    apply Hw; [exact Hir|].
    intro Ef0.
    apply Hnz.
    rewrite (Hdead (Z.of_nat i) Hir Ef0).
    reflexivity. }
  (* cast the count sums to Z and split at level 1 *)
  assert (HblcOfPt : forall b, 0 <= b <= 15 ->
            blc b = Z.of_nat (bl_count L (Z.to_nat b)))
    by (intros b Hb; apply Hblcof; exact Hb).
  assert (HblcNN : forall b, 0 <= b <= 15 -> 0 <= blc b)
    by (intros b Hb; rewrite (HblcOfPt b Hb); lia).
  (* direct bounds *)
  assert (Hcast : forall (a nn : nat), (1 <= a)%nat -> (a + nn <= 16)%nat ->
            zho_sumZ blc a nn = Z.of_nat (zho_lvlsum L a nn)).
  { intros a nn; revert a; induction nn as [|m IH]; intros a Ha Hann;
      cbn [zho_sumZ zho_lvlsum]; [reflexivity|].
    rewrite (IH (S a)) by lia.
    rewrite (HblcOfPt (Z.of_nat a)) by lia.
    rewrite Nat2Z.id.
    assert (Ebl : bl_count L a = count_occ Nat.eq_dec L a).
    { unfold bl_count, count_len. destruct a; [lia | reflexivity]. }
    rewrite Ebl. lia. }
  assert (Hcap2 : forall (a nn : nat), (2 <= a)%nat ->
            Z.of_nat (a + nn) - 1 <= M ->
            zksum_over M blc (seq a nn) <= zho_sumZ blc a nn * 2 ^ (M - 2)).
  { intros a nn; revert a; induction nn as [|m IH]; intros a Ha Hann;
      cbn [seq zho_sumZ]; [unfold zksum_over; cbn; lia|].
    unfold zksum_over. cbn [map fold_right].
    fold (zksum_over M blc (seq (S a) m)).
    assert (Hrec : zksum_over M blc (seq (S a) m)
                   <= zho_sumZ blc (S a) m * 2 ^ (M - 2))
      by (apply IH; lia).
    assert (Hterm : blc (Z.of_nat a) * 2 ^ (M - Z.of_nat a)
                    <= blc (Z.of_nat a) * 2 ^ (M - 2)).
    { apply Z.mul_le_mono_nonneg_l.
      - apply HblcNN. lia.
      - apply Z.pow_le_mono_r; lia. }
    lia. }
  assert (Hmem2 : forall (a nn : nat), (Z.of_nat a <= l)%Z ->
            (l < Z.of_nat (a + nn))%Z -> (1 <= a)%nat -> (a + nn <= 16)%nat ->
            blc l <= zho_sumZ blc a nn).
  { intros a nn; revert a; induction nn as [|m IH]; intros a Hla Hlb Ha Hab;
      cbn [zho_sumZ].
    - lia.
    - destruct (Z.eq_dec (Z.of_nat a) l) as [El|Enl].
      + rewrite El.
        assert (0 <= zho_sumZ blc (S a) m); [|lia].
        apply (zho_sumZ_nonneg blc (S a) m); try lia.
        intros b Hb. apply HblcNN. exact Hb.
      + assert (blc l <= zho_sumZ blc (S a) m) by (apply IH; lia).
        assert (0 <= blc (Z.of_nat a)) by (apply HblcNN; lia).
        lia. }
  (* peel level 1 off the zksum *)
  assert (HMge2 : 2 <= M) by lia.
  assert (Epeel : zksum M blc
                  = blc 1 * 2 ^ (M - 1) + zksum_over M blc (seq 2 (Z.to_nat M - 1))).
  { unfold zksum.
    replace (Z.to_nat M) with (S (Z.to_nat M - 1)) at 1 by lia.
    unfold zksum_over. cbn [seq map fold_right].
    change (Z.of_nat 1) with 1.
    reflexivity. }
  set (S1 := blc 1) in *.
  set (S2 := zho_sumZ blc 2 (Z.to_nat M - 1)) in *.
  assert (HS2cap : zksum_over M blc (seq 2 (Z.to_nat M - 1))
                   <= S2 * 2 ^ (M - 2))
    by (apply Hcap2; lia).
  assert (HS2mem : blc l <= S2) by (apply Hmem2; lia).
  assert (Hsum12 : S1 + S2 <= 2).
  { assert (Ecast1 : zho_sumZ blc 1 (Z.to_nat M) = Z.of_nat (zho_lvlsum L 1 (Z.to_nat M)))
      by (apply Hcast; lia).
    assert (Epeel2 : zho_sumZ blc 1 (Z.to_nat M) = S1 + S2).
    { replace (Z.to_nat M) with (S (Z.to_nat M - 1)) by lia.
      cbn [zho_sumZ]. unfold S1, S2.
      change (Z.of_nat 1) with 1. reflexivity. }
    (* lvlsum over [1, M] <= lvlsum over [1, 15] *)
    assert (Hsplit : (zho_lvlsum L 1 (Z.to_nat M) <= zho_lvlsum L 1 15)%nat).
    { assert (Hext : forall (a n1 n2 : nat),
                zho_lvlsum L a (n1 + n2)
                = (zho_lvlsum L a n1 + zho_lvlsum L (a + n1) n2)%nat).
      { intros a n1; revert a; induction n1 as [|p IHp]; intros a n2;
          cbn [Nat.add zho_lvlsum].
        - replace (a + 0)%nat with a by lia. reflexivity.
        - rewrite IHp. replace (S a + p)%nat with (a + S p)%nat by lia. lia. }
      replace 15%nat with (Z.to_nat M + (15 - Z.to_nat M))%nat by lia.
      rewrite Hext. lia. }
    lia. }
  assert (HS1nn : 0 <= S1) by (apply HblcNN; lia).
  assert (HS2nn : 1 <= S2) by lia.
  (* the contradiction *)
  assert (Epow1 : 2 ^ (M - 1) = 2 * 2 ^ (M - 2)).
  { replace (M - 1) with (1 + (M - 2)) by lia.
    rewrite Z.pow_add_r by lia. lia. }
  assert (EpowM : 2 ^ M = 4 * 2 ^ (M - 2)).
  { replace M with (2 + (M - 2)) at 1 by lia.
    rewrite Z.pow_add_r by lia. lia. }
  assert (Hpnn : 1 <= 2 ^ (M - 2)).
  { replace 1 with (2 ^ 0) by reflexivity.
    apply Z.pow_le_mono_r; lia. }
  assert (HS1le1 : S1 <= 1) by lia.
  rewrite Epeel in Hzks.
  assert (HzkUB : 2 ^ M <= S1 * 2 ^ (M - 1) + S2 * 2 ^ (M - 2)) by lia.
  rewrite Epow1, EpowM in HzkUB.
  destruct (Z.eq_dec S1 0) as [-> | HS1e]; [nia | assert (S1 = 1) by lia; subst S1; nia].
Qed.

(** bt_force2 at one live symbol: the manufactured node, exactly *)
Lemma zho_force2_one : forall stree t hp dep maxc ol sl
                              t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  bt_force2 3%nat stree t hp dep 1 maxc ol sl
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  exists nd,
    nd = (if Z.ltb maxc 2 then maxc + 1 else 0)
    /\ t1 = t_setfreq t nd 1
    /\ maxc1 = (if Z.ltb maxc 2 then maxc + 1 else maxc)
    /\ ol1 = u64 (ol - 1)
    /\ sl1 = match stree with
             | None => sl
             | Some st => u64 (sl - t_len st nd)
             end.
Proof.
  intros stree t hp dep maxc ol sl t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E.
  cbn [bt_force2] in E.
  cbv zeta in E.
  destruct (Z.ltb maxc 2) eqn:Em in E; cbn in E;
    destruct stree as [st|];
    inversion E; subst; eexists;
    (split; [reflexivity|]);
    rewrite ?Em; repeat split; reflexivity.
Qed.

(** a zero wsum of nonnegative indicator terms is pointwise zero *)
Lemma zho_wsum_zero_pt : forall (f : Z -> Z) lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) ->
  wsum f lo n = 0 ->
  forall i, lo <= i < lo + Z.of_nat n -> f i = 0.
Proof.
  intros f lo n; revert lo; induction n as [|m IH]; intros lo Hnn H0 i Hi.
  - cbn [Z.of_nat] in Hi. lia.
  - rewrite Nat2Z.inj_succ in Hi.
    cbn [wsum] in H0.
    assert (Hh : 0 <= f lo) by (apply Hnn; lia).
    assert (Ht : 0 <= wsum f (lo + 1) m).
    { apply wsum_nonneg. intros j Hj. apply Hnn. lia. }
    destruct (Z.eq_dec i lo) as [->|Hne]; [lia|].
    apply (IH (lo + 1)); try lia.
    intros j Hj. apply Hnn. lia.
Qed.

(* ==========================================================================
   2.  The per-build UPPER: the counter delta is at most the tallied
       frequency-weighted cost of the built lengths (forced slots repaid
       exactly by the ol-decrements).
   ========================================================================== *)

Theorem zho_btc_upper : forall k s,
  3 <= sd_elems k <= 286 ->
  1 <= sd_max_length k <= 15 ->
  4 * (sd_elems k - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (forall i, 0 <= i < sd_elems k -> 0 <= t_freq (ts_trees s k) i <= 65535) ->
  (forall v, 0 <= v < sd_elems k ->
     0 <= xbits (sd_extra_base k) (sd_extra k) v <= 16) ->
  (forall v, 0 <= v <= 2 -> xbits (sd_extra_base k) (sd_extra k) v = 0) ->
  ts_optlen s = u64 (ts_optlen s) ->
  ts_statlen s = u64 (ts_statlen s) ->
  exists BTC,
    ts_optlen (build_tree k s) = u64 (ts_optlen s + BTC)
    /\ ts_statlen (build_tree k s) = u64 (ts_statlen (build_tree k s))
    /\ -2 <= BTC <= 68719476736
    /\ BTC <= wsum (fun v => t_freq (ts_trees s k) v
                 * (t_len (ts_trees (build_tree k s) k) v
                    + xbits (sd_extra_base k) (sd_extra k) v))
                0 (Z.to_nat (sd_elems k)).
Proof.
  intros k s Hel HM HK4 Hbl0 Hfr Hxb Hxb0 Hido Hids.
  assert (HLC : L_CODES = 286) by reflexivity.
  set (frq := t_freq (ts_trees s k)) in *.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_init_census_call (Z.to_nat L_CODES + 2) (sd_elems k)
              (ts_trees s k) (ts_heap s) (ts_depth s) t0 hp0 dep0 hlen0 maxc0
              E0
              ltac:(change (Z.of_nat (Z.to_nat L_CODES + 2)) with 288; lia)
              ltac:(lia)) as [Hout0 Hfr0].
  fold frq in Hfr0.
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; try eassumption; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(lia) E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz' [Hcen Hfrt0]]]].
  fold frq in Hfrt0.
  assert (Hh1e : hlen1 <= sd_elems k).
  { rewrite (io_total _ _ _ _ _ Hout1). apply live_total_le. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length k) by lia.
  (* u64-idempotence of the force outputs, via the landed case split *)
  destruct (bt_force2_full (sd_stree k) (sd_elems k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s) t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              E2 ltac:(lia) Hout0) as [Hmcmono Hcases].
  assert (Hol_sl : ol1 = u64 ol1 /\ sl1 = u64 sl1).
  { destruct Hcases as
      [(_ & _ & _ & Ho & Hs2)
      |[(v1 & _ & _ & _ & _ & _ & Ho & Hs2)
       |(_ & _ & _ & _ & _ & Ho & Hs2)]].
    - rewrite Ho, Hs2. split; [exact Hido | exact Hids].
    - split.
      + rewrite Ho. symmetry. apply g6_u64_idem.
      + rewrite Hs2. destruct (sd_stree k);
          [symmetry; apply g6_u64_idem | exact Hids].
    - split.
      + rewrite Ho. symmetry. apply g6_u64_idem.
      + rewrite Hs2. destruct (sd_stree k);
          [symmetry; apply g6_u64_idem | exact Hids]. }
  destruct Hol_sl as [Holu Hslu].
  destruct (build_tree_account k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1
              maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 Holu Hslu E0 E2 Eloop)
    as [Gol Gsl].
  destruct (BtItem6b.build_tree_out k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1
              hlen1 maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 E0 E2 Eloop)
    as (Hmc' & _ & _ & _ & _ & _ & Hlen7).
  set (TFIN := ts_trees (build_tree k s) k) in *.
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmax := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  assert (Hnd : ndf - sd_elems k <= 285) by lia.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hbmc.
  (* the statlen idempotence conjunct, once and for all *)
  assert (GSL : ts_statlen (build_tree k s) = u64 (ts_statlen (build_tree k s))).
  { rewrite Gsl. destruct (sd_stree k).
    - symmetry. apply g6_u64_idem.
    - exact Hslu. }
  (* the opt-side cost function and its window sum *)
  set (Cop := fun v => t_len TFIN v + xbits (sd_extra_base k) (sd_extra k) v)
    in *.
  assert (HCop : forall v, 0 <= v < sd_elems k -> 0 <= Cop v <= 32).
  { intros v Hv. unfold Cop.
    pose proof (Hlen7 v Hv). pose proof (Hxb v Hv). lia. }
  set (WSo := wsum (olterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k) TFIN)
                (hmax + 1) (Z.to_nat (HEAP_SIZE - (hmax + 1)))) in *.
  (* per-case frequency facts feed the kit *)
  assert (Hfr1gen : forall v, 0 <= v < sd_elems k -> 0 <= t_freq t1 v <= 65535).
  { intros v Hv.
    destruct Hcases as
      [(_ & Et1 & _)
      |[(v1 & _ & Et1 & _ & _ & _ & _ & _)
       |(_ & Et1 & _)]]; rewrite Et1.
    - rewrite Hfrt0. apply Hfr. exact Hv.
    - destruct (Z.eq_dec v v1) as [->|Hne].
      + rewrite g6_t_freq_setfreq_same.
        change (u16 1) with 1. lia.
      + rewrite g6_t_freq_setfreq_other by exact Hne.
        rewrite Hfrt0. apply Hfr. exact Hv.
    - destruct (Z.eq_dec v 1) as [->|Hne1].
      + rewrite g6_t_freq_setfreq_same.
        change (u16 1) with 1. lia.
      + rewrite g6_t_freq_setfreq_other by exact Hne1.
        destruct (Z.eq_dec v 0) as [->|Hne0].
        * rewrite g6_t_freq_setfreq_same.
          change (u16 1) with 1. lia.
        * rewrite g6_t_freq_setfreq_other by exact Hne0.
          rewrite Hfrt0. apply Hfr. exact Hv. }
  assert (EWo : WSo = wsum (fun p => wF maxc1 (b_tree stf) Cop (hp3 p))
                        (hmax + 1) (NW hmax)).
  { unfold WSo, NW. apply wsum_ext. intros p _.
    unfold wF, olterm, Cop.
    destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|Hgt]; cbn [ind].
    - rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia. reflexivity.
    - ring. }
  pose proof (kit_bound (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cop
                Hpk ltac:(lia) Hnd Hfr1gen HCop) as BDo.
  pose proof (kit_upper (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cop
                Hpk ltac:(lia) Hnd Hfr1gen HCop) as UPo.
  rewrite <- EWo in BDo, UPo.
  (* trichotomy on the live count *)
  pose proof (io_hlen _ _ _ _ _ Hout0) as Hh00.
  destruct (Z.le_gt_cases 2 hlen0) as [Hh2|Hh01].
  - (* no manufactured slot *)
    destruct Hcases as
      [(_ & Et1 & Emc1 & Eol1 & _)
      |[(v1 & Hh1 & _)|(Hh0 & _)]]; [|lia|lia].
    assert (ET1F : forall v, 0 <= v < sd_elems k -> t_freq t1 v = frq v)
      by (intros v Hv; rewrite Et1; apply Hfrt0).
    exists WSo.
    split.
    { rewrite Gol, Eol1. reflexivity. }
    split; [exact GSL|].
    split; [lia|].
    eapply Z.le_trans; [exact UPo|].
    apply Z.eq_le_incl.
    apply wsum_ext. intros v Hv.
    rewrite ET1F by lia. unfold Cop. reflexivity.
  - (* manufactured slots *)
    (* unique live symbol characterization at hlen0 <= 1 *)
    assert (Hlive1 : forall x, 0 <= x < sd_elems k -> frq x <> 0 ->
                     live_b t0 maxc0 x = true).
    { intros x Hx Hnz.
      destruct (Z.le_gt_cases x maxc0) as [Hle|Hgt].
      - unfold live_b.
        replace ((0 <=? x) && (x <=? maxc0))%bool with true
          by (symmetry; apply Bool.andb_true_iff; split;
              [apply Z.leb_le; lia | apply Z.leb_le; lia]).
        cbn [andb].
        rewrite <- (Hfr0 x) in Hnz.
        apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hnz.
      - exfalso. apply Hnz. rewrite <- (Hfr0 x).
        apply (io_gapz _ _ _ _ _ Hout0). lia. }
    destruct (Z.eq_dec hlen0 1) as [Eh1|Eh0'].
    + (* exactly one live symbol *)
      subst hlen0.
      destruct (zho_force2_one (sd_stree k) t0 hp0 dep0 maxc0
                  (ts_optlen s) (ts_statlen s)
                  t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E2)
        as (nd & End & Et1 & Emc1 & Eol1 & Esl1).
      assert (Hnd2 : 0 <= nd <= 2).
      { rewrite End.
        pose proof (io_maxc _ _ _ _ _ Hout0).
        destruct (Z.ltb_spec maxc0 2); lia. }
      assert (Hndmc : nd <= maxc1).
      { rewrite End, Emc1.
        destruct (Z.ltb_spec maxc0 2); lia. }
      (* the unique live symbol *)
      set (w := hp0 1) in *.
      assert (Huniq : forall x, 0 <= x < sd_elems k -> frq x <> 0 -> x = w).
      { intros x Hx Hnz.
        pose proof (io_spec _ _ _ _ _ Hout0 x) as Hsp.
        rewrite (Hlive1 x Hx Hnz) in Hsp.
        cbn [ind] in Hsp.
        unfold lcount, wcount in Hsp.
        change (Z.to_nat 1) with 1%nat in Hsp.
        cbn [wsum] in Hsp.
        cbv beta in Hsp.
        fold w in Hsp.
        destruct (Z.eqb_spec w x) as [->|Hne]; [reflexivity|].
        cbn [ind] in Hsp. lia. }
      assert (Hfrnd : frq nd = 0).
      { rewrite End.
        destruct (Z.ltb_spec maxc0 2) as [Hm2|Hm2].
        - rewrite <- (Hfr0 (maxc0 + 1)).
          apply (io_gapz _ _ _ _ _ Hout0). lia.
        - (* nd = 0; the unique live is maxc0 >= 2, so 0 is dead *)
          destruct (Z.eq_dec (frq 0) 0) as [E00|E00]; [exact E00|].
          exfalso.
          assert (H0w : 0 = w) by (apply Huniq; [lia | exact E00]).
          assert (Hmw : maxc0 = w).
          { apply Huniq; [pose proof (io_maxc _ _ _ _ _ Hout0); lia|].
            destruct (io_live _ _ _ _ _ Hout0) as [Hm1|Hnz0]; [lia|].
            rewrite <- (Hfr0 maxc0). exact Hnz0. }
          lia. }
      (* t1 frequencies split into frq + the nd delta *)
      assert (ET1F : forall v, 0 <= v < sd_elems k ->
                t_freq t1 v = frq v + (if Z.eqb nd v then 1 else 0)).
      { intros v Hv. rewrite Et1.
        destruct (Z.eqb_spec nd v) as [->|Hne].
        - rewrite g6_t_freq_setfreq_same.
          change (u16 1) with 1. rewrite Hfrnd. lia.
        - rewrite g6_t_freq_setfreq_other by (intro; apply Hne; congruence).
          rewrite Hfrt0. lia. }
      (* the length cap at the manufactured slot *)
      assert (Hlnd : t_len TFIN nd <= 1).
      { apply (zho_len_le1 k s t0 hp0 dep0 1 maxc0
                 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
                 ltac:(lia) HM HK Hbl0 E0 E2 Eloop w nd).
        - intros x Hx Hnz.
          rewrite (ET1F x Hx) in Hnz.
          destruct (Z.eqb_spec nd x) as [->|Hne]; [right; reflexivity|].
          left. apply Huniq; [exact Hx|]. cbn [ind] in Hnz. lia.
        - lia. }
      assert (HCnd : Cop nd <= 1).
      { unfold Cop.
        rewrite (Hxb0 nd Hnd2). lia. }
      exists (WSo - 1).
      split.
      { rewrite Gol, Eol1.
        rewrite g6_u64_shift.
        f_equal. ring. }
      split; [exact GSL|].
      split; [lia|].
      apply Z.le_trans
        with (m := wsum (fun v => t_freq t1 v * Cop v)
                     0 (Z.to_nat (sd_elems k)) - 1); [lia|].
      rewrite (wsum_ext (fun v => t_freq t1 v * Cop v)
                 (fun v => frq v
                             * (t_len TFIN v
                                + xbits (sd_extra_base k) (sd_extra k) v)
                           + (if Z.eqb nd v then 1 else 0) * Cop v)
                 0 (Z.to_nat (sd_elems k))).
      2:{ intros v Hv.
          rewrite ET1F by lia. unfold Cop. ring. }
      rewrite wsum_plus.
      rewrite (wsum_delta Cop nd 0 (Z.to_nat (sd_elems k))) by lia.
      lia.
    + (* no live symbols: hlen0 = 0 *)
      assert (Eh0 : hlen0 = 0) by lia.
      subst hlen0.
      destruct Hcases as
        [(Hh2' & _)|[(v1 & Hh1 & _)|(_ & Et1 & Ef00 & Ef01 & Emc1 & Eol1 & Esl1)]];
        [lia|lia|].
      (* every entry frequency vanishes *)
      assert (Hfrall : forall x, 0 <= x < sd_elems k -> frq x = 0).
      { intros x Hx.
        destruct (Z.eq_dec (frq x) 0) as [E|E]; [exact E|].
        exfalso.
        pose proof (Hlive1 x Hx E) as Hlb.
        pose proof (io_total _ _ _ _ _ Hout0) as Htot.
        unfold live_total in Htot.
        assert (Hpt : ind (live_b t0 maxc0 x) = 0).
        { apply (zho_wsum_zero_pt
                   (fun y => ind (live_b t0 maxc0 y)) 0 (Z.to_nat (sd_elems k))).
          - intros i _. destruct (live_b t0 maxc0 i); cbn [ind]; lia.
          - lia.
          - lia. }
        rewrite Hlb in Hpt. cbn [ind] in Hpt. lia. }
      assert (ET1F : forall v, 0 <= v < sd_elems k ->
                t_freq t1 v = frq v + (if Z.eqb 0 v then 1 else 0)
                              + (if Z.eqb 1 v then 1 else 0)).
      { intros v Hv. rewrite Et1.
        destruct (Z.eqb_spec 1 v) as [<-|Hne1].
        - rewrite g6_t_freq_setfreq_same.
          change (u16 1) with 1.
          rewrite (Hfrall 1) by lia.
          reflexivity.
        - rewrite g6_t_freq_setfreq_other by (intro; apply Hne1; congruence).
          destruct (Z.eqb_spec 0 v) as [<-|Hne0].
          + rewrite g6_t_freq_setfreq_same.
            change (u16 1) with 1.
            rewrite (Hfrall 0) by lia.
            reflexivity.
          + rewrite g6_t_freq_setfreq_other by (intro; apply Hne0; congruence).
            rewrite Hfrt0. lia. }
      assert (Hl0 : t_len TFIN 0 <= 1 /\ t_len TFIN 1 <= 1).
      { assert (Hcap : forall v, 0 <= v <= maxc1 -> t_len TFIN v <= 1).
        { apply (zho_len_le1 k s t0 hp0 dep0 0 maxc0
                   t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
                   ltac:(lia) HM HK Hbl0 E0 E2 Eloop 0 1).
          intros x Hx Hnz.
          rewrite (ET1F x Hx) in Hnz.
          destruct (Z.eqb_spec 0 x) as [<-|Hne0]; [left; reflexivity|].
          destruct (Z.eqb_spec 1 x) as [<-|Hne1]; [right; reflexivity|].
          exfalso. rewrite (Hfrall x Hx) in Hnz. cbn [ind] in Hnz. lia. }
        split; apply Hcap; lia. }
      destruct Hl0 as [Hl00 Hl01].
      assert (HC0 : Cop 0 <= 1)
        by (unfold Cop; rewrite (Hxb0 0 ltac:(lia)); lia).
      assert (HC1 : Cop 1 <= 1)
        by (unfold Cop; rewrite (Hxb0 1 ltac:(lia)); lia).
      exists (WSo - 2).
      split.
      { rewrite Gol, Eol1.
        rewrite g6_u64_shift.
        f_equal. ring. }
      split; [exact GSL|].
      split; [lia|].
      apply Z.le_trans
        with (m := wsum (fun v => t_freq t1 v * Cop v)
                     0 (Z.to_nat (sd_elems k)) - 2); [lia|].
      rewrite (wsum_ext (fun v => t_freq t1 v * Cop v)
                 (fun v => frq v
                             * (t_len TFIN v
                                + xbits (sd_extra_base k) (sd_extra k) v)
                           + ((if Z.eqb 0 v then 1 else 0) * Cop v
                              + (if Z.eqb 1 v then 1 else 0) * Cop v))
                 0 (Z.to_nat (sd_elems k))).
      2:{ intros v Hv.
          rewrite ET1F by lia. unfold Cop. ring. }
      rewrite wsum_plus.
      rewrite wsum_plus.
      rewrite (wsum_delta Cop 0 0 (Z.to_nat (sd_elems k))) by lia.
      rewrite (wsum_delta Cop 1 0 (Z.to_nat (sd_elems k))) by lia.
      lia.
Qed.

Theorem dispatch_ol_upper : forall ts toks,
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  ts_optlen (S2P ts)
  <= toks_cost (ts_trees (S2P ts) TK_L) (ts_trees (S2P ts) TK_D) toks
     + t_len (ts_trees (S2P ts) TK_L) END_BLOCK
     + (14 + 3 * (S2M ts + 1))
     + zho_bldesc ts TK_L + zho_bldesc ts TK_D
     + 6.
Proof.
  intros ts toks Hol0 Hsl0 Hbl0 HFI Henc Hlen HblZ HnnL HnnD.
  destruct HFI as [HFL HFD].
  assert (HfrL : forall i, 0 <= i < sd_elems TK_L ->
                 0 <= t_freq (ts_trees ts TK_L) i <= 65535).
  { intros i Hi. change (sd_elems TK_L) with 286 in Hi.
    rewrite (HFL i) by (unfold L_CODES; lia).
    pose proof (count_L_nonneg i toks).
    pose proof (count_L_le_len i toks).
    destruct (Z.eqb i END_BLOCK); lia. }
  assert (HfrD0 : forall i, 0 <= i < sd_elems TK_D ->
                  0 <= t_freq (ts_trees ts TK_D) i <= 65535).
  { intros i Hi. change (sd_elems TK_D) with 30 in Hi.
    rewrite (HFD i) by (unfold D_CODES; lia).
    pose proof (count_D_nonneg i toks).
    pose proof (count_D_le_len i toks). lia. }
  (* --- the L build --- *)
  set (BL' := build_tree TK_L ts) in *.
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (2 ^ sd_max_length TK_L) with 32768; lia).
  assert (HxbL : forall v, 0 <= v < sd_elems TK_L ->
                 0 <= xbits (sd_extra_base TK_L) (sd_extra TK_L) v <= 16)
    by (intros v Hv; change (sd_elems TK_L) with 286 in Hv;
        apply xbits_L_range; exact Hv).
  assert (Hxb0L : forall v, 0 <= v <= 2 ->
                  xbits (sd_extra_base TK_L) (sd_extra TK_L) v = 0).
  { intros v Hv. unfold xbits.
    change (sd_extra_base TK_L) with 257.
    replace (257 <=? v) with false
      by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  destruct (zho_btc_upper TK_L ts HelL HML HKL Hbl0 HfrL HxbL Hxb0L
              ltac:(rewrite Hol0; reflexivity)
              ltac:(rewrite Hsl0; reflexivity))
    as (BTCL & EolL & EslLidem & HbLr & HupL).
  fold BL' in EolL, EslLidem, HupL.
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl0)
    as (HmcLr & HlenL & HblL & HcapL).
  fold BL' in HmcLr, HlenL, HblL, HcapL.
  (* --- the D build --- *)
  set (BD' := build_tree TK_D BL') in *.
  assert (NEQ_D_L : TK_D <> TK_L)
    by (change TK_D with 1; change TK_L with 0; lia).
  assert (NEQ_L_D : TK_L <> TK_D)
    by (change TK_L with 0; change TK_D with 1; lia).
  assert (NEQ_L_BL : TK_L <> TK_BL)
    by (change TK_L with 0; change TK_BL with 2; lia).
  assert (NEQ_D_BL : TK_D <> TK_BL)
    by (change TK_D with 1; change TK_BL with 2; lia).
  assert (NEQ_BL_L : TK_BL <> TK_L)
    by (change TK_BL with 2; change TK_L with 0; lia).
  assert (NEQ_BL_D : TK_BL <> TK_D)
    by (change TK_BL with 2; change TK_D with 1; lia).
  assert (EfrD : ts_trees BL' TK_D = ts_trees ts TK_D)
    by (unfold BL'; apply build_tree_tree_other; exact NEQ_D_L).
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (2 ^ sd_max_length TK_D) with 32768; lia).
  assert (HxbD : forall v, 0 <= v < sd_elems TK_D ->
                 0 <= xbits (sd_extra_base TK_D) (sd_extra TK_D) v <= 16)
    by (intros v Hv; change (sd_elems TK_D) with 30 in Hv;
        apply xbits_D_range; exact Hv).
  assert (Hxb0D : forall v, 0 <= v <= 2 ->
                  xbits (sd_extra_base TK_D) (sd_extra TK_D) v = 0).
  { intros v Hv. unfold xbits.
    change (sd_extra_base TK_D) with 0.
    replace (0 <=? v) with true
      by (symmetry; apply Z.leb_le; lia).
    assert (Hv3 : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hv3 as [-> | [-> | ->]]; reflexivity. }
  assert (HfrD : forall i, 0 <= i < sd_elems TK_D ->
                 0 <= t_freq (ts_trees BL' TK_D) i <= 65535)
    by (intros i Hi; rewrite EfrD; apply HfrD0; exact Hi).
  destruct (zho_btc_upper TK_D BL' HelD HMD HKD HblL HfrD HxbD Hxb0D
              ltac:(rewrite EolL; symmetry; apply g6_u64_idem)
              EslLidem)
    as (BTCD & EolD & EslDidem & HbDr & HupD0).
  fold BD' in EolD, EslDidem, HupD0.
  assert (HupD : BTCD <= wsum (fun v => t_freq (ts_trees ts TK_D) v
                          * (t_len (ts_trees BD' TK_D) v
                             + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
                    0 (Z.to_nat (sd_elems TK_D))).
  { eapply Z.le_trans; [exact HupD0|].
    apply Z.eq_le_incl. apply wsum_ext. intros i _.
    rewrite EfrD. reflexivity. }
  destruct (build_tree_shape TK_D BL' HelD HMD HKD HblL)
    as (HmcDr & HlenD & HblD & HcapD).
  fold BD' in HmcDr, HlenD, HblD, HcapD.
  (* --- the build_bl_tree pipeline, destructured --- *)
  set (tL := ts_trees BD' TK_L) in *.
  set (mcL := ts_maxcode BD' TK_L) in *.
  set (bl0 := ts_trees BD' TK_BL) in *.
  set (p1 := scan_tree tL mcL bl0) in *.
  set (s1' := set_tree TK_BL (snd p1) (set_tree TK_L (fst p1) BD')) in *.
  set (tD := ts_trees s1' TK_D) in *.
  set (mcD := ts_maxcode s1' TK_D) in *.
  set (bl1 := ts_trees s1' TK_BL) in *.
  set (p2 := scan_tree tD mcD bl1) in *.
  set (s2' := set_tree TK_BL (snd p2) (set_tree TK_D (fst p2) s1')) in *.
  set (s3 := build_tree TK_BL s2') in *.
  set (mbi := bbl_scan (Z.to_nat BL_CODES + 1) (ts_trees s3 TK_BL)
                (BL_CODES - 1)) in *.
  assert (EP : build_bl_tree BD'
               = (mbi, set_optlen
                         (u64 (ts_optlen s3 + 3 * (mbi + 1) + 5 + 5 + 4))
                         s3)).
  { unfold build_bl_tree. cbv zeta. reflexivity. }
  assert (EtL : tL = ts_trees BL' TK_L)
    by (unfold tL, BD'; apply build_tree_tree_other; exact NEQ_L_D).
  assert (EmcL0 : mcL = ts_maxcode BL' TK_L)
    by (unfold mcL, BD'; apply build_tree_maxcode_other; exact NEQ_L_D).
  assert (Ebl0 : forall v, 0 <= v < 19 -> t_freq bl0 v = 0).
  { intros v Hv. unfold bl0, BD'.
    rewrite (build_tree_tree_other TK_D BL' TK_BL) by exact NEQ_BL_D.
    unfold BL'.
    rewrite (build_tree_tree_other TK_L ts TK_BL) by exact NEQ_BL_L.
    apply HblZ. exact Hv. }
  assert (EtD : tD = ts_trees BD' TK_D).
  { unfold tD, s1'.
    rewrite (set_tree_other TK_BL (snd p1) (set_tree TK_L (fst p1) BD') TK_D)
      by exact NEQ_D_BL.
    rewrite (set_tree_other TK_L (fst p1) BD' TK_D) by exact NEQ_D_L.
    reflexivity. }
  assert (EmcD0 : mcD = ts_maxcode BD' TK_D)
    by (unfold mcD, s1'; rewrite !g6_mc_settree; reflexivity).
  assert (Ebl1 : bl1 = snd p1)
    by (unfold bl1, s1'; apply set_tree_same).
  assert (EtrL : ts_trees (snd (build_bl_tree BD')) TK_L = fst p1).
  { rewrite EP. cbn [snd]. rewrite g6_tr_setoptlen.
    unfold s3.
    rewrite (build_tree_tree_other TK_BL s2' TK_L) by exact NEQ_L_BL.
    unfold s2'.
    rewrite (set_tree_other TK_BL (snd p2) (set_tree TK_D (fst p2) s1') TK_L)
      by exact NEQ_L_BL.
    rewrite (set_tree_other TK_D (fst p2) s1' TK_L) by exact NEQ_L_D.
    unfold s1'.
    rewrite (set_tree_other TK_BL (snd p1) (set_tree TK_L (fst p1) BD') TK_L)
      by exact NEQ_L_BL.
    apply set_tree_same. }
  assert (EtrD : ts_trees (snd (build_bl_tree BD')) TK_D = fst p2).
  { rewrite EP. cbn [snd]. rewrite g6_tr_setoptlen.
    unfold s3.
    rewrite (build_tree_tree_other TK_BL s2' TK_D) by exact NEQ_D_BL.
    unfold s2'.
    rewrite (set_tree_other TK_BL (snd p2) (set_tree TK_D (fst p2) s1') TK_D)
      by exact NEQ_D_BL.
    apply set_tree_same. }
  assert (EtrB : ts_trees (snd (build_bl_tree BD')) TK_BL = ts_trees s3 TK_BL)
    by (rewrite EP; cbn [snd]; apply g6_tr_setoptlen).
  assert (EmcLf : ts_maxcode (snd (build_bl_tree BD')) TK_L = mcL).
  { rewrite EP. cbn [snd]. rewrite g6_mc_setoptlen.
    unfold s3.
    rewrite (build_tree_maxcode_other TK_BL s2' TK_L) by exact NEQ_L_BL.
    unfold s2'. rewrite !g6_mc_settree.
    reflexivity. }
  assert (EmcDf : ts_maxcode (snd (build_bl_tree BD')) TK_D = mcD).
  { rewrite EP. cbn [snd]. rewrite g6_mc_setoptlen.
    unfold s3.
    rewrite (build_tree_maxcode_other TK_BL s2' TK_D) by exact NEQ_D_BL.
    unfold s2'. rewrite !g6_mc_settree.
    reflexivity. }
  (* --- the scan count laws --- *)
  assert (Hbud0 : RBudget bl0 0)
    by (intros v Hv; rewrite (Ebl0 v Hv); lia).
  assert (HmcL285 : 0 <= mcL <= 285)
    by (rewrite EmcL0; change (sd_elems TK_L) with 286 in HmcLr; lia).
  assert (HlentL : forall i, 0 <= i <= mcL -> 0 <= t_len tL i <= 15).
  { intros i Hi. rewrite EtL.
    assert (Hi' : 0 <= i < sd_elems TK_L)
      by (change (sd_elems TK_L) with 286; lia).
    pose proof (HlenL i Hi').
    change (sd_max_length TK_L) with 15 in *. lia. }
  assert (Cnt1 : forall v, t_freq (snd p1) v
                 = t_freq bl0 v
                   + hid_zcount v (items_syms (send_tree_items (fst p1) mcL))).
  { intro v.
    apply (scan_tree_counts_r tL mcL bl0 v 0 287 HmcL285 HlentL Hbud0);
      lia. }
  assert (Hbud1 : RBudget bl1 286).
  { rewrite Ebl1.
    apply (scan_tree_budget_r tL mcL bl0 0 286 HmcL285 HlentL Hbud0); lia. }
  assert (HmcD285 : 0 <= mcD <= 285)
    by (rewrite EmcD0; change (sd_elems TK_D) with 30 in HmcDr; lia).
  assert (HlentD : forall i, 0 <= i <= mcD -> 0 <= t_len tD i <= 15).
  { intros i Hi. rewrite EtD.
    assert (Hi' : 0 <= i < sd_elems TK_D)
      by (change (sd_elems TK_D) with 30; rewrite EmcD0 in Hi;
          change (sd_elems TK_D) with 30 in HmcDr; lia).
    pose proof (HlenD i Hi').
    change (sd_max_length TK_D) with 15 in *. lia. }
  assert (Cnt2 : forall v, t_freq (snd p2) v
                 = t_freq bl1 v
                   + hid_zcount v (items_syms (send_tree_items (fst p2) mcD))).
  { intro v.
    apply (scan_tree_counts_r tD mcD bl1 v 286 572 HmcD285 HlentD Hbud1);
      lia. }
  assert (CntB : forall v, 0 <= v < 19 ->
                 t_freq (ts_trees s2' TK_BL) v
                 = hid_zcount v (items_syms (send_tree_items (fst p1) mcL))
                   + hid_zcount v (items_syms (send_tree_items (fst p2) mcD))).
  { intros v Hv.
    unfold s2'. rewrite set_tree_same.
    rewrite (Cnt2 v). rewrite Ebl1. rewrite (Cnt1 v). rewrite (Ebl0 v Hv).
    ring. }
  (* --- the BL build --- *)
  assert (HelB : 3 <= sd_elems TK_BL <= 286)
    by (change (sd_elems TK_BL) with 19; lia).
  assert (HMB : 1 <= sd_max_length TK_BL <= 15)
    by (change (sd_max_length TK_BL) with 7; lia).
  assert (HKB : 4 * (sd_elems TK_BL - 1) < 2 ^ sd_max_length TK_BL)
    by (change (sd_elems TK_BL) with 19;
        change (2 ^ sd_max_length TK_BL) with 128; lia).
  assert (HblS2 : forall b, b < 0 \/ 15 < b -> ts_blcount s2' b = 0).
  { intros b Hb. unfold s2'. rewrite !g6_bc_settree.
    unfold s1'. rewrite !g6_bc_settree. apply HblD. exact Hb. }
  assert (HhidL : forall v,
            0 <= hid_zcount v (items_syms (send_tree_items (fst p1) mcL))
            <= 867).
  { intro v. split; [apply hid_nonneg|].
    eapply Z.le_trans; [apply hid_le_length|].
    rewrite items_syms_length.
    pose proof (send_tree_items_count (fst p1) mcL). lia. }
  assert (HhidD : forall v,
            0 <= hid_zcount v (items_syms (send_tree_items (fst p2) mcD))
            <= 867).
  { intro v. split; [apply hid_nonneg|].
    eapply Z.le_trans; [apply hid_le_length|].
    rewrite items_syms_length.
    pose proof (send_tree_items_count (fst p2) mcD). lia. }
  assert (HfrB : forall i, 0 <= i < sd_elems TK_BL ->
                 0 <= t_freq (ts_trees s2' TK_BL) i <= 65535).
  { intros i Hi. change (sd_elems TK_BL) with 19 in Hi.
    rewrite (CntB i Hi).
    pose proof (HhidL i). pose proof (HhidD i). lia. }
  assert (HxbB : forall v, 0 <= v < sd_elems TK_BL ->
                 0 <= xbits (sd_extra_base TK_BL) (sd_extra TK_BL) v <= 16)
    by (intros v Hv; change (sd_elems TK_BL) with 19 in Hv;
        apply xbits_BL_range; exact Hv).
  assert (Hxb0B : forall v, 0 <= v <= 2 ->
                  xbits (sd_extra_base TK_BL) (sd_extra TK_BL) v = 0).
  { intros v Hv. unfold xbits.
    change (sd_extra_base TK_BL) with 0.
    replace (0 <=? v) with true
      by (symmetry; apply Z.leb_le; lia).
    assert (Hv3 : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hv3 as [-> | [-> | ->]]; reflexivity. }
  assert (EolS2 : ts_optlen s2' = ts_optlen BD').
  { unfold s2'. rewrite !g6_ol_settree.
    unfold s1'. rewrite !g6_ol_settree. reflexivity. }
  assert (EslS2 : ts_statlen s2' = ts_statlen BD').
  { unfold s2'. rewrite !g6_sl_settree.
    unfold s1'. rewrite !g6_sl_settree. reflexivity. }
  destruct (zho_btc_upper TK_BL s2' HelB HMB HKB HblS2 HfrB HxbB Hxb0B
              ltac:(rewrite EolS2, EolD; symmetry; apply g6_u64_idem)
              ltac:(rewrite EslS2; exact EslDidem))
    as (BTCB & EolB & _ & HbBr & HupB).
  fold s3 in EolB, HupB.
  (* --- mbi --- *)
  assert (Hmbi : 2 <= mbi <= 18).
  { unfold mbi.
    change (Z.to_nat BL_CODES + 1)%nat with 20%nat.
    change (BL_CODES - 1) with 18.
    destruct (bbl_scan_spec 20%nat (ts_trees s3 TK_BL) 18
                ltac:(change (Z.of_nat 20) with 20; lia)
                ltac:(lia)) as [Hr _].
    exact Hr. }
  (* --- the counter value, plain --- *)
  set (OL := BTCL + BTCD + BTCB + 3 * (mbi + 1) + 5 + 5 + 4) in *.
  assert (EOL : ts_optlen (snd (build_bl_tree BD')) = OL).
  { rewrite EP. cbn [snd]. rewrite ol_optlen.
    rewrite EolB.
    replace (u64 (ts_optlen s2' + BTCB) + 3 * (mbi + 1) + 5 + 5 + 4)
      with (u64 (ts_optlen s2' + BTCB) + (3 * (mbi + 1) + 5 + 5 + 4))
      by ring.
    rewrite g6_u64_shift.
    rewrite EolS2, EolD.
    replace (u64 (ts_optlen BL' + BTCD) + BTCB + (3 * (mbi + 1) + 5 + 5 + 4))
      with (u64 (ts_optlen BL' + BTCD)
            + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4))) by ring.
    rewrite g6_u64_shift.
    rewrite EolL, Hol0.
    replace (u64 (0 + BTCL) + BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4)))
      with (u64 (0 + BTCL)
            + (BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4)))) by ring.
    rewrite g6_u64_shift.
    replace (0 + BTCL + (BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4))))
      with OL by (unfold OL; ring).
    unfold u64. apply Z.mod_small. unfold OL. lia. }
  (* --- the guard bridges --- *)
  assert (HcapL' : forall i, 0 <= i < 286 ->
                   t_freq (ts_trees ts TK_L) i <> 0 -> i <> mcL + 1).
  { intros i Hi Hnz Heq.
    assert (Hle : i <= ts_maxcode BL' TK_L).
    { apply HcapL; [change (sd_elems TK_L) with 286; lia | exact Hnz]. }
    rewrite <- EmcL0 in Hle. lia. }
  assert (HcapD' : forall i, 0 <= i < 30 ->
                   t_freq (ts_trees ts TK_D) i <> 0 -> i <> mcD + 1).
  { intros i Hi Hnz Heq.
    assert (Hle : i <= ts_maxcode BD' TK_D).
    { apply HcapD; [change (sd_elems TK_D) with 30; lia |].
      rewrite EfrD. exact Hnz. }
    rewrite <- EmcD0 in Hle. lia. }
  (* --- the upper chains at the dispatch trees --- *)
  assert (HL2 : BTCL <= wsum (fun i => t_freq (ts_trees ts TK_L) i
                          * cost_L (fst p1) i) 0 (Z.to_nat L_CODES)).
  { eapply Z.le_trans; [exact HupL|].
    apply Z.eq_le_incl.
    rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i * cost_L (fst p1) i)
               (fun i => t_freq (ts_trees ts TK_L) i
                         * (t_len (fst p1) i
                            + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
               0 (Z.to_nat L_CODES))
      by (intros i _; rewrite g6_costL_vocab; reflexivity).
    unfold p1.
    rewrite (g6_scan_len_bridge (t_freq (ts_trees ts TK_L)) tL mcL bl0
               (xbits (sd_extra_base TK_L) (sd_extra TK_L)) (Z.to_nat L_CODES)).
    2:{ intros i Hi Hnz.
        apply HcapL'; [|exact Hnz].
        change (Z.of_nat (Z.to_nat L_CODES)) with 286 in Hi. lia. }
    apply wsum_ext.
    intros i _. rewrite EtL. reflexivity. }
  assert (HD2 : BTCD <= wsum (fun i => t_freq (ts_trees ts TK_D) i
                          * cost_D (fst p2) i) 0 (Z.to_nat D_CODES)).
  { eapply Z.le_trans; [exact HupD|].
    apply Z.eq_le_incl.
    rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_D) i * cost_D (fst p2) i)
               (fun i => t_freq (ts_trees ts TK_D) i
                         * (t_len (fst p2) i
                            + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
               0 (Z.to_nat D_CODES))
      by (intros i Hi; rewrite g6_costD_vocab
            by (change (Z.of_nat (Z.to_nat D_CODES)) with 30 in Hi; lia);
          reflexivity).
    unfold p2.
    rewrite (g6_scan_len_bridge (t_freq (ts_trees ts TK_D)) tD mcD bl1
               (xbits (sd_extra_base TK_D) (sd_extra TK_D)) (Z.to_nat D_CODES)).
    2:{ intros i Hi Hnz.
        apply HcapD'; [|exact Hnz].
        change (Z.of_nat (Z.to_nat D_CODES)) with 30 in Hi. lia. }
    apply wsum_ext.
    intros i _. rewrite EtD. reflexivity. }
  assert (HB2 : BTCB <= wsum (fun sy =>
                    hid_zcount sy (items_syms (send_tree_items (fst p1) mcL))
                    * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy)) 0 19
                + wsum (fun sy =>
                    hid_zcount sy (items_syms (send_tree_items (fst p2) mcD))
                    * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy)) 0 19).
  { eapply Z.le_trans; [exact HupB|].
    apply Z.eq_le_incl.
    rewrite <- wsum_plus.
    change (Z.to_nat (sd_elems TK_BL)) with 19%nat.
    apply wsum_ext. intros sy Hsy.
    change (Z.of_nat 19) with 19 in Hsy.
    rewrite (CntB sy ltac:(lia)).
    rewrite <- (g6_costBL_vocab (ts_trees s3 TK_BL) sy) by lia.
    ring. }
  (* --- the count regroupings --- *)
  assert (EregL : wsum (fun i => t_freq (ts_trees ts TK_L) i
                          * cost_L (fst p1) i) 0 (Z.to_nat L_CODES)
                  = wsum (fun i => count_L i toks * cost_L (fst p1) i)
                      0 (Z.to_nat L_CODES)
                    + cost_L (fst p1) 256).
  { apply (g6_countL_to_freq ts toks (cost_L (fst p1)) HFL). }
  assert (EregD : wsum (fun i => t_freq (ts_trees ts TK_D) i
                          * cost_D (fst p2) i) 0 (Z.to_nat D_CODES)
                  = wsum (fun i => count_D i toks * cost_D (fst p2) i)
                      0 (Z.to_nat D_CODES)).
  { apply (g6_countD_to_freq ts toks (cost_D (fst p2)) HFD). }
  assert (Ereg : toks_cost (fst p1) (fst p2) toks
                 = wsum (fun i => count_L i toks * cost_L (fst p1) i)
                     0 (Z.to_nat L_CODES)
                   + wsum (fun i => count_D i toks * cost_D (fst p2) i)
                       0 (Z.to_nat D_CODES))
    by (apply toks_cost_regroup; exact Henc).
  assert (Ecost256 : cost_L (fst p1) 256 = t_len (fst p1) END_BLOCK).
  { rewrite g6_costL_vocab.
    change END_BLOCK with 256.
    unfold xbits.
    change (sd_extra_base TK_L) with 257.
    replace (257 <=? 256) with false by reflexivity.
    ring. }
  rewrite EregL in HL2.
  rewrite Ecost256 in HL2.
  rewrite EregD in HD2.
  (* --- assemble --- *)
  unfold S2P, S2M.
  fold BL'. fold BD'.
  rewrite EOL.
  unfold zho_bldesc, S2P.
  fold BL'. fold BD'.
  rewrite EtrL, EtrD, EtrB, EmcLf, EmcDf, EP.
  cbn [fst].
  rewrite Ereg.
  unfold OL. lia.
Qed.
