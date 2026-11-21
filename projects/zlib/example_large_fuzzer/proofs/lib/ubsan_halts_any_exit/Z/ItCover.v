(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSort.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma fillset : forall c l y s, 0 <= l <= c -> 0 <= y < 2 ^ c -> 0 <= s < 2 ^ l ->
  (y mod 2 ^ l = rev l s <-> rev c y / 2 ^ (c - l) = s).
Proof.
  intros c l y s Hl Hy Hs.
  assert (E0 : rev c y = rev (l + (c - l)) y) by (f_equal; lia). rewrite E0. rewrite rev_split by lia.
  pose proof (rev_bound (c - l) (y / 2 ^ l) ltac:(lia)) as B.
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia). rewrite (Z.div_small _ _ B). rewrite Z.add_0_r.
  pose proof (Z.mod_pos_bound y (2 ^ l) ltac:(apply pow2_pos; lia)) as M.
  split.
  - intros E. rewrite E. apply rev_rev; lia.
  - intros E. apply (rev_inj l); try lia; [apply rev_bound; lia|]. rewrite rev_rev by lia. exact E.
Qed.

Lemma in_progression : forall base l e x, 0 <= l -> 0 <= e -> 0 <= base < 2 ^ l ->
  0 <= x < 2 ^ (l + e) -> x mod 2 ^ l = base ->
  exists j, 0 <= j < 2 ^ e /\ x = base + j * 2 ^ l.
Proof.
  intros base l e x Hl He Hb Hx Hm. exists (x / 2 ^ l).
  pose proof (pow2_pos l Hl). pose proof (Z.div_mod x (2 ^ l) ltac:(lia)).
  rewrite Z.pow_add_r in Hx by lia.
  split; [|lia]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.


Section Cover.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1 HK".

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation Anext := (Anext wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).
  Local Notation GR := (GR wl root).
  Local Notation Pfx := (Pfx wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation used := (used wl root).
  Local Notation drop := (drop wl root).
  Local Notation wsym := (wsym wl ll).
  Local Notation fill_writes := (fill_writes wl ll root ty table).
  Local Notation link_writes := (link_writes wl root ty table).
  Local Notation trip_writes := (trip_writes wl ll root ty table).
  Local Notation trips_writes := (trips_writes wl ll root ty table).

  Lemma In_fill_writes : forall k i v, 0 <= len_at k - drop k <= curr k ->
    In (i, v) (fill_writes k) <->
    v = here wl ll root ty k /\
    exists j, 0 <= j < 2 ^ (curr k - (len_at k - drop k)) /\
              i = table + noff k + hf k / 2 ^ drop k + j * 2 ^ (len_at k - drop k).
  Proof.
    intros k i v Hk. unfold ItDefs.fill_writes. rewrite in_map_iff. split.
    - intros [j [E Hj]]. apply in_rev, in_seq in Hj. injection E; intros <- <-. split; [reflexivity|].
      exists (Z.of_nat j). split; [|reflexivity]. pose proof (Z.pow_nonneg 2 (curr k - (len_at k - drop k))). lia.
    - intros [-> [j [Hj ->]]]. exists (Z.to_nat j). split; [rewrite Z2Nat.id by lia; reflexivity|].
      apply (proj1 (in_rev (seq _ _) _)). apply in_seq. lia.
  Qed.

  Lemma In_link_writes : forall k i v,
    In (i, v) (link_writes k) <->
    k + 1 < NZ /\ newtable (k + 1) = true /\ it_not_enough ty (used (k + 1)) = false /\
    i = table + rev root (Pfx (k + 1)) /\ v = code_pack (curr (k + 1)) root (noff (k + 1)).
  Proof.
    intros k i v. unfold ItDefs.link_writes.
    destruct (Z.ltb_spec (k + 1) NZ) as [LT|GE]; destruct (newtable (k + 1)); destruct (it_not_enough ty (used (k + 1)));
      cbn [andb negb]; split.
    all: first [ solve [intros [HH|[]]; injection HH; intros <- <-; repeat split; try reflexivity; lia]
               | solve [intros (H1 & H2 & H3 & -> & ->); first [discriminate H2 | discriminate H3 | lia | (left; reflexivity)]]
               | solve [intros []] ].
  Qed.

  Lemma In_trips_writes : forall n p, 0 <= n ->
    In p (trips_writes n) <-> exists k, 0 <= k < n /\ In p (trip_writes k).
  Proof.
    intros n p Hn. unfold ItDefs.trips_writes. rewrite in_flat_map. split.
    - intros [j [Hj Hp]]. apply in_seq in Hj. exists (Z.of_nat j). split; [lia|exact Hp].
    - intros [k [Hk Hp]]. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. exact Hp.
  Qed.

  Lemma In_trip_writes : forall k p,
    In p (trip_writes k) <-> In p (fill_writes k) \/ In p (link_writes k).
  Proof. intros k p. unfold ItDefs.trip_writes. apply in_app_iff. Qed.


  Lemma newtable_unique : forall g g', 0 <= g < NZ -> 0 <= g' < NZ ->
    newtable g = true -> newtable g' = true -> Pfx g = Pfx g' -> g = g'.
  Proof.
    intros g g' Hg Hg' N N' E.
    assert (GEN : forall a b, 0 <= a < b -> b < NZ -> newtable a = true -> newtable b = true -> Pfx a = Pfx b -> False).
    { intros a b Hab Hb Na Nb Eab.
      pose proof (newtable_long wl HW HL root Hroot HM1 a Na) as La.
      pose proof (islong_mono wl HW HL root Hroot HM1 a (b - 1) ltac:(lia) ltac:(lia) La) as Lb1.
      pose proof (Pfx_mono wl HW HL root Hroot HM1 a (b - 1) ltac:(lia) ltac:(lia)) as M1.
      pose proof (Pfx_mono wl HW HL root Hroot HM1 (b - 1) b ltac:(lia) ltac:(lia)) as M2.
      unfold ItDefs.newtable in Nb. rewrite Lb1 in Nb. apply Bool.andb_true_iff in Nb as [_ Nb]. cbn [negb orb] in Nb.
      destruct (Z.eqb_spec (Pfx b) (Pfx (b - 1))); [discriminate Nb | lia]. }
    destruct (Z.lt_total g g') as [LT|[EQ|GT]]; [exfalso; apply (GEN g g'); auto; lia | exact EQ | exfalso; apply (GEN g' g); auto; lia].
  Qed.

  Lemma subtable_of : forall k x, 0 <= k < NZ -> 2 ^ root <= x < used k ->
    exists g, 0 <= g <= k /\ newtable g = true /\ noff g <= x < noff g + 2 ^ curr g.
  Proof.
    intros k x Hk. remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn Hx.
    - exfalso. replace k with 0 in Hx by lia. unfold ItDefs.used in Hx. rewrite (lay_0 wl HW HL root Hroot HM1) in Hx. cbn [snd] in Hx. lia.
    - destruct (newtable k) eqn:N.
      + pose proof (lay_S_new wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        destruct (LS N) as [En [Ec Eu]].
        pose proof (used_eq wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as UE.
        destruct (Z.lt_ge_cases x (used (k - 1))) as [LT|GE].
        * destruct (IH (k - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [g [G1 [G2 G3]]]. exists g. repeat split; try lia; assumption.
        * exists k. rewrite En. repeat split; try lia; try assumption.
      + pose proof (lay_S_same wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        assert (Eu : used k = used (k - 1)) by (unfold ItDefs.used; rewrite (LS N); reflexivity).
        destruct (IH (k - 1) ltac:(lia) ltac:(lia) ltac:(rewrite <- Eu; exact Hx)) as [g [G1 [G2 G3]]].
        exists g. repeat split; try lia; assumption.
  Qed.

  Lemma used_enough : it_not_enough ty (2 ^ root) = false ->
    (forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false) ->
    forall k, 0 <= k < NZ -> it_not_enough ty (used k) = false.
  Proof.
    intros H0 Hnf k Hk. remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn.
    - replace k with 0 by lia. unfold ItDefs.used. rewrite (lay_0 wl HW HL root Hroot HM1). cbn [snd]. exact H0.
    - destruct (newtable k) eqn:N.
      + specialize (Hnf (k - 1) ltac:(lia)). unfold ItDefs.fails_at in Hnf.
        replace (k - 1 + 1) with k in Hnf by lia. rewrite N in Hnf.
        destruct (Z.ltb_spec k NZ); [|lia]. cbn [andb] in Hnf. exact Hnf.
      + pose proof (lay_S_same wl HW HL root Hroot HM1 (k - 1) ltac:(lia)) as LS. replace (k - 1 + 1) with k in LS by lia.
        unfold ItDefs.used. rewrite (LS N). apply (IH (k - 1)); lia.
  Qed.


  Lemma hf_div_bound : forall k, 0 <= k < NZ -> 0 <= hf k / 2 ^ drop k < 2 ^ (len_at k - drop k).
  Proof.
    intros k Hk. rewrite (hf_spec wl HW HL HK k Hk).
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    assert (Hd : 0 <= drop k) by (unfold ItDefs.drop; pose proof (root_range wl HW HL root Hroot HM1); destruct (islong k); lia).
    rewrite rev_div by lia. apply rev_bound. lia.
  Qed.

  Lemma fill_writes_range : forall k i v, 0 <= k < NZ -> In (i, v) (fill_writes k) ->
    table + noff k <= i < table + noff k + 2 ^ curr k.
  Proof.
    intros k i v Hk Hin. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    apply (In_fill_writes k i v ltac:(lia)) in Hin as [_ [j [Hj ->]]].
    pose proof (hf_div_bound k Hk) as HB.
    set (l := len_at k - drop k) in *. set (e := curr k - l) in *.
    replace (curr k) with (l + e) by lia. rewrite Z.pow_add_r by lia.
    pose proof (pow2_pos l ltac:(lia)). pose proof (pow2_pos e ltac:(lia)). nia.
  Qed.

  Lemma used_noff_curr : forall k, 0 <= k < NZ -> noff k + 2 ^ curr k = used k.
  Proof. intros k Hk. symmetry. apply (used_eq wl HW HL root Hroot HM1 k Hk). Qed.

  Lemma trips_writes_range : forall n i v, 0 <= n <= NZ -> In (i, v) (trips_writes n) ->
    table <= i < table + used (NZ - 1).
  Proof.
    intros n i v Hn Hin. apply (In_trips_writes n (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof (used_mono wl HW HL root Hroot HM1 k (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (used_lower wl HW HL root Hroot HM1 (NZ - 1) ltac:(lia)) as UL.
    apply In_trip_writes in Hin as [Hin|Hin].
    - pose proof (fill_writes_range k i v ltac:(lia) Hin). pose proof (used_noff_curr k ltac:(lia)).
      pose proof (curr_range wl HW HL root Hroot HM1 k ltac:(lia)) as [_ [_ C3]]. lia.
    - apply In_link_writes in Hin as (Hk1 & N & _ & -> & _).
      pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
      pose proof (rev_bound root (Pfx (k + 1)) ltac:(lia)). lia.
  Qed.

  Hypothesis HC : TM MAXL = 2 ^ MAXL.
  Hypothesis Hnf : forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false.
  Hypothesis H0 : it_not_enough ty (2 ^ root) = false.
  #[local] Set Default Proof Using "HW HL Hroot HM1 HK HC Hnf H0".

  Lemma cover_root_short : forall x, 0 <= x < 2 ^ root -> rev root x * GR < TM root ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k).
  Proof.
    intros x Hx Hv. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (v := rev root x) in *. pose proof (rev_bound root x ltac:(lia)) as VB. fold v in VB.
    assert (Ht : 0 <= v * GR < TM MAXL) by (pose proof (TM_mono wl HW HL root MAXL ltac:(lia)); nia).
    destruct (find_code wl HW HL root Hroot HM1 (v * GR) Ht) as [k [Hk [A1 A2]]].
    pose proof (found_short wl HW HL root Hroot HM1 k Hk ltac:(lia)) as HS.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI HS) as [En [Ec Eu]].
    assert (Ed : drop k = 0) by (unfold ItDefs.drop; rewrite HS; reflexivity).
    pose proof HS as HS'. unfold ItDefs.islong in HS'. apply Z.ltb_ge in HS'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    pose proof (code_mul wl HW HL k Hk) as CM. unfold Anext in A2.
    assert (E2 : 2 ^ (MAXL - len_at k) = 2 ^ (root - len_at k) * GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hq : v / 2 ^ (root - len_at k) = code k).
    { pose proof (pow2_pos (root - len_at k) ltac:(lia)) as PP.
      assert (code k * 2 ^ (root - len_at k) <= v < (code k + 1) * 2 ^ (root - len_at k)) by nia.
      symmetry. apply Z.div_unique with (r := v - code k * 2 ^ (root - len_at k)); [left; lia | lia]. }
    exists k, (here wl ll root ty k). split; [exact Hk|].
    apply (In_fill_writes k); [rewrite Ed, Ec; lia|]. split; [reflexivity|].
    rewrite Ed, En, Ec. rewrite Z.sub_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
    rewrite (hf_spec wl HW HL HK k Hk).
    destruct (in_progression (rev (len_at k) (code k)) (len_at k) (root - len_at k) x) as [j [Hj Ej]]; try lia.
    - apply rev_bound. lia.
    - replace (len_at k + (root - len_at k)) with root by lia. exact Hx.
    - apply (proj2 (fillset root (len_at k) x (code k) ltac:(lia) Hx ltac:(lia))). exact Hq.
    - exists j. split; [exact Hj|]. lia.
  Qed.

  Lemma cover_root_link : forall x, 0 <= x < 2 ^ root -> TM root <= rev root x * GR ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (link_writes k).
  Proof.
    intros x Hx Hv. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (v := rev root x) in *. pose proof (rev_bound root x ltac:(lia)) as VB. fold v in VB.
    assert (HP : TM root / GR <= v < 2 ^ root).
    { split; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia. }
    destruct (prefix_has_group wl HW HL root Hroot HM1 HC v HP) as [g [Hg [N E]]].
    assert (Hg1 : 1 <= g).
    { destruct (Z.eq_dec g 0) as [->|]; [|lia]. exfalso.
      pose proof (newtable_long wl HW HL root Hroot HM1 0 N) as L0. unfold ItDefs.islong in L0.
      rewrite (len_at_0 wl HW HL HM1) in L0. apply Z.ltb_lt in L0. lia. }
    exists (g - 1), (code_pack (curr g) root (noff g)). split; [lia|].
    apply In_link_writes. replace (g - 1 + 1) with g by lia.
    split; [lia|]. split; [exact N|]. split; [apply used_enough; [exact H0 | exact Hnf | lia]|].
    split; [|reflexivity]. rewrite E. subst v. rewrite rev_rev by lia. reflexivity.
  Qed.

  Lemma cover_sub : forall x, 2 ^ root <= x < used (NZ - 1) ->
    exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k).
  Proof.
    intros x Hx. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    pose proof (NZ_pos wl HW HL HM1) as NP. pose proof (MAXL_spec wl HW HL) as [MM _].
    destruct (subtable_of (NZ - 1) x ltac:(lia) Hx) as [g [Hg [N R]]].
    pose proof (newtable_long wl HW HL root Hroot HM1 g N) as Lg.
    pose proof (lay_inv wl HW HL root Hroot HM1 g ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
    set (c := curr g) in *. set (y := x - noff g).
    assert (Hy : 0 <= y < 2 ^ c) by (subst y; lia).
    set (u := rev c y). pose proof (rev_bound c y ltac:(lia)) as UB. fold u in UB.
    set (P := Pfx g). set (t := P * GR + u * 2 ^ (MAXL - root - c)).
    assert (Eg : 2 ^ c * 2 ^ (MAXL - root - c) = GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    pose proof (group_start wl HW HL root Hroot HM1 g ltac:(lia) N) as GS. fold P in GS.
    assert (HP : TM root / GR <= P < 2 ^ root).
    { split.
      - pose proof (proj1 (islong_iff wl HW HL root Hroot HM1 g ltac:(lia)) Lg) as HK0.
        pose proof (K0_range wl HW HL root Hroot HM1) as KR. unfold K0 in KR.
        pose proof (Apos_K0 wl HW HL root Hroot HM1 ltac:(unfold K0; lia)) as AK. unfold K0 in AK.
        pose proof (Apos_mono wl HW HL (OFF wl (root + 1)) g ltac:(lia) ltac:(lia)) as AM. rewrite AK in AM.
        apply Z.div_le_upper_bound; [lia|]. lia.
      - apply (Pfx_bound wl HW HL root Hroot HM1 HK g ltac:(lia)). }
    assert (Ht : P * GR <= t < (P + 1) * GR).
    { subst t. pose proof (pow2_pos (MAXL - root - c) ltac:(lia)). nia. }
    destruct (in_group wl HW HL root Hroot HM1 HC P t HP Ht) as [j [Hj [Lj [Pj [A1 A2]]]]].
    destruct (group_of wl HW HL root Hroot HM1 j Hj Lj) as [g' [Hg' [N' [P' G4]]]].
    assert (Egg : g' = g) by (apply newtable_unique; try lia; try assumption; rewrite P', Pj; reflexivity).
    subst g'. destruct (G4 j ltac:(lia)) as [Elay [EP _]].
    assert (En : noff j = noff g) by (unfold ItDefs.noff; rewrite Elay; reflexivity).
    assert (Ec : curr j = c) by (unfold c, ItDefs.curr; rewrite Elay; reflexivity).
    assert (Ed : drop j = root) by (unfold ItDefs.drop; rewrite Lj; reflexivity).
    pose proof (lay_inv wl HW HL root Hroot HM1 j Hj) as [_ LJ]. destruct (LJ Lj) as (J1 & J2 & J3 & J4 & J5). rewrite Ec in J2.
    pose proof Lj as Lj'. unfold ItDefs.islong in Lj'. apply Z.ltb_lt in Lj'.
    pose proof (len_at_spec wl HW HL j Hj) as [L _]. pose proof (len_at_range wl HW HL j Hj) as LR.
    set (l := len_at j - root) in *.
    pose proof (Apos_decomp wl HW HL root Hroot HM1 j Hj Lj) as [D1 [D2 D3]]. fold l in D1, D2, D3. rewrite Pj in D1.
    set (sfx := code j mod 2 ^ l) in *. unfold Anext in A2.
    assert (E3 : 2 ^ (MAXL - len_at j) = 2 ^ (c - l) * 2 ^ (MAXL - root - c)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hq : u / 2 ^ (c - l) = sfx).
    { pose proof (pow2_pos (c - l) ltac:(lia)) as PP. pose proof (pow2_pos (MAXL - root - c) ltac:(lia)) as PQ.
      assert (sfx * 2 ^ (c - l) <= u < (sfx + 1) * 2 ^ (c - l)).
      { subst t. rewrite E3 in D1, A2. clear - A1 A2 D1 PP PQ. split; nia. }
      symmetry. apply Z.div_unique with (r := u - sfx * 2 ^ (c - l)); [left; lia | lia]. }
    exists j, (here wl ll root ty j). split; [exact Hj|].
    apply (In_fill_writes j); [rewrite Ed, Ec; lia|]. split; [reflexivity|].
    rewrite Ed, En, Ec. fold l.
    rewrite (hf_spec wl HW HL HK j Hj). pose proof (code_nonneg wl HW HL j Hj) as CN.
    rewrite rev_div by lia. fold l. fold sfx.
    destruct (in_progression (rev l sfx) l (c - l) y) as [m [Hm Em]]; try lia.
    - apply rev_bound. lia.
    - replace (l + (c - l)) with c by lia. exact Hy.
    - apply (proj2 (fillset c l y sfx ltac:(lia) Hy ltac:(lia))). exact Hq.
    - exists m. split; [exact Hm|]. subst y. lia.
  Qed.

  Theorem coverage : forall i, table <= i < table + used (NZ - 1) ->
    In i (map fst (trips_writes NZ)).
  Proof.
    intros i Hi. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (NZ_pos wl HW HL HM1) as NP.
    set (x := i - table). replace i with (table + x) by lia.
    assert (CASES : (exists k v, 0 <= k < NZ /\ In (table + x, v) (fill_writes k)) \/
                    (exists k v, 0 <= k < NZ /\ In (table + x, v) (link_writes k))).
    { destruct (Z.lt_ge_cases x (2 ^ root)) as [LT|GE].
      - destruct (Z.lt_ge_cases (rev root x * GR) (TM root)).
        + left. apply cover_root_short; lia.
        + right. apply cover_root_link; lia.
      - left. apply cover_sub. lia. }
    destruct CASES as [[k [v [Hk Hin]]]|[k [v [Hk Hin]]]];
      (eapply in_map_fst; apply (In_trips_writes NZ); [lia|]; exists k; split; [exact Hk|]; apply In_trip_writes); [left|right]; exact Hin.
  Qed.

  Lemma hf_NZ_complete : hf NZ = 0.
  Proof.
    pose proof (NZ_pos wl HW HL HM1) as NP. rewrite (hf_N wl HW HL) by lia.
    pose proof (Apos_last wl HW HL HM1) as AL. pose proof (code_mul wl HW HL (NZ - 1) ltac:(lia)) as CM.
    rewrite (len_at_last wl HW HL HM1) in *. rewrite Z.sub_diag in *. change (2 ^ 0) with 1 in *.
    destruct (Z.ltb_spec (code (NZ - 1) + 1) (2 ^ MAXL)); [lia|reflexivity].
  Qed.
End Cover.
