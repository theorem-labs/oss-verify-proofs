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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItShape.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Rep.
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

  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
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
  Local Notation lay := (lay wl root).
  Local Notation fill_writes := (fill_writes wl ll root ty table).
  Local Notation link_writes := (link_writes wl root ty table).
  Local Notation trip_writes := (trip_writes wl ll root ty table).
  Local Notation trips_writes := (trips_writes wl ll root ty table).
  Local Notation here := (here wl ll root ty).

  Let RR := root_range wl HW HL root Hroot HM1.
  Let GP := GR_pos wl HW HL root Hroot HM1.
  Let NP := NZ_pos wl HW HL HM1.


  Lemma fill_short_pos : forall k i v, 0 <= k < NZ -> islong k = false -> In (i, v) (fill_writes k) ->
    let x := i - table in
    0 <= x < 2 ^ root /\ v = here k /\ x mod 2 ^ len_at k = hf k /\ 0 <= hf k < 2 ^ len_at k /\ 1 <= len_at k <= root
    /\ Apos k <= rev root x * GR < Anext k.
  Proof.
    intros k i v Hk HS Hin.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI HS) as (En & Ec & Eu).
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (C1 & C2 & C3).
    assert (Ed : drop k = 0) by (unfold ItDefs.drop; rewrite HS; reflexivity).
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> [j [Hj Ei]]].
    rewrite Ed, En, Ec in *. rewrite Z.sub_0_r in *. change (2 ^ 0) with 1 in *. rewrite Z.div_1_r in *.
    pose proof HS as HS'. unfold ItDefs.islong in HS'. apply Z.ltb_ge in HS'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _].
    pose proof (hf_spec wl HW HL HK k Hk) as Ehf.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    assert (Hh : 0 <= hf k < 2 ^ len_at k) by (rewrite Ehf; apply rev_bound; lia).
    cbv zeta. set (x := i - table). assert (Ex : x = hf k + j * 2 ^ len_at k) by lia.
    pose proof (pow2_pos (len_at k) ltac:(lia)) as PL. pose proof (pow2_pos (root - len_at k) ltac:(lia)) as PRL.
    assert (Hx : 0 <= x < 2 ^ root).
    { rewrite Ex. split; [nia|]. replace root with (len_at k + (root - len_at k)) by lia. rewrite Z.pow_add_r by lia. nia. }
    assert (Hm : x mod 2 ^ len_at k = hf k).
    { rewrite Ex. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    split; [exact Hx|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hh|]. split; [lia|].
    pose proof (proj1 (fillset root (len_at k) x (code k) ltac:(lia) Hx ltac:(lia)) ltac:(rewrite Hm, Ehf; reflexivity)) as Hq.
    pose proof (rev_bound root x ltac:(lia)) as RB.
    pose proof (Z.div_mod (rev root x) (2 ^ (root - len_at k)) ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (rev root x) (2 ^ (root - len_at k)) ltac:(lia)) as MB.
    rewrite Hq in DM.
    pose proof (code_mul wl HW HL k Hk) as CM. unfold Anext.
    assert (E2 : 2 ^ (MAXL - len_at k) = 2 ^ (root - len_at k) * GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E2 in CM |- *. nia.
  Qed.

  Lemma long_group : forall k, 0 <= k < NZ -> islong k = true ->
    exists g, 0 <= g <= k /\ newtable g = true /\ Pfx g = Pfx k /\ lay k = lay g /\ islong g = true.
  Proof.
    intros k Hk HLg. destruct (group_of wl HW HL root Hroot HM1 k Hk HLg) as [g (Hg & N & P & G4)].
    destruct (G4 k ltac:(lia)) as (E1 & E2 & E3). exists g. repeat split; try assumption; try lia.
    apply (newtable_long wl HW HL root Hroot HM1). exact N.
  Qed.

  Lemma noff_new : forall g, 1 <= g < NZ -> newtable g = true -> noff g = used (g - 1).
  Proof.
    intros g Hg N. pose proof (lay_S_new wl HW HL root Hroot HM1 (g - 1) ltac:(lia)) as LS.
    replace (g - 1 + 1) with g in LS by lia. destruct (LS N) as (E1 & _ & _).
    rewrite E1. symmetry. apply (used_eq wl HW HL root Hroot HM1). lia.
  Qed.

  Lemma group_unique_by_cell : forall g g' x, 0 <= g < NZ -> 0 <= g' < NZ ->
    newtable g = true -> newtable g' = true ->
    noff g <= x < noff g + 2 ^ curr g -> noff g' <= x < noff g' + 2 ^ curr g' -> g = g'.
  Proof.
    intros g g' x Hg Hg' N N' R R'.
    assert (GEN : forall a b, 0 <= a < b -> b < NZ -> newtable a = true -> newtable b = true ->
                  noff a + 2 ^ curr a <= noff b).
    { intros a b Hab Hb Na Nb.
      assert (Hb1 : 1 <= b).
      { destruct (Z.eq_dec b 0) as [->|]; [|lia]. lia. }
      rewrite (noff_new b ltac:(lia) Nb).
      rewrite <- (used_eq wl HW HL root Hroot HM1 a ltac:(lia)).
      apply (used_mono wl HW HL root Hroot HM1); lia. }
    destruct (Z.lt_trichotomy g g') as [LT|[EQ|GT]]; [|exact EQ|].
    - pose proof (GEN g g' ltac:(lia) ltac:(lia) N N'). lia.
    - pose proof (GEN g' g ltac:(lia) ltac:(lia) N' N). lia.
  Qed.

  Lemma fill_long_pos : forall k i v, 0 <= k < NZ -> islong k = true -> In (i, v) (fill_writes k) ->
    let x := i - table in let l := len_at k - root in let y := x - noff k in
    2 ^ root <= noff k /\ noff k <= x < noff k + 2 ^ curr k /\ v = here k
    /\ 1 <= l <= curr k /\ root + curr k <= MAXL
    /\ y mod 2 ^ l = hf k / 2 ^ root /\ 0 <= hf k / 2 ^ root < 2 ^ l
    /\ Apos k <= Pfx k * GR + rev (curr k) y * 2 ^ (MAXL - root - curr k) < Anext k.
  Proof.
    intros k i v Hk HLg Hin.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [_ LI]. destruct (LI HLg) as (J1 & J2 & J3 & J4 & J5).
    assert (Ed : drop k = root) by (unfold ItDefs.drop; rewrite HLg; reflexivity).
    pose proof (fill_writes_range wl ll root ty table HW HL Hroot HM1 HK k i v Hk Hin) as FR.
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(rewrite Ed; lia)) in Hin as [-> [j [Hj Ei]]].
    rewrite Ed in *.
    pose proof HLg as HL'. unfold ItDefs.islong in HL'. apply Z.ltb_lt in HL'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (hf_spec wl HW HL HK k Hk) as Ehf.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    cbv zeta. set (x := i - table). set (l := len_at k - root) in *. set (y := x - noff k).
    pose proof (pow2_pos l ltac:(lia)) as PL. pose proof (pow2_pos (curr k - l) ltac:(lia)) as PCL.
    set (sfx := code k mod 2 ^ l).
    assert (Hsfx : 0 <= sfx < 2 ^ l) by (subst sfx; apply Z.mod_pos_bound; lia).
    assert (Ehd : hf k / 2 ^ root = rev l sfx).
    { rewrite Ehf. subst l sfx. rewrite rev_div by lia. reflexivity. }
    assert (Hhd : 0 <= hf k / 2 ^ root < 2 ^ l) by (rewrite Ehd; apply rev_bound; lia).
    assert (Ey : y = hf k / 2 ^ root + j * 2 ^ l) by (subst y x; lia).
    assert (Hy : 0 <= y < 2 ^ curr k).
    { rewrite Ey. split; [nia|]. replace (curr k) with (l + (curr k - l)) by lia. rewrite Z.pow_add_r by lia. nia. }
    assert (Hm : y mod 2 ^ l = hf k / 2 ^ root).
    { rewrite Ey. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    split; [exact J1|]. split; [subst y; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [exact Hm|]. split; [exact Hhd|].
    pose proof (proj1 (fillset (curr k) l y sfx ltac:(lia) Hy Hsfx) ltac:(rewrite Hm, Ehd; reflexivity)) as Hq.
    pose proof (rev_bound (curr k) y ltac:(lia)) as RB.
    pose proof (Z.div_mod (rev (curr k) y) (2 ^ (curr k - l)) ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (rev (curr k) y) (2 ^ (curr k - l)) ltac:(lia)) as MB.
    rewrite Hq in DM.
    pose proof (Apos_decomp wl HW HL root Hroot HM1 k Hk HLg) as (D1 & D2 & D3). fold l sfx in D1, D2, D3.
    unfold Anext.
    pose proof (pow2_pos (MAXL - root - curr k) ltac:(lia)) as PQ.
    assert (E3 : 2 ^ (MAXL - len_at k) = 2 ^ (curr k - l) * 2 ^ (MAXL - root - curr k)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E3 in D1 |- *. nia.
  Qed.

  Lemma link_pos : forall k i v, 0 <= k < NZ -> In (i, v) (link_writes k) ->
    let g := k + 1 in let x := i - table in
    g < NZ /\ newtable g = true /\ islong g = true /\ x = rev root (Pfx g) /\ 0 <= Pfx g < 2 ^ root /\ 0 <= x < 2 ^ root
    /\ v = code_pack (curr g) root (noff g) /\ rev root x * GR = Apos g.
  Proof.
    intros k i v Hk Hin. cbv zeta.
    apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v) in Hin as (Hk1 & N & _ & Ei & ->).
    pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) N) as Lg.
    pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as P0.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)) as P1.
    assert (Ex : i - table = rev root (Pfx (k + 1))) by lia.
    rewrite Ex. rewrite rev_rev by lia.
    repeat (split; [first [assumption | reflexivity | lia | apply rev_bound; lia] |]).
    symmetry. apply (group_start wl HW HL root Hroot HM1); [lia | exact N].
  Qed.


  Lemma short_before_long : forall k g, 0 <= k < NZ -> 0 <= g < NZ -> islong k = false -> islong g = true -> k < g.
  Proof.
    intros k g Hk Hg HS HLg. destruct (Z.lt_ge_cases k g) as [X|X]; [exact X|]. exfalso.
    rewrite (islong_mono wl HW HL root Hroot HM1 g k ltac:(lia) ltac:(lia) HLg) in HS. discriminate HS.
  Qed.

  Lemma interval_unique : forall k k' t, 0 <= k < NZ -> 0 <= k' < NZ ->
    Apos k <= t < Anext k -> Apos k' <= t < Anext k' -> k = k'.
  Proof.
    intros k k' t Hk Hk' A B.
    destruct (Z.lt_trichotomy k k') as [LT|[EQ|GT]]; [|exact EQ|]; exfalso.
    - pose proof (Apos_lt wl HW HL k k' ltac:(lia) ltac:(lia)). lia.
    - pose proof (Apos_lt wl HW HL k' k ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma fill_fill_unique : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (fill_writes k) -> In (i, v') (fill_writes k') -> k = k'.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    destruct (islong k) eqn:E; destruct (islong k') eqn:E'.
    -
      pose proof (fill_long_pos k i v Hk E Hin) as A. pose proof (fill_long_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & A2 & _ & A4 & A5 & _ & _ & A8). destruct B as (B1 & B2 & _ & B4 & B5 & _ & _ & B8).
      destruct (long_group k Hk E) as (g & Hg & N & P & Lk & Lg).
      destruct (long_group k' Hk' E') as (g' & Hg' & N' & P' & Lk' & Lg').
      assert (En : noff k = noff g /\ curr k = curr g) by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk; split; reflexivity).
      assert (En' : noff k' = noff g' /\ curr k' = curr g') by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk'; split; reflexivity).
      destruct En as [En Ec]. destruct En' as [En' Ec'].
      pose proof (group_unique_by_cell g g' (i - table) ltac:(lia) ltac:(lia) N N' ltac:(rewrite <- En, <- Ec; exact A2) ltac:(rewrite <- En', <- Ec'; exact B2)) as <-.
      rewrite <- P', P in B8. rewrite En', <- En in B8. rewrite Ec', <- Ec in B8.
      exact (interval_unique k k' _ Hk Hk' A8 B8).
    - exfalso. pose proof (fill_long_pos k i v Hk E Hin) as A. pose proof (fill_short_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & A2 & _). destruct B as (B1 & _). lia.
    - exfalso. pose proof (fill_short_pos k i v Hk E Hin) as A. pose proof (fill_long_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & _). destruct B as (B1 & B2 & _). lia.
    - pose proof (fill_short_pos k i v Hk E Hin) as A. pose proof (fill_short_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (_ & _ & _ & _ & _ & A6). destruct B as (_ & _ & _ & _ & _ & B6).
      exact (interval_unique k k' _ Hk Hk' A6 B6).
  Qed.

  Lemma fill_link_disjoint : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (fill_writes k) -> In (i, v') (link_writes k') -> False.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    pose proof (link_pos k' i v' Hk' Hin') as B. cbv zeta in B. destruct B as (G1 & N & Lg & Ex & HP & Hx & _ & Et).
    destruct (islong k) eqn:E.
    - pose proof (fill_long_pos k i v Hk E Hin) as A. cbv zeta in A. destruct A as (A1 & A2 & _). lia.
    - pose proof (fill_short_pos k i v Hk E Hin) as A. cbv zeta in A. destruct A as (_ & _ & _ & _ & _ & A6).
      rewrite Et in A6.
      pose proof (short_before_long k (k' + 1) Hk ltac:(lia) E Lg) as LT.
      pose proof (Apos_lt wl HW HL k (k' + 1) ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma link_link_unique : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (link_writes k) -> In (i, v') (link_writes k') -> k = k'.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    pose proof (link_pos k i v Hk Hin) as A. pose proof (link_pos k' i v' Hk' Hin') as B. cbv zeta in A, B.
    destruct A as (G1 & N & _ & Ex & HP & _). destruct B as (G1' & N' & _ & Ex' & HP' & _).
    assert (EP : Pfx (k + 1) = Pfx (k' + 1)).
    { apply (rev_inj root); lia. }
    pose proof (newtable_unique wl root HW HL Hroot HM1 HK (k + 1) (k' + 1) ltac:(lia) ltac:(lia) N N' EP). lia.
  Qed.

  Theorem writes_unique : forall n i v v', 0 <= n <= NZ ->
    In (i, v) (trips_writes n) -> In (i, v') (trips_writes n) -> v = v'.
  Proof.
    intros n i v v' Hn Hin Hin'.
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK n (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK n (i, v') ltac:(lia)) in Hin' as [k' [Hk' Hin']].
    apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin'.
    destruct Hin as [Hin|Hin]; destruct Hin' as [Hin'|Hin'].
    - pose proof (fill_fill_unique k k' i v v' ltac:(lia) ltac:(lia) Hin Hin') as <-.
      pose proof (curr_range wl HW HL root Hroot HM1 k ltac:(lia)) as (_ & C2 & _).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> _].
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v' ltac:(lia)) in Hin' as [-> _]. reflexivity.
    - exfalso. exact (fill_link_disjoint k k' i v v' ltac:(lia) ltac:(lia) Hin Hin').
    - exfalso. exact (fill_link_disjoint k' k i v' v ltac:(lia) ltac:(lia) Hin' Hin).
    - pose proof (link_link_unique k k' i v v' ltac:(lia) ltac:(lia) Hin Hin') as <-.
      apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v) in Hin as (_ & _ & _ & _ & ->).
      apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v') in Hin' as (_ & _ & _ & _ & ->). reflexivity.
  Qed.

  Lemma In_fill_trips : forall k p, 0 <= k < NZ -> In p (fill_writes k) -> In p (trips_writes NZ).
  Proof.
    intros k p Hk Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)).
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). left. exact Hin.
  Qed.
  Lemma In_link_trips : forall k p, 0 <= k < NZ -> In p (link_writes k) -> In p (trips_writes NZ).
  Proof.
    intros k p Hk Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)).
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). right. exact Hin.
  Qed.
  Lemma In_trips_cases : forall p, In p (trips_writes NZ) ->
    exists k, 0 <= k < NZ /\ (In p (fill_writes k) \/ In p (link_writes k)).
  Proof.
    intros p Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)) in Hin as [k [Hk Hin]].
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). exact Hin.
  Qed.

  Lemma here_bits : forall k, 0 <= k < NZ -> code_bits (here k) = len_at k - drop k.
  Proof.
    intros k Hk. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (C1 & C2 & C3).
    unfold ItDefs.here. destruct (entry ty (wsym wl ll k)) as [op val]. rewrite code_bits_pack. apply wrap8_small. lia.
  Qed.


  Theorem rep_root_w : forall x x' v,
    In (table + x, v) (trips_writes NZ) -> 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
    x' mod 2 ^ code_bits v = x mod 2 ^ code_bits v ->
    In (table + x', v) (trips_writes NZ).
  Proof.
    intros x x' v Hin Hx Hx' Hm.
    destruct (In_trips_cases _ Hin) as (k & Hk & [HinF|HinL]).
    - destruct (islong k) eqn:E.
      { pose proof (fill_long_pos k _ _ Hk E HinF) as A. cbv zeta in A. destruct A as (A1 & A2 & _). exfalso. lia. }
      pose proof (fill_short_pos k _ _ Hk E HinF) as A. cbv zeta in A.
      replace (table + x - table) with x in A by lia. destruct A as (_ & Ev & Hmx & Hh & Hl & _).
      assert (Eb : code_bits v = len_at k).
      { rewrite Ev, (here_bits k Hk). unfold ItDefs.drop. rewrite E. lia. }
      rewrite Eb in Hm. rewrite Hmx in Hm.
      destruct (in_progression (hf k) (len_at k) (root - len_at k) x' ltac:(lia) ltac:(lia) Hh ltac:(replace (len_at k + (root - len_at k)) with root by lia; exact Hx') Hm)
        as [j [Hj Ej]].
      apply (In_fill_trips k); [exact Hk|].
      pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI E) as (En & Ec & Eu).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k); [unfold ItDefs.drop; rewrite E, Ec; lia|].
      split; [exact Ev|]. exists j. unfold ItDefs.drop. rewrite E, En, Ec. rewrite Z.sub_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
      split; [exact Hj|lia].
    - pose proof (link_pos k _ _ Hk HinL) as A. cbv zeta in A. replace (table + x - table) with x in A by lia.
      destruct A as (G1 & N & Lg & Ex & HP & _ & Ev & _).
      assert (Eb : code_bits v = root) by (rewrite Ev, code_bits_pack; apply wrap8_small; lia).
      rewrite Eb in Hm. rewrite !Z.mod_small in Hm by lia. subst x'. apply (In_link_trips k); [exact Hk|exact HinL].
  Qed.


  Hypothesis HU : used (NZ - 1) < 65536.

  Theorem rep_sub_w : forall k x L y y' v,
    0 <= k < NZ -> In (table + x, L) (link_writes k) ->
    0 <= y < 2 ^ code_op L -> 0 <= y' < 2 ^ code_op L ->
    In (table + code_val L + y, v) (trips_writes NZ) ->
    y' mod 2 ^ code_bits v = y mod 2 ^ code_bits v ->
    In (table + code_val L + y', v) (trips_writes NZ).
  Proof using HW HL Hroot HM1 HK HU.
    intros k x L y y' v Hk HinL Hy Hy' Hin Hm.
    pose proof (link_pos k _ _ Hk HinL) as A. cbv zeta in A. destruct A as (G1 & N & Lg & _ & _ & _ & Ev & _).
    set (g := k + 1) in *.
    pose proof (lay_inv wl HW HL root Hroot HM1 g ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
    pose proof (used_mono wl HW HL root Hroot HM1 g (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (MAXL_spec wl HW HL) as [MM _].
    assert (Eop : code_op L = curr g) by (rewrite Ev, code_op_pack; apply wrap8_small; lia).
    assert (Eval : code_val L = noff g) by (rewrite Ev, code_val_pack; apply wrap16_small; pose proof (Z.pow_nonneg 2 (curr g)); lia).
    rewrite Eop in Hy, Hy'. rewrite Eval in Hin |- *.
    destruct (In_trips_cases _ Hin) as (k' & Hk' & [HinF|HinL']).
    2:{ exfalso. pose proof (link_pos k' _ _ Hk' HinL') as B. cbv zeta in B. destruct B as (_ & _ & _ & _ & _ & Bx & _). lia. }
    destruct (islong k') eqn:E'.
    2:{ exfalso. pose proof (fill_short_pos k' _ _ Hk' E' HinF) as B. cbv zeta in B. destruct B as (Bx & _). lia. }
    pose proof (fill_long_pos k' _ _ Hk' E' HinF) as B. cbv zeta in B.
    replace (table + noff g + y - table) with (noff g + y) in B by lia.
    destruct B as (B1 & B2 & Ev' & Bl & Bm & Bmod & Bh & _).
    destruct (long_group k' Hk' E') as (g' & Hg' & N' & P' & Lk' & Lg').
    assert (En' : noff k' = noff g' /\ curr k' = curr g') by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk'; split; reflexivity).
    destruct En' as [En' Ec'].
    pose proof (group_unique_by_cell g' g (noff g + y) ltac:(lia) ltac:(lia) N' N ltac:(rewrite <- En', <- Ec'; exact B2) ltac:(lia)) as Egg.
    subst g'. rewrite En' in *. rewrite Ec' in *.
    replace (noff g + y - noff g) with y in Bmod by lia.
    set (l := len_at k' - root) in *.
    assert (Eb : code_bits v = l) by (rewrite Ev', (here_bits k' Hk'); unfold ItDefs.drop; rewrite E'; reflexivity).
    rewrite Eb in Hm. rewrite Bmod in Hm.
    destruct (in_progression (hf k' / 2 ^ root) l (curr g - l) y' ltac:(lia) ltac:(lia) Bh ltac:(replace (l + (curr g - l)) with (curr g) by lia; exact Hy') Hm)
      as [j [Hj Ej]].
    apply (In_fill_trips k'); [exact Hk'|].
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k'); [unfold ItDefs.drop; rewrite E', Ec'; lia|].
    split; [exact Ev'|]. exists j. unfold ItDefs.drop. rewrite E', En', Ec'. fold l. split; [exact Hj|lia].
  Qed.
End Rep.


Lemma land240_small' : forall op, 0 <= op <= 15 -> Z.land op 240 = 0.
Proof.
  intros op H. destruct op as [|p|p]; [reflexivity| |lia].
  do 4 (destruct p as [p|p|]; [| |reflexivity]); cbn in H; lia.
Qed.

Section Rep2.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hns : NC ll <= nsyms ty.
  Hypothesis HU : used wl root (NZ wl - 1) < 65536.
  Let HW := HW' wl ll root ty Hll Ewl Hroot HM1 HK Hns HU.
  Let HL := HL' wl ll root ty Hll Ewl Hroot HM1 HK Hns HU.

  Lemma here_op_notlink : forall k, 0 <= k < NZ wl -> ~ (1 <= code_op (here wl ll root ty k) <= 15).
  Proof.
    intros k Hk H. pose proof (wsym_ok wl ll root ty Hll Ewl Hroot HM1 HK Hns HU k Hk) as [SR _].
    unfold ItDefs.here in H. destruct (entry ty (wsym wl ll k)) as [op val] eqn:E.
    rewrite code_op_pack in H.
    pose proof (entry_sym_entry ty (wsym wl ll k) ltac:(lia)) as [E1 _]. rewrite E in E1. cbn [fst] in E1. rewrite E1 in H.
    destruct (sym_entry_nolink ty (wsym wl ll k) SR) as [X|X]; [lia|].
    unfold may_link_op in X. rewrite (land240_small' (fst (sym_entry ty (wsym wl ll k))) ltac:(lia)) in X. cbn in X. discriminate X.
  Qed.

  Lemma root_link_write : forall x v,
    In (table + x, v) (trips_writes wl ll root ty table (NZ wl)) -> 0 <= x < 2 ^ root -> 1 <= code_op v <= 15 ->
    exists k, 0 <= k < NZ wl /\ In (table + x, v) (link_writes wl root ty table k).
  Proof.
    intros x v Hin Hx Hop.
    destruct (In_trips_cases wl ll root ty table HW HL Hroot HM1 HK _ Hin) as (k & Hk & [HinF|HinL]).
    - exfalso. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (_ & C2 & _).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k) in HinF as [-> _]; [|lia].
      exact (here_op_notlink k Hk Hop).
    - exists k. split; [exact Hk|exact HinL].
  Qed.
End Rep2.


Section AbsRep.
  Variable wl : list Z.
Variable ll : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hll Ewl Hbits".

  Let HW := ItTable.HWa wl ll bits Hll Ewl Hbits.
  Let HL := ItTable.HLa wl ll bits Hll Ewl Hbits.

  Definition REPW (ws : list (Z * Z)) (root toff : Z) : Prop :=
    (forall i v v', In (i, v) ws -> In (i, v') ws -> v = v')
    /\ (forall x x' v, In (table + x, v) ws -> 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
          x' mod 2 ^ code_bits v = x mod 2 ^ code_bits v -> In (table + x', v) ws)
    /\ (forall x L y y' v, In (table + x, L) ws -> 0 <= x < 2 ^ root -> 1 <= code_op L <= 15 ->
          0 <= y < 2 ^ code_op L -> 0 <= y' < 2 ^ code_op L ->
          table + 2 ^ root <= table + code_val L + y < toff
          /\ (In (table + code_val L + y, v) ws -> y' mod 2 ^ code_bits v = y mod 2 ^ code_bits v ->
              In (table + code_val L + y', v) ws)).

  Theorem it_abs_rep : forall ty, ty_ok ty ll bits ->
    let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
    ret = 0 -> REPW ws bits' toff.
  Proof.
    intros ty Hty. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (ItTable.nsyms_ok wl ll bits Hll Ewl Hbits ty Hty) as NS.
    assert (HR : 2 <= it_room ty) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia).
    unfold it_abs.
    destruct (Z.eqb_spec (MAXL wl) 0) as [HM0|HM0].
    {
      intros _. change (2 ^ 1) with 2. split; [|split].
      - intros i v v' A B. destruct A as [A|[A|[]]]; destruct B as [B|[B|[]]]; congruence.
      - intros x x' v A Hx Hx' _. assert (v = code_pack 64 1 0) as -> by (destruct A as [A|[A|[]]]; congruence).
        assert (x' = 0 \/ x' = 1) as [->| ->] by lia; [left; f_equal; lia|right; left; reflexivity].
      - intros x L y y' v A Hx HL0. exfalso.
        assert (L = code_pack 64 1 0) as -> by (destruct A as [A|[A|[]]]; congruence).
        rewrite code_op_pack, wrap8_small in HL0 by lia. lia. }
    assert (HM1 : 1 <= MAXL wl) by lia.
    pose proof (MINL_spec wl HW HL HM1) as [MA [MB MC]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HL0|HL0]; [intros X; discriminate X|].
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl) by lia.
    destruct ((0 <? LEFT wl) && (codetype_eqb ty CODES || negb (MAXL wl =? 1))) eqn:Hinc; [intros X; discriminate X|].
    set (root := ROOT wl bits).
    assert (RRg : MINL wl <= root <= MAXL wl) by (subst root; unfold ROOT; lia).
    pose proof (root_range wl HW HL root RRg HM1) as RR2.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [intros X; discriminate X|].
    unfold loop_abs.
    destruct (Z.ltb_spec (first_fail wl root ty) (NZ wl - 1)) as [FF|FF]; [intros X; discriminate X|].
    intros _.
    pose proof (NZ_pos wl HW HL HM1) as NP.
    assert (Hnf : forall k, 0 <= k < NZ wl - 1 -> fails_at wl root ty k = false).
    { intros k Hk. rewrite (ItTable.first_fail_eq wl ll bits Hll Ewl Hbits) in FF. apply (zsearch_before (fails_at wl root ty) 0 (Z.to_nat (NZ wl - 1))). lia. }
    pose proof (used_lower wl HW HL root RRg HM1 (NZ wl - 1) ltac:(lia)) as UL.
    pose proof (used_enough wl root ty HW HL RRg HM1 HK NE0 Hnf (NZ wl - 1) ltac:(lia)) as UE.
    assert (HU : 2 ^ root <= used wl root (NZ wl - 1) <= it_room ty).
    { split; [exact UL|]. destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (ty = CODES) as -> by (destruct ty; cbn in TC; congruence).
        destruct (ItTable.codes_short wl ll bits Hll Ewl Hbits Hty HM1) as [E7 M7]. fold root in E7.
        pose proof (lay_inv wl HW HL root RRg HM1 (NZ wl - 1) ltac:(lia)) as [LI _].
        assert (HS : islong wl root (NZ wl - 1) = false).
        { unfold islong. apply Z.ltb_ge. rewrite (len_at_last wl HW HL HM1). lia. }
        destruct (LI HS) as [_ [_ ->]]. cbn [it_room]. rewrite E7.
        change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
      - apply (ItTable.room_enough wl ll bits Hll Ewl Hbits); [exact UE|]. destruct ty; cbn in TC; congruence. }
    assert (HU2 : used wl root (NZ wl - 1) < 65536).
    { assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia). lia. }
    destruct (Z.eq_dec (LEFT wl) 0) as [HC0|HC0].
    -
      assert (HC : TM wl (MAXL wl) = 2 ^ MAXL wl) by (apply (proj1 LS2); exact HC0).
      unfold final_writes. rewrite (hf_NZ_complete wl root ty HW HL RRg HM1 HK HC Hnf NE0). cbn [Z.eqb]. rewrite app_nil_r.
      split; [|split].
      + intros i v v' A B. exact (writes_unique wl ll root ty table HW HL RRg HM1 HK (NZ wl) i v v' ltac:(lia) A B).
      + intros x x' v A Hx Hx' Hm. exact (rep_root_w wl ll root ty table HW HL RRg HM1 HK x x' v A Hx Hx' Hm).
      + intros x L y y' v A Hx HLo Hy Hy'.
        destruct (root_link_write wl ll root ty table Hll Ewl RRg HM1 HK NS HU2 x L A Hx HLo) as (k & Hk & HinL).
        pose proof (link_pos wl root ty table HW HL RRg HM1 HK k _ _ Hk HinL) as B. cbv zeta in B.
        destruct B as (G1 & N & Lg & _ & _ & _ & Ev & _).
        pose proof (lay_inv wl HW HL root RRg HM1 (k + 1) ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
        pose proof (used_mono wl HW HL root RRg HM1 (k + 1) (NZ wl - 1) ltac:(lia) ltac:(lia)) as UM.
        assert (Eop : code_op L = curr wl root (k + 1)) by (rewrite Ev, code_op_pack; apply wrap8_small; lia).
        assert (Eval : code_val L = noff wl root (k + 1)) by (rewrite Ev, code_val_pack; apply wrap16_small; pose proof (Z.pow_nonneg 2 (curr wl root (k + 1))); lia).
        split; [rewrite Eval; rewrite Eop in Hy; lia|].
        intros B Hm. exact (rep_sub_w wl ll root ty table HW HL RRg HM1 HK HU2 k x L y y' v Hk HinL Hy Hy' B Hm).
    -
      assert (HLp : 0 < LEFT wl) by lia.
      destruct (Z.ltb_spec 0 (LEFT wl)); [|lia]. cbn [andb] in Hinc. apply Bool.orb_false_iff in Hinc as [TC HMx].
      apply Bool.negb_false_iff in HMx. apply Z.eqb_eq in HMx.
      destruct (ItTable.incomplete_facts wl ll bits Hll Ewl Hbits HLp HMx) as (Emin & W1 & NZ1 & R1 & _). fold root in R1.
      unfold final_writes. rewrite NZ1 in *. change (1 - 1) with 0 in *.
      pose proof (lay_0 wl HW HL root RRg HM1) as L0.
      assert (E0 : noff wl root 0 = 0 /\ curr wl root 0 = root /\ used wl root 0 = 2 ^ root).
      { unfold noff, curr, used. rewrite L0. repeat split; reflexivity. }
      destruct E0 as (En & Ec & Eu).
      pose proof (len_at_0 wl HW HL HM1) as EL. rewrite Emin in EL.
      assert (Ed : drop wl root 0 = 0) by (unfold drop, islong; rewrite EL, R1; reflexivity).
      assert (Ehf0 : hf wl 0 = 0) by reflexivity.
      assert (Ehf1 : hf wl 1 = 1).
      { unfold ItDefs.hf. cbn [Z.eqb]. change (1 - 1) with 0. rewrite (code_0 wl HW HL HM1), EL. reflexivity. }
      rewrite Ehf1. cbn [Z.eqb]. assert (P2 : 2 ^ root = 2) by (rewrite R1; reflexivity).
      rewrite ?Eu, ?En, ?EL, ?Ed, ?P2 in *.
      assert (ET : trips_writes wl ll root ty table 1 = fill_writes wl ll root ty table 0).
      { unfold trips_writes. change (Z.to_nat 1) with 1%nat. cbn [seq flat_map]. rewrite app_nil_r.
        change (Z.of_nat 0) with 0. unfold trip_writes, link_writes. rewrite NZ1. cbn [Z.add Z.ltb andb]. apply app_nil_r. }
      rewrite ET.
      assert (HF : forall i v, In (i, v) (fill_writes wl ll root ty table 0) <-> i = table /\ v = here wl ll root ty 0).
      { intros i v. rewrite (In_fill_writes wl ll root ty table HW HL RRg HM1 HK 0 i v) by (rewrite EL, Ed, Ec, R1; lia).
        rewrite EL, Ed, Ec, En, Ehf0, R1. change (2 ^ (1 - (1 - 0))) with 1. change (2 ^ 0) with 1. change (0 / 1) with 0.
        split.
        - intros [-> [j [Hj ->]]]. split; [lia|reflexivity].
        - intros [-> ->]. split; [reflexivity|]. exists 0. lia. }
      assert (Hb0 : code_bits (here wl ll root ty 0) = 1).
      { rewrite (here_bits wl ll root ty HW HL RRg HM1 HK 0 ltac:(lia)). rewrite EL, Ed. reflexivity. }
      assert (Hop0 : ~ (1 <= code_op (here wl ll root ty 0) <= 15)).
      { apply (here_op_notlink wl ll root ty Hll Ewl RRg HM1 HK NS); [rewrite NZ1; change (1 - 1) with 0; rewrite Eu; lia | rewrite NZ1; lia]. }
      assert (CASES : forall i v, In (i, v) (fill_writes wl ll root ty table 0 ++ [(table + 0 + 1, code_pack 64 (1 - 0) 0)]) ->
                      (i = table /\ v = here wl ll root ty 0) \/ (i = table + 0 + 1 /\ v = code_pack 64 1 0)).
      { intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]]; [left; apply HF; exact Hin | right]. injection Hin; intros E1 E2. rewrite <- E1, <- E2. split; reflexivity. }
      split; [|split].
      + intros i v v' A B. destruct (CASES _ _ A) as [[-> ->]|[-> ->]]; destruct (CASES _ _ B) as [[X ->]|[X ->]]; try reflexivity; lia.
      + intros x x' v A Hx Hx' Hm. rewrite R1 in Hx, Hx'. change (2 ^ 1) with 2 in Hx, Hx'.
        destruct (CASES _ _ A) as [[X ->]|[X ->]].
        * rewrite Hb0 in Hm. change (2 ^ 1) with 2 in Hm. rewrite !Z.mod_small in Hm by lia.
          apply in_app_iff. left. apply HF. split; [lia|reflexivity].
        * rewrite code_bits_pack in Hm. change (2 ^ wrap8 1) with 2 in Hm. rewrite !Z.mod_small in Hm by lia.
          apply in_app_iff. right. left. f_equal. lia.
      + intros x L y y' v A Hx HLo. exfalso. destruct (CASES _ _ A) as [[X ->]|[X ->]].
        * exact (Hop0 HLo).
        * rewrite code_op_pack, wrap8_small in HLo by lia. lia.
  Qed.
End AbsRep.
