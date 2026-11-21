(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition trip_cnt (mn q p k x : Z) : Z :=
  if k <? mn then (if x =? q then k else 0)
  else if negb (q =? 0) then (if negb (q =? p) then zind (x =? q) else 0) + zind (x =? REP_3_6)
  else if k <=? 10 then zind (x =? REPZ_3_10)
  else zind (x =? REPZ_11_138).

(* [comment removed for export] *)
Definition trip_cost (BD : Z -> Z) (mn q p k : Z) : Z :=
  if k <? mn then k * BD q
  else if negb (q =? 0) then (if negb (q =? p) then BD q else 0) + BD REP_3_6 + 2
  else if k <=? 10 then BD REPZ_3_10 + 3
  else BD REPZ_11_138 + 7.

Lemma trip_cnt_nonneg : forall mn q p k x, 0 <= k -> 0 <= trip_cnt mn q p k x.
Proof.
  intros. unfold trip_cnt. pose proof (zind_le1 (x =? q)). pose proof (zind_le1 (x =? REP_3_6)).
  pose proof (zind_le1 (x =? REPZ_3_10)). pose proof (zind_le1 (x =? REPZ_11_138)).
  destruct (k <? mn); [destruct (x =? q); lia|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); lia|]. destruct (k <=? 10); lia.
Qed.

Lemma trip_cnt_out : forall mn q p k x, x <> q -> x <> REP_3_6 -> x <> REPZ_3_10 -> x <> REPZ_11_138 -> trip_cnt mn q p k x = 0.
Proof.
  intros mn q p k x A B C D. unfold trip_cnt.
  replace (x =? q) with false by (symmetry; apply Z.eqb_neq; exact A).
  replace (x =? REP_3_6) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (x =? REPZ_3_10) with false by (symmetry; apply Z.eqb_neq; exact C).
  replace (x =? REPZ_11_138) with false by (symmetry; apply Z.eqb_neq; exact D). cbn [zind].
  destruct (k <? mn); [reflexivity|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); reflexivity|]. destruct (k <=? 10); reflexivity.
Qed.

Lemma trip_cnt_le : forall mn q p k x, 0 <= k -> trip_cnt mn q p k x <= (if k <? mn then k else 2).
Proof.
  intros. unfold trip_cnt. pose proof (zind_le1 (x =? q)). pose proof (zind_le1 (x =? REP_3_6)).
  pose proof (zind_le1 (x =? REPZ_3_10)). pose proof (zind_le1 (x =? REPZ_11_138)).
  destruct (k <? mn); [destruct (x =? q); lia|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); lia|]. destruct (k <=? 10); lia.
Qed.

(* [comment removed for export] *)
Lemma trip_cost_cnt : forall BD mn q p k, 0 <= q <= 15 ->
  trip_cost BD mn q p k = zsum (fun x => trip_cnt mn q p k x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  intros BD mn q p k Hq.
  assert (XB : forall x, 0 <= x <= 15 -> arr_get extra_blbits_a x = 0).
  { intros x Hx. assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15) by lia.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H]; [reflexivity|] end. subst; reflexivity. }
  assert (X16 : arr_get extra_blbits_a REP_3_6 = 2) by reflexivity.
  assert (X17 : arr_get extra_blbits_a REPZ_3_10 = 3) by reflexivity.
  assert (X18 : arr_get extra_blbits_a REPZ_11_138 = 7) by reflexivity.
  unfold trip_cost, trip_cnt, REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (k <? mn).
  - rewrite (zsum_single (fun x => (if x =? q then k else 0) * (BD x + arr_get extra_blbits_a x)) 0 19 q) by
      (try lia; intros i Hi Ni; replace (i =? q) with false by (symmetry; apply Z.eqb_neq; exact Ni); lia).
    rewrite Z.eqb_refl, (XB q Hq). lia.
  - destruct (negb (q =? 0)).
    + transitivity (zsum (fun x => (if negb (q =? p) then zind (x =? q) else 0) * (BD x + arr_get extra_blbits_a x)
                              + zind (x =? 16) * (BD x + arr_get extra_blbits_a x)) 0 19); [| apply zsum_ext; intros; lia].
      rewrite zsum_add.
      rewrite (zsum_single (fun x => zind (x =? 16) * (BD x + arr_get extra_blbits_a x)) 0 19 16) by
        (try lia; intros i Hi Ni; replace (i =? 16) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
      rewrite Z.eqb_refl, X16. cbn [zind].
      destruct (negb (q =? p)).
      * rewrite (zsum_single (fun x => zind (x =? q) * (BD x + arr_get extra_blbits_a x)) 0 19 q) by
          (try lia; intros i Hi Ni; replace (i =? q) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, (XB q Hq). cbn [zind]. lia.
      * rewrite zsum_0 by (intros; lia). lia.
    + destruct (k <=? 10).
      * rewrite (zsum_single (fun x => zind (x =? 17) * (BD x + arr_get extra_blbits_a x)) 0 19 17) by
          (try lia; intros i Hi Ni; replace (i =? 17) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, X17. cbn [zind]. lia.
      * rewrite (zsum_single (fun x => zind (x =? 18) * (BD x + arr_get extra_blbits_a x)) 0 19 18) by
          (try lia; intros i Hi Ni; replace (i =? 18) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, X18. cbn [zind]. lia.
Qed.

(* [comment removed for export] *)
Lemma st_upd_cnt : forall mn b q p k x,
  0 <= q <= 15 -> 19 <= arr_len b -> 0 <= k ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) -> (forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p k y < 65536) ->
  arr_get (st_upd mn b q p k) x = arr_get b x + trip_cnt mn q p k x.
Proof.
  intros mn b q p k x Hq Hb Hk H0 HB.
  assert (G : forall a i v y, 0 <= i < arr_len a -> 0 <= v < 65536 ->
             arr_get (arr_set a i (wrap16 v)) y = if y =? i then v else arr_get a y).
  { intros a i v y Hi Hv. rewrite arr_get_set. unfold arr_inb.
    replace ((0 <=? i) && (i <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite (Z.eqb_sym i y). destruct (y =? i); cbn [andb]; [apply wrap16_id; lia | reflexivity]. }
  assert (T : forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p k y < 65536 /\ 0 <= arr_get b y) by (intros y Hy; split; [apply HB | apply H0]; exact Hy).
  unfold st_upd, trip_cnt in *. unfold REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (k <? mn) eqn:E1.
  - pose proof (T q ltac:(lia)) as Tq. rewrite Z.eqb_refl in Tq. rewrite G by lia. destruct (Z.eqb_spec x q) as [->|N]; lia.
  - destruct (negb (q =? 0)) eqn:E2.
    + pose proof (T 16 ltac:(lia)) as T16. rewrite Z.eqb_refl in T16.
      destruct (negb (q =? p)) eqn:E3.
      * pose proof (T q ltac:(lia)) as Tq. rewrite Z.eqb_refl in Tq.
        assert (Nq1 : (q =? 16) = false) by (apply Z.eqb_neq; lia). assert (Nq2 : (16 =? q) = false) by (apply Z.eqb_neq; lia).
        rewrite Nq1 in Tq. rewrite Nq2 in T16. cbn [zind Z.add] in Tq, T16.
        assert (I16 : arr_get (arr_set b q (wrap16 (arr_get b q + 1))) 16 = arr_get b 16) by (rewrite (G b q (arr_get b q + 1) 16) by lia; rewrite Nq2; reflexivity).
        rewrite (G (arr_set b q (wrap16 (arr_get b q + 1))) 16 _ x); [| rewrite arr_len_set; lia | rewrite I16; lia].
        rewrite I16. rewrite (G b q (arr_get b q + 1) x) by lia.
        destruct (Z.eqb_spec x 16) as [->|N16]; [rewrite Nq2; cbn [zind]; lia|].
        destruct (Z.eqb_spec x q) as [->|Nxq]; cbn [zind]; lia.
      * cbn [zind Z.add] in T16. rewrite G by lia. destruct (Z.eqb_spec x 16) as [->|N16]; cbn [zind]; lia.
    + destruct (k <=? 10) eqn:E4.
      * pose proof (T 17 ltac:(lia)) as T17. rewrite Z.eqb_refl in T17. cbn [zind] in T17. rewrite G by lia. destruct (Z.eqb_spec x 17) as [->|N]; cbn [zind]; lia.
      * pose proof (T 18 ltac:(lia)) as T18. rewrite Z.eqb_refl in T18. cbn [zind] in T18. rewrite G by lia. destruct (Z.eqb_spec x 18) as [->|N]; cbn [zind]; lia.
Qed.

(* [comment removed for export] *)
Lemma st_calls_clen : forall s mn q p k, 1 <= k ->
  clen (st_calls s mn q p k) = trip_cost (fun x => Len s TB x) mn q p k.
Proof.
  intros s mn q p k Hk. unfold st_calls, trip_cost, blc.
  destruct (k <? mn); [rewrite clen_repeat; cbn [snd]; lia|].
  destruct (negb (q =? 0)); [destruct (negb (q =? p)); cbn [clen app]; lia|].
  destruct (k <=? 10); cbn [clen]; lia.
Qed.

Lemma st_calls_lens : forall s mn q p k,
  (forall x, 0 <= x < 19 -> 0 <= Len s TB x <= 16) -> 0 <= q <= 15 ->
  Forall (fun c => 0 <= snd c <= 16) (st_calls s mn q p k).
Proof.
  intros s mn q p k HB Hq. unfold st_calls, blc.
  destruct (k <? mn).
  - apply Forall_forall. intros c Hc. apply repeat_spec in Hc. subst c. cbn. apply HB. lia.
  - destruct (negb (q =? 0)).
    + destruct (negb (q =? p)); cbn [app]; repeat constructor; cbn; try lia; try (apply HB; unfold REP_3_6; lia).
    + destruct (k <=? 10); repeat constructor; cbn; try lia; apply HB; unfold REPZ_3_10, REPZ_11_138; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint td_cnt (L : Z -> Z) (mc : Z) (fuel : nat) (n p q k mx mn : Z) (x : Z) : Z :=
  match fuel with
  | O => 0
  | S f =>
      if n <=? mc then
        let nl := L (n + 1) in
        let k' := k + 1 in
        if (k' <? mx) && (q =? nl) then td_cnt L mc f (n + 1) p nl k' mx mn x
        else let '(mx', mn') := tree_counts q nl in
             trip_cnt mn q p k' x + td_cnt L mc f (n + 1) q nl 0 mx' mn' x
      else 0
  end.

Fixpoint td_cost (BD L : Z -> Z) (mc : Z) (fuel : nat) (n p q k mx mn : Z) : Z :=
  match fuel with
  | O => 0
  | S f =>
      if n <=? mc then
        let nl := L (n + 1) in
        let k' := k + 1 in
        if (k' <? mx) && (q =? nl) then td_cost BD L mc f (n + 1) p nl k' mx mn
        else let '(mx', mn') := tree_counts q nl in
             trip_cost BD mn q p k' + td_cost BD L mc f (n + 1) q nl 0 mx' mn'
      else 0
  end.

(* [comment removed for export] *)
Definition lens_ok (L : Z -> Z) (n mc : Z) : Prop := forall i, n < i <= mc -> 0 <= L i <= 15.

Lemma td_cnt_nonneg : forall L mc f n p q k mx mn x, 0 <= k -> 0 <= td_cnt L mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros; cbn [td_cnt]; [lia|].
  destruct (n <=? mc); [|lia]. cbv zeta. destruct (_ && _); [apply IH; lia|].
  destruct (tree_counts _ _). pose proof (trip_cnt_nonneg mn q p (k + 1) x ltac:(lia)). specialize (IH (n + 1) q (L (n + 1)) 0). pose proof (IH). 
  match goal with |- 0 <= _ + ?r => assert (0 <= r) by (apply IH; lia) end. lia.
Qed.

(* [comment removed for export] *)
Lemma td_cnt_le : forall L mc f n p q k mx mn x, 0 <= k -> 0 <= n ->
  td_cnt L mc f n p q k mx mn x <= k + 2 * (Z.max 0 (mc + 1 - n)).
Proof.
  induction f as [|f IH]; intros n p q k mx mn x Hk Hn; cbn [td_cnt]; [lia|].
  destruct (Z.leb_spec n mc); [|lia]. cbv zeta. destruct (_ && _).
  - specialize (IH (n + 1) p (L (n + 1)) (k + 1) mx mn x ltac:(lia) ltac:(lia)). lia.
  - destruct (tree_counts _ _) as [mx' mn']. pose proof (trip_cnt_le mn q p (k + 1) x ltac:(lia)).
    specialize (IH (n + 1) q (L (n + 1)) 0 mx' mn' x ltac:(lia) ltac:(lia)).
    destruct (k + 1 <? mn); lia.
Qed.

Lemma td_cnt_out : forall L mc f n p q k mx mn x,
  lens_ok L n mc -> 0 <= q <= 15 -> (x < 0 \/ 19 <= x) -> td_cnt L mc f n p q k mx mn x = 0.
Proof.
  induction f as [|f IH]; intros n p q k mx mn x HL Hq Hx; cbn [td_cnt]; [reflexivity|].
  destruct (Z.leb_spec n mc); [|reflexivity]. cbv zeta.
  destruct (Z.eq_dec n mc) as [En|Nn].
  - (* [comment removed for export] *)
    destruct (_ && _).
    + cbn [td_cnt]. destruct f; [reflexivity|]. cbn [td_cnt]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + destruct (tree_counts _ _). rewrite trip_cnt_out by (unfold REP_3_6, REPZ_3_10, REPZ_11_138; lia).
      destruct f; [reflexivity|]. cbn [td_cnt]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - pose proof (HL (n + 1) ltac:(lia)) as Hl.
    destruct (_ && _).
    + apply IH; [intros i Hi; apply HL; lia | exact Hl | exact Hx].
    + destruct (tree_counts _ _). rewrite trip_cnt_out by (unfold REP_3_6, REPZ_3_10, REPZ_11_138; lia).
      rewrite IH; [lia | intros i Hi; apply HL; lia | exact Hl | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma td_cost_cnt : forall BD L mc f n p q k mx mn,
  lens_ok L n mc -> 0 <= q <= 15 ->
  td_cost BD L mc f n p q k mx mn = zsum (fun x => td_cnt L mc f n p q k mx mn x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  induction f as [|f IH]; intros n p q k mx mn HL Hq; cbn [td_cost td_cnt].
  - symmetry. apply zsum_0. intros; lia.
  - destruct (Z.leb_spec n mc); [| symmetry; apply zsum_0; intros; lia]. cbv zeta.
    destruct (Z.eq_dec n mc) as [En|Nn].
    + (* [comment removed for export] *)
      destruct (_ && _).
      * destruct f; cbn [td_cost td_cnt]; [symmetry; apply zsum_0; intros; lia|].
        replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). symmetry; apply zsum_0; intros; lia.
      * destruct (tree_counts _ _) as [mx' mn']. rewrite trip_cost_cnt by exact Hq.
        assert (R0 : td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' = 0 /\ forall x, td_cnt L mc f (n + 1) q (L (n + 1)) 0 mx' mn' x = 0).
        { destruct f; cbn [td_cost td_cnt]; [split; intros; reflexivity|].
          replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). split; intros; reflexivity. }
        destruct R0 as [A B]. rewrite A, Z.add_0_r. apply zsum_ext. intros x Hx. rewrite B. lia.
    + pose proof (HL (n + 1) ltac:(lia)) as Hl.
      assert (HL' : lens_ok L (n + 1) mc) by (intros i Hi; apply HL; lia).
      destruct (_ && _).
      * apply IH; assumption.
      * destruct (tree_counts _ _). rewrite trip_cost_cnt by exact Hq. rewrite (IH (n + 1) q (L (n + 1)) 0) by assumption.
        rewrite <- zsum_add. apply zsum_ext. intros; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scan_loop_cnt : forall f s0 b t mc n p q k mx mn,
  t <> TB -> lens_ok (fun i => Len s0 t i) n mc -> 0 <= q <= 15 -> 0 <= k -> 0 <= n -> 39 <= arr_len b ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) ->
  (forall y, 0 <= y < 19 -> arr_get b y + (k + 2 * Z.max 0 (mc + 1 - n)) < 65536) ->
  exists b', scan_tree_loop f (set_bl_tree_fc s0 b) t mc n p q k mx mn = set_bl_tree_fc s0 b'
    /\ arr_len b' = arr_len b
    /\ forall x, arr_get b' x = arr_get b x + td_cnt (fun i => Len s0 t i) mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros s0 b t mc n p q k mx mn Ht HL Hq Hk Hn Hb H0 HB.
  - exists b. rewrite scan_loop_0. split; [reflexivity|]. split; [reflexivity|]. intros; cbn; lia.
  - rewrite scan_loop_S. cbn [td_cnt]. destruct (Z.leb_spec n mc); [| exists b; split; [reflexivity|]; split; [reflexivity|]; intros; lia]. cbv zeta.
    destruct (Z.eq_dec n mc) as [En|Nn].
    + (* [comment removed for export] *)
      destruct (_ && _).
      * exists b. rewrite scan_loop_out by lia. split; [reflexivity|]. split; [reflexivity|]. intros x.
        destruct f; cbn [td_cnt]; [lia|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). lia.
      * destruct (tree_counts _ _) as [mx' mn'].
        exists (st_upd mn b q p (k + 1)). rewrite scan_loop_out by lia. split; [reflexivity|]. split; [apply st_upd_len|]. intros x.
        rewrite st_upd_cnt; [| lia | lia | lia | exact H0 |].
        2:{ intros y Hy. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        destruct f; cbn [td_cnt]; [lia|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). lia.
    + pose proof (HL (n + 1) ltac:(lia)) as Hl. assert (HL' : lens_ok (fun i => Len s0 t i) (n + 1) mc) by (intros i Hi; apply HL; lia).
      destruct (_ && _).
      * apply IH; try assumption; try lia. intros y Hy. pose proof (HB y Hy). lia.
      * destruct (tree_counts _ _) as [mx' mn'].
        assert (TB' : forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p (k + 1) y < 65536).
        { intros y Hy. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        destruct (IH s0 (st_upd mn b q p (k + 1)) t mc (n + 1) q (Len s0 t (n + 1)) 0 mx' mn' Ht HL' Hl ltac:(lia) ltac:(lia)) as (b' & E & Lb & Gb).
        { rewrite st_upd_len. lia. }
        { intros y Hy. rewrite st_upd_cnt; try lia; try assumption. pose proof (H0 y Hy). pose proof (trip_cnt_nonneg mn q p (k + 1) y ltac:(lia)). lia. }
        { intros y Hy. rewrite st_upd_cnt; try lia; try assumption. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        exists b'. split; [exact E|]. rewrite st_upd_len in Lb. split; [exact Lb|]. intros x. rewrite Gb, st_upd_cnt; try lia; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma send_loop_facts : forall f (L BD : Z -> Z) s t mc n p q k mx mn,
  (forall i, Len s t i = L i) -> (forall x, Len s TB x = BD x) ->
  1 <= mn -> 0 <= k -> lens_ok L n mc -> 0 <= q <= 15 ->
  (forall x, 0 <= x < 19 -> 0 <= BD x <= 16) -> 0 <= ds_bi_valid s <= 16 ->
  let s' := send_tree_loop f s t mc n p q k mx mn in
  ov_W s' = ov_W s + td_cost BD L mc f n p q k mx mn
  /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s')
  /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
  /\ (forall PBL, ov_W s' <= 8 * PBL -> send_tree_ok PBL f s t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros L BD s t mc n p q k mx mn ELn EBD Hmn Hk HL Hq HB Hbv s'; subst s'.
  - rewrite send_loop_0. cbn [td_cost send_tree_ok]. repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end.
  - rewrite send_loop_S by exact Hmn. cbn [td_cost send_tree_ok].
    destruct (Z.leb_spec n mc); [| repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end]. cbv zeta.
    rewrite !ELn.
    assert (HBs : forall x, 0 <= x < 19 -> 0 <= Len s TB x <= 16) by (intros x Hx; rewrite EBD; apply HB; exact Hx).
    assert (TRIP : forall mx' mn', 1 <= mn' -> 0 <= L (n + 1) <= 15 \/ n = mc ->
      let cs := st_calls s mn q p (k + 1) in
      let s1 := sbs_run s cs in
      let s' := send_tree_loop f s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn' in
      ov_W s' = ov_W s + (trip_cost BD mn q p (k + 1) + td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn')
      /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
      /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
      /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
      /\ (PBB s -> PBB s')
      /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
      /\ (forall PBL, ov_W s' <= 8 * PBL -> sbs_ok PBL s cs /\ send_tree_ok PBL f s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn')).
    { intros mx' mn' Hmn' Hl cs s1 s'. subst s'.
      pose proof (st_calls_lens s mn q p (k + 1) HBs Hq) as CL. fold cs in CL.
      pose proof (st_calls_clen s mn q p (k + 1) ltac:(lia)) as CC. fold cs in CC.
      assert (CC' : clen cs = trip_cost BD mn q p (k + 1)).
      { rewrite CC. unfold trip_cost. rewrite !EBD. reflexivity. }
      pose proof (sbs_W cs s) as W1. pose proof (sbs_nb_view cs s) as V1. pose proof (sbs_biv cs s Hbv CL) as B1.
      pose proof (sbs_pbl cs s) as P1. pose proof (sbs_pending_mono cs s) as M1. fold s1 in W1, V1, B1, P1, M1.
      pose proof (nb_view_facts _ _ V1) as (_ & _ & _ & _ & _ & _ & Vfc & Vdl & _).
      assert (EL : forall t' i, Len s1 t' i = Len s t' i) by (intros; unfold Len; rewrite Vdl; reflexivity).
      destruct (Z.eq_dec n mc) as [En|Nn].
      - rewrite !send_loop_out by lia.
        assert (TC0 : td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' = 0).
        { destruct f; cbn [td_cost]; [reflexivity|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite TC0. rewrite CC' in W1. split; [lia|]. split; [exact V1|]. split; [exact B1|]. split; [exact P1|]. split; [exact M1|].
        split; [intros i Hi; apply sbs_frame; exact Hi|]. split; [intros HP; apply sbs_PBB; exact HP|].
        split; [intros; apply sbs_bib; assumption|].
        intros PBL HW. split; [| destruct f; cbn [send_tree_ok]; [exact I|]; replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia); exact I].
        apply sbs_ok_of_bound; [exact Hbv | exact CL | lia].
      - destruct Hl as [Hl|Hl]; [|lia].
        assert (HL1 : lens_ok L (n + 1) mc) by (intros i Hi; apply HL; lia).
        specialize (IH L BD s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn' ltac:(intros; rewrite EL; apply ELn) ltac:(intros; rewrite EL; apply EBD) Hmn' ltac:(lia) HL1 Hl HB B1).
        cbv zeta in IH.
        destruct IH as (IW & IV & IB & IP & IM & IF & IPB & IBB & IOK).
        rewrite W1, CC' in IW. split; [lia|]. split; [rewrite IV; exact V1|]. split; [exact IB|]. split; [rewrite IP; exact P1|]. split; [lia|].
        split; [intros i Hi; rewrite IF by lia; apply (sbs_frame cs s i); fold s1; lia|].
        split; [intros HP; apply IPB; apply sbs_PBB; exact HP|].
        split; [intros; apply IBB; apply sbs_bib; assumption|].
        intros PBL HW. split.
        + apply sbs_ok_of_bound; [exact Hbv | exact CL |].
          pose proof (td_cost_cnt BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' HL1 Hl) as TCC.
          assert (0 <= td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn').
          { rewrite TCC. apply zsum_nonneg. intros x Hx. pose proof (td_cnt_nonneg L mc f (n + 1) q (L (n + 1)) 0 mx' mn' x ltac:(lia)).
            pose proof (HB x ltac:(lia)). pose proof (extra_blbits_bound x). nia. }
          lia.
        + apply IOK. exact HW. }
    destruct ((k + 1 <? mx) && (q =? L (n + 1))) eqn:EC.
    + apply andb_prop in EC. destruct EC as [_ EC]. apply Z.eqb_eq in EC.
      destruct (Z.eq_dec n mc) as [En|Nn].
      * rewrite !send_loop_out by lia.
        assert (TC0 : td_cost BD L mc f (n + 1) p (L (n + 1)) (k + 1) mx mn = 0).
        { destruct f; cbn [td_cost]; [reflexivity|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite TC0. repeat split; intros; try reflexivity; try lia; try assumption; try (match goal with HP : PBB _ |- _ => apply HP; assumption end).
        destruct f; cbn [send_tree_ok]; [exact I|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia); exact I.
      * apply (IH L BD s t mc (n + 1) p (L (n + 1)) (k + 1) mx mn ELn EBD Hmn ltac:(lia)); try assumption.
        { intros i Hi; apply HL; lia. }
        { rewrite <- EC. exact Hq. }
    + destruct (tree_counts q (L (n + 1))) as [mx' mn'] eqn:ET.
      pose proof (tree_counts_range _ _ _ _ ET) as [_ Rmn'].
      apply (TRIP mx' mn' ltac:(lia)).
      destruct (Z.eq_dec n mc) as [En|Nn]; [right; exact En | left; apply HL; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cnts0 (q : Z) : Z * Z := if q =? 0 then (138, 3) else (7, 4).

(* [comment removed for export] *)
Definition TDcnt (L : Z -> Z) (mc : Z) (x : Z) : Z :=
  let '(mx, mn) := cnts0 (L 0) in td_cnt L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 mx mn x.
Definition TDcost (BD L : Z -> Z) (mc : Z) : Z :=
  let '(mx, mn) := cnts0 (L 0) in td_cost BD L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 mx mn.

Lemma cnts0_range : forall q, 1 <= snd (cnts0 q) /\ (fst (cnts0 q) = 138 \/ fst (cnts0 q) = 7) /\ (snd (cnts0 q) = 3 \/ snd (cnts0 q) = 4).
Proof. intros q. unfold cnts0. destruct (q =? 0); cbn; lia. Qed.

Lemma TDcost_cnt : forall BD L mc, (forall i, 0 <= i <= mc -> 0 <= L i <= 15) ->
  TDcost BD L mc = zsum (fun x => TDcnt L mc x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  intros BD L mc HL. unfold TDcost, TDcnt. destruct (cnts0 (L 0)) as [mx mn].
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc].
  - replace (Z.to_nat (mc + 1)) with 0%nat by lia. cbn [td_cost td_cnt]. symmetry. apply zsum_0. intros; lia.
  - apply td_cost_cnt; [intros i Hi; apply HL; lia | apply HL; lia].
Qed.

Lemma TDcnt_nonneg : forall L mc x, 0 <= TDcnt L mc x.
Proof. intros. unfold TDcnt. destruct (cnts0 (L 0)). apply td_cnt_nonneg. lia. Qed.

Lemma TDcnt_le : forall L mc x, 0 <= mc -> TDcnt L mc x <= 2 * (mc + 1).
Proof. intros. unfold TDcnt. destruct (cnts0 (L 0)). pose proof (td_cnt_le L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 z z0 x ltac:(lia) ltac:(lia)). lia. Qed.

Lemma TDcnt_out : forall L mc x, (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> (x < 0 \/ 19 <= x) -> TDcnt L mc x = 0.
Proof.
  intros L mc x HL Hx. unfold TDcnt. destruct (cnts0 (L 0)).
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc]; [replace (Z.to_nat (mc + 1)) with 0%nat by lia; reflexivity|].
  apply td_cnt_out; [intros i Hi; apply HL; lia | apply HL; lia | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma set_Len_sbf : forall s0 b t i v, t <> TB -> set_Len (set_bl_tree_fc s0 b) t i v = set_bl_tree_fc (set_Len s0 t i v) b.
Proof. intros s0 b [| |] i v H; [ | | exfalso; apply H; reflexivity]; unfold set_Len, set_Dad; destruct s0; reflexivity. Qed.

(* [comment removed for export] *)
Lemma scan_tree_cnt : forall s0 b t mc,
  t <> TB -> 0 <= mc -> mc + 1 < arr_len (tree_dl s0 t) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s0 t i <= 15) -> 39 <= arr_len b ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) -> (forall y, 0 <= y < 19 -> arr_get b y + 2 * (mc + 1) < 65536) ->
  let s0' := set_Len s0 t (mc + 1) 65535 in
  exists b', scan_tree (set_bl_tree_fc s0 b) t mc = set_bl_tree_fc s0' b'
    /\ arr_len b' = arr_len b
    /\ (forall x, arr_get b' x = arr_get b x + TDcnt (fun i => Len s0' t i) mc x)
    /\ (forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i) /\ Len s0' t (mc + 1) = 65535.
Proof.
  intros s0 b t mc Ht Hmc Hlen HL Hb H0 HB s0'.
  assert (EL : forall i, Len s0' t i = if mc + 1 =? i then 65535 else Len s0 t i).
  { intros i. subst s0'. rewrite Len_set_Len by lia. destruct (mc + 1 =? i); [apply wrap16_id; lia | reflexivity]. }
  assert (EL' : forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i).
  { intros i Hi. rewrite EL. replace (mc + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  unfold scan_tree. rewrite sbf_Len. rewrite (set_Len_sbf s0 b t) by exact Ht. fold s0'.
  unfold TDcnt, cnts0. rewrite (EL' 0) by lia.
  assert (GO : forall mx mn : Z,
    exists b', scan_tree_loop (Z.to_nat (mc + 1)) (set_bl_tree_fc s0' b) t mc 0 (-1) (Len s0 t 0) 0 mx mn = set_bl_tree_fc s0' b'
      /\ arr_len b' = arr_len b
      /\ (forall x, arr_get b' x = arr_get b x + td_cnt (fun i => Len s0' t i) mc (Z.to_nat (mc + 1)) 0 (-1) (Len s0 t 0) 0 mx mn x)
      /\ (forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i) /\ Len s0' t (mc + 1) = 65535).
  { intros mx mn.
    destruct (scan_loop_cnt (Z.to_nat (mc + 1)) s0' b t mc 0 (-1) (Len s0 t 0) 0 mx mn Ht
                ltac:(intros i Hi; rewrite EL' by lia; apply HL; lia) ltac:(apply HL; lia) ltac:(lia) ltac:(lia) Hb H0
                ltac:(intros y Hy; pose proof (HB y Hy); lia)) as (b' & E & Lb & Gb).
    exists b'. split; [exact E|]. split; [exact Lb|]. split; [exact Gb|]. split; [exact EL'|].
    rewrite EL, Z.eqb_refl. reflexivity. }
  destruct (Len s0 t 0 =? 0); apply GO.
Qed.

(* [comment removed for export] *)
Lemma send_tree_facts : forall (L BD : Z -> Z) s t mc,
  (forall i, Len s t i = L i) -> (forall x, Len s TB x = BD x) ->
  (forall i, 0 <= i <= mc -> 0 <= L i <= 15) ->
  (forall x, 0 <= x < 19 -> 0 <= BD x <= 16) -> 0 <= ds_bi_valid s <= 16 ->
  let s' := send_tree s t mc in
  ov_W s' = ov_W s + TDcost BD L mc
  /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s')
  /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
  /\ (forall PBL, ov_W s' <= 8 * PBL ->
        send_tree_ok PBL (Z.to_nat (mc + 1)) s t mc 0 (-1) (Len s t 0) 0 (fst (cnts0 (Len s t 0))) (snd (cnts0 (Len s t 0)))).
Proof.
  intros L BD s t mc EL EBD HL HB Hbv s'.
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc].
  { subst s'. unfold send_tree, TDcost. rewrite EL. unfold cnts0.
    replace (Z.to_nat (mc + 1)) with 0%nat by lia.
    destruct (L 0 =? 0); rewrite send_loop_0; cbn [td_cost send_tree_ok fst snd];
      (repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end). }
  pose proof (send_loop_facts (Z.to_nat (mc + 1)) L BD s t mc 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0))) EL EBD
                (proj1 (cnts0_range (L 0))) ltac:(lia) ltac:(intros i Hi; apply HL; lia) ltac:(apply HL; lia) HB Hbv) as F.
  cbv zeta in F.
  assert (ES : send_tree s t mc = send_tree_loop (Z.to_nat (mc + 1)) s t mc 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0)))).
  { unfold send_tree. rewrite EL. unfold cnts0. destruct (L 0 =? 0); reflexivity. }
  assert (EC : TDcost BD L mc = td_cost BD L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0)))).
  { unfold TDcost. destruct (cnts0 (L 0)); reflexivity. }
  subst s'. rewrite ES, EC, EL. exact F.
Qed.
