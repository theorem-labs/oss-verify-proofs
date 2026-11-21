(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tail3.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Local Notation HM := (HM L).
Local Notation C := (C t L HPf).
Local Notation leafb := (leafb t HPf).
Local Notation nd := (nd HPf).
Local Notation par := (par t L HPf).
Local Notation tail := (tail L).
Local Notation cntL := (cntL t L HPf).
Local Notation NI := (NI t L HPf 573).
Local Notation nleaf := (nleaf t L HPf).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.

Let RHM : 2 <= HM <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RML : 7 <= ML <= 15 /\ E <= 2 ^ ML := ML_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.


Fixpoint Df (f : nat) (i : Z) : Z :=
  match f with
  | O => 0
  | S f' => if i <=? HM then 0 else Df f' (par i) + 1
  end.
Definition D (i : Z) : Z := Df 573 i.

Lemma Df_stable : forall f g i, tail i -> (Z.to_nat (i - HM) < f)%nat -> (Z.to_nat (i - HM) < g)%nat -> Df f i = Df g i.
Proof.
  induction f as [|f IH]; intros g i Hi Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. cbn [Df].
  destruct (Z.leb_spec i HM) as [Le|Gt]; [reflexivity|].
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail in Hi; lia)) as (A & B & _).
  rewrite (IH g (par i) A); [reflexivity | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma Df_S : forall f i, Df (S f) i = if i <=? HM then 0 else Df f (par i) + 1.
Proof. reflexivity. Qed.

Lemma D_root : D HM = 0.
Proof. unfold D. change 573%nat with (S 572). rewrite Df_S. rewrite Z.leb_refl. reflexivity. Qed.

Lemma D_step : forall i, HM < i < 573 -> D i = D (par i) + 1.
Proof.
  intros i Hi. unfold D. change 573%nat with (S 572). rewrite Df_S.
  replace (i <=? HM) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i Hi) as (A & B & _).
  rewrite (Df_stable 572 573 (par i) A); [reflexivity | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma Df_nonneg : forall f i, 0 <= Df f i.
Proof. induction f as [|f IH]; intros i; cbn [Df]; [lia|]. destruct (i <=? HM); [lia|]. pose proof (IH (par i)). lia. Qed.

Lemma D_nonneg : forall i, 0 <= D i.
Proof. intros i. apply Df_nonneg. Qed.


Lemma C_min : forall n i, tail i -> (Z.to_nat (i - HM) <= n)%nat -> C i = Z.min (D i) ML.
Proof.
  induction n as [|n IH]; intros i Hi Hn.
  - assert (i = HM) by (unfold RefDeflSafeB3.tail in Hi; lia). subst i. rewrite D_root, (C_root t L HPf). lia.
  - destruct (Z.eq_dec i HM) as [->|N]; [rewrite D_root, (C_root t L HPf); lia|].
    unfold RefDeflSafeB3.tail in Hi. rewrite D_step by lia. rewrite (C_step _ _ _ _ _ _ _ _ _ HR) by lia.
    destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (A & B & _).
    rewrite (IH (par i) A ltac:(unfold RefDeflSafeB3.tail in A; lia)). pose proof (D_nonneg (par i)). lia.
Qed.

Lemma C_min' : forall i, tail i -> C i = Z.min (D i) ML.
Proof. intros i Hi. apply (C_min (Z.to_nat (i - HM))); [exact Hi | lia]. Qed.

Lemma internal_deeper : forall n p, tail p -> leafb p = false -> (Z.to_nat (573 - p) <= n)%nat ->
  exists l, HM < l < 573 /\ leafb l = true /\ D p < D l.
Proof.
  induction n as [|n IH]; intros p Hp Hl Hn; [unfold RefDeflSafeB3.tail in Hp; lia|].
  unfold RefDeflSafeB3.leafb in Hl. apply Z.ltb_ge in Hl.
  destruct (children_pos _ _ _ _ _ _ _ _ _ HR p Hp Hl) as (A & B & Cq).
  set (c := 571 - 2 * (nd p - E)) in *.
  assert (Pc : par c = p) by (apply (proj2 (children_internal _ _ _ _ _ _ _ _ _ HR p c Hp Hl ltac:(lia))); right; reflexivity).
  pose proof (D_step c ltac:(lia)) as Dc. rewrite Pc in Dc.
  destruct (leafb c) eqn:Lc.
  - exists c. split; [lia|]. split; [exact Lc | lia].
  - destruct (IH c ltac:(unfold RefDeflSafeB3.tail; lia) Lc ltac:(lia)) as (l & Hl1 & Hl2 & Hl3).
    exists l. split; [exact Hl1|]. split; [exact Hl2 | lia].
Qed.

Lemma noovf_NI : (forall i, HM < i < 573 -> leafb i = true -> D i <= ML) -> NI = 0.
Proof.
  intros H. unfold RefDeflSafeB3.NI. apply zsum_0. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (C i) ML) as [EQ|NE]; [|reflexivity]. exfalso.
  rewrite C_min' in EQ by (unfold RefDeflSafeB3.tail; lia).
  destruct (internal_deeper (Z.to_nat (573 - i)) i ltac:(unfold RefDeflSafeB3.tail; lia) Li ltac:(lia)) as (l & Hl1 & Hl2 & Hl3).
  pose proof (H l Hl1 Hl2). lia.
Qed.

Lemma NI0_depth : NI = 0 -> forall i, tail i -> D i <= ML.
Proof.
  intros H i Hi.
  destruct (Z_lt_le_dec ML (D i)) as [LT|]; [|assumption]. exfalso.
  assert (UP : forall n j, tail j -> (Z.to_nat (j - HM) <= n)%nat -> ML < D j -> exists a, HM < a < 573 /\ leafb a = false /\ D a = ML).
  { induction n as [|n IH]; intros j Hj Hn Dj.
    - assert (j = HM) by (unfold RefDeflSafeB3.tail in Hj; lia). subst j. rewrite D_root in Dj. lia.
    - destruct (Z.eq_dec j HM) as [->|N]; [rewrite D_root in Dj; lia|].
      unfold RefDeflSafeB3.tail in Hj. rewrite D_step in Dj by lia.
      destruct (par_spec _ _ _ _ _ _ _ _ _ HR j ltac:(lia)) as (A & B & _ & Dg).
      destruct (Z.eq_dec (D (par j)) ML) as [EQ|NE].
      + exists (par j). unfold RefDeflSafeB3.tail in A. split; [| split; [unfold RefDeflSafeB3.leafb; apply Z.ltb_ge; exact Dg | exact EQ]].
        destruct (Z.eq_dec (par j) HM) as [Ep|]; [| lia]. rewrite Ep, D_root in EQ. lia.
      + apply (IH (par j) A ltac:(unfold RefDeflSafeB3.tail in A; lia)). lia. }
  destruct (UP (Z.to_nat (i - HM)) i Hi ltac:(lia) LT) as (a & Ha & La & Da).
  assert (X : zind (negb (leafb a) && (C a =? ML)) <= NI).
  { unfold RefDeflSafeB3.NI. apply (zsum_ge_point (fun i0 => zind (negb (leafb i0) && (C i0 =? ML))) (HM + 1) (Z.to_nat (573 - HM - 1)) a).
    - intros; apply (proj1 (zind_le1 _)).
    - lia. }
  rewrite La, (C_min' a), Da, Z.min_id, Z.eqb_refl in X by (unfold RefDeflSafeB3.tail; lia). cbn in X. lia.
Qed.


Lemma find_agree : forall f X (c : Z -> Z) b,
  (forall j, b - Z.of_nat f < j <= b -> bl_count_get X j = c j) ->
  gen_bitlen_find f X b = rep_find f c b.
Proof.
  induction f as [|f IH]; intros X c b H; cbn [gen_bitlen_find rep_find]; [reflexivity|].
  rewrite H by lia. destruct (c b =? 0); [| reflexivity]. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma adj_rep_step : forall (c : Z -> Z) r b, 1 <= r <= ML - 1 -> adj t c r b = rep_step ML c r b.
Proof.
  intros c r b Hr. unfold adj, rep_step.
  destruct (Z.eqb_spec b ML) as [->|N1].
  - replace (ML =? r) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec (r + 1) ML) as [E1|N2].
    + rewrite <- E1, Z.eqb_refl. lia.
    + replace (ML =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (Z.eqb_spec b (r + 1)) as [->|N2].
    + replace (r + 1 =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + destruct (Z.eqb_spec b r) as [->|]; reflexivity.
Qed.

Lemma rep_iter_S : forall n MLx h, rep_iter (S n) MLx h = rep_iter n MLx (rep_step MLx h (rep_find (Z.to_nat MLx) h (MLx - 1))).
Proof. reflexivity. Qed.

Lemma loop2_exact : forall f k s FC DL HP HL HMx DP BC OL SL MC (c : Z -> Z),
  (Z.of_nat f >= k) -> 1 <= k ->
  L2I t L HPf c (2 * k) -> (forall b, 0 <= b < 16 -> arr_get BC b = c b) -> arr_len BC = 16 ->
  let X := bt_upd s t FC DL HP HL HMx DP BC OL SL MC in
  exists BC',
    gen_bitlen_loop2 f X ML (2 * k) = bt_upd s t FC DL HP HL HMx DP BC' OL SL MC
    /\ (forall b, 0 <= b < 16 -> arr_get BC' b = rep_iter (Z.to_nat k) ML c b)
    /\ L2I t L HPf (rep_iter (Z.to_nat k) ML c) 0 /\ arr_len BC' = 16.
Proof.
  induction f as [|f IH]; intros k s FC DL HP HL HMx DP BC OL SL MC c Hf Hk HI HBC LBC; [lia|]. cbv zeta.
  rewrite (GL2_step t ML). cbv zeta.
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1)).
  destruct (L2_find _ _ _ _ _ _ _ _ _ HR c (2 * k) HI ltac:(lia)) as (r0 & Hr0 & Cr0).
  assert (Hr : r0 <= r <= ML - 1).
  { split; [| apply find_le]. apply find_ge; [lia|]. rewrite bt_bl_count_get. rewrite HBC by lia. exact Cr0. }
  assert (Cr : c r <> 0).
  { pose proof (find_nz (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1) ltac:(subst r; lia)) as X.
    rewrite bt_bl_count_get in X. fold r in X. rewrite HBC in X by lia. exact X. }
  assert (Er : r = rep_find (Z.to_nat ML) c (ML - 1)).
  { subst r. apply find_agree. intros j Hj. rewrite bt_bl_count_get. apply HBC. lia. }
  pose proof (L2_step _ _ _ _ _ _ _ _ _ HR c (2 * k) r HI ltac:(lia) ltac:(lia) Cr) as HI'.
  pose proof (bl_adj_get _ _ _ _ _ _ _ _ _ HR c (2 * k) BC r HI HBC LBC ltac:(lia) Cr ltac:(lia)) as AG.
  set (c1 := rep_step ML c (rep_find (Z.to_nat ML) c (ML - 1))).
  assert (AG1 : forall b, 0 <= b < 16 -> arr_get (bl_adj ML BC r) b = c1 b).
  { intros b Hb. rewrite (AG b Hb). subst c1. rewrite <- Er. apply adj_rep_step. lia. }
  assert (HI1 : L2I t L HPf c1 (2 * k - 2)).
  { apply (L2I_ext _ _ _ _ _ _ _ _ _ HR (adj t c r)); [exact HI'|]. intros b Hb. subst c1. rewrite <- Er. symmetry. apply adj_rep_step. lia. }
  assert (LBC' : arr_len (bl_adj ML BC r) = 16) by (unfold bl_adj; rewrite !arr_len_set; exact LBC).
  replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. rewrite rep_iter_S. fold c1.
  replace (2 * k - 2) with (2 * (k - 1)) in * by lia.
  destruct (Z.ltb_spec 0 (2 * (k - 1))) as [Ck|Ck].
  - destruct (IH (k - 1) s FC DL HP HL HMx DP (bl_adj ML BC r) OL SL MC c1 ltac:(lia) ltac:(lia) HI1 AG1 LBC') as (BC' & EQ & HB & HIf & LBCf).
    exists BC'. split; [exact EQ|]. split; [exact HB|]. split; [exact HIf | exact LBCf].
  - exists (bl_adj ML BC r). split; [reflexivity|].
    replace (Z.to_nat (k - 1)) with 0%nat by lia. cbn [rep_iter].
    replace (2 * (k - 1)) with 0 in HI1 by lia.
    split; [exact AG1|]. split; [exact HI1 | exact LBC'].
Qed.

Lemma KR_kraftZ_gen : forall c : Z -> Z, c 0 = 0 -> (forall b, ML < b < 16 -> c b = 0) -> KR t c = kraftZ ML c.
Proof.
  intros c Z0 HI. unfold KR, kraftZ.
  replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
  rewrite zsum_shift, Z0 by lia. rewrite zsum_split.
  rewrite (zsum_0 _ (0 + 1 + Z.of_nat (Z.to_nat ML))); [| intros b Hb; rewrite HI by lia; lia].
  replace (0 + 1) with 1 by lia. lia.
Qed.

Lemma KR_kraftZ : KR t cntL = kraftZ ML cntL.
Proof. apply KR_kraftZ_gen; [apply (cntL_zero _ _ _ _ _ _ _ _ _ HR); lia | intros; apply (cntL_zero _ _ _ _ _ _ _ _ _ HR); lia]. Qed.

Lemma NI_kraftZ : NI = kraftZ ML cntL - 2 ^ ML.
Proof. rewrite <- KR_kraftZ, (kraft_identity _ _ _ _ _ _ _ _ _ HR). lia. Qed.

Lemma repair_cntL : forall b, repair ML cntL b = rep_iter (Z.to_nat NI) ML cntL b.
Proof. intros b. unfold repair. rewrite NI_kraftZ. reflexivity. Qed.


Definition lcnt (DL : arr) (h b : Z) : Z :=
  zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) h (Z.to_nat (573 - h)).

Lemma lcnt_step : forall DL h b, h <= 573 ->
  lcnt DL (h - 1) b = lcnt DL h b + zind (leafb (h - 1) && (arr_get DL (nd (h - 1)) =? b)).
Proof.
  intros DL h b Hh. unfold lcnt. replace (Z.to_nat (573 - (h - 1))) with (S (Z.to_nat (573 - h))) by lia.
  rewrite zsum_shift. replace (h - 1 + 1) with h by lia. lia.
Qed.

Lemma lcnt_ext : forall DL DL' h b, (forall i, h <= i < 573 -> leafb i = true -> arr_get DL' (nd i) = arr_get DL (nd i)) ->
  lcnt DL' h b = lcnt DL h b.
Proof.
  intros DL DL' h b H. unfold lcnt. apply zsum_ext. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [andb]; [|reflexivity]. rewrite H by (try exact Li; lia). reflexivity.
Qed.

Lemma lcnt_zero : forall DL h b, (forall i, h <= i < 573 -> leafb i = true -> arr_get DL (nd i) <> b) -> lcnt DL h b = 0.
Proof.
  intros DL h b H. unfold lcnt. apply zsum_0. intros i Hi.
  destruct (leafb i) eqn:Li; cbn [andb]; [|reflexivity].
  destruct (Z.eqb_spec (arr_get DL (nd i)) b) as [Eb|Nb]; [|reflexivity]. exfalso. apply (H i ltac:(lia) Li Eb).
Qed.

Record RK (DL : arr) (bits n h : Z) (BCf : Z -> Z) : Prop := {
  rk_h : HM + 1 <= h <= 573;
  rk_rng : forall i, h <= i < 573 -> leafb i = true -> bits <= arr_get DL (nd i) <= ML;
  rk_mono : forall p q, h <= q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DL (nd q) <= arr_get DL (nd p);
  rk_above : forall b, bits < b <= ML -> lcnt DL h b = BCf b;
  rk_at : bits <= ML -> lcnt DL h bits = BCf bits - n }.

Lemma loop3i_rank : forall f s DL BC (B : Z) OL SL bits n h BCf,
  (Z.of_nat f >= h - HM) -> HM + 1 <= h <= 573 -> 0 <= n <= nleaf h -> 1 <= bits <= ML ->
  DLI t FC2 L HPf DL -> OL = wrap64 (B + S_opt t FC2 L HPf DL) -> RK DL bits n h BCf ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL' h',
    gen_bitlen_loop3i f X t mc bits n h = (bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc, h')
    /\ HM + 1 <= h' <= h /\ nleaf h' = nleaf h - n
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (B + S_opt t FC2 L HPf DL')
    /\ RK DL' bits 0 h' BCf.
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits n h BCf Hf Hh Hn Hbits HDL HOL HRK; cbv zeta.
  - exists DL, OL, h. cbn [gen_bitlen_loop3i]. assert (n = 0 \/ h = HM) by lia.
    pose proof (nleaf_base t L HPf). destruct H as [-> | ->]; [|exfalso; lia].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact HRK].
  - rewrite (GL3i_step t mc).
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    + exists DL, OL, h. subst n. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact HRK].
    + assert (Hh1 : HM + 1 <= h - 1).
      { destruct (Z_lt_le_dec (HM + 1) h) as [|C0]; [lia|]. exfalso. replace h with (HM + 1) in Hn by lia. rewrite (nleaf_base t L HPf) in Hn. lia. }
      pose proof (elems_range t) as RE. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
      assert (Th : tail (h - 1)) by (unfold RefDeflSafeB3.tail; lia).
      pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as NC. pose proof (leaf_mc _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as LM.
      pose proof (nleaf_step t L HPf (h - 1) ltac:(lia)) as NS. replace (h - 1 + 1) with h in NS by lia.
      rewrite (GB3i_flat t mc). cbv zeta. change (arr_get HPf (h - 1)) with (nd (h - 1)).
      destruct (Z.ltb_spec mc (nd (h - 1))) as [Ci|Cl].
      *
        assert (Lf : leafb (h - 1) = false) by (unfold RefDeflSafeB3.leafb; apply Z.ltb_ge; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        assert (HRK' : RK DL bits n (h - 1) BCf).
        { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
          - lia.
          - intros i Hi Li. destruct (Z.eq_dec i (h - 1)) as [->|Ni]; [rewrite Lf in Li; discriminate|]. apply R2; [lia | exact Li].
          - intros p q Hq Hqp Hp Lp Lq. destruct (Z.eq_dec q (h - 1)) as [->|Nq]; [rewrite Lf in Lq; discriminate|]. apply R3; try assumption; lia.
          - intros b Hb. rewrite lcnt_step, Lf by lia. cbn [andb zind]. rewrite R4 by lia. lia.
          - intros Hb. rewrite lcnt_step, Lf by lia. cbn [andb zind]. rewrite R5 by lia. lia. }
        destruct (IH s DL BC B OL SL bits n (h - 1) BCf ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
        exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
      * assert (Lf : leafb (h - 1) = true) by (unfold RefDeflSafeB3.leafb; apply Z.ltb_lt; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        set (DL1 := if arr_get DL (nd (h - 1)) =? bits then DL else arr_set DL (nd (h - 1)) (wrap16 bits)).
        assert (G1 : arr_get DL1 (nd (h - 1)) = bits).
        { subst DL1. destruct (Z.eqb_spec (arr_get DL (nd (h - 1))) bits) as [Eb|Nb]; [exact Eb|].
          rewrite arr_get_set, Z.eqb_refl. unfold arr_inb. rewrite (dli_len _ _ _ _ _ HDL).
          replace ((0 <=? nd (h - 1)) && (nd (h - 1) <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. apply wrap16_id. pose proof RML. lia. }
        assert (G2 : forall i, h <= i < 573 -> arr_get DL1 (nd i) = arr_get DL (nd i)).
        { intros i Hi. subst DL1. destruct (arr_get DL (nd (h - 1)) =? bits); [reflexivity|].
          rewrite arr_get_set. replace (nd (h - 1) =? nd i) with false; [reflexivity|].
          symmetry. apply Z.eqb_neq. intros EQ. pose proof (hr_inj _ _ _ _ _ _ _ _ _ HR (h - 1) i ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.HM in *; lia) EQ). lia. }
        assert (HRK' : RK DL1 bits (n - 1) (h - 1) BCf).
        { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
          - lia.
          - intros i Hi Li. destruct (Z.eq_dec i (h - 1)) as [->|Ni]; [rewrite G1; lia|]. rewrite G2 by lia. apply R2; [lia | exact Li].
          - intros p q Hq Hqp Hp Lp Lq. rewrite (G2 p) by lia.
            destruct (Z.eq_dec q (h - 1)) as [->|Nq]; [rewrite G1; pose proof (R2 p ltac:(lia) Lp); lia|].
            rewrite (G2 q) by lia. apply R3; try assumption; lia.
          - intros b Hb. rewrite lcnt_step, Lf, G1 by lia. rewrite (lcnt_ext DL DL1 h b) by (intros; apply G2; lia).
            replace (bits =? b) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb zind]. rewrite R4 by lia. lia.
          - intros Hb. rewrite lcnt_step, Lf, G1, Z.eqb_refl by lia. rewrite (lcnt_ext DL DL1 h bits) by (intros; apply G2; lia).
            cbn [andb zind]. rewrite R5 by lia. lia. }
        destruct (Z.eqb_spec (arr_get DL (nd (h - 1))) bits) as [Eb|Nb].
        -- assert (E1 : DL1 = DL) by (subst DL1; first [reflexivity | rewrite (proj2 (Z.eqb_eq _ _) Eb); reflexivity]).
           rewrite E1 in HRK'.
           destruct (IH s DL BC B OL SL bits (n - 1) (h - 1) BCf ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
        -- assert (E1 : DL1 = arr_set DL (nd (h - 1)) (wrap16 bits)) by (subst DL1; first [reflexivity | rewrite (proj2 (Z.eqb_neq _ _) Nb); reflexivity]).
           rewrite E1 in HRK'.
           assert (HDL' : DLI t FC2 L HPf (arr_set DL (nd (h - 1)) (wrap16 bits))).
           { destruct HDL as [A0 B0 Cq D0]. constructor.
             - intros i Hi Li. rewrite arr_get_set. destruct (_ && _); [rewrite wrap16_id by lia; lia | apply A0; assumption].
             - intros u Hu Fu. rewrite arr_get_set. destruct (Z.eqb_spec (nd (h - 1)) u) as [Eu|Nu]; cbn [andb]; [| apply B0; assumption].
               exfalso. rewrite <- Eu in Fu. destruct NC as [[_ X]|X]; [exact (X Fu) | lia].
             - rewrite arr_len_set. exact Cq.
             - intros u. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply D0]. }
           assert (HOL' : wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1))) = wrap64 (B + S_opt t FC2 L HPf (arr_set DL (nd (h - 1)) (wrap16 bits)))).
           { rewrite HOL, wrap64_add_l. rewrite (S_opt_set _ _ _ _ _ _ _ _ _ HR DL (h - 1) bits) by (try lia; try exact Lf; apply (dli_len _ _ _ _ _ HDL)).
             rewrite (hr_fc _ _ _ _ _ _ _ _ _ HR) by lia. f_equal. lia. }
           destruct (IH s (arr_set DL (nd (h - 1)) (wrap16 bits)) BC B (wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1)))) SL bits (n - 1) (h - 1) BCf
                     ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL' HOL' HRK') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4 | exact R5].
Qed.

Lemma loop3_rank : forall f s DL BC B OL SL bits h BCf,
  (Z.of_nat f >= bits) -> 0 <= bits <= ML -> HM + 1 <= h <= 573 ->
  zsum (arr_get BC) 1 (Z.to_nat bits) <= nleaf h -> (forall b, 1 <= b <= ML -> 0 <= arr_get BC b) ->
  (forall b, 1 <= b <= ML -> arr_get BC b = BCf b) ->
  DLI t FC2 L HPf DL -> OL = wrap64 (B + S_opt t FC2 L HPf DL) -> RK DL (bits + 1) 0 h BCf ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL' h',
    gen_bitlen_loop3 f X t mc bits h = bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (B + S_opt t FC2 L HPf DL')
    /\ RK DL' 1 0 h' BCf /\ nleaf h' = nleaf h - zsum (arr_get BC) 1 (Z.to_nat bits).
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits h BCf Hf Hbits Hh Hdem Hnn HBC HDL HOL HRK; cbv zeta.
  - exists DL, OL, h. cbn [gen_bitlen_loop3]. assert (B0 : bits = 0) by lia. subst bits. cbn in HRK. change (zsum (arr_get BC) 1 (Z.to_nat 0)) with 0.
    split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL|]. split; [exact HRK | lia].
  - rewrite (GL3_step t mc). rewrite bt_bl_count_get.
    destruct (Z.eqb_spec bits 0) as [B0|B0]; cbn [negb].
    + exists DL, OL, h. subst bits. cbn in HRK. change (zsum (arr_get BC) 1 (Z.to_nat 0)) with 0. split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL|]. split; [exact HRK | lia].
    + assert (Hc : 0 <= arr_get BC bits <= nleaf h).
      { pose proof (Hnn bits ltac:(lia)). split; [lia|].
        pose proof (zsum_ge_point (arr_get BC) 1 (Z.to_nat bits) bits ltac:(intros; apply Hnn; lia) ltac:(lia)). lia. }
      assert (HRKi : RK DL bits (arr_get BC bits) h BCf).
      { destruct HRK as [R1 R2 R3 R4 R5]. constructor.
        - exact R1.
        - intros i Hi Li. pose proof (R2 i Hi Li). lia.
        - exact R3.
        - intros b Hb. destruct (Z.eq_dec b (bits + 1)) as [->|Nb]; [rewrite R5 by lia; lia | apply R4; lia].
        - intros _. rewrite HBC by lia. rewrite lcnt_zero; [lia|]. intros i Hi Li. pose proof (R2 i Hi Li). lia. }
      destruct (loop3i_rank 574 s DL BC B OL SL bits (arr_get BC bits) h BCf ltac:(lia) Hh Hc ltac:(lia) HDL HOL HRKi)
        as (DL1 & OL1 & h1 & EQ1 & R1 & R2 & R3 & R4 & R5).
      rewrite EQ1.
      destruct (IH s DL1 BC B OL1 SL (bits - 1) h1 BCf ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & h' & EQ & D' & O' & K' & N'); try assumption.
      { replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) in Hdem by lia. rewrite zsum_snoc in Hdem.
        replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits in Hdem by lia. lia. }
      { replace (bits - 1 + 1) with bits by lia. exact R5. }
      exists DL', OL', h'. split; [exact EQ|]. split; [exact D'|]. split; [exact O'|]. split; [exact K'|].
      rewrite N', R2. replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) by lia. rewrite zsum_snoc.
      replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits by lia. lia.
Qed.


Lemma lcnt_noleaf : forall DL h' b, HM + 1 <= h' <= 573 -> nleaf h' = 0 -> lcnt DL (HM + 1) b = lcnt DL h' b.
Proof.
  intros DL h' b Hh Hn. unfold lcnt.
  replace (Z.to_nat (573 - (HM + 1))) with (Z.to_nat (h' - HM - 1) + Z.to_nat (573 - h'))%nat by lia.
  rewrite zsum_split. replace (HM + 1 + Z.of_nat (Z.to_nat (h' - HM - 1))) with h' by lia.
  assert (A : 0 <= zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) (HM + 1) (Z.to_nat (h' - HM - 1))).
  { apply zsum_nonneg. intros; apply (proj1 (zind_le1 _)). }
  assert (B : zsum (fun i => zind (leafb i && (arr_get DL (nd i) =? b))) (HM + 1) (Z.to_nat (h' - HM - 1)) <= nleaf h').
  { unfold RefDeflSafeB4.nleaf. apply zsum_mono. intros i Hi. destruct (leafb i), (arr_get DL (nd i) =? b); cbn; lia. }
  lia.
Qed.

Lemma noleaf_below : forall h' q, HM + 1 <= h' -> nleaf h' = 0 -> HM < q < h' -> leafb q = true -> False.
Proof.
  intros h' q Hh Hn Hq Lq.
  pose proof (zsum_ge_point (fun i => zind (leafb i)) (HM + 1) (Z.to_nat (h' - HM - 1)) q ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(lia)) as X.
  unfold RefDeflSafeB4.nleaf in Hn. cbv beta in X. rewrite Lq in X. cbn [zind] in X. lia.
Qed.

Theorem gen_bitlen_exact : forall s BC OL SL,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  let s7 := bt_upd s t FCf DLf HPf 1 HM DPf BC OL SL mc in
  exists DL' BC' OL' SL',
    gen_bitlen s7 t = bt_upd s t FCf DL' HPf 1 HM DPf BC' OL' SL' mc
    /\ DLI t FC2 L HPf DL' /\ OL' = wrap64 (OL + S_opt t FC2 L HPf DL') /\ SL' = (if stree_has t then wrap64 (SL + S_stat t FC2 L HPf) else SL)
    /\ arr_len BC' = 16 /\ (forall b, 0 <= b < 16 -> 0 <= arr_get BC' b <= 572)
    /\ (NI = 0 -> forall i, HM < i < 573 -> arr_get DL' (nd i) = D i)
    /\ (forall b, 1 <= b <= ML -> lcnt DL' (HM + 1) b = repair ML cntL b)
    /\ kraftZ ML (fun b => lcnt DL' (HM + 1) b) = 2 ^ ML
    /\ (NI <> 0 -> forall p q, HM < q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DL' (nd q) <= arr_get DL' (nd p)).
Proof.
  intros s BC OL SL LBC HOL HSL. cbv zeta.
  unfold gen_bitlen. autorewrite with btupd.
  set (s9 := bt_upd s t FCf (arr_set DLf (arr_get HPf HM) (wrap16 0)) HPf 1 HM DPf (arr_fill BC 0 (MAX_BITS + 1) 0) OL SL mc) in *.
  pose proof (L1_init _ _ _ _ _ _ _ _ _ HR s BC OL SL LBC HOL HSL) as I0. fold s9 in I0.
  pose proof (L1_run _ _ _ _ _ _ _ _ _ HR 573 s BC OL SL (HM + 1) s9 0 I0 ltac:(lia)) as [I1 G1].
  destruct (gen_bitlen_loop1 573 s9 t mc (sd_extra_base t) ML (HM + 1) 0) as [X10 ovf] eqn:ER1. cbn [fst snd] in I1.
  destruct I1 as [Hh (DL10 & BC10 & OL10 & SL10 & EX & HDL10 & LDL10 & HBC10 & LBC10 & HOL10 & HSL10) Hovf].
  replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in HBC10, HOL10, HSL10, Hovf by lia.
  assert (D10 : DLI t FC2 L HPf DL10) by (apply (DLI_pass1 _ _ _ _ _ _ _ _ _ HR); assumption).
  assert (O10 : OL10 = wrap64 (OL + S_opt t FC2 L HPf DL10)) by (rewrite HOL10, (S_opt_pass1 _ _ _ _ _ _ _ _ _ HR DL10 HDL10); reflexivity).
  assert (S10 : SL10 = (if stree_has t then wrap64 (SL + S_stat t FC2 L HPf) else SL)) by (rewrite HSL10; reflexivity).
  rewrite (ovf_identity _ _ _ _ _ _ _ _ _ HR) in Hovf.
  assert (C10 : forall i, tail i -> arr_get DL10 (nd i) = C i).
  { intros i Hi. rewrite HDL10. unfold dl_at. destruct (tid_nd _ _ _ _ _ _ _ _ _ HR i Hi) as [T P]. rewrite T, P.
    replace (i <? 573) with true by (symmetry; apply Z.ltb_lt; unfold RefDeflSafeB3.tail in Hi; lia). reflexivity. }
  assert (LC10 : forall b, lcnt DL10 (HM + 1) b = cntL b).
  { intros b. unfold lcnt, RefDeflSafeB3.cntL. replace (Z.to_nat (573 - (HM + 1))) with (Z.to_nat (572 - HM)) by lia.
    apply zsum_ext. intros i Hi. unfold w_cnt. rewrite C10 by (unfold RefDeflSafeB3.tail; lia). reflexivity. }
  assert (BCE : forall b, 0 <= b < 16 -> arr_get BC10 b = cntL b) by (intros b Hb; rewrite HBC10 by exact Hb; reflexivity).
  subst X10. destruct (Z.eqb_spec ovf 0) as [Z0|NZ].
  -
    assert (NI0 : NI = 0) by lia.
    exists DL10, BC10, OL10, SL10. split; [reflexivity|]. split; [exact D10|]. split; [exact O10|]. split; [exact S10|]. split; [exact LBC10|].
    split. { intros b Hb. rewrite BCE by exact Hb. pose proof (cnt_bound t L HPf b (HM + 1) (Z.to_nat (572 - HM))). unfold RefDeflSafeB3.cntL. lia. }
    split. { intros _ i Hi. rewrite C10 by (unfold RefDeflSafeB3.tail; lia). rewrite C_min' by (unfold RefDeflSafeB3.tail; lia).
             pose proof (NI0_depth NI0 i ltac:(unfold RefDeflSafeB3.tail; lia)). lia. }
    split. { intros b Hb. rewrite LC10, repair_cntL, NI0. reflexivity. }
    split. { unfold kraftZ. rewrite (zsum_ext (fun b => lcnt DL10 (HM + 1) b * 2 ^ (ML - b)) (fun b => cntL b * 2 ^ (ML - b))) by (intros; rewrite LC10; reflexivity).
             change (zsum (fun b : Z => cntL b * 2 ^ (ML - b)) 1 (Z.to_nat ML)) with (kraftZ ML cntL).
             rewrite <- KR_kraftZ, (kraft_identity _ _ _ _ _ _ _ _ _ HR), NI0. lia. }
    intros X. exfalso. exact (X NI0).
  -
    assert (HI : L2I t L HPf cntL (2 * NI)) by exact (L2_init _ _ _ _ _ _ _ _ _ HR).
    assert (NIB : 1 <= NI <= 570) by (pose proof (NI_bound _ _ _ _ _ _ _ _ _ HR); lia).
    rewrite Hovf.
    destruct (loop2_exact 573 NI s FCf DL10 HPf 1 HM DPf BC10 OL10 SL10 mc cntL ltac:(lia) ltac:(lia) HI BCE LBC10) as (BC' & EQ2 & HB' & HI2 & LBC').
    rewrite EQ2. unfold HEAP_SIZE.
    set (BCf := rep_iter (Z.to_nat NI) ML cntL) in *.
    pose proof HI2 as [NN Z0 HI0 _ TOT _ _].
    destruct (loop3_rank (Z.to_nat ML) s DL10 BC' OL OL10 SL10 ML 573 BCf ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & h' & EQ3 & D' & O' & K' & N'); try assumption.
    { rewrite <- TOT.
      replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
      rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
      rewrite (zsum_ext (arr_get BC') BCf 1 (Z.to_nat ML)) by (intros; apply HB'; lia).
      pose proof (zsum_nonneg BCf (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
    { intros b Hb. rewrite HB' by lia. apply NN. lia. }
    { intros b Hb. apply HB'. lia. }
    { constructor; [lia | intros; lia | intros; lia | intros; lia | intros; lia]. }
    assert (NL : nleaf h' = 0).
    { rewrite N'. rewrite (zsum_ext (arr_get BC') BCf 1 (Z.to_nat ML)) by (intros; apply HB'; lia).
      rewrite <- TOT. replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
      rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
      rewrite (zsum_0 BCf (1 + Z.of_nat (Z.to_nat ML))) by (intros; apply HI0; lia). lia. }
    pose proof (rk_h _ _ _ _ _ K') as Rh'.
    exists DL', BC', OL', SL10. split; [exact EQ3|]. split; [exact D'|]. split; [exact O'|]. split; [exact S10|]. split; [exact LBC'|].
    split. { intros b Hb. rewrite HB' by exact Hb. exact (L2_bound _ _ _ _ _ _ _ _ _ HR BCf 0 b HI2 Hb). }
    split. { intros X. exfalso. lia. }
    assert (HB : forall b, 1 <= b <= ML -> lcnt DL' (HM + 1) b = BCf b).
    { intros b Hb. rewrite (lcnt_noleaf DL' h' b) by (try exact NL; lia).
      destruct (Z.eq_dec b 1) as [->|Nb]; [rewrite (rk_at _ _ _ _ _ K') by lia; lia | apply (rk_above _ _ _ _ _ K'); lia]. }
    split. { intros b Hb. rewrite HB by exact Hb. rewrite repair_cntL. reflexivity. }
    split. { unfold kraftZ. rewrite (zsum_ext (fun b => lcnt DL' (HM + 1) b * 2 ^ (ML - b)) (fun b => BCf b * 2 ^ (ML - b))) by (intros; rewrite HB by lia; reflexivity).
             change (zsum (fun b : Z => BCf b * 2 ^ (ML - b)) 1 (Z.to_nat ML)) with (kraftZ ML BCf).
             rewrite <- (KR_kraftZ_gen BCf Z0 HI0). pose proof (l2_kr _ _ _ _ _ HI2).
             assert (P2 : 2 ^ (ML + 1) = 2 * 2 ^ ML) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia). lia. }
    intros _ p q Hq Hqp Hp Lp Lq.
    assert (h' <= q) by (destruct (Z_lt_le_dec q h') as [C0|C0]; [exfalso; exact (noleaf_below h' q ltac:(lia) NL ltac:(lia) Lq) | exact C0]).
    apply (rk_mono _ _ _ _ _ K'); assumption || lia.
Qed.

End Tail3.
