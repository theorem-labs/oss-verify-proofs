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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma find_ge : forall f X b j, b - Z.of_nat f < j <= b -> bl_count_get X j <> 0 -> j <= gen_bitlen_find f X b.
Proof.
  induction f as [|f IH]; intros X b j Hj Hz; cbn [gen_bitlen_find]; [lia|].
  destruct (Z.eqb_spec (bl_count_get X b) 0) as [E0|N0]; [|lia].
  destruct (Z.eq_dec j b) as [->|N]; [congruence|]. apply IH; [lia | exact Hz].
Qed.

Lemma find_le : forall f X b, gen_bitlen_find f X b <= b.
Proof. induction f as [|f IH]; intros X b; cbn [gen_bitlen_find]; [lia|]. destruct (_ =? 0); [pose proof (IH X (b - 1)); lia | lia]. Qed.

Lemma find_nz : forall f X b, b - Z.of_nat f < gen_bitlen_find f X b -> bl_count_get X (gen_bitlen_find f X b) <> 0.
Proof.
  induction f as [|f IH]; intros X b H; cbn [gen_bitlen_find] in *; [lia|].
  destruct (Z.eqb_spec (bl_count_get X b) 0) as [E0|N0]; [|exact N0]. apply IH. lia.
Qed.

Section Tail2.
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
Local Notation cntL := (cntL t L HPf).
Local Notation NI := (NI t L HPf 573).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.

Definition nleaf (h : Z) : Z := zsum (fun i => zind (leafb i)) (HM + 1) (Z.to_nat (h - HM - 1)).

Lemma nleaf_bound : forall h, 0 <= nleaf h <= Z.of_nat (Z.to_nat (h - HM - 1)).
Proof.
  intros h. unfold nleaf. induction (Z.to_nat (h - HM - 1)) as [|n IH]; [cbn; lia|].
  rewrite zsum_snoc. pose proof (zind_le1 (leafb (HM + 1 + Z.of_nat n))). lia.
Qed.

Lemma cnt_total : zsum cntL 0 16 = nleaf 573.
Proof.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). pose proof (ML_range t _ _ _ _ _ _ _ _ HR).
  unfold cntL, nleaf. replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) by lia. rewrite (zsum_swap (fun b p => w_cnt t L HPf b p)).
  apply zsum_ext. intros p Hp. unfold w_cnt.
  destruct (leafb p) eqn:Lp; cbn [andb].
  - pose proof (C_range _ _ _ _ _ _ _ _ _ HR p ltac:(unfold tail; lia)). pose proof (C_pos _ _ _ _ _ _ _ _ _ HR p ltac:(lia)).
    rewrite (zsum_single (fun b => zind (C p =? b)) 0 16 (C p)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros b Hb Nb. replace (C p =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - apply zsum_0. intros; reflexivity.
Qed.

Lemma cntL_nonneg : forall b, 0 <= cntL b.
Proof. intros b. unfold cntL. apply zsum_nonneg. intros i Hi. unfold w_cnt. apply (proj1 (zind_le1 _)). Qed.

Lemma cntL_zero : forall b, (b <= 0 \/ ML < b) -> cntL b = 0.
Proof.
  intros b Hb. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). unfold cntL. apply zsum_0. intros i Hi. unfold w_cnt.
  destruct (leafb i); cbn [andb]; [|reflexivity].
  pose proof (C_range _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)). pose proof (C_pos _ _ _ _ _ _ _ _ _ HR i ltac:(lia)).
  replace (C i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.


Record L2I (c : Z -> Z) (ovf : Z) : Prop := {
  l2_nn : forall b, 0 <= b < 16 -> 0 <= c b;
  l2_z0 : c 0 = 0;
  l2_hi : forall b, ML < b < 16 -> c b = 0;
  l2_kr : 2 * KR t c = 2 ^ (ML + 1) + ovf;
  l2_tot : zsum c 0 16 = nleaf 573;
  l2_ml : 0 < ovf -> ovf + 2 <= 2 * c ML;
  l2_ovf : 0 <= ovf }.

Lemma L2_init : L2I cntL (2 * NI).
Proof.
  pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  constructor.
  - intros b _. apply cntL_nonneg.
  - apply cntL_zero. lia.
  - intros b Hb. apply cntL_zero. lia.
  - pose proof (kraft_identity _ _ _ _ _ _ _ _ _ HR) as K. replace (2 ^ (ML + 1)) with (2 * 2 ^ ML) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia). lia.
  - apply cnt_total.
  - intros P. pose proof (capped_leaf_surplus _ _ _ _ _ _ _ _ _ HR ltac:(lia)). lia.
  - unfold RefDeflSafeB3.NI. pose proof (zsum_nonneg (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) (Z.to_nat (573 - HM - 1)) ltac:(intros; apply (proj1 (zind_le1 _)))). lia.
Qed.

Lemma L2_bound : forall c ovf b, L2I c ovf -> 0 <= b < 16 -> 0 <= c b <= 572.
Proof.
  intros c ovf b HI Hb. destruct HI as [NN _ _ _ TOT _ _].
  pose proof (nleaf_bound 573) as NB. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR).
  split; [apply NN; exact Hb|].
  pose proof (zsum_ge_point c 0 16 b ltac:(intros; apply NN; lia) ltac:(lia)). lia.
Qed.

Lemma L2_find : forall c ovf, L2I c ovf -> 0 < ovf -> exists r, 1 <= r <= ML - 1 /\ c r <> 0.
Proof.
  intros c ovf HI Hovf. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML. pose proof (E_range t) as RE.
  destruct (Z_lt_le_dec 0 (zsum (fun b => zind (negb (c b =? 0))) 1 (Z.to_nat (ML - 1)))) as [P|P].
  - destruct (zsum_pos_has _ _ _ P) as (r & Hr & Pr & _). exists r. split; [lia|].
    apply Bool.negb_true_iff in Pr. apply Z.eqb_neq in Pr. exact Pr.
  - exfalso. destruct HI as [NN Z0 HI0 KRE TOT MLc OV].
    assert (ALL0 : forall b, 1 <= b <= ML - 1 -> c b = 0).
    { intros b Hb. destruct (Z.eq_dec (c b) 0) as [|Nz]; [assumption|]. exfalso.
      pose proof (zsum_ind_ge1 (fun b => negb (c b =? 0)) 1 (Z.to_nat (ML - 1)) b ltac:(lia)
                    ltac:(apply Bool.negb_true_iff; apply Z.eqb_neq; exact Nz)). lia. }
    assert (KRv : KR t c = c ML).
    { unfold KR. rewrite (zsum_single (fun b => c b * 2 ^ (ML - b)) 0 16 ML); [rewrite Z.sub_diag; change (2 ^ 0) with 1; lia | lia |].
      intros b Hb Nb. destruct (Z_lt_le_dec ML b) as [A|A].
      - rewrite (Z.pow_neg_r 2 (ML - b)) by lia. lia.
      - destruct (Z.eq_dec b 0) as [->|]; [rewrite Z0; lia|]. rewrite ALL0 by lia. lia. }
    pose proof (L2_bound c ovf ML ltac:(constructor; assumption) ltac:(lia)) as [_ CB].
    pose proof (nleaf_bound 573) as NB. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL.
    assert (c ML <= nleaf 573).
    { rewrite <- TOT. apply (zsum_ge_point c 0 16 ML); [intros; apply NN; lia | lia]. }
    assert (P2 : 2 ^ (ML + 1) = 2 * 2 ^ ML) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
    assert (nleaf 573 < 2 ^ ML); [| lia].
    unfold RefDeflSafeB3.HM in NB, RHM. destruct t; cbn in RE, NB, RL |- *; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS in *; cbn; lia.
Qed.

Definition adj (c : Z -> Z) (r : Z) : Z -> Z :=
  fun b => if b =? ML then (if r + 1 =? ML then c ML + 1 else c ML - 1)
           else if b =? r + 1 then c (r + 1) + 2
           else if b =? r then c r - 1
           else c b.

Lemma L2_step : forall c ovf r, L2I c ovf -> 2 <= ovf -> 1 <= r <= ML - 1 -> c r <> 0 -> L2I (adj c r) (ovf - 2).
Proof.
  intros c ovf r HI Hovf Hr Hcr. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  destruct HI as [NN Z0 HI0 KRE TOT MLc OV].
  pose proof (NN r ltac:(lia)) as Nr. pose proof (NN (r + 1) ltac:(lia)) as Nr1. pose proof (NN ML ltac:(lia)) as NML.
  assert (AML : adj c r ML = (if r + 1 =? ML then c ML + 1 else c ML - 1)) by (unfold adj; rewrite Z.eqb_refl; reflexivity).
  constructor.
  - intros b Hb. unfold adj. destruct (Z.eqb_spec b ML); [destruct (Z.eqb_spec (r + 1) ML); lia|].
    destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b r); [lia|]. apply NN. lia.
  - unfold adj. replace (0 =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (0 =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (0 =? r) with false by (symmetry; apply Z.eqb_neq; lia). exact Z0.
  - intros b Hb. unfold adj. replace (b =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (b =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (b =? r) with false by (symmetry; apply Z.eqb_neq; lia). apply HI0. lia.
  -
    assert (D : KR t (adj c r) = KR t c - 1); [| lia].
    unfold KR. 
    transitivity (zsum (fun b => c b * 2 ^ (ML - b) + (if b =? ML then (if r + 1 =? ML then 1 else -1) * 1 else if b =? r + 1 then 2 * 2 ^ (ML - (r + 1)) else if b =? r then - (2 ^ (ML - r)) else 0)) 0 16).
    + apply zsum_ext. intros b Hb. unfold adj.
      destruct (Z.eqb_spec b ML) as [->|N1]; [rewrite Z.sub_diag; change (2 ^ 0) with 1; destruct (r + 1 =? ML); lia|].
      destruct (Z.eqb_spec b (r + 1)) as [->|N2]; [lia|].
      destruct (Z.eqb_spec b r) as [->|N3]; [lia|]. lia.
    + rewrite zsum_add.
      assert (P2 : 2 ^ (ML - r) = 2 * 2 ^ (ML - (r + 1))).
      { replace (ML - r) with (ML - (r + 1) + 1) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. }
      destruct (Z.eqb_spec (r + 1) ML) as [Er|Nr'].
      *
        rewrite (zsum_two (fun b => if b =? ML then 1 * 1 else if b =? r + 1 then 2 * 2 ^ (ML - (r + 1)) else if b =? r then - 2 ^ (ML - r) else 0) 0 16 ML r); try lia.
        -- rewrite Z.eqb_refl. replace (r =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
           rewrite P2. rewrite <- Er. rewrite Z.sub_diag. change (2 ^ 0) with 1. lia.
        -- intros i Hi N1 N2. replace (i =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (i =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * assert (T3 : zsum (fun b => if b =? ML then -1 * 1 else if b =? r + 1 then 2 * 2 ^ (ML - (r + 1)) else if b =? r then - 2 ^ (ML - r) else 0) 0 16 = -1).
        {
          transitivity (zsum (fun b => (if b =? ML then -1 else 0) + (if b =? r + 1 then 2 * 2 ^ (ML - (r + 1)) else if b =? r then - 2 ^ (ML - r) else 0)) 0 16).
          { apply zsum_ext. intros b Hb. destruct (Z.eqb_spec b ML) as [->|]; [|lia].
            replace (ML =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (ML =? r) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
          rewrite zsum_add. rewrite (zsum_single (fun b => if b =? ML then -1 else 0) 0 16 ML); [| lia | intros i Hi Ni; replace (i =? ML) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity].
          rewrite Z.eqb_refl.
          rewrite (zsum_two (fun b => if b =? r + 1 then 2 * 2 ^ (ML - (r + 1)) else if b =? r then - 2 ^ (ML - r) else 0) 0 16 (r + 1) r); try lia.
          -- rewrite Z.eqb_refl. replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia.
          -- intros i Hi N1 N2. replace (i =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        rewrite T3. lia.
  - rewrite <- TOT.
    transitivity (zsum (fun b => c b + (if b =? ML then (if r + 1 =? ML then 1 else -1) else if b =? r + 1 then 2 else if b =? r then -1 else 0)) 0 16).
    + apply zsum_ext. intros b Hb. unfold adj.
      destruct (Z.eqb_spec b ML) as [->|N1]; [destruct (r + 1 =? ML); lia|].
      destruct (Z.eqb_spec b (r + 1)) as [->|N2]; [lia|]. destruct (Z.eqb_spec b r) as [->|N3]; lia.
    + rewrite zsum_add.
      destruct (Z.eqb_spec (r + 1) ML) as [Er|Nr'].
      * rewrite (zsum_two (fun b => if b =? ML then 1 else if b =? r + 1 then 2 else if b =? r then -1 else 0) 0 16 ML r); try lia.
        -- rewrite Z.eqb_refl. replace (r =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia.
        -- intros i Hi N1 N2. replace (i =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (i =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      * transitivity (zsum c 0 16 + zsum (fun b => (if b =? ML then -1 else 0) + (if b =? r + 1 then 2 else if b =? r then -1 else 0)) 0 16).
        { f_equal. apply zsum_ext. intros b Hb. destruct (Z.eqb_spec b ML) as [->|]; [|lia].
          replace (ML =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (ML =? r) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
        rewrite zsum_add. rewrite (zsum_single (fun b => if b =? ML then -1 else 0) 0 16 ML); [| lia | intros i Hi Ni; replace (i =? ML) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity].
        rewrite Z.eqb_refl.
        rewrite (zsum_two (fun b => if b =? r + 1 then 2 else if b =? r then -1 else 0) 0 16 (r + 1) r); try lia.
        -- rewrite Z.eqb_refl. replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. lia.
        -- intros i Hi N1 N2. replace (i =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - intros _. specialize (MLc ltac:(lia)). rewrite AML. destruct (r + 1 =? ML); lia.
  - lia.
Qed.

Local Ltac bool_cases :=
  repeat (first [ match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end
                | match goal with |- context [?x <=? ?y] => destruct (Z.leb_spec x y) end
                | match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end ];
          cbn [andb orb negb]); try lia.

Lemma bl_adj_get : forall c ovf BC r, L2I c ovf -> (forall b, 0 <= b < 16 -> arr_get BC b = c b) -> arr_len BC = 16 ->
  1 <= r <= ML - 1 -> c r <> 0 -> 2 <= ovf ->
  forall b, 0 <= b < 16 -> arr_get (bl_adj ML BC r) b = adj c r b.
Proof.
  intros c ovf BC r HI HBC LBC Hr Hcr Hovf b Hb. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  pose proof (L2_bound c ovf r HI ltac:(lia)) as Br. pose proof (L2_bound c ovf (r + 1) HI ltac:(lia)) as Br1. pose proof (L2_bound c ovf ML HI ltac:(lia)) as BML.
  pose proof (l2_ml _ _ HI ltac:(lia)) as MLc.
  pose proof (HBC r ltac:(lia)) as Gr. pose proof (HBC (r + 1) ltac:(lia)) as Gr1. pose proof (HBC ML ltac:(lia)) as GML. pose proof (HBC b Hb) as Gb.
  unfold adj.
  destruct (Z.eq_dec (r + 1) ML) as [Er|Nr].
  - rewrite bl_adj_eq by lia. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LBC. rewrite Gr, Gr1.
    rewrite !wrap16_id by (rewrite ?wrap16_id by lia; lia).
    rewrite <- Er in *. bool_cases; subst; try lia. all: try (rewrite <- Gb; reflexivity). all: try reflexivity.
    all: exfalso; lia.
  - rewrite bl_adj_lt by lia. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LBC. rewrite Gr, Gr1, GML.
    rewrite !wrap16_id by lia.
    bool_cases; subst; try lia. all: try (rewrite <- Gb; reflexivity). all: try reflexivity. all: exfalso; lia.
Qed.

Lemma L2I_ext : forall c c' ovf, L2I c ovf -> (forall b, 0 <= b < 16 -> c' b = c b) -> L2I c' ovf.
Proof.
  intros c c' ovf [NN Z0 HI0 KRE TOT MLc OV] E. pose proof (ML_range t _ _ _ _ _ _ _ _ HR). constructor.
  - intros b Hb. rewrite E by lia. apply NN. lia.
  - rewrite E by lia. exact Z0.
  - intros b Hb. rewrite E by lia. apply HI0. lia.
  - assert (EK : KR t c' = KR t c).
    { unfold KR. apply zsum_ext. intros i Hi. rewrite E by lia. reflexivity. }
    rewrite EK. exact KRE.
  - assert (ET : zsum c' 0 16 = zsum c 0 16) by (apply zsum_ext; intros; apply E; lia).
    rewrite ET. exact TOT.
  - rewrite E by lia. exact MLc.
  - exact OV.
Qed.

Lemma gb2_ok_intro : forall f s FC DL HP HL HMx DP BC OL SL MC ovf,
  let X := bt_upd s t FC DL HP HL HMx DP BC OL SL MC in
  let r := gen_bitlen_find (Z.to_nat ML) X (ML - 1) in
  0 <= r -> (0 < ovf - 2 -> gb2_ok ML f (bt_upd s t FC DL HP HL HMx DP (bl_adj ML BC r) OL SL MC) (ovf - 2)) ->
  gb2_ok ML (S f) X ovf.
Proof.
  intros f s FC DL HP HL HMx DP BC OL SL MC ovf. cbv zeta. intros Hr Hrest. cbn [gb2_ok]. split; [exact Hr|].
  repeat (first [rewrite bt_bl_count_get | rewrite bt_bl_count_set]). unfold bl_adj in Hrest.
  destruct (Z.ltb_spec 0 (ovf - 2)); [apply Hrest; assumption | exact I].
Qed.

Lemma loop2_run : forall f k s FC DL HP HL HMx DP BC OL SL MC,
  (Z.of_nat f >= k) -> 1 <= k ->
  L2I (arr_get BC) (2 * k) -> arr_len BC = 16 ->
  let X := bt_upd s t FC DL HP HL HMx DP BC OL SL MC in
  exists BC',
    gen_bitlen_loop2 f X ML (2 * k) = bt_upd s t FC DL HP HL HMx DP BC' OL SL MC
    /\ L2I (arr_get BC') 0 /\ arr_len BC' = 16
    /\ gb2_ok ML f X (2 * k).
Proof.
  induction f as [|f IH]; intros k s FC DL HP HL HMx DP BC OL SL MC Hf Hk HI LBC; [lia|]. cbv zeta.
  pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  rewrite (GL2_step t ML). cbv zeta.
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1)).
  destruct (L2_find (arr_get BC) (2 * k) HI ltac:(lia)) as (r0 & Hr0 & Cr0).
  assert (Hr : r0 <= r <= ML - 1).
  { split; [| apply find_le]. apply find_ge; [lia|]. rewrite bt_bl_count_get. exact Cr0. }
  assert (Cr : arr_get BC r <> 0).
  { pose proof (find_nz (Z.to_nat ML) (bt_upd s t FC DL HP HL HMx DP BC OL SL MC) (ML - 1) ltac:(subst r; lia)) as X.
    rewrite bt_bl_count_get in X. exact X. }
  pose proof (L2_step (arr_get BC) (2 * k) r HI ltac:(lia) ltac:(lia) Cr) as HI'.
  pose proof (bl_adj_get (arr_get BC) (2 * k) BC r HI ltac:(intros; reflexivity) LBC ltac:(lia) Cr ltac:(lia)) as AG.
  pose proof (L2I_ext _ (arr_get (bl_adj ML BC r)) _ HI' AG) as HI2.
  assert (LBC' : arr_len (bl_adj ML BC r) = 16) by (unfold bl_adj; rewrite !arr_len_set; exact LBC).
  replace (2 * k - 2) with (2 * (k - 1)) in * by lia.
  destruct (Z.ltb_spec 0 (2 * (k - 1))) as [Ck|Ck].
  - destruct (IH (k - 1) s FC DL HP HL HMx DP (bl_adj ML BC r) OL SL MC ltac:(lia) ltac:(lia) HI2 LBC') as (BC' & EQ & HIf & LBCf & GB).
    exists BC'. split; [exact EQ|]. split; [exact HIf|]. split; [exact LBCf|].
    apply gb2_ok_intro; [lia|]. intros _. fold r. replace (2 * k - 2) with (2 * (k - 1)) by lia. exact GB.
  - exists (bl_adj ML BC r). split; [reflexivity|]. replace (2 * (k - 1)) with 0 in HI2 by lia.
    split; [exact HI2|]. split; [exact LBC'|].
    apply gb2_ok_intro; [lia|]. intros X. exfalso. lia.
Qed.


Record DLI (DL : arr) : Prop := {
  dli_leaf : forall i, HM < i < 573 -> leafb i = true -> 1 <= arr_get DL (nd i) <= ML;
  dli_zero : forall u, 0 <= u < E -> arr_get FC2 u = 0 -> arr_get DL u = 0;
  dli_len : arr_len DL = tsize t;
  dli_rng : forall u, 0 <= arr_get DL u < 65536 }.

Lemma nleaf_step : forall h, HM + 1 <= h -> nleaf (h + 1) = nleaf h + zind (leafb h).
Proof.
  intros h Hh. unfold nleaf. replace (Z.to_nat (h + 1 - HM - 1)) with (S (Z.to_nat (h - HM - 1))) by lia.
  rewrite zsum_snoc. replace (HM + 1 + Z.of_nat (Z.to_nat (h - HM - 1))) with h by lia. reflexivity.
Qed.

Lemma nleaf_base : nleaf (HM + 1) = 0.
Proof. unfold nleaf. replace (Z.to_nat (HM + 1 - HM - 1)) with 0%nat by lia. reflexivity. Qed.

Definition S_opt (DL : arr) : Z :=
  zsum (fun i => zind (leafb i) * (arr_get FC2 (nd i) * (arr_get DL (nd i) + xbits t (nd i)))) (HM + 1) (Z.to_nat (572 - HM)).

Lemma S_opt_set : forall DL p v, HM < p < 573 -> leafb p = true -> arr_len DL = tsize t -> 0 <= v < 2 ^ 16 ->
  S_opt (arr_set DL (nd p) (wrap16 v)) = S_opt DL + arr_get FC2 (nd p) * (v - arr_get DL (nd p)).
Proof.
  intros DL p v Hp Lp LDL Hv. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). pose proof (elems_range t). pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
  pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR p ltac:(unfold tail; lia)) as NC.
  unfold S_opt.
  transitivity (zsum (fun i => zind (leafb i) * (arr_get FC2 (nd i) * (arr_get DL (nd i) + xbits t (nd i)))
                              + (if i =? p then arr_get FC2 (nd p) * (v - arr_get DL (nd p)) else 0)) (HM + 1) (Z.to_nat (572 - HM))).
  - apply zsum_ext. intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite LDL.
    destruct (Z.eqb_spec i p) as [->|Nip].
    + rewrite Z.eqb_refl, Lp. replace ((0 <=? nd p) && (nd p <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb zind]. rewrite wrap16_id by lia. lia.
    + destruct (Z.eqb_spec (nd p) (nd i)) as [Epi|Npi]; cbn [andb]; [|lia].
      exfalso. apply Nip. symmetry. apply (hr_inj _ _ _ _ _ _ _ _ _ HR p i); [unfold RefDeflSafeB3.HM in *; lia | unfold RefDeflSafeB3.HM in *; lia | exact Epi].
  - rewrite zsum_add. rewrite (zsum_single (fun i => if i =? p then _ else 0) (HM + 1) (Z.to_nat (572 - HM)) p); [| lia |].
    + rewrite Z.eqb_refl. reflexivity.
    + intros i Hi Ni. replace (i =? p) with false by (symmetry; apply Z.eqb_neq; exact Ni). reflexivity.
Qed.

Definition S_stat : Z := zsum (w_stat t FC2 HPf) (HM + 1) (Z.to_nat (572 - HM)).

Lemma S_opt_pass1 : forall DL, (forall u, arr_get DL u = dl_at t L DLf HPf 573 u) ->
  S_opt DL = zsum (w_opt t FC2 L HPf) (HM + 1) (Z.to_nat (572 - HM)).
Proof.
  intros DL HDL. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). unfold S_opt. apply zsum_ext. intros i Hi. unfold w_opt.
  rewrite HDL. unfold dl_at. destruct (tid_nd _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)) as [T P]. rewrite T, P.
  replace (i <? 573) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. reflexivity.
Qed.

Lemma loop3i_run : forall f s DL BC (B : Z) OL SL bits n h,
  (Z.of_nat f >= h - HM) -> HM + 1 <= h <= 573 -> 0 <= n <= nleaf h -> 1 <= bits <= ML ->
  DLI DL -> OL = wrap64 (B + S_opt DL) ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL' h',
    gen_bitlen_loop3i f X t mc bits n h = (bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc, h')
    /\ HM + 1 <= h' <= h /\ nleaf h' = nleaf h - n
    /\ DLI DL' /\ OL' = wrap64 (B + S_opt DL')
    /\ gb3i_ok t mc f X bits n h.
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits n h Hf Hh Hn Hbits HDL HOL; cbv zeta.
  - exists DL, OL, h. cbn [gen_bitlen_loop3i gb3i_ok]. assert (n = 0 \/ h = HM) by lia.
    pose proof nleaf_base. destruct H as [->| ->]; [| ]. 1: { split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact I]. }
    exfalso. lia.
  - rewrite (GL3i_step t mc). cbn [gb3i_ok].
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    + exists DL, OL, h. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HDL|]. split; [exact HOL | exact I].
    +
      assert (Hh1 : HM + 1 <= h - 1).
      { destruct (Z_lt_le_dec (HM + 1) h) as [|C0]; [lia|]. exfalso. replace h with (HM + 1) in Hn by lia. rewrite nleaf_base in Hn. lia. }
      pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (elems_range t) as RE.
      pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
      assert (Th : tail L (h - 1)) by (unfold tail; lia).
      pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as NC. pose proof (leaf_mc _ _ _ _ _ _ _ _ _ HR (h - 1) Th) as LM.
      pose proof (nleaf_step (h - 1) ltac:(lia)) as NS. replace (h - 1 + 1) with h in NS by lia.
      assert (HG : 0 <= heap_get (bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc) (h - 1) < 573).
      { unfold heap_get. rewrite bt_heap. change (arr_get HPf (h - 1)) with (nd (h - 1)). lia. }
      rewrite (GB3i_flat t mc). cbv zeta. change (arr_get HPf (h - 1)) with (nd (h - 1)).
      destruct (Z.ltb_spec mc (nd (h - 1))) as [Ci|Cl].
      *
        unfold RefDeflSafeB3.leafb in NS. replace (RefDeflSafeB3.nd HPf (h - 1) <? E) with false in NS by (symmetry; apply Z.ltb_ge; lia). cbn [zind] in NS.
        destruct (IH s DL BC B OL SL bits n (h - 1) ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL) as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
        exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4|].
        split; [lia|]. split; [exact HG|]. exact R5.
      * assert (Lf : leafb (h - 1) = true) by (unfold RefDeflSafeB3.leafb; apply Z.ltb_lt; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        destruct (Z.eqb_spec (arr_get DL (nd (h - 1))) bits) as [Eb|Nb].
        -- destruct (IH s DL BC B OL SL bits (n - 1) (h - 1) ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL HOL) as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4|].
           split; [lia|]. split; [exact HG|]. exact R5.
        -- assert (HDL' : DLI (arr_set DL (nd (h - 1)) (wrap16 bits))).
           { destruct HDL as [A0 B0 Cq D0]. constructor.
             - intros i Hi Li. rewrite arr_get_set. destruct (_ && _); [rewrite wrap16_id by lia; lia | apply A0; assumption].
             - intros u Hu Fu. rewrite arr_get_set. destruct (Z.eqb_spec (nd (h - 1)) u) as [Eu|Nu]; cbn [andb]; [| apply B0; assumption].
               exfalso. rewrite <- Eu in Fu. destruct NC as [[_ X]|X]; [exact (X Fu) | lia].
             - rewrite arr_len_set. exact Cq.
             - intros u. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply D0]. }
           assert (HOL' : wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1))) = wrap64 (B + S_opt (arr_set DL (nd (h - 1)) (wrap16 bits)))).
           { rewrite HOL, wrap64_add_l. rewrite (S_opt_set DL (h - 1) bits) by (try lia; try exact Lf; apply (dli_len _ HDL)).
             rewrite (hr_fc _ _ _ _ _ _ _ _ _ HR) by lia. f_equal. lia. }
           destruct (IH s (arr_set DL (nd (h - 1)) (wrap16 bits)) BC B (wrap64 (OL + (bits - arr_get DL (nd (h - 1))) * arr_get FCf (nd (h - 1)))) SL bits (n - 1) (h - 1)
                     ltac:(lia) ltac:(lia) ltac:(lia) Hbits HDL' HOL') as (DL' & OL' & h' & EQ & R1 & R2 & R3 & R4 & R5).
           exists DL', OL', h'. split; [exact EQ|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [exact R4|].
           split; [lia|]. split; [exact HG|]. exact R5.
Qed.

Lemma loop3_run : forall f s DL BC B OL SL bits h,
  (Z.of_nat f >= bits) -> 0 <= bits <= ML -> HM + 1 <= h <= 573 ->
  zsum (arr_get BC) 1 (Z.to_nat bits) <= nleaf h -> (forall b, 1 <= b <= ML -> 0 <= arr_get BC b) ->
  DLI DL -> OL = wrap64 (B + S_opt DL) ->
  let X := bt_upd s t FCf DL HPf 1 HM DPf BC OL SL mc in
  exists DL' OL',
    gen_bitlen_loop3 f X t mc bits h = bt_upd s t FCf DL' HPf 1 HM DPf BC OL' SL mc
    /\ DLI DL' /\ OL' = wrap64 (B + S_opt DL')
    /\ gb3_ok t mc f X bits h.
Proof.
  induction f as [|f IH]; intros s DL BC B OL SL bits h Hf Hbits Hh Hdem Hnn HDL HOL; cbv zeta.
  - exists DL, OL. cbn [gen_bitlen_loop3 gb3_ok]. split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL | exact I].
  - rewrite (GL3_step t mc). cbn [gb3_ok]. rewrite bt_bl_count_get.
    destruct (Z.eqb_spec bits 0) as [B0|B0]; cbn [negb].
    + exists DL, OL. split; [reflexivity|]. split; [exact HDL|]. split; [exact HOL | exact I].
    + assert (Hc : 0 <= arr_get BC bits <= nleaf h).
      { pose proof (Hnn bits ltac:(lia)). split; [lia|].
        pose proof (zsum_ge_point (arr_get BC) 1 (Z.to_nat bits) bits ltac:(intros; apply Hnn; lia) ltac:(lia)). lia. }
      destruct (loop3i_run 574 s DL BC B OL SL bits (arr_get BC bits) h ltac:(pose proof (HM_range _ _ _ _ _ _ _ _ _ HR); lia) Hh Hc ltac:(lia) HDL HOL)
        as (DL1 & OL1 & h1 & EQ1 & R1 & R2 & R3 & R4 & R5).
      rewrite EQ1.
      destruct (IH s DL1 BC B OL1 SL (bits - 1) h1 ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & EQ & D' & O' & G'); try assumption.
      { replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) in Hdem by lia. rewrite zsum_snoc in Hdem.
        replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits in Hdem by lia. lia. }
      exists DL', OL'. split; [exact EQ|]. split; [exact D'|]. split; [exact O'|]. split; [exact R5|]. exact G'.
Qed.

Lemma DLI_pass1 : forall DL, (forall u, arr_get DL u = dl_at t L DLf HPf 573 u) -> arr_len DL = tsize t -> DLI DL.
Proof.
  intros DL HDL LDL. pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). pose proof (ML_range t _ _ _ _ _ _ _ _ HR).
  constructor.
  - intros i Hi Li. rewrite HDL. unfold dl_at.
    destruct (tid_nd _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)) as [T P]. rewrite T, P.
    replace (i <? 573) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    pose proof (C_range _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)). pose proof (C_pos _ _ _ _ _ _ _ _ _ HR i ltac:(lia)). lia.
  - intros u Hu Fu. rewrite HDL. unfold dl_at.
    destruct (tid L HPf u) eqn:Tu; cbn [andb].
    + exfalso. apply (tid_true _ _ _ _ _ _ _ _ _ HR) in Tu. destruct Tu as [Tu Eu].
      destruct (nd_cases _ _ _ _ _ _ _ _ _ HR (posof L HPf u) Tu) as [[A B]|A]; rewrite Eu in *; [exact (B Fu) | lia].
    + apply (hr_dl0 _ _ _ _ _ _ _ _ _ HR); assumption.
  - exact LDL.
  - intros u. rewrite HDL. unfold dl_at. destruct (_ && _); [| apply (hr_dlr _ _ _ _ _ _ _ _ _ HR)].
    pose proof (C_range _ _ _ _ _ _ _ _ _ HR (posof L HPf u) (posof_range _ _ _ _ _ _ _ _ _ HR u)). lia.
Qed.


Lemma NI_bound : 0 <= NI <= 570.
Proof.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM. unfold RefDeflSafeB3.NI.
  pose proof (zsum_nonneg (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) (Z.to_nat (573 - HM - 1)) ltac:(intros; apply (proj1 (zind_le1 _)))) as A.
  pose proof (zsum_mono (fun i => zind (negb (leafb i) && (C i =? ML))) (fun _ => 1) (HM + 1) (Z.to_nat (573 - HM - 1)) ltac:(intros; apply (proj2 (zind_le1 _)))) as B.
  rewrite zsum_const1 in B. lia.
Qed.

Theorem gen_bitlen_run : forall s BC OL SL,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  let s7 := bt_upd s t FCf DLf HPf 1 HM DPf BC OL SL mc in
  let s8 := set_bl_count s7 (arr_fill (ds_bl_count s7) 0 (MAX_BITS + 1) 0) in
  let s9 := set_Len s8 t (heap_get s8 (ds_heap_max s8)) 0 in
  (exists DL' BC' OL' SL',
      gen_bitlen s7 t = bt_upd s t FCf DL' HPf 1 HM DPf BC' OL' SL' mc
      /\ DLI DL' /\ OL' = wrap64 (OL + S_opt DL') /\ SL' = (if stree_has t then wrap64 (SL + S_stat) else SL) /\ arr_len BC' = 16
      /\ (forall b, 0 <= b < 16 -> 0 <= arr_get BC' b <= 572))
  /\ gb1_ok t mc 573%nat s9 (ds_heap_max s9 + 1) 0
  /\ (let '(s10, ovf) := gen_bitlen_loop1 573%nat s9 t mc (sd_extra_base t) ML (ds_heap_max s9 + 1) 0 in
      (ovf <> 0 -> gb2_ok ML 573%nat s10 ovf /\ gb3_ok t mc (Z.to_nat ML) (gen_bitlen_loop2 573%nat s10 ML ovf) ML HEAP_SIZE)).
Proof.
  intros s BC OL SL LBC HOL HSL. cbv zeta.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML.
  unfold gen_bitlen. autorewrite with btupd.
  set (s9 := bt_upd s t FCf (arr_set DLf (arr_get HPf HM) (wrap16 0)) HPf 1 HM DPf (arr_fill BC 0 (MAX_BITS + 1) 0) OL SL mc) in *.
  pose proof (L1_init _ _ _ _ _ _ _ _ _ HR s BC OL SL LBC HOL HSL) as I0. fold s9 in I0.
  pose proof (L1_run _ _ _ _ _ _ _ _ _ HR 573 s BC OL SL (HM + 1) s9 0 I0 ltac:(lia)) as [I1 G1].
  destruct (gen_bitlen_loop1 573 s9 t mc (sd_extra_base t) ML (HM + 1) 0) as [X10 ovf] eqn:ER1. cbn [fst snd] in I1.
  destruct I1 as [Hh (DL10 & BC10 & OL10 & SL10 & EX & HDL10 & LDL10 & HBC10 & LBC10 & HOL10 & HSL10) Hovf].
  replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in HBC10, HOL10, HSL10, Hovf by lia.
  assert (D10 : DLI DL10) by (apply DLI_pass1; assumption).
  assert (O10 : OL10 = wrap64 (OL + S_opt DL10)) by (rewrite HOL10, (S_opt_pass1 DL10 HDL10); reflexivity).
  assert (S10 : SL10 = (if stree_has t then wrap64 (SL + S_stat) else SL)) by (rewrite HSL10; reflexivity).
  rewrite (ovf_identity _ _ _ _ _ _ _ _ _ HR) in Hovf.
  split; [| split; [exact G1 |]].
  - subst X10. destruct (Z.eqb_spec ovf 0) as [Z0|NZ].
    + exists DL10, BC10, OL10, SL10. split; [reflexivity|]. split; [exact D10|]. split; [exact O10|]. split; [exact S10|]. split; [exact LBC10|].
      intros b Hb. rewrite HBC10 by exact Hb. pose proof (cnt_bound t L HPf b (HM + 1) (Z.to_nat (572 - HM))). pose proof (HM_range _ _ _ _ _ _ _ _ _ HR). lia.
    + pose proof (L2_init) as L20.
      assert (HI : L2I (arr_get BC10) (2 * NI)).
      { apply (L2I_ext cntL); [exact L20|]. intros b Hb. rewrite HBC10 by exact Hb. reflexivity. }
      assert (NIB : 1 <= NI <= 570) by (pose proof NI_bound; lia).
      rewrite Hovf.
      destruct (loop2_run 573 NI s FCf DL10 HPf 1 HM DPf BC10 OL10 SL10 mc ltac:(lia) ltac:(lia) HI LBC10) as (BC' & EQ2 & HI2 & LBC' & GB2).
      rewrite EQ2.
      destruct (loop3_run (Z.to_nat ML) s DL10 BC' OL OL10 SL10 ML 573 ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & EQ3 & D' & O' & G3); try assumption.
      { destruct HI2 as [NN Z0 HI0 _ TOT _ _]. rewrite <- TOT.
        replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
        rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
        pose proof (zsum_nonneg (arr_get BC') (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
      { intros b Hb. apply (l2_nn _ _ HI2). lia. }
      exists DL', BC', OL', SL10. split; [exact EQ3|]. split; [exact D'|]. split; [exact O'|]. split; [exact S10|]. split; [exact LBC'|].
      intros b Hb. exact (L2_bound _ _ b HI2 Hb).
  - intros NZ. subst X10.
    pose proof (L2_init) as L20.
    assert (HI : L2I (arr_get BC10) (2 * NI)).
    { apply (L2I_ext cntL); [exact L20|]. intros b Hb. rewrite HBC10 by exact Hb. reflexivity. }
    assert (NIB : 1 <= NI <= 570) by (pose proof NI_bound; lia).
    rewrite Hovf.
    destruct (loop2_run 573 NI s FCf DL10 HPf 1 HM DPf BC10 OL10 SL10 mc ltac:(lia) ltac:(lia) HI LBC10) as (BC' & EQ2 & HI2 & LBC' & GB2).
    split; [exact GB2|]. rewrite EQ2. unfold HEAP_SIZE.
    destruct (loop3_run (Z.to_nat ML) s DL10 BC' OL OL10 SL10 ML 573 ltac:(lia) ltac:(lia) ltac:(lia)) as (DL' & OL' & EQ3 & D' & O' & G3); try assumption.
    { destruct HI2 as [NN Z0 HI0 _ TOT _ _]. rewrite <- TOT.
      replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
      rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
      pose proof (zsum_nonneg (arr_get BC') (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
    { intros b Hb. apply (l2_nn _ _ HI2). lia. }
Qed.
End Tail2.
