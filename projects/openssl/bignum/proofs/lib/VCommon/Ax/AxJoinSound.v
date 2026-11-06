(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxMemC AxZZ AxState AxEntryRel AxSys AxJoin.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition Sound (segs : list Segment) (cfg : SpuriousCfg) (LIM : Z) (MR : valuation -> amodel -> Model -> Prop)
    (KT : valuation -> list byte -> TSet) (A : astate amodel) : Prop :=
  forall ρ c, R segs amodel (MR ρ) LIM ρ A c -> forall o, pieces_val ρ (am_out (a_model A)) o -> realizes_cfg segs cfg c (KT ρ o).

Lemma w_eqb_eq (a b : w64) : w_eqb a b = true -> a = b.
Proof. rewrite w_eqb_spec. intros H. apply Z.eqb_eq in H. exact (wZ_inj a b H). Qed.

Lemma xbs_eqb_eq : forall l1 l2, xbs_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|a r IH]; intros [|b r2] H; cbn [xbs_eqb] in H; try discriminate; [reflexivity|].
  apply land_true in H as [H1 H2]. rewrite (IH r2 H2). f_equal.
  destruct a as [x| |t1 o1 i1], b as [y| |t2 o2 i2]; try discriminate; [|reflexivity|].
  - apply Uint63.eqb_spec in H1. subst. reflexivity.
  - apply land_true in H1 as [H1 H3]. apply land_true in H1 as [Hi Ho]. apply Nat.eqb_eq in Hi. apply w_eqb_eq in Ho. apply teqb_eq in H3.
    subst. reflexivity.
Qed.

Lemma xv_eqb_eq (a b : xv) : xv_eqb a b = true -> a = b.
Proof.
  destruct a, b; cbn [xv_eqb]; intros H; try discriminate; try reflexivity.
  - apply w_eqb_eq in H. subst. reflexivity.
  - apply land_true in H as [H1 H2]. apply w_eqb_eq in H1. apply teqb_eq in H2. subst. reflexivity.
  - apply land_true in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply land_true in H as [H1 H2]. apply w_eqb_eq in H1. apply w_eqb_eq in H2. subst. reflexivity.
  - apply xbs_eqb_eq in H. subst. reflexivity.
Qed.

Lemma cell_eqb_eq (c d : cell) : cell_eqb c d = true -> c = d.
Proof.
  destruct c, d; cbn [cell_eqb]; intros H; try discriminate.
  - apply w_eqb_eq in H. subst. reflexivity.
  - apply xbs_eqb_eq in H. subst. reflexivity.
Qed.

Lemma kind_eqb_eq (k1 k2 : rkind) : kind_eqb k1 k2 = true -> k1 = k2.
Proof.
  destruct k1 as [| | |w1 i1|p1], k2 as [| | |w2 i2|p2]; cbn [kind_eqb]; intros H; try discriminate; try reflexivity.
  - apply land_true in H as [H1 H2]. apply Bool.eqb_prop in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
  - apply land_true in H as [H H3]. apply land_true in H as [H1 H2]. apply N.eqb_eq in H1. apply N.eqb_eq in H2. apply N.eqb_eq in H3.
    destruct p1, p2. cbn in *. subst. reflexivity.
Qed.

Lemma fields_eqb_eq (R1 R2 : region) : fields_eqb R1 R2 = true ->
  rg_ts R2 = rg_ts R1 /\ rg_bo R2 = rg_bo R1 /\ rg_n R2 = rg_n R1 /\ rg_kind R2 = rg_kind R1 /\ rg_d R2 = rg_d R1.
Proof.
  unfold fields_eqb. intros H. apply land_true in H as [H H5]. apply land_true in H as [H H4]. apply land_true in H as [H H3].
  apply land_true in H as [H1 H2]. apply w_eqb_eq in H1. apply Uint63.eqb_spec in H2. apply Nat.eqb_eq in H3. apply kind_eqb_eq in H4. apply teqb_eq in H5.
  repeat split; congruence.
Qed.

Lemma vjoin_l (ρ : valuation) (sa sb : store) (a b : xv) (w : bv 64) : sat ρ sa -> xv_val ρ a w -> xv_val ρ (vjoin sa sb a b) w.
Proof.
  intros Hs Ha. unfold vjoin. destruct (xv_eqb a b); [exact Ha|].
  destruct (xrange sa a) as [[l1 h1]|] eqn:E1; [|exact I]. destruct (xrange sb b) as [[l2 h2]|]; [|exact I].
  pose proof (xrange_sound ρ sa a w Hs Ha _ E1) as H. cbn [fst snd] in H. apply mk_rng_sound. lia.
Qed.

Lemma vjoin_r (ρ : valuation) (sa sb : store) (a b : xv) (w : bv 64) : sat ρ sb -> xv_val ρ b w -> xv_val ρ (vjoin sa sb a b) w.
Proof.
  intros Hs Hb. unfold vjoin. destruct (xv_eqb a b) eqn:E; [apply xv_eqb_eq in E; subst; exact Hb|].
  destruct (xrange sa a) as [[l1 h1]|]; [|exact I]. destruct (xrange sb b) as [[l2 h2]|] eqn:E2; [|exact I].
  pose proof (xrange_sound ρ sb b w Hs Hb _ E2) as H. cbn [fst snd] in H. apply mk_rng_sound. lia.
Qed.

Lemma bjoin1_l (ρ : valuation) (a b : xb) (z : Z) : xb_z ρ a z -> xb_z ρ (bjoin1 a b) z.
Proof.
  intros H. destruct a as [x| |t1 o1 i1], b as [y| |t2 o2 i2]; cbn [bjoin1]; try exact I.
  - destruct (x =? y)%uint63; [exact H | exact I].
  - destruct (Nat.eqb i1 i2 &&& w_eqb o1 o2 &&& teqb t1 t2); [exact H | exact I].
Qed.

Lemma bjoin1_r (ρ : valuation) (a b : xb) (z : Z) : xb_z ρ b z -> xb_z ρ (bjoin1 a b) z.
Proof.
  intros H. destruct a as [x| |t1 o1 i1], b as [y| |t2 o2 i2]; cbn [bjoin1]; try exact I.
  - destruct (eqbP x y) as [E|E]; [|exact I]. apply to_Z_inj in E. subst. exact H.
  - destruct (Nat.eqb i1 i2 &&& w_eqb o1 o2 &&& teqb t1 t2) eqn:E; [|exact I].
    apply land_true in E as [E E3]. apply land_true in E as [E1 E2]. apply Nat.eqb_eq in E1. apply w_eqb_eq in E2. apply teqb_eq in E3. subst. exact H.
Qed.

Lemma cjoin_byte (c d : cell) (i : nat) : (i < 8)%nat -> cell_eqb c d = false -> cbyte (cjoin c d) i = bjoin1 (cbyte c i) (cbyte d i).
Proof.
  intros Hi E. unfold cjoin. rewrite E. cbn [cbyte]. do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma cjoin_l (ρ : valuation) (c d : cell) (i : nat) (z : Z) : (i < 8)%nat -> xb_z ρ (cbyte c i) z -> xb_z ρ (cbyte (cjoin c d) i) z.
Proof.
  intros Hi H. destruct (cell_eqb c d) eqn:E; [unfold cjoin; rewrite E; exact H|]. rewrite cjoin_byte by assumption. apply bjoin1_l. exact H.
Qed.

Lemma cjoin_r (ρ : valuation) (c d : cell) (i : nat) (z : Z) : (i < 8)%nat -> xb_z ρ (cbyte d i) z -> xb_z ρ (cbyte (cjoin c d) i) z.
Proof.
  intros Hi H. destruct (cell_eqb c d) eqn:E; [unfold cjoin; rewrite E; apply cell_eqb_eq in E; subst; exact H|].
  rewrite cjoin_byte by assumption. apply bjoin1_r. exact H.
Qed.

Definition tl_ {A : Type} (t : itrie A) : itrie A := match t with INode l _ => l | _ => IEmpty end.
Definition tr_ {A : Type} (t : itrie A) : itrie A := match t with INode _ r => r | _ => IEmpty end.

Lemma iget_S {A : Type} (d : nat) (t : itrie A) (k : int) :
  iget (S d) t k = if iodd k then iget d (tr_ t) (k >> 1)%uint63 else iget d (tl_ t) (k >> 1)%uint63.
Proof. destruct t; cbn [iget tl_ tr_]; rewrite ?iget_empty; destruct (iodd k); reflexivity. Qed.

Lemma rjoin_iget (sa sb : store) : forall (d : nat) (ta tb : itrie xv) (k : int),
  iget d (rjoin d sa sb ta tb) k =
  match iget d ta k, iget d tb k with
  | None, None => None
  | oa, ob => Some (vjoin sa sb (match oa with Some v => v | None => XL w_zero end) (match ob with Some v => v | None => XL w_zero end))
  end.
Proof.
  induction d as [|d IH]; intros ta tb k.
  - destruct ta as [|a|], tb as [|b|]; reflexivity.
  - assert (E : rjoin (S d) sa sb ta tb = match ta, tb with IEmpty, IEmpty => IEmpty | _, _ => INode (rjoin d sa sb (tl_ ta) (tl_ tb)) (rjoin d sa sb (tr_ ta) (tr_ tb)) end)
      by (destruct ta, tb; reflexivity).
    rewrite E. rewrite (iget_S d ta k), (iget_S d tb k).
    destruct ta as [|a|la ra]; [destruct tb as [|b|lb rb]|..].
    1: { cbn [tl_ tr_]. rewrite !iget_empty. destruct (iodd k); reflexivity. }
    all: cbn [iget]; destruct (iodd k); rewrite IH; reflexivity.
Qed.

Lemma aget_rjoin (sa sb : store) (ta tb : aregs) (r : int) :
  aget (rjoin 5 sa sb ta tb) r = vjoin sa sb (aget ta r) (aget tb r).
Proof.
  unfold aget. destruct (r =? 0)%uint63; [reflexivity|]. rewrite rjoin_iget.
  destruct (iget 5 ta r), (iget 5 tb r); reflexivity.
Qed.

Lemma RRegs_rjoin_l (ρ : valuation) (sa sb : store) (ta tb : aregs) (ms : machine_state) :
  sat ρ sa -> RRegs ρ ta ms -> RRegs ρ (rjoin 5 sa sb ta tb) ms.
Proof. intros Hs H r. rewrite aget_rjoin. apply vjoin_l; [exact Hs | exact (H r)]. Qed.

Lemma RRegs_rjoin_r (ρ : valuation) (sa sb : store) (ta tb : aregs) (ms : machine_state) :
  sat ρ sb -> RRegs ρ tb ms -> RRegs ρ (rjoin 5 sa sb ta tb) ms.
Proof. intros Hs H r. rewrite aget_rjoin. apply vjoin_r; [exact Hs | exact (H r)]. Qed.

Section Mem.
Variable segs : list Segment.

Lemma iodd_b2z (k : int) : to_Z k = 2 * to_Z (k >> 1)%uint63 + (if iodd k then 1 else 0).
Proof.
  rewrite iodd_spec, phi_half. pose proof (Z.div_mod (to_Z k) 2 ltac:(lia)) as H. pose proof (Z.mod_pos_bound (to_Z k) 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (to_Z k mod 2) 1); lia.
Qed.

Lemma int_lin (acc w k : int) : to_Z acc + to_Z w * to_Z k < 2 ^ 62 -> to_Z (acc + w * k)%uint63 = to_Z acc + to_Z w * to_Z k.
Proof.
  intros H. pose proof (to_Z_bounded acc). pose proof (to_Z_bounded w). pose proof (to_Z_bounded k).
  assert (0 <= to_Z w * to_Z k) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite add_spec, mul_spec. change wB with (2 ^ 63). rewrite (Z.mod_small (to_Z w * to_Z k)) by lia. apply Z.mod_small. lia.
Qed.

Lemma tjoin_iget (kd : rkind) : forall (d : nat) (ta tb : itrie cell) (acc w k : int),
  to_Z k < 2 ^ Z.of_nat d -> to_Z acc + to_Z w * (2 ^ Z.of_nat d - 1) <= 2 ^ 61 -> 0 < to_Z w ->
  iget d (tjoin segs kd d ta tb acc w) k =
  match iget d ta k, iget d tb k with
  | None, None => None
  | oa, ob => let df := default_cell segs kd (acc + w * k)%uint63 in
              Some (cjoin (match oa with Some c => c | None => df end) (match ob with Some c => c | None => df end))
  end.
Proof.
  induction d as [|d IH]; intros ta tb acc w k Hk Hacc Hw.
  - change (2 ^ Z.of_nat 0) with 1 in Hk. pose proof (to_Z_bounded k) as Hkb.
    assert (k = 0%uint63) by (apply to_Z_inj; change (to_Z 0%uint63) with 0; lia). subst k.
    assert (E0 : (acc + w * 0)%uint63 = acc).
    { apply to_Z_inj. rewrite int_lin; change (to_Z 0%uint63) with 0; rewrite Z.mul_0_r; pose proof (to_Z_bounded acc); lia. }
    rewrite E0. destruct ta as [|a|], tb as [|b|]; reflexivity.
  - assert (E : tjoin segs kd (S d) ta tb acc w = match ta, tb with IEmpty, IEmpty => IEmpty
               | _, _ => INode (tjoin segs kd d (tl_ ta) (tl_ tb) acc (w << 1)%uint63) (tjoin segs kd d (tr_ ta) (tr_ tb) (acc + w)%uint63 (w << 1)%uint63) end)
      by (destruct ta, tb; reflexivity).
    rewrite E. rewrite (iget_S d ta k), (iget_S d tb k).
    pose proof (to_Z_bounded k) as Hkb. pose proof (to_Z_bounded acc) as Hab. pose proof (to_Z_bounded w) as Hwb.
    pose proof (to_Z_bounded (k >> 1)%uint63) as Hk1b.
    assert (Hp : 2 ^ Z.of_nat (S d) = 2 * 2 ^ Z.of_nat d) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
    assert (Hpd : 1 <= 2 ^ Z.of_nat d) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat d) ltac:(lia) ltac:(lia)); lia).
    rewrite Hp in Hk, Hacc.
    set (P := 2 ^ Z.of_nat d) in *. set (W := to_Z w) in *.
    assert (HWP : W * (2 * P - 1) = 2 * (W * (P - 1)) + W) by ring. rewrite HWP in Hacc.
    assert (HW0 : 0 <= W * (P - 1)) by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (iodd_b2z k) as Hk2. set (K1 := to_Z (k >> 1)%uint63) in *.
    assert (Hk1 : K1 < P) by (destruct (iodd k); lia).
    assert (HWK : W * K1 <= W * (P - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (HWK0 : 0 <= W * K1) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hw2 : to_Z (w << 1)%uint63 = 2 * W).
    { rewrite lsl_spec. change (to_Z 1%uint63) with 1. change (2 ^ 1) with 2. change wB with (2 ^ 63). fold W. rewrite Z.mod_small; lia. }
    assert (Haw : to_Z (acc + w)%uint63 = to_Z acc + W) by (rewrite add_spec; change wB with (2 ^ 63); fold W; apply Z.mod_small; lia).
    assert (Hkey : (acc + w * k)%uint63 = if iodd k then ((acc + w) + (w << 1) * (k >> 1))%uint63 else (acc + (w << 1) * (k >> 1))%uint63).
    { assert (EK : W * to_Z k = 2 * (W * K1) + (if iodd k then W else 0)) by (rewrite Hk2; destruct (iodd k); ring).
      destruct (iodd k); apply to_Z_inj; rewrite !int_lin; fold W K1; rewrite ?Hw2, ?Haw, ?EK; try lia;
        replace (2 * W * K1) with (2 * (W * K1)) by ring; lia. }
    assert (Hrec1 : to_Z acc + to_Z (w << 1)%uint63 * (P - 1) <= 2 ^ 61) by (rewrite Hw2; replace (2 * W * (P - 1)) with (2 * (W * (P - 1))) by ring; lia).
    assert (Hrec2 : to_Z (acc + w)%uint63 + to_Z (w << 1)%uint63 * (P - 1) <= 2 ^ 61) by (rewrite Haw, Hw2; replace (2 * W * (P - 1)) with (2 * (W * (P - 1))) by ring; lia).
    destruct ta as [|a|la ra]; [destruct tb as [|b|lb rb]|..].
    1: { cbn [tl_ tr_]. rewrite !iget_empty. destruct (iodd k); reflexivity. }
    all: cbn [iget]; rewrite Hkey; destruct (iodd k) eqn:Eo; rewrite IH; try reflexivity; try exact Hk1; try (rewrite Hw2; lia); first [exact Hrec1 | exact Hrec2].
Qed.

Lemma regjoin_fields (R1 R2 R : region) : regjoin segs R1 R2 = Some R -> same_fields R1 R /\ same_fields R2 R.
Proof.
  unfold regjoin. rewrite (proj1 (tjoin2_eq segs _ _ _ _ _ _)). destruct (fields_eqb R1 R2) eqn:E; [|discriminate]. intros H. injection H as <-.
  destruct (fields_eqb_eq R1 R2 E) as (F1 & F2 & F3 & F4 & F5). split; repeat split; cbn [with_cells rg_ts rg_bo rg_n rg_kind rg_d]; congruence.
Qed.

Lemma regjoin_rbyte (ρ : valuation) (R1 R2 R : region) (y : int) (z : Z) :
  regjoin segs R1 R2 = Some R -> to_Z (rg_n R1) <= 8 * 2 ^ Z.of_nat (rg_d R1) -> (rg_d R1 <= 44)%nat -> to_Z y < to_Z (rg_n R1) ->
  (xb_z ρ (rbyte segs R1 y) z -> xb_z ρ (rbyte segs R y) z) /\ (xb_z ρ (rbyte segs R2 y) z -> xb_z ρ (rbyte segs R y) z).
Proof.
  unfold regjoin. rewrite (proj1 (tjoin2_eq segs _ _ _ _ _ _)). destruct (fields_eqb R1 R2) eqn:E; [|discriminate]. intros H Hd Hd44 Hy. injection H as <-.
  destruct (fields_eqb_eq R1 R2 E) as (F1 & F2 & F3 & F4 & F5).
  pose proof (key_small R1 y Hd Hy) as Hk. pose proof (to_Z_bounded y) as Hyb.
  assert (H60 : to_Z y < 2 ^ 60).
  { assert (2 ^ Z.of_nat (rg_d R1) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hp : 2 ^ Z.of_nat (rg_d R1) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  unfold rbyte at 2 4. unfold get_cell_opt. cbn [with_cells rg_d rg_cells rg_kind].
  rewrite tjoin_iget by (try exact Hk; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia).
  assert (Ek : (0 + 1 * (y >> 3))%uint63 = (y >> 3)%uint63).
  { apply to_Z_inj. rewrite add_spec, mul_spec. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
    rewrite Z.mul_1_l, Z.add_0_l, Z.mod_mod by (change wB with (2^63); lia). apply Z.mod_small. apply to_Z_bounded. }
  rewrite Ek.
  pose proof (cbyte_cell_of segs R1 y H60) as C1. pose proof (cbyte_cell_of segs R2 y H60) as C2.
  unfold cell_of, get_cell_opt in C1, C2. rewrite F4, F5 in C2.
  destruct (iget (rg_d R1) (rg_cells R1) (y >> 3)%uint63) as [c1|] eqn:E1; destruct (iget (rg_d R1) (rg_cells R2) (y >> 3)%uint63) as [c2|] eqn:E2; cbv zeta.
  4: { unfold rbyte, get_cell_opt. rewrite E1, F5, E2, F4. split; exact (fun X => X). }
  all: rewrite <- C1, <- C2; split; [apply cjoin_l | apply cjoin_r]; apply i2n_lt8.
Qed.

Lemma RRegion_cover (ρ : valuation) (m : word -> option byte) (R1 R : region) :
  same_fields R1 R -> (forall y z, to_Z y < to_Z (rg_n R1) -> xb_z ρ (rbyte segs R1 y) z -> xb_z ρ (rbyte segs R y) z) ->
  RRegion segs ρ m R1 -> RRegion segs ρ m R.
Proof.
  intros [F1 [F2 [F3 [F4 F5]]]] Hc H.
  assert (Hb : rbase ρ R = rbase ρ R1) by (unfold rbase; rewrite F1, F2; reflexivity).
  assert (H0 : RRegion0 segs ρ m R1 -> RRegion0 segs ρ m R).
  { intros H0 y Hy. rewrite F3 in Hy. rewrite Hb, F4. destruct (H0 y Hy) as [[b [Hbv Hab]] Hw].
    split; [exists b; split; [exact Hbv | exact (Hc y _ Hy Hab)] | exact Hw]. }
  unfold RRegion in *. rewrite F4. destruct (rg_kind R1); try (apply H0; exact H). rewrite Hb, F3. exact H.
Qed.

Lemma regjoin_RRegion_l (ρ : valuation) (m : word -> option byte) (R1 R2 R : region) :
  regjoin segs R1 R2 = Some R -> region_wf ρ R1 -> RRegion segs ρ m R1 -> RRegion segs ρ m R.
Proof.
  intros HJ Hwf. destruct (regjoin_fields R1 R2 R HJ) as [S1 _]. destruct Hwf as [_ [_ [Hd [Hd44 _]]]].
  apply RRegion_cover; [exact S1|]. intros y z Hy. exact (proj1 (regjoin_rbyte ρ R1 R2 R y z HJ Hd Hd44 Hy)).
Qed.

Lemma regjoin_RRegion_r (ρ : valuation) (m : word -> option byte) (R1 R2 R : region) :
  regjoin segs R1 R2 = Some R -> region_wf ρ R2 -> RRegion segs ρ m R2 -> RRegion segs ρ m R.
Proof.
  intros HJ Hwf. destruct (regjoin_fields R1 R2 R HJ) as [[G1 [G2 [G3 [G4 G5]]]] S2]. pose proof S2 as [F1 [F2 [F3 [F4 F5]]]].
  destruct Hwf as [_ [_ [Hd [Hd44 _]]]].
  assert (En : rg_n R1 = rg_n R2) by congruence. assert (Ed : rg_d R1 = rg_d R2) by congruence.
  apply RRegion_cover; [exact S2|]. intros y z Hy. refine (proj2 (regjoin_rbyte ρ R1 R2 R y z HJ _ _ _)); rewrite ?En, ?Ed; assumption.
Qed.

Lemma mjoin_fields : forall A B J, mjoin segs A B = Some J -> Forall2 same_fields A J /\ Forall2 same_fields B J.
Proof.
  induction A as [|R1 A IH]; intros [|R2 B] J H; cbn [mjoin] in H; try discriminate.
  - injection H as <-. split; constructor.
  - destruct (regjoin segs R1 R2) as [R|] eqn:E1; [|discriminate]. destruct (mjoin segs A B) as [l|] eqn:E2; [|discriminate]. injection H as <-.
    destruct (regjoin_fields R1 R2 R E1) as [S1 S2]. destruct (IH B l E2) as [I1 I2]. split; constructor; assumption.
Qed.

Lemma mjoin_RMem_l (ρ : valuation) (m : word -> option byte) : forall A B J, mjoin segs A B = Some J -> RMem segs ρ A m -> RMem segs ρ J m.
Proof.
  intros A B J HJ [Hok HR]. split; [exact (regions_ok_same ρ A J (proj1 (mjoin_fields A B J HJ)) Hok)|].
  revert B J HJ Hok HR. induction A as [|R1 A IH]; intros [|R2 B] J H Hok HR; cbn [mjoin] in H; try discriminate.
  - injection H as <-. constructor.
  - destruct (regjoin segs R1 R2) as [R|] eqn:E1; [|discriminate]. destruct (mjoin segs A B) as [l|] eqn:E2; [|discriminate]. injection H as <-.
    destruct Hok as [Hw [_ Hok']]. apply Forall_cons_iff in HR as [HR1 HR2].
    constructor; [exact (regjoin_RRegion_l ρ m R1 R2 R E1 Hw HR1) | exact (IH B l E2 Hok' HR2)].
Qed.

Lemma mjoin_RMem_r (ρ : valuation) (m : word -> option byte) : forall A B J, mjoin segs A B = Some J -> RMem segs ρ B m -> RMem segs ρ J m.
Proof.
  intros A B J HJ [Hok HR]. split; [exact (regions_ok_same ρ B J (proj2 (mjoin_fields A B J HJ)) Hok)|].
  revert B J HJ Hok HR. induction A as [|R1 A IH]; intros [|R2 B] J H Hok HR; cbn [mjoin] in H; try discriminate.
  - injection H as <-. constructor.
  - destruct (regjoin segs R1 R2) as [R|] eqn:E1; [|discriminate]. destruct (mjoin segs A B) as [l|] eqn:E2; [|discriminate]. injection H as <-.
    destruct Hok as [Hw [_ Hok']]. apply Forall_cons_iff in HR as [HR1 HR2].
    constructor; [exact (regjoin_RRegion_r ρ m R1 R2 R E1 Hw HR1) | exact (IH B l E2 Hok' HR2)].
Qed.

End Mem.

Lemma boxjoin_iget : forall (d : nat) (ta tb : itrie (Z * Z)) (k : int) (i : Z * Z),
  iget d (boxjoin ta tb) k = Some i ->
  exists ia ib, iget d ta k = Some ia /\ iget d tb k = Some ib /\ fst i = Z.min (fst ia) (fst ib) /\ snd i = Z.max (snd ia) (snd ib).
Proof.
  induction d as [|d IH]; intros ta tb k i H.
  - destruct ta as [|[l1 h1]|], tb as [|[l2 h2]|]; cbn [boxjoin iget] in H; try discriminate.
    injection H as <-. exists (l1, h1), (l2, h2). repeat split.
  - destruct ta as [|[l1 h1]|a1 a2], tb as [|[l2 h2]|b1 b2]; cbn [boxjoin iget] in H; try discriminate.
    cbn [iget]. destruct (iodd k); exact (IH _ _ _ i H).
Qed.

Lemma box_ok_join_l (ρ : valuation) (ta tb : itrie (Z * Z)) : box_ok ρ ta -> box_ok ρ (boxjoin ta tb).
Proof.
  intros H x i Hx Hg. destruct (boxjoin_iget bdepth ta tb x i Hg) as [ia [ib [Ea [_ [E1 E2]]]]].
  pose proof (H x ia Hx Ea). lia.
Qed.

Lemma box_ok_join_r (ρ : valuation) (ta tb : itrie (Z * Z)) : box_ok ρ tb -> box_ok ρ (boxjoin ta tb).
Proof.
  intros H x i Hx Hg. destruct (boxjoin_iget bdepth ta tb x i Hg) as [ia [ib [_ [Eb [E1 E2]]]]].
  pose proof (H x ib Hx Eb). lia.
Qed.

Lemma lin_eqb'_eq (f g : lin) : lin_eqb' f g = true -> f = g.
Proof.
  destruct f as [c ts], g as [d us]. unfold lin_eqb'. cbn [fst snd]. intros H. apply land_true in H as [H1 H2].
  apply Z.eqb_eq in H1. apply teqb_eq in H2. subst. reflexivity.
Qed.

Lemma ffind_spec (f : lin) (l : list fact) (fb : fact) : ffind f l = Some fb -> In fb l /\ fc_hole fb = false /\ fc_f fb = f.
Proof.
  induction l as [|fc r IH]; cbn [ffind]; [discriminate|].
  destruct (negb (fc_hole fc) &&& lin_eqb' f (fc_f fc)) eqn:E.
  - intros H. injection H as <-. apply land_true in E as [E1 E2]. apply negb_true_iff in E1. apply lin_eqb'_eq in E2.
    split; [left; reflexivity | split; [exact E1 | symmetry; exact E2]].
  - intros H. destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Lemma hole_implied_sat (ρ : valuation) (sb : store) (fc : fact) : sat ρ sb -> fc_hole fc = true -> hole_implied sb fc = true -> fact_sat ρ fc.
Proof.
  intros Hs Eh H. unfold hole_implied in H. destruct (lrange sb (fc_f fc)) as [[lo hi]|] eqn:El; [|discriminate].
  pose proof (lrange_sound ρ sb _ Hs _ El) as Hr. cbn [fst snd] in Hr. unfold fact_sat. rewrite Eh.
  apply lor_true in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma hback_l (ρ : valuation) (sa : store) (l : list fact) : sat ρ sa -> Forall (fact_sat ρ) (hback sa l).
Proof.
  intros Hs. induction l as [|fc r IH]; cbn [hback]; [constructor|].
  destruct (fc_hole fc &&& negb (lexists (hole_eqb fc) (st_facts sa)) &&& hole_implied sa fc) eqn:E; [|exact IH].
  apply land_true in E as [E Ei]. apply land_true in E as [Eh _]. constructor; [exact (hole_implied_sat ρ sa fc Hs Eh Ei) | exact IH].
Qed.

Lemma hback_r (ρ : valuation) (sa : store) (l : list fact) : Forall (fact_sat ρ) l -> Forall (fact_sat ρ) (hback sa l).
Proof.
  intros Hl. induction Hl as [|fc r Hfc Hr IH]; cbn [hback]; [constructor|].
  destruct (fc_hole fc &&& negb (lexists (hole_eqb fc) (st_facts sa)) &&& hole_implied sa fc); [constructor; assumption | exact IH].
Qed.

Lemma fjoin1_l (ρ : valuation) (sb : store) (fc f : fact) : fact_sat ρ fc -> fjoin1 sb fc = Some f -> fact_sat ρ f.
Proof.
  intros Hf H. unfold fjoin1 in H. destruct (fc_hole fc) eqn:Eh.
  - destruct (lexists (hole_eqb fc) (st_facts sb) ||| hole_implied sb fc); [|discriminate]. injection H as <-. exact Hf.
  - unfold fact_sat in Hf. rewrite Eh in Hf.
    destruct (ffind (fc_f fc) (st_facts sb)) as [fb|].
    + injection H as <-. unfold fact_sat. cbn [fc_hole fc_f fc_lo fc_hi]. lia.
    + destruct (lrange sb (fc_f fc)) as [[lo hi]|]; [|discriminate]. injection H as <-. unfold fact_sat. cbn [fc_hole fc_f fc_lo fc_hi]. lia.
Qed.

Lemma fjoin1_r (ρ : valuation) (sb : store) (fc f : fact) : sat ρ sb -> fjoin1 sb fc = Some f -> fact_sat ρ f.
Proof.
  intros Hs H. unfold fjoin1 in H. destruct (fc_hole fc) eqn:Eh.
  - destruct (lexists (hole_eqb fc) (st_facts sb)) eqn:Ex; cbv iota in H.
    2:{ destruct (hole_implied sb fc) eqn:Ei; [|discriminate]. injection H as <-. exact (hole_implied_sat ρ sb fc Hs Eh Ei). }
    injection H as <-.
    apply lexists_exists in Ex as [fb [Hin Hb]]. unfold hole_eqb in Hb.
    apply land_true in Hb as [Hb H4]. apply land_true in Hb as [Hb H3]. apply land_true in Hb as [H1 H2].
    apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. apply lin_eqb'_eq in H4.
    destruct Hs as [_ Hfs]. rewrite Forall_forall in Hfs. pose proof (Hfs fb Hin) as Hfb.
    unfold fact_sat in *. rewrite Eh. rewrite H1 in Hfb. rewrite H2, H3, H4. exact Hfb.
  - destruct (ffind (fc_f fc) (st_facts sb)) as [fb|] eqn:Ef.
    + injection H as <-. destruct (ffind_spec _ _ _ Ef) as [Hin [Hh Hff]].
      destruct Hs as [_ Hfs]. rewrite Forall_forall in Hfs. pose proof (Hfs fb Hin) as Hfb.
      unfold fact_sat in *. rewrite Hh, Hff in Hfb. cbn [fc_hole fc_f fc_lo fc_hi]. lia.
    + destruct (lrange sb (fc_f fc)) as [[lo hi]|] eqn:El; [|discriminate]. injection H as <-.
      pose proof (lrange_sound ρ sb _ Hs _ El) as Hr. cbn [fst snd] in Hr. unfold fact_sat. cbn [fc_hole fc_f fc_lo fc_hi]. lia.
Qed.

Lemma hole_cands_small (x : int) : In x hole_cands -> to_Z x < 2 ^ 16.
Proof. unfold hole_cands. cbn [map In]. intros H. repeat (destruct H as [<-|H]; [cbv; reflexivity|]). destruct H. Qed.

Lemma hjoin_sat (ρ : valuation) (sa sb : store) : box_ok ρ (st_box sa) \/ box_ok ρ (st_box sb) -> Forall (fact_sat ρ) (hjoin sa sb).
Proof.
  intros Hb. unfold hjoin. apply Forall_flat_map. apply Forall_forall. intros x Hx. pose proof (hole_cands_small x Hx) as Hsm.
  unfold hjoin1. destruct (iget bdepth (st_box sa) x) as [[l1 h1]|] eqn:Ea; [|constructor].
  destruct (iget bdepth (st_box sb) x) as [[l2 h2]|] eqn:Eb; [|constructor].
  assert (Hc : (l1 <= ρ x <= h1) \/ (l2 <= ρ x <= h2)).
  { destruct Hb as [Hb|Hb]; [left; exact (Hb x _ Hsm Ea) | right; exact (Hb x _ Hsm Eb)]. }
  destruct (Z.ltb_spec (h1 + 1) l2) as [H1|H1].
  - constructor; [|constructor]. unfold fact_sat. cbn [fc_hole fc_f fc_lo fc_hi]. rewrite leval_lvar. lia.
  - destruct (Z.ltb_spec (h2 + 1) l1) as [H2|H2]; [|constructor].
    constructor; [|constructor]. unfold fact_sat. cbn [fc_hole fc_f fc_lo fc_hi]. rewrite leval_lvar. lia.
Qed.

Lemma fact_eqb_eq (a b : fact) : fact_eqb a b = true -> a = b.
Proof.
  unfold fact_eqb. intros H. apply land_true in H as [H H4]. apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
  apply Bool.eqb_prop in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. apply lin_eqb'_eq in H4.
  destruct a as [fa la ha oa], b as [fb lb hb ob]. cbn [fc_f fc_lo fc_hi fc_hole] in *. subst. reflexivity.
Qed.

Lemma fjoin_l (ρ : valuation) (sb : store) (l : list fact) : Forall (fact_sat ρ) l -> Forall (fact_sat ρ) (fjoin sb l).
Proof.
  intros Hf. induction Hf as [|fc r Hfc Hr IH]; cbn [fjoin]; [constructor|].
  destruct (fjoin1 sb fc) as [f|] eqn:E; [constructor; [exact (fjoin1_l ρ sb fc f Hfc E) | exact IH] | exact IH].
Qed.

Lemma fjoin_r (ρ : valuation) (sb : store) (l : list fact) : sat ρ sb -> Forall (fact_sat ρ) (fjoin sb l).
Proof.
  intros Hs. induction l as [|fc r IH]; cbn [fjoin]; [constructor|].
  destruct (fjoin1 sb fc) as [f|] eqn:E; [constructor; [exact (fjoin1_r ρ sb fc f Hs E) | exact IH] | exact IH].
Qed.

Lemma fzip_l (ρ : valuation) (sa sb : store) : sat ρ sa -> forall la lb, Forall (fact_sat ρ) la -> Forall (fact_sat ρ) (fzip sa sb la lb).
Proof.
  intros Hs. induction la as [|fa ra IH]; intros lb Hl.
  - cbn [fzip]. destruct lb; (apply Forall_app; split; [constructor | exact (hback_l ρ sa _ Hs)]).
  - inversion Hl as [|? ? Hfa Hra]; subst. destruct lb as [|fb rb]; cbn [fzip].
    + apply Forall_app. split; [exact (fjoin_l ρ sb _ Hl) | constructor].
    + destruct (fact_eqb fa fb); [constructor; [exact Hfa | exact (IH rb Hra)]|].
      apply Forall_app. split.
      { unfold fj1. destruct (fjoin1 sb fa) as [f|] eqn:E; [constructor; [exact (fjoin1_l ρ sb fa f Hfa E) | constructor] | constructor]. }
      apply Forall_app. split; [|exact (IH rb Hra)].
      unfold hback1. destruct (fc_hole fb &&& negb (lexists (hole_eqb fb) (st_facts sa)) &&& hole_implied sa fb) eqn:E; [|constructor].
      apply land_true in E as [E Ei]. apply land_true in E as [Eh _]. constructor; [exact (hole_implied_sat ρ sa fb Hs Eh Ei) | constructor].
Qed.

Lemma fzip_r (ρ : valuation) (sa sb : store) : sat ρ sb -> forall la lb, Forall (fact_sat ρ) lb -> Forall (fact_sat ρ) (fzip sa sb la lb).
Proof.
  intros Hs. induction la as [|fa ra IH]; intros lb Hl.
  - cbn [fzip]. destruct lb; (apply Forall_app; split; [constructor | exact (hback_r ρ sa _ Hl)]).
  - destruct lb as [|fb rb]; cbn [fzip].
    + apply Forall_app. split; [exact (fjoin_r ρ sb _ Hs) | constructor].
    + inversion Hl as [|? ? Hfb Hrb]; subst.
      destruct (fact_eqb fa fb) eqn:Ee; [apply fact_eqb_eq in Ee; subst fb; constructor; [exact Hfb | exact (IH rb Hrb)]|].
      apply Forall_app. split.
      { unfold fj1. destruct (fjoin1 sb fa) as [f|] eqn:E; [constructor; [exact (fjoin1_r ρ sb fa f Hs E) | constructor] | constructor]. }
      apply Forall_app. split; [|exact (IH rb Hrb)].
      unfold hback1. destruct (fc_hole fb &&& negb (lexists (hole_eqb fb) (st_facts sa)) &&& hole_implied sa fb); [constructor; [exact Hfb | constructor] | constructor].
Qed.

Lemma Forall_firstn' {X : Type} (P : X -> Prop) (n : nat) (l : list X) : Forall P l -> Forall P (firstn n l).
Proof. intros H. revert n. induction H as [|x r Hx Hr IH]; intros [|n]; cbn [firstn]; constructor; [exact Hx | apply IH]. Qed.

Lemma Forall_skipn' {X : Type} (P : X -> Prop) (n : nat) (l : list X) : Forall P l -> Forall P (skipn n l).
Proof. intros H. revert n. induction H as [|x r Hx Hr IH]; intros [|n]; cbn [skipn]; first [constructor; assumption | apply IH | constructor]. Qed.

Lemma sjoin_l (ρ : valuation) (sa sb : store) : sat ρ sa -> sat ρ (sjoin sa sb).
Proof.
  intros Hs. pose proof Hs as [Hb Hf]. split; [exact (box_ok_join_l ρ _ _ Hb)|]. cbn [sjoin st_facts].
  apply Forall_app. split; [exact (hjoin_sat ρ sa sb (or_introl Hb))|]. unfold fjoin_fast.
  apply Forall_app. split; [exact (fjoin_l ρ sb _ (Forall_firstn' _ _ _ Hf))|].
  apply Forall_app. split; [exact (hback_l ρ sa _ Hs) | exact (fzip_l ρ sa sb Hs _ _ (Forall_skipn' _ _ _ Hf))].
Qed.

Lemma sjoin_r (ρ : valuation) (sa sb : store) : sat ρ sb -> sat ρ (sjoin sa sb).
Proof.
  intros Hs. pose proof Hs as [Hb Hf]. split; [exact (box_ok_join_r ρ _ _ Hb)|]. cbn [sjoin st_facts].
  apply Forall_app. split; [exact (hjoin_sat ρ sa sb (or_intror Hb))|]. unfold fjoin_fast.
  apply Forall_app. split; [exact (fjoin_r ρ sb _ Hs)|].
  apply Forall_app. split; [exact (hback_r ρ sa _ (Forall_firstn' _ _ _ Hf)) | exact (fzip_r ρ sa sb Hs _ _ (Forall_skipn' _ _ _ Hf))].
Qed.

Lemma list_eqb_eq {X : Type} (e : X -> X -> bool) : (forall a b, e a b = true -> a = b) -> forall l1 l2, list_eqb e l1 l2 = true -> l1 = l2.
Proof.
  intros He. induction l1 as [|a r IH]; intros [|b r2] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  apply land_true in H as [H1 H2]. rewrite (He a b H1), (IH r2 H2). reflexivity.
Qed.

Lemma piece_eqb_eq (p q : piece) : piece_eqb p q = true -> p = q.
Proof.
  destruct p as [a|j], q as [b|k]; cbn [piece_eqb]; intros H; try discriminate.
  - unfold xb_eqb1 in H. apply xbs_eqb_eq in H. injection H as <-. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Lemma exp_eqb_eq (x y : aent * lin * Z) : exp_eqb x y = true -> x = y.
Proof.
  destruct x as [[e1 f1] z1], y as [[e2 f2] z2]. unfold exp_eqb. cbn [fst snd]. intros H.
  apply land_true in H as [H H3]. apply land_true in H as [H1 H2]. apply aent_eqb_eq in H1. apply lin_eqb_eq in H2. apply Z.eqb_eq in H3.
  subst. reflexivity.
Qed.

Lemma afd_eqb_eq (f g : afd) : afd_eqb f g = true -> f = g.
Proof.
  destruct f, g; cbn [afd_eqb]; intros H; try discriminate; try reflexivity.
  - apply land_true in H as [H H4]. apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
    apply lin_eqb_eq in H1. apply Uint63.eqb_spec in H2. apply Uint63.eqb_spec in H3. apply Uint63.eqb_spec in H4. subst. reflexivity.
  - apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
    apply Uint63.eqb_spec in H1. apply Uint63.eqb_spec in H2. apply Uint63.eqb_spec in H3. subst. reflexivity.
Qed.

Lemma model_eqb_eq (a b : amodel) : model_eqb a b = true -> b = set_next a (am_next b).
Proof.
  unfold model_eqb. intros H.
  apply land_true in H as [H H9]. apply land_true in H as [H H8]. apply land_true in H as [H H7]. apply land_true in H as [H H6].
  apply land_true in H as [H H5]. apply land_true in H as [H H4]. apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
  apply Bool.eqb_prop in H1. apply lin_eqb_eq in H3. apply lin_eqb_eq in H4. apply lin_eqb_eq in H5. apply afd_eqb_eq in H6.
  apply (list_eqb_eq _ piece_eqb_eq) in H7. apply (list_eqb_eq _ exp_eqb_eq) in H8. apply (list_eqb_eq _ aent_eqb_eq) in H9.
  assert (H2' : am_tid a = am_tid b).
  { unfold opt_xv_eqb in H2. destruct (am_tid a), (am_tid b); try discriminate; [apply xv_eqb_eq in H2; subst|]; reflexivity. }
  destruct a, b. cbn in *. unfold set_next. cbn. subst. reflexivity.
Qed.

Lemma RResv_join_l (ρ : valuation) (a b : rsv) (mr : option word) : RResv ρ a mr -> RResv ρ (rsv_join a b) mr.
Proof. destruct a, b; cbn [rsv_join RResv]; try exact (fun _ => I); try exact (fun X => X). destruct (xv_eqb v v0); [exact (fun X => X) | exact (fun _ => I)]. Qed.

Lemma RResv_join_r (ρ : valuation) (a b : rsv) (mr : option word) : RResv ρ b mr -> RResv ρ (rsv_join a b) mr.
Proof.
  destruct a, b; cbn [rsv_join RResv]; try exact (fun _ => I); try exact (fun X => X).
  destruct (xv_eqb v v0) eqn:E; [apply xv_eqb_eq in E; subst; exact (fun X => X) | exact (fun _ => I)].
Qed.

Section Join.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable MR : valuation -> amodel -> Model -> Prop.
Hypothesis MR_nx : forall ρ am m nx, MR ρ am m -> MR ρ (set_next am nx) m.

Notation RR ρ := (R segs amodel (MR ρ) LIM ρ).

Lemma some_inj {X : Type} (a b : X) : Some a = Some b -> a = b.
Proof. intros H. injection H. exact (fun E => E). Qed.

Lemma ajoin_parts (A B J : astate amodel) : ajoin segs A B = Some J ->
  a_pc B = a_pc A /\ a_model B = set_next (a_model A) (am_next (a_model B)) /\
  exists mem, mjoin segs (a_mem A) (a_mem B) = Some mem /\ J = ajoin_state A B mem.
Proof.
  unfold ajoin. destruct (w_eqb (a_pc A) (a_pc B) &&& model_eqb (a_model A) (a_model B)) eqn:E; [|discriminate].
  apply land_true in E as [E1 E2]. apply w_eqb_eq in E1. apply model_eqb_eq in E2.
  destruct (mjoin segs (a_mem A) (a_mem B)) as [mem|] eqn:Em; [|discriminate]. intros H. apply some_inj in H.
  split; [symmetry; exact E1|]. split; [exact E2|]. exists mem. split; [reflexivity | symmetry; exact H].
Qed.

Lemma ajoin_R_l (ρ : valuation) (A B J : astate amodel) (c : config) : ajoin segs A B = Some J -> RR ρ A c -> RR ρ J c.
Proof.
  intros HJ HR. destruct (ajoin_parts A B J HJ) as [Epc [Emod [mem [Em ->]]]].
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  destruct (mjoin_fields segs _ _ _ Em) as [HF _].
  constructor; unfold ajoin_state; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  - apply RRegs_rjoin_l; assumption.
  - apply RResv_join_l. exact Hres.
  - exact (mjoin_RMem_l segs ρ _ _ _ _ Em Hmem).
  - apply MR_nx. exact Hmod.
  - split; [lia | exact Hl].
  - apply sjoin_l. exact Hsat.
  - exact (hs_ok_geom ρ _ _ _ HF Hhs).
  - exact (comp_inv_geom segs ρ _ _ _ HF Hcomp).
  - exact (na_ok_geom segs ρ _ _ _ _ HF Hna).
Qed.

Lemma ajoin_R_r (ρ : valuation) (A B J : astate amodel) (c : config) : ajoin segs A B = Some J -> RR ρ B c -> RR ρ J c.
Proof.
  intros HJ HR. destruct (ajoin_parts A B J HJ) as [Epc [Emod [mem [Em ->]]]].
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  destruct (mjoin_fields segs _ _ _ Em) as [_ HF]. rewrite Epc in Hpc, Hal.
  constructor; unfold ajoin_state; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  - apply RRegs_rjoin_r; assumption.
  - apply RResv_join_r. exact Hres.
  - exact (mjoin_RMem_r segs ρ _ _ _ _ Em Hmem).
  - rewrite Emod in Hmod. apply (MR_nx ρ _ _ (max_next (am_next (a_model A)) (am_next (a_model B)))) in Hmod. exact Hmod.
  - split; [lia | exact Hl].
  - apply sjoin_r. exact Hsat.
  - exact (hs_ok_geom ρ _ _ _ HF Hhs).
  - exact (comp_inv_geom segs ρ _ _ _ HF Hcomp).
  - exact (na_ok_geom segs ρ _ _ _ _ HF Hna).
Qed.

Lemma ajoin_out_l (A B J : astate amodel) : ajoin segs A B = Some J -> am_out (a_model J) = am_out (a_model A).
Proof. intros HJ. destruct (ajoin_parts A B J HJ) as [_ [_ [mem [_ ->]]]]. reflexivity. Qed.

Lemma ajoin_out_r (A B J : astate amodel) : ajoin segs A B = Some J -> am_out (a_model J) = am_out (a_model B).
Proof. intros HJ. destruct (ajoin_parts A B J HJ) as [_ [Emod [mem [_ ->]]]]. rewrite Emod. reflexivity. Qed.

Theorem join_sound (KT : valuation -> list byte -> TSet) (A B J : astate amodel) :
  ajoin segs A B = Some J -> Sound segs cfg LIM MR KT J -> Sound segs cfg LIM MR KT A /\ Sound segs cfg LIM MR KT B.
Proof.
  intros HJ HS. split; intros ρ c HR o Ho.
  - apply (HS ρ c (ajoin_R_l ρ A B J c HJ HR) o). rewrite (ajoin_out_l A B J HJ). exact Ho.
  - apply (HS ρ c (ajoin_R_r ρ A B J c HJ HR) o). rewrite (ajoin_out_r A B J HJ). exact Ho.
Qed.

Lemma ajoin_nm_R_l (ρ : valuation) (A B J : astate amodel) (c : config) : ajoin_nm A B = Some J -> RR ρ A c -> RR ρ J c.
Proof.
  unfold ajoin_nm. destruct (w_eqb (a_pc A) (a_pc B)); [|discriminate]. intros HJ HR. apply some_inj in HJ. subst J.
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  constructor; unfold ajoin_state; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  - apply RRegs_rjoin_l; assumption.
  - apply RResv_join_l. exact Hres.
  - apply MR_nx. exact Hmod.
  - split; [lia | exact Hl].
  - apply sjoin_l. exact Hsat.
Qed.

Lemma ajoin_nm_R_r (ρ : valuation) (A B J : astate amodel) (c : config) :
  a_mem B = a_mem A -> a_model B = a_model A -> ajoin_nm A B = Some J -> RR ρ B c -> RR ρ J c.
Proof.
  unfold ajoin_nm. intros Em Emod. destruct (w_eqb (a_pc A) (a_pc B)) eqn:Epc; [|discriminate]. apply w_eqb_eq in Epc.
  intros HJ HR. apply some_inj in HJ. subst J.
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna].
  rewrite <- Epc in Hpc, Hal. rewrite Em in Hmem, Hhs, Hcomp, Hna. rewrite Emod in Hmod.
  constructor; unfold ajoin_state; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  - apply RRegs_rjoin_r; assumption.
  - apply RResv_join_r. exact Hres.
  - apply MR_nx. exact Hmod.
  - split; [lia | exact Hl].
  - apply sjoin_r. exact Hsat.
Qed.

Theorem join_nm_sound (KT : valuation -> list byte -> TSet) (A B J : astate amodel) :
  a_mem B = a_mem A -> a_model B = a_model A -> ajoin_nm A B = Some J ->
  Sound segs cfg LIM MR KT J -> Sound segs cfg LIM MR KT A /\ Sound segs cfg LIM MR KT B.
Proof.
  intros Em Emod HJ HS.
  assert (EJ : am_out (a_model J) = am_out (a_model A)).
  { unfold ajoin_nm in HJ. destruct (w_eqb (a_pc A) (a_pc B)); [|discriminate]. apply some_inj in HJ. subst J. reflexivity. }
  split; intros ρ c HR o Ho.
  - apply (HS ρ c (ajoin_nm_R_l ρ A B J c HJ HR) o). rewrite EJ. exact Ho.
  - apply (HS ρ c (ajoin_nm_R_r ρ A B J c Em Emod HJ HR) o). rewrite EJ, <- Emod. exact Ho.
Qed.

End Join.
