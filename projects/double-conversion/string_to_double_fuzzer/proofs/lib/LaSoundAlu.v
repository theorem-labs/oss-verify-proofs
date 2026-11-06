(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem LaStep LaCheck LaSem LaWf LaSoundVal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF LASV.
Open Scope Z_scope.

Module LASA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma Z_land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  destruct a as [|p|p]; [rewrite Z.land_0_l; lia| |lia].
  destruct b as [|q|q]; [rewrite Z.land_0_r; lia| |lia].
  pose proof (N.land_le_l (N.pos p) (N.pos q)) as H.
  change (Z.of_N (Pos.land p q) <= Z.pos p). change ((Pos.land p q <= N.pos p)%N) in H. lia.
Qed.
Lemma Z_land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros. rewrite Z.land_comm. apply Z_land_le_l; lia. Qed.


Lemma itv_div_sound : forall z i m, 0 < m -> in_itv z i -> in_itv (z / m) (itv_div i m).
Proof.
  intros z [lo hi] m Hm [H1 H2]; unfold itv_div, in_itv; cbn in *.
  destruct lo, hi; cbn; split; try exact I; apply Z.div_le_mono; lia.
Qed.

Lemma lrange_sound : forall rho C l, ctx_ok rho C -> in_itv (evl rho l) (lrange C l).
Proof. intros rho C l HC. apply lrange_ok. exact HC. Qed.
Lemma lrange2_sound : forall rho C l, ctx_ok rho C -> in_itv (evl rho l) (lrange2 C l).
Proof. intros rho C l HC. apply lrange2_ok. exact HC. Qed.

Lemma ihi_sound : forall rho C l h, ctx_ok rho C -> ihi (lrange C l) = Some h -> evl rho l <= h.
Proof. intros rho C l h HC E. pose proof (lrange_sound rho C l HC) as [_ H]. rewrite E in H. exact H. Qed.

(* [comment removed for export] *)
Lemma degrade2 : forall rho st a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho2,
    let p1 := degrade st a in let p2 := degrade (snd p1) b in
    vext rho st rho2 (snd p2) /\ VS rho2 (snd p2)
    /\ val_ok rho2 (fst p1) wa /\ val_ok rho2 (fst p2) wb
    /\ aval_below (fst p1) (s_next (snd p2)) = true /\ aval_below (fst p2) (s_next (snd p2)) = true.
Proof.
  intros rho st a b wa wb HVS Ha Hb Ba Bb.
  destruct (degrade_sound rho st a wa HVS Ha Ba) as (rho1 & E1 & V1 & Ha1 & Ba1).
  destruct (vext_val _ _ _ _ _ _ E1 Bb Hb) as [Hb1 Bb1].
  destruct (degrade_sound rho1 (snd (degrade st a)) b wb V1 Hb1 Bb1) as (rho2 & E2 & V2 & Hb2 & Bb2).
  destruct (vext_val _ _ _ _ _ _ E2 Ba1 Ha1) as [Ha2 Ba2].
  exists rho2. cbn zeta. split; [eapply vext_trans; eauto|]. split; [exact V2|]. split; [exact Ha2|]. split; [exact Hb2|]. split; [exact Ba2|exact Bb2].
Qed.

Lemma VOK_after_ex : forall rho st rho1 st1 p w,
  vext rho st rho1 st1 -> (exists rho', VOK rho1 st1 p rho' w) -> exists rho', VOK rho st p rho' w.
Proof. intros rho st rho1 st1 p w He (rho' & G). exists rho'. eapply VOK_after; eauto. Qed.

Lemma val01 : forall (c : bool), exists z, (if c then Z_to_bv 64 1 else Z_to_bv 64 0) = w64 z /\ 0 <= z <= 1.
Proof. intros c. exists (if c then 1 else 0). split; [destruct c; reflexivity | destruct c; lia]. Qed.

Lemma land_pow2_mod : forall a j, 0 <= a -> 0 <= j -> Z.land a (2 ^ j - 1) = a mod 2 ^ j.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma galign_vext : forall rho st rho' st', (NGLOB <= s_next st)%nat -> vext rho st rho' st' -> galign rho -> galign rho'.
Proof.
  intros rho st rho' st' HN (A & _) G. unfold galign in *.
  rewrite !A by (unfold SYM_SP0, SYM_DATA, SYM_S32, SYM_D16, SYM_R32, NGLOB in *; lia). exact G.
Qed.

Lemma pow2_log2_self : forall u j, j = Z.log2 (u + 1) -> u + 1 = 2 ^ j -> 0 <= j.
Proof. intros u j Hj _. subst. apply Z.log2_nonneg. Qed.

Lemma mod_mod_pow2_le : forall a j k, 0 <= j <= k -> (a mod 2 ^ k) mod 2 ^ j = a mod 2 ^ j.
Proof.
  intros a j k Hjk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma testbit_ones : forall n i, 0 <= n -> 0 <= i -> Z.testbit (Z.ones n) i = Z.ltb i n.
Proof. intros n i Hn Hi. apply Z.testbit_ones_nonneg; lia. Qed.

Lemma land_clear_low : forall a k, 0 <= a < 2 ^ 64 -> 0 < k < 64 ->
  Z.land a (2 ^ 64 - 2 ^ k) = 2 ^ k * (a / 2 ^ k).
Proof.
  intros a k Ha Hk.
  assert (Hmask : 2 ^ 64 - 2 ^ k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
    replace (2 ^ 64) with (2 ^ (64 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite Hmask. rewrite <- Z.shiftr_div_pow2, Z.mul_comm, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i k) as [L|Ge].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    rewrite testbit_ones by lia.
    destruct (Z.ltb_spec (i - k) (64 - k)).
    + apply andb_true_r.
    + rewrite andb_false_r. destruct (Z.eq_dec a 0) as [->|NE]; [rewrite Z.bits_0; reflexivity|].
      rewrite Z.bits_above_log2; [reflexivity|lia|]. assert (Z.log2 a < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma mul_div_mod64 : forall x k, 0 < k < 64 -> (2 ^ k * ((x mod 2 ^ 64) / 2 ^ k)) mod 2 ^ 64 = (2 ^ k * (x / 2 ^ k)) mod 2 ^ 64.
Proof.
  intros x k Hk.
  rewrite (Z.mod_eq x (2 ^ 64)) by lia. set (t := x / 2 ^ 64).
  replace (x - 2 ^ 64 * t) with (x + (- t * 2 ^ (64 - k)) * 2 ^ k)
    by (rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia; replace (64 - k + k) with 64 by lia; lia).
  rewrite Z.div_add by lia. rewrite Z.mul_add_distr_l.
  replace (2 ^ k * (- t * 2 ^ (64 - k))) with ((- t) * 2 ^ 64)
    by (rewrite (Z.mul_comm (2 ^ k)), <- Z.mul_assoc, <- Z.pow_add_r by lia; replace (64 - k + k) with 64 by lia; lia).
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma aand_clear_sound : forall rho st x k wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> wa = w64 (evl rho x) -> lin_below x (s_next st) = true ->
  0 < k < 64 -> bv_unsigned wb = 2 ^ 64 - 2 ^ k ->
  exists rho', VOK rho st (aand_clear st x k) rho' (alu64 ALU_AND wa wb).
Proof.
  intros rho st x k wa wb GA HNG HVS Ha Bx Hk Hub. unfold aand_clear.
  assert (RES : bv_unsigned (alu64 ALU_AND wa wb) = 2 ^ k * (bv_unsigned wa / 2 ^ k)).
  { rewrite and_w64_unsigned, Hub. apply land_clear_low; [apply u64_range | exact Hk]. }
  assert (CORE : forall x', w64 (evl rho x') = wa -> lin_below x' (s_next st) = true ->
     exists rho', VOK rho st (let (v, st') := shr_floor st x' k (itv_div (lrange (s_ctx st) x') (2 ^ k)) in
                              (match v with LV q => LV (lscale (2 ^ k) q) | _ => Top end, st')) rho' (alu64 ALU_AND wa wb)).
  { intros x' Hx' Bx'.
    destruct (shr_floor_sound rho st x' k (itv_div (lrange (s_ctx st) x') (2 ^ k)) GA HVS HNG Bx' ltac:(lia)
                ltac:(apply itv_div_sound; [lia | apply lrange_sound; exact (proj1 HVS)])) as (rho' & A & B & C & D).
    destruct (shr_floor st x' k _) as [v st']. cbn [fst snd] in *.
    exists rho'. unfold VOK; cbn [fst snd]. split; [exact A|]. split; [exact B|].
    destruct v as [|q| |]; try (split; [exact I|reflexivity]).
    cbn in C. cbn [aval_below] in D. split; [|cbn [aval_below]; apply lscale_below; exact D].
    cbn [val_ok]. apply bv_eq. rewrite RES, lscale_sound, <- Hx', !w64_unsigned.
    match goal with |- ?l = _ => replace l with ((2 ^ k * ((evl rho x' mod 2 ^ 64) / 2 ^ k)) mod 2 ^ 64) end.
    2:{ apply Z.mod_small. pose proof (Z.mod_pos_bound (evl rho x') (2 ^ 64) ltac:(lia)) as Hr.
        split; [apply Z.mul_nonneg_nonneg; [lia|apply Z.div_pos; lia]|].
        eapply Z.le_lt_trans; [apply Z.mul_div_le; lia|lia]. }
    rewrite mul_div_mod64 by exact Hk.
    apply (f_equal bv_unsigned) in C. rewrite !w64_unsigned in C.
    rewrite Z.mul_mod, C, <- Z.mul_mod by lia. reflexivity. }
  destruct (uview (s_ctx st) x) as [x'|] eqn:Ux.
  - apply CORE; [|eapply uview_below; eauto]. rewrite Ha. exact (proj1 (uview_sound rho _ x x' (proj1 HVS) Ux)).
  - destruct (sexact (s_ctx st) x).
    + apply CORE; [symmetry; exact Ha | exact Bx].
    + exists rho. apply VOK_top. exact HVS.
Qed.

Lemma mod_pow2_congr : forall a b k, 0 <= k <= 64 -> a mod 2 ^ 64 = b mod 2 ^ 64 -> a mod 2 ^ k = b mod 2 ^ k.
Proof. intros a b k Hk H. rewrite <- (mod_mod_pow2_le a k 64), <- (mod_mod_pow2_le b k 64) by lia. rewrite H. reflexivity. Qed.

Lemma aand_low_sound : forall rho st x k wa wb p,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> wa = w64 (evl rho x) -> lin_below x (s_next st) = true ->
  0 <= k <= 64 -> bv_unsigned wb = 2 ^ k - 1 -> aand_low st x k = Some p ->
  exists rho', VOK rho st p rho' (alu64 ALU_AND wa wb).
Proof.
  intros rho st x k wa wb p GA HNG HVS Ha Bx Hk Hub H. unfold aand_low in H.
  assert (RES : bv_unsigned (alu64 ALU_AND wa wb) = bv_unsigned wa mod 2 ^ k).
  { rewrite and_w64_unsigned, Hub. apply land_pow2_mod; [apply u64_range | lia]. }
  assert (CORE : forall x', w64 (evl rho x') = wa -> lin_below x' (s_next st) = true ->
     (let (v, st') := shr_floor st x' k (itv_div (lrange (s_ctx st) x') (2 ^ k)) in
      match v with LV q => Some (LV (lsub x' (lscale (2 ^ k) q)), st') | _ => None end) = Some p ->
     exists rho', VOK rho st p rho' (alu64 ALU_AND wa wb)).
  { intros x' Hx' Bx' Hp.
    destruct (shr_floor_sound rho st x' k (itv_div (lrange (s_ctx st) x') (2 ^ k)) GA HVS HNG Bx' ltac:(lia)
                ltac:(apply itv_div_sound; [lia | apply lrange_sound; exact (proj1 HVS)])) as (rho' & A & B & C & D).
    destruct (shr_floor st x' k _) as [v st']. cbn [fst snd] in *.
    destruct v as [|q| |]; try discriminate. injection Hp; intros <-.
    cbn in C. cbn [aval_below] in D.
    exists rho'. unfold VOK; cbn [fst snd]. split; [exact A|]. split; [exact B|].
    split; [|cbn [aval_below]; apply lsub_below; [eapply lin_below_mono; [|exact Bx']; exact (proj1 (proj2 A)) | apply lscale_below; exact D]].
    cbn [val_ok]. apply bv_eq. rewrite RES, w64_unsigned, lsub_sound, lscale_sound.
    assert (EX : evl rho' x' = evl rho x') by (eapply evl_agree; [exact Bx' | exact (proj1 A)]).
    rewrite EX. apply (f_equal bv_unsigned) in C. rewrite !w64_unsigned in C.
    rewrite <- Hx', w64_unsigned. rewrite (mod_mod_pow2_le (evl rho x') k 64) by lia.
    (* [comment removed for export] *)
    assert (P64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hq : exists t, evl rho' q = evl rho x' / 2 ^ k + t * 2 ^ 64).
    { exists ((evl rho' q - evl rho x' / 2 ^ k) / 2 ^ 64).
      pose proof (Z.div_mod (evl rho' q - evl rho x' / 2 ^ k) (2 ^ 64) ltac:(lia)) as DM.
      assert (MZ : (evl rho' q - evl rho x' / 2 ^ k) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, C, Z.sub_diag; reflexivity). lia. }
    destruct Hq as [t Ht]. rewrite Ht.
    pose proof (Z.div_mod (evl rho x') (2 ^ k) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (evl rho x') (2 ^ k) ltac:(lia)) as MB.
    replace (evl rho x' - 2 ^ k * (evl rho x' / 2 ^ k + t * 2 ^ 64)) with (evl rho x' mod 2 ^ k + (- t * 2 ^ k) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (uview (s_ctx st) x) as [x'|] eqn:Ux.
  - apply (CORE x'); [| eapply uview_below; eauto | exact H]. rewrite Ha. exact (proj1 (uview_sound rho _ x x' (proj1 HVS) Ux)).
  - destruct (sexact (s_ctx st) x); [|discriminate]. apply (CORE x); [symmetry; exact Ha | exact Bx | exact H].
Qed.

Lemma testbit_of_div : forall X k q, 0 <= k -> X / 2 ^ k = q -> Z.testbit X k = Z.odd q.
Proof.
  intros X k q Hk Hq. rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia. now rewrite Hq.
Qed.

Lemma lor_pow2_set : forall X k, 0 <= k -> Z.testbit X k = true -> Z.lor X (2 ^ k) = X.
Proof.
  intros X k Hk Hb. apply Z.bits_inj'. intros j Hj.
  rewrite Z.lor_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb k j) eqn:E; [apply Z.eqb_eq in E; subst; rewrite Hb; reflexivity | apply orb_false_r].
Qed.

Lemma lor_pow2_clear : forall X k, 0 <= X -> 0 <= k -> Z.testbit X k = false -> Z.lor X (2 ^ k) = X + 2 ^ k.
Proof.
  intros X k HX Hk Hb.
  assert (L : Z.land X (2 ^ k) = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb k j) eqn:E; [apply Z.eqb_eq in E; subst; rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma div_between : forall lo hi X m q, 0 < m -> lo <= X <= hi -> lo / m = q -> hi / m = q -> X / m = q.
Proof.
  intros lo hi X m q Hm [H1 H2] Hl Hh.
  pose proof (Z.div_le_mono lo X m Hm H1). pose proof (Z.div_le_mono X hi m Hm H2). lia.
Qed.

(* [comment removed for export] *)
Ltac bool_facts Hr EX EY :=
  repeat (apply Forall_cons; [split;
    [ repeat first [apply laddc_below | apply lneg_below | apply lsub_below | apply ladd_below | apply lscale_below
                  | apply lvar_below; lia | eapply lin_below_mono; [|eassumption]; lia]
    | repeat (rewrite laddc_sound || rewrite lneg_sound || rewrite lsub_sound || rewrite ladd_sound || rewrite lscale_sound || rewrite lvar_sound);
      rewrite ?Hr, ?EX, ?EY; nia ] |]);
  apply Forall_nil.

(* [comment removed for export] *)
Lemma in01_sound : forall rho C l w, ctx_ok rho C -> in01 C l = true -> w = w64 (evl rho l) ->
  0 <= evl rho l <= 1 /\ bv_unsigned w = evl rho l.
Proof.
  intros rho C l w HC H Hw. unfold in01 in H. pose proof (in_range_sound rho C l 0 2 HC H) as R.
  split; [lia|]. rewrite Hw, w64_unsigned. apply Z.mod_small. lia.
Qed.
Lemma land_01 : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 -> Z.land a b = a * b.
Proof. intros a b Ha Hb. assert (a = 0 \/ a = 1) as [->| ->] by lia; assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma lor_01 : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 -> Z.lor a b = a + b - a * b.
Proof. intros a b Ha Hb. assert (a = 0 \/ a = 1) as [->| ->] by lia; assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma lxor_01 : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 -> Z.lxor a b = a + b - 2 * (a * b).
Proof. intros a b Ha Hb. assert (a = 0 \/ a = 1) as [->| ->] by lia; assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.

(* [comment removed for export] *)
Lemma bool_op_sound : forall rho st x y wa wb (v : Z) (facts : sym -> list lin) (w : word),
  VS rho st -> in01 (s_ctx st) x = true -> in01 (s_ctx st) y = true ->
  wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  0 <= v <= 1 -> bv_unsigned w = v ->
  (forall r, facts r = map (fun f => f r) (match facts r with l => [] end) \/ True) ->
  (forall rho' r, rho' r = v -> evl rho' x = evl rho x -> evl rho' y = evl rho y -> (r = s_next st) ->
      Forall (fun l => lin_below l (S (s_next st)) = true /\ 0 <= evl rho' l) (facts r)) ->
  exists rho', VOK rho st (let (r, st1) := fresh st (Itv (Some 0) (Some 1)) in (LV (lvar r), learn_all st1 (facts r))) rho' w.
Proof.
  intros rho st x y wa wb v facts w HVS Ix Iy Ha Hb Bx By Hv Hw _ HF.
  apply (bool_fresh_sound rho st facts v w HVS Hv ltac:(rewrite <- Hw; symmetry; apply w64_of_unsigned)).
  intros rho' Hr AG. apply HF; [exact Hr | eapply evl_agree; eauto | eapply evl_agree; eauto | reflexivity].
Qed.

Lemma aand_gen_sound : forall rho st x y wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  exists rho', VOK rho st (aand_gen st x y) rho' (alu64 ALU_AND wa wb).
Proof.
  intros rho2 st2 x y wa wb GA2 HN2 V2 Ha2 Hb2 Ba2 Bb2. pose proof (proj1 V2) as HC2. unfold aand_gen.
  pose proof (u64_range wa) as Ra. pose proof (u64_range wb) as Rb.
  assert (LAND : bv_unsigned (alu64 ALU_AND wa wb) = Z.land (bv_unsigned wa) (bv_unsigned wb)) by apply and_w64_unsigned.
  assert (Lnn : 0 <= Z.land (bv_unsigned wa) (bv_unsigned wb)) by (apply Z.land_nonneg; lia).
  destruct (is_const y) as [m|] eqn:Ky.
  + pose proof (is_const_sound rho2 y m Ky) as Hm.
    assert (Hub : bv_unsigned wb = m mod two64) by (rewrite Hb2, Hm, w64_unsigned, two64I_eq; reflexivity).
    rewrite two64I_eq in *. pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)) as Hmm.
    set (um := m mod 2 ^ 64) in *.
    set (kc := Z.log2 (2 ^ 64 - um)).
    destruct (Z.ltb 0 kc &&& Z.ltb kc 64 &&& Z.eqb (2 ^ 64 - um) (2 ^ kc))%bool eqn:Ekc.
    { apply andb_prop in Ekc as [Ekc E3]. apply andb_prop in Ekc as [E1 E2].
      apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3.
      apply aand_clear_sound; [exact GA2 | exact HN2 | exact V2 | exact Ha2 | exact Ba2 | lia | rewrite Hub; lia]. }
    set (j := Z.log2 (um + 1)).
    destruct (Z.eqb (um + 1) (2 ^ j)) eqn:Ej; cbn [andb].
    * apply Z.eqb_eq in Ej. assert (Hj : 0 <= j) by (unfold j; apply Z.log2_nonneg).
      assert (Hj64 : j <= 64).
      { destruct (Z.le_gt_cases j 64) as [|Hgt]; [assumption|]. exfalso.
        assert (2 ^ 64 < 2 ^ j) by (apply Z.pow_lt_mono_r; lia). lia. }
      assert (LANDm : forall u, 0 <= u -> Z.land u um = u mod 2 ^ j).
      { intros u Hu. replace um with (2 ^ j - 1) by lia. apply land_pow2_mod; lia. }
      destruct (in_range (s_ctx st2) x 0 (um + 1)) eqn:Er.
      -- pose proof (in_range_sound rho2 _ x _ _ HC2 Er) as Hxr.
         exists rho2. apply VOK_lv; [exact V2 | exact Ba2 |].
         apply bv_eq. rewrite LAND, Hub, w64_unsigned, LANDm by lia.
         assert (Hux : bv_unsigned wa = evl rho2 x) by (rewrite Ha2, w64_unsigned; apply Z.mod_small; lia).
         rewrite Hux. rewrite !Z.mod_small; [reflexivity | lia | lia].
      -- destruct (in_range (s_ctx st2) x (- (um + 1)) 0) eqn:Er2.
         ++ pose proof (in_range_sound rho2 _ x _ _ HC2 Er2) as Hxr.
            exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; exact Ba2 |].
            apply bv_eq. rewrite LAND, Hub, w64_unsigned, LANDm, laddc_sound by lia.
            assert (Hux : bv_unsigned wa = evl rho2 x + 2 ^ 64).
            { rewrite Ha2, w64_unsigned. replace (evl rho2 x) with ((evl rho2 x + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
              rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
            rewrite Hux, Ej. replace (evl rho2 x + 2 ^ 64) with ((evl rho2 x + 2 ^ j) + (2 ^ (64 - j) - 1) * 2 ^ j)
              by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; replace (64 - j + j) with 64 by lia; lia).
            rewrite Z.mod_add by lia.
            assert (2 ^ j <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
            rewrite !Z.mod_small; [reflexivity | lia | lia].
         ++ destruct (and_block (s_ctx st2) x (um + 1)) as [rb|] eqn:Eblk.
            { (* [comment removed for export] *)
              unfold and_block in Eblk. pose proof (lrange2_ok rho2 _ x HC2) as [Rl Rh].
              destruct (lrange2 (s_ctx st2) x) as [[lo|] [hi|]]; try discriminate. cbn in Rl, Rh.
              destruct (Z.eqb_spec (lo / (um + 1)) (hi / (um + 1))) as [Eq|]; [|discriminate]. injection Eblk; intros <-.
              set (p2 := um + 1) in *. set (q := lo / p2) in *.
              assert (Hq : evl rho2 x / p2 = q) by (eapply div_between; [lia | split; [exact Rl | exact Rh] | reflexivity | symmetry; exact Eq]).
              exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; exact Ba2 |].
              apply bv_eq. rewrite LAND, Hub, !w64_unsigned, LANDm, laddc_sound by lia.
              rewrite Ha2, w64_unsigned. rewrite mod_mod_pow2_le by lia.
              assert (P2 : 2 ^ j <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). rewrite <- Ej in P2. rewrite <- Ej.
              pose proof (Z.div_mod (evl rho2 x) p2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (evl rho2 x) p2 ltac:(lia)) as MB.
              rewrite Hq in DM. replace (evl rho2 x + - (q * p2)) with (evl rho2 x mod p2) by lia.
              symmetry. apply Z.mod_small. lia. }
            destruct (Z.leb (um + 1) 16 &&& talign16 (lt x))%bool eqn:Ea.
            ** apply andb_prop in Ea as [E16 Eal]. apply Z.leb_le in E16.
               exists rho2. apply VOK_lit; [exact V2|].
               apply bv_eq. rewrite LAND, Hub, !w64_unsigned, LANDm, Ha2, w64_unsigned by lia.
               assert (Hj4 : j <= 4).
               { destruct (Z.le_gt_cases j 4) as [|Hgt]; [assumption|]. exfalso.
                 assert (2 ^ 4 < 2 ^ j) by (apply Z.pow_lt_mono_r; lia). change (2 ^ 4) with 16 in H. lia. }
               rewrite mod_mod_pow2_le by lia.
               pose proof (talign16_sound rho2 (lt x) GA2 Eal) as Hal.
               unfold evl. rewrite Z.add_mod, <- (mod_mod_pow2_le (evalt rho2 (lt x)) j 4) by lia.
               change (2 ^ 4) with 16. rewrite Hal, (Z.mod_0_l (2 ^ j)), Z.add_0_r, Z.mod_mod by lia.
               replace (um + 1) with (2 ^ j) by lia.
               pose proof (Z.mod_pos_bound (lc x) (2 ^ j) ltac:(lia)).
               symmetry. apply Z.mod_small. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 H)|].
               apply Z.pow_le_mono_r; lia.
            ** (* [comment removed for export] *)
               destruct (and_lowlit (s_ctx st2) x j) as [cl|] eqn:Elit.
               { destruct (and_lowlit_sound rho2 (s_ctx st2) x j cl GA2 (proj1 V2) ltac:(lia) Elit) as [Hcl Rcl].
                 exists rho2. apply VOK_lit; [exact V2|].
                 apply bv_eq. rewrite LAND, Hub, !w64_unsigned, LANDm, Ha2, w64_unsigned by lia.
                 rewrite mod_mod_pow2_le by lia. rewrite Hcl. symmetry. apply Z.mod_small.
                 assert (2 ^ j <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
               destruct (aand_low st2 x j) as [pl|] eqn:Elow.
               { eapply (aand_low_sound rho2 st2 x j wa wb pl GA2 HN2 V2 Ha2 Ba2); [lia | rewrite Hub; lia | exact Elow]. }
               eapply VOK_fresh; [exact V2 | | symmetry; apply w64_of_unsigned]. rewrite LAND. unfold in_itv; cbn [ilo ihi].
               split; [exact Lnn|]. rewrite <- Hub. apply Z_land_le_r; lia.
    * eapply VOK_fresh; [exact V2 | | symmetry; apply w64_of_unsigned]. rewrite LAND. unfold in_itv; cbn [ilo ihi].
      split; [exact Lnn|]. rewrite <- Hub. apply Z_land_le_r; lia.
  + destruct (is_const x) as [m|] eqn:Kx.
    * pose proof (is_const_sound rho2 x m Kx) as Hm.
      assert (Hua : bv_unsigned wa = m mod two64) by (rewrite Ha2, Hm, w64_unsigned, two64I_eq; reflexivity).
      eapply VOK_fresh; [exact V2 | | symmetry; apply w64_of_unsigned]. rewrite LAND. unfold in_itv; cbn [ilo ihi].
      split; [exact Lnn|]. rewrite <- Hua. apply Z_land_le_l; lia.
    * destruct (in01 (s_ctx st2) x &&& in01 (s_ctx st2) y)%bool eqn:B01.
      { apply andb_prop in B01 as [Ix Iy].
        destruct (in01_sound rho2 _ x wa HC2 Ix Ha2) as [Rx Ux]. destruct (in01_sound rho2 _ y wb HC2 Iy Hb2) as [Ry Uy].
        eapply (bool_op_sound rho2 st2 x y wa wb (evl rho2 x * evl rho2 y)); try eassumption; [nia | rewrite LAND, Ux, Uy; apply land_01; assumption | intros; right; exact I |].
        intros rho' r Hr EX EY ->. bool_facts Hr EX EY. }
      destruct (ihi (lrange (s_ctx st2) x)) as [hx|] eqn:Ehx; destruct (ihi (lrange (s_ctx st2) y)) as [hy|] eqn:Ehy;
        try (destruct (uexact (s_ctx st2) x &&& uexact (s_ctx st2) y)%bool eqn:E); try (exists rho2; apply VOK_top; exact V2);
        apply andb_prop in E as [Ux Uy];
        pose proof (uexact_unsigned rho2 _ x wa HC2 Ux Ha2) as Hux; pose proof (uexact_unsigned rho2 _ y wb HC2 Uy Hb2) as Huy;
        eapply VOK_fresh; try exact V2; try (symmetry; apply w64_of_unsigned); rewrite LAND; unfold in_itv; cbn [ilo ihi];
        split; try exact Lnn.
      -- pose proof (ihi_sound rho2 _ x hx HC2 Ehx). pose proof (ihi_sound rho2 _ y hy HC2 Ehy).
         apply Z.min_glb; [eapply Z.le_trans; [apply Z_land_le_l; lia|lia] | eapply Z.le_trans; [apply Z_land_le_r; lia|lia]].
      -- pose proof (ihi_sound rho2 _ x hx HC2 Ehx). eapply Z.le_trans; [apply Z_land_le_l; lia|lia].
      -- pose proof (ihi_sound rho2 _ y hy HC2 Ehy). eapply Z.le_trans; [apply Z_land_le_r; lia|lia].
Qed.

Lemma aor_bit_sound : forall rho C x y r wa wb,
  ctx_ok rho C -> aor_bit C x y = Some r -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  alu64 ALU_OR wa wb = w64 (evl rho r).
Proof.
  intros rho C x y r wa wb HC H Ha Hb. unfold aor_bit in H.
  destruct (is_const y) as [m|] eqn:Ky; [|discriminate].
  destruct (Z.ltb 0 m) eqn:E1; [|discriminate]. apply Z.ltb_lt in E1.
  destruct (Z.eqb m (2 ^ Z.log2 m)) eqn:E2; [|discriminate]. apply Z.eqb_eq in E2.
  destruct (Z.ltb (Z.log2 m) 63) eqn:E3; [|discriminate]. apply Z.ltb_lt in E3.
  assert (R0 : in_itv (evl rho x) (lrange C x)) by (apply lrange_ok; exact HC).
  destruct (lrange C x) as [[lo|] [hi|]] eqn:EL; try discriminate.
  destruct (Z.leb 0 lo) eqn:E4; [|discriminate]. apply Z.leb_le in E4.
  destruct (Z.ltb hi two63) eqn:E5; [|discriminate]. apply Z.ltb_lt in E5.
  destruct (Z.eqb (lo / m) (hi / m)) eqn:E6; [|discriminate]. apply Z.eqb_eq in E6.
  destruct R0 as [R1 R2]; cbn in R1, R2.
  set (k := Z.log2 m) in *. assert (Hk : 0 <= k) by (subst k; apply Z.log2_nonneg).
  pose proof (is_const_sound rho y m Ky) as Ey.
  assert (T63 : two63 = 2 ^ 63) by reflexivity.
  assert (HX : bv_unsigned wa = evl rho x). { rewrite Ha, w64_unsigned. apply Z.mod_small. lia. }
  assert (HM : bv_unsigned wb = m). { rewrite Hb, w64_unsigned, Ey. apply Z.mod_small. assert (2 ^ k < 2 ^ 63) by (apply Z.pow_lt_mono_r; lia). lia. }
  assert (Q : evl rho x / m = lo / m) by (eapply div_between; eauto; lia).
  pose proof (testbit_of_div (evl rho x) k (lo / m) Hk ltac:(rewrite <- E2; exact Q)) as TB.
  rewrite <- (w64_of_unsigned (alu64 ALU_OR wa wb)), or_w64_unsigned, HX, HM.
  destruct (Z.odd (lo / m)) eqn:Eo; injection H; intros <-.
  - rewrite E2, lor_pow2_set by (try lia; rewrite TB; reflexivity). reflexivity.
  - rewrite laddc_sound, E2, lor_pow2_clear; [reflexivity | lia | lia | exact TB].
Qed.

Lemma aor_bit_below : forall C x y r n, aor_bit C x y = Some r -> lin_below x n = true -> lin_below r n = true.
Proof.
  intros C x y r n H Bx. unfold aor_bit in H.
  destruct (is_const y); [|discriminate].
  destruct (Z.ltb 0 z &&& Z.eqb z (2 ^ Z.log2 z) &&& Z.ltb (Z.log2 z) 63)%bool; [|discriminate].
  destruct (lrange C x) as [[lo|] [hi|]]; try discriminate.
  destruct (Z.leb 0 lo &&& Z.ltb hi two63 &&& Z.eqb (lo / z) (hi / z))%bool; [|discriminate].
  destruct (Z.odd (lo / z)); injection H; intros <-; [exact Bx | apply laddc_below; exact Bx].
Qed.

Lemma aor_gen_sound : forall rho st x y wa wb,
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  exists rho', VOK rho st (aor_gen st x y) rho' (alu64 ALU_OR wa wb).
Proof.
  intros rho2 st2 x y wa wb V2 Ha2 Hb2 Ba2 Bb2. pose proof (proj1 V2) as HC2. unfold aor_gen.
  destruct (in01 (s_ctx st2) x &&& in01 (s_ctx st2) y)%bool eqn:B01.
  { apply andb_prop in B01 as [Ix Iy].
    destruct (in01_sound rho2 _ x wa HC2 Ix Ha2) as [Rx Ux]. destruct (in01_sound rho2 _ y wb HC2 Iy Hb2) as [Ry Uy].
    eapply (bool_op_sound rho2 st2 x y wa wb (evl rho2 x + evl rho2 y - evl rho2 x * evl rho2 y)); try eassumption;
      [nia | rewrite or_w64_unsigned, Ux, Uy; apply lor_01; assumption | intros; right; exact I |].
    intros rho' r Hr EX EY ->. bool_facts Hr EX EY. }
  destruct (aor_bit (s_ctx st2) x y) as [r|] eqn:EB1.
  { exists rho2. apply VOK_lv; [exact V2 | eapply aor_bit_below; eauto |].
    eapply aor_bit_sound; eauto. }
  destruct (aor_bit (s_ctx st2) y x) as [r|] eqn:EB2.
  { exists rho2. apply VOK_lv; [exact V2 | eapply aor_bit_below; eauto |].
    rewrite or_comm_w64. eapply aor_bit_sound; eauto. }
  destruct (ihi (lrange (s_ctx st2) x)) as [hx|] eqn:Ehx; [|exists rho2; apply VOK_top; exact V2].
  destruct (ihi (lrange (s_ctx st2) y)) as [hy|] eqn:Ehy; [|exists rho2; apply VOK_top; exact V2].
  destruct (uexact (s_ctx st2) x &&& uexact (s_ctx st2) y &&& Z.leb 0 hx &&& Z.leb 0 hy)%bool eqn:E; [|exists rho2; apply VOK_top; exact V2].
  apply andb_prop in E as [E Hhy]. apply andb_prop in E as [E Hhx]. apply andb_prop in E as [Ux Uy].
  apply Z.leb_le in Hhx. apply Z.leb_le in Hhy.
  pose proof (uexact_unsigned rho2 _ x wa HC2 Ux Ha2) as Hux. pose proof (uexact_unsigned rho2 _ y wb HC2 Uy Hb2) as Huy.
  pose proof (ihi_sound rho2 _ x hx HC2 Ehx) as Bx. pose proof (ihi_sound rho2 _ y hy HC2 Ehy) as By.
  pose proof (u64_range wa) as Ra. pose proof (u64_range wb) as Rb.
  eapply VOK_fresh; [exact V2 | | symmetry; apply w64_of_unsigned].
  rewrite or_w64_unsigned. unfold in_itv; cbn [ilo ihi].
  set (kk := Z.max (Z.log2_up (hx + 1)) (Z.log2_up (hy + 1))).
  assert (Ka : bv_unsigned wa < 2 ^ kk).
  { eapply Z.lt_le_trans; [apply log2_up_bound; split; [lia|rewrite Hux; exact Bx]|]. apply Z.pow_le_mono_r; [lia|apply Z.le_max_l]. }
  assert (Kb : bv_unsigned wb < 2 ^ kk).
  { eapply Z.lt_le_trans; [apply log2_up_bound; split; [lia|rewrite Huy; exact By]|]. apply Z.pow_le_mono_r; [lia|apply Z.le_max_r]. }
  split; [apply Z.lor_nonneg; lia | apply lor_below_pow2; lia].
Qed.

Lemma asrl_var_sound : forall rho st x y wa wb,
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  exists rho', VOK rho st (asrl_var st x y) rho' (alu64 ALU_SRL wa wb).
Proof.
  intros rho st x y wa wb HVS Ha Hb Bx By. pose proof (proj1 HVS) as HC. unfold asrl_var.
  pose proof (lrange_sound rho _ y HC) as Ry.
  destruct (lrange (s_ctx st) y) as [[slo|] [shi|]]; try (exists rho; apply VOK_top; exact HVS).
  destruct (Z.leb 0 slo &&& Z.leb shi 63)%bool eqn:E; [|exists rho; apply VOK_top; exact HVS].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. destruct Ry as [R1 R2]; cbn in R1, R2.
  rewrite Hb, srl_w64. rewrite Z.mod_small by lia.
  pose proof (u64_range wa) as Ra.
  set (s := evl rho y) in *.
  assert (GEN : forall lo hi, 0 <= lo -> lo <= bv_unsigned wa <= hi ->
            exists rho', VOK rho st (fresh_val st (Itv (Some (lo / 2 ^ shi)) (Some (hi / 2 ^ slo)))) rho' (w64 (bv_unsigned wa / 2 ^ s))).
  { intros lo hi Hlo [W1 W2]. eapply VOK_fresh; [exact HVS | | reflexivity]. unfold in_itv; cbn [ilo ihi].
    assert (P1 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    assert (P2 : 2 ^ s <= 2 ^ shi) by (apply Z.pow_le_mono_r; lia).
    assert (P3 : 2 ^ slo <= 2 ^ s) by (apply Z.pow_le_mono_r; lia).
    assert (P4 : 0 < 2 ^ slo) by (apply Z.pow_pos_nonneg; lia).
    split.
    - apply (Z.le_trans _ (lo / 2 ^ s)); [apply Z.div_le_compat_l; [exact Hlo | split; [exact P1 | exact P2]] | apply Z.div_le_mono; [exact P1 | exact W1]].
    - apply (Z.le_trans _ (hi / 2 ^ s)); [apply Z.div_le_mono; [exact P1 | exact W2] | apply Z.div_le_compat_l; [lia | split; [exact P4 | exact P3]]]. }
  destruct (uview (s_ctx st) x) as [x'|] eqn:Ux.
  - pose proof (uview_unsigned rho _ x x' wa HC Ux Ha) as U. pose proof (lrange_sound rho _ x' HC) as [Rx1 Rx2].
    destruct (ilo (lrange (s_ctx st) x')) as [lo|]; destruct (ihi (lrange (s_ctx st) x')) as [hi|]; cbn [fst snd] in *;
      apply GEN; unfold two64, LXL.two64 in *; try lia.
  - cbn [fst snd]. apply GEN; unfold two64, LXL.two64; lia.
Qed.

Lemma div_mono_denom_neg : forall p q r, p <= 0 -> 0 < q <= r -> p / q <= p / r.
Proof.
  intros p q r Hp Hqr. apply Z.div_le_lower_bound; [lia|].
  assert (A : p / q <= 0) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.mul_div_le p q ltac:(lia)) as B. nia.
Qed.

Lemma asra_var_sound : forall rho st x y wa wb,
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  exists rho', VOK rho st (asra_var st x y) rho' (alu64 ALU_SRA wa wb).
Proof.
  intros rho st x y wa wb HVS Ha Hb Bx By. pose proof (proj1 HVS) as HC. unfold asra_var.
  pose proof (lrange_sound rho _ y HC) as Ry.
  destruct (lrange (s_ctx st) y) as [[slo|] [shi|]]; try (exists rho; apply VOK_top; exact HVS).
  destruct (Z.leb 0 slo &&& Z.leb shi 63 &&& sexact (s_ctx st) x)%bool eqn:E; [|exists rho; apply VOK_top; exact HVS].
  apply andb_prop in E as [E Sx]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  destruct Ry as [R1 R2]; cbn in R1, R2.
  rewrite Hb, sra_w64. rewrite Z.mod_small by lia.
  pose proof (sexact_signed rho _ x wa HC Sx Ha) as SX. rewrite SX.
  set (s := evl rho y) in *. set (v := evl rho x) in *.
  assert (P1 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2 ^ s <= 2 ^ shi) by (apply Z.pow_le_mono_r; lia).
  assert (P3 : 2 ^ slo <= 2 ^ s) by (apply Z.pow_le_mono_r; lia).
  assert (P4 : 0 < 2 ^ slo) by (apply Z.pow_pos_nonneg; lia).
  pose proof (lrange_sound rho _ x HC) as Rx. fold v in Rx.
  destruct (lrange (s_ctx st) x) as [[lo|] [hi|]].
  2-4: eapply VOK_fresh; [exact HVS | | reflexivity]; unfold in_itv; cbn [ilo ihi];
       pose proof (in_range_sound rho _ x _ _ HC Sx) as SR; fold v in SR; rewrite two63_eq in SR; unfold two63, LXL.two63;
       assert (P5 : 2 ^ s <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia);
       (split; [apply Z.div_le_lower_bound; [lia|nia] | enough (v / 2 ^ s < 2 ^ 63) by lia; apply Z.div_lt_upper_bound; [lia|nia]]).
  destruct Rx as [Rx1 Rx2]; cbn in Rx1, Rx2.
  eapply VOK_fresh; [exact HVS | | reflexivity]. unfold in_itv; cbn [ilo ihi]. split.
  - destruct (Z.ltb_spec lo 0).
    + apply (Z.le_trans _ (lo / 2 ^ s)).
      * destruct (Z.le_gt_cases lo 0); [apply div_mono_denom_neg; lia | lia].
      * apply Z.div_le_mono; [exact P1 | exact Rx1].
    + apply (Z.le_trans _ (lo / 2 ^ s)); [apply Z.div_le_compat_l; [lia | split; [exact P1 | exact P2]] | apply Z.div_le_mono; [exact P1 | exact Rx1]].
  - destruct (Z.leb_spec 0 hi).
    + apply (Z.le_trans _ (hi / 2 ^ s)); [apply Z.div_le_mono; [exact P1 | exact Rx2] | apply Z.div_le_compat_l; [lia | split; [exact P4 | exact P3]]].
    + apply (Z.le_trans _ (hi / 2 ^ s)); [apply Z.div_le_mono; [exact P1 | exact Rx2] | apply div_mono_denom_neg; lia].
Qed.

Lemma asll_range_sound : forall rho C x y smax lim i, ctx_ok rho C -> asll_range C x y smax lim = Some i ->
  0 <= evl rho y <= smax /\ 0 <= evl rho x /\ (in_itv (evl rho x * 2 ^ evl rho y) i /\ evl rho x * 2 ^ evl rho y < lim).
Proof.
  intros rho C x y smax lim i HC H. unfold asll_range in H.
  pose proof (lrange_sound rho C y HC) as Ry. pose proof (lrange_sound rho C x HC) as Rx.
  destruct (lrange C y) as [[slo|] [shi|]]; try discriminate. destruct (lrange C x) as [[lo|] [hi|]]; try discriminate.
  destruct Ry as [R1 R2]; destruct Rx as [R3 R4]; cbn in R1, R2, R3, R4.
  destruct (Z.leb 0 slo &&& Z.leb shi smax &&& Z.leb 0 lo &&& Z.ltb (hi * 2 ^ shi) lim)%bool eqn:E; [|discriminate].
  apply andb_prop in E as [E E4]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3. apply Z.ltb_lt in E4. injection H; intros <-.
  assert (P1 : 2 ^ slo <= 2 ^ evl rho y) by (apply Z.pow_le_mono_r; lia).
  assert (P2 : 2 ^ evl rho y <= 2 ^ shi) by (apply Z.pow_le_mono_r; lia).
  assert (P0 : 0 < 2 ^ slo) by (apply Z.pow_pos_nonneg; lia).
  split; [lia|]. split; [lia|]. unfold in_itv; cbn. split; [split|]; nia.
Qed.
Lemma asll_var_sound : forall rho st x y wa wb,
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
  exists rho', VOK rho st (asll_var st x y 63 two64) rho' (alu64 ALU_SLL wa wb).
Proof.
  intros rho st x y wa wb HVS Ha Hb Bx By. pose proof (proj1 HVS) as HC. unfold asll_var.
  destruct (asll_range (s_ctx st) x y 63 two64) as [i|] eqn:Er; [|exists rho; apply VOK_top; exact HVS].
  destruct (asll_range_sound rho (s_ctx st) x y 63 two64 i HC Er) as (SR & XR & VR & _).
  rewrite Ha, Hb, sll_w64. rewrite Z.mod_small by lia.
  eapply VOK_fresh; [exact HVS | | reflexivity]. rewrite Z.mul_comm. exact VR.
Qed.

Lemma aalu_gen_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aalu_gen st op a b) rho' (alu64 op wa wb).
Proof.
  intros rho st op a b wa wb GA HN HVS Ha Hb Ba Bb. unfold aalu_gen.
  destruct (degrade2 rho st a b wa wb HVS Ha Hb Ba Bb) as (rho2 & H).
  destruct (degrade st a) as [a1 st1] eqn:Da. cbn [fst snd] in H.
  destruct (degrade st1 b) as [b1 st2] eqn:Db. cbn [fst snd] in H.
  destruct H as (E2 & V2 & Ha2 & Hb2 & Ba2 & Bb2).
  pose proof (galign_vext rho st rho2 st2 HN E2 GA) as GA2.
  assert (HN2 : (NGLOB <= s_next st2)%nat) by (rewrite <- (proj1 (proj2 E2)); exact HN).
  cbn beta iota.
  apply (VOK_after_ex rho st rho2 st2 _ _ E2).
  pose proof (proj1 V2) as HC2.
  destruct op; destruct a1 as [|x|n1 k1 u1 v1|u1 v1]; try (exists rho2; apply VOK_top; exact V2);
    destruct b1 as [|y|n2 k2 u2 v2|u2 v2]; try (exists rho2; apply VOK_top; exact V2);
    cbn in Ha2, Hb2; cbn [aval_below] in Ba2, Bb2.
  - (* [comment removed for export] *) exists rho2. apply VOK_lv; [exact V2 | apply ladd_below; assumption |].
    rewrite Ha2, Hb2, add_w64, ladd_sound. reflexivity.
  - (* [comment removed for export] *) exists rho2. apply VOK_lv; [exact V2 | apply lsub_below; assumption |].
    rewrite Ha2, Hb2, sub_w64, lsub_sound. reflexivity.
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky; [|apply asll_var_sound; assumption].
    exists rho2. apply VOK_lv; [exact V2 | apply lscale_below; assumption |].
    rewrite Ha2, Hb2, (is_const_sound rho2 y k Ky), sll_w64, lscale_sound. reflexivity.
  - (* [comment removed for export] *) destruct (sexact (s_ctx st2) x &&& sexact (s_ctx st2) y)%bool eqn:Ex.
    + apply andb_prop in Ex as [Sx Sy].
      pose proof (sexact_signed rho2 _ x wa HC2 Sx Ha2) as Hsx. pose proof (sexact_signed rho2 _ y wb HC2 Sy Hb2) as Hsy.
      assert (Hw : alu64 ALU_SLT wa wb = w64 (if Z.ltb (evl rho2 x) (evl rho2 y) then 1 else 0)).
      { rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite Hsx, Hsy. destruct (Z.ltb _ _); reflexivity. }
      destruct (decide_ge0 (s_ctx st2) (laddc (lsub y x) (-1))) as [[|]|] eqn:Dc.
      * pose proof (proj1 (decide_ge0_sound rho2 _ _ _ HC2 Dc) eq_refl) as Hp. rewrite laddc_sound, lsub_sound in Hp.
        exists rho2. apply VOK_lit; [exact V2|]. rewrite Hw. destruct (Z.ltb_spec (evl rho2 x) (evl rho2 y)); [reflexivity|lia].
      * pose proof (proj2 (decide_ge0_sound rho2 _ _ _ HC2 Dc) eq_refl) as Hp. rewrite laddc_sound, lsub_sound in Hp.
        exists rho2. apply VOK_lit; [exact V2|]. rewrite Hw. destruct (Z.ltb_spec (evl rho2 x) (evl rho2 y)); [lia|reflexivity].
      * exists rho2. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact V2|]. split.
        -- cbn [val_ok cmp_holds xorb]. exact Hw.
        -- cbn [aval_below]. rewrite Ba2, Bb2. reflexivity.
    + destruct (val01 (c_lts wa wb)) as (z & Hz & Rz).
      eapply VOK_fresh; [exact V2 | | rewrite alu_slt; unfold v_slt; exact Hz]. unfold itv01, in_itv; cbn; lia.
  - (* [comment removed for export] *) destruct (uview (s_ctx st2) x) as [x'|] eqn:Ux; [destruct (uview (s_ctx st2) y) as [y'|] eqn:Uy|].
    + pose proof (uview_unsigned rho2 _ x x' wa HC2 Ux Ha2) as Hsx. pose proof (uview_unsigned rho2 _ y y' wb HC2 Uy Hb2) as Hsy.
      pose proof (uview_below _ _ _ _ Ux Ba2) as Bx'. pose proof (uview_below _ _ _ _ Uy Bb2) as By'.
      assert (Hw : alu64 ALU_SLTU wa wb = w64 (if Z.ltb (evl rho2 x') (evl rho2 y') then 1 else 0)).
      { rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite Hsx, Hsy. destruct (Z.ltb _ _); reflexivity. }
      destruct (decide_ge0 (s_ctx st2) (laddc (lsub y' x') (-1))) as [[|]|] eqn:Dc.
      * pose proof (proj1 (decide_ge0_sound rho2 _ _ _ HC2 Dc) eq_refl) as Hp. rewrite laddc_sound, lsub_sound in Hp.
        exists rho2. apply VOK_lit; [exact V2|]. rewrite Hw. destruct (Z.ltb_spec (evl rho2 x') (evl rho2 y')); [reflexivity|lia].
      * pose proof (proj2 (decide_ge0_sound rho2 _ _ _ HC2 Dc) eq_refl) as Hp. rewrite laddc_sound, lsub_sound in Hp.
        exists rho2. apply VOK_lit; [exact V2|]. rewrite Hw. destruct (Z.ltb_spec (evl rho2 x') (evl rho2 y')); [lia|reflexivity].
      * exists rho2. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact V2|]. split.
        -- cbn [val_ok cmp_holds xorb]. exact Hw.
        -- cbn [aval_below]. rewrite Bx', By'. reflexivity.
    + destruct (val01 (c_ltu wa wb)) as (z & Hz & Rz).
      eapply VOK_fresh; [exact V2 | | rewrite alu_sltu; unfold v_sltu; exact Hz]. unfold itv01, in_itv; cbn; lia.
    + destruct (val01 (c_ltu wa wb)) as (z & Hz & Rz).
      eapply VOK_fresh; [exact V2 | | rewrite alu_sltu; unfold v_sltu; exact Hz]. unfold itv01, in_itv; cbn; lia.
  - (* [comment removed for export] *)
    assert (GEN : exists rho', VOK rho2 st2 (XV x y, st2) rho' (alu64 ALU_XOR wa wb)).
    { exists rho2. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact V2|]. split.
      + cbn [val_ok]. rewrite Ha2, Hb2. apply bv_eq. rewrite xor_w64_unsigned, bv_xor_unsigned. reflexivity.
      + cbn [aval_below]. rewrite Ba2, Bb2. reflexivity. }
    assert (NOTy : is_const y = Some (-1) -> exists rho', VOK rho2 st2 (LV (laddc (lneg x) (-1)), st2) rho' (alu64 ALU_XOR wa wb)).
    { intros Ky. exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; apply lneg_below; exact Ba2 |].
      rewrite Ha2, Hb2, (is_const_sound rho2 y (-1) Ky), xor_m1_w64, laddc_sound, lneg_sound. reflexivity. }
    assert (NOTx : is_const x = Some (-1) -> exists rho', VOK rho2 st2 (LV (laddc (lneg y) (-1)), st2) rho' (alu64 ALU_XOR wa wb)).
    { intros Kx. exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; apply lneg_below; exact Bb2 |].
      rewrite Ha2, Hb2, (is_const_sound rho2 x (-1) Kx), xor_comm_w64, xor_m1_w64, laddc_sound, lneg_sound. reflexivity. }
    assert (Z0y : is_const y = Some 0 -> exists rho', VOK rho2 st2 (LV x, st2) rho' (alu64 ALU_XOR wa wb)).
    { intros Ky. exists rho2. apply VOK_lv; [exact V2 | exact Ba2 |]. rewrite Hb2, (is_const_sound rho2 y 0 Ky), xor_0_w64. exact Ha2. }
    assert (Z0x : is_const x = Some 0 -> exists rho', VOK rho2 st2 (LV y, st2) rho' (alu64 ALU_XOR wa wb)).
    { intros Kx. exists rho2. apply VOK_lv; [exact V2 | exact Bb2 |]. rewrite Ha2, (is_const_sound rho2 x 0 Kx), xor_comm_w64, xor_0_w64. exact Hb2. }
    (* [comment removed for export] *)
    assert (B1y : is_const y = Some 1 -> exists rho', VOK rho2 st2 (if in01 (s_ctx st2) x then (LV (laddc (lneg x) 1), st2) else (XV x y, st2)) rho' (alu64 ALU_XOR wa wb)).
    { intros Ky. destruct (in01 (s_ctx st2) x) eqn:Ix; [|exact GEN].
      destruct (in01_sound rho2 _ x wa HC2 Ix Ha2) as [Rx Ux].
      exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; apply lneg_below; exact Ba2 |].
      apply bv_eq. rewrite xor_w64_unsigned, Ux, Hb2, (is_const_sound rho2 y 1 Ky), !w64_unsigned, laddc_sound, lneg_sound.
      change (1 mod 2 ^ 64) with 1. assert (evl rho2 x = 0 \/ evl rho2 x = 1) as [E|E] by lia; rewrite E; reflexivity. }
    assert (B1x : is_const x = Some 1 -> exists rho', VOK rho2 st2 (if in01 (s_ctx st2) y then (LV (laddc (lneg y) 1), st2) else (XV x y, st2)) rho' (alu64 ALU_XOR wa wb)).
    { intros Kx. destruct (in01 (s_ctx st2) y) eqn:Iy; [|exact GEN].
      destruct (in01_sound rho2 _ y wb HC2 Iy Hb2) as [Ry Uy].
      exists rho2. apply VOK_lv; [exact V2 | apply laddc_below; apply lneg_below; exact Bb2 |].
      apply bv_eq. rewrite xor_comm_w64, xor_w64_unsigned, Uy, Ha2, (is_const_sound rho2 x 1 Kx), !w64_unsigned, laddc_sound, lneg_sound.
      change (1 mod 2 ^ 64) with 1. assert (evl rho2 y = 0 \/ evl rho2 y = 1) as [E|E] by lia; rewrite E; reflexivity. }
    assert (BB : exists rho', VOK rho2 st2
              (if (in01 (s_ctx st2) x &&& in01 (s_ctx st2) y)%bool then
                 let (r, st1) := fresh st2 (Itv (Some 0) (Some 1)) in
                 (LV (lvar r), learn_all st1 [lsub (ladd x y) (lvar r); ladd (lsub (lvar r) x) y; lsub (ladd (lvar r) x) y;
                                           laddc (lneg (ladd (ladd x y) (lvar r))) 2])
               else (XV x y, st2)) rho' (alu64 ALU_XOR wa wb)).
    { destruct (in01 (s_ctx st2) x &&& in01 (s_ctx st2) y)%bool eqn:B01; [|exact GEN].
      apply andb_prop in B01 as [Ix Iy].
      destruct (in01_sound rho2 _ x wa HC2 Ix Ha2) as [Rx Ux]. destruct (in01_sound rho2 _ y wb HC2 Iy Hb2) as [Ry Uy].
      eapply (bool_op_sound rho2 st2 x y wa wb (evl rho2 x + evl rho2 y - 2 * (evl rho2 x * evl rho2 y))
                (fun r => [lsub (ladd x y) (lvar r); ladd (lsub (lvar r) x) y; lsub (ladd (lvar r) x) y; laddc (lneg (ladd (ladd x y) (lvar r))) 2]));
        try eassumption; [nia | rewrite xor_w64_unsigned, Ux, Uy; apply lxor_01; assumption | intros; right; exact I |].
      intros rho' r Hr EX EY ->. bool_facts Hr EX EY. }
    destruct (is_const y) as [[|py|py]|] eqn:Ky; destruct (is_const x) as [[|px|px]|] eqn:Kx;
      repeat match goal with |- context [match ?p with xH => _ | _ => _ end] => destruct p end;
      first [exact BB | exact GEN | apply NOTy; reflexivity | apply NOTx; reflexivity | apply Z0y; reflexivity | apply Z0x; reflexivity
            | apply B1y; reflexivity | apply B1x; reflexivity].
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky; [|apply asrl_var_sound; assumption].
    pose proof (is_const_sound rho2 y k Ky) as Hk.
    assert (Hwb : wb = w64 k) by (rewrite Hb2, Hk; reflexivity).
    assert (Hm : 0 <= k mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    rewrite Hwb, srl_w64.
    destruct (Z.eqb (k mod 64) 0) eqn:E0.
    + apply Z.eqb_eq in E0. rewrite E0, Z.pow_0_r, Z.div_1_r, w64_of_unsigned.
      exists rho2. apply VOK_lv; [exact V2 | exact Ba2 | exact Ha2].
    + destruct (uview (s_ctx st2) x) as [x'|] eqn:Ux.
      * rewrite (uview_unsigned rho2 _ x x' wa HC2 Ux Ha2).
        apply shr_floor_sound; [eapply galign_vext; [exact HN | exact E2 | exact GA] | exact V2 | rewrite <- (proj1 (proj2 E2)); exact HN | eapply uview_below; eauto | lia |].
        apply itv_div_sound; [apply Z.pow_pos_nonneg; lia | apply lrange_sound; exact HC2].
      * eapply VOK_fresh; [exact V2 | | reflexivity]. unfold itv_u, in_itv; cbn [ilo ihi].
        pose proof (u64_range wa). split; [apply Z.div_pos; lia|].
        enough (bv_unsigned wa / 2 ^ (k mod 64) < 2 ^ (64 - k mod 64)) by lia.
        apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k mod 64 + (64 - k mod 64)) with 64 by lia. lia.
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky; [|apply asra_var_sound; assumption].
    pose proof (is_const_sound rho2 y k Ky) as Hk.
    assert (Hwb : wb = w64 k) by (rewrite Hb2, Hk; reflexivity).
    assert (Hm : 0 <= k mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    rewrite Hwb, sra_w64.
    destruct (Z.eqb (k mod 64) 0) eqn:E0.
    + apply Z.eqb_eq in E0. rewrite E0, Z.pow_0_r, Z.div_1_r.
      assert (Hs : w64 (bv_signed wa) = wa).
      { apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap.
        rewrite bv_wrap_sub_idemp_l.
        replace (bv_unsigned wa + bv_half_modulus 64 - bv_half_modulus 64) with (bv_unsigned wa) by lia.
        apply bv_wrap_bv_unsigned. }
      rewrite Hs. exists rho2. apply VOK_lv; [exact V2 | exact Ba2 | exact Ha2].
    + destruct (sexact (s_ctx st2) x) eqn:Sx.
      * rewrite (sexact_signed rho2 _ x wa HC2 Sx Ha2).
        apply shr_floor_sound; [eapply galign_vext; [exact HN | exact E2 | exact GA] | exact V2 | rewrite <- (proj1 (proj2 E2)); exact HN | exact Ba2 | lia |].
        apply itv_div_sound; [apply Z.pow_pos_nonneg; lia | apply lrange_sound; exact HC2].
      * eapply VOK_fresh; [exact V2 | | reflexivity]. unfold in_itv; cbn [ilo ihi].
        pose proof (bv_signed_in_range 64 wa) as R. unfold bv_half_modulus, bv_modulus in R.
        change (2 ^ Z.of_N 64 `div` 2) with (2 ^ 63) in R.
        assert (Hp : 2 ^ 63 = 2 ^ (k mod 64) * 2 ^ (63 - k mod 64)).
        { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        split.
        -- apply Z.div_le_lower_bound; [lia|]. nia.
        -- enough (bv_signed wa / 2 ^ (k mod 64) < 2 ^ (63 - k mod 64)) by lia. apply Z.div_lt_upper_bound; [lia|]. nia.
  - (* [comment removed for export] *)
    assert (Z0y : is_const y = Some 0 -> exists rho', VOK rho2 st2 (LV x, st2) rho' (alu64 ALU_OR wa wb)).
    { intros Ky. exists rho2. apply VOK_lv; [exact V2 | exact Ba2 |]. rewrite Hb2, (is_const_sound rho2 y 0 Ky), or_0_w64. exact Ha2. }
    assert (Z0x : is_const x = Some 0 -> exists rho', VOK rho2 st2 (LV y, st2) rho' (alu64 ALU_OR wa wb)).
    { intros Kx. exists rho2. apply VOK_lv; [exact V2 | exact Bb2 |]. rewrite Ha2, (is_const_sound rho2 x 0 Kx), or_comm_w64, or_0_w64. exact Hb2. }
    pose proof (aor_gen_sound rho2 st2 x y wa wb V2 Ha2 Hb2 Ba2 Bb2) as GEN.
    destruct (is_const y) as [[|py|py]|] eqn:Ky; destruct (is_const x) as [[|px|px]|] eqn:Kx;
      first [apply Z0y; reflexivity | apply Z0x; reflexivity | exact GEN].
  - (* [comment removed for export] *)
    assert (M1y : is_const y = Some (-1) -> exists rho', VOK rho2 st2 (LV x, st2) rho' (alu64 ALU_AND wa wb)).
    { intros Ky. exists rho2. apply VOK_lv; [exact V2 | exact Ba2 |]. rewrite Hb2, (is_const_sound rho2 y (-1) Ky), and_m1_w64. exact Ha2. }
    assert (M1x : is_const x = Some (-1) -> exists rho', VOK rho2 st2 (LV y, st2) rho' (alu64 ALU_AND wa wb)).
    { intros Kx. exists rho2. apply VOK_lv; [exact V2 | exact Bb2 |]. rewrite Ha2, (is_const_sound rho2 x (-1) Kx), and_comm_w64, and_m1_w64. exact Hb2. }
    pose proof (aand_gen_sound rho2 st2 x y wa wb GA2 HN2 V2 Ha2 Hb2 Ba2 Bb2) as GEN.
    destruct (is_const y) as [[|py|[py|py|]]|] eqn:Ky; destruct (is_const x) as [[|px|[px|px|]]|] eqn:Kx;
      first [apply M1y; reflexivity | apply M1x; reflexivity | exact GEN].
Qed.

Lemma aalu0_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aalu0 st op a b) rho' (alu64 op wa wb).
Proof.
  intros rho st op a b wa wb GA HN HVS Ha Hb Ba Bb. unfold aalu0.
  destruct (aval_litC (s_ctx st) a) as [x|] eqn:La; [destruct (aval_litC (s_ctx st) b) as [y|] eqn:Lb|]; try (apply aalu_gen_sound; assumption).
  rewrite (aval_litC_sound rho _ a x wa (proj1 HVS) La Ha), (aval_litC_sound rho _ b y wb (proj1 HVS) Lb Hb).
  exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [apply lit_alu_ok | apply alit_below].
Qed.

(* [comment removed for export] *)
Lemma swrap32_mod64 : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b H. apply bv_swrap_congr. rewrite !bv_wrap32_mod.
  rewrite <- (Z.mod_mod_divide a (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  rewrite <- (Z.mod_mod_divide b (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  rewrite H. reflexivity.
Qed.

Lemma addw_w64 : forall x y, sext 64 (alu32 ALU_ADD (low32 (w64 x)) (low32 (w64 y))) = w64 (bv_swrap 32 (x + y)).
Proof.
  intros. rewrite w_addw. unfold v_addw. unfold w64 at 3. f_equal. apply swrap32_mod64.
  rewrite !w64_unsigned, <- Z.add_mod by lia. reflexivity.
Qed.
Lemma subw_w64 : forall x y, sext 64 (alu32 ALU_SUB (low32 (w64 x)) (low32 (w64 y))) = w64 (bv_swrap 32 (x - y)).
Proof.
  intros. rewrite w_subw. unfold v_subw. unfold w64 at 3. f_equal. apply swrap32_mod64.
  rewrite !w64_unsigned, <- Zminus_mod. reflexivity.
Qed.
Lemma sllw_w64 : forall x k, sext 64 (alu32 ALU_SLL (low32 (w64 x)) (low32 (w64 k))) = w64 (bv_swrap 32 (2 ^ (k mod 32) * x)).
Proof.
  intros. rewrite w_sllw. unfold v_sllw. unfold w64 at 3. f_equal.
  assert (Hk : (k mod 2 ^ 64) mod 32 = k mod 32) by (apply Z.mod_mod_divide; exists (2 ^ 59); reflexivity).
  rewrite !w64_unsigned, Hk, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  apply swrap32_mod64. rewrite Z.mul_mod_idemp_l by lia. f_equal. lia.
Qed.
Lemma srlw_val : forall (a : word) k, sext 64 (alu32 ALU_SRL (low32 a) (low32 (w64 k))) = w64 (bv_swrap 32 ((bv_unsigned a mod 2 ^ 32) / 2 ^ (k mod 32))).
Proof.
  intros. rewrite w_srlw. unfold v_srlw. unfold w64 at 2. f_equal.
  assert (Hk : (k mod 2 ^ 64) mod 32 = k mod 32) by (apply Z.mod_mod_divide; exists (2 ^ 59); reflexivity).
  rewrite w64_unsigned, Hk, bv_wrap32_mod, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma sraw_val : forall (a : word) k, sext 64 (alu32 ALU_SRA (low32 a) (low32 (w64 k))) = w64 (bv_swrap 32 (bv_swrap 32 (bv_unsigned a) / 2 ^ (k mod 32))).
Proof.
  intros. rewrite w_sraw. unfold v_sraw. unfold w64 at 2. f_equal.
  assert (Hk : (k mod 2 ^ 64) mod 32 = k mod 32) by (apply Z.mod_mod_divide; exists (2 ^ 59); reflexivity).
  rewrite w64_unsigned, Hk, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.

Lemma swrap32_of_wrapped : forall z, bv_swrap 32 (z mod 2 ^ 64) = bv_swrap 32 z.
Proof. intros. apply swrap32_mod64. apply Z.mod_mod. lia. Qed.

Lemma aaluw_gen_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aaluw_gen st op a b) rho' (sext 64 (alu32 op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb GA HN HVS Ha Hb Ba Bb. unfold aaluw_gen.
  destruct (degrade2 rho st a b wa wb HVS Ha Hb Ba Bb) as (rho2 & H).
  destruct (degrade st a) as [a1 st1] eqn:Da. cbn [fst snd] in H.
  destruct (degrade st1 b) as [b1 st2] eqn:Db. cbn [fst snd] in H.
  destruct H as (E2 & V2 & Ha2 & Hb2 & Ba2 & Bb2).
  pose proof (galign_vext rho st rho2 st2 HN E2 GA) as GA2.
  assert (HN2 : (NGLOB <= s_next st2)%nat) by (rewrite <- (proj1 (proj2 E2)); exact HN).
  cbn beta iota.
  apply (VOK_after_ex rho st rho2 st2 _ _ E2).
  pose proof (proj1 V2) as HC2.
  (* [comment removed for export] *)
  assert (GEN : exists rho', VOK rho2 st2 (fresh_val st2 itv_s32) rho' (sext 64 (alu32 op (low32 wa) (low32 wb)))).
  { eapply VOK_fresh; [exact V2 | | ].
    2: { apply bv_eq. rewrite sext32_unsigned. unfold w64. rewrite Z_to_bv_unsigned. reflexivity. }
    unfold itv_s32, in_itv; cbn [ilo ihi]. unfold LAI.two31. rewrite two31_eq. pose proof (bv_swrap32_range (bv_unsigned (alu32 op (low32 wa) (low32 wb)))). lia. }
  destruct op; destruct a1 as [|x|n1 k1 u1 v1|u1 v1]; try exact GEN;
    destruct b1 as [|y|n2 k2 u2 v2|u2 v2]; try exact GEN;
    cbn in Ha2, Hb2; cbn [aval_below] in Ba2, Bb2.
  - (* [comment removed for export] *) apply norm32_sound; [exact V2 | apply ladd_below; assumption |]. rewrite Ha2, Hb2, addw_w64, ladd_sound. reflexivity.
  - (* [comment removed for export] *) apply norm32_sound; [exact V2 | apply lsub_below; assumption |]. rewrite Ha2, Hb2, subw_w64, lsub_sound. reflexivity.
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky.
    2:{ destruct (asll_range (s_ctx st2) x y 31 two31) as [i|] eqn:Er; [|exact GEN].
        destruct (asll_range_sound rho2 (s_ctx st2) x y 31 two31 i HC2 Er) as (SR & XR & VR & VL).
        rewrite Ha2, Hb2, sllw_w64. rewrite Z.mod_small by lia.
        rewrite bv_swrap32_small. 2:{ unfold two31, LXL.two31 in VL. assert (0 < 2 ^ evl rho2 y) by (apply Z.pow_pos_nonneg; lia). nia. }
        eapply VOK_fresh; [exact V2 | | reflexivity]. rewrite Z.mul_comm. exact VR. }
    apply norm32_sound; [exact V2 | apply lscale_below; assumption |].
    rewrite Ha2, Hb2, (is_const_sound rho2 y k Ky), sllw_w64, lscale_sound. reflexivity.
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky; [|exact GEN].
    pose proof (is_const_sound rho2 y k Ky) as Hk.
    assert (Hwb : wb = w64 k) by (rewrite Hb2, Hk; reflexivity).
    assert (Hm : 0 <= k mod 32 < 32) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eqb (k mod 32) 0) eqn:E0.
    + rewrite Hwb, srlw_val. apply Z.eqb_eq in E0. rewrite E0, Z.pow_0_r, Z.div_1_r.
      apply norm32_sound; [exact V2 | exact Ba2 |]. f_equal. rewrite Ha2, w64_unsigned.
      rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity). rewrite <- bv_wrap32_mod, bv_swrap_wrap. reflexivity.
    + rewrite Hwb, srlw_val.
      assert (Hp32 : 2 ^ 32 = 2 ^ (k mod 32) * 2 ^ (32 - k mod 32)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hle31 : 2 ^ (32 - k mod 32) <= 2 ^ 31) by (apply Z.pow_le_mono_r; [lia|]; apply Z.eqb_neq in E0; lia).
      destruct (uexact32 (s_ctx st2) x) eqn:Ux.
      2: { pose proof (Z.mod_pos_bound (bv_unsigned wa) (2 ^ 32) ltac:(lia)) as Rm.
           assert (Hq : 0 <= bv_unsigned wa mod 2 ^ 32 / 2 ^ (k mod 32) < 2 ^ (32 - k mod 32)).
           { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
           rewrite bv_swrap32_small by lia.
           eapply VOK_fresh; [exact V2 | | reflexivity]. unfold itv_u, in_itv; cbn [ilo ihi]. lia. }
      pose proof (in_range_sound rho2 _ x 0 LXL.two32 HC2 Ux) as Rx. rewrite two32_eq in Rx.
      assert (Hux : bv_unsigned wa mod 2 ^ 32 = evl rho2 x).
      { rewrite Ha2, w64_unsigned. rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity). apply Z.mod_small. lia. }
      rewrite Hux.
      assert (Hq : 0 <= evl rho2 x / 2 ^ (k mod 32) < 2 ^ 31).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        eapply Z.lt_le_trans; [apply (proj2 Rx)|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
      rewrite bv_swrap32_small by lia.
      apply shr_floor_sound; [eapply galign_vext; [exact HN | exact E2 | exact GA] | exact V2 | rewrite <- (proj1 (proj2 E2)); exact HN | exact Ba2 | lia |].
      apply itv_div_sound; [apply Z.pow_pos_nonneg; lia | apply lrange_sound; exact HC2].
  - (* [comment removed for export] *) destruct (is_const y) as [k|] eqn:Ky; [|exact GEN].
    pose proof (is_const_sound rho2 y k Ky) as Hk.
    assert (Hwb : wb = w64 k) by (rewrite Hb2, Hk; reflexivity).
    assert (Hm : 0 <= k mod 32 < 32) by (apply Z.mod_pos_bound; lia).
    assert (Hsx0 : bv_swrap 32 (bv_unsigned wa) = bv_swrap 32 (evl rho2 x)).
    { rewrite Ha2, w64_unsigned. apply swrap32_of_wrapped. }
    destruct (Z.eqb (k mod 32) 0) eqn:E0.
    + rewrite Hwb, sraw_val, Hsx0. apply Z.eqb_eq in E0. rewrite E0, Z.pow_0_r, Z.div_1_r.
      apply norm32_sound; [exact V2 | exact Ba2 |]. f_equal. apply bv_swrap32_small. apply bv_swrap32_range.
    + rewrite Hwb, sraw_val, Hsx0.
      assert (Hp0 : 2 ^ 31 = 2 ^ (k mod 32) * 2 ^ (31 - k mod 32)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      destruct (sexact32 (s_ctx st2) x) eqn:Sx.
      2: { pose proof (bv_swrap32_range (evl rho2 x)) as Rm.
           assert (Hq : - 2 ^ (31 - k mod 32) <= bv_swrap 32 (evl rho2 x) / 2 ^ (k mod 32) < 2 ^ (31 - k mod 32)).
           { split; [apply Z.div_le_lower_bound; [lia|]; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
           assert (Hle : 2 ^ (31 - k mod 32) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
           rewrite bv_swrap32_small by lia.
           eapply VOK_fresh; [exact V2 | | reflexivity]. unfold in_itv; cbn [ilo ihi]. lia. }
      pose proof (in_range_sound rho2 _ x _ _ HC2 Sx) as Rx. rewrite two31_eq in Rx.
      rewrite (bv_swrap32_small (evl rho2 x)) by lia.
      assert (Hp : 2 ^ 31 = 2 ^ (k mod 32) * 2 ^ (31 - k mod 32)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hq : - 2 ^ 31 <= evl rho2 x / 2 ^ (k mod 32) < 2 ^ 31).
      { split; [apply Z.div_le_lower_bound; [lia|]; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
      rewrite bv_swrap32_small by lia.
      apply shr_floor_sound; [eapply galign_vext; [exact HN | exact E2 | exact GA] | exact V2 | rewrite <- (proj1 (proj2 E2)); exact HN | exact Ba2 | lia |].
      apply itv_div_sound; [apply Z.pow_pos_nonneg; lia | apply lrange_sound; exact HC2].
Qed.

Lemma aaluw0_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aaluw0 st op a b) rho' (sext 64 (alu32 op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb GA HN HVS Ha Hb Ba Bb. unfold aaluw0.
  destruct (aval_litC (s_ctx st) a) as [x|] eqn:La; [destruct (aval_litC (s_ctx st) b) as [y|] eqn:Lb|]; try (apply aaluw_gen_sound; assumption).
  rewrite (aval_litC_sound rho _ a x wa (proj1 HVS) La Ha), (aval_litC_sound rho _ b y wb (proj1 HVS) Lb Hb).
  exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [apply lit_aluw_ok | apply alit_below].
Qed.

Lemma amul_itv_sound : forall rho st x y wa wb,
  VS rho st -> wa = w64 (evl rho x) -> wb = w64 (evl rho y) ->
  exists rho', VOK rho st (amul_itv st x y) rho' (mul_div M_MUL wa wb).
Proof.
  intros rho st x y wa wb HVS Ha Hb. pose proof (proj1 HVS) as HC. unfold amul_itv.
  pose proof (lrange_sound rho _ x HC) as Rx. pose proof (lrange_sound rho _ y HC) as Ry.
  destruct (lrange (s_ctx st) x) as [[lx|] [hx|]]; try (exists rho; apply VOK_top; exact HVS).
  destruct (lrange (s_ctx st) y) as [[ly|] [hy|]]; try (exists rho; apply VOK_top; exact HVS).
  destruct (Z.leb 0 lx &&& Z.leb 0 ly &&& Z.ltb (hx * hy) two64)%bool eqn:E; [|exists rho; apply VOK_top; exact HVS].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
  destruct Rx as [Rx1 Rx2]; destruct Ry as [Ry1 Ry2]; cbn in Rx1, Rx2, Ry1, Ry2.
  eapply VOK_fresh; [exact HVS | | rewrite Ha, Hb, mul_w64; reflexivity].
  unfold in_itv; cbn. split; nia.
Qed.

Lemma amuldiv0_sound : forall rho st op a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (amuldiv0 st op a b) rho' (mul_div op wa wb).
Proof.
  intros rho st op a b wa wb HVS Ha Hb Ba Bb. unfold amuldiv0.
  destruct (aval_litC (s_ctx st) a) as [x0|] eqn:La; [destruct (aval_litC (s_ctx st) b) as [y0|] eqn:Lb|].
  1: { rewrite (aval_litC_sound rho _ a x0 wa (proj1 HVS) La Ha), (aval_litC_sound rho _ b y0 wb (proj1 HVS) Lb Hb).
       exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [apply lit_md_ok | apply alit_below]. }
  all: unfold amuldiv_gen;
    destruct (degrade2 rho st a b wa wb HVS Ha Hb Ba Bb) as (rho2 & H);
    destruct (degrade st a) as [a1 st1] eqn:Da; cbn [fst snd] in H;
    destruct (degrade st1 b) as [b1 st2] eqn:Db; cbn [fst snd] in H;
    destruct H as (E2 & V2 & Ha2 & Hb2 & Ba2 & Bb2);
    cbn beta iota; apply (VOK_after_ex rho st rho2 st2 _ _ E2);
    destruct op; destruct a1 as [|x|n1 k1 u1 v1|u1 v1]; try (exists rho2; apply VOK_top; exact V2);
    destruct b1 as [|y|n2 k2 u2 v2|u2 v2]; try (exists rho2; apply VOK_top; exact V2);
    cbn in Ha2, Hb2; cbn [aval_below] in Ba2, Bb2;
    (destruct (is_const x) as [c|] eqn:Kx;
      [ exists rho2; apply VOK_lv; [exact V2 | apply lscale_below; exact Bb2 |];
        rewrite Ha2, Hb2, (is_const_sound rho2 x c Kx), mul_w64, lscale_sound; reflexivity
      | destruct (is_const y) as [c|] eqn:Ky;
        [ exists rho2; apply VOK_lv; [exact V2 | apply lscale_below; exact Ba2 |];
          rewrite Ha2, Hb2, (is_const_sound rho2 y c Ky), mul_w64, lscale_sound; f_equal; lia
        | apply amul_itv_sound; assumption ] ]).
Qed.

Lemma sext32_is_w64 : forall v : bv 32, exists z, sext 64 v = w64 z /\ - 2 ^ 31 <= z < 2 ^ 31.
Proof.
  intros v. exists (bv_swrap 32 (bv_unsigned v)). split; [|apply bv_swrap32_range].
  apply bv_eq. rewrite sext32_unsigned. unfold w64. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma mulw_w64 : forall x y, sext 64 (mul_div M_MUL (low32 (w64 x)) (low32 (w64 y))) = w64 (bv_swrap 32 (x * y)).
Proof.
  intros. rewrite w_mulw. unfold v_mulw. unfold w64 at 3. f_equal. apply swrap32_mod64.
  rewrite !w64_unsigned, <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma amuldivw_gen_sound : forall rho st op a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (amuldivw_gen st op a b) rho' (sext 64 (mul_div op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb HVS Ha Hb Ba Bb. unfold amuldivw_gen.
  destruct (degrade2 rho st a b wa wb HVS Ha Hb Ba Bb) as (rho2 & H).
  destruct (degrade st a) as [a1 st1] eqn:Da. cbn [fst snd] in H.
  destruct (degrade st1 b) as [b1 st2] eqn:Db. cbn [fst snd] in H.
  destruct H as (E2 & V2 & Ha2 & Hb2 & Ba2 & Bb2).
  cbn beta iota. apply (VOK_after_ex rho st rho2 st2 _ _ E2).
  assert (FRESH : exists rho', VOK rho2 st2 (fresh_val st2 itv_s32) rho' (sext 64 (mul_div op (low32 wa) (low32 wb)))).
  { destruct (sext32_is_w64 (mul_div op (low32 wa) (low32 wb))) as (z & Hz & Rz). rewrite Hz.
    eapply VOK_fresh; [exact V2 | | reflexivity]. unfold itv_s32, in_itv; cbn [ilo ihi]; unfold LAI.two31; rewrite two31_eq; lia. }
  destruct op; try exact FRESH.
  destruct a1 as [|x|n1 k1 u1 v1|u1 v1]; try exact FRESH. destruct b1 as [|y|n2 k2 u2 v2|u2 v2]; try exact FRESH.
  cbn in Ha2, Hb2; cbn [aval_below] in Ba2, Bb2.
  destruct (is_const x) as [c|] eqn:Kx.
  - apply norm32_sound; [exact V2 | apply lscale_below; exact Bb2 |].
    rewrite Ha2, Hb2, (is_const_sound rho2 x c Kx), mulw_w64, lscale_sound. reflexivity.
  - destruct (is_const y) as [c|] eqn:Ky; [|exact FRESH].
    apply norm32_sound; [exact V2 | apply lscale_below; exact Ba2 |].
    rewrite Ha2, Hb2, (is_const_sound rho2 y c Ky), mulw_w64, lscale_sound. do 2 f_equal. lia.
Qed.

Lemma amuldivw0_sound : forall rho st op a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (amuldivw0 st op a b) rho' (sext 64 (mul_div op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb HVS Ha Hb Ba Bb. unfold amuldivw0.
  destruct (aval_litC (s_ctx st) a) as [x0|] eqn:La; [destruct (aval_litC (s_ctx st) b) as [y0|] eqn:Lb|].
  1: { rewrite (aval_litC_sound rho _ a x0 wa (proj1 HVS) La Ha), (aval_litC_sound rho _ b y0 wb (proj1 HVS) Lb Hb).
       exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [apply lit_mdw_ok | apply alit_below]. }
  all: apply amuldivw_gen_sound; assumption.
Qed.

(* [comment removed for export] *)
Lemma w64_01_eq : forall (c : bool), (if c then Z_to_bv 64 1 else Z_to_bv 64 0) = w64 (if c then 1 else 0).
Proof. intros [|]; reflexivity. Qed.

Lemma is_zero_cond0_sound : forall rho st v w,
  VS rho st -> val_ok rho v w -> aval_below v (s_next st) = true ->
  exists rho', VOK rho st (is_zero_cond0 st v) rho' (if Z.ltb (bv_unsigned w) 1 then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros rho st v w HVS Hv Hb. unfold is_zero_cond0. pose proof (u64_range w) as Rw.
  destruct v as [|l|n k a b|a b].
  - destruct (val01 (Z.ltb (bv_unsigned w) 1)) as (z & Hz & Rz). rewrite Hz.
    eapply VOK_fresh; [exact HVS | | reflexivity]. unfold itv01, in_itv; cbn; lia.
  - cbn in Hv. destruct (is_const l) as [c|] eqn:Kl.
    + exists rho. apply VOK_lit; [exact HVS|]. rewrite Hv, (is_const_sound rho l c Kl), w64_unsigned, two64I_eq.
      pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)).
      destruct (Z.eqb_spec (c mod 2 ^ 64) 0) as [E|E]; destruct (Z.ltb_spec (c mod 2 ^ 64) 1); try reflexivity; lia.
    + exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
      * cbn [val_ok cmp_holds xorb]. rewrite lconst_sound, two64z_eq, Hv, w64_unsigned.
        rewrite (Z.mod_small 0) by lia. pose proof (Z.mod_pos_bound (evl rho l) (2 ^ 64) ltac:(lia)).
        destruct (Z.ltb_spec (evl rho l mod 2 ^ 64) 1); destruct (Z.eqb_spec (evl rho l mod 2 ^ 64) 0); try reflexivity; lia.
      * cbn [aval_below]. cbn in Hb. rewrite Hb. reflexivity.
  - exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
    + cbn [val_ok] in *. rewrite Hv, w64_unsigned. destruct n, (cmp_holds rho k a b); reflexivity.
    + exact Hb.
  - exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
    + cbn [val_ok cmp_holds xorb] in *. rewrite Hv, bv_xor_unsigned, !w64_unsigned, two64z_eq.
      pose proof (Z.mod_pos_bound (evl rho a) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (evl rho b) (2 ^ 64) ltac:(lia)).
      destruct (Z.eqb_spec (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64)) as [E|E].
      * rewrite E, Z.lxor_nilpotent. reflexivity.
      * assert (Hnz : Z.lxor (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64) <> 0) by (intros X; apply (proj1 (Z.lxor_eq_0_iff _ _)) in X; exact (E X)).
        pose proof (proj2 (Z.lxor_nonneg (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64)) ltac:(split; intros; lia)).
        destruct (Z.ltb_spec (Z.lxor (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64)) 1); [lia|reflexivity].
    + exact Hb.
Qed.

Lemma is_nonzero_cond0_sound : forall rho st v w,
  VS rho st -> val_ok rho v w -> aval_below v (s_next st) = true ->
  exists rho', VOK rho st (is_nonzero_cond0 st v) rho' (if Z.ltb 0 (bv_unsigned w) then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros rho st v w HVS Hv Hb. unfold is_nonzero_cond0. pose proof (u64_range w) as Rw.
  destruct v as [|l|n k a b|a b].
  - destruct (val01 (Z.ltb 0 (bv_unsigned w))) as (z & Hz & Rz). rewrite Hz.
    eapply VOK_fresh; [exact HVS | | reflexivity]. unfold itv01, in_itv; cbn; lia.
  - cbn in Hv. destruct (is_const l) as [c|] eqn:Kl.
    + exists rho. apply VOK_lit; [exact HVS|]. rewrite Hv, (is_const_sound rho l c Kl), w64_unsigned, two64I_eq.
      pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)).
      destruct (Z.eqb_spec (c mod 2 ^ 64) 0) as [E|E]; destruct (Z.ltb_spec 0 (c mod 2 ^ 64)); try reflexivity; lia.
    + exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
      * cbn [val_ok cmp_holds xorb negb]. rewrite lconst_sound, two64z_eq, Hv, w64_unsigned.
        rewrite (Z.mod_small 0) by lia. pose proof (Z.mod_pos_bound (evl rho l) (2 ^ 64) ltac:(lia)).
        destruct (Z.ltb_spec 0 (evl rho l mod 2 ^ 64)); destruct (Z.eqb_spec (evl rho l mod 2 ^ 64) 0); try reflexivity; lia.
      * cbn [aval_below]. cbn in Hb. rewrite Hb. reflexivity.
  - exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
    + cbn [val_ok] in *. rewrite Hv, w64_unsigned. destruct n, (cmp_holds rho k a b); reflexivity.
    + exact Hb.
  - exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split.
    + cbn [val_ok cmp_holds xorb negb] in *. rewrite Hv, bv_xor_unsigned, !w64_unsigned, two64z_eq.
      pose proof (Z.mod_pos_bound (evl rho a) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (evl rho b) (2 ^ 64) ltac:(lia)).
      destruct (Z.eqb_spec (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64)) as [E|E].
      * rewrite E, Z.lxor_nilpotent. reflexivity.
      * assert (Hnz : Z.lxor (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64) <> 0) by (intros X; apply (proj1 (Z.lxor_eq_0_iff _ _)) in X; exact (E X)).
        pose proof (proj2 (Z.lxor_nonneg (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64)) ltac:(split; intros; lia)).
        destruct (Z.ltb_spec 0 (Z.lxor (evl rho a mod 2 ^ 64) (evl rho b mod 2 ^ 64))); [reflexivity|lia].
    + exact Hb.
Qed.

(* [comment removed for export] *)
Lemma VOK_cv_lit : forall rho st p rho' w,
  VOK rho st p rho' w -> VOK rho st (cv_lit (s_ctx (snd p)) (fst p), snd p) rho' w.
Proof.
  intros rho st [v st'] rho' w (A & B & C & D). unfold VOK; cbn [fst snd] in *.
  split; [exact A|]. split; [exact B|]. split; [apply cv_lit_sound; [exact (proj1 B) | exact C] | apply cv_lit_below; exact D].
Qed.
Lemma is_zero_cond_sound : forall rho st v w,
  VS rho st -> val_ok rho v w -> aval_below v (s_next st) = true ->
  exists rho', VOK rho st (is_zero_cond st v) rho' (if Z.ltb (bv_unsigned w) 1 then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros rho st v w HVS Hv Hb. unfold is_zero_cond.
  destruct (is_zero_cond0_sound rho st v w HVS Hv Hb) as (rho' & H). exists rho'. apply VOK_cv_lit. exact H.
Qed.
Lemma is_nonzero_cond_sound : forall rho st v w,
  VS rho st -> val_ok rho v w -> aval_below v (s_next st) = true ->
  exists rho', VOK rho st (is_nonzero_cond st v) rho' (if Z.ltb 0 (bv_unsigned w) then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros rho st v w HVS Hv Hb. unfold is_nonzero_cond.
  destruct (is_nonzero_cond0_sound rho st v w HVS Hv Hb) as (rho' & H). exists rho'. apply VOK_cv_lit. exact H.
Qed.


(* [comment removed for export] *)
Lemma litze_ok : forall rho C v w, ctx_ok rho C -> val_ok rho v w -> val_ok rho (litze C v) w.
Proof.
  intros rho C v w HC Hv. unfold litze. destruct (aval_litC C v) as [z|] eqn:E; [|exact Hv].
  apply alit_ok'. exact (aval_litC_sound rho C v z w HC E Hv).
Qed.
Lemma litze_below : forall C v n, aval_below v n = true -> aval_below (litze C v) n = true.
Proof. intros C v n H. unfold litze. destruct (aval_litC C v); [apply alit_below | exact H]. Qed.

Lemma aalu_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aalu st op a b) rho' (alu64 op wa wb).
Proof.
  intros rho st op a b wa wb GA N2 HVS Ha Hb Ba Bb. unfold aalu.
  apply aalu0_sound; try assumption; try (apply litze_ok; [exact (proj1 HVS) | assumption]); apply litze_below; assumption.
Qed.
Lemma aaluw_sound : forall rho st op a b wa wb,
  galign rho -> (NGLOB <= s_next st)%nat ->
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (aaluw st op a b) rho' (sext 64 (alu32 op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb GA HN HVS Ha Hb Ba Bb. unfold aaluw.
  apply aaluw0_sound; try assumption; try (apply litze_ok; [exact (proj1 HVS) | assumption]); apply litze_below; assumption.
Qed.
Lemma amuldiv_sound : forall rho st op a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (amuldiv st op a b) rho' (mul_div op wa wb).
Proof.
  intros rho st op a b wa wb HVS Ha Hb Ba Bb. unfold amuldiv.
  apply amuldiv0_sound; try assumption; try (apply litze_ok; [exact (proj1 HVS) | assumption]); apply litze_below; assumption.
Qed.
Lemma amuldivw_sound : forall rho st op a b wa wb,
  VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
  aval_below a (s_next st) = true -> aval_below b (s_next st) = true ->
  exists rho', VOK rho st (amuldivw st op a b) rho' (sext 64 (mul_div op (low32 wa) (low32 wb))).
Proof.
  intros rho st op a b wa wb HVS Ha Hb Ba Bb. unfold amuldivw.
  apply amuldivw0_sound; try assumption; try (apply litze_ok; [exact (proj1 HVS) | assumption]); apply litze_below; assumption.
Qed.

End LASA.
