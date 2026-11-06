(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Inductive aval : Type :=
| VL (w : w64)
| VS (f : lin)
| VR (lo hi : Z)
| VT
| VK (m v : Z).     (* [comment removed for export] *)

Definition aval_val (ρ : valuation) (v : aval) (w : bv 64) : Prop :=
  match v with
  | VL x => bv_unsigned w = wZ x
  | VS f => bv_unsigned w = leval ρ f
  | VR lo hi => lo <= bv_unsigned w <= hi
  | VT => True
  | VK m v => Z.land (bv_unsigned w) m = v
  end.

Definition vzero : aval := VL w_zero.

Lemma bvu_range (w : bv 64) : 0 <= bv_unsigned w < two64.
Proof. pose proof (bv_unsigned_in_range 64 w) as H. rewrite bv_modulus_64 in H. exact H. Qed.

Lemma aval_VL (ρ : valuation) (x : w64) (w : bv 64) : aval_val ρ (VL x) w <-> w = wbv x.
Proof. cbn [aval_val]. split; intros H; [apply bv_eq; rewrite wbv_unsigned; exact H | subst w; apply wbv_unsigned]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vrange (s : store) (v : aval) : option ivl :=
  match v with
  | VL x => let z := wZ x in Some (z, z)
  | VS f => lrange s f
  | VR lo hi => Some (lo, hi)
  | VT => None
  | VK _ _ => None
  end.

Lemma vrange_sound (ρ : valuation) (s : store) (v : aval) (w : bv 64) :
  sat ρ s -> aval_val ρ v w -> forall i, vrange s v = Some i -> fst i <= bv_unsigned w <= snd i.
Proof.
  intros Hs Hv i H. destruct v as [x|f|lo hi| |m v]; cbn [vrange aval_val] in *.
  - injection H as <-. rewrite Hv. cbn. lia.
  - rewrite Hv. exact (lrange_sound ρ s f Hs i H).
  - injection H as <-. cbn. lia.
  - discriminate.
  - discriminate.
Qed.

(* [comment removed for export] *)
Definition vform (v : aval) : option lin :=
  match v with
  | VL x => Some (lconst (wZ x))
  | VS f => Some f
  | _ => None
  end.

Lemma vform_sound (ρ : valuation) (v : aval) (w : bv 64) (f : lin) :
  aval_val ρ v w -> vform v = Some f -> bv_unsigned w = leval ρ f.
Proof.
  intros Hv H. destruct v; cbn [vform aval_val] in *; try discriminate; injection H as <-.
  - rewrite Hv, leval_lconst. reflexivity.
  - exact Hv.
Qed.

(* [comment removed for export] *)
Definition mk_vs0 (s : store) (f : lin) : aval :=
  match snd f with
  | [] => VL (wofZ (fst f))
  | _ =>
    match lrange s f with
    | Some (lo, hi) =>
        let j := lo / two64 in
        if j =? hi / two64 then
          (if lo =? hi then VL (wofZ lo) else VS (laddc f (- (j * two64))))
        else VT
    | None => VT
    end
  end.

Lemma mk_vs0_sound (ρ : valuation) (s : store) (f : lin) (w : bv 64) :
  sat ρ s -> bv_unsigned w = leval ρ f mod two64 -> aval_val ρ (mk_vs0 s f) w.
Proof.
  intros Hs Hw. unfold mk_vs0. destruct (snd f) as [|t r] eqn:Ets.
  - cbn [aval_val]. rewrite wZ_wofZ, Hw. unfold leval. rewrite Ets. cbn [teval]. rewrite Z.add_0_r. reflexivity.
  - destruct (lrange s f) as [[lo hi]|] eqn:El; [|exact I].
    pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr.
    destruct (Z.eqb_spec (lo / two64) (hi / two64)) as [E|E]; [|exact I].
    assert (Hq : leval ρ f / two64 = lo / two64).
    { apply Z.le_antisymm; [rewrite E|]; apply Z.div_le_mono; unfold two64; lia. }
    assert (Hm : leval ρ f mod two64 = leval ρ f - lo / two64 * two64).
    { rewrite Z.mod_eq by (unfold two64; lia). rewrite Hq. ring. }
    destruct (Z.eqb_spec lo hi) as [->|Hne]; cbn [aval_val].
    + rewrite wZ_wofZ, Hw. replace (leval ρ f) with hi by lia. reflexivity.
    + rewrite Hw, Hm, leval_laddc. ring.
Qed.

(* [comment removed for export] *)
Definition mk_vs (s : store) (f : lin) : aval := mk_vs0 s (lnorm s f).

Lemma mk_vs_sound (ρ : valuation) (s : store) (f : lin) (w : bv 64) :
  sat ρ s -> bv_unsigned w = leval ρ f mod two64 -> aval_val ρ (mk_vs s f) w.
Proof. intros Hs Hw. unfold mk_vs. apply mk_vs0_sound; [exact Hs|]. rewrite (lnorm_sound ρ s f Hs). exact Hw. Qed.

Definition mk_rng (lo hi : Z) : aval :=
  if (0 <=? lo) && (lo <=? hi) && (hi <? two64) then (if lo =? hi then VL (wofZ lo) else VR lo hi) else VT.

(* [comment removed for export] *)
Lemma mk_rng_mod (ρ : valuation) (lo hi z : Z) (w : bv 64) :
  lo <= z <= hi -> bv_unsigned w = z mod two64 -> aval_val ρ (mk_rng lo hi) w.
Proof.
  intros Hz Hw. unfold mk_rng. pose proof (bvu_range w).
  destruct ((0 <=? lo) && (lo <=? hi) && (hi <? two64)) eqn:E; cbn [aval_val]; [|exact I].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
  rewrite Z.mod_small in Hw by lia.
  destruct (Z.eqb_spec lo hi) as [->|Hne]; cbn [aval_val]; [|lia].
  rewrite wZ_wofZ. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mk_rng_sound (ρ : valuation) (lo hi : Z) (w : bv 64) :
  lo <= bv_unsigned w <= hi -> aval_val ρ (mk_rng lo hi) w.
Proof.
  intros H. apply (mk_rng_mod ρ lo hi (bv_unsigned w)); [exact H|]. symmetry. apply Z.mod_small. apply bvu_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wS_mod (b : w64) : wS b mod two64 = wZ b.
Proof.
  unfold wS. pose proof (wZ_range b). destruct (wh b).
  - replace (wZ b - two64) with (wZ b + (-1) * two64) by ring. rewrite Z.mod_add by (unfold two64; lia).
    apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma add_mod_wS (b : w64) (z : Z) : (wZ b + z) mod two64 = (wS b + z) mod two64.
Proof. rewrite <- (wS_mod b). rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma sub_mod_wS (b : w64) (z : Z) : (z - wZ b) mod two64 = (z - wS b) mod two64.
Proof. rewrite <- (wS_mod b). rewrite Zminus_mod_idemp_r. reflexivity. Qed.

Definition a_add (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_add a b)
  | VS f, VL b => mk_vs s (laddc f (wS b))
  | VL b, VS f => mk_vs s (laddc f (wS b))
  | VS f, VS g => mk_vs s (ladd f g)
  | VR lo hi, VL b => let k := wS b in mk_rng (lo + k) (hi + k)
  | VL b, VR lo hi => let k := wS b in mk_rng (lo + k) (hi + k)
  | _, _ => VT
  end.

Lemma a_add_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_add s x y) (bv_add a b).
Proof.
  intros Hs Hx Hy.
  assert (E : bv_unsigned (bv_add a b) = (bv_unsigned a + bv_unsigned b) mod two64)
    by (rewrite bv_add_unsigned; unfold bv_wrap; rewrite bv_modulus_64; reflexivity).
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_add aval_val] in *; try exact I.
  - rewrite E, Hx, Hy, wZ_add. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_laddc, Hx, Hy, add_mod_wS. f_equal. ring.
  - apply (mk_rng_mod ρ _ _ (wS xa + bv_unsigned b)); [lia|]. rewrite E, Hx, add_mod_wS. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_laddc, Hx, Hy, Z.add_comm, add_mod_wS. f_equal. ring.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_ladd, Hx, Hy. reflexivity.
  - apply (mk_rng_mod ρ _ _ (wS yb + bv_unsigned a)); [lia|]. rewrite E, Hy, Z.add_comm, add_mod_wS. reflexivity.
Qed.

Definition a_sub (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sub a b)
  | VS f, VL b => mk_vs s (laddc f (- wS b))
  | VL a, VS g => mk_vs s (lsub (lconst (wZ a)) g)
  | VS f, VS g => mk_vs s (lsub f g)
  | VR lo hi, VL b => let k := wS b in mk_rng (lo - k) (hi - k)
  | _, _ => VT
  end.

Lemma a_sub_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_sub s x y) (bv_sub a b).
Proof.
  intros Hs Hx Hy.
  assert (E : bv_unsigned (bv_sub a b) = (bv_unsigned a - bv_unsigned b) mod two64)
    by (rewrite bv_sub_unsigned; unfold bv_wrap; rewrite bv_modulus_64; reflexivity).
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_sub aval_val] in *; try exact I.
  - rewrite E, Hx, Hy, wZ_sub. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_lsub, leval_lconst, Hx, Hy. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_laddc, Hx, Hy, sub_mod_wS. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_lsub, Hx, Hy. reflexivity.
  - apply (mk_rng_mod ρ _ _ (bv_unsigned a - wS yb)); [lia|]. rewrite E, Hy, sub_mod_wS. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition low_mask_bits (m : Z) : option Z :=
  let k := Z.log2 (m + 1) in if (0 <=? m) && (2 ^ k =? m + 1) then Some k else None.

Lemma low_mask_bits_spec (m k : Z) : low_mask_bits m = Some k -> 0 <= k /\ m = 2 ^ k - 1.
Proof.
  unfold low_mask_bits. destruct ((0 <=? m) && (2 ^ Z.log2 (m + 1) =? m + 1)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E2.
  split; [apply Z.log2_nonneg | lia].
Qed.

Lemma land_low_mask (z k : Z) : 0 <= k -> Z.land z (2 ^ k - 1) = z mod 2 ^ k.
Proof. intros Hk. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma and_mask_range (z m k : Z) : 0 <= z -> 0 <= k -> m = 2 ^ k - 1 -> 0 <= Z.land z m <= m.
Proof.
  intros Hz Hk ->. rewrite land_low_mask by lia. pose proof (Z.mod_pos_bound z (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

(* [comment removed for export] *)
Fixpoint tsplit (k2 : Z) (ts : terms) : terms * terms :=
  match ts with
  | [] => ([], [])
  | (x, a) :: r =>
      let p := tsplit k2 r in
      if a mod k2 =? 0 then ((x, a / k2) :: fst p, snd p) else (fst p, (x, a) :: snd p)
  end.

Lemma tsplit_sound (ρ : valuation) (k2 : Z) (ts : terms) : 0 < k2 ->
  teval ρ ts = k2 * teval ρ (fst (tsplit k2 ts)) + teval ρ (snd (tsplit k2 ts)).
Proof.
  intros Hk. induction ts as [|[x a] r IH]; cbn [tsplit teval fst snd]; [lia|].
  destruct (Z.eqb_spec (a mod k2) 0) as [E|E]; cbn [teval fst snd].
  - rewrite IH. pose proof (Z.div_mod a k2 ltac:(lia)) as Ha. rewrite E, Z.add_0_r in Ha.
    rewrite Ha at 1. ring.
  - rewrite IH. ring.
Qed.

(* [comment removed for export] *)
Definition lshr0 (s : store) (f : lin) (k : Z) : option lin :=
  let k2 := 2 ^ k in
  let p := tsplit k2 (snd f) in
  match lrange s (fst f, snd p) with
  | Some (lo, hi) => if lo / k2 =? hi / k2 then Some (lo / k2, fst p) else None
  | None => None
  end.

Lemma lshr0_sound (ρ : valuation) (s : store) (f g : lin) (k : Z) :
  sat ρ s -> 0 <= k -> lshr0 s f k = Some g -> leval ρ g = leval ρ f / 2 ^ k.
Proof.
  intros Hs Hk H. unfold lshr0 in H. set (k2 := 2 ^ k) in *.
  assert (Hk2 : 0 < k2) by (apply Z.pow_pos_nonneg; lia).
  destruct (lrange s (fst f, snd (tsplit k2 (snd f)))) as [[lo hi]|] eqn:El; [|discriminate].
  destruct (Z.eqb_spec (lo / k2) (hi / k2)) as [E|E]; [|discriminate]. injection H as <-.
  pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. unfold leval in *. cbn [fst snd] in *.
  rewrite (tsplit_sound ρ k2 (snd f) Hk2).
  set (G := teval ρ (fst (tsplit k2 (snd f)))). set (Hh := teval ρ (snd (tsplit k2 (snd f)))) in *.
  replace (fst f + (k2 * G + Hh)) with ((fst f + Hh) + G * k2) by ring.
  rewrite Z.div_add by lia.
  assert (Hq : (fst f + Hh) / k2 = lo / k2).
  { apply Z.le_antisymm.
    - rewrite E. apply Z.div_le_mono; lia.
    - apply Z.div_le_mono; lia. }
  rewrite Hq. ring.
Qed.

(* [comment removed for export] *)
Definition lshr (s : store) (f : lin) (k : Z) : option lin :=
  match lrange s f with
  | Some (lo, hi) => if lo / 2 ^ k =? hi / 2 ^ k then Some (lconst (lo / 2 ^ k)) else lshr0 s f k
  | None => lshr0 s f k
  end.

Lemma lshr_sound (ρ : valuation) (s : store) (f g : lin) (k : Z) :
  sat ρ s -> 0 <= k -> lshr s f k = Some g -> leval ρ g = leval ρ f / 2 ^ k.
Proof.
  intros Hs Hk H. unfold lshr in H.
  destruct (lrange s f) as [[lo hi]|] eqn:El; [|exact (lshr0_sound ρ s f g k Hs Hk H)].
  destruct (Z.eqb_spec (lo / 2 ^ k) (hi / 2 ^ k)) as [E|E]; [|exact (lshr0_sound ρ s f g k Hs Hk H)].
  injection H as <-. rewrite leval_lconst. pose proof (lrange_sound ρ s f Hs _ El) as Hr. cbn [fst snd] in Hr.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  apply Z.le_antisymm; [apply Z.div_le_mono; lia|]. rewrite E. apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)
Definition bitrun (m : Z) : option (Z * Z) :=
  if 0 <? m then
    let j := Z.log2 (Z.land m (- m)) in
    if m mod 2 ^ j =? 0 then match low_mask_bits (m / 2 ^ j) with Some i => Some (j, i) | None => None end else None
  else None.

Lemma bitrun_spec (m j i : Z) : bitrun m = Some (j, i) -> 0 <= j /\ 0 <= i /\ m = 2 ^ j * (2 ^ i - 1).
Proof.
  unfold bitrun. destruct (Z.ltb_spec 0 m) as [Hm|Hm]; [|discriminate].
  set (j0 := Z.log2 (Z.land m (- m))).
  destruct (Z.eqb_spec (m mod 2 ^ j0) 0) as [E|E]; [|discriminate].
  destruct (low_mask_bits (m / 2 ^ j0)) as [i0|] eqn:El; [|discriminate].
  intros H. injection H as <- <-. destruct (low_mask_bits_spec _ _ El) as [Hi Hmi].
  assert (Hj : 0 <= j0) by apply Z.log2_nonneg.
  split; [exact Hj|]. split; [exact Hi|].
  pose proof (Z.div_mod m (2 ^ j0) ltac:(apply Z.pow_nonzero; lia)) as Hd. rewrite E, Z.add_0_r in Hd. rewrite Hd at 1. rewrite Hmi. ring.
Qed.

Lemma land_run (f j i : Z) : 0 <= f -> 0 <= j -> 0 <= i ->
  Z.land f (2 ^ j * (2 ^ i - 1)) = 2 ^ j * ((f / 2 ^ j) mod 2 ^ i).
Proof.
  intros Hf Hj Hi.
  assert (E1 : 2 ^ j * (2 ^ i - 1) = Z.shiftl (Z.ones i) j) by (rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia; lia).
  assert (E2 : 2 ^ j * ((f / 2 ^ j) mod 2 ^ i) = Z.shiftl (Z.land (Z.shiftr f j) (Z.ones i)) j).
  { rewrite Z.shiftl_mul_pow2, Z.land_ones, Z.shiftr_div_pow2 by lia. ring. }
  rewrite E1, E2.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.ltb_spec n j) as [Hl|Hl].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (n - j + j) with n by ring.
    destruct (Z.ltb_spec (n - j) i) as [Hl2|Hl2].
    + rewrite !Z.ones_spec_low by lia. reflexivity.
    + rewrite !Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition a_and_run (s : store) (f : lin) (m : Z) : option aval :=
  match bitrun m with
  | Some (j, i) =>
      match lshr s f j with
      | Some g1 => match lshr s g1 i with
                   | Some g2 => Some (mk_vs s (lscale (2 ^ j) (lsub g1 (lscale (2 ^ i) g2))))
                   | None => None
                   end
      | None => None
      end
  | None => None
  end.

Lemma a_and_run_sound (ρ : valuation) (s : store) (f : lin) (m : w64) (a : bv 64) (v : aval) :
  sat ρ s -> bv_unsigned a = leval ρ f -> a_and_run s f (wZ m) = Some v -> aval_val ρ v (bv_and a (wbv m)).
Proof.
  intros Hs Ha H. unfold a_and_run in H.
  destruct (bitrun (wZ m)) as [[j i]|] eqn:Eb; [|discriminate].
  destruct (bitrun_spec _ _ _ Eb) as [Hj [Hi Hm]].
  destruct (lshr s f j) as [g1|] eqn:E1; [|discriminate].
  destruct (lshr s g1 i) as [g2|] eqn:E2; [|discriminate]. injection H as <-.
  apply mk_vs_sound; [exact Hs|].
  pose proof (lshr_sound ρ s f g1 j Hs Hj E1) as H1. pose proof (lshr_sound ρ s g1 g2 i Hs Hi E2) as H2.
  pose proof (bvu_range a) as Hra.
  rewrite bv_and_unsigned, wbv_unsigned, Hm, Ha. rewrite land_run by lia.
  rewrite leval_lscale, leval_lsub, leval_lscale, H2, H1.
  set (X := leval ρ f / 2 ^ j).
  replace (X - 2 ^ i * (X / 2 ^ i)) with (X mod 2 ^ i) by (rewrite Z.mod_eq by (apply Z.pow_nonzero; lia); ring).
  symmetry. apply Z.mod_small.
  pose proof (Z.mod_pos_bound X (2 ^ i) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (wZ_range m) as Hr. rewrite Hm in Hr.
  split; nia.
Qed.

(* [comment removed for export] *)
Definition a_and_mask0 (s : store) (v : aval) (m : w64) : aval :=
  match low_mask_bits (wZ m) with
  | Some k =>
      match v with
      | VS f =>
          match lrange s f with
          | Some (lo, hi) => if (0 <=? lo) && (hi <=? wZ m) then VS f else mk_rng 0 (wZ m)
          | None => mk_rng 0 (wZ m)
          end
      | VR lo hi => if (0 <=? lo) && (hi <=? wZ m) then v else mk_rng 0 (wZ m)
      | _ => mk_rng 0 (wZ m)
      end
  | None => VT
  end.

Lemma a_and_mask0_sound (ρ : valuation) (s : store) (v : aval) (m : w64) (a : bv 64) :
  sat ρ s -> aval_val ρ v a -> aval_val ρ (a_and_mask0 s v m) (bv_and a (wbv m)).
Proof.
  intros Hs Hv. unfold a_and_mask0. pose proof (bvu_range a) as Ha.
  destruct (low_mask_bits (wZ m)) as [k|] eqn:Ek; [|exact I].
  pose proof (low_mask_bits_spec _ _ Ek) as [Hk Hm].
  assert (E : bv_unsigned (bv_and a (wbv m)) = bv_unsigned a mod 2 ^ k).
  { rewrite bv_and_unsigned, wbv_unsigned, Hm. apply land_low_mask. exact Hk. }
  assert (Hr : 0 <= bv_unsigned (bv_and a (wbv m)) <= wZ m).
  { rewrite E, Hm. pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)). lia. }
  destruct v as [x|f|lo hi| |km kv]; try (apply mk_rng_sound; exact Hr).
  - destruct (lrange s f) as [[lo hi]|] eqn:El; [|apply mk_rng_sound; exact Hr].
    pose proof (lrange_sound ρ s f Hs _ El) as Hr2. cbn [fst snd aval_val] in Hr2, Hv.
    destruct ((0 <=? lo) && (hi <=? wZ m)) eqn:Ec; [|apply mk_rng_sound; exact Hr].
    apply andb_prop in Ec as [Ec1 Ec2]. apply Z.leb_le in Ec1. apply Z.leb_le in Ec2.
    cbn [aval_val]. rewrite E, Hv. apply Z.mod_small. lia.
  - cbn [aval_val] in Hv. destruct ((0 <=? lo) && (hi <=? wZ m)) eqn:Ec; [|apply mk_rng_sound; exact Hr].
    apply andb_prop in Ec as [Ec1 Ec2]. apply Z.leb_le in Ec1. apply Z.leb_le in Ec2.
    cbn [aval_val]. rewrite E. rewrite Z.mod_small by lia. lia.
Qed.

Definition a_and_mask (s : store) (v : aval) (m : w64) : aval :=
  match v with
  | VS f => match a_and_run s f (wZ m) with Some r => r | None => a_and_mask0 s v m end
  | _ => a_and_mask0 s v m
  end.

Lemma a_and_mask_sound (ρ : valuation) (s : store) (v : aval) (m : w64) (a : bv 64) :
  sat ρ s -> aval_val ρ v a -> aval_val ρ (a_and_mask s v m) (bv_and a (wbv m)).
Proof.
  intros Hs Hv. unfold a_and_mask. destruct v as [x|f|lo hi| |km kv]; try (apply a_and_mask0_sound; assumption).
  destruct (a_and_run s f (wZ m)) as [r|] eqn:E; [|apply a_and_mask0_sound; assumption].
  exact (a_and_run_sound ρ s f m a r Hs Hv E).
Qed.

Definition a_and (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_and a b)
  | v, VL m => a_and_mask s v m
  | VL m, v => a_and_mask s v m
  | _, _ => VT
  end.

Lemma a_and_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_and s x y) (bv_and a b).
Proof.
  intros Hs Hx Hy.
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_and] in *; try exact I;
    try (apply aval_VL in Hy; subst b; apply a_and_mask_sound; assumption);
    try (apply aval_VL in Hx; subst a; rewrite bv_and_comm; apply a_and_mask_sound; assumption).
  cbn [aval_val] in *. rewrite bv_and_unsigned, Hx, Hy, wZ_and. reflexivity.
Qed.

Definition a_or0 (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_or a b)
  | v, VL b => if w_eqb b w_zero then v else VT
  | VL b, v => if w_eqb b w_zero then v else VT
  | _, _ => VT
  end.

Lemma a_or0_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_or0 s x y) (bv_or a b).
Proof.
  intros Hx Hy.
  assert (Z0 : forall (w : w64) (c d : bv 64) v, w_eqb w w_zero = true -> bv_unsigned d = wZ w -> aval_val ρ v c ->
                 aval_val ρ v (bv_or c d) /\ aval_val ρ v (bv_or d c)).
  { intros w c d v Hw Hd Hv. rewrite w_eqb_spec, wZ_zero in Hw. apply Z.eqb_eq in Hw.
    assert (Ed : d = Z_to_bv 64 0) by (apply bv_eq; rewrite Hd, Hw; reflexivity). subst d.
    replace (bv_or c (Z_to_bv 64 0)) with c by (apply bv_eq; rewrite bv_or_unsigned; cbn; rewrite Z.lor_0_r; reflexivity).
    replace (bv_or (Z_to_bv 64 0) c) with c by (apply bv_eq; rewrite bv_or_unsigned; cbn; rewrite Z.lor_0_l; reflexivity).
    split; exact Hv. }
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_or0] in *; try exact I.
  all: try (cbn [aval_val] in *; rewrite bv_or_unsigned, Hx, Hy, wZ_or; reflexivity).
  all: try (destruct (w_eqb yb w_zero) eqn:Ew; [exact (proj1 (Z0 yb a b _ Ew Hy Hx)) | exact I]).
  all: try (destruct (w_eqb xa w_zero) eqn:Ew; [exact (proj2 (Z0 xa b a _ Ew Hx Hy)) | exact I]).
Qed.

Definition a_xor (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_xor a b)
  | _, _ => VT
  end.

Lemma a_xor_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_xor s x y) (bv_xor a b).
Proof.
  intros Hx Hy. destruct x, y; cbn [a_xor aval_val] in *; try exact I.
  rewrite bv_xor_unsigned, Hx, Hy, wZ_xor. reflexivity.
Qed.

(* [comment removed for export] *)

Definition a_sll (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sll a (w_shamt6 b))
  | VS f, VL b => mk_vs s (lscale (2 ^ to_Z (w_shamt6 b)) f)
  | _, _ => VT
  end.

Lemma a_sll_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_sll s x y) (bv_shiftl a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_sll] in *; try exact I;
    apply aval_VL in Hy; subst b.
  - apply aval_VL in Hx. subst a. apply aval_VL. symmetry. apply wbv_sll.
  - apply mk_vs_sound; [exact Hs|]. rewrite leval_lscale. cbn [aval_val] in Hx.
    rewrite bv_shiftl_unsigned, bv_and_unsigned, wbv_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
    rewrite <- phi_shamt6. unfold bv_wrap. rewrite bv_modulus_64.
    rewrite Z.shiftl_mul_pow2 by (pose proof (phi_shamt6_range yb); lia). rewrite Hx. f_equal. ring.
Qed.

Definition a_srl (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_srl a (w_shamt6 b))
  | VS f, VL b =>
      let k := to_Z (w_shamt6 b) in
      match lshr s f k with
      | Some g => mk_vs s g
      | None => match lrange s f with Some (lo, hi) => mk_rng (Z.max 0 lo / 2 ^ k) (Z.min (two64 - 1) hi / 2 ^ k) | None => VT end
      end
  | VR lo hi, VL b => let k := to_Z (w_shamt6 b) in mk_rng (lo / 2 ^ k) (hi / 2 ^ k)
  | _, _ => VT
  end.

Lemma a_srl_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_srl s x y) (bv_shiftr a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_srl] in *; try exact I;
    apply aval_VL in Hy; subst b.
  all: assert (E : bv_unsigned (bv_shiftr a (bv_and (wbv yb) (Z_to_bv 64 63))) = bv_unsigned a / 2 ^ to_Z (w_shamt6 yb))
         by (rewrite bv_shiftr_unsigned, bv_and_unsigned, wbv_unsigned, Z_to_bv_unsigned; change (bv_wrap 64 63) with 63;
             rewrite <- phi_shamt6; apply Z.shiftr_div_pow2; pose proof (phi_shamt6_range yb); lia).
  all: pose proof (phi_shamt6_range yb) as Hk; pose proof (bvu_range a) as Ha.
  all: assert (Hk2 : 0 < 2 ^ to_Z (w_shamt6 yb)) by (apply Z.pow_pos_nonneg; lia).
  - apply aval_VL in Hx. subst a. apply aval_VL. symmetry. apply wbv_srl.
  - cbn [aval_val] in Hx. destruct (lshr s f (to_Z (w_shamt6 yb))) as [g|] eqn:El.
    + apply mk_vs_sound; [exact Hs|]. rewrite (lshr_sound ρ s f g (to_Z (w_shamt6 yb)) Hs ltac:(lia) El), E, Hx.
      rewrite Z.mod_small; [reflexivity|]. rewrite <- Hx. split; [apply Z.div_pos; lia|].
      apply Z.le_lt_trans with (bv_unsigned a); [apply Z.div_le_upper_bound; nia | lia].
    + destruct (lrange s f) as [[lo hi]|] eqn:Er; [|exact I]. apply mk_rng_sound.
      pose proof (lrange_sound ρ s f Hs _ Er) as Hr. cbn [fst snd] in Hr. rewrite E.
      split; apply Z.div_le_mono; lia.
  - cbn [aval_val] in Hx. apply mk_rng_sound. rewrite E. split; apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)
Definition a_sra (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sra a (w_shamt6 b))
  | _, _ => VT
  end.

Lemma a_sra_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_sra s x y) (bv_ashiftr a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hx Hy. destruct x, y; cbn [a_sra]; try exact I.
  apply aval_VL in Hx. apply aval_VL in Hy. subst. apply aval_VL. symmetry. apply wbv_sra.
Qed.

Definition a_mul (s : store) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_mul a b)
  | VS f, VL b => mk_vs s (lscale (wZ b) f)
  | VL b, VS f => mk_vs s (lscale (wZ b) f)
  | _, _ => VT
  end.

Lemma a_mul_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_mul s x y) (bv_mul a b).
Proof.
  intros Hs Hx Hy.
  assert (E : bv_unsigned (bv_mul a b) = (bv_unsigned a * bv_unsigned b) mod two64)
    by (rewrite bv_mul_unsigned; unfold bv_wrap; rewrite bv_modulus_64; reflexivity).
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_mul aval_val] in *; try exact I.
  - rewrite E, Hx, Hy, wZ_mul. reflexivity.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_lscale, Hx, Hy. f_equal; ring.
  - apply mk_vs_sound; [exact Hs|]. rewrite E, leval_lscale, Hx, Hy. f_equal; ring.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kb_or_sound (w1 w2 m1 m2 v1 v2 : Z) :
  Z.land w1 m1 = v1 -> Z.land w2 m2 = v2 ->
  Z.land (Z.lor w1 w2) (Z.lor (Z.land m1 m2) (Z.lor v1 v2)) = Z.lor v1 v2.
Proof.
  intros H1 H2. subst v1 v2. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec.
  destruct (Z.testbit w1 i), (Z.testbit w2 i), (Z.testbit m1 i), (Z.testbit m2 i); reflexivity.
Qed.

Lemma testbit_small (w i : Z) : 0 <= w < 2 ^ 64 -> 64 <= i -> Z.testbit w i = false.
Proof.
  intros Hw Hi. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply Z.lt_le_trans with (2 ^ 64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma mask_hi (t : Z) : 0 <= t <= 64 -> 2 ^ 64 - 2 ^ t = Z.shiftl (Z.ones (64 - t)) t.
Proof.
  intros Ht. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv.
  assert (E : 2 ^ 64 = 2 ^ (64 - t) * 2 ^ t) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). rewrite E. unfold Z.pred. ring.
Qed.

Lemma land_ldiff_ones (w t : Z) : 0 <= w < 2 ^ 64 -> 0 <= t <= 64 ->
  Z.land w (2 ^ 64 - 2 ^ t) = w / 2 ^ t * 2 ^ t.
Proof.
  intros Hw Ht. rewrite mask_hi by lia. rewrite <- Z.shiftr_div_pow2 by lia. rewrite <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_dec i t) as [Hit|Hit].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia. rewrite Z.shiftr_spec by lia.
    replace (i - t + t) with i by lia.
    destruct (Z_lt_dec i 64) as [H64|H64].
    + rewrite (proj2 (Z.ltb_lt (i - t) (64 - t))) by lia. rewrite (proj2 (Z.leb_le 0 (i - t))) by lia. apply andb_true_r.
    + rewrite testbit_small by lia. reflexivity.
Qed.

Lemma testbit_smallW (w i W : Z) : 0 <= W -> 0 <= w < 2 ^ W -> W <= i -> Z.testbit w i = false.
Proof.
  intros HW Hw Hi. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. apply Z.lt_le_trans with (2 ^ W); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma kb_srl_sound (w m v k W : Z) : Z.land w m = v -> 0 <= W <= 64 -> 0 <= w < 2 ^ W -> 0 <= k <= W ->
  Z.land (Z.shiftr w k) (Z.lor (Z.shiftr m k) (2 ^ 64 - 2 ^ (W - k))) = Z.shiftr v k.
Proof.
  intros H HW Hw Hk. subst v. rewrite mask_hi by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, !Z.shiftr_spec, Z.land_spec by lia.
  destruct (Z_lt_dec i (W - k)) as [H1|H1].
  - rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r. reflexivity.
  - rewrite (testbit_smallW w (i + k) W) by lia. reflexivity.
Qed.

Lemma kb_sll_sound (w m v k : Z) : Z.land w m = v -> 0 <= k <= 64 ->
  Z.land ((Z.shiftl w k) mod 2 ^ 64) (Z.lor ((Z.shiftl m k) mod 2 ^ 64) (Z.ones k)) = (Z.shiftl v k) mod 2 ^ 64.
Proof.
  intros H Hk. subst v. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  destruct (Z_lt_dec i k) as [H1|H1].
  - rewrite !Z.shiftl_spec_low by lia. cbn. reflexivity.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec.
    rewrite (proj2 (Z.ltb_ge i k)) by lia. rewrite (proj2 (Z.leb_le 0 i)) by lia. destruct (Z.testbit w (i - k)), (Z.testbit m (i - k)), (i <? 64); reflexivity.
Qed.

Lemma some_pair_eq {X Y : Type} (a c : X) (b d : Y) : Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros H. injection H. auto. Qed.

Lemma some_inj {X : Type} (a b : X) : Some a = Some b -> a = b.
Proof. intros H. injection H. auto. Qed.

Lemma lor_shl_disj (x y k : Z) : 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y ->
  Z.lor (Z.shiftl y k) x = Z.shiftl y k + x.
Proof.
  intros Hk Hx Hy. rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
    destruct (Z_lt_dec i k) as [Hl|Hl]; [rewrite Z.shiftl_spec_low by lia; reflexivity
    | rewrite (testbit_smallW x i k) by lia; apply andb_false_r]).
  rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec i k) as [Hl|Hl]; [rewrite Z.shiftl_spec_low by lia; reflexivity | rewrite (testbit_smallW x i k) by lia; apply andb_false_r].
Qed.

Lemma ones64 : two64 - 1 = Z.ones 64.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint ptz (lo hi t : Z) (fuel : nat) : Z :=
  match fuel with O => 64 | S f => if lo / 2 ^ t =? hi / 2 ^ t then t else ptz lo hi (t + 1) f end.

(* [comment removed for export] *)
Definition tok (s : store) (x : aval) : option (Z * Z) :=
  match x with
  | VL a => Some (two64 - 1, wZ a)
  | VK m v => Some (m, v)
  | VT => None
  | _ =>
      match vrange s x with
      | Some (lo, hi) =>
          let t := ptz lo hi 0 65 in
          if (0 <=? lo) && (lo <=? hi) && (hi <? two64) && (0 <=? t) && (t <=? 64) && (lo / 2 ^ t =? hi / 2 ^ t)
          then Some (two64 - 2 ^ t, lo / 2 ^ t * 2 ^ t) else None
      | None => None
      end
  end.

Lemma tok_sound (ρ : valuation) (s : store) (x : aval) (w : bv 64) (m v : Z) :
  sat ρ s -> aval_val ρ x w -> tok s x = Some (m, v) -> Z.land (bv_unsigned w) m = v.
Proof.
  intros Hs Hx H. pose proof (bvu_range w) as Hw. unfold two64 in Hw.
  assert (Hgen : forall lo hi, vrange s x = Some (lo, hi) ->
            (if (0 <=? lo) && (lo <=? hi) && (hi <? two64) && (0 <=? ptz lo hi 0 65) && (ptz lo hi 0 65 <=? 64)
                && (lo / 2 ^ ptz lo hi 0 65 =? hi / 2 ^ ptz lo hi 0 65)
             then Some (two64 - 2 ^ ptz lo hi 0 65, lo / 2 ^ ptz lo hi 0 65 * 2 ^ ptz lo hi 0 65) else None) = Some (m, v) ->
            Z.land (bv_unsigned w) m = v).
  { intros lo hi Er E. set (t := ptz lo hi 0 65) in *.
    destruct ((0 <=? lo) && (lo <=? hi) && (hi <? two64) && (0 <=? t) && (t <=? 64) && (lo / 2 ^ t =? hi / 2 ^ t)) eqn:Ec; [|discriminate].
    apply some_pair_eq in E as [<- <-].
    repeat match goal with Hc : _ && _ = true |- _ => apply andb_prop in Hc as [? ?] end.
    repeat match goal with Hc : (_ <=? _) = true |- _ => apply Z.leb_le in Hc
                      | Hc : (_ <? _) = true |- _ => apply Z.ltb_lt in Hc
                      | Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc end.
    pose proof (vrange_sound ρ s x w Hs Hx _ Er) as Hr. cbn [fst snd] in Hr.
    assert (Hp : 0 < 2 ^ t) by (apply Z.pow_pos_nonneg; lia).
    assert (Hd : bv_unsigned w / 2 ^ t = lo / 2 ^ t).
    { apply Z.le_antisymm.
      - match goal with Hq : lo / 2 ^ t = hi / 2 ^ t |- _ => rewrite Hq end. apply Z.div_le_mono; lia.
      - apply Z.div_le_mono; lia. }
    unfold two64. rewrite land_ldiff_ones by lia. rewrite Hd. reflexivity. }
  destruct x as [a|f|lo hi| |km kv]; cbn [tok] in H.
  - apply some_pair_eq in H as [<- <-]. cbn [aval_val] in Hx. rewrite <- Hx.
    rewrite ones64. rewrite Z.land_ones by lia. apply Z.mod_small. lia.
  - destruct (vrange s (VS f)) as [[lo hi]|] eqn:Er; [|discriminate]. exact (Hgen lo hi eq_refl H).
  - destruct (vrange s (VR lo hi)) as [[lo' hi']|] eqn:Er; [|discriminate]. exact (Hgen lo' hi' eq_refl H).
  - discriminate.
  - apply some_pair_eq in H as [<- <-]. exact Hx.
Qed.

Definition mkvk (m v : Z) : aval := if m =? two64 - 1 then VL (wofZ v) else VK m v.

Lemma mkvk_sound (ρ : valuation) (m v : Z) (w : bv 64) : Z.land (bv_unsigned w) m = v -> aval_val ρ (mkvk m v) w.
Proof.
  intros H. unfold mkvk. destruct (Z.eqb_spec m (two64 - 1)) as [E|E]; cbn [aval_val]; [|exact H].
  pose proof (bvu_range w) as Hw. subst m. rewrite ones64 in H.
  rewrite Z.land_ones in H by lia. rewrite Z.mod_small in H by (unfold two64 in Hw; lia). rewrite wZ_wofZ, <- H. rewrite Z.mod_small; [reflexivity|]. exact Hw.
Qed.

Definition a_or_kb (s : store) (x y : aval) : aval :=
  match tok s x, tok s y with
  | Some (m1, v1), Some (m2, v2) => mkvk (Z.lor (Z.land m1 m2) (Z.lor v1 v2)) (Z.lor v1 v2)
  | _, _ => VT
  end.

Lemma a_or_kb_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_or_kb s x y) (bv_or a b).
Proof.
  intros Hs Hx Hy. unfold a_or_kb.
  destruct (tok s x) as [[m1 v1]|] eqn:E1; [|exact I]. destruct (tok s y) as [[m2 v2]|] eqn:E2; [|exact I].
  apply mkvk_sound. rewrite bv_or_unsigned. apply kb_or_sound; [exact (tok_sound ρ s x a m1 v1 Hs Hx E1) | exact (tok_sound ρ s y b m2 v2 Hs Hy E2)].
Qed.

(* [comment removed for export] *)
Definition a_or_disj (s : store) (x y : aval) : option aval :=
  match vform x, vform y with
  | Some f, Some g =>
      match lrange s g, lrange s f with
      | Some (lo2, hi2), Some (lo1, hi1) =>
          if (0 <=? lo2) && (0 <? hi2) && (0 <=? lo1) && (hi1 + hi2 <? two64) then
            let k2 := 2 ^ (Z.log2 hi2 + 1) in
            match tsplit k2 (snd f) with
            | (_, []) => if fst f mod k2 =? 0 then Some (mk_vs s (ladd f g)) else None
            | _ => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Lemma a_or_disj_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) (v : aval) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_or_disj s x y = Some v -> aval_val ρ v (bv_or a b).
Proof.
  intros Hs Hx Hy H. unfold a_or_disj in H.
  destruct (vform x) as [f|] eqn:Ef; [|discriminate]. destruct (vform y) as [g|] eqn:Eg; [|discriminate].
  destruct (lrange s g) as [[lo2 hi2]|] eqn:Er2; [|discriminate]. destruct (lrange s f) as [[lo1 hi1]|] eqn:Er1; [|discriminate].
  destruct ((0 <=? lo2) && (0 <? hi2) && (0 <=? lo1) && (hi1 + hi2 <? two64)) eqn:Ec; [|discriminate].
  apply andb_prop in Ec as [Ec E4]. apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. apply Z.ltb_lt in E4.
  set (K := Z.log2 hi2 + 1) in *. set (k2 := 2 ^ K) in *.
  assert (HK : 0 <= K) by (unfold K; pose proof (Z.log2_nonneg hi2); lia).
  assert (Hk2 : 0 < k2) by (apply Z.pow_pos_nonneg; lia).
  assert (Hhi2 : hi2 < k2) by (unfold k2, K; apply Z.log2_spec; lia).
  destruct (tsplit k2 (snd f)) as [dv rest] eqn:Et. destruct rest as [|? ?]; [|discriminate].
  destruct (fst f mod k2 =? 0) eqn:Em; [|discriminate]. apply some_inj in H. subst v. apply Z.eqb_eq in Em.
  pose proof (vform_sound ρ x a f Hx Ef) as Ha. pose proof (vform_sound ρ y b g Hy Eg) as Hb.
  pose proof (lrange_sound ρ s f Hs _ Er1) as Hr1. pose proof (lrange_sound ρ s g Hs _ Er2) as Hr2. cbn [fst snd] in Hr1, Hr2.
  pose proof (tsplit_sound ρ k2 (snd f) Hk2) as Hts. rewrite Et in Hts. cbn [fst snd teval] in Hts.
  apply mk_vs_sound; [exact Hs|]. rewrite bv_or_unsigned, Ha, Hb, leval_ladd.
  assert (Hf2 : leval ρ f = k2 * (fst f / k2 + teval ρ dv)).
  { unfold leval. rewrite Hts. pose proof (Z.div_mod (fst f) k2 ltac:(lia)) as Hdm. rewrite Em, Z.add_0_r in Hdm. rewrite Hdm at 1. ring. }
  assert (Hh : 0 <= fst f / k2 + teval ρ dv) by nia.
  rewrite Hf2.
  replace (k2 * (fst f / k2 + teval ρ dv)) with (Z.shiftl (fst f / k2 + teval ρ dv) K) by (rewrite Z.shiftl_mul_pow2 by lia; unfold k2; ring).
  rewrite lor_shl_disj by (try lia; rewrite <- Hb; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (E : (fst f / k2 + teval ρ dv) * 2 ^ K = leval ρ f) by (rewrite Hf2; unfold k2; ring). rewrite E.
  rewrite Z.mod_small; [reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a_or_low (s : store) (x y : aval) : option aval :=
  match x, y with
  | VS f, VL c =>
      let cz := wZ c in
      if 0 <? cz then
        let K := Z.log2 cz + 1 in
        match lshr s f K with
        | Some g =>
            match lrange s (lsub f (lscale (2 ^ K) g)) with
            | Some (r0, r1) => if (r0 =? r1) && (0 <=? r0) then Some (mk_vs s (laddc (lscale (2 ^ K) g) (Z.lor r0 cz))) else None
            | None => None
            end
        | None => None
        end
      else None
  | _, _ => None
  end.

Lemma lor_lt_pow2 (a b k : Z) : 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  assert (Sa : Z.shiftr a k = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  assert (Sb : Z.shiftr b k = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  assert (S : Z.shiftr (Z.lor a b) k = 0) by (rewrite Z.shiftr_lor, Sa, Sb; reflexivity).
  rewrite Z.shiftr_div_pow2 in S by lia.
  pose proof (Z.lor_nonneg a b) as Hn.
  destruct (Z_lt_le_dec (Z.lor a b) (2 ^ k)) as [H|H]; [exact H|].
  exfalso. assert (1 <= Z.lor a b / 2 ^ k) by (apply Z.div_le_lower_bound; [apply Z.pow_pos_nonneg; lia | lia]). lia.
Qed.

Lemma a_or_low_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) (v : aval) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_or_low s x y = Some v -> aval_val ρ v (bv_or a b).
Proof.
  intros Hs Hx Hy H. unfold a_or_low in H. destruct x as [|f| | |]; try discriminate. destruct y as [c| | | |]; try discriminate.
  cbn [aval_val] in Hx, Hy. set (cz := wZ c) in *. destruct (Z.ltb_spec 0 cz) as [Hc|Hc]; [|discriminate].
  set (K := Z.log2 cz + 1) in *. assert (HK : 0 <= K) by (unfold K; pose proof (Z.log2_nonneg cz); lia).
  destruct (lshr s f K) as [g|] eqn:Eg; [|discriminate].
  destruct (lrange s (lsub f (lscale (2 ^ K) g))) as [[r0 r1]|] eqn:Er; [|discriminate].
  destruct ((r0 =? r1) && (0 <=? r0)) eqn:Ec; [|discriminate]. apply some_inj in H. subst v.
  apply andb_prop in Ec as [E1 E2]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. subst r1.
  pose proof (lshr_sound ρ s f g K Hs HK Eg) as Hg. pose proof (lrange_sound ρ s _ Hs _ Er) as Hr. cbn [fst snd] in Hr.
  rewrite leval_lsub, leval_lscale, Hg in Hr.
  pose proof (bvu_range a) as Ha. pose proof (wZ_range c) as Hcr.
  assert (HK2 : 0 < 2 ^ K) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcz : cz < 2 ^ K) by (unfold K; apply Z.log2_spec; lia).
  assert (Er0 : r0 = leval ρ f mod 2 ^ K) by (rewrite Z.mod_eq by lia; lia).
  assert (Hr0 : 0 <= r0 < 2 ^ K) by (rewrite Er0; apply Z.mod_pos_bound; lia).
  apply mk_vs_sound; [exact Hs|]. rewrite leval_laddc, leval_lscale, Hg.
  rewrite bv_or_unsigned, Hx, Hy. fold cz.
  set (q := leval ρ f / 2 ^ K).
  assert (Hq : 0 <= q) by (apply Z.div_pos; lia).
  assert (Ef : leval ρ f = Z.shiftl q K + r0).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Er0. unfold q. pose proof (Z.div_mod (leval ρ f) (2 ^ K) ltac:(lia)). lia. }
  pose proof (lor_lt_pow2 r0 cz K HK Hr0 ltac:(lia)) as Hlr.
  assert (Elor : Z.lor (leval ρ f) cz = 2 ^ K * q + Z.lor r0 cz).
  { rewrite Ef. rewrite <- (lor_shl_disj r0 q K HK Hr0 Hq). rewrite <- Z.lor_assoc.
    rewrite (lor_shl_disj (Z.lor r0 cz) q K HK Hlr Hq). rewrite Z.shiftl_mul_pow2 by lia. ring. }
  rewrite <- Elor. symmetry. apply Z.mod_small.
  rewrite <- Hx. apply (lor_lt_pow2 _ _ 64); [lia | rewrite Hx; unfold two64 in *; lia | unfold two64 in *; lia].
Qed.

Definition a_or (s : store) (x y : aval) : aval :=
  match a_or0 s x y with
  | VT => match a_or_disj s x y with
          | Some v => v
          | None => match a_or_disj s y x with
                    | Some v => v
                    | None => match a_or_low s x y with
                              | Some v => v
                              | None => match a_or_low s y x with Some v => v | None => a_or_kb s x y end
                              end
                    end
          end
  | v => v
  end.

Lemma a_or_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_or s x y) (bv_or a b).
Proof.
  intros Hs Hx Hy. unfold a_or. pose proof (a_or0_sound ρ s x y a b Hx Hy) as H0.
  destruct (a_or0 s x y) eqn:E; try exact H0.
  destruct (a_or_disj s x y) as [v|] eqn:E1; [exact (a_or_disj_sound ρ s x y a b v Hs Hx Hy E1)|].
  destruct (a_or_disj s y x) as [v|] eqn:E2.
  - rewrite bv_or_comm. exact (a_or_disj_sound ρ s y x b a v Hs Hy Hx E2).
  - destruct (a_or_low s x y) as [v|] eqn:E3; [exact (a_or_low_sound ρ s x y a b v Hs Hx Hy E3)|].
    destruct (a_or_low s y x) as [v|] eqn:E4.
    + rewrite bv_or_comm. exact (a_or_low_sound ρ s y x b a v Hs Hy Hx E4).
    + exact (a_or_kb_sound ρ s x y a b Hs Hx Hy).
Qed.

(* [comment removed for export] *)
Definition a_srl' (s : store) (x y : aval) : aval :=
  match a_srl s x y, x, y with
  | VT, VK m v, VL b => let k := to_Z (w_shamt6 b) in mkvk (Z.lor (Z.shiftr m k) (two64 - 2 ^ (64 - k))) (Z.shiftr v k)
  | r, _, _ => r
  end.

Lemma a_srl'_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_srl' s x y) (bv_shiftr a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. unfold a_srl'. pose proof (a_srl_sound ρ s x y a b Hs Hx Hy) as H0.
  destruct (a_srl s x y) eqn:E; try exact H0.
  destruct x as [| | | |m v]; try exact H0. destruct y as [yb| | | |]; try exact H0.
  apply aval_VL in Hy. subst b. apply mkvk_sound. cbn [aval_val] in Hx.
  rewrite bv_shiftr_unsigned, bv_and_unsigned, wbv_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
  rewrite <- phi_shamt6. pose proof (phi_shamt6_range yb). pose proof (bvu_range a). unfold two64 in *.
  apply kb_srl_sound; [exact Hx | lia | lia | lia].
Qed.

Definition a_sll' (s : store) (x y : aval) : aval :=
  match a_sll s x y, x, y with
  | VT, VK m v, VL b => let k := to_Z (w_shamt6 b) in mkvk (Z.lor ((Z.shiftl m k) mod two64) (Z.ones k)) ((Z.shiftl v k) mod two64)
  | r, _, _ => r
  end.

Lemma a_sll'_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_sll' s x y) (bv_shiftl a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. unfold a_sll'. pose proof (a_sll_sound ρ s x y a b Hs Hx Hy) as H0.
  destruct (a_sll s x y) eqn:E; try exact H0.
  destruct x as [| | | |m v]; try exact H0. destruct y as [yb| | | |]; try exact H0.
  apply aval_VL in Hy. subst b. apply mkvk_sound. cbn [aval_val] in Hx.
  rewrite bv_shiftl_unsigned, bv_and_unsigned, wbv_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 63) with 63.
  rewrite <- phi_shamt6. pose proof (phi_shamt6_range yb). unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  apply kb_sll_sound; [exact Hx | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition a_ltu (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_ltu a b)
  | _, _ =>
      match vform x, vform y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if hi <? 0 then Some true else if 0 <=? lo then Some false else None
          | None => None
          end
      | _, _ =>
          match vrange s x, vrange s y with
          | Some (xl, xh), Some (yl, yh) => if xh <? yl then Some true else if yh <=? xl then Some false else None
          | _, _ => None
          end
      end
  end.

Lemma a_ltu_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) (r : bool) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_ltu s x y = Some r -> r = bv_ltu a b.
Proof.
  intros Hs Hx Hy H. unfold bv_ltu.
  assert (Hgen : forall d, (bv_unsigned a <? bv_unsigned b) = d ->
                   (match vform x, vform y with
                    | Some f, Some g =>
                        match lrange s (lsub f g) with
                        | Some (lo, hi) => if hi <? 0 then Some true else if 0 <=? lo then Some false else None
                        | None => None
                        end
                    | _, _ =>
                        match vrange s x, vrange s y with
                        | Some (xl, xh), Some (yl, yh) => if xh <? yl then Some true else if yh <=? xl then Some false else None
                        | _, _ => None
                        end
                    end) = Some r -> r = d).
  { intros d Hd Hm. destruct (vform x) as [f|] eqn:Ef; destruct (vform y) as [g|] eqn:Eg.
    1:{ pose proof (vform_sound ρ x a f Hx Ef) as Hf. pose proof (vform_sound ρ y b g Hy Eg) as Hg.
      destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:El; [|discriminate].
      pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub, <- Hf, <- Hg in Hr.
      subst d. destruct (Z.ltb_spec hi 0); [injection Hm as <-; symmetry; apply Z.ltb_lt; lia|].
      destruct (Z.leb_spec 0 lo); [injection Hm as <-; symmetry; apply Z.ltb_ge; lia | discriminate]. }
    all: destruct (vrange s x) as [[xl xh]|] eqn:Ex; destruct (vrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    all: pose proof (vrange_sound ρ s x a Hs Hx _ Ex) as Hrx; pose proof (vrange_sound ρ s y b Hs Hy _ Ey) as Hry.
    all: cbn [fst snd] in Hrx, Hry; subst d.
    all: destruct (Z.ltb_spec xh yl); [injection Hm as <-; symmetry; apply Z.ltb_lt; lia|].
    all: destruct (Z.leb_spec yh xl); [injection Hm as <-; symmetry; apply Z.ltb_ge; lia | discriminate]. }
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_ltu] in H;
    try (apply (Hgen _ eq_refl H)).
  injection H as <-. cbn [aval_val] in *. rewrite Hx, Hy. apply w_ltu_spec.
Qed.

(* [comment removed for export] *)
Definition a_eq (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_eqb a b)
  | _, _ =>
      match vform x, vform y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else if (lo =? 0) && (hi =? 0) then Some true else None
          | None => None
          end
      | _, _ =>
          match vrange s x, vrange s y with
          | Some (xl, xh), Some (yl, yh) => if (xh <? yl) || (yh <? xl) then Some false else None
          | _, _ => None
          end
      end
  end.

Lemma a_eq_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) (r : bool) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_eq s x y = Some r -> r = bv_eqb a b.
Proof.
  intros Hs Hx Hy H. unfold bv_eqb.
  assert (Hgen : forall d, (bv_unsigned a =? bv_unsigned b) = d ->
                   (match vform x, vform y with
                    | Some f, Some g =>
                        match lrange s (lsub f g) with
                        | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else if (lo =? 0) && (hi =? 0) then Some true else None
                        | None => None
                        end
                    | _, _ =>
                        match vrange s x, vrange s y with
                        | Some (xl, xh), Some (yl, yh) => if (xh <? yl) || (yh <? xl) then Some false else None
                        | _, _ => None
                        end
                    end) = Some r -> r = d).
  { intros d Hd Hm. destruct (vform x) as [f|] eqn:Ef; destruct (vform y) as [g|] eqn:Eg.
    1:{ pose proof (vform_sound ρ x a f Hx Ef) as Hf. pose proof (vform_sound ρ y b g Hy Eg) as Hg.
      destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:El; [|discriminate].
      pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub, <- Hf, <- Hg in Hr.
      subst d. destruct ((hi <? 0) || (0 <? lo)) eqn:E1.
      + injection Hm as <-. symmetry. apply Z.eqb_neq. apply orb_prop in E1 as [E1|E1];
          [apply Z.ltb_lt in E1 | apply Z.ltb_lt in E1]; lia.
      + destruct ((lo =? 0) && (hi =? 0)) eqn:E2; [|discriminate]. injection Hm as <-.
        apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. symmetry. apply Z.eqb_eq. lia. }
    all: destruct (vrange s x) as [[xl xh]|] eqn:Ex; destruct (vrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    all: pose proof (vrange_sound ρ s x a Hs Hx _ Ex) as Hrx; pose proof (vrange_sound ρ s y b Hs Hy _ Ey) as Hry.
    all: cbn [fst snd] in Hrx, Hry; subst d.
    all: destruct ((xh <? yl) || (yh <? xl)) eqn:E1; [|discriminate]; injection Hm as <-; symmetry; apply Z.eqb_neq.
    all: apply orb_prop in E1 as [E1|E1]; apply Z.ltb_lt in E1; lia. }
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_eq] in H;
    try (apply (Hgen _ eq_refl H)).
  injection H as <-. cbn [aval_val] in *. rewrite Hx, Hy. apply w_eqb_spec.
Qed.

(* [comment removed for export] *)
Definition a_lts (s : store) (x y : aval) : option bool :=
  match x, y with
  | VL a, VL b => Some (w_lts a b)
  | _, _ =>
      match vrange s x, vrange s y with
      | Some (xl, xh), Some (yl, yh) =>
          if (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63) then a_ltu s x y else None
      | _, _ => None
      end
  end.

Lemma bv_signed_small (w : bv 64) : 0 <= bv_unsigned w < two63 -> bv_signed w = bv_unsigned w.
Proof.
  intros H. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with two63. rewrite bv_modulus_64.
  rewrite Z.mod_small by (unfold two63, two64 in *; lia). ring.
Qed.

Lemma a_lts_sound (ρ : valuation) (s : store) (x y : aval) (a b : bv 64) (r : bool) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_lts s x y = Some r -> r = bv_lts a b.
Proof.
  intros Hs Hx Hy H.
  assert (Hgen : (match vrange s x, vrange s y with
                  | Some (xl, xh), Some (yl, yh) =>
                      if (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63) then a_ltu s x y else None
                  | _, _ => None
                  end) = Some r -> r = bv_lts a b).
  { intros Hm. destruct (vrange s x) as [[xl xh]|] eqn:Ex; destruct (vrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    pose proof (vrange_sound ρ s x a Hs Hx _ Ex) as Hrx. pose proof (vrange_sound ρ s y b Hs Hy _ Ey) as Hry.
    cbn [fst snd] in Hrx, Hry.
    destruct ((0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)) eqn:Ec; [|discriminate].
    repeat (apply andb_prop in Ec as [Ec ?]). apply Z.leb_le in Ec.
    rewrite (a_ltu_sound ρ s x y a b r Hs Hx Hy Hm). unfold bv_lts, bv_ltu.
    rewrite !bv_signed_small; [reflexivity | | ]; split; try lia;
      match goal with H : (_ <? two63) = true |- _ => apply Z.ltb_lt in H end; lia. }
  destruct x as [xa|f|lo hi| |m1 v1], y as [yb|g|lo2 hi2| |m2 v2]; cbn [a_lts] in H; try (apply (Hgen H)).
  injection H as <-. apply aval_VL in Hx. apply aval_VL in Hy. subst. apply w_lts_bv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition a_bool (b : option bool) : aval :=
  match b with Some true => VL w_one | Some false => VL w_zero | None => VR 0 1 end.

Definition a_alu64 (s : store) (op : aluop) (x y : aval) : aval :=
  match op with
  | ALU_ADD => a_add s x y
  | ALU_SUB => a_sub s x y
  | ALU_SLL => a_sll' s x y
  | ALU_SLT => a_bool (a_lts s x y)
  | ALU_SLTU => a_bool (a_ltu s x y)
  | ALU_XOR => a_xor s x y
  | ALU_SRL => a_srl' s x y
  | ALU_SRA => a_sra s x y
  | ALU_OR => a_or s x y
  | ALU_AND => a_and s x y
  end.

Lemma a_bool_sound (ρ : valuation) (o : option bool) (c : bool) :
  (forall r, o = Some r -> r = c) -> aval_val ρ (a_bool o) (if c then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros H. destruct o as [[]|]; cbn [a_bool aval_val].
  - rewrite <- (H true eq_refl). reflexivity.
  - rewrite <- (H false eq_refl). reflexivity.
  - destruct c; cbn [aval_val]; [change (bv_unsigned (Z_to_bv 64 1)) with 1 | change (bv_unsigned (Z_to_bv 64 0)) with 0]; lia.
Qed.

Lemma a_alu64_sound (ρ : valuation) (s : store) (op : aluop) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_alu64 s op x y) (alu64 op a b).
Proof.
  intros Hs Hx Hy. unfold alu64, alu. destruct op; cbn [a_alu64].
  - apply a_add_sound; assumption.
  - apply a_sub_sound; assumption.
  - apply a_sll'_sound; assumption.
  - apply a_bool_sound. intros r Hr. exact (a_lts_sound ρ s x y a b r Hs Hx Hy Hr).
  - apply a_bool_sound. intros r Hr. exact (a_ltu_sound ρ s x y a b r Hs Hx Hy Hr).
  - apply a_xor_sound; assumption.
  - apply a_srl'_sound; assumption.
  - apply a_sra_sound; assumption.
  - apply a_or_sound; assumption.
  - apply a_and_sound; assumption.
Qed.

Definition a_muldiv (s : store) (op : mulop) (x y : aval) : aval :=
  match op, x, y with
  | M_MUL, _, _ => a_mul s x y
  | _, VL a, VL b => VL (w_muldiv op a b)
  | _, _, _ => VT
  end.

Lemma a_muldiv_sound (ρ : valuation) (s : store) (op : mulop) (x y : aval) (a b : bv 64) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> aval_val ρ (a_muldiv s op x y) (mul_div op a b).
Proof.
  intros Hs Hx Hy. destruct op; cbn [a_muldiv];
    [ apply a_mul_sound; assumption | .. ];
    (destruct x; try exact I; destruct y; try exact I;
     apply aval_VL in Hx; apply aval_VL in Hy; subst; apply aval_VL; symmetry; apply w_muldiv_ok).
Qed.

(* [comment removed for export] *)

Definition aval_val32 (ρ : valuation) (v : aval) (X : bv 32) : Prop :=
  exists a : bv 64, aval_val ρ v a /\ bv_unsigned X = bv_unsigned a mod two32.

Lemma aval_val32_low32 (ρ : valuation) (v : aval) (a : bv 64) : aval_val ρ v a -> aval_val32 ρ v (low32 a).
Proof.
  intros H. exists a. split; [exact H|]. unfold low32. rewrite bv_extract_unsigned. unfold bv_wrap.
  change (bv_modulus 32) with two32. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma low32_of_VL (ρ : valuation) (x : w64) (X : bv 32) : aval_val32 ρ (VL x) X -> to_Z (w_low32 x) = bv_unsigned X.
Proof. intros [a [Ha HX]]. cbn [aval_val] in Ha. rewrite HX, Ha, phi_low32. reflexivity. Qed.

Definition a_alu32 (s : store) (op : aluop) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sext32 (w_alu32 op (w_low32 a) (w_low32 b)))
  | _, _ => VT
  end.

Lemma a_alu32_sound (ρ : valuation) (s : store) (op : aluop) (x y : aval) (X Y : bv 32) :
  aval_val32 ρ x X -> aval_val32 ρ y Y -> aval_val ρ (a_alu32 s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hx Hy. unfold a_alu32. destruct x as [xa| | | |]; try exact I; destruct y as [yb| | | |]; try exact I.
  apply aval_VL. symmetry. apply w_op32_ok; apply (low32_of_VL ρ); assumption.
Qed.

Definition a_muldiv32 (s : store) (op : mulop) (x y : aval) : aval :=
  match x, y with
  | VL a, VL b => VL (w_sext32 (w_muldiv32 op (w_low32 a) (w_low32 b)))
  | _, _ => VT
  end.

Lemma a_muldiv32_sound (ρ : valuation) (s : store) (op : mulop) (x y : aval) (X Y : bv 32) :
  aval_val32 ρ x X -> aval_val32 ρ y Y -> aval_val ρ (a_muldiv32 s op x y) (sext 64 (mul_div op X Y)).
Proof.
  intros Hx Hy. unfold a_muldiv32. destruct x as [xa| | | |]; try exact I; destruct y as [yb| | | |]; try exact I.
  apply aval_VL. symmetry. apply w_sext32_ok. apply w_muldiv32_ok; apply (low32_of_VL ρ); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition a_branch (s : store) (bc : branch_cond) (x y : aval) : option bool :=
  match bc with
  | BC_EQ => a_eq s x y
  | BC_NE => option_map negb (a_eq s x y)
  | BC_LT => a_lts s x y
  | BC_GE => option_map negb (a_lts s x y)
  | BC_LTU => a_ltu s x y
  | BC_GEU => option_map negb (a_ltu s x y)
  end.

Lemma a_branch_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : aval) (a b : bv 64) (r : bool) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_branch s bc x y = Some r -> r = branch_taken bc a b.
Proof.
  intros Hs Hx Hy H. destruct bc; cbn [a_branch branch_taken] in *.
  - exact (a_eq_sound ρ s x y a b r Hs Hx Hy H).
  - destruct (a_eq s x y) as [r'|] eqn:E; [|discriminate]. injection H as <-.
    rewrite (a_eq_sound ρ s x y a b r' Hs Hx Hy E). reflexivity.
  - exact (a_lts_sound ρ s x y a b r Hs Hx Hy H).
  - destruct (a_lts s x y) as [r'|] eqn:E; [|discriminate]. injection H as <-.
    rewrite (a_lts_sound ρ s x y a b r' Hs Hx Hy E). reflexivity.
  - exact (a_ltu_sound ρ s x y a b r Hs Hx Hy H).
  - destruct (a_ltu s x y) as [r'|] eqn:E; [|discriminate]. injection H as <-.
    rewrite (a_ltu_sound ρ s x y a b r' Hs Hx Hy E). reflexivity.
Qed.

(* [comment removed for export] *)
Definition fk (s : store) (d : lin) (lo hi : Z) (b : bool) : list (store * bool) :=
  match lrange s d with
  | Some (l, h) => let l' := Z.max l lo in let h' := Z.min h hi in
                   if l' <=? h' then [(sadd s d l' h', b)] else []
  | None => [(sadd s d lo hi, b)]
  end.

Lemma fk_in (ρ : valuation) (s : store) (d : lin) (lo hi : Z) (b : bool) :
  sat ρ s -> lo <= leval ρ d <= hi -> exists s', In (s', b) (fk s d lo hi b) /\ sat ρ s'.
Proof.
  intros Hs Hd. unfold fk. destruct (lrange s d) as [[l h]|] eqn:E.
  - pose proof (lrange_sound ρ s d Hs _ E) as Hr. cbn [fst snd] in Hr.
    destruct (Z.max l lo <=? Z.min h hi) eqn:Ec.
    + eexists. split; [left; reflexivity|]. apply sat_sadd; [exact Hs | lia].
    + apply Z.leb_gt in Ec. lia.
  - eexists. split; [left; reflexivity|]. apply sat_sadd; [exact Hs | lia].
Qed.

Definition a_fork (s : store) (bc : branch_cond) (x y : aval) : option (list (store * bool)) :=
  match vform x, vform y with
  | Some f, Some g =>
      let d := lsub f g in
      let lt := fk s d (- two64) (-1) true ++ fk s d 0 two64 false in
      let eq := fk s d 0 0 true ++ fk s d (- two64) (-1) false ++ fk s d 1 two64 false in
      let small := match vrange s x, vrange s y with
                   | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
                   | _, _ => false
                   end in
      match bc with
      | BC_LTU => Some lt
      | BC_GEU => Some (map (fun p => (fst p, negb (snd p))) lt)
      | BC_LT => if small then Some lt else None
      | BC_GE => if small then Some (map (fun p => (fst p, negb (snd p))) lt) else None
      | BC_EQ => Some eq
      | BC_NE => Some (map (fun p => (fst p, negb (snd p))) eq)
      end
  | _, _ => None
  end.

Lemma a_fork_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : aval) (a b : bv 64) (l : list (store * bool)) :
  sat ρ s -> aval_val ρ x a -> aval_val ρ y b -> a_fork s bc x y = Some l ->
  exists s' r, In (s', r) l /\ sat ρ s' /\ r = branch_taken bc a b.
Proof.
  intros Hs Hx Hy H. unfold a_fork in H.
  destruct (vform x) as [f|] eqn:Ef; [|discriminate]. destruct (vform y) as [g|] eqn:Eg; [|discriminate].
  pose proof (vform_sound ρ x a f Hx Ef) as Hf. pose proof (vform_sound ρ y b g Hy Eg) as Hg.
  pose proof (bvu_range a) as Ha. pose proof (bvu_range b) as Hb.
  set (d := lsub f g) in *.
  assert (Hd : leval ρ d = bv_unsigned a - bv_unsigned b) by (unfold d; rewrite leval_lsub, Hf, Hg; reflexivity).
  assert (Hlt : exists s' r, In (s', r) (fk s d (- two64) (-1) true ++ fk s d 0 two64 false) /\ sat ρ s' /\ r = bv_ltu a b).
  { unfold bv_ltu. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b)).
    - destruct (fk_in ρ s d (- two64) (-1) true Hs ltac:(unfold two64 in *; lia)) as [s' [Hi Hs']].
      exists s', true. split; [apply in_or_app; left; exact Hi|]. split; [exact Hs' | reflexivity].
    - destruct (fk_in ρ s d 0 two64 false Hs ltac:(unfold two64 in *; lia)) as [s' [Hi Hs']].
      exists s', false. split; [apply in_or_app; right; exact Hi|]. split; [exact Hs' | reflexivity]. }
  assert (Heq : exists s' r, In (s', r) (fk s d 0 0 true ++ fk s d (- two64) (-1) false ++ fk s d 1 two64 false)
                             /\ sat ρ s' /\ r = bv_eqb a b).
  { unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)).
    - destruct (fk_in ρ s d 0 0 true Hs ltac:(unfold two64 in *; lia)) as [s' [Hi Hs']].
      exists s', true. split; [apply in_or_app; left; exact Hi|]. split; [exact Hs' | reflexivity].
    - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned b)).
      + destruct (fk_in ρ s d (- two64) (-1) false Hs ltac:(unfold two64 in *; lia)) as [s' [Hi Hs']].
        exists s', false. split; [apply in_or_app; right; apply in_or_app; left; exact Hi|]. split; [exact Hs' | reflexivity].
      + destruct (fk_in ρ s d 1 two64 false Hs ltac:(unfold two64 in *; lia)) as [s' [Hi Hs']].
        exists s', false. split; [apply in_or_app; right; apply in_or_app; right; exact Hi|]. split; [exact Hs' | reflexivity]. }
  assert (Hneg : forall (l0 : list (store * bool)) c, (exists s' r, In (s', r) l0 /\ sat ρ s' /\ r = c) ->
            exists s' r, In (s', r) (map (fun p => (fst p, negb (snd p))) l0) /\ sat ρ s' /\ r = negb c).
  { intros l0 c [s' [r [Hi [Hsat Hr]]]]. exists s', (negb r). split; [|split; [exact Hsat | rewrite Hr; reflexivity]].
    apply in_map_iff. exists (s', r). split; [reflexivity | exact Hi]. }
  assert (Hsmall : forall (l0 : list (store * bool)),
            (match vrange s x, vrange s y with
             | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
             | _, _ => false
             end) = true -> bv_lts a b = bv_ltu a b).
  { intros l0 Hc. destruct (vrange s x) as [[xl xh]|] eqn:Ex; destruct (vrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    pose proof (vrange_sound ρ s x a Hs Hx _ Ex). pose proof (vrange_sound ρ s y b Hs Hy _ Ey). cbn [fst snd] in *.
    repeat (apply andb_prop in Hc as [Hc ?]). apply Z.leb_le in Hc.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
    unfold bv_lts, bv_ltu. rewrite !bv_signed_small by lia. reflexivity. }
  set (small := match vrange s x, vrange s y with
                 | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
                 | _, _ => false
                 end) in *.
  destruct bc; cbn [branch_taken].
  - injection H as <-. exact Heq.
  - injection H as <-. exact (Hneg _ _ Heq).
  - destruct small eqn:Ec; [|discriminate]. injection H as <-. rewrite (Hsmall [] eq_refl). exact Hlt.
  - destruct small eqn:Ec; [|discriminate]. injection H as <-. rewrite (Hsmall [] eq_refl).
    exact (Hneg _ _ Hlt).
  - injection H as <-. exact Hlt.
  - injection H as <-. exact (Hneg _ _ Hlt).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sext64_32 (X : bv 32) :
  bv_unsigned (sext 64 X) = if bv_unsigned X <? 2 ^ 31 then bv_unsigned X else bv_unsigned X + two64 - 2 ^ 32.
Proof.
  unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  pose proof (bv_unsigned_in_range 32 X) as HX. change (bv_modulus 32) with (2 ^ 32) in *. change (bv_modulus 64) with two64.
  change (bv_half_modulus 32) with (2 ^ 31). unfold two64.
  destruct (Z.ltb_spec (bv_unsigned X) (2 ^ 31)).
  - rewrite (Z.mod_small (bv_unsigned X + 2 ^ 31)) by lia.
    replace (bv_unsigned X + 2 ^ 31 - 2 ^ 31) with (bv_unsigned X) by ring. apply Z.mod_small. lia.
  - replace (bv_unsigned X + 2 ^ 31) with ((bv_unsigned X - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (bv_unsigned X - 2 ^ 31) (2 ^ 32)) by lia.
    replace (bv_unsigned X - 2 ^ 31 - 2 ^ 31) with ((bv_unsigned X + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Definition two31 : Z := 2147483648.

Lemma mod_neg_add (a m : Z) : 0 < m -> - m <= a < 0 -> a mod m = a + m.
Proof.
  intros Hm Ha. replace a with ((a + m) + (-1) * m) at 1 by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Definition a_alu32' (s : store) (op : aluop) (x y : aval) : aval :=
  match a_alu32 s op x y with
  | VT =>
      match op with
      | ALU_ADD | ALU_SUB =>
          match vform x, vform y with
          | Some f, Some g =>
              let d := match op with ALU_ADD => ladd f g | _ => lsub f g end in
              match lrange s d with
              | Some (lo, hi) => if (0 <=? lo) && (hi <? two31) then mk_vs s d
                                 else if (- two31 <=? lo) && (hi <? 0) then mk_vs s (laddc d two64) else VT
              | None => VT
              end
          | _, _ => VT
          end
      | ALU_SRL =>
          match y with
          | VL b => let k := to_Z (w_low32 b) mod 32 in
                    if 1 <=? k then
                      match tok s x with
                      | Some (m, v) => mkvk (Z.lor (Z.shiftr (m mod two32) k) (two64 - 2 ^ (32 - k))) (Z.shiftr (v mod two32) k)
                      | None => VT
                      end
                    else VT
          | _ => VT
          end
      | _ => VT
      end
  | r => r
  end.

Lemma a_alu32'_sound (ρ : valuation) (s : store) (op : aluop) (x y : aval) (X Y : bv 32) :
  sat ρ s -> aval_val32 ρ x X -> aval_val32 ρ y Y -> aval_val ρ (a_alu32' s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs Hx Hy. unfold a_alu32'. pose proof (a_alu32_sound ρ s op x y X Y Hx Hy) as H0.
  destruct (a_alu32 s op x y) eqn:E; try exact H0.
  destruct Hx as [a [Ha HX]]. destruct Hy as [b [Hb HY]].
  assert (Hsum : forall d : lin, (lrange s d = None -> False) -> True) by (intros; exact I).
  destruct op; try exact I.
  - (* [comment removed for export] *)
    destruct (vform x) as [f|] eqn:Ef; [|exact I]. destruct (vform y) as [g|] eqn:Eg; [|exact I].
    pose proof (vform_sound ρ x a f Ha Ef) as Haf. pose proof (vform_sound ρ y b g Hb Eg) as Hbg.
    destruct (lrange s (ladd f g)) as [[lo hi]|] eqn:Er; [|exact I].
    pose proof (lrange_sound ρ s _ Hs _ Er) as Hr. cbn [fst snd] in Hr. rewrite leval_ladd in Hr.
    assert (HZ : bv_unsigned (alu32 ALU_ADD X Y) = (leval ρ f + leval ρ g) mod 2 ^ 32).
    { unfold alu32, alu. rewrite bv_add_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). unfold two32.
      rewrite <- Haf, <- Hbg. change (2 ^ 32) with 4294967296. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity. }
    destruct ((0 <=? lo) && (hi <? two31)) eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply mk_vs_sound; [exact Hs|].
      rewrite sext64_32, HZ, leval_ladd. unfold two31, two64 in *. rewrite Z.mod_small by lia.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.mod_small; [reflexivity | lia].
    + destruct ((- two31 <=? lo) && (hi <? 0)) eqn:E2; [|exact I].
      apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply mk_vs_sound; [exact Hs|].
      rewrite sext64_32, HZ, leval_laddc, leval_ladd. unfold two31, two64 in *.
      rewrite mod_neg_add by lia.
      rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Z.mod_small by lia. ring.
  - (* [comment removed for export] *)
    destruct (vform x) as [f|] eqn:Ef; [|exact I]. destruct (vform y) as [g|] eqn:Eg; [|exact I].
    pose proof (vform_sound ρ x a f Ha Ef) as Haf. pose proof (vform_sound ρ y b g Hb Eg) as Hbg.
    destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:Er; [|exact I].
    pose proof (lrange_sound ρ s _ Hs _ Er) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub in Hr.
    assert (HZ : bv_unsigned (alu32 ALU_SUB X Y) = (leval ρ f - leval ρ g) mod 2 ^ 32).
    { unfold alu32, alu. rewrite bv_sub_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). unfold two32.
      rewrite <- Haf, <- Hbg. change (2 ^ 32) with 4294967296. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity. }
    destruct ((0 <=? lo) && (hi <? two31)) eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply mk_vs_sound; [exact Hs|].
      rewrite sext64_32, HZ, leval_lsub. unfold two31, two64 in *. rewrite Z.mod_small by lia.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.mod_small; [reflexivity | lia].
    + destruct ((- two31 <=? lo) && (hi <? 0)) eqn:E2; [|exact I].
      apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply mk_vs_sound; [exact Hs|].
      rewrite sext64_32, HZ, leval_laddc, leval_lsub. unfold two31, two64 in *.
      rewrite mod_neg_add by lia.
      rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Z.mod_small by lia. ring.
  - (* [comment removed for export] *)
    destruct y as [yb| | | |]; try exact I. cbn [aval_val] in Hb.
    destruct (1 <=? to_Z (w_low32 yb) mod 32) eqn:Ek; [|exact I]. apply Z.leb_le in Ek.
    destruct (tok s x) as [[m v]|] eqn:Et; [|exact I].
    pose proof (tok_sound ρ s x a m v Hs Ha Et) as Hkb.
    set (k := to_Z (w_low32 yb) mod 32) in *.
    assert (Hk : 0 <= k < 32) by (unfold k; apply Z.mod_pos_bound; lia).
    assert (HYk : bv_unsigned (bv_and Y (Z_to_bv 32 31)) = k).
    { rewrite bv_and_unsigned, HY, Z_to_bv_unsigned. change (bv_wrap 32 31) with (Z.ones 5). rewrite Z.land_ones by lia.
      unfold k. rewrite phi_low32, Hb. change (2 ^ 5) with 32. reflexivity. }
    assert (HZ : bv_unsigned (alu32 ALU_SRL X Y) = Z.shiftr (bv_unsigned X) k).
    { unfold alu32, alu. rewrite bv_shiftr_unsigned, HYk. reflexivity. }
    pose proof (bv_unsigned_in_range 32 X) as HXr. change (bv_modulus 32) with (2 ^ 32) in HXr.
    apply mkvk_sound. rewrite sext64_32, HZ.
    assert (Hsm : Z.shiftr (bv_unsigned X) k < 2 ^ 31).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      apply Z.lt_le_trans with (2 ^ 32); [lia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
    rewrite (proj2 (Z.ltb_lt _ _)) by exact Hsm.
    assert (HXm : Z.land (bv_unsigned X) (m mod two32) = v mod two32).
    { rewrite HX. unfold two32. change 4294967296 with (2 ^ 32). rewrite <- !Z.land_ones by lia. rewrite <- Hkb.
      apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec. destruct (Z.testbit (bv_unsigned a) i), (Z.testbit m i), (Z.testbit (Z.ones 32) i); reflexivity. }
    apply (kb_srl_sound (bv_unsigned X) (m mod two32) (v mod two32) k 32 HXm); lia.
Qed.
