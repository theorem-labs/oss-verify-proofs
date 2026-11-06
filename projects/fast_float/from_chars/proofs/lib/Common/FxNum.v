(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import PrimInt63 Uint63Axioms Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition i0 : int := 0%uint63.
Definition i1 : int := 1%uint63.
Definition i4 : int := 4%uint63.
Definition i65 : int := 65%uint63.
Definition B60 : int := 1152921504606846976%uint63.
Definition B61 : int := 2305843009213693952%uint63.
Definition B62 : int := 4611686018427387904%uint63.
Definition NB60 : int := 3458764513820540928%uint63.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ival (x : int) : Z := let z := to_Z x in if Z.ltb z 4611686018427387904 then z else z - 9223372036854775808.
Definition smallb (r : int) : bool := PrimInt63.ltb (PrimInt63.add r B61) B62.             (* [comment removed for export] *)
Definition iabs (x : int) : int := if PrimInt63.leb B62 x then PrimInt63.sub i0 x else x.  (* [comment removed for export] *)
Definition slt (x y : int) : bool := PrimInt63.ltb (PrimInt63.add x B62) (PrimInt63.add y B62). (* [comment removed for export] *)
Definition wlt (a1 b1 a2 b2 : int) : bool := if PrimInt63.eqb b1 b2 then slt a1 a2 else slt b1 b2.
Definition imin (x y : int) : int := if PrimInt63.ltb x y then x else y.
Definition wv (a b : int) : Z := ival a + ival b * 4611686018427387904.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint p2i (p : positive) (w acc : int) : int * option positive :=
  if PrimInt63.eqb w B62 then (acc, Some p) else
  match p with
  | xH => (PrimInt63.add acc w, None)
  | xO q => p2i q (PrimInt63.add w w) acc
  | xI q => p2i q (PrimInt63.add w w) (PrimInt63.add acc w)
  end.
(* [comment removed for export] *)
Fixpoint p2i2 (p : positive) (w acc : int) : int * option positive :=
  if PrimInt63.eqb w B62 then (acc, Some p) else
  match p with
  | xH => (PrimInt63.add acc w, None)
  | xO xH => (PrimInt63.add acc (PrimInt63.add w w), None)
  | xI xH => (PrimInt63.add acc (PrimInt63.add w (PrimInt63.add w w)), None)
  | xO (xO q) => let w2 := PrimInt63.add w w in p2i2 q (PrimInt63.add w2 w2) acc
  | xI (xO q) => let w2 := PrimInt63.add w w in p2i2 q (PrimInt63.add w2 w2) (PrimInt63.add acc w)
  | xO (xI q) => let w2 := PrimInt63.add w w in p2i2 q (PrimInt63.add w2 w2) (PrimInt63.add acc w2)
  | xI (xI q) => let w2 := PrimInt63.add w w in p2i2 q (PrimInt63.add w2 w2) (PrimInt63.add acc (PrimInt63.add w w2))
  end.
(* [comment removed for export] *)
Definition k2c (k : Z) : option int :=
  match k with
  | Z0 => Some i0
  | Zpos p => match p2i2 p i1 i0 with
              | (a, None) => if PrimInt63.ltb a B60 then Some a else None
              | (a, Some (xI xH)) => if PrimInt63.ltb NB60 a then Some (PrimInt63.sub a B62) else None
              | _ => None
              end
  | Zneg _ => None
  end.
Definition p2w (p : positive) : option (int * int) :=
  match p2i2 p i1 i0 with
  | (a, None) => if PrimInt63.ltb a B61 then Some (a, i0) else Some (PrimInt63.sub a B62, i1)
  | (a, Some q) => match p2i2 q i1 i0 with
                   | (b, None) => if PrimInt63.ltb a B61 then (if smallb b then Some (a, b) else None)
                                  else let b' := PrimInt63.add b i1 in if smallb b' then Some (PrimInt63.sub a B62, b') else None
                   | _ => None
                   end
  end.
Definition z2w (z : Z) : option (int * int) :=
  match z with
  | Z0 => Some (i0, i0)
  | Zpos p => p2w p
  | Zneg p => match p2w p with
              | Some (a, b) => let a' := PrimInt63.sub i0 a in let b' := PrimInt63.sub i0 b in
                               if smallb a' then (if smallb b' then Some (a', b') else None) else None
              | None => None
              end
  end.

(* [comment removed for export] *)
Record wiv : Type := WI { w_al : int; w_bl : int; w_ah : int; w_bh : int }.
Definition wiv2z (r : wiv) : Z * Z := (wv (w_al r) (w_bl r), wv (w_ah r) (w_bh r)).
(* [comment removed for export] *)
Record ventry : Type := VE { v_al : int; v_bl : int; v_ah : int; v_bh : int; v_h : int }.
Definition mk_ve (r : Z * Z) : option ventry :=
  match z2w (fst r), z2w (snd r) with
  | Some (al, bl), Some (ah, bh) =>
      Some (VE al bl ah bh (imin (imin (PrimInt63.head0 (iabs al)) (PrimInt63.head0 (iabs bl))) (imin (PrimInt63.head0 (iabs ah)) (PrimInt63.head0 (iabs bh)))))
  | _, _ => None
  end.
Record cterm : Type := CT { ct_x : positive; ct_c : int; ct_e : ventry }.
Record clin : Type := CL { cl_c : int; cl_t : list cterm }.

(* [comment removed for export] *)
Fixpoint ct_add (a : list cterm) : list cterm -> list cterm :=
  match a with
  | [] => fun b => b
  | ta :: a' =>
      fix go (b : list cterm) : list cterm :=
        match b with
        | [] => a
        | tb :: b' =>
            match Pos.compare (ct_x ta) (ct_x tb) with
            | Eq => let k := PrimInt63.add (ct_c ta) (ct_c tb) in if PrimInt63.eqb k i0 then ct_add a' b' else CT (ct_x ta) k (ct_e ta) :: ct_add a' b'
            | Lt => ta :: ct_add a' b
            | Gt => tb :: go b'
            end
        end
  end.
(* [comment removed for export] *)
Fixpoint ct_neg (t : list cterm) : list cterm :=
  match t with
  | [] => []
  | tb :: t' => if PrimInt63.eqb (ct_c tb) i0 then ct_neg t' else CT (ct_x tb) (PrimInt63.sub i0 (ct_c tb)) (ct_e tb) :: ct_neg t'
  end.
(* [comment removed for export] *)
Fixpoint ct_iv (t : list cterm) (al bl ah bh : int) : option wiv :=
  match t with
  | [] => Some (WI al bl ah bh)
  | CT _ c e :: t' =>
      if PrimInt63.leb i65 (PrimInt63.add (PrimInt63.head0 (iabs c)) (v_h e)) then
        let neg := PrimInt63.leb B62 c in
        let al' := PrimInt63.add al (PrimInt63.mul c (if neg then v_ah e else v_al e)) in
        let bl' := PrimInt63.add bl (PrimInt63.mul c (if neg then v_bh e else v_bl e)) in
        let ah' := PrimInt63.add ah (PrimInt63.mul c (if neg then v_al e else v_ah e)) in
        let bh' := PrimInt63.add bh (PrimInt63.mul c (if neg then v_bl e else v_bh e)) in
        if smallb al' then if smallb bl' then if smallb ah' then if smallb bh' then ct_iv t' al' bl' ah' bh'
        else None else None else None else None
      else None
  end.
(* [comment removed for export] *)
Definition wmeet_win (acc c : wiv) : option wiv :=
  let '(WI aal abl aah abh) := acc in
  let '(WI cal cbl cah cbh) := c in
  let hi_c := wlt aah abh cah cbh in      (* [comment removed for export] *)
  let lo_c := wlt cal cbl aal abl in      (* [comment removed for export] *)
  let mah := if hi_c then cah else aah in let mbh := if hi_c then cbh else abh in
  let mal := if lo_c then cal else aal in let mbl := if lo_c then cbl else abl in
  let da := PrimInt63.sub mah mal in let db := PrimInt63.sub mbh mbl in
  if smallb da then if smallb db then
    if wlt da db i0 i4 then
      Some (WI (if lo_c then aal else cal) (if lo_c then abl else cbl) (if hi_c then aah else cah) (if hi_c then abh else cbh))
    else
      let wca := PrimInt63.sub cah cal in let wcb := PrimInt63.sub cbh cbl in
      let waa := PrimInt63.sub aah aal in let wab := PrimInt63.sub abh abl in
      if smallb wca then if smallb wcb then if smallb waa then if smallb wab then
        Some (if wlt wca wcb waa wab then c else acc)
      else None else None else None else None
  else None else None.

(* [comment removed for export] *)
Definition cl_iv (cl : clin) : option wiv := ct_iv (cl_t cl) (cl_c cl) i0 (cl_c cl) i0.
(* [comment removed for export] *)
Definition wstep_iv (cl cg : clin) (loa lob hia hib : int) (acc : wiv) : option wiv :=
  let c1 := PrimInt63.sub (cl_c cl) (cl_c cg) in let c2 := PrimInt63.add (cl_c cl) (cl_c cg) in
  match ct_iv (ct_add (cl_t cl) (ct_neg (cl_t cg))) c1 i0 c1 i0 with
  | None => None
  | Some r1 =>
      match ct_iv (ct_add (cl_t cl) (cl_t cg)) c2 i0 c2 i0 with
      | None => None
      | Some r2 =>
          let w1al := PrimInt63.add loa (w_al r1) in let w1bl := PrimInt63.add lob (w_bl r1) in
          let w1ah := PrimInt63.add hia (w_ah r1) in let w1bh := PrimInt63.add hib (w_bh r1) in
          let w2al := PrimInt63.sub (w_al r2) hia in let w2bl := PrimInt63.sub (w_bl r2) hib in
          let w2ah := PrimInt63.sub (w_ah r2) loa in let w2bh := PrimInt63.sub (w_bh r2) lob in
          if smallb w1al then if smallb w1bl then if smallb w1ah then if smallb w1bh then
          if smallb w2al then if smallb w2bl then if smallb w2ah then if smallb w2bh then
            match wmeet_win acc (WI w1al w1bl w1ah w1bh) with
            | None => None
            | Some acc1 => wmeet_win acc1 (WI w2al w2bl w2ah w2bh)
            end
          else None else None else None else None else None else None else None else None
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition small (x : int) : Prop := -2305843009213693952 <= ival x < 2305843009213693952.

Lemma to_Z_i0 : to_Z i0 = 0. Proof. reflexivity. Qed.
Lemma to_Z_i1 : to_Z i1 = 1. Proof. reflexivity. Qed.
Lemma to_Z_i4 : to_Z i4 = 4. Proof. reflexivity. Qed.
Lemma to_Z_i65 : to_Z i65 = 65. Proof. reflexivity. Qed.
Lemma to_Z_B60 : to_Z B60 = 1152921504606846976. Proof. reflexivity. Qed.
Lemma to_Z_B61 : to_Z B61 = 2305843009213693952. Proof. reflexivity. Qed.
Lemma to_Z_B62 : to_Z B62 = 4611686018427387904. Proof. reflexivity. Qed.
Lemma to_Z_NB60 : to_Z NB60 = 3458764513820540928. Proof. reflexivity. Qed.
Lemma wB_eq : wB = 9223372036854775808. Proof. reflexivity. Qed.
Lemma to_Z_rng : forall x, 0 <= to_Z x < 9223372036854775808.
Proof. intros x. pose proof (to_Z_bounded x) as H. rewrite wB_eq in H. exact H. Qed.

Lemma mod63_pos : forall z, 0 <= z < 9223372036854775808 -> z mod 9223372036854775808 = z.
Proof. intros z H. apply Z.mod_small. exact H. Qed.
Lemma mod63_neg : forall z, -9223372036854775808 <= z < 0 -> z mod 9223372036854775808 = z + 9223372036854775808.
Proof.
  intros z H. rewrite <- (Z.mod_small (z + 9223372036854775808) 9223372036854775808) by lia.
  replace (z + 9223372036854775808) with (z + 1 * 9223372036854775808) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma ival_range : forall x, -4611686018427387904 <= ival x < 4611686018427387904.
Proof. intros x. unfold ival. pose proof (to_Z_rng x). destruct (Z.ltb_spec (to_Z x) 4611686018427387904); lia. Qed.
Lemma to_Z_ival : forall x, to_Z x = ival x mod 9223372036854775808.
Proof.
  intros x. unfold ival. pose proof (to_Z_rng x). destruct (Z.ltb_spec (to_Z x) 4611686018427387904).
  - rewrite mod63_pos by lia. reflexivity.
  - rewrite mod63_neg by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma ival_intro : forall x z, -4611686018427387904 <= z < 4611686018427387904 -> to_Z x = z mod 9223372036854775808 -> ival x = z.
Proof.
  intros x z Hz H. unfold ival. destruct (Z.leb_spec 0 z).
  - rewrite mod63_pos in H by lia. rewrite H. destruct (Z.ltb_spec z 4611686018427387904); lia.
  - rewrite mod63_neg in H by lia. rewrite H. destruct (Z.ltb_spec (z + 9223372036854775808) 4611686018427387904); lia.
Qed.
Lemma ival_inj : forall x y, ival x = ival y -> x = y.
Proof. intros x y H. apply to_Z_inj. rewrite (to_Z_ival x), (to_Z_ival y), H. reflexivity. Qed.

Lemma ival_add : forall x y, -4611686018427387904 <= ival x + ival y < 4611686018427387904 -> ival (PrimInt63.add x y) = ival x + ival y.
Proof.
  intros x y H. apply ival_intro; [exact H|]. rewrite add_spec, wB_eq, (to_Z_ival x), (to_Z_ival y).
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma ival_sub : forall x y, -4611686018427387904 <= ival x - ival y < 4611686018427387904 -> ival (PrimInt63.sub x y) = ival x - ival y.
Proof.
  intros x y H. apply ival_intro; [exact H|]. rewrite sub_spec, wB_eq, (to_Z_ival x), (to_Z_ival y).
  rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma ival_mul : forall x y, -4611686018427387904 <= ival x * ival y < 4611686018427387904 -> ival (PrimInt63.mul x y) = ival x * ival y.
Proof.
  intros x y H. apply ival_intro; [exact H|]. rewrite mul_spec, wB_eq, (to_Z_ival x), (to_Z_ival y).
  rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma ival_i0 : ival i0 = 0. Proof. reflexivity. Qed.
Lemma ival_i1 : ival i1 = 1. Proof. reflexivity. Qed.
Lemma ival_i4 : ival i4 = 4. Proof. reflexivity. Qed.
Lemma ival_nonneg : forall x, to_Z x < 4611686018427387904 -> ival x = to_Z x.
Proof. intros x H. unfold ival. destruct (Z.ltb_spec (to_Z x) 4611686018427387904); lia. Qed.

Lemma smallb_spec : forall r, smallb r = true <-> small r.
Proof.
  intros r. unfold smallb, small. rewrite ltb_spec, add_spec, wB_eq, to_Z_B61, to_Z_B62, (to_Z_ival r).
  pose proof (ival_range r) as Hr. rewrite <- (Z.mod_small 2305843009213693952 9223372036854775808) at 1 by lia.
  rewrite <- Z.add_mod by lia.
  destruct (Z.leb_spec 0 (ival r + 2305843009213693952)).
  - rewrite mod63_pos by lia. lia.
  - rewrite mod63_neg by lia. lia.
Qed.
Lemma smallb_true : forall r, smallb r = true -> small r.
Proof. intros r H. apply smallb_spec. exact H. Qed.
Lemma small_range : forall x, small x -> -4611686018427387904 <= ival x < 4611686018427387904.
Proof. unfold small. intros; lia. Qed.

Lemma addB62 : forall x, to_Z (PrimInt63.add x B62) = ival x + 4611686018427387904.
Proof.
  intros x. rewrite add_spec, wB_eq, to_Z_B62, (to_Z_ival x). pose proof (ival_range x).
  rewrite <- (Z.mod_small 4611686018427387904 9223372036854775808) at 1 by lia. rewrite <- Z.add_mod by lia.
  apply mod63_pos. lia.
Qed.
Lemma slt_spec : forall x y, slt x y = true <-> ival x < ival y.
Proof. intros x y. unfold slt. rewrite ltb_spec, !addB62. lia. Qed.
Lemma slt_false : forall x y, slt x y = false <-> ival y <= ival x.
Proof. intros x y. destruct (slt x y) eqn:E; split; intros H; try discriminate; try reflexivity.
  - apply slt_spec in E. lia.
  - destruct (Z.lt_ge_cases (ival x) (ival y)) as [H'|H']; [apply slt_spec in H'; congruence | exact H'].
Qed.

Lemma wlt_spec : forall a1 b1 a2 b2, small a1 -> small a2 -> (wlt a1 b1 a2 b2 = true <-> wv a1 b1 < wv a2 b2).
Proof.
  intros a1 b1 a2 b2 H1 H2. unfold wlt, wv, small in *. destruct (PrimInt63.eqb b1 b2) eqn:E.
  - apply eqb_correct in E. subst b2. rewrite slt_spec. lia.
  - assert (Hne : ival b1 <> ival b2). { intros Hs. apply ival_inj in Hs. subst b2. rewrite eqb_refl in E. discriminate. }
    rewrite slt_spec. split; intros H.
    + assert (ival b1 + 1 <= ival b2) by lia. nia.
    + destruct (Z.lt_ge_cases (ival b1) (ival b2)) as [Hl|Hl]; [exact Hl|]. assert (ival b2 + 1 <= ival b1) by lia. nia.
Qed.
Lemma wlt_false : forall a1 b1 a2 b2, small a1 -> small a2 -> (wlt a1 b1 a2 b2 = false <-> wv a2 b2 <= wv a1 b1).
Proof.
  intros a1 b1 a2 b2 H1 H2. pose proof (wlt_spec a1 b1 a2 b2 H1 H2) as H. destruct (wlt a1 b1 a2 b2); split; intros H'; try discriminate; try reflexivity.
  - destruct H as [H _]. specialize (H eq_refl). lia.
  - destruct (Z.lt_ge_cases (wv a1 b1) (wv a2 b2)) as [Hl|Hl]; [apply H in Hl; discriminate | exact Hl].
Qed.

Lemma iabs_spec : forall x, to_Z (iabs x) = Z.abs (ival x).
Proof.
  intros x. unfold iabs. pose proof (to_Z_rng x). destruct (PrimInt63.leb B62 x) eqn:E.
  - apply leb_spec in E. rewrite to_Z_B62 in E. rewrite sub_spec, to_Z_i0, wB_eq.
    unfold ival. destruct (Z.ltb_spec (to_Z x) 4611686018427387904); [lia|]. rewrite mod63_neg by lia. lia.
  - assert (to_Z x < 4611686018427387904). { destruct (Z.lt_ge_cases (to_Z x) 4611686018427387904) as [H'|H']; [exact H'|].
      assert (PrimInt63.leb B62 x = true) by (apply leb_spec; rewrite to_Z_B62; lia). congruence. }
    rewrite ival_nonneg by lia. lia.
Qed.

Lemma head0_le63 : forall x, to_Z (PrimInt63.head0 x) <= 63.
Proof.
  intros x. destruct (Z.eq_dec (to_Z x) 0) as [H0|H0].
  - rewrite (head00_spec x H0). reflexivity.
  - pose proof (to_Z_rng x) as Hx. pose proof (head0_spec x ltac:(lia)) as [_ Hs]. rewrite wB_eq in Hs.
    pose proof (to_Z_rng (PrimInt63.head0 x)).
    destruct (Z.le_gt_cases (to_Z (PrimInt63.head0 x)) 63) as [Hl|Hl]; [exact Hl|].
    assert (2 ^ 63 <= 2 ^ to_Z (PrimInt63.head0 x)) by (apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma head0_lt : forall x, to_Z x < 2 ^ (63 - to_Z (PrimInt63.head0 x)).
Proof.
  intros x. pose proof (head0_le63 x) as Hh. pose proof (to_Z_rng (PrimInt63.head0 x)) as Hh0.
  destruct (Z.eq_dec (to_Z x) 0) as [H0|H0].
  - rewrite H0. apply Z.pow_pos_nonneg; lia.
  - pose proof (to_Z_rng x) as Hx. pose proof (head0_spec x ltac:(lia)) as [_ H]. rewrite wB_eq in H.
    assert (E : 9223372036854775808 = 2 ^ to_Z (PrimInt63.head0 x) * 2 ^ (63 - to_Z (PrimInt63.head0 x))).
    { rewrite <- Z.pow_add_r by lia. replace (to_Z (PrimInt63.head0 x) + (63 - to_Z (PrimInt63.head0 x))) with 63 by lia. reflexivity. }
    rewrite E in H. assert (0 < 2 ^ to_Z (PrimInt63.head0 x)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
(* [comment removed for export] *)
Lemma mul_guard : forall c v h,
  to_Z h <= to_Z (PrimInt63.head0 (iabs v)) -> PrimInt63.leb i65 (PrimInt63.add (PrimInt63.head0 (iabs c)) h) = true ->
  -2305843009213693952 < ival c * ival v < 2305843009213693952.
Proof.
  intros c v h Hh Hg. apply leb_spec in Hg. rewrite to_Z_i65, add_spec, wB_eq in Hg.
  pose proof (head0_le63 (iabs c)) as Hc63. pose proof (head0_le63 (iabs v)) as Hv63.
  pose proof (to_Z_rng (PrimInt63.head0 (iabs c))). pose proof (to_Z_rng h).
  rewrite mod63_pos in Hg by lia.
  pose proof (head0_lt (iabs c)) as Hc. pose proof (head0_lt (iabs v)) as Hv. rewrite iabs_spec in Hc, Hv.
  set (hc := to_Z (PrimInt63.head0 (iabs c))) in *. set (hv := to_Z (PrimInt63.head0 (iabs v))) in *.
  assert (Hv' : Z.abs (ival v) < 2 ^ (63 - to_Z h)).
  { eapply Z.lt_le_trans; [exact Hv|]. apply Z.pow_le_mono_r; lia. }
  assert (HP : 2 ^ (63 - hc) * 2 ^ (63 - to_Z h) <= 2305843009213693952).
  { rewrite <- Z.pow_add_r by lia. change 2305843009213693952 with (2 ^ 61). apply Z.pow_le_mono_r; lia. }
  assert (HA : Z.abs (ival c * ival v) < 2305843009213693952).
  { rewrite Z.abs_mul. assert (0 <= Z.abs (ival c)) by lia. assert (0 <= Z.abs (ival v)) by lia.
    assert (Z.abs (ival c) * Z.abs (ival v) < 2 ^ (63 - hc) * 2 ^ (63 - to_Z h)).
    { apply Z.mul_lt_mono_nonneg; lia. }
    lia. }
  lia.
Qed.

Lemma imin_le : forall x y, to_Z (imin x y) <= to_Z x /\ to_Z (imin x y) <= to_Z y.
Proof. intros x y. unfold imin. destruct (PrimInt63.ltb x y) eqn:E; [apply ltb_spec in E | ]; split; try lia.
  destruct (Z.lt_ge_cases (to_Z y) (to_Z x)) as [H|H]; [lia|]. destruct (Z.eq_dec (to_Z x) (to_Z y)); [lia|].
  assert (PrimInt63.ltb x y = true) by (apply ltb_spec; lia). congruence.
Qed.

(* [comment removed for export] *)
Lemma p2i_spec : forall p w acc j, to_Z w = 2 ^ j -> 0 <= j <= 62 -> 0 <= to_Z acc < to_Z w ->
  match p2i p w acc with
  | (a, None) => to_Z a = to_Z acc + to_Z w * Zpos p /\ to_Z a < 4611686018427387904
  | (a, Some q) => to_Z acc + to_Z w * Zpos p = to_Z a + 4611686018427387904 * Zpos q /\ to_Z a < 4611686018427387904
  end.
Proof.
  induction p as [q IH|q IH|]; intros w acc j Hw Hj Ha; cbn [p2i];
    (destruct (PrimInt63.eqb w B62) eqn:E;
     [apply eqb_correct in E; subst w; rewrite to_Z_B62 in *; split; [reflexivity | lia]|]);
    (assert (Hj' : j <= 61);
     [destruct (Z.eq_dec j 62) as [->|]; [|lia]; exfalso; assert (w = B62) by (apply to_Z_inj; rewrite Hw, to_Z_B62; reflexivity);
      subst w; rewrite eqb_refl in E; discriminate|]);
    assert (Hw61 : to_Z w <= 2305843009213693952) by (rewrite Hw; change 2305843009213693952 with (2 ^ 61); apply Z.pow_le_mono_r; lia);
    assert (Hww2 : to_Z (PrimInt63.add w w) = 2 * to_Z w) by (rewrite add_spec, wB_eq, mod63_pos by lia; lia);
    assert (Hww : to_Z (PrimInt63.add w w) = 2 ^ (j + 1)) by (rewrite Hww2, Z.pow_add_r, Hw by lia; lia).
  - (* [comment removed for export] *)
    assert (Hacc : to_Z (PrimInt63.add acc w) = to_Z acc + to_Z w) by (rewrite add_spec, wB_eq, mod63_pos by lia; reflexivity).
    specialize (IH (PrimInt63.add w w) (PrimInt63.add acc w) (j + 1) Hww ltac:(lia) ltac:(lia)).
    destruct (p2i q (PrimInt63.add w w) (PrimInt63.add acc w)) as [a [r|]]; rewrite Hacc, Hww2 in IH; rewrite Pos2Z.inj_xI; lia.
  - (* [comment removed for export] *)
    specialize (IH (PrimInt63.add w w) acc (j + 1) Hww ltac:(lia) ltac:(lia)).
    destruct (p2i q (PrimInt63.add w w) acc) as [a [r|]]; rewrite Hww2 in IH; rewrite Pos2Z.inj_xO; lia.
  - (* [comment removed for export] *)
    rewrite add_spec, wB_eq, mod63_pos by lia. lia.
Qed.
Lemma p2i_1 : forall p,
  match p2i p i1 i0 with
  | (a, None) => to_Z a = Zpos p /\ to_Z a < 4611686018427387904
  | (a, Some q) => Zpos p = to_Z a + 4611686018427387904 * Zpos q /\ to_Z a < 4611686018427387904
  end.
Proof.
  intros p. pose proof (p2i_spec p i1 i0 0 ltac:(reflexivity) ltac:(lia) ltac:(rewrite to_Z_i0, to_Z_i1; lia)) as H.
  destruct (p2i p i1 i0) as [a [q|]]; rewrite to_Z_i0, to_Z_i1 in H; lia.
Qed.

Lemma p2i2_spec : forall p w acc j, to_Z w = 2 ^ (2 * j) -> 0 <= j <= 31 -> 0 <= to_Z acc < to_Z w ->
  match p2i2 p w acc with
  | (a, None) => to_Z a = to_Z acc + to_Z w * Zpos p /\ to_Z a < 4611686018427387904
  | (a, Some q) => to_Z acc + to_Z w * Zpos p = to_Z a + 4611686018427387904 * Zpos q /\ to_Z a < 4611686018427387904
  end.
Proof.
  fix IH 1. intros p w acc j Hw Hj Ha. pose proof (to_Z_rng w) as Rw. pose proof (to_Z_rng acc) as Ra.
  destruct p as [[q|q|]|[q|q|]|]; cbn [p2i2];
    (destruct (PrimInt63.eqb w B62) eqn:E;
     [apply Uint63Axioms.eqb_correct in E; subst w; rewrite to_Z_B62 in *; split; [reflexivity | lia]|]);
    (assert (Hj' : j <= 30);
     [destruct (Z.eq_dec j 31) as [->|]; [|lia]; exfalso; assert (w = B62) by (apply to_Z_inj; rewrite Hw, to_Z_B62; reflexivity);
      subst w; rewrite Uint63Axioms.eqb_refl in E; discriminate|]);
    assert (Hw60 : to_Z w <= 1152921504606846976) by (rewrite Hw; change 1152921504606846976 with (2 ^ (2 * 30)); apply Z.pow_le_mono_r; lia);
    assert (Hw2 : to_Z (PrimInt63.add w w) = 2 * to_Z w) by (rewrite add_spec, wB_eq, mod63_pos by lia; lia);
    assert (Hw4 : to_Z (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) = 4 * to_Z w) by (rewrite add_spec, wB_eq, Hw2, mod63_pos by lia; lia);
    assert (Hw4j : to_Z (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) = 2 ^ (2 * (j + 1))) by
      (rewrite Hw4, Z.mul_add_distr_l, Z.pow_add_r, Hw by lia; lia);
    cbv zeta.
  - (* [comment removed for export] *)
    assert (Hacc : to_Z (PrimInt63.add acc (PrimInt63.add w (PrimInt63.add w w))) = to_Z acc + 3 * to_Z w)
      by (rewrite add_spec, wB_eq, (add_spec w), wB_eq, Hw2, (mod63_pos (to_Z w + _)) by lia; rewrite mod63_pos by lia; lia).
    specialize (IH q (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) (PrimInt63.add acc (PrimInt63.add w (PrimInt63.add w w))) (j + 1) Hw4j ltac:(lia) ltac:(lia)).
    destruct (p2i2 q _ _) as [a [r|]]; rewrite Hacc, Hw4 in IH; rewrite (Pos2Z.inj_xI (xI q)), (Pos2Z.inj_xI q); lia.
  - (* [comment removed for export] *)
    assert (Hacc : to_Z (PrimInt63.add acc w) = to_Z acc + to_Z w) by (rewrite add_spec, wB_eq, mod63_pos by lia; reflexivity).
    specialize (IH q (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) (PrimInt63.add acc w) (j + 1) Hw4j ltac:(lia) ltac:(lia)).
    destruct (p2i2 q _ _) as [a [r|]]; rewrite Hacc, Hw4 in IH; rewrite (Pos2Z.inj_xI (xO q)), (Pos2Z.inj_xO q); lia.
  - (* [comment removed for export] *)
    rewrite add_spec, wB_eq, (add_spec w), wB_eq, Hw2, (mod63_pos (to_Z w + _)) by lia. rewrite mod63_pos by lia. lia.
  - (* [comment removed for export] *)
    assert (Hacc : to_Z (PrimInt63.add acc (PrimInt63.add w w)) = to_Z acc + 2 * to_Z w) by (rewrite add_spec, wB_eq, Hw2, mod63_pos by lia; lia).
    specialize (IH q (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) (PrimInt63.add acc (PrimInt63.add w w)) (j + 1) Hw4j ltac:(lia) ltac:(lia)).
    destruct (p2i2 q _ _) as [a [r|]]; rewrite Hacc, Hw4 in IH; rewrite (Pos2Z.inj_xO (xI q)), (Pos2Z.inj_xI q); lia.
  - (* [comment removed for export] *)
    specialize (IH q (PrimInt63.add (PrimInt63.add w w) (PrimInt63.add w w)) acc (j + 1) Hw4j ltac:(lia) ltac:(lia)).
    destruct (p2i2 q _ _) as [a [r|]]; rewrite Hw4 in IH; rewrite (Pos2Z.inj_xO (xO q)), (Pos2Z.inj_xO q); lia.
  - (* [comment removed for export] *)
    rewrite add_spec, wB_eq, Hw2, mod63_pos by lia. lia.
  - (* [comment removed for export] *)
    rewrite add_spec, wB_eq, mod63_pos by lia. lia.
Qed.
Lemma p2i2_1 : forall p,
  match p2i2 p i1 i0 with
  | (a, None) => to_Z a = Zpos p /\ to_Z a < 4611686018427387904
  | (a, Some q) => Zpos p = to_Z a + 4611686018427387904 * Zpos q /\ to_Z a < 4611686018427387904
  end.
Proof.
  intros p. pose proof (p2i2_spec p i1 i0 0 ltac:(reflexivity) ltac:(lia) ltac:(rewrite to_Z_i0, to_Z_i1; lia)) as H.
  destruct (p2i2 p i1 i0) as [a [q|]]; rewrite to_Z_i0, to_Z_i1 in H; lia.
Qed.
Lemma k2c_spec : forall k c, k2c k = Some c ->
  (0 <= k < 1152921504606846976 /\ ival c = k) \/ (18446744073709551616 - 1152921504606846976 < k < 18446744073709551616 /\ ival c = k - 18446744073709551616).
Proof.
  intros k c H. destruct k as [|p|p]; cbn [k2c] in H; [injection H as <-; left; split; [lia | reflexivity] | | discriminate].
  pose proof (p2i2_1 p) as Hp. pose proof (to_Z_rng (fst (p2i2 p i1 i0))).
  destruct (p2i2 p i1 i0) as [a [q|]]; cbn [fst] in *.
  - destruct q as [q1|q1|]; try discriminate. destruct q1; try discriminate.
    destruct (PrimInt63.ltb NB60 a) eqn:E; [|discriminate]. injection H as <-.
    apply ltb_spec in E. rewrite to_Z_NB60 in E. right. split; [lia|].
    apply ival_intro; [lia|]. rewrite sub_spec, wB_eq, to_Z_B62. rewrite (mod63_neg (to_Z a - _)) by lia.
    rewrite (mod63_neg (Z.pos p - _)) by lia. lia.
  - destruct (PrimInt63.ltb a B60) eqn:E; [|discriminate]. injection H as <-. apply ltb_spec in E. rewrite to_Z_B60 in E.
    left. split; [lia|]. rewrite ival_nonneg by lia. lia.
Qed.

Lemma p2w_spec : forall p a b, p2w p = Some (a, b) -> small a /\ small b /\ wv a b = Zpos p.
Proof.
  intros p a b H. unfold p2w in H. pose proof (p2i2_1 p) as Hp. pose proof (to_Z_rng (fst (p2i2 p i1 i0))).
  destruct (p2i2 p i1 i0) as [a0 [q|]]; cbn [fst] in *.
  - pose proof (p2i2_1 q) as Hq. pose proof (to_Z_rng (fst (p2i2 q i1 i0))).
    destruct (p2i2 q i1 i0) as [b0 [r|]]; cbn [fst] in *; [discriminate|].
    destruct (PrimInt63.ltb a0 B61) eqn:E.
    + apply ltb_spec in E. rewrite to_Z_B61 in E. destruct (smallb b0) eqn:Eb; [|discriminate]. injection H as <- <-.
      apply smallb_true in Eb. unfold small in *. rewrite ival_nonneg in Eb by lia.
      unfold wv. rewrite !ival_nonneg by lia. split; [lia|]. split; [lia|]. lia.
    + destruct (smallb (PrimInt63.add b0 i1)) eqn:Eb; [|discriminate]. injection H as <- <-.
      assert (E' : 2305843009213693952 <= to_Z a0).
      { destruct (Z.lt_ge_cases (to_Z a0) 2305843009213693952) as [h|h]; [|exact h].
        assert (PrimInt63.ltb a0 B61 = true) by (apply ltb_spec; rewrite to_Z_B61; exact h). congruence. }
      apply smallb_true in Eb. unfold small in *.
      assert (Hb1 : to_Z (PrimInt63.add b0 i1) = to_Z b0 + 1) by (rewrite add_spec, wB_eq, to_Z_i1, mod63_pos by lia; reflexivity).
      assert (Hb' : ival (PrimInt63.add b0 i1) = to_Z b0 + 1).
      { unfold ival in Eb |- *. rewrite Hb1 in Eb |- *. destruct (Z.ltb_spec (to_Z b0 + 1) 4611686018427387904); lia. }
      assert (Ha : ival (PrimInt63.sub a0 B62) = to_Z a0 - 4611686018427387904).
      { apply ival_intro; [lia|]. rewrite sub_spec, wB_eq, to_Z_B62. reflexivity. }
      unfold wv. rewrite Ha, Hb'. rewrite Hb' in Eb. split; [lia|]. split; [lia|]. lia.
  - destruct (PrimInt63.ltb a0 B61) eqn:E.
    + injection H as <- <-. apply ltb_spec in E. rewrite to_Z_B61 in E. unfold small, wv. rewrite ival_i0, ival_nonneg by lia.
      split; [lia|]. split; [lia|]. lia.
    + injection H as <- <-.
      assert (E' : 2305843009213693952 <= to_Z a0).
      { destruct (Z.lt_ge_cases (to_Z a0) 2305843009213693952) as [h|h]; [|exact h].
        assert (PrimInt63.ltb a0 B61 = true) by (apply ltb_spec; rewrite to_Z_B61; exact h). congruence. }
      assert (Ha : ival (PrimInt63.sub a0 B62) = to_Z a0 - 4611686018427387904).
      { apply ival_intro; [lia|]. rewrite sub_spec, wB_eq, to_Z_B62. reflexivity. }
      unfold small, wv. rewrite Ha, ival_i1. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma z2w_spec : forall z a b, z2w z = Some (a, b) -> small a /\ small b /\ wv a b = z.
Proof.
  intros z a b H. destruct z as [|p|p]; cbn [z2w] in H.
  - injection H as <- <-. unfold small, wv. rewrite ival_i0. lia.
  - exact (p2w_spec p a b H).
  - destruct (p2w p) as [[a0 b0]|] eqn:E; [|discriminate]. apply p2w_spec in E as [Ha [Hb Hv]].
    destruct (smallb (PrimInt63.sub i0 a0)) eqn:Ea; [|discriminate]. destruct (smallb (PrimInt63.sub i0 b0)) eqn:Eb; [|discriminate].
    injection H as <- <-. apply smallb_true in Ea, Eb. unfold small in *. split; [exact Ea|]. split; [exact Eb|].
    unfold wv in *. rewrite !ival_sub in * by (rewrite ival_i0; lia). rewrite ival_i0 in *. lia.
Qed.

