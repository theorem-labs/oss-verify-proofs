(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExBytes.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxKb.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive xb : Type :=
| BL (b : int)                      (* [comment removed for export] *)
| BT                                (* [comment removed for export] *)
| BF (ts : terms) (o : w64) (i : nat).  (* [comment removed for export] *)

Inductive xv : Type :=
| XL (w : w64)
| XS (ts : terms) (o : w64)
| XR (lo hi : Z)
| XK (m v : w64)
| XB (l : list xb)
| XT.

Definition smod (ρ : valuation) (ts : terms) (o : w64) : Z := (teval ρ ts + wZ o) mod two64.

(* [comment removed for export] *)
Definition xb_z (ρ : valuation) (x : xb) (z : Z) : Prop :=
  match x with
  | BL c => z = to_Z c
  | BT => True
  | BF ts o i => z = zbyte (smod ρ ts o) i
  end.

Definition xv_val (ρ : valuation) (v : xv) (w : bv 64) : Prop :=
  match v with
  | XL x => bv_unsigned w = wZ x
  | XS ts o => bv_unsigned w = smod ρ ts o
  | XR lo hi => lo <= bv_unsigned w <= hi
  | XK m x => Z.land (bv_unsigned w) (wZ m) = wZ x
  | XB l => length l = 8%nat /\ forall i, (i < 8)%nat -> xb_z ρ (nth i l BT) (zbyte (bv_unsigned w) i)
  | XT => True
  end.

Lemma bvu_range (w : bv 64) : 0 <= bv_unsigned w < two64.
Proof. pose proof (bv_unsigned_in_range 64 w) as H. rewrite bv_modulus_64 in H. exact H. Qed.

Lemma xv_XL (ρ : valuation) (x : w64) (w : bv 64) : xv_val ρ (XL x) w <-> w = wbv x.
Proof. cbn [xv_val]. split; intros H; [apply bv_eq; rewrite wbv_unsigned; exact H | subst w; apply wbv_unsigned]. Qed.

Lemma smod_range (ρ : valuation) (ts : terms) (o : w64) : 0 <= smod ρ ts o < two64.
Proof. unfold smod. apply Z.mod_pos_bound. unfold two64. lia. Qed.

Lemma wS_mod (b : w64) : wS b mod two64 = wZ b.
Proof.
  unfold wS. pose proof (wZ_range b). destruct (wh b).
  - replace (wZ b - two64) with (wZ b + (-1) * two64) by ring. rewrite Z.mod_add by (unfold two64; lia).
    apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma wS_range (b : w64) : - two63 <= wS b < two63.
Proof.
  unfold wS. pose proof (wZ_split b) as E. pose proof (phi_range (wl b)) as Hl.
  destruct (wh b) eqn:Eh; cbn [Z.b2z] in E; rewrite E; unfold two64, two63 in *; lia.
Qed.

(* [comment removed for export] *)
Definition mk_xs (ts : terms) (o : w64) : xv := match ts with [] => XL o | _ => XS ts o end.

Lemma mk_xs_sound (ρ : valuation) (ts : terms) (o : w64) (w : bv 64) :
  bv_unsigned w = smod ρ ts o -> xv_val ρ (mk_xs ts o) w.
Proof.
  intros H. unfold mk_xs. destruct ts as [|t r]; cbn [xv_val]; [|exact H].
  rewrite H. unfold smod. cbn [teval]. rewrite Z.add_0_l. apply Z.mod_small. apply wZ_range.
Qed.

Definition of_form (f : lin) : xv := mk_xs (snd f) (wofZ (fst f)).

Lemma of_form_sound (ρ : valuation) (f : lin) (w : bv 64) :
  bv_unsigned w = leval ρ f mod two64 -> xv_val ρ (of_form f) w.
Proof.
  intros H. apply mk_xs_sound. rewrite H. unfold smod, leval. rewrite wZ_wofZ.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia). f_equal. ring.
Qed.

(* [comment removed for export] *)
Definition xmod (v : xv) : option lin :=
  match v with
  | XL x => Some (wZ x, [])
  | XS ts o => Some (wZ o, ts)
  | _ => None
  end.

Lemma xmod_sound (ρ : valuation) (v : xv) (w : bv 64) (f : lin) :
  xv_val ρ v w -> xmod v = Some f -> bv_unsigned w = leval ρ f mod two64.
Proof.
  intros Hv H. destruct v; cbn [xmod xv_val] in *; try discriminate; injection H as <-; unfold leval; cbn [fst snd teval].
  - rewrite Hv. rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply wZ_range.
  - rewrite Hv. unfold smod. f_equal. ring.
Qed.

(* [comment removed for export] *)
Definition xform (s : store) (v : xv) : option lin :=
  match v with
  | XL x => Some (wZ x, [])
  | XS ts o =>
      let f := (wS o, ts) in
      match lrange s f with
      | Some (lo, hi) => if (0 <=? lo) && (hi <? two64) then Some f
                         else if (- two64 <=? lo) && (hi <? 0) then Some (wS o + two64, ts)
                         else if (two64 <=? lo) && (hi <? two64 + two64) then Some (wS o - two64, ts) else None
      | None => None
      end
  | _ => None
  end.

Lemma xform_sound (ρ : valuation) (s : store) (v : xv) (w : bv 64) (f : lin) :
  sat ρ s -> xv_val ρ v w -> xform s v = Some f -> bv_unsigned w = leval ρ f.
Proof.
  intros Hs Hv H. destruct v as [x|ts o| | | |]; cbn [xform xv_val] in *; try discriminate.
  - injection H as <-. unfold leval. cbn [fst snd teval]. lia.
  - destruct (lrange s (wS o, ts)) as [[lo hi]|] eqn:El; [|discriminate].
    pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr.
    destruct ((0 <=? lo) && (hi <? two64)) eqn:Ec.
    + injection H as <-.
      apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      rewrite Hv. unfold smod, leval. cbn [fst snd].
      rewrite <- (wS_mod o). rewrite Z.add_mod_idemp_r by (unfold two64; lia).
      rewrite Z.add_comm. apply Z.mod_small. unfold leval in Hr. cbn [fst snd] in Hr. lia.
    + destruct ((- two64 <=? lo) && (hi <? 0)) eqn:Ec2.
      * injection H as <-.
        apply andb_prop in Ec2 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        rewrite Hv. unfold smod, leval. cbn [fst snd].
        rewrite <- (wS_mod o). rewrite Z.add_mod_idemp_r by (unfold two64; lia).
        unfold leval in Hr. cbn [fst snd] in Hr.
        rewrite <- (Z.mod_unique (teval ρ ts + wS o) two64 (-1) (wS o + two64 + teval ρ ts)) by (unfold two64 in *; lia). reflexivity.
      * destruct ((two64 <=? lo) && (hi <? two64 + two64)) eqn:Ec3; [|discriminate]. injection H as <-.
        apply andb_prop in Ec3 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        rewrite Hv. unfold smod, leval. cbn [fst snd].
        rewrite <- (wS_mod o). rewrite Z.add_mod_idemp_r by (unfold two64; lia).
        unfold leval in Hr. cbn [fst snd] in Hr.
        rewrite <- (Z.mod_unique (teval ρ ts + wS o) two64 1 (wS o - two64 + teval ρ ts)) by (unfold two64 in *; lia). reflexivity.
Qed.

Definition mk_rng (lo hi : Z) : xv :=
  if (0 <=? lo) && (lo <=? hi) && (hi <? two64) then (if lo =? hi then XL (wofZ lo) else XR lo hi) else XT.

Lemma mk_rng_sound (ρ : valuation) (lo hi : Z) (w : bv 64) :
  lo <= bv_unsigned w <= hi -> xv_val ρ (mk_rng lo hi) w.
Proof.
  intros H. unfold mk_rng. pose proof (bvu_range w).
  destruct ((0 <=? lo) && (lo <=? hi) && (hi <? two64)) eqn:E; cbn [xv_val]; [|exact I].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
  destruct (Z.eqb_spec lo hi) as [->|Hne]; cbn [xv_val]; [|lia].
  rewrite wZ_wofZ. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Fixpoint kb_bytes (l : list xb) (i : Z) : Z * Z :=
  match l with
  | [] => (0, 0)
  | BL c :: r => let p := kb_bytes r (i + 8) in (Z.lor (Z.shiftl 255 i) (fst p), Z.lor (Z.shiftl (to_Z c) i) (snd p))
  | _ :: r => kb_bytes r (i + 8)
  end.

Lemma land_shiftl_byte (u i : Z) : 0 <= i -> Z.land u (Z.shiftl 255 i) = Z.shiftl (Z.land (Z.shiftr u i) 255) i.
Proof.
  intros Hi. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.shiftl_spec by lia. rewrite Z.land_spec.
  destruct (Z_lt_le_dec (n - i) 0) as [Hlt|Hge].
  - rewrite !(Z.testbit_neg_r _ (n - i)) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftr_spec by lia. replace (n - i + i) with n by lia. reflexivity.
Qed.

Lemma zbyte_land (u : Z) (j : nat) : zbyte u j = Z.land (Z.shiftr u (8 * Z.of_nat j)) 255.
Proof. unfold zbyte. rewrite Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma kb_bytes_sound (ρ : valuation) : forall (l : list xb) (j : nat) (u : Z),
  (forall k, (k < length l)%nat -> xb_z ρ (nth k l BT) (zbyte u (j + k))) ->
  kb_val (fst (kb_bytes l (8 * Z.of_nat j))) (snd (kb_bytes l (8 * Z.of_nat j))) u.
Proof.
  induction l as [|b r IH]; intros j u H; cbn [kb_bytes].
  - unfold kb_val. cbn [fst snd]. apply Z.land_0_r.
  - assert (IH' : kb_val (fst (kb_bytes r (8 * Z.of_nat j + 8))) (snd (kb_bytes r (8 * Z.of_nat j + 8))) u).
    { replace (8 * Z.of_nat j + 8) with (8 * Z.of_nat (S j)) by lia. apply IH. intros k Hk.
      specialize (H (S k) ltac:(cbn [length]; lia)). cbn [nth] in H. replace (S j + k)%nat with (j + S k)%nat by lia. exact H. }
    destruct b as [c| |ts o i]; try exact IH'.
    specialize (H 0%nat ltac:(cbn [length]; lia)). cbn [nth xb_z] in H. rewrite Nat.add_0_r in H.
    unfold kb_val in *. cbn [fst snd]. rewrite Z.land_lor_distr_r, IH'. f_equal.
    rewrite land_shiftl_byte by lia. rewrite <- zbyte_land, H. reflexivity.
Qed.

(* [comment removed for export] *)
Definition xrange (s : store) (v : xv) : option ivl :=
  match v with
  | XL x => let z := wZ x in Some (z, z)
  | XS ts o =>
      match lrange s (wS o, ts) with
      | Some (lo, hi) => if (0 <=? lo) && (hi <? two64) then Some (lo, hi) else None
      | None => None
      end
  | XR lo hi => Some (lo, hi)
  | XK m x => Some (wZ x, wZ x + (two64 - 1 - wZ m))
  | XB l => let p := kb_bytes l 0 in
            if (0 <=? fst p) && (fst p <? two64) then Some (snd p, snd p + (two64 - 1 - fst p)) else None
  | XT => None
  end.

Lemma kb_bytes_val (ρ : valuation) (l : list xb) (w : bv 64) : xv_val ρ (XB l) w -> kb_val (fst (kb_bytes l 0)) (snd (kb_bytes l 0)) (bv_unsigned w).
Proof. intros [Hl Hb]. apply (kb_bytes_sound ρ l 0%nat). intros k Hk. apply Hb. lia. Qed.

Lemma xrange_sound (ρ : valuation) (s : store) (v : xv) (w : bv 64) :
  sat ρ s -> xv_val ρ v w -> forall i, xrange s v = Some i -> fst i <= bv_unsigned w <= snd i.
Proof.
  intros Hs Hv i H. destruct v as [x|ts o|lo hi|m x|l|].
  5:{ pose proof (kb_bytes_val ρ l w Hv) as Hk. cbn [xrange] in H.
      destruct ((0 <=? fst (kb_bytes l 0)) && (fst (kb_bytes l 0) <? two64)) eqn:Ec; [|discriminate]. injection H as <-.
      apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [fst snd]. pose proof (bvu_range w).
      unfold two64 in *. split; [apply (kb_lower (fst (kb_bytes l 0)) (snd (kb_bytes l 0)) (bv_unsigned w)); [lia | exact Hk] | apply kb_upper; [lia | lia | exact Hk]]. }
  all: cbn [xrange xv_val] in *; try discriminate.
  - injection H as <-. cbn. lia.
  - destruct (lrange s (wS o, ts)) as [[lo hi]|] eqn:El; [|discriminate].
    destruct ((0 <=? lo) && (hi <? two64)) eqn:Ec; [|discriminate]. injection H as <-.
    assert (Hf : xform s (XS ts o) = Some (wS o, ts)) by (cbn [xform]; rewrite El, Ec; reflexivity).
    pose proof (xform_sound ρ s (XS ts o) w _ Hs Hv Hf) as E.
    pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in *. lia.
  - injection H as <-. cbn. lia.
  - injection H as <-. cbn [fst snd]. pose proof (bvu_range w). pose proof (wZ_range m).
    unfold two64 in *. split; [apply (kb_lower (wZ m) (wZ x)); [lia | exact Hv] |].
    apply kb_upper; [lia | lia | exact Hv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ones64 : Z := Z.ones 64.

(* [comment removed for export] *)
Fixpoint tz_aux (n : nat) (c : Z) : Z :=
  match n with
  | O => 0
  | S n' => if Z.even c then 1 + tz_aux n' (c / 2) else 0
  end.
Definition tz (c : Z) : Z := tz_aux 64 c.

Lemma tz_aux_spec (n : nat) (c : Z) : 0 <= tz_aux n c <= Z.of_nat n /\ (2 ^ tz_aux n c | c).
Proof.
  revert c. induction n as [|n IH]; intros c; cbn [tz_aux].
  - split; [lia|]. rewrite Z.pow_0_r. apply Z.divide_1_l.
  - destruct (Z.even c) eqn:E.
    + destruct (IH (c / 2)) as [H1 [q Hq]]. split; [lia|].
      exists q. rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
      pose proof (Z.div_mod c 2 ltac:(lia)) as Hd. rewrite Zmod_even, E in Hd. lia.
    + split; [lia|]. rewrite Z.pow_0_r. apply Z.divide_1_l.
Qed.

Lemma pow2_divide (a b : Z) : 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof. intros H. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Fixpoint tlow (ts : terms) : Z :=
  match ts with
  | [] => 64
  | (_, c) :: r => Z.min (tz c) (tlow r)
  end.

Lemma tlow_spec (ρ : valuation) (ts : terms) : 0 <= tlow ts <= 64 /\ (2 ^ tlow ts | teval ρ ts).
Proof.
  induction ts as [|[x c] r IH]; cbn [tlow teval].
  - split; [lia|]. apply Z.divide_0_r.
  - destruct IH as [H1 H2]. destruct (tz_aux_spec 64 c) as [H3 H4]. unfold tz. split; [lia|].
    apply Z.divide_add_r.
    + apply Z.divide_mul_l. eapply Z.divide_trans; [|exact H4]. apply pow2_divide. lia.
    + eapply Z.divide_trans; [|exact H2]. apply pow2_divide. lia.
Qed.

(* [comment removed for export] *)
Definition prefix (lo hi : Z) : Z * Z :=
  let k := Z.log2 (Z.lxor lo hi) + 1 in
  let m := Z.ldiff ones64 (Z.ones k) in (m, Z.land lo m).

Lemma prefix_sound (lo hi u : Z) : 0 <= lo <= u -> u <= hi < two64 ->
  kb_val (fst (prefix lo hi)) (snd (prefix lo hi)) u.
Proof.
  intros H1 H2. unfold prefix. cbn [fst snd]. set (k := Z.log2 (Z.lxor lo hi) + 1).
  assert (Hk : 0 <= k) by (unfold k; pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia).
  assert (Hxn : 0 <= Z.lxor lo hi) by (apply Z.lxor_nonneg; split; intros; lia).
  assert (Hq : lo / 2 ^ k = hi / 2 ^ k).
  { rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.bits_inj'. intros i Hi.
    rewrite !Z.shiftr_spec by lia.
    assert (Z.testbit (Z.lxor lo hi) (i + k) = false).
    { apply Z.bits_above_log2; [exact Hxn|]. unfold k. lia. }
    rewrite Z.lxor_spec in H. destruct (Z.testbit lo (i + k)), (Z.testbit hi (i + k)); cbn in H; congruence. }
  assert (Hu : u / 2 ^ k = lo / 2 ^ k).
  { apply Z.le_antisymm; [rewrite Hq|]; apply Z.div_le_mono; try apply Z.pow_pos_nonneg; lia. }
  unfold kb_val. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec.
  unfold ones64. rewrite !Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec i k) as [Hlt|Hge].
  - rewrite (proj2 (Z.ltb_lt i k)) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite (proj2 (Z.ltb_ge i k)) by lia. cbn [negb]. rewrite !andb_true_r.
    replace i with ((i - k) + k) by lia. rewrite <- !Z.shiftr_spec by lia.
    rewrite !Z.shiftr_div_pow2 by lia. rewrite Hu. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kb_meet (p q : Z * Z) : Z * Z := (Z.lor (fst p) (fst q), Z.lor (snd p) (snd q)).

Lemma kb_meet_sound (p q : Z * Z) (u : Z) :
  kb_val (fst p) (snd p) u -> kb_val (fst q) (snd q) u -> kb_val (fst (kb_meet p q)) (snd (kb_meet p q)) u.
Proof.
  intros H1 H2. unfold kb_meet, kb_val in *; cbn [fst snd]. rewrite <- H1, <- H2.
  apply Z.bits_inj'. intros i Hi. bits. destruct (Z.testbit u i), (Z.testbit (fst p) i), (Z.testbit (fst q) i); reflexivity.
Qed.

Definition to_kb (s : store) (v : xv) : Z * Z :=
  match v with
  | XL x => (ones64, wZ x)
  | XS ts o =>
      let k := tlow ts in
      let low := (Z.ones k, wZ o mod 2 ^ k) in
      match xrange s v with
      | Some (lo, hi) => kb_meet low (prefix lo hi)
      | None => low
      end
  | XR lo hi => if (0 <=? lo) && (lo <=? hi) && (hi <? two64) then prefix lo hi else (0, 0)
  | XK m x => (wZ m, wZ x)
  | XB l => kb_bytes l 0
  | XT => (0, 0)
  end.

Lemma kb_low_sound (ρ : valuation) (ts : terms) (o : w64) :
  kb_val (Z.ones (tlow ts)) (wZ o mod 2 ^ tlow ts) (smod ρ ts o).
Proof.
  destruct (tlow_spec ρ ts) as [Hk [q Hq]]. unfold kb_val, smod. rewrite Z.land_ones by lia.
  assert (Hdiv : (2 ^ tlow ts | two64)) by (change two64 with (2 ^ 64); apply pow2_divide; lia).
  rewrite Z.mod_mod_divide by exact Hdiv. rewrite Hq. rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma to_kb_sound (ρ : valuation) (s : store) (v : xv) (w : bv 64) :
  sat ρ s -> xv_val ρ v w -> kb_val (fst (to_kb s v)) (snd (to_kb s v)) (bv_unsigned w).
Proof.
  intros Hs Hv. pose proof (bvu_range w) as Hw. destruct v as [x|ts o|lo hi|m x| |]; cbn [to_kb].
  - cbn [xv_val] in Hv. unfold kb_val, ones64. cbn [fst snd]. rewrite Z.land_ones by lia. rewrite Hv.
    apply Z.mod_small. pose proof (wZ_range x). unfold two64 in *. lia.
  - assert (Hlow : kb_val (fst (Z.ones (tlow ts), wZ o mod 2 ^ tlow ts)) (snd (Z.ones (tlow ts), wZ o mod 2 ^ tlow ts)) (bv_unsigned w)).
    { cbn [fst snd xv_val] in *. rewrite Hv. apply kb_low_sound. }
    destruct (xrange s (XS ts o)) as [[lo hi]|] eqn:Er; [|exact Hlow].
    pose proof (xrange_sound ρ s _ w Hs Hv _ Er) as Hr. cbn [fst snd] in Hr.
    apply kb_meet_sound; [exact Hlow|].
    cbn [xrange] in Er. destruct (lrange s (wS o, ts)) as [[lo' hi']|]; [|discriminate].
    destruct ((0 <=? lo') && (hi' <? two64)) eqn:Ec; [|discriminate]. injection Er as <- <-.
    apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply prefix_sound; lia.
  - cbn [xv_val] in Hv. destruct ((0 <=? lo) && (lo <=? hi) && (hi <? two64)) eqn:Ec.
    + apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
      apply Z.leb_le in E1. apply Z.ltb_lt in E3. apply prefix_sound; lia.
    + unfold kb_val. cbn. apply Z.land_0_r.
  - exact Hv.
  - exact (kb_bytes_val ρ l w Hv).
  - unfold kb_val. cbn. apply Z.land_0_r.
Qed.

(* [comment removed for export] *)
Definition mk_kb (p : Z * Z) : xv :=
  let m := Z.land (fst p) ones64 in
  let x := Z.land (snd p) m in
  if m =? ones64 then XL (wofZ x) else if m =? 0 then XT else XK (wofZ m) (wofZ x).

Lemma mk_kb_sound (ρ : valuation) (p : Z * Z) (w : bv 64) :
  kb_val (fst p) (snd p) (bv_unsigned w) -> xv_val ρ (mk_kb p) w.
Proof.
  intros H. unfold mk_kb. pose proof (bvu_range w) as Hw.
  set (m := Z.land (fst p) ones64). set (x := Z.land (snd p) m).
  assert (Hm : 0 <= m < two64).
  { unfold m, ones64. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. unfold two64; lia. }
  assert (Hx : Z.land (bv_unsigned w) m = x).
  { unfold x, m. unfold kb_val in H. rewrite <- H. apply Z.bits_inj'. intros i Hi. bits.
    destruct (Z.testbit (bv_unsigned w) i), (Z.testbit (fst p) i), (Z.testbit ones64 i); reflexivity. }
  assert (Hxr : 0 <= x < two64).
  { rewrite <- Hx. split; [apply Z.land_nonneg; lia|].
    pose proof (land_add_ldiff m (bv_unsigned w)) as E. rewrite Z.land_comm in E.
    pose proof (ldiff_nonneg m (bv_unsigned w) ltac:(lia)). lia. }
  destruct (Z.eqb_spec m ones64) as [Em|Em].
  - cbn [xv_val]. rewrite wZ_wofZ, Z.mod_small by lia. rewrite <- Hx, Em. unfold ones64.
    rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. unfold two64 in Hw. lia.
  - destruct (Z.eqb_spec m 0) as [E0|E0]; [exact I|]. cbn [xv_val].
    rewrite !wZ_wofZ, !Z.mod_small by lia. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_add_z (a b : bv 64) : bv_unsigned (bv_add a b) = (bv_unsigned a + bv_unsigned b) mod two64.
Proof. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.
Lemma bv_sub_z (a b : bv 64) : bv_unsigned (bv_sub a b) = (bv_unsigned a - bv_unsigned b) mod two64.
Proof. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.
Lemma bv_mul_z (a b : bv 64) : bv_unsigned (bv_mul a b) = (bv_unsigned a * bv_unsigned b) mod two64.
Proof. rewrite bv_mul_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.

Lemma smod_add (ρ : valuation) (t1 t2 : terms) (o1 o2 : w64) :
  (smod ρ t1 o1 + smod ρ t2 o2) mod two64 = smod ρ (tadd t1 t2) (w_add o1 o2).
Proof.
  unfold smod. rewrite teval_tadd, wZ_add. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma smod_addc (ρ : valuation) (t : terms) (o b : w64) :
  (smod ρ t o + wZ b) mod two64 = smod ρ t (w_add o b).
Proof.
  unfold smod. rewrite wZ_add. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma mod_wS (z : Z) (d : w64) : (z + wZ d) mod two64 = (z + wS d) mod two64.
Proof. rewrite <- (wS_mod d). rewrite Zplus_mod_idemp_r. reflexivity. Qed.

Lemma mk_rng_shift_sound (ρ : valuation) (lo hi u : Z) (d : w64) (c : bv 64) :
  lo <= u <= hi -> bv_unsigned c = (u + wZ d) mod two64 -> xv_val ρ (mk_rng (lo + wS d) (hi + wS d)) c.
Proof.
  intros Hu Hc. destruct ((0 <=? lo + wS d) && (hi + wS d <? two64)) eqn:Ec.
  - apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply mk_rng_sound. rewrite Hc, mod_wS. rewrite Z.mod_small by lia. lia.
  - unfold mk_rng. destruct ((0 <=? lo + wS d) && (lo + wS d <=? hi + wS d) && (hi + wS d <? two64)) eqn:E2; [|exact I].
    exfalso. apply andb_prop in E2 as [E2 E3]. apply andb_prop in E2 as [E1 _]. rewrite E1, E3 in Ec. discriminate.
Qed.

Definition a_add (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_add a b)
  | XS ts o, XL b => XS ts (w_add o b)
  | XL b, XS ts o => XS ts (w_add o b)
  | XS t1 o1, XS t2 o2 => mk_xs (tadd t1 t2) (w_add o1 o2)
  | XR lo hi, XL b => mk_rng (lo + wS b) (hi + wS b)
  | XL b, XR lo hi => mk_rng (lo + wS b) (hi + wS b)
  | _, _ => mk_kb (kbz_add (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)) false)
  end.

Lemma a_add_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_add s x y) (bv_add a b).
Proof.
  intros Hs Hx Hy. pose proof (bv_add_z a b) as E.
  assert (Hkb : xv_val ρ (mk_kb (kbz_add (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)) false)) (bv_add a b)).
  { apply mk_kb_sound. rewrite E.
    exact (kbz_add_sound _ _ _ _ (bv_unsigned a) (bv_unsigned b) false (to_kb_sound ρ s x a Hs Hx) (to_kb_sound ρ s y b Hs Hy)). }
  pose proof (bvu_range a) as Ha. pose proof (bvu_range b) as Hb.
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_add]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end);
    cbn [xv_val] in Hx, Hy.
  - (* [comment removed for export] *) cbn [xv_val]. rewrite E, Hx, Hy, wZ_add. reflexivity.
  - (* [comment removed for export] *) cbn [xv_val]. rewrite E, Hx, Hy. rewrite Z.add_comm. apply smod_addc.
  - (* [comment removed for export] *) apply (mk_rng_shift_sound ρ lo2 hi2 (bv_unsigned b) xa); [exact Hy|]. rewrite E, Hx. f_equal; ring.
  - (* [comment removed for export] *) cbn [xv_val]. rewrite E, Hx, Hy. apply smod_addc.
  - (* [comment removed for export] *) apply mk_xs_sound. rewrite E, Hx, Hy. apply smod_add.
  - (* [comment removed for export] *) apply (mk_rng_shift_sound ρ lo hi (bv_unsigned a) yb); [exact Hx|]. rewrite E, Hy. reflexivity.
Qed.

Lemma smod_sub (ρ : valuation) (t1 t2 : terms) (o1 o2 : w64) :
  (smod ρ t1 o1 - smod ρ t2 o2) mod two64 = smod ρ (tadd t1 (tscale (-1) t2)) (w_sub o1 o2).
Proof.
  unfold smod. rewrite teval_tadd, teval_tscale, wZ_sub. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma smod_subc (ρ : valuation) (t : terms) (o b : w64) :
  (smod ρ t o - wZ b) mod two64 = smod ρ t (w_sub o b).
Proof.
  unfold smod. rewrite wZ_sub. rewrite Zminus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma smod_csub (ρ : valuation) (t : terms) (o a : w64) :
  (wZ a - smod ρ t o) mod two64 = smod ρ (tscale (-1) t) (w_sub a o).
Proof.
  unfold smod. rewrite teval_tscale, wZ_sub. rewrite Zminus_mod_idemp_r, Zplus_mod_idemp_r. f_equal. ring.
Qed.

Definition a_sub (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_sub a b)
  | XS ts o, XL b => XS ts (w_sub o b)
  | XL a, XS ts o => mk_xs (tscale (-1) ts) (w_sub a o)
  | XS t1 o1, XS t2 o2 => mk_xs (tadd t1 (tscale (-1) t2)) (w_sub o1 o2)
  | XR lo hi, XL b => mk_rng (lo - wS b) (hi - wS b)
  | _, _ => mk_kb (kbz_add (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)) true)
  end.

Lemma mk_rng_shift_sound' (ρ : valuation) (lo hi u : Z) (d : w64) (c : bv 64) :
  lo <= u <= hi -> bv_unsigned c = (u - wZ d) mod two64 -> xv_val ρ (mk_rng (lo - wS d) (hi - wS d)) c.
Proof.
  intros Hu Hc. destruct ((0 <=? lo - wS d) && (hi - wS d <? two64)) eqn:Ec.
  - apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply mk_rng_sound. rewrite Hc. rewrite <- (wS_mod d), Zminus_mod_idemp_r. rewrite Z.mod_small by lia. lia.
  - unfold mk_rng. destruct ((0 <=? lo - wS d) && (lo - wS d <=? hi - wS d) && (hi - wS d <? two64)) eqn:E2; [|exact I].
    exfalso. apply andb_prop in E2 as [E2 E3]. apply andb_prop in E2 as [E1 _]. rewrite E1, E3 in Ec. discriminate.
Qed.

Lemma a_sub_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_sub s x y) (bv_sub a b).
Proof.
  intros Hs Hx Hy. pose proof (bv_sub_z a b) as E.
  assert (Hkb : xv_val ρ (mk_kb (kbz_add (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)) true)) (bv_sub a b)).
  { apply mk_kb_sound. rewrite E.
    exact (kbz_add_sound _ _ _ _ (bv_unsigned a) (bv_unsigned b) true (to_kb_sound ρ s x a Hs Hx) (to_kb_sound ρ s y b Hs Hy)). }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_sub]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end);
    cbn [xv_val] in Hx, Hy.
  - cbn [xv_val]. rewrite E, Hx, Hy, wZ_sub. reflexivity.
  - apply mk_xs_sound. rewrite E, Hx, Hy. apply smod_csub.
  - cbn [xv_val]. rewrite E, Hx, Hy. apply smod_subc.
  - apply mk_xs_sound. rewrite E, Hx, Hy. apply smod_sub.
  - apply (mk_rng_shift_sound' ρ lo hi (bv_unsigned a) yb); [exact Hx|]. rewrite E, Hy. reflexivity.
Qed.

Definition a_mul (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_mul a b)
  | XS ts o, XL b => mk_xs (tscale (wS b) ts) (w_mul o b)
  | XL b, XS ts o => mk_xs (tscale (wS b) ts) (w_mul o b)
  | _, _ => XT
  end.

Lemma smod_mulc (ρ : valuation) (t : terms) (o b : w64) :
  (smod ρ t o * wZ b) mod two64 = smod ρ (tscale (wS b) t) (w_mul o b).
Proof.
  unfold smod. rewrite teval_tscale, wZ_mul. rewrite Zmult_mod_idemp_l. rewrite Zplus_mod_idemp_r.
  assert (Eb : exists d, wZ b = wS b + d * two64) by (unfold wS; destruct (wh b); [exists 1 | exists 0]; ring).
  destruct Eb as [d ->].
  replace ((teval ρ t + wZ o) * (wS b + d * two64)) with ((teval ρ t + wZ o) * wS b + ((teval ρ t + wZ o) * d) * two64) by ring.
  replace (wS b * teval ρ t + wZ o * (wS b + d * two64)) with ((teval ρ t + wZ o) * wS b + (wZ o * d) * two64) by ring.
  rewrite !Z.mod_add by (unfold two64; lia). reflexivity.
Qed.

Lemma a_mul_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_mul s x y) (bv_mul a b).
Proof.
  intros Hx Hy. pose proof (bv_mul_z a b) as E.
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_mul]; try exact I;
    cbn [xv_val] in Hx, Hy.
  - cbn [xv_val]. rewrite E, Hx, Hy, wZ_mul. reflexivity.
  - apply mk_xs_sound. rewrite E, Hx, Hy. rewrite Z.mul_comm. apply smod_mulc.
  - apply mk_xs_sound. rewrite E, Hx, Hy. apply smod_mulc.
Qed.

(* [comment removed for export] *)
Definition shamt (y : xv) : option int :=
  match y with XL b => Some (w_shamt6 b) | _ => None end.

Lemma shamt_sound (ρ : valuation) (y : xv) (b : bv 64) (k : int) :
  xv_val ρ y b -> shamt y = Some k -> bv_unsigned (bv_and b (Z_to_bv 64 63)) = to_Z k /\ 0 <= to_Z k < 64.
Proof.
  intros Hy H. destruct y as [yb| | | | |]; cbn [shamt] in H; try discriminate. injection H as <-.
  cbn [xv_val] in Hy. split; [|apply phi_shamt6_range].
  rewrite bv_and_unsigned, Hy, Z_to_bv_unsigned. change (bv_wrap 64 63) with 63. rewrite phi_shamt6. reflexivity.
Qed.

Lemma smod_shl (ρ : valuation) (t : terms) (o : w64) (k : int) : 0 <= to_Z k < 64 ->
  (smod ρ t o * 2 ^ to_Z k) mod two64 = smod ρ (tscale (2 ^ to_Z k) t) (w_sll o k).
Proof.
  intros Hk. unfold smod. rewrite teval_tscale, wZ_sll by lia. rewrite Zmult_mod_idemp_l.
  rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

Definition a_sll (s : store) (x y : xv) : xv :=
  match shamt y with
  | Some k =>
      match x with
      | XL a => XL (w_sll a k)
      | XS ts o => mk_xs (tscale (2 ^ to_Z k) ts) (w_sll o k)
      | XR lo hi => if (0 <=? lo) && (hi * 2 ^ to_Z k <? two64) then XR (lo * 2 ^ to_Z k) (hi * 2 ^ to_Z k)
                    else mk_kb (kbz_sll (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))
      | _ => mk_kb (kbz_sll (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))
      end
  | None => XT
  end.

Lemma a_sll_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_sll s x y) (bv_shiftl a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. unfold a_sll. destruct (shamt y) as [k|] eqn:Ek; [|exact I].
  destruct (shamt_sound ρ y b k Hy Ek) as [Eb Hk].
  assert (E : bv_unsigned (bv_shiftl a (bv_and b (Z_to_bv 64 63))) = (bv_unsigned a * 2 ^ to_Z k) mod two64).
  { rewrite bv_shiftl_unsigned, Eb. unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (Hkb : xv_val ρ (mk_kb (kbz_sll (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))) (bv_shiftl a (bv_and b (Z_to_bv 64 63)))).
  { apply mk_kb_sound. rewrite E. pose proof (kbz_sll_sound _ _ (bv_unsigned a) (to_Z k) Hk (to_kb_sound ρ s x a Hs Hx)) as K.
    rewrite Z.land_ones, Z.shiftl_mul_pow2 in K by lia. exact K. }
  destruct x as [xa|t1 o1|lo hi| | |]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end); cbn [xv_val] in Hx.
  - cbn [xv_val]. rewrite E, Hx, wZ_sll by lia. reflexivity.
  - apply mk_xs_sound. rewrite E, Hx. apply smod_shl. exact Hk.
  - destruct ((0 <=? lo) && (hi * 2 ^ to_Z k <? two64)) eqn:Ec; [|exact Hkb].
    apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    cbn [xv_val]. rewrite E. pose proof (Z.pow_pos_nonneg 2 (to_Z k) ltac:(lia) ltac:(lia)) as Hp.
    rewrite Z.mod_small by (split; [nia | nia]). split; nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Fixpoint floor_find (fs : list fact) (hc : Z) (T : terms) (k2 : Z) : option (int * Z) :=
  match fs with
  | [] => None
  | Fact (cF, TF) lo hi false :: r =>
      match tadd TF (tscale (-1) T) with
      | [(v, a)] => if a =? - k2 then
                      let d1 := (lo + hc - cF) / k2 in let d2 := (hi + hc - cF) / k2 in
                      if d1 =? d2 then Some (v, d1) else floor_find r hc T k2
                    else floor_find r hc T k2
      | _ => floor_find r hc T k2
      end
  | _ :: r => floor_find r hc T k2
  end.

Lemma floor_find_sound (ρ : valuation) (fs : list fact) (hc : Z) (T : terms) (k2 : Z) (v : int) (d : Z) :
  0 < k2 -> Forall (fact_sat ρ) fs -> floor_find fs hc T k2 = Some (v, d) -> (hc + teval ρ T) / k2 = ρ v + d.
Proof.
  intros Hk2. induction fs as [|[[cF TF] lo hi ho] r IH]; intros Hs H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. destruct ho; [apply IH; assumption|]. cbn [floor_find] in H.
  unfold fact_sat, leval in Hf. cbn [fc_f fc_lo fc_hi fc_hole fst snd] in Hf.
  destruct (tadd TF (tscale (-1) T)) as [|[w a] [|q rr]] eqn:Et; try (apply IH; assumption).
  destruct (Z.eqb_spec a (- k2)) as [Ea|Ea]; [|apply IH; assumption].
  destruct (Z.eqb_spec ((lo + hc - cF) / k2) ((hi + hc - cF) / k2)) as [Ed|Ed]; [|apply IH; assumption].
  injection H as <- <-.
  assert (Htf : teval ρ TF = teval ρ T - k2 * ρ w).
  { pose proof (f_equal (teval ρ) Et) as E2. rewrite teval_tadd, teval_tscale in E2. cbn [teval] in E2. lia. }
  set (h := hc + teval ρ T).
  assert (Hb : lo + hc - cF <= h - k2 * ρ w <= hi + hc - cF) by (unfold h; lia).
  assert (Hq : (h - k2 * ρ w) / k2 = (lo + hc - cF) / k2).
  { apply Z.le_antisymm.
    - rewrite Ed. apply Z.div_le_mono; lia.
    - apply Z.div_le_mono; lia. }
  replace h with ((h - k2 * ρ w) + ρ w * k2) by ring. rewrite Z.div_add by lia. rewrite Hq. ring.
Qed.

(* [comment removed for export] *)
Definition lshr (s : store) (f : lin) (k : Z) : option lin :=
  let k2 := 2 ^ k in
  let p := tsplit k2 (snd f) in
  match lrange s (fst f, snd p) with
  | Some (lo, hi) => if lo / k2 =? hi / k2 then Some (lo / k2, fst p) else
                     match floor_find (st_facts s) (fst f) (snd p) k2 with
                     | Some (v, d) => Some (d, tadd (fst p) [(v, 1)])
                     | None => None
                     end
  | None => None
  end.

Lemma lshr_sound (ρ : valuation) (s : store) (f g : lin) (k : Z) :
  sat ρ s -> 0 <= k -> lshr s f k = Some g -> leval ρ g = leval ρ f / 2 ^ k.
Proof.
  intros Hs Hk H. unfold lshr in H. set (k2 := 2 ^ k) in *.
  assert (Hk2 : 0 < k2) by (apply Z.pow_pos_nonneg; lia).
  destruct (lrange s (fst f, snd (tsplit k2 (snd f)))) as [[lo hi]|] eqn:El; [|discriminate].
  pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. unfold leval in *. cbn [fst snd] in *.
  rewrite (tsplit_sound ρ k2 (snd f) Hk2).
  set (G := teval ρ (fst (tsplit k2 (snd f)))). set (Hh := teval ρ (snd (tsplit k2 (snd f)))) in *.
  replace (fst f + (k2 * G + Hh)) with ((fst f + Hh) + G * k2) by ring.
  rewrite Z.div_add by lia.
  destruct (Z.eqb_spec (lo / k2) (hi / k2)) as [E|E].
  - injection H as <-. cbn [fst snd].
    assert (Hq : (fst f + Hh) / k2 = lo / k2).
    { apply Z.le_antisymm.
      - rewrite E. apply Z.div_le_mono; lia.
      - apply Z.div_le_mono; lia. }
    rewrite Hq. unfold G. ring.
  - destruct (floor_find (st_facts s) (fst f) (snd (tsplit k2 (snd f))) k2) as [[v d]|] eqn:Ef; [|discriminate].
    injection H as <-. cbn [fst snd]. rewrite teval_tadd. cbn [teval].
    pose proof (floor_find_sound ρ (st_facts s) (fst f) _ k2 v d Hk2 (proj2 Hs) Ef) as HF. fold Hh in HF.
    rewrite HF. unfold G. ring.
Qed.

Definition a_srl (s : store) (x y : xv) : xv :=
  match shamt y with
  | Some k =>
      match x with
      | XL a => XL (w_srl a k)
      | _ =>
          match xform s x with
          | Some f => match lshr s f (to_Z k) with
                      | Some g => of_form g
                      | None => match xrange s x with
                                | Some (lo, hi) => mk_rng (lo / 2 ^ to_Z k) (hi / 2 ^ to_Z k)
                                | None => mk_kb (kbz_srl (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))
                                end
                      end
          | None => match x with
                    | XR lo hi => mk_rng (lo / 2 ^ to_Z k) (hi / 2 ^ to_Z k)
                    | _ => mk_kb (kbz_srl (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))
                    end
          end
      end
  | None => XT
  end.

Lemma a_srl_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_srl s x y) (bv_shiftr a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. unfold a_srl. destruct (shamt y) as [k|] eqn:Ek; [|exact I].
  destruct (shamt_sound ρ y b k Hy Ek) as [Eb Hk]. pose proof (bvu_range a) as Ha.
  assert (E : bv_unsigned (bv_shiftr a (bv_and b (Z_to_bv 64 63))) = bv_unsigned a / 2 ^ to_Z k).
  { rewrite bv_shiftr_unsigned, Eb. apply Z.shiftr_div_pow2. lia. }
  assert (Hk2 : 0 < 2 ^ to_Z k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hkb : xv_val ρ (mk_kb (kbz_srl (fst (to_kb s x)) (snd (to_kb s x)) (to_Z k))) (bv_shiftr a (bv_and b (Z_to_bv 64 63)))).
  { apply mk_kb_sound. rewrite E. rewrite <- Z.shiftr_div_pow2 by lia.
    apply kbz_srl_sound; [lia | unfold two64 in Ha; lia | apply (to_kb_sound ρ); assumption]. }
  assert (Hrng : forall lo hi, lo <= bv_unsigned a <= hi -> xv_val ρ (mk_rng (lo / 2 ^ to_Z k) (hi / 2 ^ to_Z k)) (bv_shiftr a (bv_and b (Z_to_bv 64 63)))).
  { intros lo hi Hr. apply mk_rng_sound. rewrite E. split; apply Z.div_le_mono; lia. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|].
  - cbn [xv_val] in *. rewrite E, Hx, wZ_srl by lia. reflexivity.
  - destruct (xform s (XS t1 o1)) as [f|] eqn:Ef; [|exact Hkb].
    pose proof (xform_sound ρ s _ a f Hs Hx Ef) as Hf.
    destruct (lshr s f (to_Z k)) as [g|] eqn:Eg.
    + apply of_form_sound. rewrite E, (lshr_sound ρ s f g (to_Z k) Hs ltac:(lia) Eg), Hf.
      symmetry. apply Z.mod_small. rewrite <- Hf. split; [apply Z.div_pos; lia|].
      apply Z.le_lt_trans with (bv_unsigned a); [apply Z.div_le_upper_bound; nia | lia].
    + destruct (xrange s (XS t1 o1)) as [[lo hi]|] eqn:Er; [|exact Hkb].
      apply Hrng. exact (xrange_sound ρ s _ a Hs Hx _ Er).
  - cbn [xform]. apply Hrng. exact Hx.
  - cbn [xform]. exact Hkb.
  - cbn [xform]. exact Hkb.
  - cbn [xform]. exact Hkb.
Qed.

(* [comment removed for export] *)
Definition a_sra (s : store) (x y : xv) : xv :=
  match x, shamt y with
  | XL a, Some k => XL (w_sra a k)
  | _, Some k => match xrange s x with
                 | Some (lo, hi) => if (0 <=? lo) && (hi <? two63) then a_srl s x y else XT
                 | None => XT
                 end
  | _, None => XT
  end.

Lemma a_sra_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_sra s x y) (bv_ashiftr a (bv_and b (Z_to_bv 64 63))).
Proof.
  intros Hs Hx Hy. unfold a_sra. destruct (shamt y) as [k|] eqn:Ek; [|destruct x; exact I].
  destruct (shamt_sound ρ y b k Hy Ek) as [Eb Hk].
  assert (Hgen : (match xrange s x with
                  | Some (lo, hi) => if (0 <=? lo) && (hi <? two63) then a_srl s x y else XT
                  | None => XT
                  end) = XT \/ (exists lo hi, xrange s x = Some (lo, hi) /\ 0 <= lo /\ hi < two63 /\
                   (match xrange s x with
                    | Some (lo, hi) => if (0 <=? lo) && (hi <? two63) then a_srl s x y else XT
                    | None => XT
                    end) = a_srl s x y)).
  { destruct (xrange s x) as [[lo hi]|]; [|left; reflexivity].
    destruct ((0 <=? lo) && (hi <? two63)) eqn:Ec; [|left; reflexivity]. right. exists lo, hi.
    apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. repeat split; lia. }
  assert (Hsmall : forall lo hi, xrange s x = Some (lo, hi) -> 0 <= lo -> hi < two63 ->
            bv_ashiftr a (bv_and b (Z_to_bv 64 63)) = bv_shiftr a (bv_and b (Z_to_bv 64 63))).
  { intros lo hi Er H1 H2. pose proof (xrange_sound ρ s x a Hs Hx _ Er) as Hr. cbn [fst snd] in Hr.
    apply bv_eq. rewrite bv_ashiftr_unsigned, bv_shiftr_unsigned.
    assert (Hsg : bv_signed a = bv_unsigned a).
    { unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with two63. rewrite bv_modulus_64.
      rewrite Z.mod_small by (unfold two63, two64 in *; lia). ring. }
    rewrite Hsg. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small.
    rewrite Eb. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; try apply Z.pow_pos_nonneg; lia|].
    apply Z.le_lt_trans with (bv_unsigned a); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|];
      pose proof (Z.pow_pos_nonneg 2 (to_Z k) ltac:(lia) ltac:(lia)); nia | unfold two63, two64 in *; lia]. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|];
    try (destruct Hgen as [-> | (lo' & hi' & Er & H1 & H2 & ->)]; [exact I|];
         rewrite (Hsmall lo' hi' Er H1 H2); apply a_srl_sound; assumption).
  all: apply xv_XL in Hx; subst a.
  all: destruct y as [yb| | | | |]; cbn [shamt] in Ek; try discriminate; injection Ek as <-.
  all: apply xv_XL in Hy; subst b; apply xv_XL; symmetry; apply wbv_sra.
Qed.

(* [comment removed for export] *)
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

Lemma land_high_mask (u k : Z) : 0 <= k <= 64 -> 0 <= u < two64 ->
  Z.land u (two64 - 1 - (2 ^ k - 1)) = u - u mod 2 ^ k.
Proof.
  intros Hk Hu.
  assert (E : two64 - 1 - (2 ^ k - 1) = Z.ldiff ones64 (Z.ones k)).
  { pose proof (land_add_ldiff ones64 (Z.ones k)) as E0.
    assert (Z.land ones64 (Z.ones k) = Z.ones k) as E1.
    { rewrite Z.land_comm. unfold ones64. rewrite Z.land_ones by lia. apply Z.mod_small.
      rewrite Z.ones_equiv, <- Z.sub_1_r. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia|].
      pose proof (Z.pow_le_mono_r 2 k 64 ltac:(lia) ltac:(lia)). lia. }
    rewrite E1 in E0. unfold ones64 in *. rewrite !Z.ones_equiv, <- !Z.sub_1_r in *. unfold two64. lia. }
  rewrite E. pose proof (land_add_ldiff u (Z.ones k)) as E2. rewrite Z.land_ones in E2 by lia.
  assert (E3 : Z.land u (Z.ldiff ones64 (Z.ones k)) = Z.ldiff u (Z.ones k)).
  { apply Z.bits_inj'. intros i Hi. bits. unfold ones64. rewrite !Z.testbit_ones_nonneg by lia.
    destruct (Z_lt_le_dec i 64) as [Hl|Hg].
    - rewrite (proj2 (Z.ltb_lt i 64)) by lia. destruct (Z.testbit u i), (i <? k); reflexivity.
    - rewrite (proj2 (Z.ltb_ge i 64)) by lia. rewrite (proj2 (Z.ltb_ge i k)) by lia.
      assert (Z.testbit u i = false) as ->.
      { apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec u 0) as [->|Hn]; [cbn; lia|].
        apply Z.log2_lt_pow2; [lia|]. pose proof (Z.pow_le_mono_r 2 64 i ltac:(lia) ltac:(lia)). unfold two64 in Hu. lia. }
      reflexivity. }
  rewrite E3. lia.
Qed.

Definition kb_and_lit (s : store) (x : xv) (mz : Z) : xv :=
  mk_kb (kbz_and (fst (to_kb s x)) (snd (to_kb s x)) ones64 mz).

Definition a_and_lit (s : store) (x : xv) (m : w64) : xv :=
  let mz := wZ m in
  match low_mask_bits mz with
  | Some k =>
      match xrange s x with
      | Some (lo, hi) => if (0 <=? lo) && (hi <=? mz) then x else
          match xform s x with
          | Some f => match lshr s f k with Some g => of_form (lsub f (lscale (2 ^ k) g)) | None => kb_and_lit s x mz end
          | None => kb_and_lit s x mz
          end
      | None => kb_and_lit s x mz
      end
  | None =>
      match low_mask_bits (two64 - 1 - mz) with
      | Some k =>
          match xform s x with
          | Some f => match lshr s f k with Some g => of_form (lscale (2 ^ k) g) | None => kb_and_lit s x mz end
          | None => kb_and_lit s x mz
          end
      | None => kb_and_lit s x mz
      end
  end.

Lemma kb_and_lit_sound (ρ : valuation) (s : store) (x : xv) (m : w64) (a : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ (kb_and_lit s x (wZ m)) (bv_and a (wbv m)).
Proof.
  intros Hs Hx. unfold kb_and_lit. apply mk_kb_sound. rewrite bv_and_unsigned, wbv_unsigned.
  apply kbz_and_sound; [apply (to_kb_sound ρ); assumption|].
  unfold kb_val, ones64. rewrite Z.land_ones by lia. apply Z.mod_small. pose proof (wZ_range m). unfold two64 in *. lia.
Qed.

Lemma a_and_lit_sound (ρ : valuation) (s : store) (x : xv) (m : w64) (a : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ (a_and_lit s x m) (bv_and a (wbv m)).
Proof.
  intros Hs Hx. unfold a_and_lit. pose proof (bvu_range a) as Ha. pose proof (wZ_range m) as Hm.
  pose proof (kb_and_lit_sound ρ s x m a Hs Hx) as Hkb.
  assert (Ebv : bv_unsigned (bv_and a (wbv m)) = Z.land (bv_unsigned a) (wZ m)) by (rewrite bv_and_unsigned, wbv_unsigned; reflexivity).
  destruct (low_mask_bits (wZ m)) as [k|] eqn:Ek.
  - destruct (low_mask_bits_spec _ _ Ek) as [Hk Hmk].
    assert (Ebk : bv_unsigned (bv_and a (wbv m)) = bv_unsigned a mod 2 ^ k) by (rewrite Ebv, Hmk; apply land_low_mask; lia).
    destruct (xrange s x) as [[lo hi]|] eqn:Er; [|exact Hkb].
    pose proof (xrange_sound ρ s x a Hs Hx _ Er) as Hr. cbn [fst snd] in Hr.
    destruct ((0 <=? lo) && (hi <=? wZ m)) eqn:Ec.
    + apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      replace (bv_and a (wbv m)) with a; [exact Hx|].
      apply bv_eq. rewrite Ebk. symmetry. apply Z.mod_small. lia.
    + destruct (xform s x) as [f|] eqn:Ef; [|exact Hkb]. pose proof (xform_sound ρ s x a f Hs Hx Ef) as Hf.
      destruct (lshr s f k) as [g|] eqn:Eg; [|exact Hkb].
      apply of_form_sound. rewrite Ebk, leval_lsub, leval_lscale, (lshr_sound ρ s f g k Hs Hk Eg), <- Hf.
      rewrite <- Z.mod_eq by (apply Z.pow_nonzero; lia).
      symmetry. apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)).
      pose proof (Z.mod_le (bv_unsigned a) (2 ^ k) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
  - destruct (low_mask_bits (two64 - 1 - wZ m)) as [k|] eqn:Ek2; [|exact Hkb].
    destruct (low_mask_bits_spec _ _ Ek2) as [Hk Hmk].
    destruct (xform s x) as [f|] eqn:Ef; [|exact Hkb]. pose proof (xform_sound ρ s x a f Hs Hx Ef) as Hf.
    destruct (lshr s f k) as [g|] eqn:Eg; [|exact Hkb].
    assert (Hk64 : k <= 64).
    { destruct (Z_le_gt_dec k 64) as [|Hg]; [exact l|]. exfalso.
      pose proof (Z.pow_lt_mono_r 2 64 k ltac:(lia) ltac:(lia) ltac:(lia)). unfold two64 in *. lia. }
    apply of_form_sound. rewrite Ebv. replace (wZ m) with (two64 - 1 - (2 ^ k - 1)) by lia.
    rewrite land_high_mask by lia. rewrite leval_lscale, (lshr_sound ρ s f g k Hs Hk Eg), <- Hf.
    rewrite Z.mod_eq by (apply Z.pow_nonzero; lia).
    replace (bv_unsigned a - (bv_unsigned a - 2 ^ k * (bv_unsigned a / 2 ^ k))) with (2 ^ k * (bv_unsigned a / 2 ^ k)) by ring.
    symmetry. apply Z.mod_small.
    pose proof (Z.mul_div_le (bv_unsigned a) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.div_pos (bv_unsigned a) (2 ^ k) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). nia.
Qed.

Definition a_and (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_and a b)
  | _, XL m => a_and_lit s x m
  | XL m, _ => a_and_lit s y m
  | _, _ => mk_kb (kbz_and (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  end.

Lemma a_and_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_and s x y) (bv_and a b).
Proof.
  intros Hs Hx Hy.
  assert (Hkb : xv_val ρ (mk_kb (kbz_and (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))) (bv_and a b)).
  { apply mk_kb_sound. rewrite bv_and_unsigned. apply kbz_and_sound; apply (to_kb_sound ρ); assumption. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_and]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end);
    try (apply xv_XL in Hy; subst b; apply a_and_lit_sound; assumption);
    try (apply xv_XL in Hx; subst a; rewrite bv_and_comm; apply a_and_lit_sound; assumption).
  cbn [xv_val] in *. rewrite bv_and_unsigned, Hx, Hy, wZ_and. reflexivity.
Qed.

(* [comment removed for export] *)
Definition or_as_add (x : xv) (c : w64) : bool :=
  let k := Z.log2 (wZ c) + 1 in
  match x with
  | XS ts o => (k <=? tlow ts) && (wZ o mod 2 ^ k =? 0)
  | _ => false
  end.

Lemma lor_disj_add (u c : Z) : Z.land u c = 0 -> Z.lor u c = u + c.
Proof.
  intros H. rewrite Z.add_nocarry_lxor by exact H. apply Z.bits_inj'. intros i Hi. bits.
  assert (Hb : Z.testbit (Z.land u c) i = false) by (rewrite H; apply Z.bits_0).
  rewrite Z.land_spec in Hb. destruct (Z.testbit u i), (Z.testbit c i); cbn in *; congruence.
Qed.

Lemma land_low_zero (u c k : Z) : 0 <= k -> u mod 2 ^ k = 0 -> 0 <= c < 2 ^ k -> Z.land u c = 0.
Proof.
  intros Hk Hu Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k) as [Hl|Hg].
  - rewrite <- (Z.mod_pow2_bits_low u k i) by lia. rewrite Hu, Z.bits_0. reflexivity.
  - destruct (Z.eq_dec c 0) as [->|Hn]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 c i); [apply andb_false_r | lia |].
    apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma or_as_add_sound (ρ : valuation) (x : xv) (c : w64) (a : bv 64) :
  xv_val ρ x a -> or_as_add x c = true -> bv_or a (wbv c) = bv_add a (wbv c).
Proof.
  intros Hx H. destruct x as [|ts o| | | |]; cbn [or_as_add] in H; try discriminate.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.eqb_eq in H2.
  set (k := Z.log2 (wZ c) + 1) in *.
  assert (Hk0 : 0 <= k) by (unfold k; pose proof (Z.log2_nonneg (wZ c)); lia).
  assert (Hc : 0 <= wZ c < 2 ^ k).
  { pose proof (wZ_range c). unfold k. destruct (Z.eq_dec (wZ c) 0) as [E|E]; [rewrite E; cbn; lia|].
    split; [lia|]. apply Z.log2_spec. lia. }
  cbn [xv_val] in Hx. pose proof (kb_low_sound ρ ts o) as Hkl. unfold kb_val in Hkl.
  destruct (tlow_spec ρ ts) as [Ht [q Hq]].
  assert (Hu : bv_unsigned a mod 2 ^ k = 0).
  { rewrite Hx. unfold smod. rewrite Z.mod_mod_divide by (change two64 with (2 ^ 64); apply pow2_divide; lia).
    rewrite Hq. replace (q * 2 ^ tlow ts + wZ o) with (wZ o + (q * 2 ^ (tlow ts - k)) * 2 ^ k)
      by (rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia; replace (tlow ts - k + k) with (tlow ts) by lia; ring).
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). exact H2. }
  apply bv_eq. rewrite bv_or_unsigned, bv_add_unsigned, wbv_unsigned.
  rewrite lor_disj_add by (apply (land_low_zero _ _ k); lia).
  unfold bv_wrap. rewrite bv_modulus_64. symmetry. apply Z.mod_small.
  pose proof (bvu_range a).
  assert (Hk64 : k <= 64).
  { unfold k. pose proof (wZ_range c). destruct (Z.eq_dec (wZ c) 0) as [E|E]; [rewrite E; cbn; lia|].
    assert (Z.log2 (wZ c) < 64) by (apply Z.log2_lt_pow2; [lia | unfold two64 in *; lia]). lia. }
  assert (Hdiv : bv_unsigned a = 2 ^ k * (bv_unsigned a / 2 ^ k)).
  { pose proof (Z.div_mod (bv_unsigned a) (2 ^ k) ltac:(apply Z.pow_nonzero; lia)). lia. }
  assert (Hq2 : bv_unsigned a / 2 ^ k < 2 ^ (64 - k)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia.
    replace (k + (64 - k)) with 64 by lia. unfold two64 in *. lia. }
  assert (E64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  unfold two64 in *. split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Definition or_disj (s : store) (x y : xv) : bool :=
  match x with
  | XS ts o => match xrange s y with
               | Some (lo, hi) => (wZ o mod 2 ^ tlow ts =? 0) && (0 <=? lo) && (hi <? 2 ^ tlow ts)
               | None => false
               end
  | _ => false
  end.

Lemma or_disj_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> or_disj s x y = true -> bv_or a b = bv_add a b.
Proof.
  intros Hs Hx Hy H. destruct x as [|ts o| | | |]; cbn [or_disj] in H; try discriminate.
  destruct (xrange s y) as [[lo hi]|] eqn:Er; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H2 H1]. apply Z.eqb_eq in H2. apply Z.leb_le in H1. apply Z.ltb_lt in H3.
  pose proof (xrange_sound ρ s y b Hs Hy _ Er) as Hb. cbn [fst snd] in Hb.
  set (k := tlow ts) in *. destruct (tlow_spec ρ ts) as [Hk [q Hq]]. fold k in Hk, Hq.
  cbn [xv_val] in Hx.
  assert (Hu : bv_unsigned a mod 2 ^ k = 0).
  { rewrite Hx. unfold smod. rewrite Z.mod_mod_divide by (change two64 with (2 ^ 64); apply pow2_divide; lia).
    rewrite Hq. rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). exact H2. }
  apply bv_eq. rewrite bv_or_unsigned, bv_add_unsigned.
  rewrite lor_disj_add by (apply (land_low_zero _ _ k); lia).
  unfold bv_wrap. rewrite bv_modulus_64. symmetry. apply Z.mod_small.
  pose proof (bvu_range a).
  assert (Hdiv : bv_unsigned a = 2 ^ k * (bv_unsigned a / 2 ^ k)).
  { pose proof (Z.div_mod (bv_unsigned a) (2 ^ k) ltac:(apply Z.pow_nonzero; lia)). lia. }
  assert (Hq2 : bv_unsigned a / 2 ^ k < 2 ^ (64 - k)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia.
    replace (k + (64 - k)) with 64 by lia. unfold two64 in *. lia. }
  assert (E64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  unfold two64 in *. split; [lia|]. nia.
Qed.

Definition a_or (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_or a b)
  | _, XL c => if w_eqb c w_zero then x else if or_as_add x c then a_add s x y
               else mk_kb (kbz_or (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  | XL c, _ => if w_eqb c w_zero then y else if or_as_add y c then a_add s y x
               else mk_kb (kbz_or (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  | _, _ => if or_disj s x y then a_add s x y else if or_disj s y x then a_add s y x
            else mk_kb (kbz_or (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  end.

Lemma bv_or_zero_r (a : bv 64) : bv_or a (Z_to_bv 64 0) = a.
Proof. apply bv_eq. rewrite bv_or_unsigned. cbn. rewrite Z.lor_0_r. reflexivity. Qed.

Lemma a_or_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_or s x y) (bv_or a b).
Proof.
  intros Hs Hx Hy.
  assert (Hkb : xv_val ρ (mk_kb (kbz_or (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))) (bv_or a b)).
  { apply mk_kb_sound. rewrite bv_or_unsigned. apply kbz_or_sound; apply (to_kb_sound ρ); assumption. }
  assert (Hz : forall (c : w64) (d e : bv 64) v, w_eqb c w_zero = true -> xv_val ρ (XL c) d -> xv_val ρ v e ->
                 xv_val ρ v (bv_or e d) /\ xv_val ρ v (bv_or d e)).
  { intros c d e v Hc Hd He. rewrite w_eqb_spec, wZ_zero in Hc. apply Z.eqb_eq in Hc.
    cbn [xv_val] in Hd. assert (Ed : d = Z_to_bv 64 0) by (apply bv_eq; rewrite Hd, Hc; reflexivity). subst d.
    rewrite bv_or_zero_r, bv_or_comm, bv_or_zero_r. split; exact He. }
  assert (Hdj : or_disj s x y = true \/ or_disj s y x = true -> xv_val ρ (a_add s x y) (bv_or a b) /\ xv_val ρ (a_add s y x) (bv_or a b)).
  { intros [D|D].
    - rewrite (or_disj_sound ρ s x y a b Hs Hx Hy D). split; [apply a_add_sound; assumption|].
      replace (bv_add a b) with (bv_add b a) by (apply bv_eq; rewrite !bv_add_unsigned, Z.add_comm; reflexivity). apply a_add_sound; assumption.
    - rewrite bv_or_comm, (or_disj_sound ρ s y x b a Hs Hy Hx D). split; [|apply a_add_sound; assumption].
      replace (bv_add b a) with (bv_add a b) by (apply bv_eq; rewrite !bv_add_unsigned, Z.add_comm; reflexivity). apply a_add_sound; assumption. }
  assert (Hlast : xv_val ρ (if or_disj s x y then a_add s x y else if or_disj s y x then a_add s y x
            else mk_kb (kbz_or (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))) (bv_or a b)).
  { destruct (or_disj s x y) eqn:D1; [exact (proj1 (Hdj (or_introl eq_refl)))|].
    destruct (or_disj s y x) eqn:D2; [exact (proj2 (Hdj (or_intror eq_refl))) | exact Hkb]. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_or]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end); try exact Hlast.
  all: try (cbn [xv_val] in *; rewrite bv_or_unsigned, Hx, Hy, wZ_or; reflexivity).
  all: try (destruct (w_eqb yb w_zero) eqn:Ew; [exact (proj1 (Hz yb b a _ Ew Hy Hx))|];
            destruct (or_as_add _ yb) eqn:Eo; [| exact Hkb];
            pose proof Hy as Hy'; apply xv_XL in Hy'; subst b; rewrite (or_as_add_sound ρ _ yb a Hx Eo);
            apply a_add_sound; [exact Hs | exact Hx | apply xv_XL; reflexivity]).
  all: try (destruct (w_eqb xa w_zero) eqn:Ew; [exact (proj2 (Hz xa a b _ Ew Hx Hy))|];
            destruct (or_as_add _ xa) eqn:Eo; [| exact Hkb];
            pose proof Hx as Hx'; apply xv_XL in Hx'; subst a; rewrite bv_or_comm, (or_as_add_sound ρ _ xa b Hy Eo);
            apply a_add_sound; [exact Hs | exact Hy | apply xv_XL; reflexivity]).
Qed.

(* [comment removed for export] *)
Fixpoint xne_hole (fs : list fact) (c : Z) (ts : terms) : bool :=
  match fs with
  | [] => false
  | Fact (cf, tf) lo hi true :: r => (teqb tf ts && (lo <? cf - c) && (cf - c <? hi)) || xne_hole r c ts
  | _ :: r => xne_hole r c ts
  end.

Lemma xne_hole_sound (ρ : valuation) (fs : list fact) (c : Z) (ts : terms) :
  Forall (fact_sat ρ) fs -> xne_hole fs c ts = true -> c + teval ρ ts <> 0.
Proof.
  induction fs as [|[[cf tf] lo hi ho] r IH]; intros Hfs H; [discriminate|].
  inversion Hfs as [|? ? Hf Hr]; subst. cbn [xne_hole] in H. destruct ho; [|exact (IH Hr H)].
  apply orb_prop in H as [H|H]; [|exact (IH Hr H)].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply teqb_eq in H1. subst tf.
  apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  unfold fact_sat, leval in Hf. cbn [fc_hole fc_f fc_lo fc_hi fst snd] in Hf. lia.
Qed.

(* [comment removed for export] *)
Definition xs_ne (s : store) (x y : xv) : bool :=
  match xform s x, xform s y with
  | Some f, Some g => xne_hole (st_facts s) (fst (lsub f g)) (snd (lsub f g)) || xne_hole (st_facts s) (fst (lsub g f)) (snd (lsub g f))
  | _, _ => false
  end.

Lemma xs_ne_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xs_ne s x y = true -> bv_unsigned a <> bv_unsigned b.
Proof.
  intros Hs Hx Hy H. unfold xs_ne in H.
  destruct (xform s x) as [f|] eqn:Ef; [|discriminate H]. destruct (xform s y) as [g|] eqn:Eg; [|discriminate H].
  pose proof (xform_sound ρ s x a f Hs Hx Ef) as Ha. pose proof (xform_sound ρ s y b g Hs Hy Eg) as Hb.
  apply orb_prop in H as [H|H]; pose proof (xne_hole_sound ρ _ _ _ (proj2 Hs) H) as X;
    [fold (leval ρ (lsub f g)) in X | fold (leval ρ (lsub g f)) in X]; rewrite leval_lsub in X; lia.
Qed.

Definition a_xor (s : store) (x y : xv) : xv :=
  match x, y with
  | XL a, XL b => XL (w_xor a b)
  | XS t1 o1, XS t2 o2 => if teqb t1 t2 then (if w_eqb o1 o2 then XL w_zero else XR 1 (two64 - 1))
                          else if xs_ne s x y then XR 1 (two64 - 1)
                          else mk_kb (kbz_xor (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  | _, _ => mk_kb (kbz_xor (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))
  end.

Lemma a_xor_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_xor s x y) (bv_xor a b).
Proof.
  intros Hs Hx Hy.
  assert (Hkb : xv_val ρ (mk_kb (kbz_xor (fst (to_kb s x)) (snd (to_kb s x)) (fst (to_kb s y)) (snd (to_kb s y)))) (bv_xor a b)).
  { apply mk_kb_sound. rewrite bv_xor_unsigned. apply kbz_xor_sound; apply (to_kb_sound ρ); assumption. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_xor]; try (match goal with |- xv_val _ (mk_kb _) _ => exact Hkb end).
  - cbn [xv_val] in *. rewrite bv_xor_unsigned, Hx, Hy, wZ_xor. reflexivity.
  - destruct (teqb t1 t2) eqn:E1.
    2:{ destruct (xs_ne s (XS t1 o1) (XS t2 o2)) eqn:En; [|exact Hkb].
        pose proof (xs_ne_sound ρ s _ _ a b Hs Hx Hy En) as Hab. cbn [xv_val].
        pose proof (bvu_range (bv_xor a b)) as Hr.
        assert (Hne : bv_unsigned (bv_xor a b) <> 0) by (rewrite bv_xor_unsigned; intros E0; apply Z.lxor_eq in E0; exact (Hab E0)).
        lia. }
    apply teqb_eq in E1. subst t2.
    destruct (w_eqb o1 o2) eqn:E2.
    + rewrite w_eqb_spec in E2. apply Z.eqb_eq in E2.
      apply wZ_inj in E2. subst o2. cbn [xv_val] in *.
      rewrite bv_xor_unsigned, Hx, Hy, Z.lxor_nilpotent. reflexivity.
    + (* [comment removed for export] *)
      rewrite w_eqb_spec in E2. apply Z.eqb_neq in E2. cbn [xv_val] in *.
      pose proof (bvu_range (bv_xor a b)) as Hr.
      assert (Hne : bv_unsigned (bv_xor a b) <> 0).
      { rewrite bv_xor_unsigned. intros E0. apply Z.lxor_eq in E0. rewrite Hx, Hy in E0. unfold smod in E0.
        pose proof (wZ_range o1) as R1. pose proof (wZ_range o2) as R2.
        assert (Em : (wZ o1 - wZ o2) mod two64 = 0).
        { replace (wZ o1 - wZ o2) with ((teval ρ t1 + wZ o1) - (teval ρ t1 + wZ o2)) by ring.
          rewrite Zminus_mod, E0, Z.sub_diag. apply Z.mod_0_l. unfold two64; lia. }
        apply Z.mod_divide in Em; [|unfold two64; lia]. destruct Em as [q Hq].
        assert (q = 0) by (unfold two64 in *; nia). subst q. lia. }
      lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xb_eqb (a b : xb) : bool :=
  match a, b with
  | BL x, BL y => (x =? y)%uint63
  | BF t1 o1 i1, BF t2 o2 i2 => teqb t1 t2 && w_eqb o1 o2 && Nat.eqb i1 i2
  | _, _ => false
  end.

Fixpoint xbl_eqb (l1 l2 : list xb) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => xb_eqb a b && xbl_eqb r1 r2
  | _, _ => false
  end.

Lemma xb_eqb_det (ρ : valuation) (a b : xb) (u v : Z) : xb_eqb a b = true -> xb_z ρ a u -> xb_z ρ b v -> u = v.
Proof.
  intros H Ha Hb. destruct a as [x| |t1 o1 i1], b as [y| |t2 o2 i2]; cbn [xb_eqb xb_z] in *; try discriminate.
  - apply Uint63.eqb_spec in H. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply teqb_eq in H1.
    rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2. apply Nat.eqb_eq in H3. subst. reflexivity.
Qed.

Lemma xbl_eqb_nth (ρ : valuation) (l1 l2 : list xb) (i : nat) (u v : Z) :
  xbl_eqb l1 l2 = true -> (i < length l1)%nat -> xb_z ρ (nth i l1 BT) u -> xb_z ρ (nth i l2 BT) v -> u = v.
Proof.
  revert l2 i; induction l1 as [|a r IH]; intros [|b r2] i H Hi Ha Hb; cbn [xbl_eqb length] in *; try discriminate; [lia|].
  apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth] in *.
  - exact (xb_eqb_det ρ a b u v H1 Ha Hb).
  - apply (IH r2 i H2 ltac:(lia) Ha Hb).
Qed.

Lemma bytes_eq_word (u v : Z) : 0 <= u < two64 -> 0 <= v < two64 -> (forall i, (i < 8)%nat -> zbyte u i = zbyte v i) -> u = v.
Proof.
  intros Hu Hv H. rewrite <- (Z.mod_small u (2 ^ (8 * Z.of_nat 8))) by (unfold two64 in *; cbn; lia).
  rewrite <- (Z.mod_small v (2 ^ (8 * Z.of_nat 8))) by (unfold two64 in *; cbn; lia).
  rewrite <- !zcombine_bytes by lia. f_equal. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Definition ivl_cmp (a b : option ivl) : option bool :=
  match a, b with
  | Some (xl, xh), Some (yl, yh) => if xh <? yl then Some true else if yh <=? xl then Some false else None
  | _, _ => None
  end.

Definition a_ltu (s : store) (x y : xv) : option bool :=
  match x, y with
  | XL a, XL b => Some (w_ltu a b)
  | _, _ =>
      match xform s x, xform s y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if hi <? 0 then Some true else if 0 <=? lo then Some false else ivl_cmp (xrange s x) (xrange s y)
          | None => ivl_cmp (xrange s x) (xrange s y)
          end
      | _, _ => ivl_cmp (xrange s x) (xrange s y)
      end
  end.

Lemma ivl_cmp_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> ivl_cmp (xrange s x) (xrange s y) = Some r -> r = (bv_unsigned a <? bv_unsigned b).
Proof.
  intros Hs Hx Hy Hm. unfold ivl_cmp in Hm.
  destruct (xrange s x) as [[xl xh]|] eqn:Ex; destruct (xrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
  pose proof (xrange_sound ρ s x a Hs Hx _ Ex) as Hrx; pose proof (xrange_sound ρ s y b Hs Hy _ Ey) as Hry.
  cbn [fst snd] in Hrx, Hry.
  destruct (Z.ltb_spec xh yl); [injection Hm as <-; symmetry; apply Z.ltb_lt; lia|].
  destruct (Z.leb_spec yh xl); [injection Hm as <-; symmetry; apply Z.ltb_ge; lia | discriminate].
Qed.

Lemma a_ltu_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_ltu s x y = Some r -> r = bv_ltu a b.
Proof.
  intros Hs Hx Hy H. unfold bv_ltu.
  assert (Hgen : (match xform s x, xform s y with
                    | Some f, Some g =>
                        match lrange s (lsub f g) with
                        | Some (lo, hi) => if hi <? 0 then Some true else if 0 <=? lo then Some false else ivl_cmp (xrange s x) (xrange s y)
                        | None => ivl_cmp (xrange s x) (xrange s y)
                        end
                    | _, _ => ivl_cmp (xrange s x) (xrange s y)
                    end) = Some r -> r = (bv_unsigned a <? bv_unsigned b)).
  { intros Hm. destruct (xform s x) as [f|] eqn:Ef; destruct (xform s y) as [g|] eqn:Eg;
      try (exact (ivl_cmp_sound ρ s x y a b r Hs Hx Hy Hm)).
    pose proof (xform_sound ρ s x a f Hs Hx Ef) as Hf. pose proof (xform_sound ρ s y b g Hs Hy Eg) as Hg.
    destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:El; [|exact (ivl_cmp_sound ρ s x y a b r Hs Hx Hy Hm)].
    pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub, <- Hf, <- Hg in Hr.
    destruct (Z.ltb_spec hi 0); [injection Hm as <-; symmetry; apply Z.ltb_lt; lia|].
    destruct (Z.leb_spec 0 lo); [injection Hm as <-; symmetry; apply Z.ltb_ge; lia|].
    exact (ivl_cmp_sound ρ s x y a b r Hs Hx Hy Hm). }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_ltu] in H;
    try (apply (Hgen H)).
  injection H as <-. cbn [xv_val] in *. rewrite Hx, Hy. apply w_ltu_spec.
Qed.

(* [comment removed for export] *)
Definition kb_differ (p q : Z * Z) : bool := negb (Z.land (Z.lxor (snd p) (snd q)) (Z.land (fst p) (fst q)) =? 0).

Lemma kb_differ_sound (p q : Z * Z) (u v : Z) :
  kb_val (fst p) (snd p) u -> kb_val (fst q) (snd q) v -> kb_differ p q = true -> u <> v.
Proof.
  intros H1 H2 H E. subst v. unfold kb_differ in H. apply negb_true_iff in H. apply Z.eqb_neq in H. apply H.
  unfold kb_val in *. rewrite <- H1, <- H2. apply Z.bits_inj'. intros i Hi. bits. rewrite Z.bits_0.
  destruct (Z.testbit u i), (Z.testbit (fst p) i), (Z.testbit (fst q) i); reflexivity.
Qed.

Definition a_eq (s : store) (x y : xv) : option bool :=
  match x, y with
  | XL a, XL b => Some (w_eqb a b)
  | XS t1 o1, XS t2 o2 =>
      if teqb t1 t2 then Some (w_eqb o1 o2) else
      match xform s x, xform s y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else None
          | None => None
          end
      | _, _ => None
      end
  | XB l1, XB l2 => if xbl_eqb l1 l2 then Some true else None
  | _, _ =>
      match xform s x, xform s y with
      | Some f, Some g =>
          match lrange s (lsub f g) with
          | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else if (lo =? 0) && (hi =? 0) then Some true else None
          | None => None
          end
      | _, _ =>
          if kb_differ (to_kb s x) (to_kb s y) then Some false else
          match xrange s x, xrange s y with
          | Some (xl, xh), Some (yl, yh) => if (xh <? yl) || (yh <? xl) then Some false else None
          | _, _ => None
          end
      end
  end.

Lemma a_eq_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_eq s x y = Some r -> r = bv_eqb a b.
Proof.
  intros Hs Hx Hy H. unfold bv_eqb. pose proof (bvu_range a) as Ha. pose proof (bvu_range b) as Hb.
  assert (Hform : forall f g, xform s x = Some f -> xform s y = Some g ->
            forall lo hi, lrange s (lsub f g) = Some (lo, hi) -> lo <= bv_unsigned a - bv_unsigned b <= hi).
  { intros f g Ef Eg lo hi El. pose proof (xform_sound ρ s x a f Hs Hx Ef) as Hf. pose proof (xform_sound ρ s y b g Hs Hy Eg) as Hg.
    pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub, <- Hf, <- Hg in Hr. exact Hr. }
  assert (Hgen : forall d, (bv_unsigned a =? bv_unsigned b) = d ->
                   (match xform s x, xform s y with
                    | Some f, Some g =>
                        match lrange s (lsub f g) with
                        | Some (lo, hi) => if (hi <? 0) || (0 <? lo) then Some false else if (lo =? 0) && (hi =? 0) then Some true else None
                        | None => None
                        end
                    | _, _ =>
                        if kb_differ (to_kb s x) (to_kb s y) then Some false else
                        match xrange s x, xrange s y with
                        | Some (xl, xh), Some (yl, yh) => if (xh <? yl) || (yh <? xl) then Some false else None
                        | _, _ => None
                        end
                    end) = Some r -> r = d).
  { intros d Hd Hm. destruct (xform s x) as [f|] eqn:Ef; destruct (xform s y) as [g|] eqn:Eg.
    1:{ destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:El; [|discriminate].
      pose proof (Hform f g eq_refl eq_refl lo hi El) as Hr. subst d. destruct ((hi <? 0) || (0 <? lo)) eqn:E1.
      + injection Hm as <-. symmetry. apply Z.eqb_neq. apply orb_prop in E1 as [E1|E1]; apply Z.ltb_lt in E1; lia.
      + destruct ((lo =? 0) && (hi =? 0)) eqn:E2; [|discriminate]. injection Hm as <-.
        apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. symmetry. apply Z.eqb_eq. lia. }
    all: destruct (kb_differ (to_kb s x) (to_kb s y)) eqn:Ek.
    all: try (injection Hm as <-; subst d; symmetry; apply Z.eqb_neq;
              exact (kb_differ_sound _ _ _ _ (to_kb_sound ρ s x a Hs Hx) (to_kb_sound ρ s y b Hs Hy) Ek)).
    all: destruct (xrange s x) as [[xl xh]|] eqn:Ex; destruct (xrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    all: pose proof (xrange_sound ρ s x a Hs Hx _ Ex) as Hrx; pose proof (xrange_sound ρ s y b Hs Hy _ Ey) as Hry.
    all: cbn [fst snd] in Hrx, Hry; subst d.
    all: destruct ((xh <? yl) || (yh <? xl)) eqn:E1; [|discriminate]; injection Hm as <-; symmetry; apply Z.eqb_neq.
    all: apply orb_prop in E1 as [E1|E1]; apply Z.ltb_lt in E1; lia. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_eq] in H;
    try (apply (Hgen _ eq_refl H)).
  - injection H as <-. cbn [xv_val] in *. rewrite Hx, Hy. apply w_eqb_spec.
  - destruct (teqb t1 t2) eqn:Et.
    + injection H as <-. apply teqb_eq in Et. subst t2. cbn [xv_val] in *. rewrite Hx, Hy. unfold smod.
      rewrite w_eqb_spec. destruct (Z.eqb_spec (wZ o1) (wZ o2)) as [E|E].
      * rewrite E. symmetry. apply Z.eqb_refl.
      * symmetry. apply Z.eqb_neq. intros Hm. apply E.
        pose proof (wZ_range o1). pose proof (wZ_range o2).
        assert (Hd : ((teval ρ t1 + wZ o1) - (teval ρ t1 + wZ o2)) mod two64 = 0).
        { rewrite Zminus_mod, Hm, Z.sub_diag. reflexivity. }
        replace ((teval ρ t1 + wZ o1) - (teval ρ t1 + wZ o2)) with (wZ o1 - wZ o2) in Hd by ring.
        apply Z.mod_divide in Hd; [|unfold two64; lia]. destruct Hd as [q Hq].
        assert (q = 0) by (unfold two64 in *; nia). subst q. lia.
    + destruct (xform s (XS t1 o1)) as [f|] eqn:Ef; destruct (xform s (XS t2 o2)) as [g|] eqn:Eg; try discriminate.
      destruct (lrange s (lsub f g)) as [[lo hi]|] eqn:El; [|discriminate].
      pose proof (Hform f g eq_refl eq_refl lo hi El) as Hr. destruct ((hi <? 0) || (0 <? lo)) eqn:E1; [|discriminate].
      injection H as <-. symmetry. apply Z.eqb_neq. apply orb_prop in E1 as [E1|E1]; apply Z.ltb_lt in E1; lia.
  - destruct (xbl_eqb l1 l2) eqn:El; [|discriminate]. injection H as <-. symmetry. apply Z.eqb_eq.
    cbn [xv_val] in Hx, Hy. destruct Hx as [Hl1 Hx]. destruct Hy as [Hl2 Hy].
    apply bytes_eq_word; [exact Ha | exact Hb|]. intros i Hi.
    apply (xbl_eqb_nth ρ l1 l2 i); [exact El | lia | apply Hx; exact Hi | apply Hy; exact Hi].
Qed.

Definition a_lts (s : store) (x y : xv) : option bool :=
  match x, y with
  | XL a, XL b => Some (w_lts a b)
  | _, _ =>
      match xrange s x, xrange s y with
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

Lemma a_lts_sound (ρ : valuation) (s : store) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_lts s x y = Some r -> r = bv_lts a b.
Proof.
  intros Hs Hx Hy H.
  assert (Hgen : (match xrange s x, xrange s y with
                  | Some (xl, xh), Some (yl, yh) =>
                      if (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63) then a_ltu s x y else None
                  | _, _ => None
                  end) = Some r -> r = bv_lts a b).
  { intros Hm. destruct (xrange s x) as [[xl xh]|] eqn:Ex; destruct (xrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    pose proof (xrange_sound ρ s x a Hs Hx _ Ex) as Hrx. pose proof (xrange_sound ρ s y b Hs Hy _ Ey) as Hry.
    cbn [fst snd] in Hrx, Hry.
    destruct ((0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)) eqn:Ec; [|discriminate].
    repeat (apply andb_prop in Ec as [Ec ?]). apply Z.leb_le in Ec.
    rewrite (a_ltu_sound ρ s x y a b r Hs Hx Hy Hm). unfold bv_lts, bv_ltu.
    rewrite !bv_signed_small; [reflexivity | | ]; split; try lia;
      match goal with H : (_ <? two63) = true |- _ => apply Z.ltb_lt in H end; lia. }
  destruct x as [xa|t1 o1|lo hi|m1 x1|l1|], y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; cbn [a_lts] in H; try (apply (Hgen H)).
  injection H as <-. apply xv_XL in Hx. apply xv_XL in Hy. subst. apply w_lts_bv.
Qed.

Definition a_branch (s : store) (bc : branch_cond) (x y : xv) : option bool :=
  match bc with
  | BC_EQ => a_eq s x y
  | BC_NE => option_map negb (a_eq s x y)
  | BC_LT => a_lts s x y
  | BC_GE => option_map negb (a_lts s x y)
  | BC_LTU => a_ltu s x y
  | BC_GEU => option_map negb (a_ltu s x y)
  end.

Lemma a_branch_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : xv) (a b : bv 64) (r : bool) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_branch s bc x y = Some r -> r = branch_taken bc a b.
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
Definition a_fork (s : store) (bc : branch_cond) (x y : xv) : option (list (store * bool)) :=
  match xform s x, xform s y with
  | Some f, Some g =>
      let d := lsub f g in
      let lt := [(sadd s d (- two64) (-1), true); (sadd s d 0 two64, false)] in
      let eq := [(sadd s d 0 0, true); (sadd s d (- two64) (-1), false); (sadd s d 1 two64, false)] in
      let small := match xrange s x, xrange s y with
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

Lemma a_fork_sound (ρ : valuation) (s : store) (bc : branch_cond) (x y : xv) (a b : bv 64) (l : list (store * bool)) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> a_fork s bc x y = Some l ->
  exists s' r, In (s', r) l /\ sat ρ s' /\ r = branch_taken bc a b.
Proof.
  intros Hs Hx Hy H. unfold a_fork in H.
  destruct (xform s x) as [f|] eqn:Ef; [|discriminate]. destruct (xform s y) as [g|] eqn:Eg; [|discriminate].
  pose proof (xform_sound ρ s x a f Hs Hx Ef) as Hf. pose proof (xform_sound ρ s y b g Hs Hy Eg) as Hg.
  pose proof (bvu_range a) as Ha. pose proof (bvu_range b) as Hb.
  set (d := lsub f g) in *.
  assert (Hd : leval ρ d = bv_unsigned a - bv_unsigned b) by (unfold d; rewrite leval_lsub, Hf, Hg; reflexivity).
  assert (Hlt : exists s' r, In (s', r) [(sadd s d (- two64) (-1), true); (sadd s d 0 two64, false)] /\ sat ρ s' /\ r = bv_ltu a b).
  { unfold bv_ltu. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b)).
    - exists (sadd s d (- two64) (-1)), true. split; [left; reflexivity|]. split; [apply sat_sadd; [exact Hs | lia] | reflexivity].
    - exists (sadd s d 0 two64), false. split; [right; left; reflexivity|]. split; [apply sat_sadd; [exact Hs | lia] | reflexivity]. }
  assert (Heq : exists s' r, In (s', r) [(sadd s d 0 0, true); (sadd s d (- two64) (-1), false); (sadd s d 1 two64, false)]
                             /\ sat ρ s' /\ r = bv_eqb a b).
  { unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)).
    - exists (sadd s d 0 0), true. split; [left; reflexivity|]. split; [apply sat_sadd; [exact Hs | lia] | reflexivity].
    - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned b)).
      + exists (sadd s d (- two64) (-1)), false. split; [right; left; reflexivity|]. split; [apply sat_sadd; [exact Hs | lia] | reflexivity].
      + exists (sadd s d 1 two64), false. split; [right; right; left; reflexivity|]. split; [apply sat_sadd; [exact Hs | lia] | reflexivity]. }
  assert (Hneg : forall (l0 : list (store * bool)) c, (exists s' r, In (s', r) l0 /\ sat ρ s' /\ r = c) ->
            exists s' r, In (s', r) (map (fun p => (fst p, negb (snd p))) l0) /\ sat ρ s' /\ r = negb c).
  { intros l0 c [s' [r [Hi [Hsat Hr]]]]. exists s', (negb r). split; [|split; [exact Hsat | rewrite Hr; reflexivity]].
    apply in_map_iff. exists (s', r). split; [reflexivity | exact Hi]. }
  assert (Hsmall : (match xrange s x, xrange s y with
             | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
             | _, _ => false
             end) = true -> bv_lts a b = bv_ltu a b).
  { intros Hc. destruct (xrange s x) as [[xl xh]|] eqn:Ex; destruct (xrange s y) as [[yl yh]|] eqn:Ey; try discriminate.
    pose proof (xrange_sound ρ s x a Hs Hx _ Ex). pose proof (xrange_sound ρ s y b Hs Hy _ Ey). cbn [fst snd] in *.
    repeat (apply andb_prop in Hc as [Hc ?]). apply Z.leb_le in Hc.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
    unfold bv_lts, bv_ltu. rewrite !bv_signed_small by lia. reflexivity. }
  set (small := match xrange s x, xrange s y with
                 | Some (xl, xh), Some (yl, yh) => (0 <=? xl) && (xh <? two63) && (0 <=? yl) && (yh <? two63)
                 | _, _ => false
                 end) in *.
  destruct bc; cbn [branch_taken].
  - injection H as <-. exact Heq.
  - injection H as <-. exact (Hneg [(sadd s d 0 0, true); (sadd s d (- two64) (-1), false); (sadd s d 1 two64, false)] _ Heq).
  - destruct small eqn:Ec; [|discriminate]. injection H as <-. rewrite (Hsmall eq_refl). exact Hlt.
  - destruct small eqn:Ec; [|discriminate]. injection H as <-. rewrite (Hsmall eq_refl).
    exact (Hneg [(sadd s d (- two64) (-1), true); (sadd s d 0 two64, false)] _ Hlt).
  - injection H as <-. exact Hlt.
  - injection H as <-. exact (Hneg [(sadd s d (- two64) (-1), true); (sadd s d 0 two64, false)] _ Hlt).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition a_bool (b : option bool) : xv :=
  match b with Some true => XL w_one | Some false => XL w_zero | None => XR 0 1 end.

Lemma a_bool_sound (ρ : valuation) (o : option bool) (c : bool) :
  (forall r, o = Some r -> r = c) -> xv_val ρ (a_bool o) (if c then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intros H. destruct o as [[]|]; cbn [a_bool xv_val].
  - rewrite <- (H true eq_refl). reflexivity.
  - rewrite <- (H false eq_refl). reflexivity.
  - destruct c; cbn [xv_val]; [change (bv_unsigned (Z_to_bv 64 1)) with 1 | change (bv_unsigned (Z_to_bv 64 0)) with 0]; lia.
Qed.

Definition a_alu64 (s : store) (op : aluop) (x y : xv) : xv :=
  match op with
  | ALU_ADD => a_add s x y
  | ALU_SUB => a_sub s x y
  | ALU_SLL => a_sll s x y
  | ALU_SLT => a_bool (a_lts s x y)
  | ALU_SLTU => a_bool (a_ltu s x y)
  | ALU_XOR => a_xor s x y
  | ALU_SRL => a_srl s x y
  | ALU_SRA => a_sra s x y
  | ALU_OR => a_or s x y
  | ALU_AND => a_and s x y
  end.

Lemma a_alu64_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_alu64 s op x y) (alu64 op a b).
Proof.
  intros Hs Hx Hy. unfold alu64, alu. destruct op; cbn [a_alu64].
  - apply a_add_sound; assumption.
  - apply a_sub_sound; assumption.
  - apply a_sll_sound; assumption.
  - apply a_bool_sound. intros r Hr. exact (a_lts_sound ρ s x y a b r Hs Hx Hy Hr).
  - apply a_bool_sound. intros r Hr. exact (a_ltu_sound ρ s x y a b r Hs Hx Hy Hr).
  - apply a_xor_sound; assumption.
  - apply a_srl_sound; assumption.
  - apply a_sra_sound; assumption.
  - apply a_or_sound; assumption.
  - apply a_and_sound; assumption.
Qed.

(* [comment removed for export] *)
Definition pow2_of (b : w64) : option Z :=
  let k := Z.log2 (wZ b) in if (0 <? wZ b) && (2 ^ k =? wZ b) then Some k else None.

Lemma pow2_of_spec (b : w64) (k : Z) : pow2_of b = Some k -> 0 <= k /\ wZ b = 2 ^ k.
Proof.
  unfold pow2_of. destruct ((0 <? wZ b) && (2 ^ Z.log2 (wZ b) =? wZ b)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply andb_prop in E as [_ E]. apply Z.eqb_eq in E. split; [apply Z.log2_nonneg | lia].
Qed.

Lemma shamt_lit (k : Z) : 0 <= k < 64 -> bv_unsigned (bv_and (wbv (wofZ k)) (Z_to_bv 64 63)) = k.
Proof.
  intros Hk. rewrite bv_and_unsigned, wbv_unsigned, wZ_wofZ, Z_to_bv_unsigned. change (bv_wrap 64 63) with (Z.ones 6).
  rewrite (Z.mod_small k) by (unfold two64; lia). rewrite Z.land_ones by lia. apply Z.mod_small. cbn. lia.
Qed.

Lemma divu_pow2 (a : bv 64) (yb : w64) (k : Z) : wZ yb = 2 ^ k -> 0 <= k < 64 ->
  bv_divu a (wbv yb) = bv_shiftr a (bv_and (wbv (wofZ k)) (Z_to_bv 64 63)).
Proof.
  intros Eb Hk. apply bv_eq. rewrite bv_divu_unsigned, bv_shiftr_unsigned, shamt_lit by exact Hk.
  rewrite wbv_unsigned, Eb. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Definition a_muldiv (s : store) (op : mulop) (x y : xv) : xv :=
  match op, x, y with
  | M_MUL, _, _ => a_mul s x y
  | _, XL a, XL b => XL (w_muldiv op a b)
  | M_DIVU, _, XL b => match pow2_of b with Some k => a_srl s x (XL (wofZ k)) | None => XT end
  | M_REMU, _, XL b => match pow2_of b with Some k => a_and s x (XL (wofZ (2 ^ k - 1))) | None => XT end
  | _, _, _ => XT
  end.

Lemma a_muldiv_sound (ρ : valuation) (s : store) (op : mulop) (x y : xv) (a b : bv 64) :
  sat ρ s -> xv_val ρ x a -> xv_val ρ y b -> xv_val ρ (a_muldiv s op x y) (mul_div op a b).
Proof.
  intros Hs Hx Hy. pose proof (bvu_range a) as Ha.
  destruct op; cbn [a_muldiv]; [apply a_mul_sound; assumption| ..];
    (destruct x as [xa|t1 o1|lo hi|m1 x1|l1|]; destruct y as [yb|t2 o2|lo2 hi2|m2 y2|l2|]; try exact I;
     try (apply xv_XL in Hx; apply xv_XL in Hy; subst; apply xv_XL; symmetry; apply w_muldiv_ok)).
  all: destruct (pow2_of yb) as [k|] eqn:Ek; try exact I; destruct (pow2_of_spec yb k Ek) as [Hk Eb].
  all: apply xv_XL in Hy; subst b; unfold mul_div.
  all: assert (Hb0 : bv_unsigned (wbv yb) =? 0 = false) by (rewrite wbv_unsigned, Eb; apply Z.eqb_neq; apply Z.pow_nonzero; lia).
  all: rewrite Hb0.
  all: assert (Hk64 : k < 64) by (destruct (Z_lt_le_dec k 64) as [|Hg]; [lia|];
        pose proof (Z.pow_le_mono_r 2 64 k ltac:(lia) Hg); pose proof (wZ_range yb); unfold two64 in *; lia).
  (* [comment removed for export] *)
  all: try (rewrite (divu_pow2 a yb k Eb ltac:(lia)); apply a_srl_sound; [exact Hs | exact Hx | apply xv_XL; reflexivity]).
  all: try (replace (bv_modu a (wbv yb)) with (bv_and a (wbv (wofZ (2 ^ k - 1))));
        [apply a_and_sound; [exact Hs | exact Hx | apply xv_XL; reflexivity]|];
        apply bv_eq; rewrite bv_and_unsigned, bv_modu_unsigned, !wbv_unsigned, wZ_wofZ, Eb;
        rewrite (Z.mod_small (2 ^ k - 1)) by (pose proof (Z.pow_lt_mono_r 2 k 64 ltac:(lia) ltac:(lia) Hk64);
            pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); unfold two64; lia);
        apply land_low_mask; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_XT (v : xv) : bool := match v with XT => true | _ => false end.

Lemma is_XT_spec (v : xv) : is_XT v = false -> v <> XT.
Proof. destruct v; cbn; congruence. Qed.

Definition xv_val32 (ρ : valuation) (v : xv) (X : bv 32) : Prop :=
  exists a : bv 64, xv_val ρ v a /\ bv_unsigned X = bv_unsigned a mod two32.

Lemma xv_val32_low32 (ρ : valuation) (v : xv) (a : bv 64) : xv_val ρ v a -> xv_val32 ρ v (low32 a).
Proof.
  intros H. exists a. split; [exact H|]. unfold low32. rewrite bv_extract_unsigned. unfold bv_wrap.
  change (bv_modulus 32) with two32. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma low32_of_XL (ρ : valuation) (x : w64) (X : bv 32) : xv_val32 ρ (XL x) X -> to_Z (w_low32 x) = bv_unsigned X.
Proof. intros [a [Ha HX]]. cbn [xv_val] in Ha. rewrite HX, Ha, phi_low32. reflexivity. Qed.

(* [comment removed for export] *)
Definition lit32 (s : store) (v : xv) : option w64 :=
  match v with
  | XL x => Some x
  | _ => let p := to_kb s v in if 32 <=? lowrun (fst p) then Some (wofZ (Z.land (snd p) (Z.ones 32))) else None
  end.

Lemma lit32_kb (ρ : valuation) (s : store) (v : xv) (a : bv 64) :
  sat ρ s -> xv_val ρ v a -> 32 <= lowrun (fst (to_kb s v)) ->
  bv_unsigned a mod two32 = bv_unsigned (wbv (wofZ (Z.land (snd (to_kb s v)) (Z.ones 32)))) mod two32.
Proof.
  intros Hs Ha E. pose proof (to_kb_sound ρ s _ a Hs Ha) as Hk.
  destruct (lowrun_spec (fst (to_kb s v))) as [_ Hb].
  pose proof (kb_mod _ _ _ 32 ltac:(lia) (fun i Hi => Hb i ltac:(lia)) Hk) as Hm.
  rewrite wbv_unsigned, wZ_wofZ, Z.land_ones by lia.
  rewrite (Z.mod_small (snd (to_kb s v) mod 2 ^ 32)) by (pose proof (Z.mod_pos_bound (snd (to_kb s v)) (2 ^ 32) ltac:(lia)); unfold two64; lia).
  change two32 with (2 ^ 32). rewrite Hm. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma lit32_sound (ρ : valuation) (s : store) (v : xv) (X : bv 32) (x : w64) :
  sat ρ s -> xv_val32 ρ v X -> lit32 s v = Some x -> xv_val32 ρ (XL x) X.
Proof.
  intros Hs [a [Ha HX]] H.
  assert (Hgen : (if 32 <=? lowrun (fst (to_kb s v)) then Some (wofZ (Z.land (snd (to_kb s v)) (Z.ones 32))) else None) = Some x ->
                 xv_val32 ρ (XL x) X).
  { intros H'. destruct (32 <=? lowrun (fst (to_kb s v))) eqn:E; [|discriminate]. injection H' as <-.
    apply Z.leb_le in E. exists (wbv (wofZ (Z.land (snd (to_kb s v)) (Z.ones 32)))). split; [apply xv_XL; reflexivity|].
    rewrite HX. apply (lit32_kb ρ s v a Hs Ha E). }
  destruct v as [xv0| | | | |]; cbn [lit32] in H; try (exact (Hgen H)).
  injection H as <-. exists a. split; [exact Ha | exact HX].
Qed.

Definition a_alu32 (s : store) (op : aluop) (x y : xv) : xv :=
  match lit32 s x, lit32 s y with
  | Some a, Some b => XL (w_sext32 (w_alu32 op (w_low32 a) (w_low32 b)))
  | _, _ =>
      match op with
      | ALU_ADD | ALU_SUB =>
          let r := match op with ALU_ADD => a_add s x y | _ => a_sub s x y end in
          match xrange s x, xrange s y, xrange s r with
          | Some (xl, xh), Some (yl, yh), Some (rl, rh) =>
              if (0 <=? xl) && (xh <? 2147483648) && (0 <=? yl) && (yh <? 2147483648) && (0 <=? rl) && (rh <? 2147483648)
              then r else XT
          | _, _, _ => XT
          end
      | _ => XT
      end
  end.

Lemma sext64_small (X : bv 32) : 0 <= bv_unsigned X < 2147483648 -> bv_unsigned (sext 64 X) = bv_unsigned X.
Proof.
  intros H. unfold sext. rewrite bv_sign_extend_unsigned.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 32) with two32. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 64) with two64.
  rewrite (Z.mod_small (bv_unsigned X + 2147483648)) by (unfold two32; lia).
  rewrite Z.mod_small by (unfold two64; lia). lia.
Qed.

Lemma alu32_addsub_small (op : aluop) (a b : bv 64) (X Y : bv 32) :
  op = ALU_ADD \/ op = ALU_SUB ->
  bv_unsigned X = bv_unsigned a mod two32 -> bv_unsigned Y = bv_unsigned b mod two32 ->
  0 <= bv_unsigned a < 2147483648 -> 0 <= bv_unsigned b < 2147483648 ->
  0 <= bv_unsigned (match op with ALU_ADD => bv_add a b | _ => bv_sub a b end) < 2147483648 ->
  sext 64 (alu32 op X Y) = (match op with ALU_ADD => bv_add a b | _ => bv_sub a b end).
Proof.
  intros Hop HX HY Ha Hb Hr. rewrite (Z.mod_small (bv_unsigned a)) in HX by (unfold two32; lia).
  rewrite (Z.mod_small (bv_unsigned b)) in HY by (unfold two32; lia).
  destruct Hop as [-> | ->]; cbn [alu32 alu] in *; apply bv_eq.
  - rewrite bv_add_z in Hr. rewrite Z.mod_small in Hr by (unfold two64; lia).
    rewrite sext64_small.
    + rewrite bv_add_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
      rewrite bv_add_z, !Z.mod_small by (unfold two32, two64; lia). reflexivity.
    + rewrite bv_add_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
      rewrite Z.mod_small by (unfold two32; lia). lia.
  - rewrite bv_sub_z in Hr.
    assert (Hge : bv_unsigned b <= bv_unsigned a).
    { destruct (Z_le_gt_dec (bv_unsigned b) (bv_unsigned a)) as [|Hg]; [lia|].
      replace (bv_unsigned a - bv_unsigned b) with ((bv_unsigned a - bv_unsigned b + two64) + (-1) * two64) in Hr by ring.
      rewrite Z.mod_add in Hr by (unfold two64; lia). rewrite Z.mod_small in Hr by (unfold two64; lia). unfold two64 in Hr. lia. }
    rewrite Z.mod_small in Hr by (unfold two64; lia).
    rewrite sext64_small.
    + rewrite bv_sub_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
      rewrite bv_sub_z, !Z.mod_small by (unfold two32, two64; lia). reflexivity.
    + rewrite bv_sub_unsigned, HX, HY. unfold bv_wrap. change (bv_modulus 32) with two32.
      rewrite Z.mod_small by (unfold two32; lia). lia.
Qed.

Lemma small_rule (ρ : valuation) (s : store) (op : aluop) (x y r : xv) (a b : bv 64) (X Y : bv 32) :
  op = ALU_ADD \/ op = ALU_SUB -> sat ρ s ->
  xv_val ρ x a -> bv_unsigned X = bv_unsigned a mod two32 -> xv_val ρ y b -> bv_unsigned Y = bv_unsigned b mod two32 ->
  xv_val ρ r (match op with ALU_ADD => bv_add a b | _ => bv_sub a b end) ->
  (match xrange s x, xrange s y, xrange s r with
   | Some (xl, xh), Some (yl, yh), Some (rl, rh) =>
       if (0 <=? xl) && (xh <? 2147483648) && (0 <=? yl) && (yh <? 2147483648) && (0 <=? rl) && (rh <? 2147483648)
       then r else XT
   | _, _, _ => XT
   end) <> XT ->
  xv_val ρ (match xrange s x, xrange s y, xrange s r with
   | Some (xl, xh), Some (yl, yh), Some (rl, rh) =>
       if (0 <=? xl) && (xh <? 2147483648) && (0 <=? yl) && (yh <? 2147483648) && (0 <=? rl) && (rh <? 2147483648)
       then r else XT
   | _, _, _ => XT
   end) (sext 64 (alu32 op X Y)).
Proof.
  intros Hop Hs Ha HX Hb HY Hr Hn.
  destruct (xrange s x) as [[xl xh]|] eqn:Erx; [|congruence].
  destruct (xrange s y) as [[yl yh]|] eqn:Ery; [|congruence].
  destruct (xrange s r) as [[rl rh]|] eqn:Err; [|congruence].
  destruct ((0 <=? xl) && (xh <? 2147483648) && (0 <=? yl) && (yh <? 2147483648) && (0 <=? rl) && (rh <? 2147483648)) eqn:Ec; [|congruence].
  repeat (apply andb_prop in Ec as [Ec ?]); apply Z.leb_le in Ec;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  pose proof (xrange_sound ρ s x a Hs Ha _ Erx). pose proof (xrange_sound ρ s y b Hs Hb _ Ery).
  pose proof (xrange_sound ρ s r _ Hs Hr _ Err). cbn [fst snd] in *.
  rewrite (alu32_addsub_small op a b X Y Hop HX HY ltac:(lia) ltac:(lia) ltac:(lia)). exact Hr.
Qed.

Lemma is_XT_true (v : xv) : is_XT v = true -> v = XT.
Proof. destruct v; cbn; congruence. Qed.

Lemma a_alu32_sound (ρ : valuation) (s : store) (op : aluop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_alu32 s op x y) (sext 64 (alu32 op X Y)).
Proof.
  intros Hs Hx Hy. unfold a_alu32.
  destruct (lit32 s x) as [xa|] eqn:Ex; destruct (lit32 s y) as [yb|] eqn:Ey.
  1:{ apply xv_XL. symmetry. apply w_op32_ok; apply (low32_of_XL ρ); eapply lit32_sound; eassumption. }
  all: destruct Hx as [a [Ha HX]]; destruct Hy as [b [Hb HY]].
  all: destruct op; try exact I.
  all: match goal with
       | |- xv_val _ ?G _ => destruct (is_XT G) eqn:E; [rewrite (is_XT_true _ E); exact I|]
       end.
  all: apply (small_rule ρ s _ x y _ a b X Y); try assumption;
       first [tauto | apply a_add_sound; assumption | apply a_sub_sound; assumption | apply is_XT_spec; exact E].
Qed.


Definition a_muldiv32 (s : store) (op : mulop) (x y : xv) : xv :=
  match lit32 s x, lit32 s y with
  | Some a, Some b => XL (w_sext32 (w_muldiv32 op (w_low32 a) (w_low32 b)))
  | _, _ => XT
  end.

Lemma a_muldiv32_sound (ρ : valuation) (s : store) (op : mulop) (x y : xv) (X Y : bv 32) :
  sat ρ s -> xv_val32 ρ x X -> xv_val32 ρ y Y -> xv_val ρ (a_muldiv32 s op x y) (sext 64 (mul_div op X Y)).
Proof.
  intros Hs Hx Hy. unfold a_muldiv32.
  destruct (lit32 s x) as [xa|] eqn:Ex; destruct (lit32 s y) as [yb|] eqn:Ey; try exact I.
  apply xv_XL. symmetry. apply w_sext32_ok. apply w_muldiv32_ok; apply (low32_of_XL ρ); eapply lit32_sound; eassumption.
Qed.
