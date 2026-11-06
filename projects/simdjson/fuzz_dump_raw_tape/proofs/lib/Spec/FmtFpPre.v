(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SoftFloat DoubleOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_to_u32 f128_of_u32 f128_of_i32.

Lemma u32_range : forall x, 0 <= u32 x < 2^32.
Proof. intros. unfold u32. apply Z.mod_pos_bound. lia. Qed.
Lemma u64_range : forall x, 0 <= u64 x < 2^64.
Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma u32_id : forall x, 0 <= x < 2^32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.
Lemma u64_id : forall x, 0 <= x < 2^64 -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small. lia. Qed.
Lemma s32_id : forall x, -2^31 <= x < 2^31 -> s32 x = x.
Proof. intros. unfold s32. rewrite Z.mod_small; lia. Qed.

Lemma lor_c_32_120 : forall c, 0 <= c -> c <> 120 -> c <> 88 -> (Z.lor c 32 =? 120) = false.
Proof.
  intros c Hc H1 H2. apply Z.eqb_neq. intros E.
  assert (Ht : forall i, 0 <= i -> i <> 5 -> Z.testbit c i = Z.testbit 120 i).
  { intros i Hi Hn. rewrite <- E, Z.lor_spec.
    replace (Z.testbit 32 i) with false; [now rewrite orb_false_r|].
    symmetry. change 32 with (2^5). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  destruct (Z.testbit c 5) eqn:B5.
  - apply H1. apply Z.bits_inj'. intros i Hi. destruct (Z.eq_dec i 5); [subst; rewrite B5; reflexivity| now apply Ht].
  - apply H2. apply Z.bits_inj'. intros i Hi. destruct (Z.eq_dec i 5); [subst; rewrite B5; reflexivity|].
    rewrite Ht by lia. change 120 with (Z.lor 88 32). rewrite Z.lor_spec.
    replace (Z.testbit 32 i) with false; [now rewrite orb_false_r|].
    symmetry. change 32 with (2^5). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Definition bitlen (x : Z) : Z := if 0 <? x then Z.log2 x + 1 else 0.
Lemma bitlen_nonneg : forall x, 0 <= bitlen x.
Proof. intros. unfold bitlen. destruct (Z.ltb_spec 0 x); [pose proof (Z.log2_nonneg x); lia| lia]. Qed.
Lemma bitlen_le32 : forall x, 0 <= x < 2^32 -> bitlen x <= 32.
Proof.
  intros x Hx. unfold bitlen. destruct (Z.ltb_spec 0 x); [|lia].
  assert (Z.log2 x < 32) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma bitlen_pos : forall x, 0 < x -> 1 <= bitlen x.
Proof. intros. unfold bitlen. destruct (Z.ltb_spec 0 x); [pose proof (Z.log2_nonneg x); lia|lia]. Qed.
Lemma bitlen_shiftr_lt : forall x s, 0 < x -> 1 <= s -> bitlen (Z.shiftr x s) < bitlen x.
Proof.
  intros x s Hx Hs. unfold bitlen. destruct (Z.ltb_spec 0 x); [|lia].
  destruct (Z.ltb_spec 0 (Z.shiftr x s)); [|pose proof (Z.log2_nonneg x); lia].
  rewrite Z.log2_shiftr by lia.
  rewrite Z.shiftr_div_pow2 in H0 by lia.
  assert (Hxs : 2 ^ s <= x).
  { destruct (Z.lt_ge_cases x (2^s)); [|lia]. rewrite Z.div_small in H0; lia. }
  assert (s <= Z.log2 x). { rewrite <- (Z.log2_pow2 s) by lia. apply Z.log2_le_mono. lia. }
  lia.
Qed.

Lemma znth_neg : forall l i, i < 0 -> znth l i = 0.
Proof. intros. unfold znth. destruct (Z.ltb_spec i 0); [reflexivity|lia]. Qed.
Lemma znth_ge : forall l i, zlength l <= i -> znth l i = 0.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply nth_overflow. lia.
Qed.
Lemma znth_app_l : forall l1 l2 i, i < zlength l1 -> znth (l1 ++ l2) i = znth l1 i.
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply app_nth1. lia.
Qed.
Lemma znth_app_r : forall l1 l2 i, zlength l1 <= i -> znth (l1 ++ l2) i = znth l2 (i - zlength l1).
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  destruct (Z.ltb_spec (i - Z.of_nat (length l1)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_In_or : forall l i, znth l i = 0 \/ In (znth l i) l.
Proof.
  intros l i. destruct (Z.lt_ge_cases i 0); [left; now apply znth_neg|].
  destruct (Z.lt_ge_cases i (zlength l)); [right; apply znth_range; lia| left; now apply znth_ge].
Qed.

Lemma znth_snoc0 : forall l i, znth (l ++ [0]) i = 0 \/ (0 <= i < zlength l /\ In (znth (l ++ [0]) i) l).
Proof.
  intros l i. destruct (Z.lt_ge_cases i 0); [left; now apply znth_neg|].
  destruct (Z.lt_ge_cases i (zlength l)).
  - right. split; [lia|]. rewrite znth_app_l by lia. apply znth_range. lia.
  - left. rewrite znth_app_r by lia. unfold znth. destruct (Z.ltb_spec (i - zlength l) 0); [reflexivity|].
    destruct (Z.to_nat (i - zlength l)) as [|[|n]]; reflexivity.
Qed.

Lemma znth_zrepeat : forall v n i, znth (zrepeat v n) i = (if (0 <=? i) && (i <? n) then v else 0).
Proof.
  intros v n i. Local Transparent zrepeat. unfold znth, zrepeat.
  destruct (Z.ltb_spec i 0); cbn [andb]. { destruct (Z.leb_spec 0 i); [lia|reflexivity]. }
  destruct (Z.leb_spec 0 i); [|lia]. cbn [andb].
  destruct (Z.ltb_spec i n).
  - apply nth_repeat_lt. lia.
  - apply nth_overflow. rewrite repeat_length. lia.
Qed.
Local Opaque zrepeat.

Definition W32 (x : list Z) : Prop := forall i, 0 <= znth x i < 2^32.
Lemma W32_zrepeat : forall n, W32 (zrepeat 0 n).
Proof. intros n i. rewrite znth_zrepeat. destruct (_ && _); lia. Qed.
Lemma W32_zupd : forall x i v, W32 x -> 0 <= v < 2^32 -> W32 (zupd x i v).
Proof.
  intros x i v Hw Hv j. destruct (Z.eq_dec i j).
  - subst. destruct (Z.lt_ge_cases j 0). { rewrite znth_neg by lia. lia. }
    destruct (Z.lt_ge_cases j (zlength x)).
    + rewrite znth_zupd_eq; [lia|lia].
    + rewrite znth_ge; [lia|]. rewrite zlength_zupd. lia.
  - rewrite znth_zupd_neq by lia. apply Hw.
Qed.
Lemma W32_u32 : forall x i v, W32 x -> W32 (zupd x i (u32 v)).
Proof. intros. apply W32_zupd; [assumption| apply u32_range]. Qed.

Lemma Z_lor_lt_pow2' : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof. intros. apply Z_lor_lt_pow2; lia. Qed.

Section Loops.
  Context {A B : Type}.

  Fixpoint wloop (cond : A -> bool) (body : A -> A) (fuel : nat) (s : A) : option A :=
    match fuel with O => None | S fu => if cond s then wloop cond body fu (body s) else Some s end.

  Lemma wloop_total : forall cond body (I : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true -> I (body s) /\ 0 <= m (body s) < m s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', wloop cond body fuel s = Some s' /\ I s' /\ cond s' = false.
  Proof.
    intros cond body I m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - destruct (Hstep s HI C) as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists s. auto.
  Qed.

  Fixpoint wbloop (cond : A -> bool) (body : A -> A + A) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => if cond s then match body s with inl s' => wbloop cond body fu s' | inr s' => Some s' end else Some s
    end.

  Lemma wbloop_total : forall cond body (I : A -> Prop) (Q : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true ->
       match body s with inl s' => I s' /\ 0 <= m s' < m s | inr s' => Q s' end) ->
    (forall s, I s -> cond s = false -> Q s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', wbloop cond body fuel s = Some s' /\ Q s'.
  Proof.
    intros cond body I Q m Hstep Hexit. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - specialize (Hstep s HI C). destruct (body s) as [s'|s'].
      + destruct Hstep as [HI' Hm']. apply IH; [exact HI'|lia].
      + exists s'. auto.
    - exists s. split; [reflexivity| now apply Hexit].
  Qed.

  Fixpoint bloop (body : A -> A + B) (fuel : nat) (s : A) : option B :=
    match fuel with
    | O => None
    | S fu => match body s with inl s' => bloop body fu s' | inr r => Some r end
    end.

  Lemma bloop_total : forall body (I : A -> Prop) (Q : B -> Prop) (m : A -> Z),
    (forall s, I s -> match body s with inl s' => I s' /\ 0 <= m s' < m s | inr r => Q r end) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists r, bloop body fuel s = Some r /\ Q r.
  Proof.
    intros body I Q m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. specialize (Hstep s HI). destruct (body s) as [s'|r].
    - destruct Hstep as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists r. auto.
  Qed.

  Fixpoint owloop (cond : A -> bool) (body : A -> option A) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => if cond s then match body s with Some s' => owloop cond body fu s' | None => None end else Some s
    end.

  Lemma owloop_total : forall cond body (I : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true -> exists s', body s = Some s' /\ I s' /\ 0 <= m s' < m s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', owloop cond body fuel s = Some s' /\ I s' /\ cond s' = false.
  Proof.
    intros cond body I m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - destruct (Hstep s HI C) as [s' (E & HI' & Hm')]. rewrite E. apply IH; [exact HI'|lia].
    - exists s. auto.
  Qed.

  Fixpoint obloop (body : A -> option (A + A)) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => match body s with Some (inl s') => obloop body fu s' | Some (inr s') => Some s' | None => None end
    end.

  Lemma obloop_total : forall body (I : A -> Prop) (Q : A -> Prop) (m : A -> Z),
    (forall s, I s -> exists r, body s = Some r /\
                 match r with inl s' => I s' /\ 0 <= m s' < m s | inr s' => Q s' end) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', obloop body fuel s = Some s' /\ Q s'.
  Proof.
    intros body I Q m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (Hstep s HI) as [r [E Hr]]. rewrite E. destruct r as [s'|s'].
    - destruct Hr as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists s'. auto.
  Qed.
End Loops.
