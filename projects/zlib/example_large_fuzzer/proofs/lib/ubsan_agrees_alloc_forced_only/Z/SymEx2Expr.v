(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.   (* [comment removed for export] *)

Record venv : Type := VEnv {
  vv  : nat -> Z;
  vf1 : nat -> Z -> Z;
  vf2 : nat -> Z -> Z -> Z
}.

(* [comment removed for export] *)
Definition szwrap (k a : Z) : Z := (a + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bounds : Type := list (nat * Z).

Fixpoint blookup (l : bounds) (n : nat) : option Z :=
  match l with
  | [] => None
  | (m, b) :: rest => if Nat.eqb m n then Some b else blookup rest n
  end.

Definition vars_ok (E : venv) (vb : bounds) : Prop :=
  forall n b, blookup vb n = Some b -> 0 <= vv E n < b.

Definition funs_ok (E : venv) (fb : bounds) : Prop :=
  forall f b x, blookup fb f = Some b -> 0 <= vf1 E f x < b.

(* [comment removed for export] *)
Definition pow2_above (b : Z) : Z := 2 ^ (Z.log2_up b).

Definition omin (x y : option Z) : option Z :=
  match x, y with
  | Some a, Some b => Some (Z.min a b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.

Lemma land_upper : forall a b, 0 <= a -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; left; exact Ha).
  split; [exact H0|].
  (* [comment removed for export] *)
  assert (E : a = Z.lor (Z.land a b) (Z.ldiff a b)).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  assert (Hd : 0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha).
  assert (Hdis : Z.land (Z.land a b) (Z.ldiff a b) = 0).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hdis) as Hx.
  rewrite Z.lxor_lor in Hx by exact Hdis.
  lia.
Qed.

Lemma lor_lxor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n ->
  0 <= Z.lor a b < 2 ^ n /\ 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn.
  assert (Hta : forall k, n <= k -> Z.testbit a k = false).
  { intros k Hk. destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Htb : forall k, n <= k -> Z.testbit b k = false).
  { intros k Hk. destruct (Z.eq_dec b 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Hor0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (Hxor0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; split; try assumption.
  - destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lor a b) (Z.log2 (Z.lor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lor_spec, Hta, Htb in Ht by lia. discriminate.
  - destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lxor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lxor a b) (Z.log2 (Z.lxor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lxor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lxor_spec, Hta, Htb in Ht by lia. discriminate.
Qed.

Lemma szwrap_small : forall k a, 0 < k -> - 2 ^ (k - 1) <= a < 2 ^ (k - 1) -> szwrap k a = a.
Proof.
  intros k a Hk Ha. unfold szwrap.
  assert (2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (k - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma szwrap_eqm : forall k a, 0 < k -> (szwrap k a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zminus_mod_idemp_l.
  replace (a + 2 ^ (k - 1) - 2 ^ (k - 1)) with a by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mod_mod_le : forall a j k, 0 <= j <= k -> (a mod 2 ^ k) mod 2 ^ j = a mod 2 ^ j.
Proof.
  intros a j k Hjk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_mod_pow2 : forall a n i, 0 <= n -> 0 <= i ->
  Z.testbit (a mod 2 ^ n) i = if i <? n then Z.testbit a i else false.
Proof.
  intros a n i Hn Hi. destruct (Z.ltb_spec i n).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma lxor_mod : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2 ^ n = Z.lxor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !testbit_mod_pow2, Z.lxor_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section Smart.
Variable vb : bounds.
Variable fb : bounds.

(* [comment removed for export] *)
Definition mask_width (m : Z) : option Z :=
  if (0 <=? m) && (Z.eqb (2 ^ (Z.log2 (m + 1))) (m + 1)) then Some (Z.log2 (m + 1)) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Context (E : venv).
Context (Hv : vars_ok E vb).
Context (Hf : funs_ok E fb).

End Smart.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sem.
Variable vb : bounds.
Variable fb : bounds.

Context (E : venv).
Context (Hv : vars_ok E vb).
Context (Hf : funs_ok E fb).

End Sem.
