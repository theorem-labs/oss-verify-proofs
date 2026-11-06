(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zfupd (f : Z -> Z) (i v : Z) : Z -> Z :=
  fun j => if Z.eqb j i then v else f j.

Lemma zfupd_same : forall f i v, zfupd f i v i = v.
Proof. intros. unfold zfupd. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma zfupd_other : forall f i v j, j <> i -> zfupd f i v j = f j.
Proof. intros f i v j H. unfold zfupd. rewrite (proj2 (Z.eqb_neq j i) H). reflexivity. Qed.

Lemma zfupd_eq : forall f i v j, zfupd f i v j = (if Z.eqb j i then v else f j).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => zcount P lo n' + (if P (lo + Z.of_nat n') then 1 else 0)
  end.

(* [comment removed for export] *)
Lemma zcount_S : forall P lo n,
  zcount P lo (S n) = zcount P lo n + (if P (lo + Z.of_nat n) then 1 else 0).
Proof. reflexivity. Qed.

Lemma zcount_bounds : forall P lo n, 0 <= zcount P lo n <= Z.of_nat n.
Proof. induction n as [|n IH]; cbn [zcount]; [lia|]. destruct (P _); lia. Qed.

Lemma zcount_ext : forall P Q lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> P k = Q k) -> zcount P lo n = zcount Q lo n.
Proof.
  induction n as [|n IH]; intros E; cbn [zcount]; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma zcount_false : forall P lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> P k = false) -> zcount P lo n = 0.
Proof.
  induction n as [|n IH]; intros E; cbn [zcount]; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. lia.
Qed.

Lemma zcount_mono : forall P Q lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> P k = true -> Q k = true) ->
  zcount P lo n <= zcount Q lo n.
Proof.
  induction n as [|n IH]; intros E; cbn [zcount]; [lia|].
  assert (zcount P lo n <= zcount Q lo n) by (apply IH; intros k Hk HP; apply E; [lia|exact HP]).
  destruct (P (lo + Z.of_nat n)) eqn:EP.
  - rewrite (E (lo + Z.of_nat n)); [cbn; lia | lia | exact EP].
  - destruct (Q _); cbn; lia.
Qed.

(* [comment removed for export] *)

Lemma zcount_le_add : forall P lo n m, zcount P lo n <= zcount P lo (n + m).
Proof.
  induction m as [|m IH]; intros. - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. cbn [zcount]. destruct (P _); lia.
Qed.

Lemma zcount_app : forall P lo n m,
  zcount P lo (n + m) = zcount P lo n + zcount P (lo + Z.of_nat n) m.
Proof.
  induction m as [|m IH]; intros.
  - rewrite Nat.add_0_r. cbn. lia.
  - rewrite Nat.add_succ_r. cbn [zcount]. rewrite IH.
    replace (lo + Z.of_nat (n + m)) with (lo + Z.of_nat n + Z.of_nat m) by lia. lia.
Qed.

Lemma zcount_or_disj : forall P Q lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> P k = true -> Q k = true -> False) ->
  zcount (fun k => P k || Q k) lo n = zcount P lo n + zcount Q lo n.
Proof.
  induction n as [|n IH]; intros D; cbn [zcount]; [lia|].
  rewrite IH by (intros k Hk; apply D; lia).
  destruct (P (lo + Z.of_nat n)) eqn:EP; destruct (Q (lo + Z.of_nat n)) eqn:EQ; cbn; try lia.
  exfalso. apply (D (lo + Z.of_nat n)); auto; lia.
Qed.

Lemma zcount_true1 : forall P lo n k,
  lo <= k < lo + Z.of_nat n -> P k = true -> 1 <= zcount P lo n.
Proof.
  induction n as [|n IH]; intros k Hk HP; cbn [zcount]; [lia|].
  pose proof (zcount_bounds P lo n).
  destruct (Z.eq_dec k (lo + Z.of_nat n)) as [->|NE].
  - rewrite HP. cbn. lia.
  - assert (1 <= zcount P lo n) by (apply (IH k); [lia|auto]).
    destruct (P (lo + Z.of_nat n)); cbn; lia.
Qed.

Lemma zcount_cons : forall P lo n,
  zcount P lo (S n) = (if P lo then 1 else 0) + zcount P (lo + 1) n.
Proof.
  intros. change (S n) with (1 + n)%nat. rewrite zcount_app.
  change (zcount P lo 1) with (0 + (if P (lo + 0) then 1 else 0)).
  change (Z.of_nat 1) with 1. rewrite Z.add_0_r. lia.
Qed.

Lemma zcount_all : forall P lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> P k = true) -> zcount P lo n = Z.of_nat n.
Proof.
  induction n as [|n IH]; intros E; cbn [zcount]; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. lia.
Qed.

(* [comment removed for export] *)
Fixpoint zsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => zsum f lo n' + f (lo + Z.of_nat n')
  end.
(* [comment removed for export] *)
Lemma zsum_S : forall f lo n, zsum f lo (S n) = zsum f lo n + f (lo + Z.of_nat n). Proof. reflexivity. Qed.
Lemma zsum_ext : forall f g lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> f k = g k) -> zsum f lo n = zsum g lo n.
Proof.
  induction n as [|n IH]; intros E; cbn [zsum]; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.
Lemma zsum_bounds : forall f lo n a b,
  (forall k, lo <= k < lo + Z.of_nat n -> a <= f k <= b) ->
  Z.of_nat n * a <= zsum f lo n <= Z.of_nat n * b.
Proof.
  induction n as [|n IH]; intros a b E; cbn [zsum]; [lia|].
  specialize (IH a b ltac:(intros; apply E; lia)). specialize (E (lo + Z.of_nat n) ltac:(lia)). lia.
Qed.

Lemma zsum_app : forall f lo n m, zsum f lo (n + m) = zsum f lo n + zsum f (lo + Z.of_nat n) m.
Proof.
  induction m as [|m IH]; intros.
  - rewrite Nat.add_0_r. cbn. lia.
  - rewrite Nat.add_succ_r. cbn [zsum]. rewrite IH.
    replace (lo + Z.of_nat (n + m)) with (lo + Z.of_nat n + Z.of_nat m) by lia. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lor_shiftl1_bit : forall z b, 0 <= z -> 0 <= b <= 1 -> Z.lor (Z.shiftl z 1) b = 2 * z + b.
Proof.
  intros z b Hz Hb.
  assert (Eb : exists bb : bool, b = Z.b2z bb).
  { destruct (Z.eq_dec b 0) as [->|]; [exists false; reflexivity| exists true; cbn; lia]. }
  destruct Eb as [bb ->].
  rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  replace (z * 2) with (2 * z + Z.b2z false) by (cbn [Z.b2z]; lia).
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite !Z.testbit_0_r, Z.b2z_bit0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_succ_r by lia.
    replace (Z.testbit (Z.b2z bb) (Z.succ (n - 1))) with false; [now rewrite orb_false_r|].
    symmetry. destruct bb; [|apply Z.bits_0]. cbn [Z.b2z]. apply Z.bits_above_log2; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma opaque_23 : {z : Z | z = 23}. Proof. exists 23. reflexivity. Qed.
Definition BZ_MAX_CODE_LEN : Z := proj1_sig opaque_23.
Lemma BZ_MAX_CODE_LEN_eq : BZ_MAX_CODE_LEN = 23.
Proof. exact (proj2_sig opaque_23). Qed.
Lemma BZ_MAX_CODE_LEN_nat : Z.to_nat BZ_MAX_CODE_LEN = 23%nat.
Proof. now rewrite BZ_MAX_CODE_LEN_eq. Qed.
Definition BZ_MAX_ALPHA_SIZE : Z := 258.

(* [comment removed for export] *)
Fixpoint hb_permJ (len : Z -> Z) (i : Z) (j : Z) (n : nat) (perm : Z -> Z) (pp : Z)
  : (Z -> Z) * Z :=
  match n with
  | O => (perm, pp)
  | S n' => if Z.eqb (len j) i
            then hb_permJ len i (j + 1) n' (zfupd perm pp j) (pp + 1)
            else hb_permJ len i (j + 1) n' perm pp
  end.

(* [comment removed for export] *)
Fixpoint hb_permI (len : Z -> Z) (alpha : Z) (i : Z) (n : nat) (perm : Z -> Z) (pp : Z)
  : (Z -> Z) * Z :=
  match n with
  | O => (perm, pp)
  | S n' => let r := hb_permJ len i 0 (Z.to_nat alpha) perm pp in
            hb_permI len alpha (i + 1) n' (fst r) (snd r)
  end.

(* [comment removed for export] *)
Fixpoint fill0 (f : Z -> Z) (i : Z) (n : nat) : Z -> Z :=
  match n with
  | O => f
  | S n' => fill0 (zfupd f i 0) (i + 1) n'
  end.

(* [comment removed for export] *)
Fixpoint hb_count (len : Z -> Z) (i : Z) (n : nat) (base : Z -> Z) : Z -> Z :=
  match n with
  | O => base
  | S n' => hb_count len (i + 1) n' (zfupd base (len i + 1) (base (len i + 1) + 1))
  end.

(* [comment removed for export] *)
Fixpoint hb_accum (i : Z) (n : nat) (base : Z -> Z) : Z -> Z :=
  match n with
  | O => base
  | S n' => hb_accum (i + 1) n' (zfupd base i (base i + base (i - 1)))
  end.

(* [comment removed for export] *)
Fixpoint hb_limit (base : Z -> Z) (i : Z) (n : nat) (limit : Z -> Z) (vec : Z)
  : (Z -> Z) * Z :=
  match n with
  | O => (limit, vec)
  | S n' => let vec1 := vec + (base (i + 1) - base i) in
            hb_limit base (i + 1) n' (zfupd limit i (vec1 - 1)) (Z.shiftl vec1 1)
  end.

(* [comment removed for export] *)
Fixpoint hb_base (limit : Z -> Z) (i : Z) (n : nat) (base : Z -> Z) : Z -> Z :=
  match n with
  | O => base
  | S n' => hb_base limit (i + 1) n' (zfupd base i (Z.shiftl (limit (i - 1) + 1) 1 - base i))
  end.

(* [comment removed for export] *)
Definition span (lo hi : Z) : nat := Z.to_nat (hi - lo + 1).

(* [comment removed for export] *)
Definition hb_create (limit0 base0 perm0 len : Z -> Z) (minLen maxLen alpha : Z)
  : (Z -> Z) * (Z -> Z) * (Z -> Z) :=
  let pp_ := hb_permI len alpha minLen (span minLen maxLen) perm0 0 in
  let perm := fst pp_ in
  let base1 := fill0 base0 0 (Z.to_nat BZ_MAX_CODE_LEN) in
  let base2 := hb_count len 0 (Z.to_nat alpha) base1 in
  let base3 := hb_accum 1 (Z.to_nat (BZ_MAX_CODE_LEN - 1)) base2 in
  let limit1 := fill0 limit0 0 (Z.to_nat BZ_MAX_CODE_LEN) in
  let lv := hb_limit base3 minLen (span minLen maxLen) limit1 0 in
  let limit := fst lv in
  let base := hb_base limit (minLen + 1) (span (minLen + 1) maxLen) base3 in
  (limit, base, perm).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_permJ_S : forall len i j n perm pp,
  hb_permJ len i j (S n) perm pp =
  if Z.eqb (len j) i then hb_permJ len i (j + 1) n (zfupd perm pp j) (pp + 1)
  else hb_permJ len i (j + 1) n perm pp.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hb_permI_S : forall len alpha i n perm pp,
  hb_permI len alpha i (S n) perm pp =
  let r := hb_permJ len i 0 (Z.to_nat alpha) perm pp in hb_permI len alpha (i + 1) n (fst r) (snd r).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fill0_S : forall f i n, fill0 f i (S n) = fill0 (zfupd f i 0) (i + 1) n. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hb_count_S : forall len i n base,
  hb_count len i (S n) base = hb_count len (i + 1) n (zfupd base (len i + 1) (base (len i + 1) + 1)).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hb_accum_S : forall i n base,
  hb_accum i (S n) base = hb_accum (i + 1) n (zfupd base i (base i + base (i - 1))).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hb_limit_S : forall base i n limit vec,
  hb_limit base i (S n) limit vec =
  let vec1 := vec + (base (i + 1) - base i) in
  hb_limit base (i + 1) n (zfupd limit i (vec1 - 1)) (Z.shiftl vec1 1).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hb_base_S : forall limit i n base,
  hb_base limit i (S n) base = hb_base limit (i + 1) n (zfupd base i (Z.shiftl (limit (i - 1) + 1) 1 - base i)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fill0_snoc : forall n f i, fill0 f i (S n) = zfupd (fill0 f i n) (i + Z.of_nat n) 0.
Proof.
  induction n as [|n IH]; intros.
  - cbn. now rewrite Z.add_0_r.
  - rewrite fill0_S, IH, fill0_S. f_equal. lia.
Qed.

Lemma hb_count_snoc : forall n len i base,
  hb_count len i (S n) base =
  let b := hb_count len i n base in let k := i + Z.of_nat n in zfupd b (len k + 1) (b (len k + 1) + 1).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add]. now rewrite Z.add_0_r.
  - rewrite hb_count_S, IH, hb_count_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

Lemma hb_accum_snoc : forall n i base,
  hb_accum i (S n) base =
  let b := hb_accum i n base in let k := i + Z.of_nat n in zfupd b k (b k + b (k - 1)).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add Z.sub]. now rewrite Z.add_0_r.
  - rewrite hb_accum_S, IH, hb_accum_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

Lemma hb_permJ_snoc : forall n len i j perm pp,
  hb_permJ len i j (S n) perm pp =
  let r := hb_permJ len i j n perm pp in
  let k := j + Z.of_nat n in
  if Z.eqb (len k) i then (zfupd (fst r) (snd r) k, snd r + 1) else r.
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add Z.eqb]. rewrite Z.add_0_r. destruct (len j =? i); reflexivity.
  - rewrite hb_permJ_S. destruct (len j =? i) eqn:E;
      rewrite IH; rewrite hb_permJ_S, E; cbn zeta;
      now replace (j + 1 + Z.of_nat n) with (j + Z.of_nat (S n)) by lia.
Qed.

Lemma hb_permI_snoc : forall n len alpha i perm pp,
  hb_permI len alpha i (S n) perm pp =
  let r := hb_permI len alpha i n perm pp in
  hb_permJ len (i + Z.of_nat n) 0 (Z.to_nat alpha) (fst r) (snd r).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add hb_permJ Z.to_nat]. rewrite Z.add_0_r. destruct (hb_permJ _ _ _ _ _ _); reflexivity.
  - rewrite hb_permI_S. cbn zeta. rewrite IH, hb_permI_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

Lemma hb_limit_snoc : forall n base i limit vec,
  hb_limit base i (S n) limit vec =
  let r := hb_limit base i n limit vec in
  let k := i + Z.of_nat n in
  let vec1 := snd r + (base (k + 1) - base k) in
  (zfupd (fst r) k (vec1 - 1), Z.shiftl vec1 1).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add Z.sub Z.shiftl]. now rewrite Z.add_0_r.
  - rewrite hb_limit_S. cbn zeta. rewrite IH, hb_limit_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

Lemma hb_base_snoc : forall n limit i base,
  hb_base limit i (S n) base =
  let b := hb_base limit i n base in let k := i + Z.of_nat n in
  zfupd b k (Z.shiftl (limit (k - 1) + 1) 1 - b k).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add Z.sub Z.shiftl]. now rewrite Z.add_0_r.
  - rewrite hb_base_S, IH, hb_base_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition occ (sym : Z -> Z) (n : nat) (b : Z) : Z := zcount (fun k => sym k =? b) 0 n.

Lemma occ_0 : forall sym b, occ sym 0 b = 0. Proof. reflexivity. Qed.
Lemma occ_S : forall sym n b,
  occ sym (S n) b = occ sym n b + (if sym (Z.of_nat n) =? b then 1 else 0).
Proof. intros. unfold occ. rewrite zcount_S. now rewrite Z.add_0_l. Qed.
Lemma occ_bounds : forall sym n b, 0 <= occ sym n b <= Z.of_nat n.
Proof. intros. unfold occ. apply zcount_bounds. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma occ_le_mono : forall sym n m b, (n <= m)%nat -> occ sym n b <= occ sym m b.
Proof. intros. unfold occ. replace m with (n + (m - n))%nat by lia. apply zcount_le_add. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hist_ok (unz sym : Z -> Z) (n : nat) : Prop :=
  forall b, 0 <= b < 256 -> unz b = occ sym n b.

(* [comment removed for export] *)
Fixpoint cf_copy (unz : Z -> Z) (i : Z) (n : nat) (cf : Z -> Z) : Z -> Z :=
  match n with
  | O => cf
  | S n' => cf_copy unz (i + 1) n' (zfupd cf i (unz (i - 1)))
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition psum (unz : Z -> Z) (k : Z) : Z := zsum unz 0 (Z.to_nat k).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lo8 (x : Z) : Z := Z.land x 255.

Fixpoint tinv (i : Z) (n : nat) (tt cf : Z -> Z) : (Z -> Z) * (Z -> Z) :=
  match n with
  | O => (tt, cf)
  | S n' => let uc := lo8 (tt i) in
            let idx := cf uc in
            tinv (i + 1) n' (zfupd tt idx (Z.lor (tt idx) (Z.shiftl i 8))) (zfupd cf uc (idx + 1))
  end.
(* [comment removed for export] *)
Lemma tinv_S : forall i n tt cf,
  tinv i (S n) tt cf = let uc := lo8 (tt i) in let idx := cf uc in
    tinv (i + 1) n (zfupd tt idx (Z.lor (tt idx) (Z.shiftl i 8))) (zfupd cf uc (idx + 1)).
Proof. reflexivity. Qed.
Lemma tinv_snoc : forall n i tt cf,
  tinv i (S n) tt cf =
  let r := tinv i n tt cf in let k := i + Z.of_nat n in
  let uc := lo8 (fst r k) in let idx := snd r uc in
  (zfupd (fst r) idx (Z.lor (fst r idx) (Z.shiftl k 8)), zfupd (snd r) uc (idx + 1)).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[Z.add Z.lor Z.shiftl lo8]. now rewrite Z.add_0_r.
  - rewrite tinv_S. cbn zeta. rewrite IH, tinv_S. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_ll4 (ll4 : Z -> Z) (i : Z) : Z :=
  Z.land (Z.shiftr (ll4 (Z.shiftr i 1)) (Z.land (Z.shiftl i 2) 4)) 15.
Definition get_ll (ll16 ll4 : Z -> Z) (i : Z) : Z :=
  Z.lor (ll16 i) (Z.shiftl (get_ll4 ll4 i) 16).
Definition set_ll4 (ll4 : Z -> Z) (i n : Z) : Z -> Z :=
  let a := Z.shiftr i 1 in
  if Z.land i 1 =? 0 then zfupd ll4 a (Z.lor (Z.land (ll4 a) 240) n)
  else zfupd ll4 a (Z.lor (Z.land (ll4 a) 15) (Z.shiftl n 4)).
Definition set_ll (ll16 ll4 : Z -> Z) (i n : Z) : (Z -> Z) * (Z -> Z) :=
  (zfupd ll16 i (Z.land n 65535), set_ll4 ll4 i (Z.shiftr n 16)).

(* [comment removed for export] *)
Fixpoint tvec (i : Z) (n : nat) (ll16 ll4 cfc : Z -> Z) : (Z -> Z) * (Z -> Z) * (Z -> Z) :=
  match n with
  | O => (ll16, ll4, cfc)
  | S n' => let uc := lo8 (ll16 i) in
            let v := cfc uc in
            let p := set_ll ll16 ll4 i v in
            tvec (i + 1) n' (fst p) (snd p) (zfupd cfc uc (v + 1))
  end.
(* [comment removed for export] *)
Lemma tvec_S : forall i n ll16 ll4 cfc,
  tvec i (S n) ll16 ll4 cfc = let uc := lo8 (ll16 i) in let v := cfc uc in let p := set_ll ll16 ll4 i v in
    tvec (i + 1) n (fst p) (snd p) (zfupd cfc uc (v + 1)).
Proof. reflexivity. Qed.

Lemma tvec_snoc : forall n i ll16 ll4 cfc,
  tvec i (S n) ll16 ll4 cfc =
  let '(a, b, c) := tvec i n ll16 ll4 cfc in
  let k := i + Z.of_nat n in let uc := lo8 (a k) in let v := c uc in
  let p := set_ll a b k v in (fst p, snd p, zfupd c uc (v + 1)).
Proof.
  induction n as [|n IH]; intros.
  - cbn -[set_ll lo8 zfupd Z.add]. now rewrite Z.add_0_r.
  - rewrite (tvec_S i (S n)). cbn zeta. rewrite IH. rewrite (tvec_S i n). cbn zeta.
    destruct (tvec (i + 1) n _ _ _) as [[a b] c]. cbn zeta.
    now replace (i + 1 + Z.of_nat n) with (i + Z.of_nat (S n)) by lia.
Qed.

(* [comment removed for export] *)
Definition pr_step (st : (Z -> Z) * (Z -> Z) * Z * Z) : (Z -> Z) * (Z -> Z) * Z * Z :=
  let '(ll16, ll4, i, j) := st in
  let tmp := get_ll ll16 ll4 j in
  let p := set_ll ll16 ll4 j i in
  (fst p, snd p, j, tmp).
Fixpoint pr_iter (k : nat) (st : (Z -> Z) * (Z -> Z) * Z * Z) : (Z -> Z) * (Z -> Z) * Z * Z :=
  match k with O => st | S k' => pr_step (pr_iter k' st) end.
Lemma pr_iter_S : forall k st, pr_iter (S k) st = pr_step (pr_iter k st). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition apr_step (st : (Z -> Z) * Z * Z) : (Z -> Z) * Z * Z :=
  let '(L, i, j) := st in (zfupd L j i, j, L j).
Fixpoint apr_iter (k : nat) (st : (Z -> Z) * Z * Z) : (Z -> Z) * Z * Z :=
  match k with O => st | S k' => apr_step (apr_iter k' st) end.
Lemma apr_iter_S : forall k st, apr_iter (S k) st = apr_step (apr_iter k st). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint iter (T : Z -> Z) (k : nat) (x : Z) : Z :=
  match k with O => x | S k' => T (iter T k' x) end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint first_ret (T : Z -> Z) (o : Z) (k0 fuel : nat) : nat :=
  match fuel with
  | O => k0
  | S f => if iter T k0 o =? o then k0 else first_ret T o (S k0) f
  end.
Definition cyc (T : Z -> Z) (n : nat) (o : Z) : nat := first_ret T o 1 n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint iif_loop (cftab : Z -> Z) (indx nb na : Z) (fuel : nat) : Z * Z :=
  match fuel with
  | O => (nb, na)
  | S f => let mid := Z.shiftr (nb + na) 1 in
           let nb' := if cftab mid <=? indx then mid else nb in
           let na' := if cftab mid <=? indx then na else mid in
           if na' - nb' =? 1 then (nb', na') else iif_loop cftab indx nb' na' f
  end.
Definition index_into_f (indx : Z) (cftab : Z -> Z) : Z := fst (iif_loop cftab indx 0 256 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MTFL_SIZE : Z := 16.

(* [comment removed for export] *)
Fixpoint mtf_init_inner (f : nat) (mtfa : Z -> Z) (ii jj kk : Z) : (Z -> Z) * Z :=
  match f with
  | O => (mtfa, kk)
  | S f' => mtf_init_inner f' (zfupd mtfa kk (ii * 16 + jj)) ii (jj - 1) (kk - 1)
  end.
Fixpoint mtf_init_outer (f : nat) (mtfa mb : Z -> Z) (ii kk : Z) : (Z -> Z) * (Z -> Z) * Z :=
  match f with
  | O => (mtfa, mb, kk)
  | S f' => let '(m', kk') := mtf_init_inner 16 mtfa ii 15 kk in
            mtf_init_outer f' m' (zfupd mb ii (kk' + 1)) (ii - 1) kk'
  end.
Definition mtf_init (mtfa mb : Z -> Z) : (Z -> Z) * (Z -> Z) :=
  let '(m, b, _) := mtf_init_outer 16 mtfa mb 15 4095 in (m, b).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint mtf_sh4 (f : nat) (mtfa : Z -> Z) (pp nn : Z) : (Z -> Z) * Z :=
  match f with
  | O => (mtfa, nn)
  | S f' => if 3 <? nn then
              let z := pp + nn in
              let m1 := zfupd mtfa z (mtfa (z - 1)) in
              let m2 := zfupd m1 (z - 1) (m1 (z - 2)) in
              let m3 := zfupd m2 (z - 2) (m2 (z - 3)) in
              let m4 := zfupd m3 (z - 3) (m3 (z - 4)) in
              mtf_sh4 f' m4 pp (nn - 4)
            else (mtfa, nn)
  end.
Fixpoint mtf_sh1 (f : nat) (mtfa : Z -> Z) (pp nn : Z) : (Z -> Z) * Z :=
  match f with
  | O => (mtfa, nn)
  | S f' => if 0 <? nn then mtf_sh1 f' (zfupd mtfa (pp + nn) (mtfa (pp + nn - 1))) pp (nn - 1) else (mtfa, nn)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mtf_pull (f : nat) (mtfa mb : Z -> Z) (lno : Z) : (Z -> Z) * (Z -> Z) * Z :=  (* [comment removed for export] *)
  match f with
  | O => (mtfa, mb, lno)
  | S f' => if 0 <? lno then
              let mb' := zfupd mb lno (mb lno - 1) in
              let mtfa' := zfupd mtfa (mb' lno) (mtfa (mb' (lno - 1) + MTFL_SIZE - 1)) in
              mtf_pull f' mtfa' mb' (lno - 1)
            else (mtfa, mb, lno)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mtf_inv (mb : Z -> Z) : Prop :=
  1 <= mb 0 /\ (forall l, 0 <= l < 15 -> mb l + 16 <= mb (l + 1)) /\ mb 15 <= 4080.
(* [comment removed for export] *)
Definition mtf_home (mb : Z -> Z) : Prop := forall l, 0 <= l < 16 -> mb l = 3840 + 16 * l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rand_upd (rNums : Z -> Z) (rNToGo rTPos : Z) : Z * Z :=
  if rNToGo =? 0 then
    let g := rNums rTPos in let p := rTPos + 1 in let p' := if p =? 512 then 0 else p in (g - 1, p')
  else (rNToGo - 1, rTPos).
(* [comment removed for export] *)
