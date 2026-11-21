(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.

Module ZChkArith.

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition AMAGIC_IMAGE : Z := 983265 * 4294967296 + 221234637.

Lemma amagic_key : ABASE * AMAGIC_IMAGE = 15 * 18446744073709551616 + 26877.
Proof. reflexivity. Qed.


Lemma mulhu_eq : forall x, 0 <= x < 1099511627776 ->
  mulhu x AMAGIC_IMAGE = (15 * x) / ABASE.
Proof.
  intros x Hx. unfold mulhu.
  pose proof (Z.div_mod (15 * x) ABASE ltac:(unfold ABASE; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (15 * x) ABASE ltac:(unfold ABASE; lia)) as Hs.
  set (g0 := (15 * x) / ABASE) in *.
  set (s := (15 * x) mod ABASE) in *.
  unfold ABASE, AMAGIC_IMAGE in *.
  assert (Hlo : 18446744073709551616 * g0 <= x * (983265 * 4294967296 + 221234637))
    by lia.
  assert (Hhi : x * (983265 * 4294967296 + 221234637)
                < 18446744073709551616 * g0 + 18446744073709551616) by lia.
  replace (x * (983265 * 4294967296 + 221234637))
    with (g0 * 18446744073709551616
          + (x * (983265 * 4294967296 + 221234637) - 18446744073709551616 * g0))
    by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  lia.
Qed.

Lemma div15_split : forall N r, 0 <= N -> 0 <= r < ABASE ->
  (15 * (ABASE * N + r)) / ABASE = 15 * N + (15 * r) / ABASE.
Proof.
  intros N r HN Hr.
  replace (15 * (ABASE * N + r)) with (15 * N * ABASE + 15 * r) by ring.
  apply Z.div_add_l. unfold ABASE; lia.
Qed.


Lemma mdiv_core : forall N r, 0 <= N -> 0 <= r < ABASE ->
  ABASE * N + r < 1099511627776 ->
  Z.shiftr (mulhu (ABASE * N + r) AMAGIC_IMAGE
            + Z.shiftr (ABASE * N + r - mulhu (ABASE * N + r) AMAGIC_IMAGE) 1) 15
  = N.
Proof.
  intros N r HN Hr Hx.
  assert (Hx0 : 0 <= ABASE * N + r < 1099511627776) by (unfold ABASE in *; lia).
  rewrite (mulhu_eq _ Hx0), (div15_split N r HN Hr).
  set (g := (15 * r) / ABASE) in *.
  assert (Hg : 0 <= g < 15).
  { unfold g; split.
    - apply Z.div_pos; [lia | unfold ABASE; lia].
    - apply Z.div_lt_upper_bound; unfold ABASE in *; lia. }
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. change (2 ^ 15) with 32768.
  set (D := ABASE * N + r - (15 * N + g)) in *.
  pose proof (Z.div_mod D 2 ltac:(lia)) as HD.
  pose proof (Z.mod_pos_bound D 2 ltac:(lia)) as He.
  set (e := D mod 2) in *.
  assert (Hlow : 0 <= r + g - e).
  { destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    - assert (Hg0 : g = 0) by (unfold g; rewrite Hr0; reflexivity).
      assert (HD2 : D = 32753 * N * 2)
        by (unfold D; rewrite Hr0, Hg0; unfold ABASE; ring).
      assert (He0 : e = 0) by (unfold e; rewrite HD2; apply Z.mod_mul; lia).
      lia.
    - lia. }
  assert (Hhigh : r + g - e <= 65534) by (unfold ABASE in *; lia).
  replace (15 * N + g + D / 2)
    with (N * 32768 + (15 * N + g + D / 2 - N * 32768)) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by (unfold ABASE in *; lia).
  lia.
Qed.


Theorem mdiv_image_correct : forall x, 0 <= x < 1099511627776 ->
  Z.shiftr (mulhu x AMAGIC_IMAGE + Z.shiftr (x - mulhu x AMAGIC_IMAGE) 1) 15
  = x / ABASE.
Proof.
  intros x Hx.
  pose proof (Z.div_mod x ABASE ltac:(unfold ABASE; lia)) as Hxd.
  pose proof (Z.mod_pos_bound x ABASE ltac:(unfold ABASE; lia)) as Hr.
  assert (HN : 0 <= x / ABASE) by (apply Z.div_pos; [lia | unfold ABASE; lia]).
  rewrite Hxd at 1 2 3.
  apply mdiv_core; [exact HN | exact Hr | unfold ABASE in *; lia].
Qed.

Theorem mdiv_correct_after_fix : AMAGIC = AMAGIC_IMAGE -> mdiv_correct_S.
Proof.
  intros HA x Hx. unfold mdiv. rewrite HA. apply mdiv_image_correct, Hx.
Qed.

Theorem mrem_correct_after_fix : AMAGIC = AMAGIC_IMAGE -> mrem_correct_S.
Proof. intros HA. apply mrem_of_mdiv, mdiv_correct_after_fix, HA. Qed.



Lemma amagic_matches_image : AMAGIC = AMAGIC_IMAGE.
Proof. reflexivity. Qed.

Theorem mdiv_correct : mdiv_correct_S.
Proof. exact (mdiv_correct_after_fix amagic_matches_image). Qed.

Theorem mrem_correct : mrem_correct_S.
Proof. exact (mrem_correct_after_fix amagic_matches_image). Qed.
End ZChkArith.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZChkAdl.ZChkArith.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


Definition b0 : byte := Z_to_bv 8 0.
Definition bZ (d : list byte) : list Z := map bv_unsigned d.
Definition bnth (d : list byte) (k : nat) : Z := bv_unsigned (nth k d b0).

Lemma bZ_length : forall d, length (bZ d) = length d.
Proof. intro d. apply length_map. Qed.

Lemma bZ_nth : forall d k, nth k (bZ d) 0 = bnth d k.
Proof.
  intros d k. unfold bZ, bnth.
  replace 0 with (bv_unsigned b0) by reflexivity.
  apply map_nth.
Qed.

Lemma firstn_S_snoc : forall {A} (l : list A) (dflt : A) k, (k < length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l dflt].
Proof.
  intros A l dflt k. revert l. induction k as [|k IH]; intros l Hk.
  - destruct l as [|x l]; cbn in Hk |- *; [lia | reflexivity].
  - destruct l as [|x l]; cbn [length] in Hk; [lia|].
    cbn [firstn nth app]. f_equal. apply IH. cbn [length] in Hk. lia.
Qed.


Definition A1 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  fst (adl_raw (firstn k (bZ d)) s1 s2).
Definition A2 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  snd (adl_raw (firstn k (bZ d)) s1 s2).

Lemma adl_raw_app : forall xs ys s1 s2,
  adl_raw (xs ++ ys) s1 s2
  = adl_raw ys (fst (adl_raw xs s1 s2)) (snd (adl_raw xs s1 s2)).
Proof.
  induction xs as [|x xs IH]; intros ys s1 s2; cbn [app adl_raw fst snd].
  - reflexivity.
  - apply IH.
Qed.

Lemma adl_raw1_fst : forall b u v, fst (adl_raw [b] u v) = u + b.
Proof. reflexivity. Qed.
Lemma adl_raw1_snd : forall b u v, snd (adl_raw [b] u v) = v + (u + b).
Proof. reflexivity. Qed.

Lemma A1_0 : forall d s1 s2, A1 d s1 s2 0 = s1.
Proof. reflexivity. Qed.
Lemma A2_0 : forall d s1 s2, A2 d s1 s2 0 = s2.
Proof. reflexivity. Qed.

Lemma A_step : forall d s1 s2 k, (k < length d)%nat ->
  A1 d s1 s2 (S k) = A1 d s1 s2 k + bnth d k
  /\ A2 d s1 s2 (S k) = A2 d s1 s2 k + A1 d s1 s2 (S k).
Proof.
  intros d s1 s2 k Hk.
  assert (Hf : firstn (S k) (bZ d) = firstn k (bZ d) ++ [bnth d k]).
  { rewrite <- bZ_nth.
    apply (firstn_S_snoc (bZ d) 0 k). rewrite bZ_length. exact Hk. }
  unfold A1, A2. rewrite Hf, adl_raw_app.
  split; [apply adl_raw1_fst|].
  rewrite adl_raw1_snd, adl_raw1_fst. reflexivity.
Qed.

Lemma A1_step : forall d s1 s2 k, (k < length d)%nat ->
  A1 d s1 s2 (S k) = A1 d s1 s2 k + bnth d k.
Proof. intros. apply A_step. assumption. Qed.

Lemma A2_step : forall d s1 s2 k, (k < length d)%nat ->
  A2 d s1 s2 (S k) = A2 d s1 s2 k + A1 d s1 s2 (S k).
Proof. intros. apply A_step. assumption. Qed.

Lemma A_full : forall d s1 s2,
  A1 d s1 s2 (length d) = fst (adl_raw (bZ d) s1 s2)
  /\ A2 d s1 s2 (length d) = snd (adl_raw (bZ d) s1 s2).
Proof.
  intros d s1 s2. unfold A1, A2.
  rewrite firstn_all2 by (rewrite bZ_length; lia). split; reflexivity.
Qed.


Definition IS1 (init : Z) : Z := Z.land init 65535.
Definition IS2 (init : Z) : Z := Z.land (Z.shiftr init 16) 65535.

Lemma IS1_range : forall init, 0 <= init -> 0 <= IS1 init < 65536.
Proof.
  intros init H. unfold IS1.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma IS2_range : forall init, 0 <= init -> 0 <= IS2 init < 65536.
Proof.
  intros init H. unfold IS2.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma adler32_model_raw : forall init d, 0 <= init ->
  adler32_model init (bZ d)
  = Z.lxor (Z.shiftl (snd (adl_raw (bZ d) (IS1 init) (IS2 init)) mod ABASE) 16)
           (fst (adl_raw (bZ d) (IS1 init) (IS2 init)) mod ABASE).
Proof.
  intros init d Hi. unfold adler32_model, IS1, IS2.
  rewrite adl_raw_mod. reflexivity.
Qed.


Lemma lor_lxor_disj : forall a b, Z.land a b = 0 -> Z.lor a b = Z.lxor a b.
Proof.
  intros a b H. apply Z.bits_inj'. intros n Hn.
  assert (Hb : andb (Z.testbit a n) (Z.testbit b n) = false)
    by (rewrite <- Z.land_spec, H, Z.bits_0; reflexivity).
  rewrite Z.lor_spec, Z.lxor_spec.
  destruct (Z.testbit a n), (Z.testbit b n); cbn in Hb |- *; congruence.
Qed.

Lemma combine_lor : forall a s, 0 <= a < 65536 -> 0 <= s ->
  Z.lor (Z.shiftl s 16) a = Z.lxor (Z.shiftl s 16) a.
Proof.
  intros a s Ha Hs. apply lor_lxor_disj. rewrite Z.land_comm.
  apply (land_shiftl_disj a s 16); [change (2 ^ 16) with 65536; lia|lia|lia].
Qed.

Lemma condsub : forall x, 0 <= x < 2 * ABASE ->
  (if Z.leb x 65520 then x else x - ABASE) = x mod ABASE.
Proof.
  intros x Hx. unfold ABASE in *.
  destruct (Z.leb_spec x 65520) as [H|H].
  - symmetry. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add x (-1) 65521) by lia.
    symmetry. apply Z.mod_small. lia.
Qed.

Lemma condsub_small : forall x, 0 <= x <= 69360 -> 0 <= x < 2 * ABASE.
Proof. unfold ABASE. lia. Qed.


Definition RQ (x : Z) : Z := Z.shiftr (x * AMAGIC_IMAGE) 64.
Definition RD (x : Z) : Z := x - RQ x.
Definition RH (x : Z) : Z := Z.shiftr (RD x) 1.
Definition RT (x : Z) : Z := Z.shiftr (RQ x + RH x) 15.

Definition RLIM : Z := 1099511627776.

Lemma RQ_mulhu : forall x, RQ x = mulhu x AMAGIC_IMAGE.
Proof.
  intro x. unfold RQ, mulhu. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma RQ_bound : forall x, 0 <= x < RLIM -> 0 <= RQ x <= x.
Proof.
  intros x Hx. unfold RLIM in Hx. rewrite RQ_mulhu, mulhu_eq by lia.
  split; [apply Z.div_pos; [lia | unfold ABASE; lia]|].
  apply Z.div_le_upper_bound; [unfold ABASE; lia | unfold ABASE; lia].
Qed.

Lemma RD_bound : forall x, 0 <= x < RLIM -> 0 <= RD x <= x.
Proof.
  intros x Hx. pose proof (RQ_bound x Hx). unfold RD. lia.
Qed.

Lemma RH_bound : forall x, 0 <= x < RLIM -> 0 <= RH x <= x.
Proof.
  intros x Hx. pose proof (RD_bound x Hx). unfold RH.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia|].
  apply Z.le_trans with (RD x); [apply Z.div_le_upper_bound; lia | lia].
Qed.

Lemma RT_div : forall x, 0 <= x < RLIM -> RT x = x / ABASE.
Proof.
  intros x Hx. unfold RT, RH, RD. rewrite !RQ_mulhu.
  apply mdiv_image_correct. exact Hx.
Qed.

Lemma RT_bound : forall x, 0 <= x < RLIM -> 0 <= RT x <= x.
Proof.
  intros x Hx. rewrite RT_div by exact Hx. unfold RLIM in Hx.
  split; [apply Z.div_pos; [lia | unfold ABASE; lia]|].
  apply Z.div_le_upper_bound; unfold ABASE; lia.
Qed.

Lemma red_mulback : forall q, (q * 4096 - q) * 16 + q = ABASE * q.
Proof. intro q. unfold ABASE. ring. Qed.

Lemma red_final : forall x, 0 <= x < RLIM ->
  x - ((RT x * 4096 - RT x) * 16 + RT x) = x mod ABASE.
Proof.
  intros x Hx. rewrite red_mulback, RT_div by exact Hx.
  symmetry. apply Z.mod_eq. unfold ABASE. lia.
Qed.

Lemma IS1_eq : forall z, 0 <= z < 2 ^ 64 -> IS1 z = Z.land z 65535.
Proof. reflexivity. Qed.

Lemma IS2_eq : forall z, 0 <= z < 2 ^ 32 -> IS2 z = Z.shiftr z 16.
Proof.
  intros z Hz. unfold IS2.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.mod_small. split; [apply Z.div_pos; lia|].
  change (2 ^ 16) with 65536. apply Z.div_lt_upper_bound; lia.
Qed.



Lemma firstn_split : forall (A : Type) (k j : nat) (l : list A),
  firstn (k + j) l = firstn k l ++ firstn j (skipn k l).
Proof.
  intros A. induction k as [|k IH]; intros j l; cbn [firstn skipn Nat.add app].
  - reflexivity.
  - destruct l as [|x l]; cbn [firstn skipn app].
    + rewrite firstn_nil. reflexivity.
    + f_equal. apply IH.
Qed.

Lemma A_split : forall d s1 s2 k j,
  (A1 d s1 s2 (k + j), A2 d s1 s2 (k + j))
  = adl_raw (firstn j (skipn k (bZ d))) (A1 d s1 s2 k) (A2 d s1 s2 k).
Proof.
  intros d s1 s2 k j. unfold A1, A2.
  rewrite firstn_split, adl_raw_app.
  destruct (adl_raw (firstn k (bZ d)) s1 s2) as [a b]. cbn [fst snd].
  destruct (adl_raw (firstn j (skipn k (bZ d))) a b). reflexivity.
Qed.

Theorem A_rebase : forall d s1 s2 k j,
  adl (firstn j (skipn k (bZ d)))
      (A1 d s1 s2 k mod ABASE) (A2 d s1 s2 k mod ABASE)
  = (A1 d s1 s2 (k + j) mod ABASE, A2 d s1 s2 (k + j) mod ABASE).
Proof.
  intros d s1 s2 k j.
  rewrite (adl_raw_mod (firstn j (skipn k (bZ d))) (A1 d s1 s2 k) (A2 d s1 s2 k)).
  rewrite <- (A_split d s1 s2 k j). cbn [fst snd]. reflexivity.
Qed.

Lemma A_rebase_reduces : forall d s1 s2 k,
  fst (adl (firstn 0 (skipn k (bZ d)))
           (A1 d s1 s2 k mod ABASE) (A2 d s1 s2 k mod ABASE)) < ABASE.
Proof.
  intros d s1 s2 k. cbn [firstn adl fst].
  apply Z.mod_pos_bound. unfold ABASE. lia.
Qed.
