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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZChkAdl.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZChkAdl.ZChkArith.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition csub (x : Z) : Z := if 65520 <? x then x - 65521 else x.

Definition lo16 (a : Z) : Z := a mod 2 ^ 16.
Definition hi16 (a : Z) : Z := (a mod 2 ^ 32) / 2 ^ 16.

Lemma lo16_range : forall a, 0 <= lo16 a < 2 ^ 16.
Proof. intro a. unfold lo16. apply Z.mod_pos_bound. lia. Qed.

Lemma hi16_range : forall a, 0 <= hi16 a < 2 ^ 16.
Proof.
  intro a. unfold hi16. pose proof (Z.mod_pos_bound a (2 ^ 32) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Definition eqm (x y : Z) : Prop := x mod ABASE = y mod ABASE.

Definition adler32_z_spec (adler P : Z) (d : list byte) : Z :=
  let s1 := lo16 adler in
  let s2 := hi16 adler in
  if Z.of_nat (length d) =? 1 then
    let a := csub (s1 + bnth d 0) in
    let b := csub (a + s2) in
    Z.lor (b * 2 ^ 16) a
  else if P =? 0 then 1
  else let (a, b) := adl_raw (bZ d) s1 s2 in
       Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE).

Lemma mod32_div16 : forall a, 0 <= a -> (a mod 2 ^ 32) / 2 ^ 16 = (a / 2 ^ 16) mod 2 ^ 16.
Proof.
  intros a Ha.
  replace (2 ^ 32) with (2 ^ 16 * 2 ^ 16) by reflexivity.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ 16)), Z.div_add by lia.
  rewrite Z.mod_div by lia. lia.
Qed.

Lemma adler32_z_spec_model : forall adler P d,
  0 <= adler -> Z.of_nat (length d) <> 1 -> P <> 0 ->
  adler32_z_spec adler P d = adler32_model adler (bZ d).
Proof.
  intros adler P d Ha Hl HP. unfold adler32_z_spec, lo16, hi16.
  replace (Z.of_nat (length d) =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hl).
  replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; exact HP).
  unfold adler32_model.
  assert (H1 : Z.land adler 65535 = adler mod 2 ^ 16).
  { change 65535 with (Z.ones 16). apply Z.land_ones. lia. }
  assert (H2 : Z.land (Z.shiftr adler 16) 65535 = (adler mod 2 ^ 32) / 2 ^ 16).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    symmetry. apply mod32_div16. exact Ha. }
  rewrite H1, H2, adl_raw_mod.
  destruct (adl_raw (bZ d) (adler mod 2 ^ 16) (adler mod 2 ^ 32 / 2 ^ 16)) as [a b]. cbn [fst snd].
  pose proof (Z.mod_pos_bound a ABASE ltac:(unfold ABASE; lia)) as Hma.
  pose proof (Z.mod_pos_bound b ABASE ltac:(unfold ABASE; lia)) as Hmb.
  rewrite <- Z.shiftl_mul_pow2 by lia. apply combine_lor; unfold ABASE in *; lia.
Qed.

Lemma Forall_firstn : forall {A} (Q : A -> Prop) n (l : list A), Forall Q l -> Forall Q (firstn n l).
Proof.
  intros A Q n l H. revert n. induction H; intros [|n]; cbn; constructor; auto.
Qed.

Lemma Forall_skipn : forall {A} (Q : A -> Prop) n (l : list A), Forall Q l -> Forall Q (skipn n l).
Proof.
  intros A Q n l H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.

Lemma adl_raw_cons : forall b l u v, adl_raw (b :: l) u v = adl_raw l (u + b) (v + (u + b)).
Proof. reflexivity. Qed.

Lemma adl_raw_bound : forall l u v,
  Forall (fun b => 0 <= b < 256) l -> 0 <= u -> 0 <= v ->
  u <= fst (adl_raw l u v) <= u + 255 * Z.of_nat (length l)
  /\ v <= snd (adl_raw l u v) <= v + Z.of_nat (length l) * (u + 255 * Z.of_nat (length l)).
Proof.
  intros l. induction l as [|b l IH]; intros u v Hl Hu Hv.
  - cbn. lia.
  - inversion Hl as [|b' l' Hb Hl']; subst. rewrite adl_raw_cons.
    destruct (IH (u + b) (v + (u + b)) Hl' ltac:(lia) ltac:(lia)) as [H1 H2].
    cbn [length]. rewrite Nat2Z.inj_succ.
    set (n := Z.of_nat (length l)) in *.
    assert (Hn : 0 <= n) by lia.
    assert (Hm : n * (u + b + 255 * n) <= n * (u + 255 * (n + 1))) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hm2 : n * (u + 255 * (n + 1)) + (u + 255 * (n + 1)) = (n + 1) * (u + 255 * (n + 1))) by ring.
    split; [lia|]. split; [lia|].
    assert (0 <= n * (u + 255 * (n + 1))) by (apply Z.mul_nonneg_nonneg; lia). nia.
Qed.

Lemma adl_raw_congr : forall l u v u' v',
  u mod ABASE = u' mod ABASE -> v mod ABASE = v' mod ABASE ->
  fst (adl_raw l u v) mod ABASE = fst (adl_raw l u' v') mod ABASE
  /\ snd (adl_raw l u v) mod ABASE = snd (adl_raw l u' v') mod ABASE.
Proof.
  intros l. induction l as [|b l IH]; intros u v u' v' Hu Hv; cbn [adl_raw fst snd].
  - auto.
  - apply IH.
    + rewrite (Zplus_mod u b), (Zplus_mod u' b), Hu. reflexivity.
    + rewrite (Zplus_mod v (u + b)), (Zplus_mod v' (u' + b)), Hv, (Zplus_mod u b), (Zplus_mod u' b), Hu.
      reflexivity.
Qed.

Lemma adl_raw_app' : forall xs ys u v,
  adl_raw (xs ++ ys) u v = adl_raw ys (fst (adl_raw xs u v)) (snd (adl_raw xs u v)).
Proof. apply adl_raw_app. Qed.

Lemma skipn_cons_nth : forall (l : list Z) i, (i < length l)%nat ->
  skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  intros l. induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bZ_nth' : forall d i, nth i (bZ d) 0 = bnth d i.
Proof. intros. apply bZ_nth. Qed.

Lemma firstn_S_skipn : forall d i k, (i < length d)%nat ->
  firstn (S k) (skipn i (bZ d)) = bnth d i :: firstn k (skipn (S i) (bZ d)).
Proof.
  intros d i k Hi. rewrite (skipn_cons_nth (bZ d) i) by (rewrite bZ_length; exact Hi).
  cbn [firstn]. rewrite bZ_nth'. reflexivity.
Qed.

Lemma firstn_skipn_app : forall (l : list Z) i k,
  firstn (i + k) l = firstn i l ++ firstn k (skipn i l).
Proof. intros l i k. apply ZChkAdl.firstn_split. Qed.

Definition magq (x : Z) : Z := x * 4223091239536077 / 2 ^ 64.
Definition magT (x : Z) : Z := (magq x + (x - magq x) mod 2 ^ 64 / 2 ^ 1) / 2 ^ 15.
Definition magred (x : Z) : Z := x - ((magT x * 2 ^ 12 - magT x) * 2 ^ 4 + magT x).

Lemma magred_ok : forall x, 0 <= x < RLIM -> magred x = x mod ABASE.
Proof.
  intros x Hx. unfold magred, magT, magq.
  pose proof (RQ_bound x Hx) as HQ.
  assert (EQ : RQ x = x * 4223091239536077 / 2 ^ 64).
  { unfold RQ, AMAGIC_IMAGE. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite <- EQ. unfold RLIM in Hx.
  rewrite Z.mod_small by lia.
  rewrite <- (red_final x Hx). unfold RT, RH, RD.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. change (2 ^ 4) with 16. reflexivity.
Qed.

Lemma csub_mod : forall x, 0 <= x < 2 * ABASE -> csub x = x mod ABASE.
Proof.
  intros x Hx. unfold csub. rewrite <- (condsub x Hx).
  destruct (Z.ltb_spec 65520 x); destruct (Z.leb_spec x 65520); unfold ABASE; lia.
Qed.



Definition adler_canon (a : Z) : Prop := 0 <= a < 2 ^ 32 /\ lo16 a < ABASE /\ hi16 a < ABASE.

Lemma adler_canon_1 : adler_canon 1.
Proof. unfold adler_canon, lo16, hi16, ABASE. cbn. lia. Qed.

Lemma adler32_model_canon : forall a bs, adler_canon (adler32_model a bs).
Proof.
  intros a bs. unfold adler32_model.
  pose proof (adl_canon bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)
                (Z.mod_pos_bound (Z.land a 65535) ABASE ltac:(unfold ABASE; lia))
                (Z.mod_pos_bound (Z.land (Z.shiftr a 16) 65535) ABASE ltac:(unfold ABASE; lia))) as Hc.
  destruct (adl bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)) as [u v].
  cbn [fst snd] in Hc. unfold ABASE in Hc.
  assert (E : Z.lxor (Z.shiftl v 16) u = v * 2 ^ 16 + u).
  { rewrite <- Z.add_nocarry_lxor.
    - rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
    - rewrite Z.land_comm. apply land_shiftl_disj; [change (2 ^ 16) with 65536; lia | lia | lia]. }
  rewrite E. unfold adler_canon, lo16, hi16, ABASE.
  split; [lia|]. split.
  - replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (v * 2 ^ 16 + u)) by lia.
    replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia.
Qed.
