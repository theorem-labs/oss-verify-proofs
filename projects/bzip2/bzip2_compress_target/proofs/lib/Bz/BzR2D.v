(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream BzDState BzDBlock BzDOut BzR2Theory BzR5a.

Module BzR2Z.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land255_word : forall b k, 0 <= b < 256 -> 0 <= k -> Z.land (b + 256 * k) 255 = b.
Proof.
  intros b k Hb Hk. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  replace (b + 256 * k) with (b + k * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma land255_byte : forall b, 0 <= b < 256 -> Z.land b 255 = b.
Proof. intros b Hb. rewrite <- (land255_word b 0) at 2 by lia. f_equal. lia. Qed.
Lemma shiftr8_word : forall b k, 0 <= b < 256 -> 0 <= k -> Z.shiftr (b + 256 * k) 8 = k.
Proof.
  intros b k Hb Hk. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (b + 256 * k) with (b + k * 256) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma lor_shiftl8 : forall b k, 0 <= b < 256 -> 0 <= k -> Z.lor b (Z.shiftl k 8) = b + 256 * k.
Proof.
  intros b k Hb Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.lor_comm.
  rewrite (lor_disjoint (k * 256) b 8); try lia.
  change (2 ^ 8) with 256. rewrite Z.mod_mul. reflexivity. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit_small : forall a k m, 0 <= a < 2 ^ k -> 0 <= k <= m -> Z.testbit a m = false.
Proof.
  intros a k m Ha Hm. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
  split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Ha)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma testbit_ones : forall k m, 0 <= k -> 0 <= m -> Z.testbit (Z.ones k) m = (m <? k).
Proof.
  intros k m Hk Hm. destruct (Z.ltb_spec m k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.
Lemma testbit_15 : forall m, 0 <= m -> Z.testbit 15 m = (m <? 4).
Proof. intros. change 15 with (Z.ones 4). apply testbit_ones; lia. Qed.
Lemma testbit_255 : forall m, 0 <= m -> Z.testbit 255 m = (m <? 8).
Proof. intros. change 255 with (Z.ones 8). apply testbit_ones; lia. Qed.
Lemma testbit_65535 : forall m, 0 <= m -> Z.testbit 65535 m = (m <? 16).
Proof. intros. change 65535 with (Z.ones 16). apply testbit_ones; lia. Qed.
Lemma testbit_240 : forall m, 0 <= m -> Z.testbit 240 m = (m <? 8) && negb (m <? 4).
Proof.
  intros. change 240 with (Z.lxor (Z.ones 8) (Z.ones 4)). rewrite Z.lxor_spec, !testbit_ones by lia.
  destruct (Z.ltb_spec m 8), (Z.ltb_spec m 4); try reflexivity. lia.
Qed.
Lemma testbit_4 : forall m, 0 <= m -> Z.testbit 4 m = (m =? 2).
Proof.
  intros. change 4 with (2 ^ 2). destruct (Z.eqb_spec m 2).
  - subst. apply Z.pow2_bits_true. lia.
  - apply Z.pow2_bits_false. lia.
Qed.
Lemma testbit_1 : forall m, 0 <= m -> Z.testbit 1 m = (m =? 0).
Proof.
  intros. change 1 with (2 ^ 0). destruct (Z.eqb_spec m 0).
  - subst. apply Z.pow2_bits_true. lia.
  - apply Z.pow2_bits_false. lia.
Qed.

(* [comment removed for export] *)
Lemma land_1_bit0 : forall i, Z.land i 1 = (if Z.testbit i 0 then 1 else 0).
Proof.
  intros i. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, testbit_1 by lia.
  destruct (Z.eqb_spec m 0).
  - subst. destruct (Z.testbit i 0); reflexivity.
  - rewrite Bool.andb_false_r. destruct (Z.testbit i 0); [rewrite testbit_1 by lia|rewrite Z.bits_0]; [|reflexivity].
    destruct (Z.eqb_spec m 0); [lia|reflexivity].
Qed.
Lemma land_shiftl2_4 : forall i, Z.land (Z.shiftl i 2) 4 = (if Z.testbit i 0 then 4 else 0).
Proof.
  intros i. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, testbit_4 by lia.
  destruct (Z.eqb_spec m 2).
  - subst. rewrite Z.shiftl_spec_high by lia. change (2 - 2) with 0.
    destruct (Z.testbit i 0); [rewrite testbit_4 by lia; reflexivity|rewrite Z.bits_0; reflexivity].
  - rewrite Bool.andb_false_r. destruct (Z.testbit i 0); [rewrite testbit_4 by lia|rewrite Z.bits_0]; [|reflexivity].
    destruct (Z.eqb_spec m 2); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma half_double_bit : forall i, 0 <= i -> i = 2 * Z.shiftr i 1 + (if Z.testbit i 0 then 1 else 0).
Proof.
  intros i Hi. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.bit0_eqb.
  pose proof (Z.div_mod i 2 ltac:(lia)). pose proof (Z.mod_pos_bound i 2 ltac:(lia)).
  destruct (Z.eqb_spec (i mod 2) 1); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nget (b : Z) (hi : bool) : Z := Z.land (Z.shiftr b (if hi then 4 else 0)) 15.
Definition nset (b : Z) (hi : bool) (v : Z) : Z :=
  if hi then Z.land (Z.lor (Z.land b 15) (Z.shiftl v 4)) 255 else Z.lor (Z.land b 240) v.

Local Ltac bits :=
  repeat first [rewrite Z.land_spec | rewrite Z.lor_spec | rewrite Z.lxor_spec | rewrite Z.shiftr_spec by lia].
Local Ltac bfin :=
  repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia end;
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia end;
  repeat match goal with |- context [Z.testbit ?x ?y] => destruct (Z.testbit x y) end;
  reflexivity.

Lemma nget_nset_same : forall b hi v, 0 <= v < 16 -> nget (nset b hi v) hi = v.
Proof.
  intros b hi v Hv. unfold nget, nset. apply Z.bits_inj'. intros m Hm. destruct hi; bits.
  - rewrite Z.shiftl_spec_high by lia. replace (m + 4 - 4) with m by lia.
    rewrite !testbit_15, !testbit_255 by lia.
    destruct (Z.lt_ge_cases m 4); [|rewrite (testbit_small v 4 m) by lia]; bfin.
  - rewrite Z.add_0_r. rewrite !testbit_15, !testbit_240 by lia.
    destruct (Z.lt_ge_cases m 4); [|rewrite (testbit_small v 4 m) by lia]; bfin.
Qed.

Lemma nget_nset_other : forall b hi v, 0 <= v < 16 -> nget (nset b hi v) (negb hi) = nget b (negb hi).
Proof.
  intros b hi v Hv. unfold nget, nset. apply Z.bits_inj'. intros m Hm. destruct hi; cbn [negb]; bits.
  - rewrite !Z.add_0_r. rewrite !testbit_15, !testbit_255 by lia.
    destruct (Z.lt_ge_cases m 4); [rewrite Z.shiftl_spec_low by lia|]; bfin.
  - rewrite !testbit_15, !testbit_240 by lia.
    destruct (Z.lt_ge_cases m 4); [rewrite (testbit_small v 4 (m + 4)) by lia|]; bfin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_ll4_nget : forall d i, get_ll4 d i = nget (zget (d_ll4 d) (Z.shiftr i 1)) (Z.testbit i 0).
Proof. intros d i. unfold get_ll4, nget. rewrite land_shiftl2_4. destruct (Z.testbit i 0); reflexivity. Qed.

Lemma set_ll4_nset : forall d i v,
  set_ll4 d i v = d_set_ll4 d (zset (d_ll4 d) (Z.shiftr i 1) (nset (zget (d_ll4 d) (Z.shiftr i 1)) (Z.testbit i 0) v)).
Proof.
  intros d i v. unfold set_ll4, nset. rewrite land_1_bit0. destruct (Z.testbit i 0); reflexivity.
Qed.

Lemma d_ll4_set_ll4 : forall d i v, d_ll4 (set_ll4 d i v) =
  zset (d_ll4 d) (Z.shiftr i 1) (nset (zget (d_ll4 d) (Z.shiftr i 1)) (Z.testbit i 0) v).
Proof. intros. rewrite set_ll4_nset. reflexivity. Qed.

Lemma get_ll4_set_ll4_same : forall d i v, 0 <= v < 16 -> get_ll4 (set_ll4 d i v) i = v.
Proof.
  intros d i v Hv. rewrite get_ll4_nget, d_ll4_set_ll4, zget_zset_same. apply nget_nset_same. exact Hv.
Qed.

Lemma get_ll4_set_ll4_other : forall d i j v, 0 <= i -> 0 <= j -> i <> j -> 0 <= v < 16 ->
  get_ll4 (set_ll4 d i v) j = get_ll4 d j.
Proof.
  intros d i j v Hi Hj Hij Hv. rewrite !get_ll4_nget, d_ll4_set_ll4, zget_zset.
  destruct (Z.eqb_spec (Z.shiftr j 1) (Z.shiftr i 1)) as [E|NE]; [|reflexivity].
  rewrite E.
  assert (P : Z.testbit j 0 = negb (Z.testbit i 0)).
  { pose proof (half_double_bit i Hi). pose proof (half_double_bit j Hj).
    destruct (Z.testbit i 0), (Z.testbit j 0); cbn; try reflexivity; lia. }
  rewrite P. apply nget_nset_other. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma lor16_split : forall v, 0 <= v -> Z.lor (Z.land v 65535) (Z.shiftl (Z.shiftr v 16) 16) = v.
Proof.
  intros v Hv. apply Z.bits_inj'. intros m Hm. rewrite Z.lor_spec, Z.land_spec, testbit_65535 by lia.
  destruct (Z.ltb_spec m 16).
  - rewrite Z.shiftl_spec_low by lia. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (m - 16 + 16) with m by lia.
    rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma d_ll16_set_ll : forall d i v, d_ll16 (set_ll d i v) = zset (d_ll16 d) i (Z.land v 65535).
Proof. intros. unfold set_ll. rewrite set_ll4_nset. reflexivity. Qed.
(* [comment removed for export] *)

Lemma get_ll_set_ll_same : forall d i v, 0 <= v < 2 ^ 20 -> get_ll (set_ll d i v) i = v.
Proof.
  intros d i v Hv. unfold get_ll. unfold set_ll at 2. rewrite get_ll4_set_ll4_same.
  2: { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
       change (2 ^ 16 * 16) with (2 ^ 20). lia. }
  rewrite d_ll16_set_ll, zget_zset_same. apply lor16_split. lia.
Qed.

Lemma get_ll_set_ll_other : forall d i j v, 0 <= i -> 0 <= j -> i <> j -> 0 <= v < 2 ^ 20 ->
  get_ll (set_ll d i v) j = get_ll d j.
Proof.
  intros d i j v Hi Hj Hij Hv. unfold get_ll. unfold set_ll at 2. rewrite get_ll4_set_ll4_other; try lia.
  2: { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|]].
       change (2 ^ 16 * 16) with (2 ^ 20). lia. }
  rewrite d_ll16_set_ll, zget_zset_other by lia.
  unfold get_ll4. cbn [d_ll4 d_set_ll16]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma get_ll_ext : forall d d' i, d_ll16 d' = d_ll16 d -> d_ll4 d' = d_ll4 d -> get_ll d' i = get_ll d i.
Proof. intros d d' i A B. unfold get_ll, get_ll4. rewrite A, B. reflexivity. Qed.

(* [comment removed for export] *)
Lemma set_ll_eq : forall d i v, set_ll d i v = d_set_ll4 (d_set_ll16 d (d_ll16 (set_ll d i v))) (d_ll4 (set_ll d i v)).
Proof. intros. unfold set_ll. rewrite set_ll4_nset. destruct d; reflexivity. Qed.
End BzR2Z.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2D1.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2D1.
Module BzR2D2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Arith.Arith Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2Z OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Ctx.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.
  Let Hn : (0 < n)%nat := bwt_n t pi rho HB.
  Let pi_lt : forall i, (i < n)%nat -> (pi i < n)%nat := bwt_pi_lt t pi rho HB.
  Let rho_lt : forall p, (p < n)%nat -> (rho p < n)%nat := bwt_rho_lt t pi rho HB.
  Let rho_pi : forall i, (i < n)%nat -> rho (pi i) = i := bwt_rho_pi t pi rho HB.
  Let pi_rho : forall p, (p < n)%nat -> pi (rho p) = p := bwt_pi_rho t pi rho HB.
  Let sorted : forall i j, (i <= j)%nat -> (j < n)%nat -> lexle (rot t (pi i)) (rot t (pi j)) := bwt_sorted t pi rho HB.
  Let BYT : Forall (fun x => 0 <= x < 256) t := bwt_bytes t pi rho HB.

  Local Abbreviation Fc := (Fc t pi).
  Local Abbreviation Lc := (Lc t pi).
  Local Abbreviation Ccnt := (Ccnt t pi).
  Local Abbreviation LF := (LF t pi).
  Local Abbreviation FL := (FL t pi).
  Local Abbreviation walk := (walk t pi rho).
  Local Abbreviation CF := (CF t pi).
  Let LF_spec' := LF_spec t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let FL_spec' := FL_spec t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let FL_LF' := FL_LF t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let LF_inj' := LF_inj t Hn pi rho pi_lt rho_lt rho_pi pi_rho.
  Let walk_lt' := walk_lt t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let origPtr_lt' := origPtr_lt t Hn rho rho_lt.
  Let fast_walk_char' := fast_walk_char t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let Lc_byte' := Lc_byte t pi rho HB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition INVF (i : nat) (tt cf : zarr) : Prop :=
    (forall c, 0 <= c <= 255 -> zget cf c = Z.of_nat (Ccnt c + cnt (fun j => Lc j =? c) i)) /\
    (forall r, (r < n)%nat -> zget tt (Z.of_nat r) = Lc r + 256 * (if (FL r <? i)%nat then Z.of_nat (FL r) else 0)).

  (* [comment removed for export] *)
  Definition TVF (tt : zarr) : Prop := forall r, (r < n)%nat -> zget tt (Z.of_nat r) = Lc r + 256 * Z.of_nat (FL r).

  Lemma INVF_step : forall i tt cf, (i < n)%nat -> INVF i tt cf ->
    let uc := Z.land (zget tt (Z.of_nat i)) 255 in
    let k := zget cf uc in
    INVF (S i) (zset tt k (Z.lor (zget tt k) (Z.shiftl (Z.of_nat i) 8))) (zset cf uc (k + 1)).
  Proof.
    intros i tt cf Hi [IC IT]. cbv zeta.
    assert (UC : Z.land (zget tt (Z.of_nat i)) 255 = Lc i).
    { rewrite (IT i Hi). apply land255_word; [apply Lc_byte'|]. destruct (FL i <? i)%nat; lia. }
    rewrite UC.
    assert (K : zget cf (Lc i) = Z.of_nat (LF i)).
    { rewrite IC by (pose proof (Lc_byte' i); lia). reflexivity. }
    rewrite K. destruct (LF_spec' i Hi) as [LFn _].
    assert (TK : zget tt (Z.of_nat (LF i)) = Lc (LF i)).
    { rewrite (IT _ LFn). rewrite FL_LF' by exact Hi. destruct (Nat.ltb_spec i i); lia. }
    split.
    - intros c Hc. rewrite zget_zset. destruct (Z.eqb_spec c (Lc i)) as [->|NE].
      + rewrite cnt_S, Z.eqb_refl. change (if true then 1 else 0)%nat with 1%nat. unfold BzR2Theory.LF, BzR2Theory.occ. lia.
      + rewrite cnt_S. rewrite IC by exact Hc. destruct (Z.eqb_spec (Lc i) c); [congruence|].
        change (if false then 1 else 0)%nat with 0%nat. lia.
    - intros r Hr. rewrite zget_zset. destruct (Z.eqb_spec (Z.of_nat r) (Z.of_nat (LF i))) as [E|NE].
      + apply Nat2Z.inj in E. subst r. rewrite TK, FL_LF' by exact Hi.
        rewrite lor_shiftl8 by (try apply Lc_byte'; lia). destruct (Nat.ltb_spec i (S i)); lia.
      + rewrite (IT r Hr). destruct (FL_spec' r Hr) as [A B].
        assert (FL r <> i) by (intros E; apply NE; rewrite <- E, B; reflexivity).
        destruct (Nat.ltb_spec (FL r) i), (Nat.ltb_spec (FL r) (S i)); lia.
  Qed.

  Lemma tinv_fast_inv : forall k i tt cf, (i + k = n)%nat -> INVF i tt cf ->
    let r := tinv_fast k (Z.of_nat i) tt cf in INVF n (fst r) (snd r).
  Proof.
    induction k as [|k IH]; intros i tt cf Hk HI.
    - cbn. replace n with i by lia. exact HI.
    - cbn [tinv_fast]. cbv zeta. replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia. apply IH; [lia|].
      apply INVF_step; [lia|exact HI].
  Qed.

  Theorem tinv_fast_TVF : forall tt cf,
    (forall r, (r < n)%nat -> zget tt (Z.of_nat r) = Lc r) -> CF cf ->
    let r := tinv_fast n 0 tt cf in
    TVF (fst r) /\ (forall c, 0 <= c <= 255 -> zget (snd r) c = Z.of_nat (Ccnt (c + 1))).
  Proof.
    intros tt cf HT HC.
    pose proof (tinv_fast_inv n 0 tt cf ltac:(lia)) as I. cbn [Z.of_nat] in I.
    destruct I as [IC IT].
    { split.
      - intros c Hc. rewrite HC by lia. rewrite cnt_0. f_equal. lia.
      - intros r Hr. rewrite HT by exact Hr. destruct (Nat.ltb_spec (FL r) 0); lia. }
    cbv zeta. split.
    - intros r Hr. rewrite (IT r Hr). destruct (FL_spec' r Hr) as [A _]. destruct (Nat.ltb_spec (FL r) n); lia.
    - intros c Hc. rewrite (IC c Hc). rewrite (Ccnt_S t pi rho HB). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma TVF_low : forall tt r, TVF tt -> (r < n)%nat -> Z.land (zget tt (Z.of_nat r)) 255 = Lc r.
  Proof. intros tt r H Hr. rewrite (H r Hr). apply land255_word; [apply Lc_byte'|lia]. Qed.
  Lemma TVF_high : forall tt r, TVF tt -> (r < n)%nat -> Z.shiftr (zget tt (Z.of_nat r)) 8 = Z.of_nat (FL r).
  Proof. intros tt r H Hr. rewrite (H r Hr). apply shiftr8_word; [apply Lc_byte'|lia]. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition posF (m : nat) : Z := Z.of_nat (walk (S m)).
  Definition symF (m : nat) : Z := Lc (walk (S m)).

  Lemma symF_spec : forall m, (m < n)%nat -> symF m = nth m t 0.
  Proof. intros m Hm. unfold symF. rewrite fast_walk_char' by lia. f_equal. lia. Qed.
  (* [comment removed for export] *)
  Lemma posF_lt : forall m, 0 <= posF m < Z.of_nat n.
  Proof. intros m. unfold posF. pose proof (walk_lt' (S m)). lia. Qed.

  (* [comment removed for export] *)
  Theorem c_get_TVF : forall tt cap c m, TVF tt -> Z.of_nat n <= cap -> c_tPos c = posF m ->
    c_get tt cap c = Some (symF m, CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (posF (S m)) (c_out c) (c_avail c)).
  Proof.
    intros tt cap c m HT Hcap Hp. unfold c_get. rewrite Hp.
    pose proof (posF_lt m) as B. destruct (Z.leb_spec cap (posF m)); [lia|].
    unfold posF at 1 2. rewrite TVF_low, TVF_high by (try exact HT; apply walk_lt'). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem get_sym_TVF : forall d m, smallb d = false -> d_rand d = 0 -> TVF (d_tt d) ->
    Z.of_nat n <= blk_cap d -> d_tPos d = posF m ->
    get_sym d = Some (symF m, d_set_tPos d (posF (S m))).
  Proof.
    intros d m HS HR HT Hcap Hp. unfold get_sym. rewrite Hp, HS, HR.
    pose proof (posF_lt m) as B. destruct (Z.leb_spec (blk_cap d) (posF m)); [lia|]. cbn [Z.eqb].
    unfold posF at 1 2. rewrite TVF_low, TVF_high by (try exact HT; apply walk_lt'). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dF_end (d : dst) (cf tt' cf' : zarr) : dst :=
    let d1 := d_set_cftab d cf in
    let d2 := d_set_state (d_set_cbcrc (d_set_out_ch (d_set_out_len d1 0) 0) crc_init) BZ_X_OUTPUT in
    let d3 := d_set_cftab (d_set_tt d2 tt') cf' in
    let d4 := d_set_nused (d_set_tPos d3 (posF 0)) 0 in
    d_set_nused (d_set_tPos (d_set_k0 d4 (symF 0)) (posF 1)) 1.

  Theorem block_end_fast : forall L d s,
    sv_nblock L = Z.of_nat n ->
    d_small d = 0 -> d_rand d = 0 ->
    (forall i, (i < n)%nat -> zget (d_tt d) (Z.of_nat i) = Lc i) ->
    HIST t pi (d_unzftab d) ->
    d_origPtr d = Z.of_nat (origPtr rho) ->
    Z.of_nat n <= 100000 * d_bs100k d ->
    exists cf tt' cf',
      block_end L d s = DRet BZ_OK (sv_set_i L (Z.of_nat n)) (dF_end d cf tt' cf') s /\
      CF cf /\ TVF tt' /\ (forall c, 0 <= c <= 255 -> zget cf' c = Z.of_nat (Ccnt (c + 1))).
  Proof.
    intros L d s HN HS HR HT HH HO HC.
    set (cf := cf_accum 256 1 (cf_copy 256 1 (d_unzftab d) (zset (d_cftab d) 0 0))).
    assert (HCF : CF cf) by (subst cf; apply (cftab_CF t pi rho HB); assumption).
    pose proof (tinv_fast_TVF (d_tt d) cf HT HCF) as TI.
    destruct (tinv_fast n 0 (d_tt d) cf) as [tt' cf'] eqn:ET. cbn [fst snd] in TI. destruct TI as [TV CF'].
    exists cf, tt', cf'. split; [|split; [exact HCF|split; [exact TV|exact CF']]].
    unfold block_end. rewrite HN, HO.
    pose proof origPtr_lt' as OL.
    destruct (Z.ltb_spec (Z.of_nat (origPtr rho)) 0); [lia|].
    destruct (Z.leb_spec (Z.of_nat n) (Z.of_nat (origPtr rho))); [lia|]. cbn [orb].
    rewrite (unz_check_ok t pi rho HB) by exact HH. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
    fold cf. rewrite (cf_check1_ok t pi rho HB) by exact HCF.
    rewrite (cf_check2_ok t pi rho HB) by exact HCF.
    cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
    unfold smallb. cbn [d_small d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_cftab]. rewrite HS. cbn [Z.eqb negb].
    cbn [d_tt d_cftab d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_cftab].
    rewrite Nat2Z.id, ET.
    cbn [d_origPtr d_rand d_tPos d_bs100k d_set_cftab d_set_tt d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_nused d_set_tPos d_set_rTPos d_set_rNToGo d_set_k0].
    rewrite HO, HR. cbn [Z.eqb].
    cbn [d_tPos d_set_nused d_set_tPos].
    rewrite (TVF_high tt' _ TV OL). change (FL (origPtr rho)) with (walk 1).
    pose proof (walk_lt' 1) as W1.
    destruct (Z.leb_spec (100000 * d_bs100k d) (Z.of_nat (walk 1))); [lia|].
    cbn [d_rand d_set_nused d_set_tPos d_set_cftab d_set_tt d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_k0].
    rewrite HR. cbn [Z.eqb].
    rewrite (TVF_low tt' _ TV W1), (TVF_high tt' _ TV W1).
    unfold dF_end, posF, symF. reflexivity.
  Qed.
End Ctx.
End BzR2D2.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR2D3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Arith.Arith Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2Z OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition upd3 (d : dst) (a b c : zarr) : dst := d_set_cftabCopy (d_set_ll4 (d_set_ll16 d a) b) c.
Definition upd2 (d : dst) (a b : zarr) : dst := d_set_ll4 (d_set_ll16 d a) b.

Lemma tvec_small_frame : forall k i d, exists a b c, tvec_small k i d = upd3 d a b c.
Proof.
  induction k as [|k IH]; intros i d.
  - exists (d_ll16 d), (d_ll4 d), (d_cftabCopy d). destruct d; reflexivity.
  - cbn [tvec_small].
    set (d1 := set_ll d i (zget (d_cftabCopy d) (Z.land (zget (d_ll16 d) i) 255))).
    cps_destruct (IH (i + 1) (d_set_cftabCopy d1 (zset (d_cftabCopy d1) (Z.land (zget (d_ll16 d) i) 255)
                  (zget (d_cftabCopy d) (Z.land (zget (d_ll16 d) i) 255) + 1)))) as (a & b & c & E).
    rewrite E. exists a, b, c. subst d1. rewrite set_ll_eq. reflexivity.
  Qed.

Lemma prev_loop_frame : forall f i j d, exists i' j' a b, prev_loop f i j d = (i', j', upd2 d a b).
Proof.
  induction f as [|f IH]; intros i j d.
  - exists i, j, (d_ll16 d), (d_ll4 d). destruct d; reflexivity.
  - cbn [prev_loop]. destruct (j =? d_origPtr d).
    + exists j, (get_ll d j), (d_ll16 (set_ll d j i)), (d_ll4 (set_ll d j i)). rewrite (set_ll_eq d j i) at 1. reflexivity.
    + cps_destruct (IH j (get_ll d j) (set_ll d j i)) as (i' & j' & a & b & E). rewrite E.
      exists i', j', a, b. rewrite (set_ll_eq d j i). reflexivity.
Qed.

Section Ctx.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.
  Let Hn : (0 < n)%nat := bwt_n t pi rho HB.
  Let pi_lt : forall i, (i < n)%nat -> (pi i < n)%nat := bwt_pi_lt t pi rho HB.
  Let rho_lt : forall p, (p < n)%nat -> (rho p < n)%nat := bwt_rho_lt t pi rho HB.
  Let rho_pi : forall i, (i < n)%nat -> rho (pi i) = i := bwt_rho_pi t pi rho HB.
  Let pi_rho : forall p, (p < n)%nat -> pi (rho p) = p := bwt_pi_rho t pi rho HB.
  Let sorted : forall i j, (i <= j)%nat -> (j < n)%nat -> lexle (rot t (pi i)) (rot t (pi j)) := bwt_sorted t pi rho HB.
  Let BYT : Forall (fun x => 0 <= x < 256) t := bwt_bytes t pi rho HB.

  Local Abbreviation Fc := (Fc t pi).
  Local Abbreviation Lc := (Lc t pi).
  Local Abbreviation Ccnt := (Ccnt t pi).
  Local Abbreviation LF := (LF t pi).
  Local Abbreviation FL := (FL t pi).
  Local Abbreviation walk := (walk t pi rho).
  Local Abbreviation CF := (CF t pi).
  Local Abbreviation o := (origPtr rho).
  Let LF_spec' := LF_spec t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let FL_spec' := FL_spec t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let FL_LF' := FL_LF t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let LF_inj' := LF_inj t Hn pi rho pi_lt rho_lt rho_pi pi_rho.
  Let walk_lt' := walk_lt t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let origPtr_lt' := origPtr_lt t Hn rho rho_lt.
  Let small_walk_char' := small_walk_char t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let Lc_byte' := Lc_byte t pi rho HB.

  (* [comment removed for export] *)
  Hypothesis N20 : Z.of_nat n < 2 ^ 20.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition INVS (i : nat) (d : dst) : Prop :=
    (forall c, 0 <= c <= 255 -> zget (d_cftabCopy d) c = Z.of_nat (Ccnt c + cnt (fun j => Lc j =? c) i)) /\
    (forall r, (r < i)%nat -> get_ll d (Z.of_nat r) = Z.of_nat (LF r)) /\
    (forall r, (i <= r < n)%nat -> zget (d_ll16 d) (Z.of_nat r) = Lc r).

  Lemma INVS_step : forall i d, (i < n)%nat -> INVS i d ->
    let uc := Z.land (zget (d_ll16 d) (Z.of_nat i)) 255 in
    let k := zget (d_cftabCopy d) uc in
    let d1 := set_ll d (Z.of_nat i) k in
    INVS (S i) (d_set_cftabCopy d1 (zset (d_cftabCopy d1) uc (k + 1))).
  Proof.
    (intros i d Hi; cps_intros (IC & IG & IL)). cbv zeta.
    assert (UC : Z.land (zget (d_ll16 d) (Z.of_nat i)) 255 = Lc i).
    { rewrite (IL i) by lia. apply land255_byte. apply Lc_byte'. }
    rewrite UC.
    assert (K : zget (d_cftabCopy d) (Lc i) = Z.of_nat (LF i)).
    { rewrite IC by (pose proof (Lc_byte' i); lia). reflexivity. }
    rewrite K. destruct (LF_spec' i Hi) as [LFn _].
    assert (FR : d_cftabCopy (set_ll d (Z.of_nat i) (Z.of_nat (LF i))) = d_cftabCopy d) by (rewrite set_ll_eq; reflexivity).
    split; [|split].
    - intros c Hc. cbn [d_cftabCopy d_set_cftabCopy]. rewrite zget_zset, FR. destruct (Z.eqb_spec c (Lc i)) as [->|NE].
      + rewrite cnt_S, Z.eqb_refl. change (if true then 1 else 0)%nat with 1%nat. unfold BzR2Theory.LF, BzR2Theory.occ. lia.
      + rewrite cnt_S. rewrite IC by exact Hc. destruct (Z.eqb_spec (Lc i) c); [congruence|].
        change (if false then 1 else 0)%nat with 0%nat. lia.
    - intros r Hr. rewrite (get_ll_ext (set_ll d (Z.of_nat i) (Z.of_nat (LF i)))) by reflexivity.
      destruct (Nat.eq_dec r i) as [->|NE].
      + apply get_ll_set_ll_same. lia.
      + rewrite get_ll_set_ll_other by lia. apply IG. lia.
    - intros r Hr. cbn [d_ll16 d_set_cftabCopy]. rewrite d_ll16_set_ll, zget_zset_other by lia. apply IL. lia.
  Qed.

  Lemma tvec_small_inv : forall k i d, (i + k = n)%nat -> INVS i d -> INVS n (tvec_small k (Z.of_nat i) d).
  Proof.
    induction k as [|k IH]; intros i d Hk HI.
    - cbn. replace n with i by lia. exact HI.
    - cbn [tvec_small]. replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia. apply IH; [lia|].
      apply INVS_step; [lia|exact HI].
  Qed.

  Theorem tvec_small_LF : forall d, CF (d_cftabCopy d) ->
    (forall r, (r < n)%nat -> zget (d_ll16 d) (Z.of_nat r) = Lc r) ->
    forall r, (r < n)%nat -> get_ll (tvec_small n 0 d) (Z.of_nat r) = Z.of_nat (LF r).
  Proof.
    intros d HC HL. pose proof (tvec_small_inv n 0 d ltac:(lia)) as I. cbn [Z.of_nat] in I.
    cps_destruct I as (_ & IG & _); [|exact IG].
    split; [|split].
    - intros c Hc. rewrite HC by lia. rewrite cnt_0, Nat.add_0_r. reflexivity.
    - intros r Hr. lia.
    - intros r Hr. apply HL. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma walk_0 : walk 0 = o. Proof. reflexivity. Qed.
  Lemma walk_S : forall k, walk (S k) = FL (walk k). Proof. reflexivity. Qed.

  Lemma FL_inj' : forall r r', (r < n)%nat -> (r' < n)%nat -> FL r = FL r' -> r = r'.
  Proof.
    intros r r' Hr Hr' E. destruct (FL_spec' r Hr) as [_ A]. destruct (FL_spec' r' Hr') as [_ A'].
    rewrite <- A, <- A', E. reflexivity.
  Qed.

  Lemma walk_back : forall a d, walk (a + d) = walk a -> walk d = walk 0.
  Proof.
    induction a as [|a IH]; intros d E; [exact E|]. apply IH.
    apply FL_inj'; [apply walk_lt'|apply walk_lt'|]. rewrite <- !walk_S. change (S a + d)%nat with (S (a + d)) in E. exact E.
  Qed.

  Lemma find_seq_first : forall (P : nat -> bool) len s m, find P (seq s len) = Some m ->
    (s <= m < s + len)%nat /\ P m = true /\ forall a, (s <= a < m)%nat -> P a = false.
  Proof.
    induction len as [|len IH]; intros s m H; cbn in H; [discriminate|].
    destruct (P s) eqn:E.
    - injection H as <-. split; [lia|]. split; [exact E|]. intros; lia.
    - cps_destruct (IH (S s) m H) as (A & B & C). split; [lia|]. split; [exact B|].
      intros a Ha. destruct (Nat.eq_dec a s) as [->|NE]; [exact E|]. apply C. lia.
  Qed.

  (* [comment removed for export] *)
  Definition mc : nat := match find (fun m => walk m =? o)%nat (seq 1 n) with Some m => m | None => 1%nat end.

  Lemma mc_spec : (1 <= mc <= n)%nat /\ walk mc = o /\ forall a, (1 <= a < mc)%nat -> walk a <> o.
  Proof.
    unfold mc. destruct (find (fun m => walk m =? o)%nat (seq 1 n)) as [m|] eqn:E.
    - cps_destruct (find_seq_first _ _ _ _ E) as (A & B & C). apply Nat.eqb_eq in B.
      split; [lia|]. split; [exact B|]. intros a Ha. apply Nat.eqb_neq. apply C. lia.
    - exfalso.
      assert (INJ : forall a b, (a < S n)%nat -> (b < S n)%nat -> walk a = walk b -> a = b).
      { intros a b Ha Hb Eab. destruct (Nat.lt_trichotomy a b) as [L|[L|L]]; [|exact L|]; exfalso.
        - pose proof (walk_back a (b - a)) as W. replace (a + (b - a))%nat with b in W by lia.
          specialize (W (eq_sym Eab)).
          pose proof (find_none _ _ E (b - a)%nat ltac:(apply in_seq; lia)) as F. cbn beta in F.
          rewrite W, walk_0, Nat.eqb_refl in F. discriminate.
        - pose proof (walk_back b (a - b)) as W. replace (b + (a - b))%nat with a in W by lia.
          specialize (W Eab).
          pose proof (find_none _ _ E (a - b)%nat ltac:(apply in_seq; lia)) as F. cbn beta in F.
          rewrite W, walk_0, Nat.eqb_refl in F. discriminate. }
      pose proof (cnt_inj_le (S n) (fun _ => true) (fun _ => true) (fun k => walk k) n) as P.
      rewrite !cnt_true in P. enough (S n <= n)%nat by lia. apply P.
      + intros k Hk _. split; [apply walk_lt'|reflexivity].
      + intros k k' Hk Hk' _ _. apply INJ; assumption.
  Qed.

  Lemma walk_period : forall a, walk (a + mc) = walk a.
  Proof.
    induction a as [|a IH].
    - cbn [Nat.add]. rewrite walk_0. apply mc_spec.
    - change (S a + mc)%nat with (S (a + mc)). rewrite !walk_S, IH. reflexivity.
  Qed.

  Lemma walk_mod : forall k, walk k = walk (k mod mc).
  Proof.
    intros k. cps_pose mc_spec as (M & _ & _).
    rewrite (Nat.div_mod_eq k mc) at 1. rewrite Nat.add_comm.
    induction (k / mc)%nat as [|q IH].
    - f_equal. lia.
    - replace (k mod mc + mc * S q)%nat with ((k mod mc + mc * q) + mc)%nat by lia. rewrite walk_period. exact IH.
  Qed.

  Lemma walk_inj_mc : forall a b, (a < mc)%nat -> (b < mc)%nat -> walk a = walk b -> a = b.
  Proof.
    intros a b Ha Hb E. cps_pose mc_spec as (M & W & MIN).
    destruct (Nat.lt_trichotomy a b) as [L|[L|L]]; [|exact L|]; exfalso.
    - pose proof (walk_back a (b - a)) as X. replace (a + (b - a))%nat with b in X by lia.
      apply (MIN (b - a)%nat ltac:(lia)). rewrite <- walk_0. apply X. symmetry. exact E.
    - pose proof (walk_back b (a - b)) as X. replace (b + (a - b))%nat with a in X by lia.
      apply (MIN (a - b)%nat ltac:(lia)). rewrite <- walk_0. apply X. exact E.
  Qed.

  Lemma LF_walk_S : forall a, LF (walk (S a)) = walk a.
  Proof. intros a. rewrite walk_S. apply FL_spec'. apply walk_lt'. Qed.

  Lemma LF_walk_0 : LF (walk 0) = walk (mc - 1).
  Proof.
    cps_pose mc_spec as (M & W & _). rewrite walk_0, <- W. replace mc with (S (mc - 1)) at 1 by lia. apply LF_walk_S.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PL (s : nat) (d : dst) : Prop :=
    (forall a, (mc - s <= a < mc)%nat -> get_ll d (Z.of_nat (walk a)) = Z.of_nat (walk (S a))) /\
    (forall a, (a < mc - s)%nat -> get_ll d (Z.of_nat (walk a)) = Z.of_nat (LF (walk a))).

  Lemma prev_loop_spec : forall f s d, (1 <= s <= mc)%nat -> (mc - s < f)%nat -> PL (s - 1) d ->
    d_origPtr d = Z.of_nat o ->
    let r := prev_loop f (Z.of_nat (walk (mc - s + 1))) (Z.of_nat (walk (mc - s))) d in
    fst (fst r) = Z.of_nat o /\ snd (fst r) = Z.of_nat (walk (mc - 1)) /\ PL mc (snd r) /\ d_origPtr (snd r) = Z.of_nat o.
  Proof.
    induction f as [|f IH]; intros s d Hs Hf [PS PU] HO; [lia|].
    cps_pose mc_spec as (M & W & MIN).
    cbn [prev_loop]. rewrite HO.
    assert (TMP : get_ll d (Z.of_nat (walk (mc - s))) = Z.of_nat (LF (walk (mc - s)))) by (apply PU; lia).
    rewrite TMP.
    set (d1 := set_ll d (Z.of_nat (walk (mc - s))) (Z.of_nat (walk (mc - s + 1)))).
    assert (P1 : PL s d1).
    { split.
      - intros a Ha. subst d1. destruct (Nat.eq_dec a (mc - s)) as [->|NE].
        + rewrite get_ll_set_ll_same; [f_equal; f_equal; lia|]. pose proof (walk_lt' (mc - s + 1)). lia.
        + rewrite get_ll_set_ll_other; [apply PS; lia|lia|lia| |pose proof (walk_lt' (mc - s + 1)); lia].
          intros E. apply Nat2Z.inj in E. apply NE. symmetry. apply walk_inj_mc; [lia|lia|exact E].
      - intros a Ha. subst d1. rewrite get_ll_set_ll_other; [apply PU; lia|lia|lia| |pose proof (walk_lt' (mc - s + 1)); lia].
        intros E. apply Nat2Z.inj in E. assert (mc - s = a)%nat by (apply walk_inj_mc; [lia|lia|exact E]). lia. }
    assert (OD : d_origPtr d1 = Z.of_nat o) by (subst d1; rewrite set_ll_eq; exact HO).
    destruct (Z.eqb_spec (Z.of_nat (walk (mc - s))) (Z.of_nat o)) as [E|NE].
    - (* [comment removed for export] *)
      assert (SM : s = mc).
      { enough (mc - s = 0)%nat by lia. apply walk_inj_mc; [lia|lia|]. rewrite walk_0. apply Nat2Z.inj. exact E. }
      subst s. cbn [fst snd]. rewrite Nat.sub_diag in *. split; [exact E|]. split; [rewrite LF_walk_0; reflexivity|].
      split; [exact P1|exact OD].
    - assert (SM : (s < mc)%nat).
      { destruct (Nat.eq_dec s mc) as [->|]; [|lia]. exfalso. apply NE. rewrite Nat.sub_diag, walk_0. reflexivity. }
      replace (LF (walk (mc - s))) with (walk (mc - S s))
        by (replace (mc - s)%nat with (S (mc - S s)) by lia; rewrite LF_walk_S; reflexivity).
      replace (mc - s)%nat with (mc - S s + 1)%nat by lia.
      apply (IH (S s)); [lia|lia| |exact OD]. replace (S s - 1)%nat with s by lia. exact P1.
  Qed.

  (* [comment removed for export] *)
  Definition WL (d : dst) : Prop := forall k, get_ll d (Z.of_nat (walk k)) = Z.of_nat (walk (S k)).

  Lemma PL_mc_WL : forall d, PL mc d -> WL d.
  Proof.
    intros d [PS _] k. cps_pose mc_spec as (M & _ & _).
    rewrite (walk_mod k). rewrite PS by (pose proof (Nat.mod_upper_bound k mc ltac:(lia)); lia).
    f_equal. rewrite !walk_S, <- walk_mod. reflexivity.
  Qed.

  Lemma o_walk_mc : Z.of_nat o = Z.of_nat (walk mc).
  Proof. cps_pose mc_spec as (_ & W & _). rewrite W. reflexivity. Qed.
  Lemma get_ll_o : forall d, (forall r, (r < n)%nat -> get_ll d (Z.of_nat r) = Z.of_nat (LF r)) ->
    get_ll d (Z.of_nat o) = Z.of_nat (walk (mc - 1)).
  Proof. intros d HG. rewrite <- LF_walk_0. exact (HG (walk 0) (walk_lt' 0)). Qed.

  Theorem prev_loop_WL : forall d f, (n <= f)%nat ->
    (forall r, (r < n)%nat -> get_ll d (Z.of_nat r) = Z.of_nat (LF r)) ->
    d_origPtr d = Z.of_nat o ->
    let r := prev_loop (S f) (Z.of_nat (walk mc)) (Z.of_nat (walk (mc - 1))) d in
    fst (fst r) = Z.of_nat o /\ snd (fst r) = Z.of_nat (walk (mc - 1)) /\ WL (snd r) /\ d_origPtr (snd r) = Z.of_nat o.
  Proof.
    intros d f Hf HG HO. cps_pose mc_spec as (M & W & _).
    replace (walk mc) with (walk (mc - 1 + 1)) by (f_equal; lia).
    pose proof (prev_loop_spec (S f) 1 d ltac:(lia) ltac:(lia)) as P.
    replace (1 - 1)%nat with 0%nat in P by lia.
    cps_destruct P as (A & B & C & D).
    - split; [intros a Ha; lia|]. intros a Ha. apply HG. apply walk_lt'.
    - exact HO.
    - cbv zeta. split; [exact A|]. split; [exact B|]. split; [apply PL_mc_WL; exact C|exact D].
  Qed.
End Ctx.
End BzR2D3.


Module BzR2D4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Arith.Arith Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2Z OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2D3.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Section Ctx.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.
  Let Hn : (0 < n)%nat := bwt_n t pi rho HB.
  Let pi_lt : forall i, (i < n)%nat -> (pi i < n)%nat := bwt_pi_lt t pi rho HB.
  Let rho_lt : forall p, (p < n)%nat -> (rho p < n)%nat := bwt_rho_lt t pi rho HB.
  Let rho_pi : forall i, (i < n)%nat -> rho (pi i) = i := bwt_rho_pi t pi rho HB.
  Let pi_rho : forall p, (p < n)%nat -> pi (rho p) = p := bwt_pi_rho t pi rho HB.
  Let sorted : forall i j, (i <= j)%nat -> (j < n)%nat -> lexle (rot t (pi i)) (rot t (pi j)) := bwt_sorted t pi rho HB.
  Let BYT : Forall (fun x => 0 <= x < 256) t := bwt_bytes t pi rho HB.

  Local Abbreviation Fc := (Fc t pi).
  Local Abbreviation Lc := (Lc t pi).
  Local Abbreviation Ccnt := (Ccnt t pi).
  Local Abbreviation LF := (LF t pi).
  Local Abbreviation FL := (FL t pi).
  Local Abbreviation walk := (walk t pi rho).
  Local Abbreviation CF := (CF t pi).
  Local Abbreviation o := (origPtr rho).
  Local Abbreviation WL := (WL t pi rho).
  Let walk_lt' := walk_lt t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let origPtr_lt' := origPtr_lt t Hn rho rho_lt.
  Let small_walk_char' := small_walk_char t Hn pi rho pi_lt rho_lt rho_pi pi_rho sorted.
  Let Fc_byte' := Fc_byte t pi rho HB.

  Hypothesis N20 : Z.of_nat n < 2 ^ 20.

  Local Ltac sd := cbn [d_origPtr d_rand d_tPos d_bs100k d_cftab d_cftabCopy d_ll16 d_ll4 d_small d_tt d_k0 d_nused
                        upd2 upd3 d_set_nused d_set_tPos d_set_k0 d_set_ll4 d_set_ll16 d_set_cftabCopy d_set_state
                        d_set_cbcrc d_set_out_ch d_set_out_len d_set_cftab d_set_rTPos d_set_rNToGo d_set_tt].
  (* [comment removed for export] *)
  Local Ltac dnorm := cbv beta iota zeta delta [upd2 upd3 BzR2Theory.walk Nat.iter
     d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
     d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv].
  Lemma get_ll_set_nused : forall d v i, get_ll (d_set_nused d v) i = get_ll d i.
  Proof. intros. apply get_ll_ext; reflexivity. Qed.
  Lemma get_ll_set_tPos : forall d v i, get_ll (d_set_tPos d v) i = get_ll d i.
  Proof. intros. apply get_ll_ext; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition TVS (d : dst) : Prop := CF (d_cftab d) /\ WL d.

  Lemma TVS_ext : forall d d', TVS d -> d_cftab d' = d_cftab d -> d_ll16 d' = d_ll16 d -> d_ll4 d' = d_ll4 d -> TVS d'.
  Proof.
    intros d d' [A B] E1 E2 E3. split; [rewrite E1; exact A|]. intros k. rewrite (get_ll_ext d d') by assumption. apply B.
  Qed.

  (* [comment removed for export] *)
  Definition posS (m : nat) : Z := Z.of_nat (walk m).
  Definition symS (m : nat) : Z := Fc (walk m).

  Lemma symS_spec : forall m, (m < n)%nat -> symS m = nth m t 0.
  Proof. intros m Hm. unfold symS. apply small_walk_char'. exact Hm. Qed.
  (* [comment removed for export] *)
  Lemma posS_lt : forall m, 0 <= posS m < Z.of_nat n.
  Proof. intros m. unfold posS. pose proof (walk_lt' m). lia. Qed.

  (* [comment removed for export] *)
  Theorem get_sym_TVS : forall d m, smallb d = true -> d_rand d = 0 -> TVS d ->
    Z.of_nat n <= blk_cap d -> d_tPos d = posS m ->
    get_sym d = Some (symS m, d_set_tPos d (posS (S m))).
  Proof.
    intros d m HS HR [HC HW] Hcap Hp. unfold get_sym. rewrite Hp, HS, HR.
    pose proof (posS_lt m) as B. destruct (Z.leb_spec (blk_cap d) (posS m)); [lia|]. cbn [Z.eqb].
    unfold posS at 1 2. rewrite (indexIntoF_Fc t pi rho HB) by (try exact HC; apply walk_lt'). rewrite HW. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dS_end (d : dst) (cf l16 l4 cc : zarr) : dst :=
    let d1 := d_set_cftab d cf in
    let d2 := d_set_state (d_set_cbcrc (d_set_out_ch (d_set_out_len d1 0) 0) crc_init) BZ_X_OUTPUT in
    let d5 := d_set_cftabCopy (d_set_ll4 (d_set_ll16 d2 l16) l4) cc in
    let d6 := d_set_nused (d_set_tPos d5 (posS 0)) 0 in
    d_set_nused (d_set_tPos (d_set_k0 d6 (symS 0)) (posS 1)) 1.

  Theorem block_end_small : forall L d s,
    sv_nblock L = Z.of_nat n ->
    d_small d <> 0 -> d_rand d = 0 ->
    (forall i, (i < n)%nat -> zget (d_ll16 d) (Z.of_nat i) = Lc i) ->
    HIST t pi (d_unzftab d) ->
    d_origPtr d = Z.of_nat o ->
    Z.of_nat n <= 100000 * d_bs100k d ->
    exists cf l16 l4 cc,
      block_end L d s = DRet BZ_OK (sv_set_j (sv_set_i L (Z.of_nat o)) (Z.of_nat (walk (mc t pi rho - 1)))) (dS_end d cf l16 l4 cc) s /\
      CF cf /\ TVS (dS_end d cf l16 l4 cc).
  Proof.
    intros L d s HN HS HR HT HH HO HC.
    set (cf := cf_accum 256 1 (cf_copy 256 1 (d_unzftab d) (zset (d_cftab d) 0 0))).
    assert (HCF : CF cf) by (subst cf; apply (cftab_CF t pi rho HB); assumption).
    unfold block_end. rewrite HN, HO.
    pose proof origPtr_lt' as OL.
    destruct (Z.ltb_spec (Z.of_nat o) 0); [lia|].
    destruct (Z.leb_spec (Z.of_nat n) (Z.of_nat o)); [lia|]. cbn [orb].
    rewrite (unz_check_ok t pi rho HB) by exact HH. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
    fold cf. rewrite (cf_check1_ok t pi rho HB) by exact HCF.
    rewrite (cf_check2_ok t pi rho HB) by exact HCF.
    cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
    unfold smallb. cbn [d_small d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_cftab].
    destruct (Z.eqb_spec (d_small d) 0); [lia|]. cbn [negb].
    cbn [d_cftab d_cftabCopy d_set_state d_set_cbcrc d_set_out_ch d_set_out_len d_set_cftab].
    rewrite Nat2Z.id.
    set (d2 := d_set_state (d_set_cbcrc (d_set_out_ch (d_set_out_len (d_set_cftab d cf) 0) 0) crc_init) BZ_X_OUTPUT).
    set (d3 := d_set_cftabCopy d2 (cf_dup 257 0 cf (d_cftabCopy d))).
    (* [comment removed for export] *)
    pose proof (tvec_small_LF t pi rho HB N20 d3) as TL. change (length t) with n in TL.
    cps_destruct (tvec_small_frame n 0 d3) as (a4 & b4 & c4 & E4). rewrite E4 in TL |- *.
    specialize (TL ltac:(subst d3 d2; sd; apply (cf_dup_CF t pi rho HB); exact HCF) ltac:(subst d3 d2; exact HT)).
    subst d3 d2. sd. rewrite HO.
    set (d4 := upd3 _ a4 b4 c4) in *.
    (* [comment removed for export] *)
    rewrite (get_ll_o t pi rho HB d4 TL).
    pose proof (o_walk_mc t pi rho HB) as OW. change (length t) with n in OW.
    match goal with |- context [prev_loop ?f (Z.of_nat o) ?x ?dd] =>
       replace (prev_loop f (Z.of_nat o) x dd) with (prev_loop f (Z.of_nat (walk (mc t pi rho))) x dd) by (rewrite <- OW; reflexivity) end.
    pose proof (prev_loop_WL t pi rho HB N20 d4 n ltac:(lia) TL ltac:(subst d4; reflexivity || exact HO)) as PW.
    change (length t) with n in PW.
    cps_destruct (prev_loop_frame (S n) (Z.of_nat (walk (mc t pi rho))) (Z.of_nat (walk (mc t pi rho - 1))) d4) as (i5 & j5 & a5 & b5 & E5).
    rewrite E5 in PW |- *. cbn [fst snd] in PW. cps_destruct PW as (-> & -> & WL5 & O5).
    exists cf, a5, b5, c4.
    subst d4. sd. rewrite ?HO, ?HR. cbn [Z.eqb]. sd.
    destruct (Z.leb_spec (100000 * d_bs100k d) (Z.of_nat o)); [lia|]. rewrite ?HR. cbn [Z.eqb]. sd.
    rewrite (indexIntoF_Fc t pi rho HB cf o HCF OL).
    rewrite get_ll_set_nused, get_ll_set_tPos.
    match goal with |- context [get_ll ?dd (Z.of_nat o)] =>
      replace (get_ll dd (Z.of_nat o)) with (Z.of_nat (walk 1)) by first [exact (WL5 0%nat) | symmetry; exact (WL5 0%nat)] end.
    split; [|split; [exact HCF|]].
    - unfold dS_end, posS, symS. dnorm. reflexivity.
    - match type of WL5 with BzR2D3.WL _ _ _ ?dd => apply (TVS_ext dd) end.
      + split; [exact HCF|exact WL5].
      + unfold dS_end; dnorm; reflexivity.
      + unfold dS_end; dnorm; reflexivity.
      + unfold dS_end; dnorm; reflexivity.
  Qed.
End Ctx.
End BzR2D4.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2Z OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2D2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2D3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2D4.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section Ctx.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.
  Let Hn : (0 < n)%nat := bwt_n t pi rho HB.

  Local Abbreviation o := (origPtr rho).
  Local Abbreviation walk := (walk t pi rho).

  (* [comment removed for export] *)
  Definition pos (sm : bool) (m : nat) : Z := if sm then posS t pi rho m else posF t pi rho m.
  Definition sym (sm : bool) (m : nat) : Z := if sm then symS t pi rho m else symF t pi rho m.

  Theorem sym_spec : forall sm m, (m < n)%nat -> sym sm m = nth m t 0.
  Proof. intros [|] m Hm; unfold sym; [apply (symS_spec t pi rho HB)|apply (symF_spec t pi rho HB)]; exact Hm. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TV (sm : bool) (d : dst) : Prop :=
    smallb d = sm /\ d_rand d = 0 /\ Z.of_nat n <= blk_cap d /\
    (if sm then Z.of_nat n < 2 ^ 20 /\ TVS t pi rho d else TVF t pi (d_tt d)).
  (* [comment removed for export] *)
  Definition TVC (tt : zarr) (cap : Z) : Prop := TVF t pi tt /\ Z.of_nat n <= cap.

  Lemma TV_small : forall sm d, TV sm d -> smallb d = sm. Proof. intros sm d H; exact (proj1 H). Qed.
  Lemma TV_rand : forall sm d, TV sm d -> d_rand d = 0. Proof. intros sm d H; exact (proj1 (proj2 H)). Qed.
  (* [comment removed for export] *)
  Lemma TV_TVC : forall d, TV false d -> TVC (d_tt d) (blk_cap d).
  Proof. (intros d; cps_intros (A & B & C & D)). split; [exact D|exact C]. Qed.

  Theorem TV_frame : forall sm d d', TV sm d ->
    d_small d' = d_small d -> d_rand d' = d_rand d -> d_bs100k d' = d_bs100k d -> d_tt d' = d_tt d ->
    d_cftab d' = d_cftab d -> d_ll16 d' = d_ll16 d -> d_ll4 d' = d_ll4 d -> TV sm d'.
  Proof.
    (intros sm d d'; cps_intros (A & B & C & D); intros E1 E2 E3 E4 E5 E6 E7). unfold TV, smallb, blk_cap in *.
    rewrite E1, E2, E3, E4. split; [exact A|]. split; [exact B|]. split; [exact C|].
    destruct sm; [|exact D]. destruct D as [D1 D2]. split; [exact D1|].
    apply (TVS_ext t pi rho d d' D2 E5 E6 E7).
  Qed.

  (* [comment removed for export] *)
  Theorem get_sym_src : forall sm d m, TV sm d -> d_tPos d = pos sm m ->
    get_sym d = Some (sym sm m, d_set_tPos d (pos sm (S m))).
  Proof.
    (intros sm d m; cps_intros (A & B & C & D); intros P). destruct sm; unfold pos, sym in *.
    - destruct D as [N20 D]. apply (get_sym_TVS t pi rho HB); assumption.
    - apply (get_sym_TVF t pi rho HB); assumption.
  Qed.

  Theorem c_get_src : forall tt cap c m, TVC tt cap -> c_tPos c = pos false m ->
    c_get tt cap c = Some (sym false m,
      CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (pos false (S m)) (c_out c) (c_avail c)).
  Proof.
    intros tt cap c m [A B] P. unfold pos, sym in *. apply (c_get_TVF t pi rho HB); assumption.
  Qed.

  (* [comment removed for export] *)
  Definition bend_upd (sm : bool) (d : dst) (cf cc tt l16 l4 : zarr) : dst :=
    d_set_nused (d_set_tPos (d_set_k0 (d_set_cbcrc (d_set_out_ch (d_set_out_len (d_set_state
      (d_set_ll4 (d_set_ll16 (d_set_tt (d_set_cftabCopy (d_set_cftab d cf) cc) tt) l16) l4)
      BZ_X_OUTPUT) 0) 0) crc_init) (sym sm 0)) (pos sm 1)) 1.
  Definition bend_L (sm : bool) (L : dsv) : dsv :=
    if sm then sv_set_j (sv_set_i L (Z.of_nat o)) (Z.of_nat (walk (mc t pi rho - 1))) else sv_set_i L (Z.of_nat n).

  (* [comment removed for export] *)
  Lemma bend_upd_fields : forall sm d cf cc tt l16 l4, let d' := bend_upd sm d cf cc tt l16 l4 in
    d_state d' = BZ_X_OUTPUT /\ d_out_len d' = 0 /\ d_out_ch d' = 0 /\ d_cbcrc d' = crc_init /\
    d_k0 d' = sym sm 0 /\ d_tPos d' = pos sm 1 /\ d_nused d' = 1 /\
    d_cftab d' = cf /\ d_cftabCopy d' = cc /\ d_tt d' = tt /\ d_ll16 d' = l16 /\ d_ll4 d' = l4 /\
    d_small d' = d_small d /\ d_rand d' = d_rand d /\ d_bs100k d' = d_bs100k d /\ d_origPtr d' = d_origPtr d /\
    d_sbcrc d' = d_sbcrc d /\ d_sccrc d' = d_sccrc d /\ d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\
    d_bsBuff d' = d_bsBuff d /\ d_bsLive d' = d_bsLive d /\ d_sv d' = d_sv d /\ d_unzftab d' = d_unzftab d /\
    d_nInUse d' = d_nInUse d /\ d_s2u d' = d_s2u d /\ d_verb d' = d_verb d /\ d_rNToGo d' = d_rNToGo d /\ d_rTPos d' = d_rTPos d.
  Proof. intros. repeat split; reflexivity. Qed.

  Lemma bend_L_fields : forall sm L, sv_nblock (bend_L sm L) = sv_nblock L /\ sv_nblockMAX (bend_L sm L) = sv_nblockMAX L /\
    sv_EOB (bend_L sm L) = sv_EOB L /\ sv_alphaSize (bend_L sm L) = sv_alphaSize L /\ sv_nGroups (bend_L sm L) = sv_nGroups L /\
    sv_nSelectors (bend_L sm L) = sv_nSelectors L.
  Proof. intros [|] L; cbn; repeat split; reflexivity. Qed.

  Local Ltac dnorm := cbv beta iota zeta delta [dF_end dS_end bend_upd upd2 upd3
     d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
     d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv].

  Local Ltac sd := cbn [bend_upd dS_end dF_end d_small d_rand d_bs100k d_tt d_cftab d_ll16 d_ll4 d_tPos d_k0 d_nused d_state d_out_len d_out_ch d_cbcrc
     d_set_nused d_set_tPos d_set_k0 d_set_cbcrc d_set_out_ch d_set_out_len d_set_state d_set_ll4 d_set_ll16 d_set_tt d_set_cftabCopy d_set_cftab].

  Theorem block_end_ok : forall sm L d s,
    sv_nblock L = Z.of_nat n ->
    smallb d = sm -> d_rand d = 0 ->
    (forall i, (i < n)%nat -> zget ((if sm then d_ll16 d else d_tt d)) (Z.of_nat i) = Lc t pi i) ->
    HIST t pi (d_unzftab d) ->
    d_origPtr d = Z.of_nat o ->
    Z.of_nat n <= 100000 * d_bs100k d ->
    (sm = true -> Z.of_nat n < 2 ^ 20) ->
    exists cf cc tt l16 l4,
      block_end L d s = DRet BZ_OK (bend_L sm L) (bend_upd sm d cf cc tt l16 l4) s /\
      TV sm (bend_upd sm d cf cc tt l16 l4).
  Proof.
    intros sm L d s HN HS HR HT HH HO HC H20. unfold smallb in HS. destruct sm.
    - destruct (Z.eqb_spec (d_small d) 0) as [E|NE]; [discriminate|].
      specialize (H20 eq_refl).
      cps_destruct (block_end_small t pi rho HB H20 L d s HN NE HR HT HH HO HC) as (cf & l16 & l4 & cc & E1 & C1 & T1).
      exists cf, cc, (d_tt d), l16, l4.
      assert (EQ : dS_end t pi rho d cf l16 l4 cc = bend_upd true d cf cc (d_tt d) l16 l4).
      { unfold bend_upd, pos, sym. dnorm. reflexivity. }
      rewrite <- EQ. split; [exact E1|].
      rewrite EQ in T1. unfold TV, smallb, blk_cap. sd.
      split; [destruct (Z.eqb_spec (d_small d) 0); [lia|reflexivity]|].
      split; [exact HR|]. split; [exact HC|]. split; [exact H20|exact T1].
    - destruct (Z.eqb_spec (d_small d) 0) as [E|NE]; [|discriminate].
      cps_destruct (block_end_fast t pi rho HB L d s HN E HR HT HH HO HC) as (cf & tt' & cf' & E1 & C1 & T1 & C2).
      exists cf', (d_cftabCopy d), tt', (d_ll16 d), (d_ll4 d).
      assert (EQ : dF_end t pi rho d cf tt' cf' = bend_upd false d cf' (d_cftabCopy d) tt' (d_ll16 d) (d_ll4 d)).
      { unfold bend_upd, pos, sym. dnorm. reflexivity. }
      rewrite <- EQ. split; [exact E1|].
      unfold TV, smallb, blk_cap. sd.
      split; [rewrite E; reflexivity|].
      split; [exact HR|]. split; [exact HC|exact T1].
  Qed.
End Ctx.
