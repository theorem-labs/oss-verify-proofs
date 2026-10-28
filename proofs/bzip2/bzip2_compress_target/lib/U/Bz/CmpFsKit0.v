(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF CmpMem BzCLemmasFs.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record fsenv := FE {
  fe_ra : word; fe_sp : word; fe_gp : word; fe_tp : word;
  fe_s0 : word; fe_s1 : word; fe_s2 : word; fe_s3 : word; fe_s4 : word; fe_s5 : word;
  fe_s6 : word; fe_s7 : word; fe_s8 : word; fe_s9 : word; fe_s10 : word; fe_s11 : word;
  fe_F : bvmap 5 word; fe_fc : bv 32;
  fe_A1 : Z; fe_A2 : Z; fe_FT : Z; fe_nb : Z; fe_lo : Z;
  fe_q1 : Z; fe_q2 : Z; fe_qF : Z; fe_qsp : Z;      (* [comment removed for export] *)
  fe_fm : zarr; fe_ec : zarr; fe_bh : zarr;          (* [comment removed for export] *)
  fe_sv : word;                                      (* [comment removed for export] *)
  fe_m0 : word -> option byte                        (* [comment removed for export] *)
}.

Definition CEILv : Z := alloc_ceiling.  (* [comment removed for export] *)

Definition fsenv_ok (X : fsenv) : Prop :=
  let usp := bv_unsigned (fe_sp X) in
  0x3b000 <= fe_A1 X /\ fe_A1 X + ARR1_SIZE <= CEILv /\
  0x3b000 <= fe_A2 X /\ fe_A2 X + ARR2_SIZE <= CEILv /\
  0x3b000 <= fe_FT X /\ fe_FT X + 262148 <= CEILv /\
  CEILv <= fe_lo X /\ fe_lo X + 3072 <= usp /\ usp < 18446744073709551616 /\
  fe_A1 X = 16 * fe_q1 X /\ fe_A2 X = 16 * fe_q2 X /\ fe_FT X = 16 * fe_qF X /\ usp = 16 * fe_qsp X /\
  1 <= fe_nb X <= (NBLOCKMAX + 19) /\
  zbok (fe_fm X) /\ zbok (fe_ec X) /\ bh_w32 (fe_bh X).

Definition apartv (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.   (* [comment removed for export] *)
Definition fsenv_sep (X : fsenv) : Prop :=
  apartv (fe_A1 X) ARR1_SIZE (fe_A2 X) ARR2_SIZE /\ apartv (fe_A1 X) ARR1_SIZE (fe_FT X) 262148 /\
  apartv (fe_A2 X) ARR2_SIZE (fe_FT X) 262148.

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
Ltac fsenv_open XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; bz_ceil; bz_params; unfold fsenv_ok, CEILv in H; cbv zeta in H;
  let FMOK := fresh "FMOK" in let ECOK := fresh "ECOK" in let BHOK := fresh "BHOK" in
  cps_destruct H as (?XA1l & ?XA1h & ?XA2l & ?XA2h & ?XFl & ?XFh & ?XLO & ?XLOF & ?XSP & ?AL1 & ?AL2 & ?ALF & ?ALS & ?LNB & FMOK & ECOK & BHOK).
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zw32_firstn : forall a n N, 0 <= n <= N -> firstn (Z.to_nat n) (zw32 a N) = zw32 a n.
Proof.
  intros a n N Hn. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [Hk|Hk].
  - rewrite nth_error_firstn' by exact Hk.
    replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite !zw32_nth by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite firstn_length, zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

Lemma zw32_split_at : forall a n N, 0 <= n <= N -> zw32 a N = zw32 a n ++ skipn (Z.to_nat n) (zw32 a N).
Proof. intros a n N Hn. rewrite <- (zw32_firstn a n N Hn). symmetry. apply firstn_skipn. Qed.

Lemma zw32_skipn_ext : forall a a' n N, 0 <= n ->
  (forall i, n <= i < N -> zget a i = zget a' i) -> skipn (Z.to_nat n) (zw32 a N) = skipn (Z.to_nat n) (zw32 a' N).
Proof.
  intros a a' n N Hn H. apply nth_error_ext. intros k. rewrite !nth_error_skipn.
  destruct (Z_lt_le_dec (n + Z.of_nat k) N) as [Hk|Hk].
  - replace (Z.to_nat n + k)%nat with (Z.to_nat (n + Z.of_nat k)) by lia. rewrite !zw32_nth by lia. rewrite H by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod32_of_mod64 : forall z, (z mod 18446744073709551616) mod 4294967296 = z mod 4294967296.
Proof.
  intros z. Z.div_mod_to_equations. lia.
Qed.
Lemma unsigned_lit_mod32 : forall z, bv_unsigned (Z_to_bv 64 z) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply mod32_of_mod64. Qed.
Lemma swrap32_mod32 : forall z, (bv_swrap 32 z) mod 4294967296 = z mod 4294967296.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma sx32_lit_mod32 : forall v, bv_unsigned (sx32 (Z_to_bv 64 v)) mod 4294967296 = v mod 4294967296.
Proof. intros v. unfold sx32. rewrite unsigned_lit_mod32, swrap32_mod32, unsigned_lit_mod32. reflexivity. Qed.

Lemma mod32_land : forall a, a mod 4294967296 = Z.land a 4294967295.
Proof. intros a. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lor_mod32 : forall a b, (Z.lor a b) mod 4294967296 = Z.lor (a mod 4294967296) (b mod 4294967296).
Proof. intros. rewrite !mod32_land. apply Z.land_lor_distr_l. Qed.
Lemma land_mod32 : forall a b, (Z.land a b) mod 4294967296 = Z.land (a mod 4294967296) (b mod 4294967296).
Proof.
  intros. rewrite !mod32_land. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit 4294967295 n); reflexivity.
Qed.
(* [comment removed for export] *)


Lemma land31_mod32 : forall zz, Z.land zz 31 = zz mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Lemma zseq_forallb : forall (P : Z -> bool) n lo, forallb P (zseq lo n) = true -> forall k, lo <= k < lo + Z.of_nat n -> P k = true.
Proof.
  induction n as [|n IH]; intros lo H k Hk; [lia|].
  cbn [zseq forallb] in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  destruct (Z.eq_dec k lo) as [->|]; [exact H1|]. apply (IH (lo + 1)); [exact H2| lia].
Qed.

Lemma set_bh_store_a : forall zz bw,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftl 1 (zz mod 32)) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))))) mod 4294967296
  = (Z.lor bw (Z.shiftl 1 (Z.land zz 31))) mod 4294967296.
Proof.
  intros zz bw. rewrite unsigned_lit_mod32. rewrite lor_mod32. rewrite mod32_of_mod64, swrap32_mod32, sx32_lit_mod32, land31_mod32.
  rewrite (lor_mod32 bw). rewrite Z.lor_comm. reflexivity.
Qed.
Lemma set_bh_store_b : forall zz bw,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 bw))) (bv_swrap 32 (Z.shiftl 1 (zz mod 32)) mod 18446744073709551616))) mod 4294967296
  = (Z.lor bw (Z.shiftl 1 (Z.land zz 31))) mod 4294967296.
Proof.
  intros zz bw. rewrite unsigned_lit_mod32. rewrite lor_mod32. rewrite mod32_of_mod64, swrap32_mod32, sx32_lit_mod32, land31_mod32.
  rewrite (lor_mod32 bw). reflexivity.
Qed.
Lemma clear_mask_eq : forall k, 0 <= k < 32 ->
  (18446744073709551615 - bv_swrap 32 (Z.shiftl 1 k) mod 18446744073709551616) mod 4294967296 = (Z.lxor (Z.shiftl 1 k) 4294967295) mod 4294967296.
Proof.
  intros k Hk.
  pose proof (zseq_forallb (fun k => ((18446744073709551615 - bv_swrap 32 (Z.shiftl 1 k) mod 18446744073709551616) mod 4294967296 =? (Z.lxor (Z.shiftl 1 k) 4294967295) mod 4294967296)) 32 0 ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
  cbn beta in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma clear_bh_store_b : forall zz bw,
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 (Z_to_bv 64 bw))) (18446744073709551615 - bv_swrap 32 (Z.shiftl 1 (zz mod 32)) mod 18446744073709551616))) mod 4294967296
  = (Z.land bw (Z.lxor (Z.shiftl 1 (Z.land zz 31)) 4294967295)) mod 4294967296.
Proof.
  intros zz bw. rewrite unsigned_lit_mod32. rewrite land_mod32. rewrite sx32_lit_mod32, land31_mod32.
  rewrite clear_mask_eq by (pose proof (Z.mod_pos_bound zz 32 ltac:(lia)); lia).
  rewrite (land_mod32 bw). reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_pow2_bit : forall w k, 0 <= k -> Z.land w (Z.shiftl 1 k) = if Z.testbit w k then Z.shiftl 1 k else 0.
Proof.
  intros w k Hk. rewrite Z.shiftl_1_l. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.testbit w k) eqn:E.
  - rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec k n); [subst; rewrite E; reflexivity| apply Bool.andb_false_r].
  - rewrite Z.bits_0. destruct (Z.eqb_spec k n); [subst; rewrite E; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma isset_bh_testbit : forall bh i, 0 <= i -> isset_bh bh i = Z.testbit (zget bh (i / 32)) (i mod 32).
Proof.
  intros bh i Hi. unfold isset_bh, bh_word. rewrite shiftr5_div, land31_mod32.
  pose proof (Z.mod_pos_bound i 32 ltac:(lia)) as Hm.
  rewrite land_pow2_bit by lia.
  destruct (Z.testbit (zget bh (i / 32)) (i mod 32)).
  - destruct (Z.eqb_spec (Z.shiftl 1 (i mod 32)) 0) as [E|]; [|reflexivity].
    exfalso. rewrite Z.shiftl_1_l in E. pose proof (Z.pow_pos_nonneg 2 (i mod 32) ltac:(lia) ltac:(lia)). lia.
  - rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma land1_mod2 : forall a, Z.land a 1 = a mod 2.
Proof. intros. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma shiftr_bit0 : forall w k, 0 <= k -> Z.testbit (Z.shiftr w k) 0 = Z.testbit w k.
Proof. intros. rewrite Z.shiftr_spec by lia. f_equal. Qed.

Lemma mod2_testbit : forall a k, 0 <= k -> (Z.shiftr a k) mod 2 = Z.b2z (Z.testbit a k).
Proof. intros a k Hk. rewrite <- Z.bit0_mod, shiftr_bit0 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma isset_test_val : forall bw i, 0 <= bw < 4294967296 -> 0 <= i ->
  Z.land (bv_swrap 32 (Z.shiftr ((bv_unsigned (sx32 (Z_to_bv 64 bw))) mod 4294967296) (i mod 32)) mod 18446744073709551616) 1
  = Z.b2z (Z.testbit bw (i mod 32)).
Proof.
  intros bw i Hbw Hi. pose proof (Z.mod_pos_bound i 32 ltac:(lia)) as Hm.
  rewrite sx32_lit_mod32, (Z.mod_small bw) by lia.
  rewrite land1_mod2.
  assert (E2 : forall z, (z mod 18446744073709551616) mod 2 = z mod 2) by (intros; Z.div_mod_to_equations; lia).
  rewrite E2.
  assert (E3 : forall z, (bv_swrap 32 z) mod 2 = z mod 2).
  { intros z. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648. Z.div_mod_to_equations. lia. }
  rewrite E3. apply mod2_testbit. lia.
Qed.

Lemma testbit31_false_small : forall bw, 0 <= bw < 4294967296 -> Z.testbit bw 31 = false -> bw < 2147483648.
Proof.
  intros bw Hb Ht. apply Z.testbit_false in Ht; [|lia]. change (2^31) with 2147483648 in Ht.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma isset_and_val : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  (Z.land (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) =? 0)
  = negb (Z.testbit bw (k mod 32)).
Proof.
  intros bw k Hbw Hk. pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hj. set (j := k mod 32) in *. clearbody j.
  assert (HU : bv_unsigned (sx32 (Z_to_bv 64 bw)) = (bv_swrap 32 bw) mod 18446744073709551616).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite (Z.mod_small bw) by lia. reflexivity. }
  rewrite HU. clear HU.
  destruct (Z.testbit bw j) eqn:Tb; cbn [negb].
  - (* [comment removed for export] *)
    apply Z.eqb_neq. intros E.
    assert (E2 : (Z.land (bv_swrap 32 (Z.shiftl 1 j) mod 18446744073709551616) (bv_swrap 32 bw mod 18446744073709551616)) mod 4294967296 = 0) by (rewrite E; reflexivity).
    rewrite land_mod32, !mod32_of_mod64, !swrap32_mod32, (Z.mod_small bw) in E2 by lia.
    rewrite (Z.mod_small (Z.shiftl 1 j)) in E2 by (pose proof (shiftl1_range j ltac:(lia)); lia).
    rewrite Z.land_comm, land_pow2_bit, Tb in E2 by lia. pose proof (shiftl1_range j ltac:(lia)). lia.
  - apply Z.eqb_eq.
    destruct (Z.eq_dec j 31) as [->|Hne].
    + (* [comment removed for export] *)
      pose proof (testbit31_false_small bw Hbw Tb) as Hs.
      replace (bv_swrap 32 bw) with bw by (unfold bv_swrap, bv_wrap; change (bv_modulus 32) with 4294967296; change (bv_half_modulus 32) with 2147483648; Z.div_mod_to_equations; lia).
      rewrite (Z.mod_small bw) by lia.
      change (bv_swrap 32 (Z.shiftl 1 31) mod 18446744073709551616) with (8589934591 * 2 ^ 31).
      apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z_lt_le_dec n 31).
      * rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      * rewrite (Z.bits_above_log2 bw n); [apply Bool.andb_false_r| lia|].
        destruct (Z.eq_dec bw 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. 
        eapply Z.lt_le_trans; [exact Hs|]. change 2147483648 with (2^31). apply Z.pow_le_mono_r; lia.
    + (* [comment removed for export] *)
      replace (bv_swrap 32 (Z.shiftl 1 j) mod 18446744073709551616) with (Z.shiftl 1 j).
      2:{ rewrite Z.shiftl_1_l. assert (B : 0 < 2 ^ j < 2147483648).
          { split; [apply Z.pow_pos_nonneg; lia|]. change 2147483648 with (2^31). apply Z.pow_lt_mono_r; lia. }
          unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
          Z.div_mod_to_equations. lia. }
      rewrite Z.land_comm, land_pow2_bit by lia.
      replace (Z.testbit (bv_swrap 32 bw mod 18446744073709551616) j) with (Z.testbit bw j); [rewrite Tb; reflexivity|].
      change 18446744073709551616 with (2^64). rewrite Z.mod_pow2_bits_low by lia.
      rewrite <- (Z.mod_pow2_bits_low (bv_swrap 32 bw) 32 j) by lia. change (2^32) with 4294967296. rewrite swrap32_mod32, (Z.mod_small bw) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma isset_and_val0 : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  (Z.land (Z.shiftl 1 (k mod 32) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) =? 0)
  = negb (Z.testbit bw (k mod 32)).
Proof.
  intros bw k Hbw Hk. pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hj. set (j := k mod 32) in *. clearbody j.
  pose proof (shiftl1_range j ltac:(lia)) as Hs.
  rewrite (Z.mod_small (Z.shiftl 1 j)) by lia.
  assert (HU : bv_unsigned (sx32 (Z_to_bv 64 bw)) = (bv_swrap 32 bw) mod 18446744073709551616).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite (Z.mod_small bw) by lia. reflexivity. }
  rewrite HU, Z.land_comm, land_pow2_bit by lia.
  replace (Z.testbit (bv_swrap 32 bw mod 18446744073709551616) j) with (Z.testbit bw j).
  2:{ change 18446744073709551616 with (2^64). rewrite Z.mod_pow2_bits_low by lia.
      rewrite <- (Z.mod_pow2_bits_low (bv_swrap 32 bw) 32 j) by lia. change (2^32) with 4294967296. rewrite swrap32_mod32, (Z.mod_small bw) by lia. reflexivity. }
  destruct (Z.testbit bw j); cbn [negb]; [apply Z.eqb_neq; lia| apply Z.eqb_eq; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma land_zero_bit1 : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  Z.land (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) = 0 -> Z.testbit bw (k mod 32) = false.
Proof. intros bw k Hb Hk E. pose proof (isset_and_val bw k Hb Hk) as V. rewrite E in V. cbn in V. destruct (Z.testbit bw (k mod 32)); [discriminate| reflexivity]. Qed.
Lemma land_nz_bit1 : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  Z.land (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) <> 0 -> Z.testbit bw (k mod 32) = true.
Proof. intros bw k Hb Hk E. pose proof (isset_and_val bw k Hb Hk) as V. destruct (Z.testbit bw (k mod 32)); [reflexivity|]. cbn in V. apply Z.eqb_eq in V. lia. Qed.
Lemma land_zero_bit0 : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  Z.land (Z.shiftl 1 (k mod 32) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) = 0 -> Z.testbit bw (k mod 32) = false.
Proof. intros bw k Hb Hk E. pose proof (isset_and_val0 bw k Hb Hk) as V. rewrite E in V. cbn in V. destruct (Z.testbit bw (k mod 32)); [discriminate| reflexivity]. Qed.
Lemma land_nz_bit0 : forall bw k, 0 <= bw < 4294967296 -> 0 <= k ->
  Z.land (Z.shiftl 1 (k mod 32) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 bw))) <> 0 -> Z.testbit bw (k mod 32) = true.
Proof. intros bw k Hb Hk E. pose proof (isset_and_val0 bw k Hb Hk) as V. destruct (Z.testbit bw (k mod 32)); [reflexivity|]. cbn in V. apply Z.eqb_eq in V. lia. Qed.
End ACeilS2.


Ltac bit_of_land H :=
  try rewrite (Z.land_comm (bv_unsigned (sx32 _))) in H;
  first [ apply land_zero_bit1 in H | apply land_nz_bit1 in H | apply land_zero_bit0 in H | apply land_nz_bit0 in H ]; [ | lia | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Tactic Notation "zw32_store" constr(ARR) constr(i) constr(v) tactic(tac) :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
    lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
      let H := fresh "ARRw" in
      pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H; clear ARR; store_done; rename H into ARR
    end end.
(* [comment removed for export] *)
Ltac wval_lit := rewrite unsigned_lit by lia; f_equal; lia.

Tactic Notation "ovw_store" constr(ARR) constr(i) constr(v) tactic(tac) :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
    lazymatch type of ARR with u32arr ?segs m ?A (ovw ?a ?J ?n) =>
      let H := fresh "ARRw" in
      pose proof (ovw_write segs m A a J n i w v ARR ltac:(lia) ltac:(tac)) as H; clear ARR; store_done; rename H into ARR
    end end.

(* [comment removed for export] *)
Ltac zb8_store4 ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
    lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
      let H := fresh "ARRw" in
      pose proof (zb8_write4 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
    end end.
Ltac zb8_store1 ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le1 ?w)) _) =>
    lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
      let H := fresh "ARRw" in
      pose proof (zb8_write1 segs m A a n i w ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
    end end.
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma sign_sel : forall d n, -2147483648 < d < 2147483648 -> 0 <= n < 18446744073709551616 ->
  Z.land ((d / 2147483648) mod 18446744073709551616) n = (if d <? 0 then n else 0).
Proof.
  intros d n Hd Hn. destruct (Z.ltb_spec d 0).
  - replace (d / 2147483648) with (-1) by (Z.div_mod_to_equations; lia).
    change ((-1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
  - rewrite (Z.div_small d) by lia. rewrite Z.mod_0_l by lia. apply Z.land_0_l.
Qed.

(* [comment removed for export] *)
Definition landv (bh : zarr) (k : Z) : Z :=
  Z.land (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 (zget bh (k / 32))))).
Lemma landv_isset : forall bh k, bh_w32 bh -> 0 <= k -> (landv bh k =? 0) = negb (isset_bh bh k).
Proof. intros bh k BW Hk. unfold landv. rewrite isset_and_val by (try apply BW; lia). rewrite isset_bh_testbit by lia. reflexivity. Qed.
(* [comment removed for export] *)
Definition landv' (bh : zarr) (k : Z) : Z :=
  Z.land (bv_unsigned (sx32 (Z_to_bv 64 (zget bh (k / 32))))) (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616).
Lemma landv'_isset : forall bh k, bh_w32 bh -> 0 <= k -> (landv' bh k =? 0) = negb (isset_bh bh k).
Proof. intros bh k BW Hk. unfold landv'. rewrite Z.land_comm. apply landv_isset; assumption. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sx32_lit_unsigned : forall bw, 0 <= bw < 4294967296 ->
  bv_unsigned (sx32 (Z_to_bv 64 bw)) = (if bw <? 2147483648 then bw else bw + 18446744069414584320).
Proof.
  intros bw Hb. unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  destruct (Z.ltb_spec bw 2147483648); Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_allones_iff : forall bw, 0 <= bw < 4294967296 -> (bv_unsigned (sx32 (Z_to_bv 64 bw)) = 18446744073709551615 <-> bw = 4294967295).
Proof. intros bw Hb. rewrite sx32_lit_unsigned by lia. destruct (Z.ltb_spec bw 2147483648); lia. Qed.
Lemma sx32_zero_iff : forall bw, 0 <= bw < 4294967296 -> (bv_unsigned (sx32 (Z_to_bv 64 bw)) = 0 <-> bw = 0).
Proof. intros bw Hb. rewrite sx32_lit_unsigned by lia. destruct (Z.ltb_spec bw 2147483648); lia. Qed.

(* [comment removed for export] *)
Lemma bveqb_m1_true : forall x, - 1 <= x < 18446744073709551615 ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1))) = true -> x <> -1.
Proof.
  intros x Hx H E. subst x. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate.
Qed.
Lemma bveqb_m1_false : forall x, - 1 <= x < 18446744073709551615 ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1))) = false -> x = -1.
Proof.
  intros x Hx H. apply Bool.negb_false_iff in H. unfold bv_eqb in H. apply Z.eqb_eq in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma lcg_hi15 : forall x, 0 <= x -> (x * 562949953421312) mod 18446744073709551616 / 562949953421312 = x mod 32768.
Proof. intros x Hx. Z.div_mod_to_equations. nia. Qed.
Lemma lcg_mod64 : forall x, 0 <= x -> (x * 562949953421312) mod 18446744073709551616 = (x mod 32768) * 562949953421312.
Proof. intros x Hx. Z.div_mod_to_equations. nia. Qed.
Lemma div3_trick : forall r, 0 <= r < 32768 -> r * 21846 / 65536 = r / 3.
Proof. intros r Hr. Z.div_mod_to_equations. lia. Qed.
Lemma lcg_div3 : forall x, 0 <= x ->
  (x * 562949953421312) mod 18446744073709551616 * 715849728 / 18446744073709551616 / 65536 = (x mod 32768) / 3.
Proof.
  intros x Hx. rewrite lcg_mod64 by lia.
  replace (x mod 32768 * 562949953421312 * 715849728) with ((x mod 32768 * 21846) * 18446744073709551616) by ring.
  rewrite Z.div_mul by lia. apply div3_trick. pose proof (Z.mod_pos_bound x 32768 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_plus_not : forall a b, - 2147483648 <= a - b - 1 < 2147483648 ->
  bv_swrap 32 (a + (18446744073709551615 - b)) = a - b - 1.
Proof.
  intros a b H. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma sx32_of_Z_signed : forall v, - 2147483648 <= v < 2147483648 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma slli32_srli30 : forall q, q * 4294967296 / 1073741824 = q * 4.
Proof. intros q. replace (q * 4294967296) with ((q * 4) * 1073741824) by lia. apply Z.div_mul. lia. Qed.
(* [comment removed for export] *)
Lemma slli32_srli32 : forall q, q * 4294967296 / 4294967296 = q.
Proof. intros q. apply Z.div_mul. lia. Qed.

End ACeilS3.
