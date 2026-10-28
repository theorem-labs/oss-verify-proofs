(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma B_nz_lt : forall bs q, (B bs q <> 0)%Z -> (q < blen bs)%Z.
Proof. intros bs q H. destruct (Z_lt_dec q (blen bs)) as [L|L]; [exact L|]. exfalso. apply H. apply B_pad. lia. Qed.

Lemma land255_mod : forall x, Z.land (x mod 18446744073709551616) 255 = (x mod 256)%Z.
Proof.
  intros x. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  change 18446744073709551616%Z with (2 ^ 56 * 2 ^ 8)%Z. change (2 ^ 8)%Z with 256%Z.
  rewrite Z.mul_comm. rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma land255_small : forall x, (0 <= x < 256)%Z -> Z.land x 255 = x.
Proof. intros x H. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Ltac nnorm :=
  s2norm;
  repeat match goal with
  | |- context [Z.land (Z.modulo ?x 18446744073709551616) 255] => rewrite (land255_mod x)
  | |- context [Z.land (B ?bs ?i) 255] => rewrite (land255_small (B bs i)) by lia
  end.
Ltac nstep := zstep; nnorm; s2_store_done_wr.
Ltac srun_to A :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end end; nstep).
Ltac srun := repeat nstep.

Local Open Scope Z_scope.
Lemma lor_add : forall n X Y, 0 <= n -> 0 <= X -> X mod 2 ^ n = 0 -> 0 <= Y < 2 ^ n -> Z.lor X Y = X + Y.
Proof.
  intros n X Y Hn HX HM HY. rewrite <- Z.add_lor_land.
  assert (L0 : Z.land X Y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i n).
    - assert (EX : X = (X / 2 ^ n) * 2 ^ n) by (pose proof (Z.div_mod X (2 ^ n) ltac:(lia)); lia).
      rewrite EX. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec Y 0) as [->|NZ]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 Y i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  lia.
Qed.

Definition V8 (b1 b2 b3 b4 b5 b6 b7 b8 : Z) : Z :=
  Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftl b8 24 mod 18446744073709551616) (Z.shiftl b7 16 mod 18446744073709551616))
                         (Z.lor (Z.shiftl b6 8 mod 18446744073709551616) b5)) 32 mod 18446744073709551616)
        (Z.lor (Z.lor (Z.shiftl b4 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
               (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1)).

Lemma V4_sum : forall b1 b2 b3 b4, 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 ->
  Z.lor (Z.lor (Z.shiftl b4 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1) = b1 + 256 * b2 + 65536 * b3 + 16777216 * b4.
Proof.
  intros b1 b2 b3 b4 H1 H2 H3 H4.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia.
  rewrite (lor_add 8 (b2 * 2 ^ 8) b1) by (try apply Z_mod_mult; lia).
  rewrite (lor_add 24 (b4 * 2 ^ 24) (b3 * 2 ^ 16)) by (try (replace (b4 * 2 ^ 24) with (b4 * 2 ^ 24) by lia; apply Z_mod_mult); lia).
  rewrite (lor_add 16 (b4 * 2 ^ 24 + b3 * 2 ^ 16) (b2 * 2 ^ 8 + b1)); [lia | lia | lia | | lia].
  replace (b4 * 2 ^ 24 + b3 * 2 ^ 16) with ((b4 * 256 + b3) * 2 ^ 16) by lia. apply Z_mod_mult.
Qed.

Lemma V8_sum : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  V8 b1 b2 b3 b4 b5 b6 b7 b8 =
  b1 + 256 * b2 + 65536 * b3 + 16777216 * b4 + 4294967296 * (b5 + 256 * b6 + 65536 * b7 + 16777216 * b8).
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8. unfold V8.
  rewrite !V4_sum by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite lor_add with (n := 32); [lia | lia | lia | apply Z_mod_mult | lia].
Qed.

Lemma V8_range : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  0 <= V8 b1 b2 b3 b4 b5 b6 b7 b8 < 18446744073709551616.
Proof. intros. rewrite V8_sum by lia. lia. Qed.

Lemma swar8_last : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  Z.lor (Z.land (Z.shiftr ((V8 b1 b2 b3 b4 b5 b6 b7 b8 + 434041037028460038) mod 18446744073709551616) 4) 1085102592571150095)
        (Z.land (V8 b1 b2 b3 b4 b5 b6 b7 b8) 17361641481138401520) = 3689348814741910323 ->
  48 <= b8 < 64.
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8 HT.
  pose proof (V8_sum b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8) as HV.
  set (V := V8 b1 b2 b3 b4 b5 b6 b7 b8) in *.
  apply (f_equal (fun x => Z.land x 17293822569102704640)) in HT.
  rewrite Z.land_lor_distr_l, <- !Z.land_assoc in HT.
  change (Z.land 1085102592571150095 17293822569102704640) with 0 in HT.
  change (Z.land 17361641481138401520 17293822569102704640) with 17293822569102704640 in HT.
  change (Z.land 3689348814741910323 17293822569102704640) with 3458764513820540928 in HT.
  rewrite Z.land_0_r, Z.lor_0_l in HT.
  apply (f_equal (fun x => Z.shiftr x 60)) in HT. rewrite Z.shiftr_land in HT.
  change (Z.shiftr 17293822569102704640 60) with (Z.ones 4) in HT. change (Z.shiftr 3458764513820540928 60) with 3 in HT.
  rewrite Z.land_ones in HT by lia. rewrite Z.shiftr_div_pow2 in HT by lia.
  change (2 ^ 60) with 1152921504606846976 in HT. change (2 ^ 4) with 16 in HT.
  lia.
Qed.
Lemma land_bit31 : forall A T, Z.land (Z.lor A T) 18446744071570489472 = 0 -> (T / 2147483648) mod 2 = 0.
Proof.
  intros A T H.
  assert (H31 : Z.testbit (Z.land (Z.lor A T) 18446744071570489472) 31 = false) by (rewrite H; apply Z.bits_0).
  rewrite Z.land_spec, Z.lor_spec in H31.
  change (Z.testbit 18446744071570489472 31) with true in H31. rewrite andb_true_r in H31.
  apply orb_false_iff in H31. destruct H31 as [_ HT].
  apply Z.testbit_false in HT; [|lia]. exact HT.
Qed.

Lemma swar4_last : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  Z.land (Z.lor (bv_swrap 32 (V8 b1 b2 b3 b4 b5 b6 b7 b8 mod 18446744073709551616 + 1179010630) mod 18446744073709551616)
                (bv_swrap 32 (V8 b1 b2 b3 b4 b5 b6 b7 b8 mod 18446744073709551616 + 18446744072901087184) mod 18446744073709551616))
         18446744071570489472 = 0 ->
  48 <= b4.
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8 HT.
  pose proof (V8_sum b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8) as HV.
  set (V := V8 b1 b2 b3 b4 b5 b6 b7 b8) in *.
  apply land_bit31 in HT.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in HT.
  change (2 ^ Z.of_N 32) with 4294967296 in HT. change (4294967296 / 2) with 2147483648 in HT.
  lia.
Qed.

Local Close Scope Z_scope.

Ltac fold_V8 :=
  repeat match goal with
  | |- context [Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftl ?b8 24 mod 18446744073709551616) (Z.shiftl ?b7 16 mod 18446744073709551616))
                                       (Z.lor (Z.shiftl ?b6 8 mod 18446744073709551616) ?b5)) 32 mod 18446744073709551616)
                      (Z.lor (Z.lor (Z.shiftl ?b4 24 mod 18446744073709551616) (Z.shiftl ?b3 16 mod 18446744073709551616))
                             (Z.lor (Z.shiftl ?b2 8 mod 18446744073709551616) ?b1))] =>
      fold (V8 b1 b2 b3 b4 b5 b6 b7 b8)
  end.

Ltac srun_cut cuts :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc end; nstep).
Ltac n_closed_branch a b := fail.
Ltac nbranch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      first [ n_closed_branch a b | (let KB := fresh "KB" in if_cases KB) ]
  end.
Ltac nexp cuts fin := srun_cut cuts; first [ fin | (nbranch; nexp cuts fin) ].

Lemma word_signed_repr : forall w : word, exists e, (-9223372036854775808 <= e < 9223372036854775808)%Z /\ w = Z_to_bv 64 e.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  exists (if (bv_unsigned w <? 9223372036854775808)%Z then bv_unsigned w else (bv_unsigned w - 18446744073709551616)%Z).
  destruct (Z.ltb_spec (bv_unsigned w) 9223372036854775808).
  - split; [lia|]. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - split; [lia|]. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    rewrite <- (Z.mod_add _ 1) by lia. replace (bv_unsigned w - 18446744073709551616 + 1 * 18446744073709551616)%Z with (bv_unsigned w) by lia.
    symmetry. apply Z.mod_small. lia.
Qed.

Lemma s2n_image_readable : forall segs (m : mem) n A bs0,
  image_bytes segs A n = Some bs0 -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs0 H HA HB.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - cbn [image_bytes] in H. destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs1|] eqn:E2; [|discriminate].
    destruct (IH (A + 1)%Z bs1 E2 ltac:(lia) ltac:(lia)) as (bs & L & BA).
    assert (exists b', mrd segs m (wa A) = Some b') as [b' Hb'].
    { unfold mrd. destruct (m (wa A)); [eexists; reflexivity| exists b; exact E]. }
    exists (b' :: bs). split; [cbn; congruence|].
    destruct BA as (B1 & B2 & B3). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb'.
    + replace (A + Z.of_nat (S i))%Z with (A + 1 + Z.of_nat i)%Z by lia. apply B3. cbn [length] in Hi. lia.
Qed.

Fixpoint s2n_covered_b (segs : list Segment) (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs (wa A) with Some _ => s2n_covered_b segs (A + 1) n' | None => false end
  end.
Lemma s2n_covered_bytes : forall segs n A, s2n_covered_b segs A n = true -> exists bs, image_bytes segs A n = Some bs.
Proof.
  intros segs n. induction n as [|n IH]; intros A H; cbn [s2n_covered_b image_bytes] in *; [eexists; reflexivity|].
  destruct (seg_rom segs (wa A)); [|discriminate]. destruct (IH _ H) as [bs ->]. eexists; reflexivity.
Qed.

Definition T_POW : Z := 0x156a8.
Definition T_POW_LEN : nat := Z.to_nat 10600.
Lemma T_POW_LEN_Z : Z.of_nat T_POW_LEN = 10600%Z.
Proof. reflexivity. Qed.
Lemma pow_tab_covered : s2n_covered_b usegs T_POW T_POW_LEN = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pow_tab_read : forall (m : mem) k a, (0 <= k)%Z -> (k + 8 <= 10600)%Z -> a = wa (T_POW + k) ->
  exists w, ov_read_bytes usegs m a 8 = Some (le8 w).
Proof.
  intros m k a Hk Hl ->.
  destruct (s2n_covered_bytes usegs T_POW_LEN T_POW pow_tab_covered) as [bs0 E0].
  pose proof T_POW_LEN_Z as HZ.
  destruct (s2n_image_readable usegs m T_POW_LEN T_POW bs0 E0 ltac:(unfold T_POW; lia) ltac:(rewrite HZ; unfold T_POW; lia)) as (bs & L & BA).
  assert (LZ : Z.of_nat (length bs) = 10600%Z) by (rewrite L; exact HZ).
  exists (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs))).
  rewrite le8_le_bytes_to_word by (rewrite length_firstn, length_skipn; lia).
  apply bytes_at_read; [exact BA | lia | lia].
Qed.

Lemma wz_eq_mod : forall x y, (x mod 18446744073709551616 = y mod 18446744073709551616)%Z -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact H.
Qed.
