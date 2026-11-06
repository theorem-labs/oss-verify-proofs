(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_HdrBits () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma testbit_small_high : forall x i, 0 <= x < 256 -> 8 <= i -> Z.testbit x i = false.
Proof.
  intros x i Hx Hi. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 8) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

#[using="Type"] Lemma testbit_256mul_low : forall b i, 0 <= b -> 0 <= i < 8 -> Z.testbit (256 * b) i = false.
Proof. intros b i Hb Hi. replace (256 * b) with (b * 2^8) by lia. apply Z.mul_pow2_bits_low. lia. Qed.

#[using="Type"] Lemma land_byte_256mul : forall x b, 0 <= x < 256 -> 0 <= b -> Z.land x (256 * b) = 0.
Proof.
  intros x b Hx Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8).
  - rewrite testbit_256mul_low by lia. apply Bool.andb_false_r.
  - rewrite testbit_small_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma add_256mul_lxor : forall x b, 0 <= x < 256 -> 0 <= b -> x + 256 * b = Z.lxor x (256 * b).
Proof. intros x b Hx Hb. symmetry. symmetry. rewrite <- Z.add_nocarry_lxor; [reflexivity|]. apply land_byte_256mul; lia. Qed.

#[using="Type"] Lemma lxor_byte_bound : forall x c, 0 <= x < 256 -> 0 <= c < 256 -> 0 <= Z.lxor x c < 256.
Proof.
  intros x c Hx Hc. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor x c) 0) as [->|NZ]; [lia|].
  apply (Z.log2_lt_cancel); rewrite ?Z.log2_pow2 by lia.
  assert (L : Z.log2 (Z.lxor x c) <= Z.max (Z.log2 x) (Z.log2 c)) by (apply Z.log2_lxor; lia).
  assert (Z.log2 x < 8) by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 c < 8) by (destruct (Z.eq_dec c 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  change (Z.log2 256) with 8. lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma w0_land : forall st b1 c, 0 <= st < 256 -> 0 <= b1 -> 0 <= c < 256 -> Z.land (st + 256 * b1) c = Z.land st c.
Proof.
  intros st b1 c Hs Hb Hc. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 8).
  - f_equal. rewrite add_256mul_lxor, Z.lxor_spec by lia. rewrite testbit_256mul_low by lia. apply Bool.xorb_false_r.
  - rewrite (testbit_small_high c) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma w0_land255 : forall st b1, 0 <= st < 256 -> 0 <= b1 -> Z.land (st + 256 * b1) 255 = st.
Proof. intros. rewrite w0_land by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma w0_lxor : ltac2:(CDefT.buildp (gd_tbl_AW_HdrBits ()) "Pst,$0.Pb1,$0.Pc,$0.P,(1.(2.=R3.)(3.R3.+100.))P,(2.=R3.)P,(1.(2.=R3.)(3.R3.+100.))(4.$0.(5.(6.R6.(7.+100.R5.))R4.)(6.(5.R6.R4.)(7.+100.R5.)))")
(* [comment removed for export] *).
Proof.
  intros st b1 c Hs Hb Hc. pose proof (lxor_byte_bound st c Hs Hc) as B.
  rewrite (add_256mul_lxor st b1), (add_256mul_lxor (Z.lxor st c) b1) by lia.
  rewrite !Z.lxor_assoc. f_equal. apply Z.lxor_comm.
Qed.

#[using="Type"] Lemma w0_shiftr8 : forall st b1, 0 <= st < 256 -> 0 <= b1 -> Z.shiftr (st + 256 * b1) 8 = b1.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.

End ARUN_1.
