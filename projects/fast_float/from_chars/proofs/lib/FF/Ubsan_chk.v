(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma lxor_high : forall x, (0 <= x < 2 ^ 63)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
  intros x Hx. symmetry. rewrite Z.add_comm, Z.lxor_comm. change 9223372036854775808%Z with (1 * 2 ^ 63)%Z.
  apply Z.add_nocarry_lxor. apply land_mulpow2_small; lia.
Qed.

Lemma lxor_high' : forall x, (2 ^ 63 <= x < 2 ^ 64)%Z -> Z.lxor x 9223372036854775808 = (x - 9223372036854775808)%Z.
Proof.
  intros x Hx. pose proof (lxor_high (x - 9223372036854775808) ltac:(lia)) as E.
  replace (x - 9223372036854775808 + 9223372036854775808)%Z with x in E by lia.
  rewrite <- E at 1. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Lemma lm_signed_lit : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.lt_ge_cases z 0) as [Hneg|Hpos].
  - rewrite <- (Z.mod_unique_pos z (2^64) (-1) (z + 2^64)) by lia.
    replace (z + 2 ^ 64 <? 2 ^ 63)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia.
    replace (z <? 2 ^ 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma land7_lor_aligned : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a mod 8 = 0)%Z -> (b mod 8 = 0)%Z ->
  Z.land (Z.lor a b) 7 = 0%Z.
Proof.
  intros a b Ha Hb Ma Mb. rewrite Z.land_lor_distr_l.
  change 7%Z with (Z.ones 3). rewrite !Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. rewrite Ma, Mb. reflexivity.
Qed.

Lemma land7_aligned_off : forall a k, (0 <= a)%Z -> (0 <= k)%Z -> (a mod 8 = 0)%Z -> (k mod 8 = 0)%Z -> Z.land (a + k) 7 = 0%Z.
Proof.
  intros a k Ha Hk Ma Mk. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite Z.add_mod, Ma, Mk by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma neg_mod64 : forall d n, (0 < n < 2 ^ 64)%Z -> ((d - (d + n)) mod 18446744073709551616 = 18446744073709551616 - n)%Z.
Proof. intros d n Hn. symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia. Qed.

Ltac decide_ltb_in H :=
  repeat match type of H with
  | context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true in H by (symmetry; apply Z.ltb_lt; lia)
            | replace (Z.ltb a b) with false in H by (symmetry; apply Z.ltb_ge; lia) ]
  end; cbn [Z.b2z negb xorb Z.lxor Z.lor Z.land] in H.

(* [comment removed for export] *)
Ltac kill_check := let Hc := fresh "Hc" in if_cases Hc;
  [ cond_cleanup Hc; repeat (rewrite Z.mod_small in Hc by lia); rewrite ?lxor_high in Hc by lia;
    decide_ltb_in Hc; exfalso; first [discriminate | lia] | clear Hc ].
(* [comment removed for export] *)
Ltac pass_check := let Hc := fresh "Hc" in if_cases Hc;
  [ clear Hc | cond_cleanup Hc; repeat (rewrite Z.mod_small in Hc by lia); rewrite ?lxor_high in Hc by lia;
    decide_ltb_in Hc; exfalso; first [discriminate | lia] ].
