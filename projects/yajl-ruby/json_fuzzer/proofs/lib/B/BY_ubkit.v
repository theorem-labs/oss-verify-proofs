(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SysStep ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import KLink.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land7_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land3_of_mod4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land3_mod4 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land7_add8 : forall x k, Z.land (x + 8 * k) 7 = Z.land x 7.
Proof. intros x k. change 7 with (Z.ones 3). rewrite !Z.land_ones by lia. change (2^3) with 8. rewrite Z.mul_comm, Z_mod_plus_full. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x) by (apply Z.ldiff_ones_r_low; [lia| destruct (Z.eq_dec x 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]]).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.testbit x n) eqn:T; cbn.
  - destruct (Z.ltb_spec n 64); [reflexivity|]. exfalso.
    assert (Z.testbit x n = false) by (apply Z.bits_above_log2; [lia|]; destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]; pose proof (Z.log2_lt_pow2 x 64 ltac:(lia)); lia). congruence.
  - destruct (Z.ltb_spec n 64); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small' : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply (bv_swrap_small 32). unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?swrap32_small' by lia; rewrite ?signed_lit_small by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia);
  rewrite ?land7_mod8, ?land3_mod4 by lia;
  intro K; first [ lia | Z.div_mod_to_equations; lia ].

(* [comment removed for export] *)
Ltac gkill G := exfalso; revert G; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?swrap32_small' by lia; rewrite ?signed_lit_small by lia; intros G; lia.
Ltac xkill G :=
  exfalso; revert G; unfold wz; rewrite ?v_sltiu_b2z, ?v_sltu_b2z; rewrite ?unsigned_lit by lia;
  repeat match goal with
         | |- context [Z.ltb ?a ?b] => first [ replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia)
                                             | replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia) ] end;
  cbv [Z.b2z Z.lxor bv_wrap]; cbn; intros G; first [discriminate G| lia].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ugd := zstepA;
  (let G := fresh "G" in
   first [ if_cases G; zify_cond G; [ solve [kill G| gkill G| xkill G] | clear G ]
         | if_cases G; zify_cond G; [ clear G | solve [kill G| gkill G| xkill G] ]
         | if_cases G; zify_cond G; [ first [kill G| gkill G| xkill G| clear G] | first [kill G| gkill G| xkill G| clear G] ] ]).

(* [comment removed for export] *)
Ltac ubtrap K := if_cases K; zify_cond K; [ kill K | ].
(* [comment removed for export] *)
Ltac ubtrap2 K := if_cases K; zify_cond K; [ | kill K ].
