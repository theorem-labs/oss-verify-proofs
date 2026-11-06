(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export Walk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


Ltac zb_masks_in H :=
  repeat match type of H with
  | context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2 ^ 64 `div` 2)%Z with (2^63)%Z.
  destruct (Z.lt_ge_cases z 0).
  - replace (z mod 2^64)%Z with (z + 2^64)%Z.
    2:{ replace z with ((z + 2^64) + (-1) * 2^64)%Z at 2 by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    replace (z + 2^64 + 2^63)%Z with ((z + 2^63) + 1 * 2^64)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => is_Zlit_zb z; rewrite (signed_of_Z z) in H by lia
  end.

Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  | |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
  end.
Ltac zs_idioms_sf_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  | context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
  end.
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
