(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ri_cells (mtx nf mfa au mu na nfr : Z) : list cell :=
  [C8 (Z_to_bv 64 mtx); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
   C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nfr);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Definition RIc (c RI : Z) : Z := RI + 128 * c.
(* [comment removed for export] *)
Lemma class_size_small : forall k, 1 <= k <= 16 -> class_size k = 32 * k.
Proof. clear. intros k Hk. unfold class_size, kMidClass, kMinSize. replace (k <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_roundup18 : forall x, 0 <= x < 2^62 -> Z.land (x + 262143) 18446744073709289472 = 262144 * ((x + 262143) / 262144).
Proof.
  intros x Hx. change 18446744073709289472 with (2^64 - 2^18). rewrite land_align_down by lia. change (2^18) with 262144.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma roundup18_next : forall mfa x, 0 <= mfa -> mfa mod 262144 = 0 -> mfa < x <= mfa + 262144 -> 262144 * ((x + 262143) / 262144) = mfa + 262144.
Proof. intros mfa x H0 HM HX. Z.div_mod_to_equations. nia. Qed.
