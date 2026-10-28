(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Lemma slliw3_neg : forall d, - 2^28 <= d <= 0 -> bv_swrap 32 ((d mod 18446744073709551616) ≪ 3) = 8 * d.
Proof.
intros d Hd.
rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. apply swrap32_eqm; [lia|].
change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
destruct (Z.eq_dec d 0) as [->|N]; [reflexivity|].
assert (E : d mod 2^64 = d + 2^64) by (symmetry; apply (Z.mod_unique_pos d (2^64) (-1) (d + 2^64)); lia).
rewrite E. replace ((d + 2^64) * 8 - 8 * d) with (2^35 * 2^32) by lia. apply Z.mod_mul. lia.
Qed.
Lemma sub_mod64_word : forall a b, Z_to_bv 64 (a - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply Z_to_bv_eqm. change 18446744073709551616 with (2^64).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma subw_mod64 : forall a b, - 2^31 <= a - b < 2^31 -> bv_swrap 32 (a - b mod 18446744073709551616) = a - b.
Proof.
intros a b H.
apply swrap32_eqm; [lia|]. change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
rewrite (Z.mod_eq b (2^64)) by lia. replace (a - (b - 2^64 * (b / 2^64)) - (a - b)) with ((2^32 * (b / 2^64)) * 2^32) by lia.
apply Z.mod_mul. lia.
Qed.
