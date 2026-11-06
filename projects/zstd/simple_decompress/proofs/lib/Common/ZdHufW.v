(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zext32_sh30 : forall x, 0 <= x < 4294967296 -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 30) = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zext32_sh31' : forall x, 0 <= x < 4294967296 -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 31) = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (2 * 2^31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zext32_sh32 : forall x, 0 <= x < 4294967296 -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32) = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma land_m2 : forall x, 0 <= x < 1024 -> Z.land x 18446744073709551614 = 2 * (x / 2).
Proof.
  assert (B : forallb (fun x => Z.land x 18446744073709551614 =? 2 * (x / 2)) (map Z.of_nat (seq 0 1024)) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.
