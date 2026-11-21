(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkA Require Import CrcAGlue.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land31_shl2_range : forall k, 0 <= Z.land k 31 ≪ 2 <= 124.
Proof.
  intros k. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
  assert (0 <= Z.land k 31 <= 31).
  { replace (Z.land k 31) with (k mod 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound k 32 ltac:(lia)). lia. }
  lia.
Qed.

Lemma x2n_guard_dead : forall k lim, 124 < lim -> ~ (lim < Z.land k 31 ≪ 2 mod 18446744073709551616).
Proof.
  intros k lim H C. pose proof (land31_shl2_range k) as R. rewrite Z.mod_small in C by lia. lia.
Qed.
