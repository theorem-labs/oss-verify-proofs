(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dk.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ub_ptr_guard_nonneg : forall base idx, 0 <= idx < 2^63 ->
Z.lxor (Z.lxor (Z.b2z (base + idx <? base)) (Z.b2z (Z.lxor idx 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof.
intros base idx Hi. change 9223372036854775808 with (2^63). rewrite (zb_lxor_pow2_small idx 63) by lia.
replace (base + idx <? base) with false by (symmetry; apply Z.ltb_ge; lia).
replace (idx + 2^63 <? 2^63) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
