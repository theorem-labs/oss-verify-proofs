(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import HeapIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PESHZ.
Lemma bat0_of_shadow_zero (M : word -> option byte) (lo g a : Z) :
  shadow_zero M lo g -> lo mod 8 = 0 -> lo <= a -> a + 1 <= lo + 8 * g -> byte_at M (S a) 0.
Proof.
  intros SZ Hlo H1 H2.
  assert (E : S a = S lo + (a - lo) / 8).
  { unfold S. assert (L8 : lo = (lo / 8) * 8) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
    replace a with ((a - lo) + (lo / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  rewrite E. apply SZ. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
End PESHZ.
