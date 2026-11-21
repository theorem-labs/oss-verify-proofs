(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* Lib/PropExec at rocq-LPS , in the dhc1 layout: a
   re-export of Common/PropExec ('s own, renamed into this namespace) and of Lib/LiaTuning, plus this package's
   own page_round_up_Z_le, word for word. The r30q2 text is kept aside. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Common Require Export PropExec.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Lib Require Export LiaTuning.

Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
  assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.
