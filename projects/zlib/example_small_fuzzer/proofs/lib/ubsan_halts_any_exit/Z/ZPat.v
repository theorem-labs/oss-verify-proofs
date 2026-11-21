(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import HarnessSmall ZApiInst ZTaint BoundPat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem PAT_init : forall g, PAT (dinit_of g).
Proof.
  intros g. unfold dinit_of, dFg. constructor; cbn [ds_level ds_strategy ds_wrap ds_status ds_gzhead ds_insert ds_lit_bufsize ds_w_size].
  - reflexivity.
  - reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - reflexivity.
  - left. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem PAT_actual_step : forall s_a x zc flush, DREL s_a x -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  PAT s_a -> PAT (fst (deflate_m s_a zc flush)).
Proof.
  intros s_a x zc flush R Hz Hf P. destruct (DREL_facts s_a x R) as (_ & HDD & _). exact (PAT_deflate_m s_a zc flush HDD Hz Hf P).
Qed.

Theorem PAT_actual_bits : forall s_a x, DREL s_a x -> PAT s_a -> ds_w_bits s_a = 15 /\ ds_hash_bits s_a = 15.
Proof. intros s_a x R P. destruct (DREL_facts s_a x R) as (_ & [D _] & _). exact (PAT_bits s_a D P). Qed.
