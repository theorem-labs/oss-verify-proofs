(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_AM. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Malloc Require MM07. Import MM07. Import MM07.MallocFacts_AMP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require Import RMalloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PM02. Import PM02. Import PM02.RAllocSlot_iface. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PM15. Import PM15. Import PM15.RF_malloc_core. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PM06. Import PM06. Import PM06.RF_malloc_top. Import PM02.RASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PM07. Import PM07. Import PM07.RF_alloc_slot. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require Import RF_malloc_big. Import PM06.RF_am_P. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require Import RF_alloc_meta.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PM01.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import PM01. Import PM01.RunDraw.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End CANSEC1.
