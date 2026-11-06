(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Zks Zkt Zm2 RT_rep Zl3 Zls Zi8 Zm0 Zkr Zi6 Zkm Zkn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_contracts2 : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts2 RTA.
Proof. intros RF CS FR. exact (mkRTC2 RTA (rta_contracts RF CS FR) rta_stack_malloc_1 rta_memmove2 rta_memcmp_wide rta_annotate rta_memcmp_zero). Qed.
