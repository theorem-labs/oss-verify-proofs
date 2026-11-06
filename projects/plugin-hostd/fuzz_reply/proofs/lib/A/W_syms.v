(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the symbols fuzz_reply.asan's program text calls, in the form of proofs/cgif/cgif_file_fuzzer/lib/YI0w.v. *)
From Stdlib Require Import ZArith.
Inductive wsym : Type :=
| WS_asan_stack_malloc_0
| WS_write
| WS_pthread_join
| WS_pthread_mutex_lock
| WS_free
| WS_pthread_mutex_unlock
| WS_asan_report_load8
| WS_asan_report_load4
| WS_asan_report_store4
| WS_asan_report_store8
| WS_strlen
| WS_errno_location
| WS_realloc
| WS_asan_memcpy
| WS_asan_handle_no_return
| WS_abort
| WS_asan_memset
| WS_fprintf
| WS_asan_stack_malloc_1
| WS_snprintf
| WS_strncmp
| WS_asan_memmove
| WS_memchr
| WS_strrchr
| WS_strcmp
| WS_strndup
| WS_asan_report_load1
| WS_asan_report_store1
| WS_strnlen
| WS_malloc
| WS_bcmp.
