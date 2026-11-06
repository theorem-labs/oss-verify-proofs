(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0w.v, with its module paths changed. *)
From Stdlib Require Import ZArith.
Inductive asym : Type :=
| AS_asan_stack_malloc_A
| AS_asan_memset
| AS_fopen
| AS_malloc
| AS_asan_memcpy
| AS_cgif_raw_newgif
| AS_fclose
| AS_free
| AS_asan_report_load2
| AS_asan_report_store4
| AS_asan_report_load4
| AS_asan_report_load8
| AS_asan_report_store8
| AS_fwrite
| AS_asan_report_load1
| AS_memcmp_2
| AS_asan_report_store2
| AS_asan_report_store1
| AS_memcmp
| AS_asan_stack_malloc_B
| AS_cgif_raw_addframe
| AS_cgif_raw_close.
