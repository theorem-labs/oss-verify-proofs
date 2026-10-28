(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SCT_FREE : Z := 0x19d50c.              (* [comment removed for export] *)
Definition SCT_LIST_FREE : Z := 0x19d5bc.         (* [comment removed for export] *)
Definition SK_SCT_FREEFUNC_THUNK : Z := 0x19d0c8. (* [comment removed for export] *)
Definition OPENSSL_SK_POP_FREE : Z := 0xe76ac.
Definition OPENSSL_SK_FREE : Z := 0xe6cc4.
Definition OPENSSL_SK_VALUE : Z := 0xe77d4.
Definition SCT_NEW : Z := 0x19d4bc.
Definition A_CT_SCT_C : Z := 0x17454.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SCT_SIZE : Z := 104.
Definition SCTO_VERSION : Z := 0.
Definition SCTO_SCT : Z := 8.
Definition SCTO_SCT_LEN : Z := 16.
Definition SCTO_LOG_ID : Z := 24.
Definition SCTO_LOG_ID_LEN : Z := 32.
Definition SCTO_TIMESTAMP : Z := 40.
Definition SCTO_EXT : Z := 48.
Definition SCTO_EXT_LEN : Z := 56.
Definition SCTO_ALGS : Z := 64.
Definition SCTO_SIG : Z := 72.
Definition SCTO_SIG_LEN : Z := 80.
Definition SCTO_ENTRY_TYPE : Z := 88.
Definition SCTO_SOURCE : Z := 92.
Definition SCTO_VALIDATION : Z := 96.

Definition STACK_SIZE : Z := 56.
Definition SKO_NUM : Z := 0.
Definition SKO_DATA : Z := 8.
Definition SKO_SORTED : Z := 16.
Definition SKO_NUM_ALLOC : Z := 20.
Definition SKO_COMP : Z := 24.
Definition SKO_CMP_THUNK : Z := 32.
Definition SKO_FREE_THUNK : Z := 40.
Definition SKO_COPY_THUNK : Z := 48.
