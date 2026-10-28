(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition OSSL_ASCII_ISDIGIT_A : Z := 0x205118.          (* [comment removed for export] *)
Definition ASN1_STRING_COPY_A : Z := 0x2242a0.            (* [comment removed for export] *)
Definition OSSL_ASN1_STRING_SET_INTERNAL_A : Z := 0x2243f8.
Definition ASN1_STRING_GET_LENGTH_A : Z := 0x224df0.      (* [comment removed for export] *)
Definition ASN1_STRING_GET0_DATA_A : Z := 0x224e40.       (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_NEW_A : Z := 0x247010.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_FREE_A : Z := 0x247034.  (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_TO_TM_A : Z := 0x26ec34.       (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_FROM_TM_A : Z := 0x26f848.     (* [comment removed for export] *)
Definition ASN1_TIME_PRINT_A : Z := 0x26fc1c.            (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_PRINT_EX_A : Z := 0x26fc48.    (* [comment removed for export] *)
Definition OPENSSL_TM_TO_POSIX_A : Z := 0x2700d4.        (* [comment removed for export] *)
Definition OPENSSL_POSIX_TO_TM_A : Z := 0x270420.        (* [comment removed for export] *)
Definition OPENSSL_GMTIME_A : Z := 0x2707e8.             (* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ_A : Z := 0x270848.         (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_SET_STRING_A : Z := 0x270a34.  (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_ADJ_A : Z := 0x270c5c.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_PRINT_A : Z := 0x270f34. (* [comment removed for export] *)
Definition E_ASAN_MEMSET_A : Z := 0x1c2e6c.              (* [comment removed for export] *)
Definition E_ASAN_MEMCPY_A : Z := 0x1c29d0.
