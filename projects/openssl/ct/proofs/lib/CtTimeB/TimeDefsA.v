(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition OSSL_ASCII_ISDIGIT_A : Z := 0x1ff8e4.          (* [comment removed for export] *)
Definition ASN1_STRING_COPY_A : Z := 0x2225cc.            (* [comment removed for export] *)
Definition OSSL_ASN1_STRING_SET_INTERNAL_A : Z := 0x222738.
Definition ASN1_STRING_GET_LENGTH_A : Z := 0x223158.      (* [comment removed for export] *)
Definition ASN1_STRING_GET0_DATA_A : Z := 0x2231b4.       (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_NEW_A : Z := 0x24a164.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_FREE_A : Z := 0x24a188.  (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_TO_TM_A : Z := 0x273e04.       (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_FROM_TM_A : Z := 0x274b80.     (* [comment removed for export] *)
Definition ASN1_TIME_PRINT_A : Z := 0x274f80.            (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_PRINT_EX_A : Z := 0x274fac.    (* [comment removed for export] *)
Definition OPENSSL_TM_TO_POSIX_A : Z := 0x275498.        (* [comment removed for export] *)
Definition OPENSSL_POSIX_TO_TM_A : Z := 0x2757fc.        (* [comment removed for export] *)
Definition OPENSSL_GMTIME_A : Z := 0x275bc4.             (* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ_A : Z := 0x275c38.         (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_SET_STRING_A : Z := 0x275e44.  (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_ADJ_A : Z := 0x27606c.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_PRINT_A : Z := 0x276344. (* [comment removed for export] *)
Definition E_ASAN_MEMSET_A : Z := 0x1bddfc.              (* [comment removed for export] *)
Definition E_ASAN_MEMCPY_A : Z := 0x1bd960.
