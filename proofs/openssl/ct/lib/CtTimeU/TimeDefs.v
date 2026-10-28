(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition OSSL_ASCII_ISDIGIT : Z := 0xebab4.          (* [comment removed for export] *)
Definition ASN1_STRING_COPY : Z := 0xfde44.            (* [comment removed for export] *)
Definition OSSL_ASN1_STRING_SET_INTERNAL : Z := 0xfdee4.
Definition ASN1_STRING_GET_LENGTH : Z := 0xfe4b8.      (* [comment removed for export] *)
Definition ASN1_STRING_GET0_DATA : Z := 0xfe4ec.       (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_NEW : Z := 0x11528c.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_FREE : Z := 0x1152b0.  (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_TO_TM : Z := 0x12c134.       (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_FROM_TM : Z := 0x12c938.     (* [comment removed for export] *)
Definition ASN1_TIME_PRINT : Z := 0x12cafc.            (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_PRINT_EX : Z := 0x12cb28.    (* [comment removed for export] *)
Definition OPENSSL_TM_TO_POSIX : Z := 0x12cd90.        (* [comment removed for export] *)
Definition OPENSSL_POSIX_TO_TM : Z := 0x12cfe8.        (* [comment removed for export] *)
Definition OPENSSL_GMTIME : Z := 0x12d2c8.             (* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ : Z := 0x12d31c.         (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_SET_STRING : Z := 0x12d3d4.  (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_ADJ : Z := 0x12d468.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_PRINT : Z := 0x12d4f8. (* [comment removed for export] *)
Definition MEMSET : Z := 0x2bdcfc.                     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TM_SIZE : Z := 56.
Definition TMO_SEC : Z := 0.
Definition TMO_MIN : Z := 4.
Definition TMO_HOUR : Z := 8.
Definition TMO_MDAY : Z := 12.
Definition TMO_MON : Z := 16.
Definition TMO_YEAR : Z := 20.
Definition TMO_WDAY : Z := 24.
Definition TMO_YDAY : Z := 28.
Definition TMO_ISDST : Z := 32.
Definition TMO_GMTOFF : Z := 40.
Definition TMO_ZONE : Z := 48.

(* [comment removed for export] *)
Definition ASO_LENGTH : Z := 0.
Definition ASO_TYPE : Z := 4.
Definition ASO_DATA : Z := 8.
Definition ASO_FLAGS : Z := 16.
Definition V_ASN1_GENERALIZEDTIME : Z := 24.
