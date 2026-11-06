(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition OSSL_ASCII_ISDIGIT : Z := 0xe6e08.          (* [comment removed for export] *)
Definition ASN1_STRING_COPY : Z := 0xf5940.            (* [comment removed for export] *)
Definition OSSL_ASN1_STRING_SET_INTERNAL : Z := 0xf59d0.
Definition ASN1_STRING_GET_LENGTH : Z := 0xf5f48.      (* [comment removed for export] *)
Definition ASN1_STRING_GET0_DATA : Z := 0xf5f6c.       (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_NEW : Z := 0x108778.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_FREE : Z := 0x10879c.  (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_TO_TM : Z := 0x11d2fc.       (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_FROM_TM : Z := 0x11d958.     (* [comment removed for export] *)
Definition ASN1_TIME_PRINT : Z := 0x11dae4.            (* [comment removed for export] *)
Definition OSSL_ASN1_TIME_PRINT_EX : Z := 0x11db10.    (* [comment removed for export] *)
Definition OPENSSL_TM_TO_POSIX : Z := 0x11dd04.        (* [comment removed for export] *)
Definition OPENSSL_POSIX_TO_TM : Z := 0x11df4c.        (* [comment removed for export] *)
Definition OPENSSL_GMTIME : Z := 0x11e22c.             (* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ : Z := 0x11e26c.         (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_SET_STRING : Z := 0x11e318.  (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_ADJ : Z := 0x11e3ac.   (* [comment removed for export] *)
Definition ASN1_GENERALIZEDTIME_PRINT : Z := 0x11e43c. (* [comment removed for export] *)
Definition MEMSET : Z := 0x2781a0.                     (* [comment removed for export] *)

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
