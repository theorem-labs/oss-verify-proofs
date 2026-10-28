(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition A_RSA_INFO : Z := 0x0f2180.
Definition A_ECKEY_INFO : Z := 0x0f2200.
Definition A_ECKEYDH_INFO : Z := 0x0f2280.
Definition A_ECDSA_INFO : Z := 0x0f2300.
Definition A_EC_INFOS : list Z := [A_ECKEY_INFO; A_ECKEYDH_INFO; A_ECDSA_INFO].
