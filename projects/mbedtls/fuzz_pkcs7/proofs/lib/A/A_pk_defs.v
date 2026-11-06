(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition A_RSA_INFO : Z := 0x0eedc0.
Definition A_ECKEY_INFO : Z := 0x0eee40.
Definition A_ECKEYDH_INFO : Z := 0x0eeec0.
Definition A_ECDSA_INFO : Z := 0x0eef40.
Definition A_EC_INFOS : list Z := [A_ECKEY_INFO; A_ECKEYDH_INFO; A_ECDSA_INFO].
