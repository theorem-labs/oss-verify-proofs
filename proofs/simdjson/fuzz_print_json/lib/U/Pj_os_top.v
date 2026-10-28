(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_os_defs Pj_os_xsputn Pj_os_ctor Pj_os_put Pj_os_dtor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem os_xsputn_closed : os_xsputn_stmt.
Proof. exact os_xsputn_proof. Qed.
Theorem os_ctor_closed : os_ctor_stmt.
Proof. exact os_ctor_proof. Qed.
Theorem os_put_closed : os_put_stmt.
Proof. exact (os_put_proof os_xsputn_proof). Qed.
Theorem ios_dtor_closed : ios_dtor_stmt.
Proof. exact ios_dtor_proof. Qed.
