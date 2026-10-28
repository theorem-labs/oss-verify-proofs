(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qz X1r0 X1r1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1it.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition hstream_ok {ptr : Type} (os : stream_st ptr) : Prop :=
stream_inv os /\ body_inv os /\ lacing_vals_ok (os_lacing os) /\ granules_ok (os_granules os)
/\ 0 <= os_body_storage os /\ 0 <= os_lacing_storage os
/\ (os_body_data os = None -> os_body_storage os = 0)
/\ (os_lacing_vals os = None -> os_lacing_storage os = 0)
/\ (os_granule_vals os = None -> os_lacing_storage os = 0)

/\ (os_body_data os <> None -> 16384 <= os_body_storage os)
/\ (os_lacing_vals os <> None -> 1024 <= os_lacing_storage os)
/\ ((os_body_data os <> None /\ os_lacing_vals os <> None /\ os_granule_vals os <> None) \/ os = stream_zero).

Definition pagein_leaf_stmt : Prop :=
forall (St ptr : Type) (lib_realloc : ptr -> Z -> M St (option ptr)) (lib_free : ptr -> M St unit)
(os : stream_st ptr) (hdr body : list Z) (s s' : St) (r : Z) (os' : stream_st ptr),
hstream_ok os ->
bytes_ok hdr -> 27 <= zlength hdr -> 0 <= znth hdr 26 -> zlength hdr = 27 + znth hdr 26 ->
zsum (lacing_of hdr) = zlength body -> bytes_ok body ->
in_leaves (ogg_stream_pagein lib_realloc lib_free os hdr body s) (Ok ((r, os'), s')) ->
(r = 0 \/ r = -1)
/\ hstream_ok os'
/\ (os_serialno os' = os_serialno os \/ os' = stream_zero)
/\ 0 <= os_lacing_fill os' <= os_lacing_fill os + znth hdr 26 + 1
/\ 0 <= os_body_fill os' <= os_body_fill os + zlength body
/\ os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32)
/\ os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024).
