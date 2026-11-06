(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqyb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qqyb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.

Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Ltac mem_after_store ::= mem_after_store_fast. Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
