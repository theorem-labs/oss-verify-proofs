(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Test file (a Theorem Labs lane; a build target of every glue green): control for the gate 6h check. Without SinkGuard, the released YI5b instance
   resolves a bare sink head. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16 YI5b YI14 YI5c.
Check (_ : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head).
Check (_ : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI14.sink_syms).
