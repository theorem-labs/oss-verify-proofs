(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YI5b.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YH03.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YI16.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
#[global] Instance src0_sink_head : sink_head := {| sk_ofl_head := src0_D_ofl_head |}.
