(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin LxState LxMem LxStep LxCheck LxUnitSplit LxEnvP LxUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC LXU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxUnitPA_def.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma PA_part3 : leaves_ok (run_some UNIT_PA 0 (un_cuts UNIT_PA) [9; 13; 16; 30; 32; 34; 35; 38; 40; 42; 43; 47; 52; 53; 55; 56; 57; 60; 62; 65; 66; 67; 71; 72; 78; 79; 82; 84; 88; 89; 90; 93; 94; 95; 100; 105]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
