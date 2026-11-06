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
Lemma PA_part1 : leaves_ok (run_some UNIT_PA 0 (un_cuts UNIT_PA) [1; 4; 5; 6; 7; 10; 15; 17; 20; 25; 27; 28; 29; 37; 39; 41; 49; 51; 54; 61; 63; 69; 70; 76; 81; 83; 85; 86; 98; 99; 101; 102; 104]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
