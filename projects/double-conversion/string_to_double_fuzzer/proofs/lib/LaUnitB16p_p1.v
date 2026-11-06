(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceB LaState LaMem LaStep LaCheck LaUnitSplit LaUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAM LAI LAC LAU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaUnitB16p_def.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma B16p_part1 : leaves_ok (run_some UNIT_B16p 0 (un_cuts UNIT_B16p) [11; 12; 14; 36; 37; 41; 46; 54; 56; 57; 65; 74; 75; 81; 106; 117; 119; 132]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
