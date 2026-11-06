(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LaState LaMem LaStep LaCheck LaUnitSplit LaUnitCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAM LAI LAC LAU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaUnitA0p_def.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma A0p_part7 : leaves_ok (run_some UNIT_A0p 0 (un_cuts UNIT_A0p) [8; 11; 13; 14; 17; 60; 74; 75; 77; 78; 81; 89; 100; 102; 112; 116; 124; 128; 132; 133; 141]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
