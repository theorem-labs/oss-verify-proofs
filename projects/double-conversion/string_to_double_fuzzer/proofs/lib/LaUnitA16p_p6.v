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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaUnitA16p_def.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma A16p_part6 : leaves_ok (run_some UNIT_A16p 0 (un_cuts UNIT_A16p) [12; 25; 32; 35; 36; 37; 48; 54; 63; 68; 72; 83; 94; 99; 111; 114; 120; 126; 127; 133; 138; 143]%nat) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
