(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface BnContract LxCheck LxInstP LxInstU LxFinalIn
  LxUnitPA LxUnitUA BnP_cbd3 BnU_cbd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem lib_P : lib_stmt_P.
Proof.
  refine (lib_P_of_unit UNIT_PA _ _ _ _ chk_PA _ cbd_P);
    [reflexivity | reflexivity | apply (nth_error_In _ 0%nat); vm_compute; reflexivity | apply (nth_error_In _ 102%nat); vm_compute; reflexivity | reflexivity].
Qed.

Theorem lib_U : lib_stmt_U.
Proof.
  refine (lib_U_of_unit UNIT_UA _ _ _ _ chk_UA _ cbd_U);
    [reflexivity | reflexivity | apply (nth_error_In _ 0%nat); vm_compute; reflexivity | apply (nth_error_In _ 88%nat); vm_compute; reflexivity | reflexivity].
Qed.
