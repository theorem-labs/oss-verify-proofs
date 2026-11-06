(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1dd X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Export X0bp.
Import ListNotations.
Open Scope Z_scope.

Definition IMG_TOP : Z := 0x652000.

Definition client_consts (m : word -> option byte) : Prop :=
ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
/\ ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
/\ ro_cells asegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
/\ ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].
