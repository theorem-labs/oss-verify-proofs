(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1dd X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9.
Import ListNotations.
Open Scope Z_scope.

Definition gB_GOT_shadow_offset_cell : Z := 0xfc118.
Definition gB_shadow_memory_dynamic_address : Z := 0x105ab8.
Definition gB_GOT_detect_uar : Z := 0xfc170.
Definition gB_detect_stack_use_after_return : Z := 0x105ac0.
Definition IMG_TOP_B : Z := 0x65b000.

Definition client_constsB (m : word -> option byte) : Prop :=
ro_cells bsegs m gB_GOT_shadow_offset_cell [C8 (Z_to_bv 64 gB_shadow_memory_dynamic_address)]
/\ ro_cells bsegs m gB_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
/\ ro_cells bsegs m gB_GOT_detect_uar [C8 (Z_to_bv 64 gB_detect_stack_use_after_return)]
/\ ro_cells bsegs m gB_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].
