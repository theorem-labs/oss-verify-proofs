(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Atp_activewA Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition IMP_GUARD_A : Z := 0x6add80.
Definition IMP_VEC_OBJ_A : Z := 0x6add40.
Definition IMP_AMEMSET_A : Z := 0x84a08.
Definition IMP_GRSI_A : Z := 0xb487c.
Definition IMP_GACQ_A : Z := 0xef780.
Definition IMP_GREL_A : Z := 0xef7d0.
Definition IMP_OPDEL_A : Z := 0x10c0a0.

Definition IMP_OKARM_STACK_A : Z := PJ_SER_STACK_A + 1024.

Definition IMP_PUT_COST_A : Z := 2^30.
Definition imp_okarm_costA (n : Z) : Z := 2 * n + 2 + 2^30 + IMP_PUT_COST_A.

Definition IMP_OKARM_LIVE_A : Z := 6.

Definition libm (m : mem) : Prop :=
  rw_cells asegs m 0x6ade60 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x6ade80 [C1 z8; C1 z8]
  /\ rw_cells asegs m 0x6adf00 [C8 (Z_to_bv 64 0x16c310); C8 (Z_to_bv 64 0x29900); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x2cfe0); C8 (Z_to_bv 64 31); C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x6adf60 [C1 one8; C1 one8].
