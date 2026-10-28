(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Atp_activewA Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition IMP_GUARD_A : Z := 0x6bc040.
Definition IMP_VEC_OBJ_A : Z := 0x6bc000.
Definition IMP_AMEMSET_A : Z := 0x84bc4.
Definition IMP_GRSI_A : Z := 0xb4a38.
Definition IMP_GACQ_A : Z := 0xfd430.
Definition IMP_GREL_A : Z := 0xfd480.
Definition IMP_OPDEL_A : Z := 0x119d50.

Definition IMP_OKARM_STACK_A : Z := PJ_SER_STACK_A + 1024.

Definition IMP_PUT_COST_A : Z := 2^30.
Definition imp_okarm_costA (n : Z) : Z := 2 * n + 2 + 2^30 + IMP_PUT_COST_A.

Definition IMP_OKARM_LIVE_A : Z := 6.

Definition libm (m : mem) : Prop :=
  rw_cells bsegs m 0x6bc120 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x6bc140 [C1 z8; C1 z8]
  /\ rw_cells bsegs m 0x6bc1c0 [C8 (Z_to_bv 64 0x17a090); C8 (Z_to_bv 64 0x29a80); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x2cda0); C8 (Z_to_bv 64 31); C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x6bc220 [C1 one8; C1 one8].
