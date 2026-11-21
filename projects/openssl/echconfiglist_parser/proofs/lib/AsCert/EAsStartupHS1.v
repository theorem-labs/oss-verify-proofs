(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state replaced by the states the start-up run reaches at LPS 727298f3, computed in the build, one per CONFIG_RSEQ value; the root plan renumbered by a map read from a probe. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit AsHSTab AsPlanRegen.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the states at hand-off 90, COMPUTED in the build, one per CONFIG_RSEQ value (the
   certificate-data method of OSSV-343, as boost-beast/http_request and jsoncons/fuzz_bigint do; the state
   recorded against the earlier model is not reached: it holds the old 160-byte auxv's words).
   [vsh_root]: the launch has V_G, V_R and V_GID (NX0 11 -> 14) and the run reads more of the auxv, so
   the root plan's fresh variables move; the map is read from the run (old fresh variable 44 is new 50 and 61 is new 67 (the thread-id word at 12248488 and its KRange 1 4194303, the words at 12248640 and 12379792), and the root plan's first PRangeGaps the run refuses names old 94 where the run's newest region is 4096 * EVar 100; with this map the run reaches hand-off 90 at counter 267 (recorded 261) at both CONFIG_RSEQ values).
   The run's own fuel and hand-off checks are the certificate's ([EAsStartupCert_startup_plan]:
   KC0 0, BFUEL 400000, FUEL 3000), which re-checks the root plan against these states. *)
Definition vsh_root : nat -> nat := tshift [(44%nat, 6%nat)].
Definition startup_plan_k : plan := psh vsh_root startup_plan.
Definition root_run (r : Z) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T 0%nat 400000%nat 3000%nat None (hinit r) startup_plan_k.
Definition HS1_easan_90_0 : acs := Eval vm_compute in hstate (collect_k 6 (root_run 0) []) (hinit 0) 90.
Definition HS1_easan_90_1 : acs := Eval vm_compute in hstate (collect_k 6 (root_run 1) []) (hinit 1) 90.
Definition HS1_easan_table_0 : list (nat * acs) := [(90%nat, HS1_easan_90_0)].
Definition HS1_easan_table_1 : list (nat * acs) := [(90%nat, HS1_easan_90_1)].
Definition HS1_easan_0 (h : nat) : option acs := hs_lookup h HS1_easan_table_0.
Definition HS1_easan_1 (h : nat) : option acs := hs_lookup h HS1_easan_table_1.
Definition HS1_easan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HS1_easan_1 else HS1_easan_0.
