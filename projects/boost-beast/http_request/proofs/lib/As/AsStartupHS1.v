(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state replaced by the states the start-up run reaches at LPS 727298f3, computed in the build, one per CONFIG_RSEQ value; the root plan renumbered by a map read from a probe. *)
(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsImages AsPlanImages AsStartup AsStartupPlan AsStartupRanges AsPlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3: the states at hand-off 90, COMPUTED in the build, one per CONFIG_RSEQ value
   (the certificate-data method, as jsoncons/fuzz_bigint and double-conversion use it; the state
   recorded against the earlier model is not reached: it holds the old 160-byte auxv's words).
   [vsh_root]: [V_GID] takes the old NX0 13 and the run reads more of the auxv, so each fresh variable
   of the root plan is the recording's + 5, read from the run (a probe of the run: at the root plan's PRangeGaps 94 the run's new region is 4096 * EVar 99, and with this map the root plan reaches hand-off 90 at both values with the fresh counter at 266 = 261 + 5).
   The two values' states at 90 have equal registers, maps, vis, ghost, brk, fd, tid flag, vm
   operations and bounds, and differ in knowledge (the auxv tail and [V_R]'s value); seg90 needs that
   knowledge (from the two states' join it stops at its 13th node, a probe of the run), so the table is one per
   value.  [AsStartupCert1] re-checks the root plan from [hinit r] against [HS1_asan_r r]. *)
Definition vsh_root : nat -> nat := vshift 13 5.
Definition startup_plan_k : plan := psh vsh_root startup_plan.
Definition root_run (r : Z) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit r) startup_plan_k.
Definition HS1_asan_90_0 : acs := Eval vm_compute in hstate (collect_k 6 (root_run 0) []) (hinit 0) 90.
Definition HS1_asan_90_1 : acs := Eval vm_compute in hstate (collect_k 6 (root_run 1) []) (hinit 1) 90.
Definition HS1_asan_table_0 : list (nat * acs) := [(90%nat, HS1_asan_90_0)].
Definition HS1_asan_table_1 : list (nat * acs) := [(90%nat, HS1_asan_90_1)].
Definition HS1_asan_0 (h : nat) : option acs := hs_lookup h HS1_asan_table_0.
Definition HS1_asan_1 (h : nat) : option acs := hs_lookup h HS1_asan_table_1.
Definition HS1_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HS1_asan_1 else HS1_asan_0.
