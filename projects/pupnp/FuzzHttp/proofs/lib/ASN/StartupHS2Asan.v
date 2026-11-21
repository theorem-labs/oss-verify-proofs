(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: hand-off states of the start-up chain computed in the build at LPS 727298f3, for each CONFIG_RSEQ value, under a variable map read from probe runs. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  AxSymExec3 AsanPlanCore AsanPlan PlanRegen StartupHSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the main phase's entry states of the ASan image, per CONFIG_RSEQ value, computed
   from the last start-up segment's check (see [StartupHSAsan]); hand-off 1 and hand-off 2 are
   the two paths of the plan's last case split. *)
Definition aM2_0 : list (nat * acs) := Eval vm_compute in
  collect_k (fun h => h) 20 (arun aIT2 0 (nxt aSD0) aSD0 aplan2) [].
Definition aS21_0 : acs := Eval vm_compute in hget aM2_0 1 aSD0.
Definition aS22_0 : acs := Eval vm_compute in hget aM2_0 2 aSD0.
Definition aHS2_0 : nat -> option acs := hs2 1 aS21_0 2 aS22_0.

Definition aM2_1 : list (nat * acs) := Eval vm_compute in
  collect_k (fun h => h) 20 (arun aIT2 1 (nxt aSD1) aSD1 aplan2) [].
Definition aS21_1 : acs := Eval vm_compute in hget aM2_1 1 aSD1.
Definition aS22_1 : acs := Eval vm_compute in hget aM2_1 2 aSD1.
Definition aHS2_1 : nat -> option acs := hs2 1 aS21_1 2 aS22_1.

Definition ash2_0 : shape := Eval vm_compute in sh_of (arun aIT2 0 (nxt aSD0) aSD0 aplan2 aHS2_0).
Definition ash2_1 : shape := Eval vm_compute in sh_of (arun aIT2 1 (nxt aSD1) aSD1 aplan2 aHS2_1).
