(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: hand-off states of the start-up chain computed in the build at LPS 727298f3, for each CONFIG_RSEQ value, under a variable map read from probe runs. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  AxSymExec3 AsanPlanCore AsanPlan PlanRegen StartupHSBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the main phase's entry states of the ASan+UBSan image, per CONFIG_RSEQ value,
   computed from the last start-up segment's check (see [StartupHSBoth]); hand-off 1 and
   hand-off 2 are the two paths of the plan's last case split. *)
Definition bM2_0 : list (nat * acs) := Eval vm_compute in
  collect_k (fun h => h) 20 (brun bIT2 0 (nxt bSD0) bSD0 bplan2) [].
Definition bS21_0 : acs := Eval vm_compute in hget bM2_0 1 bSD0.
Definition bS22_0 : acs := Eval vm_compute in hget bM2_0 2 bSD0.
Definition bHS2_0 : nat -> option acs := hs2 1 bS21_0 2 bS22_0.

Definition bM2_1 : list (nat * acs) := Eval vm_compute in
  collect_k (fun h => h) 20 (brun bIT2 1 (nxt bSD1) bSD1 bplan2) [].
Definition bS21_1 : acs := Eval vm_compute in hget bM2_1 1 bSD1.
Definition bS22_1 : acs := Eval vm_compute in hget bM2_1 2 bSD1.
Definition bHS2_1 : nat -> option acs := hs2 1 bS21_1 2 bS22_1.

Definition bsh2_0 : shape := Eval vm_compute in sh_of (brun bIT2 0 (nxt bSD0) bSD0 bplan2 bHS2_0).
Definition bsh2_1 : shape := Eval vm_compute in sh_of (brun bIT2 1 (nxt bSD1) bSD1 bplan2 bHS2_1).
