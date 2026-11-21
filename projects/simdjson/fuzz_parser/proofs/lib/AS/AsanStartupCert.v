(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded plan is renumbered where it is checked (a map read off a probe of the run at 727298f3) and its splits on AT_RANDOM's position move with the auxv's size, the hand-off state and the result shape are computed in the build, one certificate per CONFIG_RSEQ value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

(* The variable renumbering of the recorded start-up plans at LPS 727298f3, read off the probe
   runs of this image recorded in the unit's probe notes (the launch adds V_G and V_GID and the
   run reads the whole auxv, so the run allocates its fresh variables at other numbers):
   [vsteps] moves a variable up by the sum of the steps at or below it. *)
Definition VSH : list (nat * nat) := [(78%nat, 4%nat); (310%nat, 2%nat)].
Definition vsh : nat -> nat := vsteps VSH.

Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges_0.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the recorded plan, renumbered, with its splits on [e_atr8] moved by [atr8_shift r] *)
Definition startup_plan_k (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh startup_plan).

(* the certificate's own check, with hand-off table [js] *)
Definition run0 (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT r (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None (asan_init r) (startup_plan_k r).

Definition HSL_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 8 (run0 0) [].
Definition HSL_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 8 (run0 1) [].
Definition HS_A_0 : acs := Eval vm_compute in hstate HSL_0 (hform (asan_init 0)) 10.
Definition HS_A_1 : acs := Eval vm_compute in hstate HSL_1 (hform (asan_init 1)) 10.
Definition HS_A (r : Z) : acs := if Z.eqb r 1 then HS_A_1 else HS_A_0.
(* the hand-off table: only hand-off 10, at the computed state *)
Definition HS_asanA (r : Z) (h : nat) : option acs := if Nat.eqb h 10 then Some (HS_A r) else None.
Lemma HS_asanA_one : forall r h ch, HS_asanA r h = Some ch -> h = 10%nat /\ ch = HS_A r.
Proof. intros r h ch E. revert E. unfold HS_asanA. destruct (Nat.eqb_spec h 10) as [->|Hne]; intros E; [injection E as <-; split; reflexivity | discriminate E]. Qed.
Lemma NX_A_ge : forall r, (NX0 <= nxt (HS_A r))%nat.
Proof. intros r. unfold HS_A. destruct (Z.eqb r 1); vm_compute; lia. Qed.

Definition startup_shape_0 : shape := Eval vm_compute in match run0 0 (HS_asanA 0) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shape_1 : shape := Eval vm_compute in match run0 1 (HS_asanA 1) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shape (r : Z) : shape := if Z.eqb r 1 then startup_shape_1 else startup_shape_0.
Lemma startup_cert_0 : run0 0 (HS_asanA 0) = COk startup_shape_0.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shape_0)). Qed.
Lemma startup_cert_1 : run0 1 (HS_asanA 1) = COk startup_shape_1.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shape_1)). Qed.
Lemma startup_cert : forall r, 0 <= r <= 1 -> run0 r (HS_asanA r) = COk (startup_shape r).
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_cert_0 | exact startup_cert_1]. Qed.
