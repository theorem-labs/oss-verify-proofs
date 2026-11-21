(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded plan is renumbered where it is checked (a map read off a probe of the run at 727298f3) and its splits on AT_RANDOM's position move with the auxv's size, the hand-off state and the result shape are computed in the build, one certificate per CONFIG_RSEQ value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen AsanStartupCert AsanStartupCertC.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITD : itab := mk_itab_ranges ASEGS startup_plan_ranges_C.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the recorded plan, renumbered, with its splits on [e_atr8] moved by [atr8_shift r] *)
Definition startup_plan_segC_k (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh startup_plan_segC).

(* the certificate's own check, with hand-off table [js] *)
Definition runD (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS ITD ASAN (nxt (HS_C r)) AsanInit.LIMIT r (XNS ASEGS ASAN (nxt (HS_C r)) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None (HS_C r) (startup_plan_segC_k r).

Definition HSLD_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 16 (runD 0) [].
Definition HSLD_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 16 (runD 1) [].
Definition HS_D_0 : acs := Eval vm_compute in hstate HSLD_0 (hform (HS_C 0)) 0.
Definition HS_D_1 : acs := Eval vm_compute in hstate HSLD_1 (hform (HS_C 1)) 0.
Definition HS_D (r : Z) : acs := if Z.eqb r 1 then HS_D_1 else HS_D_0.
(* the hand-off table: only hand-off 0, at the computed state *)
Definition HS_asanD (r : Z) (h : nat) : option acs := if Nat.eqb h 0 then Some (HS_D r) else None.
Lemma HS_asanD_one : forall r h ch, HS_asanD r h = Some ch -> h = 0%nat /\ ch = HS_D r.
Proof. intros r h ch E. revert E. unfold HS_asanD. destruct (Nat.eqb_spec h 0) as [->|Hne]; intros E; [injection E as <-; split; reflexivity | discriminate E]. Qed.
Lemma NX_D_ge : forall r, (NX0 <= nxt (HS_D r))%nat.
Proof. intros r. unfold HS_D. destruct (Z.eqb r 1); vm_compute; lia. Qed.

Definition startup_shapeD_0 : shape := Eval vm_compute in match runD 0 (HS_asanD 0) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeD_1 : shape := Eval vm_compute in match runD 1 (HS_asanD 1) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeD (r : Z) : shape := if Z.eqb r 1 then startup_shapeD_1 else startup_shapeD_0.
Lemma startup_certD_0 : runD 0 (HS_asanD 0) = COk startup_shapeD_0.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeD_0)). Qed.
Lemma startup_certD_1 : runD 1 (HS_asanD 1) = COk startup_shapeD_1.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeD_1)). Qed.
Lemma startup_certD : forall r, 0 <= r <= 1 -> runD r (HS_asanD r) = COk (startup_shapeD r).
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certD_0 | exact startup_certD_1]. Qed.
