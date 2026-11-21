(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded plan is renumbered where it is checked (a map read off a probe of the run at 727298f3) and its splits on AT_RANDOM's position move with the auxv's size, the hand-off state and the result shape are computed in the build, one certificate per CONFIG_RSEQ value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen AsanStartupCert AsanStartupCertB.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITC : itab := mk_itab_ranges ASEGS startup_plan_ranges_B.
Lemma ITC_ok : itab_sound ASEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the recorded plan, renumbered, with its splits on [e_atr8] moved by [atr8_shift r] *)
Definition startup_plan_segB_k (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh startup_plan_segB).

(* the certificate's own check, with hand-off table [js] *)
Definition runC (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS ITC ASAN (nxt (HS_B r)) AsanInit.LIMIT r (XNS ASEGS ASAN (nxt (HS_B r)) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None (HS_B r) (startup_plan_segB_k r).

Definition HSLC_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (runC 0) [].
Definition HSLC_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (runC 1) [].
Definition HS_C_0 : acs := Eval vm_compute in hstate HSLC_0 (hform (HS_B 0)) 12.
Definition HS_C_1 : acs := Eval vm_compute in hstate HSLC_1 (hform (HS_B 1)) 12.
Definition HS_C (r : Z) : acs := if Z.eqb r 1 then HS_C_1 else HS_C_0.
(* the hand-off table: only hand-off 12, at the computed state *)
Definition HS_asanC (r : Z) (h : nat) : option acs := if Nat.eqb h 12 then Some (HS_C r) else None.
Lemma HS_asanC_one : forall r h ch, HS_asanC r h = Some ch -> h = 12%nat /\ ch = HS_C r.
Proof. intros r h ch E. revert E. unfold HS_asanC. destruct (Nat.eqb_spec h 12) as [->|Hne]; intros E; [injection E as <-; split; reflexivity | discriminate E]. Qed.
Lemma NX_C_ge : forall r, (NX0 <= nxt (HS_C r))%nat.
Proof. intros r. unfold HS_C. destruct (Z.eqb r 1); vm_compute; lia. Qed.

Definition startup_shapeC_0 : shape := Eval vm_compute in match runC 0 (HS_asanC 0) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeC_1 : shape := Eval vm_compute in match runC 1 (HS_asanC 1) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeC (r : Z) : shape := if Z.eqb r 1 then startup_shapeC_1 else startup_shapeC_0.
Lemma startup_certC_0 : runC 0 (HS_asanC 0) = COk startup_shapeC_0.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeC_0)). Qed.
Lemma startup_certC_1 : runC 1 (HS_asanC 1) = COk startup_shapeC_1.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeC_1)). Qed.
Lemma startup_certC : forall r, 0 <= r <= 1 -> runC r (HS_asanC r) = COk (startup_shapeC r).
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certC_0 | exact startup_certC_1]. Qed.
