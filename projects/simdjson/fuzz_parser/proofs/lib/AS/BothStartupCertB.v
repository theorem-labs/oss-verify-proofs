(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded plan is renumbered where it is checked (a map read off a probe of the run at 727298f3) and its splits on AT_RANDOM's position move with the auxv's size, the hand-off state and the result shape are computed in the build, one certificate per CONFIG_RSEQ value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth PlanRegen BothStartupCert.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_A.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the recorded plan, renumbered, with its splits on [e_atr8] moved by [atr8_shift r] *)
Definition startup_plan_both_segA_k (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh startup_plan_both_segA).

(* the certificate's own check, with hand-off table [js] *)
Definition runB (r : Z) (js : nat -> option acs) : cres :=
  check BSEGS ITB BOTH (nxt (HS_A r)) AsanInit.LIMIT r (XNS BSEGS BOTH (nxt (HS_A r)) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None (HS_A r) (startup_plan_both_segA_k r).

Definition HSLB_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 8 (runB 0) [].
Definition HSLB_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 8 (runB 1) [].
Definition HS_B_0 : acs := Eval vm_compute in hstate HSLB_0 (hform (HS_A 0)) 11.
Definition HS_B_1 : acs := Eval vm_compute in hstate HSLB_1 (hform (HS_A 1)) 11.
Definition HS_B (r : Z) : acs := if Z.eqb r 1 then HS_B_1 else HS_B_0.
(* the hand-off table: only hand-off 11, at the computed state *)
Definition HS_bothB (r : Z) (h : nat) : option acs := if Nat.eqb h 11 then Some (HS_B r) else None.
Lemma HS_bothB_one : forall r h ch, HS_bothB r h = Some ch -> h = 11%nat /\ ch = HS_B r.
Proof. intros r h ch E. revert E. unfold HS_bothB. destruct (Nat.eqb_spec h 11) as [->|Hne]; intros E; [injection E as <-; split; reflexivity | discriminate E]. Qed.
Lemma NX_B_ge : forall r, (NX0 <= nxt (HS_B r))%nat.
Proof. intros r. unfold HS_B. destruct (Z.eqb r 1); vm_compute; lia. Qed.

Definition startup_shapeB_0 : shape := Eval vm_compute in match runB 0 (HS_bothB 0) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeB_1 : shape := Eval vm_compute in match runB 1 (HS_bothB 1) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup_shapeB (r : Z) : shape := if Z.eqb r 1 then startup_shapeB_1 else startup_shapeB_0.
Lemma startup_certB_0 : runB 0 (HS_bothB 0) = COk startup_shapeB_0.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeB_0)). Qed.
Lemma startup_certB_1 : runB 1 (HS_bothB 1) = COk startup_shapeB_1.
Proof. vm_cast_no_check (@eq_refl cres (COk startup_shapeB_1)). Qed.
Lemma startup_certB : forall r, 0 <= r <= 1 -> runB r (HS_bothB r) = COk (startup_shapeB r).
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certB_0 | exact startup_certB_1]. Qed.
