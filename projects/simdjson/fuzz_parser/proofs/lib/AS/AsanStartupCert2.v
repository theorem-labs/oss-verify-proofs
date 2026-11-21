(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded plan is renumbered where it is checked (a map read off a probe of the run at 727298f3) and its splits on AT_RANDOM's position move with the auxv's size, the hand-off state and the result shape are computed in the build, one certificate per CONFIG_RSEQ value. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupPlan2Asan PlanRegen AsanStartupCert AsanStartupCertD.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the recorded plan, renumbered, with its splits on [e_atr8] moved by [atr8_shift r] *)
Definition startup2_plan_k (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh startup2_plan).

(* the certificate's own check, with hand-off table [js] *)
Definition run2 (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT2 ASAN (nxt (HS_D r)) AsanInit.LIMIT r (XNS ASEGS ASAN (nxt (HS_D r)) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None (HS_D r) (startup2_plan_k r).

Definition HSL2_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 16 (run2 0) [].
Definition HSL2_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 16 (run2 1) [].
Definition HS2_0 (h : nat) : option acs := match h with 1%nat | 2%nat => hlookup HSL2_0 h | _ => None end.
Definition HS2_1 (h : nat) : option acs := match h with 1%nat | 2%nat => hlookup HSL2_1 h | _ => None end.
(* the main phase's entry states, hand-offs 1 and 2, per rz *)
Definition HS_asan2 (r : Z) : nat -> option acs := if Z.eqb r 1 then HS2_1 else HS2_0.

Definition startup2_shape_0 : shape := Eval vm_compute in match run2 0 (HS_asan2 0) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup2_shape_1 : shape := Eval vm_compute in match run2 1 (HS_asan2 1) with COk s => s | CErr _ _ _ => SHole 999 end.
Definition startup2_shape (r : Z) : shape := if Z.eqb r 1 then startup2_shape_1 else startup2_shape_0.
Lemma startup2_cert_0 : run2 0 (HS_asan2 0) = COk startup2_shape_0.
Proof. vm_cast_no_check (@eq_refl cres (COk startup2_shape_0)). Qed.
Lemma startup2_cert_1 : run2 1 (HS_asan2 1) = COk startup2_shape_1.
Proof. vm_cast_no_check (@eq_refl cres (COk startup2_shape_1)). Qed.
Lemma startup2_cert : forall r, 0 <= r <= 1 -> run2 r (HS_asan2 r) = COk (startup2_shape r).
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup2_cert_0 | exact startup2_cert_1]. Qed.
