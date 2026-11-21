(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the start-up certificate is checked per CONFIG_RSEQ value at LPS 727298f3, from that value's start state, on the renumbered start-up plan and against the computed hand-off states. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesRP AsanPlanImages AsanItabFast AsanInit AsanMainDefs AsanMainLib AsanStartup StartupPlanAsan StartupPlanAsanR PlanRegen StartupHSAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges_fast ASEGS startup_plan_ranges.   (* [comment removed for export] *)
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply mk_itab_ranges_fast_sound. Qed.

(* the chain at CONFIG_RSEQ value [r] hands off at hole [r] *)
Definition startup_shape (r : Z) : shape := SHole (Z.to_nat r).

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_0 :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 AP.TT_none KC0 BFUEL FUEL None (asan_init_r 0) (startup_plan_r 0) = COk (startup_shape 0).
Proof. ltac2:(cert_refl constr:(COk (startup_shape 0))). Qed.
Lemma startup_cert_1 :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 AP.TT_none KC0 BFUEL FUEL None (asan_init_r 1) (startup_plan_r 1) = COk (startup_shape 1).
Proof. ltac2:(cert_refl constr:(COk (startup_shape 1))). Qed.

Lemma startup_cert : forall r, 0 <= r <= 1 ->
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 AP.TT_none KC0 BFUEL FUEL None (asan_init_r r) (startup_plan_r r) = COk (startup_shape r).
Proof.
  intros r Hr. assert (E : r = 0 \/ r = 1) by lia.
  destruct E as [-> | ->]; [exact startup_cert_0 | exact startup_cert_1].
Qed.

Lemma startup_holes : forall r, all_holes (startup_shape r) = true.
Proof. intros r. reflexivity. Qed.

Lemma HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.
Proof.
  intros h ch H. unfold HS_asan, hlookup in H.
  destruct (find (fun q => Nat.eqb (fst q) h) HS_asan_list) as [q|] eqn:Hf; [|discriminate].
  injection H as <-. apply find_some in Hf as [Hin _].
  assert (A : forallb (fun q => acs_noblob (snd q)) HS_asan_list = true) by (vm_compute; reflexivity).
  exact (proj1 (forallb_forall _ _) A q Hin).
Qed.
