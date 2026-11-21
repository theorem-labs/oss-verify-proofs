(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is checked at both CONFIG_RSEQ values from the start state with the auxv facts, the plan's fresh variables renumbered by a map read from a probe run, and the hand-off state computed in the build; the hand-off states collected in one run of the check). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* LPS 727298f3: the start state has the launch variable [V_GID] (NX0 12 -> 13) and the facts for the whole
   auxv, so the run gives its fresh variables other numbers than the recorded plan names.  The plan is renumbered
   where it is checked, by the map read in a probe run (probe MP1, line
   "MP1 MAPPT asan A r0" = [(13, 17)]: old 13 and above move by +4); the same map at both CONFIG_RSEQ values. *)
Definition vshA : list (nat * nat) := [(13, 17)%nat].
Definition startup_plan_k : plan := psh (mapf vshA) startup_plan.
(* the check run itself, as an abbreviation and not a definition: the certificates below are then stated in
   the form [AsanStartup.asan_startup] takes as its premise, which the kernel meets argument by argument;
   through a definition, it unfolded [check] and reduced the whole plan check lazily instead *)
#[local] Notation runA r js :=
  (check ASEGS IT0 ASAN NX0 AsanInit.LIMIT r (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (asan_init r) startup_plan_k).
(* the same check run once by [check_coll] (AsanPlan.v), giving each hand-off it reaches to
   PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition collA (r : Z) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll ASEGS IT0 ASAN NX0 AsanInit.LIMIT r (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 KC0 BFUEL _ hvisit FUEL None
        (asan_init r) startup_plan_k bm.
(* the state the run hands off at 10, computed per CONFIG_RSEQ value (method of jsoncons/fuzz_bigint's
   PlanRegenK.v), in one run of the check ([collect_handoffs1]); the certificates below check the run
   against it with [check] *)
Definition HSL_A0 : list (nat * acs) := Eval vm_compute in collect_handoffs1 4 (collA 0) [].
Definition HSL_A1 : list (nat * acs) := Eval vm_compute in collect_handoffs1 4 (collA 1) [].
Definition HSL_A (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_A1 else HSL_A0.
Definition HS_asanA (r : Z) (h : nat) : option acs := hlookup (HSL_A r) h.
Definition HA (r : Z) : acs := hstate (HSL_A r) (asan_init r) 10.
Lemma HSL_A_keys : forall r, map fst (HSL_A r) = [10%nat].
(* the file is in Ltac2 mode from its Ltac2 import; these proofs are Ltac1 scripts *)
Proof. ltac1:(intros r; unfold HSL_A; destruct (Z.eqb r 1); vm_compute; reflexivity). Qed.
Lemma HS_asanA_one : forall r h ch, HS_asanA r h = Some ch -> h = 10%nat /\ ch = HA r.
Proof. ltac1:(intros r h ch H; exact (hlookup_one (HSL_A r) (asan_init r) 10 (HSL_A_keys r) h ch H)). Qed.

Lemma startup_cert_0 : runA 0 (HS_asanA 0) = COk startup_shape.
Proof. Time (vm_cert_refl constr:(COk startup_shape)). Time Qed.
Lemma startup_cert_1 : runA 1 (HS_asanA 1) = COk startup_shape.
Proof. Time (vm_cert_refl constr:(COk startup_shape)). Time Qed.
Lemma startup_cert : forall r, 0 <= r <= 1 -> runA r (HS_asanA r) = COk startup_shape.
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_cert_0 | exact startup_cert_1]). Qed.
