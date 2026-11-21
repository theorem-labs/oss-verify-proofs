(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the segment is checked at both CONFIG_RSEQ values from the hand-off state the previous segment computes, the plan's fresh variables renumbered by a map read from a probe run, and its own hand-off state computed in the build; the hand-off states collected in one run of the check; the segment's shape written as the literal its check computes, read from a probe run). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen AsanStartupCert AsanStartupCertB AsanStartupCertC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITD : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* read in a probe run (probe MP1, "MP1 MAPPT asan segC r0") *)
Definition vshD : list (nat * nat) := [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400)]%nat.
Definition startup_plan_segC_k : plan := psh (mapf vshD) startup_plan_segC.
(* this segment's fresh-variable floor: the counter of the state the previous segment hands off, computed
   (the recorded plan's was the old run's) *)
Definition NXD (r : Z) : nat := nxt (HC r).
Lemma NXD_ge : forall r, (NX0 <= NXD r)%nat.
(* the default state of [hstate] (the previous segment's start state, open in [r]) is generalized
   before the [vm_compute]: the table has the key, so the default is never read, and an open start
   state is not normalised *)
Proof. ltac1:(intros r; apply Nat.leb_le; unfold NXD, HC, HSL_C; destruct (Z.eqb r 1); generalize (HB r); intros d; vm_compute; reflexivity). Qed.
(* the check run itself, as an abbreviation and not a definition: the certificates below are then stated in
   the form the start-up's segment lemma ([AsanBoot.seg_sound]) takes as its premise, which the kernel meets
   argument by argument; through a definition, it unfolded [check] and reduced the whole plan check lazily *)
#[local] Notation runD r js :=
  (check ASEGS ITD ASAN (NXD r) AsanInit.LIMIT r (XNS ASEGS ASAN (NXD r) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (HC r) startup_plan_segC_k).
(* the same check run once by [check_coll] (AsanPlan.v), giving each hand-off it reaches to
   PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map); the hand-off
   state collected in that one run ([collect_handoffs1]) *)
Definition collD (r : Z) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll ASEGS ITD ASAN (NXD r) AsanInit.LIMIT r (XNS ASEGS ASAN (NXD r) AsanInit.LIMIT) XE0 XB0 KC0 BFUEL _ hvisit FUEL None
        (HC r) startup_plan_segC_k bm.
Definition HSL_D0 : list (nat * acs) := Eval vm_compute in collect_handoffs1 6 (collD 0) [].
Definition HSL_D1 : list (nat * acs) := Eval vm_compute in collect_handoffs1 6 (collD 1) [].
Definition HSL_D (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_D1 else HSL_D0.
Definition HS_asanD (r : Z) (h : nat) : option acs := hlookup (HSL_D r) h.
Lemma HSL_D_keys : forall r, map fst (HSL_D r) = [0%nat].
Proof. ltac1:(intros r; unfold HSL_D; destruct (Z.eqb r 1); vm_compute; reflexivity). Qed.
Definition HD (r : Z) : acs := hstate (HSL_D r) (HC r) 0.
Lemma HS_asanD_one : forall r h ch, HS_asanD r h = Some ch -> h = 0%nat /\ ch = HD r.
Proof. ltac1:(intros r h ch H; exact (hlookup_one (HSL_D r) (HC r) 0 (HSL_D_keys r) h ch H)). Qed.
(* the result the check gives, computed (the renumbered plan's case splits name the new numbers) *)
Definition shapeD0 : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
Definition shapeD1 : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
Definition shapeD (r : Z) : shape := if Z.eqb r 1 then shapeD1 else shapeD0.
Lemma certD_0 : runD 0 (HS_asanD 0) = COk shapeD0.
Proof. Time (vm_cert_refl constr:(COk shapeD0)). Time Qed.
Lemma certD_1 : runD 1 (HS_asanD 1) = COk shapeD1.
Proof. Time (vm_cert_refl constr:(COk shapeD1)). Time Qed.
Lemma certD : forall r, 0 <= r <= 1 -> runD r (HS_asanD r) = COk (shapeD r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact certD_0 | exact certD_1]). Qed.
