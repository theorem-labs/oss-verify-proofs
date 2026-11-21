(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the segment is checked at both CONFIG_RSEQ values from the hand-off state the previous segment computes, the plan's fresh variables renumbered by a map read from a probe run, and its own hand-off state computed in the build; the hand-off states collected in one run of the check; the segment's shape written as the literal its check computes, read from a probe run). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan PlanRegen AsanStartupCert.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma ITB_ok : itab_sound ASEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* read in a probe run (probe MP1, "MP1 MAPPT asan segA r0") *)
Definition vshB : list (nat * nat) := [(13, 17); (207, 211); (310, 316)]%nat.
Definition startup_plan_segA_k : plan := psh (mapf vshB) startup_plan_segA.
(* this segment's fresh-variable floor: the counter of the state the previous segment hands off, computed
   (the recorded plan's was the old run's) *)
Definition NXB (r : Z) : nat := nxt (HA r).
Lemma NXB_ge : forall r, (NX0 <= NXB r)%nat.
(* the default state of [hstate] (the previous segment's start state, open in [r]) is generalized
   before the [vm_compute]: the table has the key, so the default is never read, and an open start
   state is not normalised *)
Proof. ltac1:(intros r; apply Nat.leb_le; unfold NXB, HA, HSL_A; destruct (Z.eqb r 1); generalize (asan_init r); intros d; vm_compute; reflexivity). Qed.
(* the check run itself, as an abbreviation and not a definition: the certificates below are then stated in
   the form the start-up's segment lemma ([AsanBoot.seg_sound]) takes as its premise, which the kernel meets
   argument by argument; through a definition, it unfolded [check] and reduced the whole plan check lazily *)
#[local] Notation runB r js :=
  (check ASEGS ITB ASAN (NXB r) AsanInit.LIMIT r (XNS ASEGS ASAN (NXB r) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (HA r) startup_plan_segA_k).
(* the same check run once by [check_coll] (AsanPlan.v), giving each hand-off it reaches to
   PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map); the hand-off
   state collected in that one run ([collect_handoffs1]) *)
Definition collB (r : Z) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll ASEGS ITB ASAN (NXB r) AsanInit.LIMIT r (XNS ASEGS ASAN (NXB r) AsanInit.LIMIT) XE0 XB0 KC0 BFUEL _ hvisit FUEL None
        (HA r) startup_plan_segA_k bm.
Definition HSL_B0 : list (nat * acs) := Eval vm_compute in collect_handoffs1 4 (collB 0) [].
Definition HSL_B1 : list (nat * acs) := Eval vm_compute in collect_handoffs1 4 (collB 1) [].
Definition HSL_B (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_B1 else HSL_B0.
Definition HS_asanB (r : Z) (h : nat) : option acs := hlookup (HSL_B r) h.
Lemma HSL_B_keys : forall r, map fst (HSL_B r) = [11%nat].
Proof. ltac1:(intros r; unfold HSL_B; destruct (Z.eqb r 1); vm_compute; reflexivity). Qed.
Definition HB (r : Z) : acs := hstate (HSL_B r) (HA r) 11.
Lemma HS_asanB_one : forall r h ch, HS_asanB r h = Some ch -> h = 11%nat /\ ch = HB r.
Proof. ltac1:(intros r h ch H; exact (hlookup_one (HSL_B r) (HA r) 11 (HSL_B_keys r) h ch H)). Qed.
(* the result the check gives, computed (the renumbered plan's case splits name the new numbers) *)
Definition shapeB0 : shape := SHole 11.
Definition shapeB1 : shape := SHole 11.
Definition shapeB (r : Z) : shape := if Z.eqb r 1 then shapeB1 else shapeB0.
Lemma certB_0 : runB 0 (HS_asanB 0) = COk shapeB0.
Proof. Time (vm_cert_refl constr:(COk shapeB0)). Time Qed.
Lemma certB_1 : runB 1 (HS_asanB 1) = COk shapeB1.
Proof. Time (vm_cert_refl constr:(COk shapeB1)). Time Qed.
Lemma certB : forall r, 0 <= r <= 1 -> runB r (HS_asanB r) = COk (shapeB r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact certB_0 | exact certB_1]). Qed.
