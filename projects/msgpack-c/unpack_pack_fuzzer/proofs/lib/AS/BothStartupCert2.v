(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the segment is checked at both CONFIG_RSEQ values from the hand-off state the previous segment computes, the plan's fresh variables renumbered by a map read from a probe run, and its own hand-off state computed in the build; the hand-off states collected in one run of the check; the segment's shape written as the literal its check computes, read from a probe run). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth PlanRegen StartupPlan2Both BothStartupCert BothStartupCertB BothStartupCertC BothStartupCertD.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma IT2_ok : itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* read in a probe run (probe MP1b, "MP1b MAPPT asan s2 r0") *)
Definition vsh2 : list (nat * nat) := [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400); (453, 459)]%nat.
Definition startup2_plan_both_k : plan := psh (mapf vsh2) startup2_plan_both.
(* this segment's fresh-variable floor: the counter of the state the previous segment hands off, computed
   (the recorded plan's was the old run's) *)
Definition NXS2 (r : Z) : nat := nxt (HD r).
Lemma NXS2_ge : forall r, (NX0 <= NXS2 r)%nat.
(* the default state of [hstate] (the previous segment's start state, open in [r]) is generalized
   before the [vm_compute]: the table has the key, so the default is never read, and an open start
   state is not normalised *)
Proof. ltac1:(intros r; apply Nat.leb_le; unfold NXS2, HD, HSL_D; destruct (Z.eqb r 1); generalize (HC r); intros d; vm_compute; reflexivity). Qed.
(* the check run itself, as an abbreviation and not a definition: the certificates below are then stated in
   the form the start-up's segment lemma ([BothBoot.seg_sound]) takes as its premise, which the kernel meets
   argument by argument; through a definition, it unfolded [check] and reduced the whole plan check lazily *)
#[local] Notation run2 r js :=
  (check BSEGS IT2 BOTH (NXS2 r) AsanInit.LIMIT r (XNS BSEGS BOTH (NXS2 r) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (HD r) startup2_plan_both_k).
(* the same check run once by [check_coll] (AsanPlan.v), giving each hand-off it reaches to
   PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map); the hand-off
   states collected in that one run ([collect_handoffs1]) *)
Definition coll2 (r : Z) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll BSEGS IT2 BOTH (NXS2 r) AsanInit.LIMIT r (XNS BSEGS BOTH (NXS2 r) AsanInit.LIMIT) XE0 XB0 KC0 BFUEL _ hvisit FUEL None
        (HD r) startup2_plan_both_k bm.
Definition HSL_20 : list (nat * acs) := Eval vm_compute in collect_handoffs1 8 (coll2 0) [].
Definition HSL_21 : list (nat * acs) := Eval vm_compute in collect_handoffs1 8 (coll2 1) [].
Definition HSL_2 (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_21 else HSL_20.
Definition HS_both2 (r : Z) (h : nat) : option acs := hlookup (HSL_2 r) h.
Lemma HSL_2_keys : forall r, map fst (HSL_2 r) = [2%nat; 1%nat].
Proof. ltac1:(intros r; unfold HSL_2; destruct (Z.eqb r 1); vm_compute; reflexivity). Qed.
(* the result the check gives, computed (the renumbered plan's case splits name the new numbers) *)
Definition shape20 : shape := SCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 350))) (ELit 3935)) 4030 (SHole 1) (SHole 2).
Definition shape21 : shape := SCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 350))) (ELit 3935)) 4030 (SHole 1) (SHole 2).
Definition shape2 (r : Z) : shape := if Z.eqb r 1 then shape21 else shape20.
Lemma cert2_0 : run2 0 (HS_both2 0) = COk shape20.
Proof. Time (vm_cert_refl constr:(COk shape20)). Time Qed.
Lemma cert2_1 : run2 1 (HS_both2 1) = COk shape21.
Proof. Time (vm_cert_refl constr:(COk shape21)). Time Qed.
Lemma cert2 : forall r, 0 <= r <= 1 -> run2 r (HS_both2 r) = COk (shape2 r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert2_0 | exact cert2_1]). Qed.
Definition HM1 (r : Z) : acs := hstate (HSL_2 r) (HD r) 1.
Definition HM2 (r : Z) : acs := hstate (HSL_2 r) (HD r) 2.
Lemma HS_both2_two : forall r h ch, HS_both2 r h = Some ch -> (h = 1%nat /\ ch = HM1 r) \/ (h = 2%nat /\ ch = HM2 r).
Proof. ltac1:(intros r h ch H; exact (hlookup_two_any (HSL_2 r) (HD r) 1 2 (or_intror (HSL_2_keys r)) eq_refl h ch H)). Qed.
