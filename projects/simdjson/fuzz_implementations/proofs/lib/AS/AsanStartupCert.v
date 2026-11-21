(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the recorded start-up plan is renumbered by a map read from a probe run, and its join and hand-off states are computed in the build by the check itself, once per CONFIG_RSEQ value, instead of the recorded ones; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/AS/AsanStartupCert.v, lines 6-12, 26-30, 44-89. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanTablesA AsanPlanImages AsanInit AsanStartup StartupPlanAsan PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
(* Ltac2 is imported for [cert_refl] only: the proofs below are Ltac1 and call it by [ltac2:(..)]. *)
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* THE RECORDED PLAN, RENUMBERED AND RECHECKED AT 727298f3.
   [startup_plan] was written against the released model's launch, whose fresh variables
   started at [NX0] = 10; the revision's launch adds [V_G] (10) and [V_GID] (11), and its
   longer auxv walk adds fresh variables before the plan's first renaming.  [F_A] is the
   plan's variable map per compaction depth ([PlanRegen.mapd]), each step read from a probe
   run of this check at the revision on this unit's binaries, in both images and at both
   CONFIG_RSEQ values, which printed the same numbers in all four runs:
   depth 0 (up to the first [PRename]): 2 higher from 10, 4 higher from 43, 6 higher from
   357.  Run with 2 higher from 10 everywhere, the plan refuses at the [PShDisj] whose page
   it calls 77, and the 65536-byte mapping the state holds there is at 81, so 77 is 4 higher;
   run with 4 higher from 77, it refuses at the [PShDisj] whose page it calls 357, whose
   4096-byte mapping is at 363, so 357 is 6 higher.  The state just before the depth-0
   [PRename], counter 397, then holds exactly sixteen variables, and they are the rename's
   sixteen sources under these three steps -- 43 + 4, 44 + 4, 77 + 4, .., 292 + 4, 357 + 6,
   .., 390 + 6 -- with no source of the rename missing from the state and no variable of the
   state left out of the rename, each in the role (a mapping, a register, or facts alone) its
   source has in the plan, so matching the sixteen sources in order against the state's
   sixteen variables gives these same three steps;
   depth 1: 2 higher from 10 and from 26 (just after the depth-0 [PRename] the counter is 28
   and the state's variables are 12 .. 27, and the first fresh variable after it, the
   [PFresh] page the depth-1 [PCase2] tests, is 28 = 26 + 2);
   depth 2: 2 higher from 10 and from 42 (the counter just after the depth-1 [PRename] is
   44 = 42 + 2, and that rename's sources under the depth-1 step are all in the state).
   The plan holds three [PRename] nodes, one at depth 0 and two at depth 1, so nothing is
   checked deeper than depth 2 and no deeper step is listed.  The join states of the plan's
   [PVia] nodes and the hand-off states are computed below by [PlanRegen.regen] from the run
   itself, once per CONFIG_RSEQ value.  Nothing here is a recorded state: the certificate
   checks each again. *)
Definition F_A : list (list (nat * nat)) := [[(10, 2); (43, 4); (357, 6)]; [(10, 2); (26, 2)]; [(10, 2); (42, 2)]]%nat.

Definition chk_A (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT r XN0 XE0 XB0 HS KC0 BFUEL FUEL lc cs p.
Definition run_A (r : Z) (VJ HL : list (nat * acs)) : cres :=
  chk_A r (hlookup HL) None (asan_a_init r) (pshd F_A (hlookup VJ) 0 startup_plan).
Definition arms_A (r : Z) (HL : list (nat * acs)) (j : nat) (js : acs) (lo : nat) (cs : acs) (ka : plan) : cres :=
  chk_A r (hlookup HL) (Some (JC j js SNil (nxt cs) lo)) cs ka.

Definition REGEN_A_0 : list (nat * acs) * list (nat * acs) * cres := Eval vm_compute in regen 30 (run_A 0) (arms_A 0) [] [].
Definition REGEN_A_1 : list (nat * acs) * list (nat * acs) * cres := Eval vm_compute in regen 30 (run_A 1) (arms_A 1) [] [].

Definition VJ_A (r : Z) : list (nat * acs) := if Z.eqb r 1 then fst (fst REGEN_A_1) else fst (fst REGEN_A_0).
Definition HL_A (r : Z) : list (nat * acs) := if Z.eqb r 1 then snd (fst REGEN_A_1) else snd (fst REGEN_A_0).
Definition HS_asan (r : Z) : nat -> option acs := hlookup (HL_A r).
Definition startup_plan_r (r : Z) : plan := pshd F_A (hlookup (VJ_A r)) 0 startup_plan.

(* the result shape of each check: [regen]'s last answer is the check of the plan with the
   states it computed ([COk] when they are complete) *)
Definition startup_shape_0 : shape := match snd REGEN_A_0 with COk s => s | CErr _ _ _ => SNil end.
Definition startup_shape_1 : shape := match snd REGEN_A_1 with COk s => s | CErr _ _ _ => SNil end.
Definition startup_shape (r : Z) : shape := if Z.eqb r 1 then startup_shape_1 else startup_shape_0.

(* TWO CLOSED CERTIFICATES, ONE PER [b : bool], joined by the [forall b] wrapper: [cert_refl]
   casts an [eq_refl] through [vm_compute] (the kernel checks it at [Qed]), so each value of the
   flag is checked closed.  Neither value is pinned. *)
Lemma startup_cert_r0 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT 0 XN0 XE0 XB0 (HS_asan 0) KC0 BFUEL FUEL None (asan_a_init 0) (startup_plan_r 0) = COk (startup_shape 0).
Proof. ltac2:(cert_refl constr:(COk (startup_shape 0))). Qed.

Lemma startup_cert_r1 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT 1 XN0 XE0 XB0 (HS_asan 1) KC0 BFUEL FUEL None (asan_a_init 1) (startup_plan_r 1) = COk (startup_shape 1).
Proof. ltac2:(cert_refl constr:(COk (startup_shape 1))). Qed.

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
        (asan_a_init (rseq_z b)) (startup_plan_r (rseq_z b)) = COk (startup_shape (rseq_z b)).
Proof. intros [|]; [exact startup_cert_r1 | exact startup_cert_r0]. Qed.

(* A fact of every computed hand-off state, from a boolean test of the list it is read from. *)
Lemma HS_asan_forall : forall (P : acs -> bool) (b : bool),
  forallb (fun q => P (snd q)) (HL_A (rseq_z b)) = true ->
  forall h ch, HS_asan (rseq_z b) h = Some ch -> P ch = true.
Proof.
  intros P b Hall h ch. unfold HS_asan, hlookup.
  destruct (find (fun q => Nat.eqb (fst q) h) (HL_A (rseq_z b))) as [q|] eqn:Hf; [|discriminate].
  intros Hq. injection Hq as <-. apply find_some in Hf as [Hin _].
  exact (proj1 (forallb_forall _ _) Hall q Hin).
Qed.
