(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: hand-off states of the start-up chain computed in the build at LPS 727298f3, for each CONFIG_RSEQ value, under a variable map read from probe runs; the certificates' statement form. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup PlanRegen
  StartupPlanAsan StartupPlan2Asan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the ASan image's start-up chain, one chain per CONFIG_RSEQ value [r] (design 1 of
   OSSV-509's rule for start-up plans; the method of OSSV-343's certificate-data note).

   The recorded plans ([StartupPlanAsan], [StartupPlan2Asan]) are checked renumbered by
   [asu_f], a total monotone map read from the probe runs (the probe note
   notes/probe-pupnp__FuzzHttp.md names the run and the output line of each breakpoint).  Its first
   breakpoint is the lowest fresh variable the plans name, old 78: below it the plans name only
   launch variables, among them [V_G] of the NEW numbering through [e_atr8], which must not move.

   Every hand-off state is computed here from the check that reaches it ([PlanRegen.collect_k],
   with [join_states] where two paths reach one hand-off), from the state the previous segment
   hands off at the same [r]; nothing is recorded.  The certificates ([AsanStartupCert*]) re-run
   each check against these states. *)

Definition ASU_TBL : list (nat * nat) := [(78, 4); (207, 4); (310, 6); (344, 6); (394, 6); (453, 6)]%nat.
Definition asu_f : nat -> nat := tshift ASU_TBL.

Definition aplanA : plan := psh asu_f startup_plan.
Definition aplanB : plan := psh asu_f startup_plan_segA.
Definition aplanC : plan := psh asu_f startup_plan_segB.
Definition aplanD : plan := psh asu_f startup_plan_segC.
Definition aplan2 : plan := psh asu_f startup2_plan.

Definition aIT : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma aIT_ok : itab_sound ASEGS aIT.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition aIT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma aIT2_ok : itab_sound ASEGS aIT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* one segment's check at CONFIG_RSEQ value [r], with the recorded certificates' fuel *)
Definition arun (IT : itab) (r : Z) (nx : nat) (st : acs) (p : plan) (hs : nat -> option acs) : cres :=
  check ASEGS IT ASAN nx AsanInit.LIMIT r (XNS ASEGS ASAN nx AsanInit.LIMIT) XE0 XB0 hs 0%nat 400000%nat 3000%nat None st p.

(* the certificates' statement form: the same check, written out by a notation, so that a
   certificate meets the start-up chain's [check] goals syntactically (converting the constant
   [arun] against [check] does not finish in hours, even over variables) *)
Notation ACHK IT r nx st p hs :=
  (check ASEGS IT ASAN nx AsanInit.LIMIT r (XNS ASEGS ASAN nx AsanInit.LIMIT) XE0 XB0 hs 0%nat 400000%nat 3000%nat None st p)
  (only parsing).

(* CONFIG_RSEQ value 0 *)
Definition aSA0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 0 NX0 (asan_init 0) aplanA) []) 10 (asan_init 0).
Definition aHSA0 : nat -> option acs := hs1 10 aSA0.
Definition aSB0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 0 (nxt aSA0) aSA0 aplanB) []) 11 aSA0.
Definition aHSB0 : nat -> option acs := hs1 11 aSB0.
Definition aSC0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 0 (nxt aSB0) aSB0 aplanC) []) 12 aSB0.
Definition aHSC0 : nat -> option acs := hs1 12 aSC0.
Definition aSD0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 0 (nxt aSC0) aSC0 aplanD) []) 0 aSC0.
Definition aHSD0 : nat -> option acs := hs1 0 aSD0.

(* CONFIG_RSEQ value 1 *)
Definition aSA1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 1 NX0 (asan_init 1) aplanA) []) 10 (asan_init 1).
Definition aHSA1 : nat -> option acs := hs1 10 aSA1.
Definition aSB1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 1 (nxt aSA1) aSA1 aplanB) []) 11 aSA1.
Definition aHSB1 : nat -> option acs := hs1 11 aSB1.
Definition aSC1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 1 (nxt aSB1) aSB1 aplanC) []) 12 aSB1.
Definition aHSC1 : nat -> option acs := hs1 12 aSC1.
Definition aSD1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (arun aIT 1 (nxt aSC1) aSC1 aplanD) []) 0 aSC1.
Definition aHSD1 : nat -> option acs := hs1 0 aSD1.

(* the shapes the segments' checks return against those maps *)
Definition ashA0 : shape := Eval vm_compute in sh_of (arun aIT 0 NX0 (asan_init 0) aplanA aHSA0).
Definition ashB0 : shape := Eval vm_compute in sh_of (arun aIT 0 (nxt aSA0) aSA0 aplanB aHSB0).
Definition ashC0 : shape := Eval vm_compute in sh_of (arun aIT 0 (nxt aSB0) aSB0 aplanC aHSC0).
Definition ashD0 : shape := Eval vm_compute in sh_of (arun aIT 0 (nxt aSC0) aSC0 aplanD aHSD0).
Definition ashA1 : shape := Eval vm_compute in sh_of (arun aIT 1 NX0 (asan_init 1) aplanA aHSA1).
Definition ashB1 : shape := Eval vm_compute in sh_of (arun aIT 1 (nxt aSA1) aSA1 aplanB aHSB1).
Definition ashC1 : shape := Eval vm_compute in sh_of (arun aIT 1 (nxt aSB1) aSB1 aplanC aHSC1).
Definition ashD1 : shape := Eval vm_compute in sh_of (arun aIT 1 (nxt aSC1) aSC1 aplanD aHSD1).
