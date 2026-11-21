(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: hand-off states of the start-up chain computed in the build at LPS 727298f3, for each CONFIG_RSEQ value, under a variable map read from probe runs; the certificates' statement form. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup PlanRegen
  StartupPlanBoth StartupPlan2Both.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the ASan+UBSan image's start-up chain, one chain per CONFIG_RSEQ value [r]
   (design 1 of OSSV-509's rule for start-up plans; the method of OSSV-343's certificate-data
   note).  The same construction as [StartupHSAsan]: the recorded plans are checked renumbered
   by [bsu_f], read from the probe runs of this image (notes/probe-pupnp__FuzzHttp.md), whose
   first breakpoint is the lowest fresh variable the plans name (old 78), and every hand-off
   state is computed here from the check that reaches it.  The certificates
   ([BothStartupCert*]) re-run each check against these states. *)

Definition BSU_TBL : list (nat * nat) := [(78, 4); (207, 4); (310, 6); (344, 6); (394, 6); (453, 6)]%nat.
Definition bsu_f : nat -> nat := tshift BSU_TBL.

Definition bplanA : plan := psh bsu_f startup_plan_both.
Definition bplanB : plan := psh bsu_f startup_plan_both_segA.
Definition bplanC : plan := psh bsu_f startup_plan_both_segB.
Definition bplanD : plan := psh bsu_f startup_plan_both_segC.
Definition bplan2 : plan := psh bsu_f startup2_plan_both.

Definition bIT : itab := mk_itab_ranges BSEGS startup_plan_both_ranges.
Lemma bIT_ok : itab_sound BSEGS bIT.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition bIT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma bIT2_ok : itab_sound BSEGS bIT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* one segment's check at CONFIG_RSEQ value [r], with the recorded certificates' fuel *)
Definition brun (IT : itab) (r : Z) (nx : nat) (st : acs) (p : plan) (hs : nat -> option acs) : cres :=
  check BSEGS IT BOTH nx AsanInit.LIMIT r (XNS BSEGS BOTH nx AsanInit.LIMIT) XE0 XB0 hs 0%nat 400000%nat 3000%nat None st p.

(* the certificates' statement form: the same check, written out by a notation, so that a
   certificate meets the start-up chain's [check] goals syntactically (converting the constant
   [brun] against [check] does not finish in hours, even over variables) *)
Notation BCHK IT r nx st p hs :=
  (check BSEGS IT BOTH nx AsanInit.LIMIT r (XNS BSEGS BOTH nx AsanInit.LIMIT) XE0 XB0 hs 0%nat 400000%nat 3000%nat None st p)
  (only parsing).

(* CONFIG_RSEQ value 0 *)
Definition bSA0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 0 NX0 (both_init 0) bplanA) []) 10 (both_init 0).
Definition bHSA0 : nat -> option acs := hs1 10 bSA0.
Definition bSB0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 0 (nxt bSA0) bSA0 bplanB) []) 11 bSA0.
Definition bHSB0 : nat -> option acs := hs1 11 bSB0.
Definition bSC0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 0 (nxt bSB0) bSB0 bplanC) []) 12 bSB0.
Definition bHSC0 : nat -> option acs := hs1 12 bSC0.
Definition bSD0 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 0 (nxt bSC0) bSC0 bplanD) []) 0 bSC0.
Definition bHSD0 : nat -> option acs := hs1 0 bSD0.

(* CONFIG_RSEQ value 1 *)
Definition bSA1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 1 NX0 (both_init 1) bplanA) []) 10 (both_init 1).
Definition bHSA1 : nat -> option acs := hs1 10 bSA1.
Definition bSB1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 1 (nxt bSA1) bSA1 bplanB) []) 11 bSA1.
Definition bHSB1 : nat -> option acs := hs1 11 bSB1.
Definition bSC1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 1 (nxt bSB1) bSB1 bplanC) []) 12 bSB1.
Definition bHSC1 : nat -> option acs := hs1 12 bSC1.
Definition bSD1 : acs := Eval vm_compute in
  hget (collect_k (fun h => h) 20 (brun bIT 1 (nxt bSC1) bSC1 bplanD) []) 0 bSC1.
Definition bHSD1 : nat -> option acs := hs1 0 bSD1.

(* the shapes the segments' checks return against those maps *)
Definition bshA0 : shape := Eval vm_compute in sh_of (brun bIT 0 NX0 (both_init 0) bplanA bHSA0).
Definition bshB0 : shape := Eval vm_compute in sh_of (brun bIT 0 (nxt bSA0) bSA0 bplanB bHSB0).
Definition bshC0 : shape := Eval vm_compute in sh_of (brun bIT 0 (nxt bSB0) bSB0 bplanC bHSC0).
Definition bshD0 : shape := Eval vm_compute in sh_of (brun bIT 0 (nxt bSC0) bSC0 bplanD bHSD0).
Definition bshA1 : shape := Eval vm_compute in sh_of (brun bIT 1 NX0 (both_init 1) bplanA bHSA1).
Definition bshB1 : shape := Eval vm_compute in sh_of (brun bIT 1 (nxt bSA1) bSA1 bplanB bHSB1).
Definition bshC1 : shape := Eval vm_compute in sh_of (brun bIT 1 (nxt bSB1) bSB1 bplanC bHSC1).
Definition bshD1 : shape := Eval vm_compute in sh_of (brun bIT 1 (nxt bSC1) bSC1 bplanD bHSD1).
