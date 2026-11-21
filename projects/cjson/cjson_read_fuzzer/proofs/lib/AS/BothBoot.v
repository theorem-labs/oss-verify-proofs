(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: startup_certB1, startup_certC, startup_certD and startup_certQ hold for both values of the rseq flag and are used at the run's own kb_rseq, and Section Boot takes the entry address apc, the launch's executable name and kernel build and the valid_launch and entry_launch_ok_va premises, which it passes on to both_node_x_sound_all and both_startup; each segment (B1, B, C, Q, D, 2) is checked at both rseq values from the hand-off state the segment before computes, its fresh variables renumbered by a table read off the run, its own hand-off states computed in the build and its shape written as the literal its check computes; segment Q's AT_RANDOM split chain is made again from the computed state by PlanRegen's chain rule; the start-up's final hand-off states (HS2) are the computed ones; Section Boot takes the launch's SIGPIPE disposition sgd after kb. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanCore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlan2Both.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PlanRegen.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module BothStartupCertB1.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB1 : itab := mk_itab_ranges BSEGS [(0x3e800, 24%nat); (0x49430, 36%nat); (0x4a320, 6628%nat); (0x53000, 92%nat); (0x54120, 8%nat); (0x54150, 8%nat); (0x54340, 28%nat); (0x54480, 16%nat); (0x55670, 12%nat); (0x5ad40, 32%nat); (0x5b2a0, 56%nat); (0x5b7c0, 20%nat); (0x5c230, 12%nat); (0x601d0, 16%nat); (0x60220, 8%nat); (0x61f10, 20%nat); (0x62620, 8%nat); (0x62670, 8%nat); (0x62930, 52%nat); (0x62b20, 16%nat); (0x63170, 12%nat); (0x66030, 16%nat); (0x66e60, 68%nat); (0x66f80, 8%nat); (0x674c0, 8%nat); (0x67710, 68%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x68bc0, 8%nat); (0x6d340, 24%nat); (0x6d550, 8%nat); (0x6e450, 8%nat); (0x8cd40, 32%nat); (0x8cde0, 28%nat); (0x8cf40, 12%nat)]%Z.
Lemma ITB1_ok : itab_sound BSEGS ITB1.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the renumbering table: old 207 is new 211, the start counter of the computed hand-off 10; launch variables 0..12 keep their numbers *)
Definition T_B1 : list (nat * nat) := [(13, 4); (207, 4)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXB1 (b : bool) : nat := nxt (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.HSA_10 b).
Lemma NXB1_ge : forall b, (NX0 <= NXB1 b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition startup_plan_segA_k : plan := PlanRegen.psh (PlanRegen.tshift T_B1) startup_plan_both_segA.
Definition run_B1 (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITB1 BOTH (NXB1 b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXB1 b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.HSA_10 b) (startup_plan_segA_k).
Definition HSL_B1_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_B1 false) [].
Definition HSL_B1_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_B1 true) [].
Definition HSB1_13 (b : bool) : acs := PlanRegen.hstate (if b then HSL_B1_1 else HSL_B1_0) (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.HSA_10 b) 13.
Definition HSB1 (b : bool) (h : nat) : option acs := if Nat.eqb h 13 then Some (HSB1_13 b) else None.
Lemma HSB1_one : forall b h ch, HSB1 b h = Some ch -> h = 13%nat /\ ch = HSB1_13 b.
Proof. intros b h ch Hh. unfold HSB1 in Hh. destruct (Nat.eqb_spec h 13) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_B1_0 : shape := SHole 13.
Definition shape_B1_1 : shape := SHole 13.
Definition shape_B1 (b : bool) : shape := if b then shape_B1_1 else shape_B1_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_B1 : forall b : bool,
  check BSEGS ITB1 BOTH (NXB1 b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXB1 b) AsanInit.LIMIT) XE0 XB0 (HSB1 b) KC0 BFUEL FUEL None (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.HSA_10 b) (startup_plan_segA_k) = COk (shape_B1 b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_B1_1)).
  (vm_cert_refl constr:(COk shape_B1_0)).
Qed.
End BothStartupCertB1.

Module BothStartupCertSB.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.ITB.
Definition ITB_ok : itab_sound BSEGS ITB := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.ITB_ok.
(* the renumbering table: old 208 is new 212, the start counter of the computed hand-off 13; the run makes two more fresh variables than the recorded one between old 245 and old 310, so old 310 is new 316 and old 311 is new 317 *)
Definition T_SB : list (nat * nat) := [(13, 4); (207, 4); (208, 4); (310, 6)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXB (b : bool) : nat := nxt (BothStartupCertB1.HSB1_13 b).
Lemma NXB_ge : forall b, (NX0 <= NXB b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition startup_plan_segB1_k : plan := PlanRegen.psh (PlanRegen.tshift T_SB) startup_plan_both_segB1.
Definition run_SB (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITB BOTH (NXB b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXB b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertB1.HSB1_13 b) (startup_plan_segB1_k).
Definition HSL_SB_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SB false) [].
Definition HSL_SB_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SB true) [].
Definition HSB_11 (b : bool) : acs := PlanRegen.hstate (if b then HSL_SB_1 else HSL_SB_0) (BothStartupCertB1.HSB1_13 b) 11.
Definition HSB (b : bool) (h : nat) : option acs := if Nat.eqb h 11 then Some (HSB_11 b) else None.
Lemma HSB_one : forall b h ch, HSB b h = Some ch -> h = 11%nat /\ ch = HSB_11 b.
Proof. intros b h ch Hh. unfold HSB in Hh. destruct (Nat.eqb_spec h 11) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_SB_0 : shape := SHole 11.
Definition shape_SB_1 : shape := SHole 11.
Definition shape_SB (b : bool) : shape := if b then shape_SB_1 else shape_SB_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_SB : forall b : bool,
  check BSEGS ITB BOTH (NXB b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXB b) AsanInit.LIMIT) XE0 XB0 (HSB b) KC0 BFUEL FUEL None (BothStartupCertB1.HSB1_13 b) (startup_plan_segB1_k) = COk (shape_SB b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_SB_1)).
  (vm_cert_refl constr:(COk shape_SB_0)).
Qed.
End BothStartupCertSB.

Module BothStartupCertC.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITC : itab := mk_itab_ranges BSEGS [(0x3ccb0, 40%nat); (0x556a0, 44%nat); (0x55800, 12%nat); (0x558d0, 40%nat); (0x55a00, 20%nat); (0x56800, 12%nat); (0x5dcd0, 24%nat); (0x5dd40, 20%nat); (0x5de40, 16%nat); (0x5df30, 12%nat); (0x5df70, 28%nat); (0x5e090, 32%nat); (0x5e1e0, 12%nat); (0x5e220, 40%nat); (0x5e360, 24%nat); (0x5e460, 28%nat); (0x5e590, 24%nat); (0x5e600, 20%nat); (0x61f60, 16%nat); (0x66030, 20%nat); (0x67720, 44%nat); (0x678d0, 20%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6b730, 12%nat); (0x6e160, 48%nat); (0x6e270, 16%nat); (0x6e770, 24%nat); (0x6e880, 24%nat); (0x6e8f0, 16%nat); (0x9ad64, 8%nat); (0x9c664, 16%nat)]%Z.
Lemma ITC_ok : itab_sound BSEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the renumbering table: old 344 is new 350, the start counter of the computed hand-off 11; old 377 is new 383 *)
Definition T_SC : list (nat * nat) := [(13, 4); (207, 4); (208, 4); (310, 6); (344, 6)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXC (b : bool) : nat := nxt (BothStartupCertSB.HSB_11 b).
Lemma NXC_ge : forall b, (NX0 <= NXC b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition startup_plan_segB_k : plan := PlanRegen.psh (PlanRegen.tshift T_SC) startup_plan_both_segB.
Definition run_SC (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITC BOTH (NXC b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXC b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertSB.HSB_11 b) (startup_plan_segB_k).
Definition HSL_SC_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SC false) [].
Definition HSL_SC_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SC true) [].
Definition HSC_14 (b : bool) : acs := PlanRegen.hstate (if b then HSL_SC_1 else HSL_SC_0) (BothStartupCertSB.HSB_11 b) 14.
Definition HSC (b : bool) (h : nat) : option acs := if Nat.eqb h 14 then Some (HSC_14 b) else None.
Lemma HSC_one : forall b h ch, HSC b h = Some ch -> h = 14%nat /\ ch = HSC_14 b.
Proof. intros b h ch Hh. unfold HSC in Hh. destruct (Nat.eqb_spec h 14) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_SC_0 : shape := SCase (EVar 6) 10 (SCase (EVar 10) 0 (SHole 14) (SHole 14)) (SCase (EVar 10) 6 (SHole 14) (SHole 14)).
Definition shape_SC_1 : shape := SCase (EVar 6) 10 (SCase (EVar 10) 0 (SHole 14) (SHole 14)) (SCase (EVar 10) 6 (SHole 14) (SHole 14)).
Definition shape_SC (b : bool) : shape := if b then shape_SC_1 else shape_SC_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_SC : forall b : bool,
  check BSEGS ITC BOTH (NXC b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXC b) AsanInit.LIMIT) XE0 XB0 (HSC b) KC0 BFUEL FUEL None (BothStartupCertSB.HSB_11 b) (startup_plan_segB_k) = COk (shape_SC b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_SC_1)).
  (vm_cert_refl constr:(COk shape_SC_0)).
Qed.
End BothStartupCertC.

Module BothStartupCertQ.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITQ : itab := mk_itab_ranges BSEGS [(0x3cd30, 20%nat); (0x3d470, 20%nat); (0x42560, 4%nat); (0x48410, 36%nat); (0x53160, 8%nat); (0x53b30, 68%nat); (0x56800, 12%nat); (0x56900, 16%nat); (0x56980, 20%nat); (0x5b400, 12%nat); (0x5b4b0, 20%nat); (0x5ba20, 12%nat); (0x5bd00, 8%nat); (0x5dcb0, 16%nat); (0x5e0f0, 12%nat); (0x5e4b0, 16%nat); (0x5e6f0, 28%nat); (0x5f890, 8%nat); (0x61f10, 20%nat); (0x66030, 16%nat); (0x677b0, 28%nat); (0x6b3e0, 44%nat); (0x6b4f0, 12%nat); (0x6b5b0, 28%nat); (0x6c760, 44%nat); (0x6c890, 52%nat); (0x6c970, 32%nat); (0x7c4f0, 20%nat); (0x7c570, 20%nat); (0x8e5c4, 8%nat); (0x8ec84, 44%nat); (0x8ef54, 20%nat); (0x8efb4, 12%nat); (0x8f034, 12%nat); (0x8f144, 24%nat); (0x8f214, 12%nat); (0x8f254, 12%nat); (0x8f2c4, 32%nat); (0x8f4a4, 12%nat); (0x9a964, 8%nat); (0x9b5b4, 32%nat); (0x9c664, 16%nat)]%Z.
Lemma ITQ_ok : itab_sound BSEGS ITQ.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the renumbering table: old 378 is new 384, the start counter of the computed hand-off 14 *)
Definition T_SQ : list (nat * nat) := [(13, 4); (207, 4); (208, 4); (310, 6); (344, 6); (378, 6)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXQ (b : bool) : nat := nxt (BothStartupCertC.HSC_14 b).
Lemma NXQ_ge : forall b, (NX0 <= NXQ b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition qc2_k : plan := PlanRegen.psh (PlanRegen.tshift T_SQ) startup_plan_both_qc2.
Definition segQ_k : plan := PlanRegen.psh (PlanRegen.tshift T_SQ) startup_plan_both_segQ.
(* the AT_RANDOM copy's split chain, made again from the computed start state by PlanRegen's chain rule;
   the seven top leaves' register values are read with the generic branch cut at PHandoff 899 *)
Definition planQ_with (g : plan) (t : Z) (ls : list plan) : plan :=
  PlanRegen.pmapH (PlanRegen.swap_chain (PlanRegen.chain g t ls)) segQ_k.
Definition TopQ (b : bool) : Z := PlanRegen.atr8_top (BothStartupCertC.HSC_14 b).
Definition cutQ (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITQ BOTH (NXQ b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXQ b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertC.HSC_14 b) (planQ_with (PHandoff 899) (TopQ b) PlanRegen.chain_cuts).
Definition CutQ_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (cutQ false) [].
Definition CutQ_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (cutQ true) [].
Definition LitsQ_0 := Eval vm_compute in map (PlanRegen.rlit CutQ_0) (seq 0 7).
Definition LitsQ_1 := Eval vm_compute in map (PlanRegen.rlit CutQ_1) (seq 0 7).
Definition planQ (b : bool) : plan := planQ_with qc2_k (TopQ b) (map (PlanRegen.leaf qc2_k) (if b then LitsQ_1 else LitsQ_0)).
Definition run_SQ (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITQ BOTH (NXQ b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXQ b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertC.HSC_14 b) (planQ b).
Definition HSL_SQ_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SQ false) [].
Definition HSL_SQ_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SQ true) [].
Definition HSQ_12 (b : bool) : acs := PlanRegen.hstate (if b then HSL_SQ_1 else HSL_SQ_0) (BothStartupCertC.HSC_14 b) 12.
Definition HSQ (b : bool) (h : nat) : option acs := if Nat.eqb h 12 then Some (HSQ_12 b) else None.
Lemma HSQ_one : forall b h ch, HSQ b h = Some ch -> h = 12%nat /\ ch = HSQ_12 b.
Proof. intros b h ch Hh. unfold HSQ in Hh. destruct (Nat.eqb_spec h 12) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_SQ_0 : shape := SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044348 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044349 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044350 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044351 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044352 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044353 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044354 (SHole 12) (SHole 12))))))).
Definition shape_SQ_1 : shape := SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044344 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044345 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044346 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044347 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044348 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044349 (SHole 12) (SCase (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 512) (EVar 10)) (EVar 11)))))) 17592186044350 (SHole 12) (SHole 12))))))).
Definition shape_SQ (b : bool) : shape := if b then shape_SQ_1 else shape_SQ_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_SQ : forall b : bool,
  check BSEGS ITQ BOTH (NXQ b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXQ b) AsanInit.LIMIT) XE0 XB0 (HSQ b) KC0 BFUEL FUEL None (BothStartupCertC.HSC_14 b) (planQ b) = COk (shape_SQ b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_SQ_1)).
  (vm_cert_refl constr:(COk shape_SQ_0)).
Qed.
End BothStartupCertQ.

Module BothStartupCertD.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITD : itab := mk_itab_ranges BSEGS [(0x30d10, 8%nat); (0x53c30, 20%nat); (0x55680, 36%nat); (0x558d0, 12%nat); (0x55920, 16%nat); (0x55a00, 20%nat); (0x56800, 12%nat); (0x5a5a0, 16%nat); (0x5b230, 16%nat); (0x5b420, 20%nat); (0x5b790, 16%nat); (0x5c240, 8%nat); (0x5d160, 40%nat); (0x5dcb0, 16%nat); (0x60070, 32%nat); (0x60140, 16%nat); (0x61f10, 20%nat); (0x62620, 8%nat); (0x62670, 8%nat); (0x657b0, 8%nat); (0x65830, 8%nat); (0x658e0, 20%nat); (0x65980, 16%nat); (0x66030, 16%nat); (0x67720, 64%nat); (0x678a0, 12%nat); (0x678f0, 12%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6a7c0, 36%nat); (0x6a9f0, 16%nat); (0x6aa50, 40%nat); (0x6ab00, 28%nat); (0x6aca0, 24%nat); (0x81c30, 84%nat); (0x81ed0, 12%nat); (0x825d0, 8%nat); (0x8d1c0, 16%nat); (0x8d270, 8%nat); (0x8dce4, 8%nat); (0x8dd14, 8%nat); (0x8ec84, 24%nat); (0x8ecf4, 24%nat); (0x8ed64, 124%nat); (0x8f264, 56%nat); (0x8f4a4, 164%nat); (0x8f844, 156%nat); (0x8fb24, 108%nat); (0x92394, 84%nat); (0x9ad64, 8%nat); (0x9b294, 8%nat); (0x9b484, 8%nat); (0x9b514, 12%nat); (0x9b624, 36%nat); (0x9c664, 16%nat); (0x9d624, 28%nat)]%Z.
Lemma ITD_ok : itab_sound BSEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* the renumbering table: old 394 is new 400, the start counter of the computed hand-off 12; the plan's PBump 437 is met at counter 436, below its renumbered 443 *)
Definition T_SD : list (nat * nat) := [(13, 4); (207, 4); (208, 4); (310, 6); (344, 6); (378, 6); (394, 6)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXD (b : bool) : nat := nxt (BothStartupCertQ.HSQ_12 b).
Lemma NXD_ge : forall b, (NX0 <= NXD b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition startup_plan_segC_k : plan := PlanRegen.psh (PlanRegen.tshift T_SD) startup_plan_both_segC.
Definition run_SD (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS ITD BOTH (NXD b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXD b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertQ.HSQ_12 b) (startup_plan_segC_k).
Definition HSL_SD_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SD false) [].
Definition HSL_SD_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_SD true) [].
Definition HSD_0 (b : bool) : acs := PlanRegen.hstate (if b then HSL_SD_1 else HSL_SD_0) (BothStartupCertQ.HSQ_12 b) 0.
Definition HSD (b : bool) (h : nat) : option acs := if Nat.eqb h 0 then Some (HSD_0 b) else None.
Lemma HSD_one : forall b h ch, HSD b h = Some ch -> h = 0%nat /\ ch = HSD_0 b.
Proof. intros b h ch Hh. unfold HSD in Hh. destruct (Nat.eqb_spec h 0) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. Qed.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_SD_0 : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
Definition shape_SD_1 : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
Definition shape_SD (b : bool) : shape := if b then shape_SD_1 else shape_SD_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_SD : forall b : bool,
  check BSEGS ITD BOTH (NXD b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXD b) AsanInit.LIMIT) XE0 XB0 (HSD b) KC0 BFUEL FUEL None (BothStartupCertQ.HSQ_12 b) (startup_plan_segC_k) = COk (shape_SD b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_SD_1)).
  (vm_cert_refl constr:(COk shape_SD_0)).
Qed.
End BothStartupCertD.

Module BothStartupCertS2.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert2.IT2.
Definition IT2_ok : itab_sound BSEGS IT2 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert2.IT2_ok.
(* the renumbering table: old 453 is new 459, the start counter of the computed hand-off 0 *)
Definition T_S2 : list (nat * nat) := [(13, 4); (207, 4); (208, 4); (310, 6); (344, 6); (378, 6); (394, 6); (453, 6)]%nat.
(* the segment's fresh-variable floor: the counter of the state the segment before hands off *)
Definition NXS2 (b : bool) : nat := nxt (BothStartupCertD.HSD_0 b).
Lemma NXS2_ge : forall b, (NX0 <= NXS2 b)%nat.
Proof. intros [|]; apply Nat.leb_le; vm_compute; reflexivity. Qed.
Definition startup2_plan_k : plan := PlanRegen.psh (PlanRegen.tshift T_S2) startup2_plan_both.
Definition run_S2 (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS IT2 BOTH (NXS2 b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXS2 b) AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (BothStartupCertD.HSD_0 b) (startup2_plan_k).
Definition HSL_S2_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S2 false) [].
Definition HSL_S2_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S2 true) [].
Definition HS2_1 (b : bool) : acs := PlanRegen.hstate (if b then HSL_S2_1 else HSL_S2_0) (BothStartupCertD.HSD_0 b) 1.
Definition HS2_2 (b : bool) : acs := PlanRegen.hstate (if b then HSL_S2_1 else HSL_S2_0) (BothStartupCertD.HSD_0 b) 2.
Definition HS2 (b : bool) (h : nat) : option acs :=
  if Nat.eqb h 1 then Some (HS2_1 b) else if Nat.eqb h 2 then Some (HS2_2 b) else None.
(* the result the check gives, as a literal; the kernel re-checks it *)
Definition shape_S2_0 : shape := SCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 350))) (ELit 3935)) 4030 (SHole 1) (SHole 2).
Definition shape_S2_1 : shape := SCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 350))) (ELit 3935)) 4030 (SHole 1) (SHole 2).
Definition shape_S2 (b : bool) : shape := if b then shape_S2_1 else shape_S2_0.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma cert_S2 : forall b : bool,
  check BSEGS IT2 BOTH (NXS2 b) AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH (NXS2 b) AsanInit.LIMIT) XE0 XB0 (HS2 b) KC0 BFUEL FUEL None (BothStartupCertD.HSD_0 b) (startup2_plan_k) = COk (shape_S2 b).
Proof.
  intros [|].
  (vm_cert_refl constr:(COk shape_S2_1)).
  (vm_cert_refl constr:(COk shape_S2_0)).
Qed.
End BothStartupCertS2.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import BothStartupCertDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.
Import BothStartupCertB1 BothStartupCertSB BothStartupCertC BothStartupCertQ BothStartupCertD BothStartupCertS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Section Boot.
  (* [comment removed for export] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable xfn : list byte.
  (* the kernel build, the argument after xfn at every AsanInit export below *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).

  #[local] Notation SINV := (SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  #[local] Notation argH := (argH0 sp rdraw argv envp xfn kb).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw xfn kb).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* the run's rseq flag: every certificate is used at it *)
  #[local] Notation RB := (kb_rseq kb).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  (* the main phase, from the start-up's final hand-off states as this run computes them *)
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM (HS2 RB) SINV argH (fun _ => H) fs.

  Let AH := argH0_high apc sp rdraw argv envp Hsp Hva xfn kb.
  Let AH2 := argH0_high2 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net Hsp Hva Hve Hfit nof sigm abt ifs urnd tmp xfn kb sgd Hlau.
  Let AA := argH0_agree sp rdraw argv envp xfn kb.
  Let SF := SINV0_frame BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.
  Let SA := SINV0_agree BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS BOTH LIM HSn SINV argH HH fs ->
      check BSEGS IT BOTH nx LIM (rseq_z RB) (XNS BSEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound BSEGS IT IT_ok BOTH nx Hnx LIM (rseq_z RB) HSn (XNS BSEGS BOTH nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
                (both_node_x_sound_all apc sp rdraw brk0 mbase argv envp stdin fs uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                (XNS_sound BSEGS BOTH nx LIM SINV argH fs AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* each segment's shape has only holes, at either rseq value *)
  Ltac holes_by_cases := cbv beta; match goal with |- holes_only (?f ?b) = true => unfold f; destruct b; vm_compute; reflexivity end.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt BSEGS BOTH LIM (HSD RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSD RB) 0%nat (HSD_0 RB) (HSD_one RB)).
    apply (seg_sound (NXS2 RB) (NXS2_ge RB) IT2 IT2_ok (HS2 RB) FUEL BFUEL KC0 startup2_plan_k (HSD_0 RB) (shape_S2 RB));
      [| exact (cert_S2 RB) | holes_by_cases].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS BOTH LIM (HSQ RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSQ RB) 12%nat (HSQ_12 RB) (HSQ_one RB)).
    apply (seg_sound (NXD RB) (NXD_ge RB) ITD ITD_ok (HSD RB) FUEL BFUEL KC0 startup_plan_segC_k (HSQ_12 RB) (shape_SD RB));
      [exact S2_sound | exact (cert_SD RB) | holes_by_cases].
  Qed.
  Lemma Q_sound : holes_stmt BSEGS BOTH LIM (HSC RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSC RB) 14%nat (HSC_14 RB) (HSC_one RB)).
    apply (seg_sound (NXQ RB) (NXQ_ge RB) ITQ ITQ_ok (HSQ RB) FUEL BFUEL KC0 (planQ RB) (HSC_14 RB) (shape_SQ RB));
      [exact D_sound | exact (cert_SQ RB) | holes_by_cases].
  Qed.
  Lemma C_sound : holes_stmt BSEGS BOTH LIM (HSB RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSB RB) 11%nat (HSB_11 RB) (HSB_one RB)).
    apply (seg_sound (NXC RB) (NXC_ge RB) ITC ITC_ok (HSC RB) FUEL BFUEL KC0 startup_plan_segB_k (HSB_11 RB) (shape_SC RB));
      [exact Q_sound | exact (cert_SC RB) | holes_by_cases].
  Qed.
  Lemma B_sound : holes_stmt BSEGS BOTH LIM (HSB1 RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSB1 RB) 13%nat (HSB1_13 RB) (HSB1_one RB)).
    apply (seg_sound (NXB RB) (NXB_ge RB) ITB ITB_ok (HSB RB) FUEL BFUEL KC0 startup_plan_segB1_k (HSB1_13 RB) (shape_SB RB));
      [exact C_sound | exact (cert_SB RB) | holes_by_cases].
  Qed.
  Lemma B1_sound : holes_stmt BSEGS BOTH LIM (HSA RB) SINV argH HH fs.
  Proof.
    apply (seg_holes (HSA RB) 10%nat (HSA_10 RB)).
    { intros h ch Hh. unfold HSA in Hh. destruct (Nat.eqb_spec h 10) as [->|]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound (NXB1 RB) (NXB1_ge RB) ITB1 ITB1_ok (HSB1 RB) FUEL BFUEL KC0 startup_plan_segA_k (HSA_10 RB) (shape_B1 RB));
      [exact B_sound | exact (cert_B1 RB) | holes_by_cases].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd))
              (sd HH t_nil E0a fs startup_shape).
  Proof.
    exact (both_startup apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd
             Hfs Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau
             IT0 IT0_ok (HSA RB) startup_plan_k startup_shape KC0 BFUEL FUEL (startup_cert RB) HH HH_agree HH_nil B1_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd))
              (H E0a fs).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
