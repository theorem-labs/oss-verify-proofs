(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, in the shape of cgif/cgif_file_fuzzer's A/AB01r.v; the hand-off states collected in one run of the check. *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's A/AB01r.v for this unit's ASan+UBSan start-up run: the join states and main-entry hand-off states of its second start-up segments (from the root's hand-offs to main's entry), per CONFIG_RSEQ flag, computed in the build by check with this unit's PlanRegen.v in place of the recorded ones; taken from projects/libreac/fuzz_boxreg/proofs/lib/A/AB01r.v, lines 20, 87 and 93, as in the LPS 727298f3 update. *)
(* The ASan+UBSan run's second start-up segments (from the root's hand-offs 0 and 1 to main's entry)
   at LPS 727298f3, per value [r] of the run's CONFIG_RSEQ flag: their join states and the
   hand-off states at main's entry computed from the run by [check] rather than recorded, and the
   two certificates over them.  The plans [Both6eh.startup_plan_both2]/[startup_plan_both2b] are checked
   as recorded, but for their one [PVia] join state and floor ([pvia_set]): they start from the
   root's computed hand-off states [BothRegen.HS_both_0r]/[HS_both_1r].  The recorded
   [Starr0h]'s and [Both6eh]'s join states were written against the
   released model's launch. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe Asanz3l AsanPlan Asanqlm Asanlzb Bothy0u Both6eh PlanRegen BothRegen.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothy0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh.Starfcw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PlanRegen OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.BothRegen.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Bootzb6.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

(* the certificates' own check, at flag [r] *)
Definition chk2_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  BFXC.check_f OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.loaded_segments IT2b BOTH NX2b target_alloc_limit r (XNb2 NX2b) XE0 XB0 HS KC2b BFUEL2b FUEL2b lc cs p.

(* the state at the [PVia], its arms' join state, and the hand-off states, as [AsanRegen] *)
Section Seg.
  Variable r : Z.
  Variable cs0 : acs.
  Variable p : plan.
  Definition seg_via : acs :=
    match chk2_from r (fun _ => None) None cs0 (pvia_set JS_STOP 0 p) with
    | CErr _ (PVia _ _ _ _ _) cs => cs | _ => JS_STOP end.
  Definition seg_arms : plan := match via_arms p with Some k => k | None => PContra end.
  Definition seg_cont : plan := match via_cont p with Some k => k | None => PContra end.
  Definition seg_js (cs : acs) : acs :=
    collect_arms 24 (fun js => chk2_from r (fun _ => None) (Some (JC 0%nat js SNil (nxt cs) (nxt js))) cs seg_arms) JS_STOP false.
  Definition seg_hsl (js : acs) : list (nat * acs) :=
    collect_handoffs 24 (fun hs => chk2_from r hs None js seg_cont) [].
End Seg.

Definition VIA2_0 : acs := Eval vm_compute in seg_via 0 (HS_both_0r 0) startup_plan_both2.
Definition VIA2_1 : acs := Eval vm_compute in seg_via 1 (HS_both_0r 1) startup_plan_both2.
Definition VIA2b_0 : acs := Eval vm_compute in seg_via 0 (HS_both_1r 0) startup_plan_both2b.
Definition VIA2b_1 : acs := Eval vm_compute in seg_via 1 (HS_both_1r 1) startup_plan_both2b.
Definition JS2_0 : acs := Eval vm_compute in seg_js 0 startup_plan_both2 VIA2_0.
Definition JS2_1 : acs := Eval vm_compute in seg_js 1 startup_plan_both2 VIA2_1.
Definition JS2b_0 : acs := Eval vm_compute in seg_js 0 startup_plan_both2b VIA2b_0.
Definition JS2b_1 : acs := Eval vm_compute in seg_js 1 startup_plan_both2b VIA2b_1.
Definition HSL2_0 : list (nat * acs) := Eval vm_compute in seg_hsl 0 startup_plan_both2 JS2_0.
Definition HSL2_1 : list (nat * acs) := Eval vm_compute in seg_hsl 1 startup_plan_both2 JS2_1.
Definition HSL2b_0 : list (nat * acs) := Eval vm_compute in seg_hsl 0 startup_plan_both2b JS2b_0.
Definition HSL2b_1 : list (nat * acs) := Eval vm_compute in seg_hsl 1 startup_plan_both2b JS2b_1.

Definition JS2_r (r : Z) : acs := if Z.eqb r 1 then JS2_1 else JS2_0.
Definition JS2b_r (r : Z) : acs := if Z.eqb r 1 then JS2b_1 else JS2b_0.
Definition HSL2_r (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL2_1 else HSL2_0.
Definition HSL2b_r (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL2b_1 else HSL2b_0.
Definition startup_plan_both2_r (r : Z) : plan := pvia_set (JS2_r r) (nxt (JS2_r r)) startup_plan_both2.
Definition startup_plan_both2b_r (r : Z) : plan := pvia_set (JS2b_r r) (nxt (JS2b_r r)) startup_plan_both2b.
(* the hand-off tables at main's entry, and their two states each *)
Definition HS_both2_r (r : Z) (h : nat) : option acs := hlookup (HSL2_r r) h.
Definition HS_both2b_r (r : Z) (h : nat) : option acs := hlookup (HSL2b_r r) h.
Definition HS_both2_1r (r : Z) : acs := hstate (HSL2_r r) JS_STOP 1.
Definition HS_both2_2r (r : Z) : acs := hstate (HSL2_r r) JS_STOP 2.
Definition HS_both2b_1r (r : Z) : acs := hstate (HSL2b_r r) JS_STOP 1.
Definition HS_both2b_2r (r : Z) : acs := hstate (HSL2b_r r) JS_STOP 2.

Lemma startup_cert_both2 : forall r, 0 <= r <= 1 ->
  check OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.loaded_segments IT2b BOTH NX2b target_alloc_limit r (XNb2 NX2b) XE0 XB0 (HS_both2_r r) KC2b BFUEL2b FUEL2b None
        (HS_both_0r r) (startup_plan_both2_r r) = COk startup_shape_both2.
Proof.
  intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia.
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape_both2)).
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape_both2)).
Qed.
Lemma startup_cert_both2b : forall r, 0 <= r <= 1 ->
  check OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.loaded_segments IT2b BOTH NX2b target_alloc_limit r (XNb2 NX2b) XE0 XB0 (HS_both2b_r r) KC2b BFUEL2b FUEL2b None
        (HS_both_1r r) (startup_plan_both2b_r r) = COk startup_shape_both2.
Proof.
  intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia.
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape_both2)).
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape_both2)).
Qed.

Lemma HS_both2_r_cases : forall r h ch, 0 <= r <= 1 -> HS_both2_r r h = Some ch ->
  (h = 1%nat /\ ch = HS_both2_1r r) \/ (h = 2%nat /\ ch = HS_both2_2r r).
Proof.
  intros r h ch Hr H. unfold HS_both2_1r, HS_both2_2r, hstate. unfold HS_both2_r in H.
  destruct h as [|[|[|h]]]; [exfalso | left | right | exfalso].
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in H; discriminate H.
  - split; [reflexivity|]. rewrite H. reflexivity.
  - split; [reflexivity|]. rewrite H. reflexivity.
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in H; discriminate H.
Qed.
Lemma HS_both2b_r_cases : forall r h ch, 0 <= r <= 1 -> HS_both2b_r r h = Some ch ->
  (h = 1%nat /\ ch = HS_both2b_1r r) \/ (h = 2%nat /\ ch = HS_both2b_2r r).
Proof.
  intros r h ch Hr H. unfold HS_both2b_1r, HS_both2b_2r, hstate. unfold HS_both2b_r in H.
  destruct h as [|[|[|h]]]; [exfalso | left | right | exfalso].
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in H; discriminate H.
  - split; [reflexivity|]. rewrite H. reflexivity.
  - split; [reflexivity|]. rewrite H. reflexivity.
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in H; discriminate H.
Qed.
Definition MAIN_PC2b : Z := 0x867f8.
Lemma pc_HS_both2_1r : forall r, 0 <= r <= 1 -> pc (HS_both2_1r r) = MAIN_PC2b.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma pc_HS_both2_2r : forall r, 0 <= r <= 1 -> pc (HS_both2_2r r) = MAIN_PC2b.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma pc_HS_both2b_1r : forall r, 0 <= r <= 1 -> pc (HS_both2b_1r r) = MAIN_PC2b.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma pc_HS_both2b_2r : forall r, 0 <= r <= 1 -> pc (HS_both2b_2r r) = MAIN_PC2b.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
