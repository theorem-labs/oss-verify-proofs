(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, in the shape of cgif/cgif_file_fuzzer's A/AB01r.v; the hand-off states collected in one run of the check. *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's A/AB01r.v for this unit's ASan start-up run: its join state and hand-off states, per CONFIG_RSEQ flag, computed in the build by check with this unit's PlanRegen.v in place of the recorded ones; taken from projects/libreac/fuzz_boxreg/proofs/lib/A/AB01r.v, lines 20-23, 49, 52, 70-73, 79, 87 and 93, as in the LPS 727298f3 update. *)
(* The ASan start-up run's join state and hand-off states at LPS 727298f3, per value [r] of the
   run's CONFIG_RSEQ flag (0 or 1), computed from the run by [check] rather than recorded, and
   the start-up certificate over them; the form of libreac/fuzz_boxreg's proofs/lib/A/AB01r.v
   with this unit's [PlanRegen.v].  The recorded plan [Asang3k.startup_plan] is checked with its
   fresh variables renumbered ([vsh]), its [PExt 7] respell rows reading AT_NULL's type word at
   its 727298f3 place ([ext7]), and its one [PVia] join state and floor replaced ([pvia_set]).
   The recorded [Staruoz.HS_asan] and [Asang3k.Stargw5.JS_asan_s1] were written against the
   released model's launch (a 10-pair auxv, AT_RANDOM above the vectors). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Asan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe Asanz3l AsanPlan Asanqlm Asanlzb Asang3k Staruoz PlanRegen.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang3k.Startjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang3k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PlanRegen.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Bootzb6.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

(* 0. The plan's variables, renumbered to the new run: the launch has one more variable
   ([Asanz3l.V_GID] at 12, NX0 12 -> 13) and the run makes more fresh variables than the
   recorded one, read in two steps, at both flags:
   - four higher from 12: the probe record of this port stops the unrenumbered run after the plan's
     [PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)] with the region the run made there at
     [4096 * EVar 82];
   - six higher from 322: the probe record runs the plan four higher to its [PVia] and shows the
     regions the plan names [EVar 228] and [EVar 257] at [EVar 232] and [EVar 261], the one it names
     [EVar 322] at [EVar 328], and the arms' first node [PBump 356] (four higher: 360) refused at
     counter 362; no variable the plan or a recorded hand-off state names lies between 258 and 321.
   The two steps hold to the hand-offs: the probe record pairs the 33 live fresh variables of each
   recorded hand-off state with the computed one's exactly by [vsh] (the thread id 44 at 48), and
   checks the certificate below to [COk] at both flags.  Read, not chosen. *)
Definition vsh (v : nat) : nat :=
  if Nat.ltb v 12 then v else if Nat.ltb v 322 then (v + 4)%nat else (v + 6)%nat.

(* 1. AT_NULL's type word, which the plan's [PExt 7] rows respell before each join and
   hand-off: pair 9 of the released model's 10-pair auxv, at [24 + 16 * 9 = 168] above
   [usp + 8 argc + 8 envc]; at 727298f3 pair [26 + 2 r] ([StackLayout.auxv_entries];
   [Asanz3l.init_kn_with]'s [auxw (26 + 2 * r) 0 (ELit 0)]), at [24 + 16 (26 + 2 r) = 440 + 32 r]. *)
Definition ext7 (off : Z) (id : nat) (args : list expr) : list expr :=
  if Nat.eqb id 7 then match args with [b; ELit 168; e] => [b; ELit off; e] | _ => args end else args.
(* 2. The hand-off states in the numbering the next segments were written against: before
   each hand-off the plan renames the fresh variables the recorded hand-off state lists
   ([Staruoz.HS_asan_0]/[HS_asan_1], read with [csvars_fo]) from their new numbers back to their
   recorded ones, so that [Asan5d5.startup_plan2]/[startup_plan2b] and the facts recorded
   after main's entry name the same variables they were written against.  [node_rename] checks
   the map (both sides at or above the plan's floor, no live variable clobbered); a wrong map
   can only make the certificate fail. *)
Definition old_hs (h : nat) : acs :=
  match h with O => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Staruoz.HS_asan_0
  | _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Staruoz.HS_asan_1 end.
Definition rb_map (h : nat) : list (nat * nat) :=
  map (fun v => (vsh v, v)) (filter (fun v => negb (Nat.eqb (vsh v) v)) (csvars_fo NX0 (old_hs h))).
Definition rb_handoff (h : nat) : plan :=
  match rb_map h with [] => PHandoff h | m => PRename m (PHandoff h) end.
Definition plan_sh (r : Z) : plan := pextmap (ext7 (440 + 32 * r)) rb_handoff (psh vsh startup_plan).

(* the certificate's own check, at flag [r] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  BFXC.check_f OSSVerify.varnish.esi_parse_fuzzer.images.Asan.M.loaded_segments IT0 ASAN NX0 target_alloc_limit r (XNa2 NX0) XE0 XB0 HS KC0 BFUEL FUEL lc cs p.

(* 2. The state at the [PVia] (the plan with its join state refused), the join state of its
   arms, the plan with that join state, and every hand-off state of the run (collected by
   checking the [PVia]'s continuation from the join state, which is what [check] does there). *)
Definition cs_via (r : Z) : acs :=
  match chk_from r (fun _ => None) None (asan_init r) (pvia_set JS_STOP 0 (plan_sh r)) with
  | CErr _ (PVia _ _ _ _ _) cs => cs | _ => JS_STOP end.
Definition arms (r : Z) : plan := match via_arms (plan_sh r) with Some k => k | None => PContra end.
Definition cont (r : Z) : plan := match via_cont (plan_sh r) with Some k => k | None => PContra end.
Definition js_of (r : Z) (cs : acs) : acs :=
  collect_arms 24 (fun js => chk_from r (fun _ => None) (Some (JC 0%nat js SNil (nxt cs) (nxt js))) cs (arms r)) JS_STOP false.
Definition hsl_of (r : Z) (js : acs) : list (nat * acs) :=
  collect_handoffs 24 (fun hs => chk_from r hs None js (cont r)) [].

Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in hsl_of 0 JS_0.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in hsl_of 1 JS_1.

Definition JS_asan_r (r : Z) : acs := if Z.eqb r 1 then JS_1 else JS_0.
Definition HSL_r (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_1 else HSL_0.
Definition startup_plan_r (r : Z) : plan := pvia_set (JS_asan_r r) (nxt (JS_asan_r r)) (plan_sh r).
(* the hand-offs the run reaches, and only those *)
Definition HS_asan_r (r : Z) (h : nat) : option acs := hlookup (HSL_r r) h.
Definition HS_asan_0r (r : Z) : acs := hstate (HSL_r r) JS_STOP 0.
Definition HS_asan_1r (r : Z) : acs := hstate (HSL_r r) JS_STOP 1.

(* THE START-UP CERTIFICATE, at each value of the run's CONFIG_RSEQ flag. *)
Lemma startup_cert : forall r, 0 <= r <= 1 ->
  check OSSVerify.varnish.esi_parse_fuzzer.images.Asan.M.loaded_segments IT0 ASAN NX0 target_alloc_limit r (XNa2 NX0) XE0 XB0 (HS_asan_r r) KC0 BFUEL FUEL None
        (asan_init r) (startup_plan_r r) = COk startup_shape.
Proof.
  intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia.
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape)).
  - cert_f. ltac2:(cert_refl constr:(COk startup_shape)).
Qed.

Lemma HS_asan_r_cases : forall r h ch, 0 <= r <= 1 -> HS_asan_r r h = Some ch ->
  (h = 0%nat /\ ch = HS_asan_0r r) \/ (h = 1%nat /\ ch = HS_asan_1r r).
Proof.
  intros r h ch Hr H. unfold HS_asan_0r, HS_asan_1r, hstate. unfold HS_asan_r in H.
  destruct h as [|[|h]]; [left | right | exfalso].
  - split; [reflexivity|]. rewrite H. reflexivity.
  - split; [reflexivity|]. rewrite H. reflexivity.
  - assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in H; discriminate H.
Qed.
Lemma pc_HS_asan_0r : forall r, 0 <= r <= 1 -> pc (HS_asan_0r r) = 0x876fc.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma pc_HS_asan_1r : forall r, 0 <= r <= 1 -> pc (HS_asan_1r r) = 0x876fc.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
