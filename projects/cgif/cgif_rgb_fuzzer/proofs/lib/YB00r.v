(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of YB00.v and the recorded band join state of YB02.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with PlanRegen.v (the hand-off states collected in one run of the check), and the recorded plan's variables renumbered by a map read from the run; the shape of cgif/cgif_file_fuzzer's A/AB01r.v. *)
(* The tra start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded plan
   [YB04.startup_plan_tra] is checked with its variables renumbered ([vsh]) and its one [PVia]
   join state and floor replaced ([PlanRegen.pvia_set]); the recorded [YB00.HS_tra] and
   [YB02.JS_tra_band] were written against the released model's launch. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0d YK0a YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB06 YB0l YB0p YB04.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tra_ranges) TRA NX0G YA02.LIMIT r (XNG TSEGS tra_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (YA0c.v), giving each hand-off it reaches to
   PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tra_ranges) TRA NX0G YA02.LIMIT r (XNG TSEGS tra_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TRA) p.

(* 0. The plan's variables, renumbered to the new run (the probe record of this unit,
   notes/probe-cgif__cgif_rgb_fuzzer.md, rounds P4 and P5).  The launch has two more plan
   variables ([V_G] at 9, [V_GID] at 11, so the released [V_HW] 9 is 10 now, NX0G 10 -> 12),
   and the run reads two auxv values no variable denotes, so its fresh variables are four
   higher: a probe build of this unit (markers ZZVIA_ARMS0/1) stops the unrenumbered run at
   the band arms' [PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))] with register 10
   holding [4096 * EVar 279], at both flags.  Two more fresh variables come between the band
   join and the plan's [PBump 391]: with the four-shift alone, the next probe build
   (markers ZZCONT_END0/1) stops the run from the computed join state at [PBump 395] with the
   counter at 397, at both flags.  Read, not chosen. *)
Definition vsh (v : nat) : nat :=
if Nat.ltb v 9 then v else if Nat.eqb v 9 then 10%nat
else if Nat.ltb v 391 then (v + 4)%nat else (v + 6)%nat.
Definition plan_sh : plan := psh vsh startup_plan_tra.
(* 1. The plan with its join state refused: the run up to the [PVia] and the state there.
   No hand-off lies before the [PVia]; if one did, this would stop at it and the certificate
   would be red. *)
Definition plan_stop : plan := pvia_set JS_STOP 0 plan_sh.
Definition cs_via (r : Z) : acs :=
match chk r (fun _ => None) plan_stop with CErr _ (PVia _ _ _ _ _) cs => cs | _ => JS_STOP end.
(* 2. The join state: the join of the two arms' end states; its floor is its own counter. *)
Definition js_of (r : Z) (cs : acs) : acs :=
match via_arms plan_sh with
| Some karms =>
match via_join (fun lc c p => chk_from r (fun _ => None) lc c p) node_casedisj_g 1 cs karms with
| Some js => js
| None => JS_STOP
end
| None => JS_STOP
end.
(* 3. The plan with that join state, and every hand-off state of the run, collected by
   checking the [PVia]'s continuation from the join state, which is what [check] does
   there: in one run ([collect_handoffs1]), the map [collect_handoffs] makes in one run per
   state it adds. *)
Definition plan_r (js : acs) : plan := pvia_set js (nxt js) plan_sh.
Definition cont : plan := match via_cont plan_sh with Some k => k | None => PContra end.
Definition HSL (r : Z) (js : acs) : list (nat * acs) :=
collect_handoffs1 120 (coll_from r None js cont) [].

Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL 0 JS_0.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL 1 JS_1.

Definition JS_tra_r (r : Z) : acs := if Z.eqb r 1 then JS_1 else JS_0.
Definition startup_plan_tra_r (r : Z) : plan := plan_r (JS_tra_r r).
Definition HSL_r (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_1 else HSL_0.
(* The hand-offs the run reaches, and only those: a hand-off the check never reaches has no
   state. *)
Definition HS_tra_r (r : Z) (h : nat) : option acs := hlookup (HSL_r r) h.
Definition HS_tra_list_r (r : Z) : list acs := map snd (HSL_r r).
(* Both flags' hand-off states in one list, which the driver's computed checks run over. *)
Definition HS_tra_list_all : list acs := HS_tra_list_r 0 ++ HS_tra_list_r 1.
Lemma HS_tra_r_In : forall r h ch, HS_tra_r r h = Some ch -> In ch HS_tra_list_all.
Proof.
intros r h ch H. unfold HS_tra_r, hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _].
unfold HS_tra_list_all, HS_tra_list_r. apply in_or_app. unfold HSL_r in F |- *.
destruct (Z.eqb r 1); [right | left]; exact (in_map snd _ _ F).
Qed.
