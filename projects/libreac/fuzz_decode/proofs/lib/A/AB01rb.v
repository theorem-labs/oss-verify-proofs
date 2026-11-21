(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of cgif/cgif_file_fuzzer's A/AB01r.v in this working copy; made for libreac/fuzz_decode from libreac/fuzz_boxreg's A/AB01r.v: this unit's module paths, and the plan's variables renumbered by a map read from this unit's probes; split per CONFIG_RSEQ flag (AB01rb.v definitions, AB01r0.v and AB01r1.v one flag each, AB01r.v joining them under the same names), the layout of plugin-hostd/fuzz_command's A/AB01r.v; the hand-off states collected in one run of the check (reac-pw/fuzz_headamp's collect_handoffs1). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_decode.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB12 AB1h AB1l AB05.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (YA0c.v), giving each hand-off it reaches to PlanRegen's
   [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TFIB) p.

(* 0. The plan's variables, renumbered to the new run.  The launch has two more plan
   variables ([V_G] at 9, [V_GID] at 11, so the released [V_HW] 9 is 10 now, NX0G 10 -> 12:
   Reusable/YA01.v:724-730),
   and the run reads two auxv values no variable denotes, so its fresh variables are four
   higher: the probe A/ZZ_decstart.v (its output ZZDEC_A0/A1) stops the recorded plan at
   its [PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))] with register 10 holding
   [4096 * EVar 279], at both flags.  The step at the plan's [PBump 391], above the band join,
   is read by the probe A/ZZ_decV40.v / ZZ_decV41.v of the run from the computed join state with the
   four-shift alone (output ZZDV_V4_0/1): at both flags it stops at the plan's [PBump 395]
   with the run's counter at 397, two above it, so from the plan's 391 up the shift is six. *)
Definition vsh (v : nat) : nat :=
if Nat.ltb v 9 then v else if Nat.eqb v 9 then 10%nat
else if Nat.ltb v 391 then (v + 4)%nat else (v + 6)%nat.
Definition plan_sh : plan := psh vsh startup_plan_tfib.
(* 1. The plan with its join state refused: the run up to the [PVia] and the state there. *)
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
   there. *)
Definition plan_r (js : acs) : plan := pvia_set js (nxt js) plan_sh.
Definition cont : plan := match via_cont plan_sh with Some k => k | None => PContra end.
Definition HSL (r : Z) (js : acs) : list (nat * acs) :=
collect_handoffs1 60 (coll_from r None js cont) [].
