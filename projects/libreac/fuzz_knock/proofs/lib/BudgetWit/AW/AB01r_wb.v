(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_knock by a Theorem Labs lane from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v at theorem-labs/oss-verify-proofs@6b32741d849a; module paths renamed; the 50 hand-off states are fuzz_knock.asan's own start-up run *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the plan's fresh variables renumbered as the run reads them; the hand-off states collected in one run of the check; the definitions of this unit's A/AB01r.v without its computations (AB01r0.v and AB01r1.v compute them, one CONFIG_RSEQ flag each; AB01r.v joins them). *)
(* Modified by Theorem Labs, 2026-11: the hand-off states collected in one run of the check; made for LPS 727298f3 in place of the recorded hand-off states of BudgetWit/AW/AB01_w.v and the recorded join state of BudgetWit/AW/AB03_w.v, as A/AB01r.v is for the start-up at the 16 GiB limit: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v; the plan's fresh variables renumbered by A/AB01r.v's map; the definitions of this unit's BudgetWit/AW/AB01r_w.v without its computations (AB01r_w0.v and AB01r_w1.v compute them, one CONFIG_RSEQ flag each; AB01r_w.v joins them); taken from projects/libreac/fuzz_knock/proofs/lib/A/AB01rb.v, lines 11-16 and 20-71, as in the LPS 727298f3 update. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded
   plan [AB05_w.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen.pvia_set]); the recorded
   [AB01_w.HS_tfib] and [AB03_w.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_knock.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (BudgetWit/AW/YA0c_w.v), giving each hand-off it reaches
   to PlanRegen_w's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TFIB) p.

(* 0. The plan's variables, renumbered to the new run: the map of A/AB01r.v's [vsh], read there from
   the probes of this binary's start-up run (A/ZZ_knstart.v, A/ZZ_knvsh.v; outputs ZZKN_U0/U1,
   ZZKV_4, ZZKV_6).  The run at this file's limit is the same start-up code of the same binary, and
   the certificate BudgetWit/AW/AB1m_w.v checks the plan under this map at both flags. *)
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
   there: in one run ([collect_handoffs1]), the map [collect_handoffs] makes in one run per
   state it adds. *)
Definition plan_r (js : acs) : plan := pvia_set js (nxt js) plan_sh.
Definition cont : plan := match via_cont plan_sh with Some k => k | None => PContra end.
Definition HSL (r : Z) (js : acs) : list (nat * acs) :=
collect_handoffs1 60 (coll_from r None js cont) [].
