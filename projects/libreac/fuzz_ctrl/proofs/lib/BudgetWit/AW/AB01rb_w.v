(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of cgif/cgif_file_fuzzer's A/AB01r.v in this working copy; libreac/fuzz_boxreg's A/AB01r.v for libreac/fuzz_ctrl's asan image, with its module paths changed and the plan's variable map read for this unit; the hand-off states collected in one run of the check (as reac-pw/fuzz_headamp's A/AB01r.v); only its definitions: AB01r0.v and AB01r1.v compute them, one CONFIG_RSEQ flag each, and AB01r.v joins them (the file layout of plugin-hostd/fuzz_command's A/AB01r.v). *)
(* Modified by Theorem Labs, 2026-11: made for the ASan run at the 16 GiB limit (lib/BudgetWit/AW) from this unit's A/AB01rb.v, in place of AB01_w.v and AB03_w.v, with the modules it imports from that set renamed to their twins; split per CONFIG_RSEQ flag (AB01rb_w.v definitions, AB01r0_w.v and AB01r1_w.v one flag each, AB01r_w.v joining them under the same names), the layout of plugin-hostd/fuzz_command's A/AB01r.v; the hand-off states collected in one run of the check (reac-pw/fuzz_headamp's collect_handoffs1); taken from projects/libreac/fuzz_ctrl/proofs/lib/A/AB01rb.v, lines 9-14 and 18-78, as in the LPS 727298f3 update. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded
   plan [AB05_w.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen_w.pvia_set]); the recorded
   [AB01_w.HS_tfib] and [AB03_w.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_ctrl.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
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

(* 0. The plan's variables, renumbered to the new run.  From the launch layout alone
   (Reusable/YA01.v:724-730 and Reusable/YK09.v:2288 against the released YA01's V_HW 9 /
   NX0G 10): the launch has two more plan variables, [V_G] at 9 and [V_GID] at 11, so the
   released [V_HW] 9 is 10 and the first fresh variable 10 is 12.  Where the run draws fresh
   variables the recorded run did not, the further steps are read from the probe
   A/ZZ_ctrlvsh.v (the unshifted and the launch-shifted run, both flags) and written here
   with the probe's output line; no step is set from whether a check passes.  This file's map
   is A/AB01rb.v's: the ASan run at the 16 GiB limit is the same run. *)
(* Read from this unit's probes: the unshifted run reaches the plan's [PVia] with register 10
   holding [4096 * EVar 279] (A/ZZ_ctrlvsh.v, output ZZCV_U0/U1), where the plan's [PCaseDisj] names
   [4096 * EVar 275] (A/ZZ_ctrlarm.v, output ZZCA_U0/U1); under the launch map alone (+2) the split is taken
   on [EVar 277] and both arms then stop at a branch on register 10.  So the run's fresh
   variables are four higher from 10 on: the two launch variables above and two auxv values no
   variable denotes (the reading libreac/fuzz_knock's probes gave for its own run).  A further
   step, if the run draws more fresh variables later, is read from the next probe output. *)
(* The second step, read from this unit's probes under the four-shift: from the join state the
   run reaches the plan's [PBump 391] (395 under the four-shift) with its counter at 397, at both
   flags (A/ZZ_ctrljoin.v, output ZZCJ_V0/V1), where [YK09.node_bump] needs the counter at most
   the bound.  So two more fresh variables come between the band join and the [PBump 391], and
   the variables from 391 on are six higher. *)
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
