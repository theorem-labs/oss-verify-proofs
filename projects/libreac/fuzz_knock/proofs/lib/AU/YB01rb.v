(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_knock by a Theorem Labs lane from proofs/cgif/cgif_file_fuzzer/lib/YB01.v at theorem-labs/oss-verify-proofs@6b32741d849a; module paths renamed; the 50 hand-off states are fuzz_knock.asan-ubsan's own start-up run *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of YB01.v and the recorded join state of YB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the plan's fresh variables renumbered as the run reads them; the hand-off states collected in one run of the check; the definitions of this unit's AU/YB01r.v without its computations (YB01r0.v and YB01r1.v compute them, one CONFIG_RSEQ flag each; YB01r.v joins them). *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded
   plan [YB05.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen.pvia_set]); the recorded
   [YB01.HS_tfib] and [YB03.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_knock.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YB12 YB1h YB1l YB05.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (Reusable/YA0c.v), giving each hand-off it reaches
   to PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TFIB) p.

(* 0. The plan's variables, renumbered to the new run.  The launch has two more plan
   variables ([V_G] at 9, [V_GID] at 11, so the released [V_HW] 9 is 10 now, NX0G 10 -> 12),
   and the run reads two auxv values no variable denotes, so its fresh variables are four
   higher: the probe AU/ZZ_knstartU.v (output ZZKNU_U0/U1) stops the unshifted run at
   the plan's [PCaseDisj (ELit 2147446784) (EMd M_MUL (ELit 4096) (EVar 275))] with register
   10 holding [4096 * EVar 279], at both flags.  Two more fresh variables come between the
   band join and the plan's [PBump 391]: the probe AU/ZZ_knvshU.v (output ZZKVU_4) stops the
   four-shift alone at [PBump 395] (391 + 4) with counter 397, so the variables from 391 on
   are six higher, and under [vsh] (output ZZKVU_6) the flag-0 check from the join state over
   its 10 collected hand-offs ends [COk]. *)
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
