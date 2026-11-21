(* SPDX-License-Identifier: MIT *)
(* Start-up data of the Both build at LPS 727298f3, computed at CONFIG_RSEQ value r = 1.  Written by gen_startup_regen.py from the start-up
   probe's printout (docs/343-certificate-data-method.md, sections 2, 3 and 5).  No state here is recorded: every
   state, table, counter and shape is computed by vm_compute from [check], and each certificate re-checks it. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan BothPlanImages
  AsanInit AsanNodesWJoin StartupPlanBoth StartupPlan2Both BothCertDefs PlanRegen StartupRegenBothPlans.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* ---- plan A at r = 1 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colA_1 : cres * list (nat * acs) := Eval vm_compute in
  checkC BSEGS IT0 BOTH NX0 AsanInit.LIMIT 1 (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (both_init 1) (planA 1) [].
Definition hslA_1 : list (nat * acs) := snd colA_1.
Definition stA_1 : acs := hstate hslA_1 (both_init 1) 10.
Definition shapeA_1 : shape := match fst colA_1 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan B at r = 1 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colB_1 : cres * list (nat * acs) := Eval vm_compute in
  checkC BSEGS ITB BOTH (nxt stA_1) AsanInit.LIMIT 1 (XNS BSEGS BOTH (nxt stA_1) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stA_1) (planB 1) [].
Definition hslB_1 : list (nat * acs) := snd colB_1.
Definition stB_1 : acs := hstate hslB_1 (stA_1) 11.
Definition shapeB_1 : shape := match fst colB_1 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan C at r = 1 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colC_1 : cres * list (nat * acs) := Eval vm_compute in
  checkC BSEGS ITC BOTH (nxt stB_1) AsanInit.LIMIT 1 (XNS BSEGS BOTH (nxt stB_1) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stB_1) (planC 1) [].
Definition hslC_1 : list (nat * acs) := snd colC_1.
Definition stC_1 : acs := hstate hslC_1 (stB_1) 12.
Definition shapeC_1 : shape := match fst colC_1 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan D at r = 1 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colD_1 : cres * list (nat * acs) := Eval vm_compute in
  checkC BSEGS ITD BOTH (nxt stC_1) AsanInit.LIMIT 1 (XNS BSEGS BOTH (nxt stC_1) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stC_1) (planD 1) [].
Definition hslD_1 : list (nat * acs) := snd colD_1.
Definition stD_1 : acs := hstate hslD_1 (stC_1) 0.
Definition shapeD_1 : shape := match fst colD_1 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan 2 at r = 1 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition col2_1 : cres * list (nat * acs) := Eval vm_compute in
  checkC BSEGS IT2 BOTH (nxt stD_1) AsanInit.LIMIT 1 (XNS BSEGS BOTH (nxt stD_1) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stD_1) (plan2 1) [].
Definition hsl2_1 : list (nat * acs) := snd col2_1.
Definition stS1_1 : acs := hstate hsl2_1 (stD_1) 1.
Definition stS2_1 : acs := hstate hsl2_1 (stD_1) 2.
Definition shape2_1 : shape := match fst col2_1 with COk s => s | CErr _ _ _ => SHole 999 end.
