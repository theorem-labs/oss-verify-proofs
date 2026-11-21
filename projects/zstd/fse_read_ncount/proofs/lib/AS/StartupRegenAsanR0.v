(* SPDX-License-Identifier: MIT *)
(* Start-up data of the Asan build at LPS 727298f3, computed at CONFIG_RSEQ value r = 0.  Written by gen_startup_regen.py from the start-up
   probe's printout (docs/343-certificate-data-method.md, sections 2, 3 and 5).  No state here is recorded: every
   state, table, counter and shape is computed by vm_compute from [check], and each certificate re-checks it. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan AsanCertDefs PlanRegen StartupRegenAsanPlans.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* ---- plan A at r = 0 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colA_0 : cres * list (nat * acs) := Eval vm_compute in
  checkC ASEGS IT0 ASAN NX0 AsanInit.LIMIT 0 (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (asan_init 0) (planA 0) [].
Definition hslA_0 : list (nat * acs) := snd colA_0.
Definition stA_0 : acs := hstate hslA_0 (asan_init 0) 10.
Definition shapeA_0 : shape := match fst colA_0 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan B at r = 0 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colB_0 : cres * list (nat * acs) := Eval vm_compute in
  checkC ASEGS ITB ASAN (nxt stA_0) AsanInit.LIMIT 0 (XNS ASEGS ASAN (nxt stA_0) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stA_0) (planB 0) [].
Definition hslB_0 : list (nat * acs) := snd colB_0.
Definition stB_0 : acs := hstate hslB_0 (stA_0) 11.
Definition shapeB_0 : shape := match fst colB_0 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan C at r = 0 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colC_0 : cres * list (nat * acs) := Eval vm_compute in
  checkC ASEGS ITC ASAN (nxt stB_0) AsanInit.LIMIT 0 (XNS ASEGS ASAN (nxt stB_0) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stB_0) (planC 0) [].
Definition hslC_0 : list (nat * acs) := snd colC_0.
Definition stC_0 : acs := hstate hslC_0 (stB_0) 12.
Definition shapeC_0 : shape := match fst colC_0 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan D at r = 0 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition colD_0 : cres * list (nat * acs) := Eval vm_compute in
  checkC ASEGS ITD ASAN (nxt stC_0) AsanInit.LIMIT 0 (XNS ASEGS ASAN (nxt stC_0) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stC_0) (planD 0) [].
Definition hslD_0 : list (nat * acs) := snd colD_0.
Definition stD_0 : acs := hstate hslD_0 (stC_0) 0.
Definition shapeD_0 : shape := match fst colD_0 with COk s => s | CErr _ _ _ => SHole 999 end.

(* ---- plan 2 at r = 0 *)
(* one run of the plan (AsanPlan.checkC) collects its hand-off table (hstep_join) and its shape *)
Definition col2_0 : cres * list (nat * acs) := Eval vm_compute in
  checkC ASEGS IT2 ASAN (nxt stD_0) AsanInit.LIMIT 0 (XNS ASEGS ASAN (nxt stD_0) AsanInit.LIMIT) XEr XBr KC0 BFUEL hstep_join FUEL None (stD_0) (plan2 0) [].
Definition hsl2_0 : list (nat * acs) := snd col2_0.
Definition stS1_0 : acs := hstate hsl2_0 (stD_0) 1.
Definition stS2_0 : acs := hstate hsl2_0 (stD_0) 2.
Definition shape2_0 : shape := match fst col2_0 with COk s => s | CErr _ _ _ => SHole 999 end.
