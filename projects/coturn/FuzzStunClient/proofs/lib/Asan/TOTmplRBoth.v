(* SPDX-License-Identifier: MIT *)
(* The TO family's hole templates on image B, one per r (rsb = true: r = 1; rsb = false: r = 0).
   The family is every main node that hands off to hole 3 (TO_both's slot): ArgR2Both's node, ArgR3Both's four,
   ArgR4Both's (which also hands off to hole 26, REP4b_s's slot) and Main5Both's root (which also hands off to
   HT hole 1, HO_s's slot). The templates are collected by [MainCol.mm_loop] over ALL seven arrivals against one
   shared table, seeded with the released templates shifted by [VarShift.ash], and stored by [Eval vm_compute]:
   a template is only a definition, so nothing here is trusted; every certificate that names one re-checks it.
   One template cannot serve both r (the arrivals at r = 0 and r = 1 differ syntactically), hence two. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ArgR234PlansBoth ArgR4RepBoth W0BPlans W0BStates1.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* node i's check under hole table HS: the certificate's own check, plan renumbered by [psh] *)
Definition to_chk_with (rsb : bool) (C : class) (cs : acs) (HS : nat -> option acs) (p : plan) : cres :=
  check BSEGS IT_both (BOTH_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNM rsb (iotab_of C)) (XEm BSEGS (BOTH_at (rseq_z rsb)) NX0)
        (XBm BSEGS (BOTH_at (rseq_z rsb)) NX0 (iotab_of C)) HS 0%nat 400000%nat 5000%nat None cs p.

Definition TO_NODES : list (class * plan) :=
  [ (root_class 2, pfx_o2b3);
    ((root_class 3) ++ [(QL1, QMIN, 0)], pfx_o3b3);
    (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)], pfx_o3b3);
    ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)], pfx_o3b3);
    ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)], pfx_o3b3);
    (root_class 4, argdb1otr);
    (root_class 5, root_opent) ].
Definition to_chk (rsb : bool) (i : nat) (HS : nat -> option acs) : cres :=
  let '(C, p) := nth i TO_NODES (root_class 2, pfx_o2b3) in
  to_chk_with rsb C (pay_start (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) C) HS (psh p).
Definition TO_SEED : list (nat * acs) := [(3%nat, ash TO_both); (26%nat, ash REP4b_s); (1%nat, ash HO_s)].
Definition to_run (rsb : bool) : mm_out := mm_loop (to_chk rsb) (seq 0 7) 64%nat TO_SEED [] [].
Definition to_hole (o : mm_out) (h : nat) (d : acs) : acs := match tlook (mm_holes o) h with Some t => t | None => d end.

Definition TO_RUN1 : mm_out := Eval vm_compute in to_run true.
Definition TO_RUN0 : mm_out := Eval vm_compute in to_run false.

Definition TO_B1 : acs := Eval vm_compute in to_hole TO_RUN1 3 (ash TO_both).
Definition TO_B0 : acs := Eval vm_compute in to_hole TO_RUN0 3 (ash TO_both).
Definition REP4b_B1 : acs := Eval vm_compute in to_hole TO_RUN1 26 (ash REP4b_s).
Definition REP4b_B0 : acs := Eval vm_compute in to_hole TO_RUN0 26 (ash REP4b_s).
Definition HO_B1 : acs := Eval vm_compute in to_hole TO_RUN1 1 (ash HO_s).
Definition HO_B0 : acs := Eval vm_compute in to_hole TO_RUN0 1 (ash HO_s).

Definition TO_both_r (rsb : bool) : acs := if rsb then TO_B1 else TO_B0.
Definition REP4b_r (rsb : bool) : acs := if rsb then REP4b_B1 else REP4b_B0.
Definition HO_r (rsb : bool) : acs := if rsb then HO_B1 else HO_B0.
