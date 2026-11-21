(* SPDX-License-Identifier: MIT *)
(* The TO family's hole templates on image A, per r (rsb = true: r = 1; rsb = false: r = 0).
   The family is every main node that hands off to hole 3 (TO_asan's slot): ArgR2Asan's node, ArgR3Asan's four,
   ArgR4Asan's (which also hands off to hole 26, REP4_s's slot) and Main5Asan's root (which also hands off to
   HT hole 1, HO_s's slot). The templates are collected by [MainCol.mm_loop] over ALL seven arrivals against one
   shared table, seeded with the released templates shifted by [VarShift.ash], and stored by [Eval vm_compute]:
   a template is only a definition, so nothing here is trusted; every certificate that names one re-checks it.
   Both r are collected. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContOAllAsan ArgR234PlansAsan ArgR4RepAsan W0Plans W0States1.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* node i's check under hole table HS: the certificate's own check, plan renumbered by [psh] *)
Definition ta_chk_with (rsb : bool) (C : class) (cs : acs) (HS : nat -> option acs) (p : plan) : cres :=
  check ASEGS IT_asan (ASAN_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNM rsb (iotab_of C)) (XEm ASEGS (ASAN_at (rseq_z rsb)) NX0)
        (XBm ASEGS (ASAN_at (rseq_z rsb)) NX0 (iotab_of C)) HS 0%nat 400000%nat 5000%nat None cs p.

Definition TOA_NODES : list (class * plan) :=
  [ (root_class 2, pfx_o2a3);
    ((root_class 3) ++ [(QL1, QMIN, 0)], pfx_o3a3);
    (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)], pfx_o3a3);
    ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)], pfx_o3a3);
    ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)], pfx_o3a3);
    (root_class 4, argda1otr);
    (root_class 5, root_opent) ].
Definition ta_chk (rsb : bool) (i : nat) (HS : nat -> option acs) : cres :=
  let '(C, p) := nth i TOA_NODES (root_class 2, pfx_o2a3) in
  ta_chk_with rsb C (pay_start (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) C) HS (psh p).
Definition TOA_SEED : list (nat * acs) := [(3%nat, ash TO_asan); (26%nat, ash REP4_s); (1%nat, ash HO_s)].
Definition ta_run (rsb : bool) : mm_out := mm_loop (ta_chk rsb) (seq 0 7) 64%nat TOA_SEED [] [].
Definition ta_hole (o : mm_out) (h : nat) (d : acs) : acs := match tlook (mm_holes o) h with Some t => t | None => d end.

Definition TOA_RUN1 : mm_out := Eval vm_compute in ta_run true.
Definition TOA_RUN0 : mm_out := Eval vm_compute in ta_run false.

Definition TO_A1 : acs := Eval vm_compute in ta_hole TOA_RUN1 3 (ash TO_asan).
Definition REP4_A1 : acs := Eval vm_compute in ta_hole TOA_RUN1 26 (ash REP4_s).
Definition HO_A1 : acs := Eval vm_compute in ta_hole TOA_RUN1 1 (ash HO_s).
Definition TO_A0 : acs := Eval vm_compute in ta_hole TOA_RUN0 3 (ash TO_asan).
Definition REP4_A0 : acs := Eval vm_compute in ta_hole TOA_RUN0 26 (ash REP4_s).
Definition HO_A0 : acs := Eval vm_compute in ta_hole TOA_RUN0 1 (ash HO_s).

Definition TO_asan_r (rsb : bool) : acs := if rsb then TO_A1 else TO_A0.
Definition REP4_r (rsb : bool) : acs := if rsb then REP4_A1 else REP4_A0.
Definition HO_r (rsb : bool) : acs := if rsb then HO_A1 else HO_A0.
