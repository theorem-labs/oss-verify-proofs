(* SPDX-License-Identifier: MIT *)
(* The U family's hole template on image B, one per r (rsb = true: r = 1; rsb = false: r = 0): every main node
   that hands off to TU_both's slot (HT hole 0 of ArgleafRootBoth0 and ArgleafRootBoth1). Collected by
   [MainCol.mm_loop] over both arrivals against one shared table, seeded with [VarShift.ash TU_both], stored by
   [Eval vm_compute]; nothing here is trusted, every certificate that names a template re-checks it. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol TOTmplRBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition TU_NODES : list (class * plan) := [ (root_class 0, pfx_u1b); (root_class 1, pfx_u3b) ].
Definition tu_chk (rsb : bool) (i : nat) (HS : nat -> option acs) : cres :=
  let '(C, p) := nth i TU_NODES (root_class 0, pfx_u1b) in
  to_chk_with rsb C (pay_start (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) C) HS (psh p).
Definition TU_SEED : list (nat * acs) := [(0%nat, ash TU_both)].
Definition tu_run (rsb : bool) : mm_out := mm_loop (tu_chk rsb) (seq 0 2) 64%nat TU_SEED [] [].

Definition TU_RUN1 : mm_out := Eval vm_compute in tu_run true.
Definition TU_RUN0 : mm_out := Eval vm_compute in tu_run false.
Definition TU_B1 : acs := Eval vm_compute in to_hole TU_RUN1 0 (ash TU_both).
Definition TU_B0 : acs := Eval vm_compute in to_hole TU_RUN0 0 (ash TU_both).
Definition TU_both_r (rsb : bool) : acs := if rsb then TU_B1 else TU_B0.
