(* SPDX-License-Identifier: MIT *)
(* The U family's hole template on image A, one per r (rsb = true: r = 1; rsb = false: r = 0): every main node
   that hands off to TU_asan's slot (HT hole 0 of ArgleafRootAsan0 and ArgleafRootAsan1). Collected by
   [MainCol.mm_loop] over both arrivals against one shared table, seeded with [VarShift.ash TU_asan], stored by
   [Eval vm_compute]; nothing here is trusted, every certificate that names a template re-checks it. Both r are
   collected; [TU_asan_r] picks [TU_A1] at r = 1 and [TU_A0] at r = 0, and the r = 0 certificates
   ([ArgleafRootAsan0.TREEAsan0_ok0], [ArgleafRootAsan1.TREEAsan1_ok0]) re-check [TU_A0]. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol TOTmplRAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition TUA_NODES : list (class * plan) := [ (root_class 0, pfx_u1a); (root_class 1, pfx_u3a) ].
Definition tua_chk (rsb : bool) (i : nat) (HS : nat -> option acs) : cres :=
  let '(C, p) := nth i TUA_NODES (root_class 0, pfx_u1a) in
  ta_chk_with rsb C (pay_start (HSA rsb (HS_mainA (rseq_z rsb)) 0%nat) C) HS (psh p).
Definition TUA_SEED : list (nat * acs) := [(0%nat, ash TU_asan)].
Definition tua_run (rsb : bool) : mm_out := mm_loop (tua_chk rsb) (seq 0 2) 64%nat TUA_SEED [] [].

Definition TUA_RUN1 : mm_out := Eval vm_compute in tua_run true.
Definition TUA_RUN0 : mm_out := Eval vm_compute in tua_run false.
Definition TU_A1 : acs := Eval vm_compute in ta_hole TUA_RUN1 0 (ash TU_asan).
Definition TU_A0 : acs := Eval vm_compute in ta_hole TUA_RUN0 0 (ash TU_asan).
Definition TU_asan_r (rsb : bool) : acs := if rsb then TU_A1 else TU_A0.
