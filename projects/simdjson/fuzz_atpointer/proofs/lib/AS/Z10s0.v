(* SPDX-License-Identifier: MIT *)
(* Image B's start-up join and hand-off states at CONFIG_RSEQ value 0, computed from the run by
   [PlanRegen.regen] ([Z10s.REGEN_B]); one file per flag value, so that the two compile in
   parallel.  [Z7d]'s certificate checks the plan with them again; a wrong state can only make
   it red. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y PlanRegen Z10s.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition RG_B0 : list (nat * acs) * list (nat * acs) * cres := Eval vm_compute in REGEN_B 0.
