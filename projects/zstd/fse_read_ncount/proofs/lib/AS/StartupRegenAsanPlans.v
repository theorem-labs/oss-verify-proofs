(* SPDX-License-Identifier: MIT *)
(* Start-up data of the Asan build at LPS 727298f3, the plans renumbered by the probe-read maps.  Written by gen_startup_regen.py from the start-up
   probe's printout (docs/343-certificate-data-method.md, sections 2, 3 and 5).  No state here is recorded: every
   state, table, counter and shape is computed by vm_compute from [check], and each certificate re-checks it. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan AsanCertDefs PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* the no-op extension tables of the start-up checks (AsanStartup.XE0 / XB0, the same bodies), defined here so that
   these files and the certificates do not wait on the soundness chain AsanStartup imports *)
Definition XEr (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XBr (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

(* ---- plan A (startup_plan): breakpoints read from the start-up probe's printout (the probe text and its output are in the pull request's probe commits), its line
   ("MAPPT asan A r0", [(13, 17)]%nat) *)
Definition bpA : list (nat * nat) := [(13, 17)]%nat.
Definition planA (r : Z) : plan := psh (mapf bpA) startup_plan.

(* ---- plan B (startup_plan_segA): breakpoints read from the start-up probe's printout (the probe text and its output are in the pull request's probe commits), its line
   ("MAPPT asan segA r0", [(13, 17); (207, 211); (310, 316)]%nat) *)
Definition bpB : list (nat * nat) := [(13, 17); (207, 211); (310, 316)]%nat.
Definition planB (r : Z) : plan := psh (mapf bpB) startup_plan_segA.

(* ---- plan C (startup_plan_segB): breakpoints read from the start-up probe's printout (the probe text and its output are in the pull request's probe commits), its line
   ("MAPPT asan segB r0", [(13, 17); (207, 211); (310, 316); (344, 350)]%nat) *)
Definition bpC : list (nat * nat) := [(13, 17); (207, 211); (310, 316); (344, 350)]%nat.
(* its AT_RANDOM split chain, per CONFIG_RSEQ value r: the top of e_atr8's range and the literal of
   registers 13 and 14 in each of the 7 top values' branches, read from the start-up probe's printout, its lines
   ("SEGBCHAIN asan r0", 17592186044357, [(Some 17594333495289, Some 17594333495289, Some 17594333495289, Some 17594333495289); (Some 17594333495290, Some 17594333495290, Some 17594333495290, Some 17594333495290); (Some 17594333495291, Some 17594333495291, Some 17594333495291, Some 17594333495291); (Some 17594333495292, Some 17594333495292, Some 17594333495292, Some 17594333495292); (Some 17594333495293, Some 17594333495293, Some 17594333495293, Some 17594333495293); (Some 17594333495294, Some 17594333495294, Some 17594333495294, Some 17594333495294); (Some 17594333495295, Some 17594333495295, Some 17594333495295, Some 17594333495295)])
   ("SEGBCHAIN asan r1", 17592186044353, [(Some 17594333495289, Some 17594333495289, Some 17594333495289, Some 17594333495289); (Some 17594333495290, Some 17594333495290, Some 17594333495290, Some 17594333495290); (Some 17594333495291, Some 17594333495291, Some 17594333495291, Some 17594333495291); (Some 17594333495292, Some 17594333495292, Some 17594333495292, Some 17594333495292); (Some 17594333495293, Some 17594333495293, Some 17594333495293, Some 17594333495293); (Some 17594333495294, Some 17594333495294, Some 17594333495294, Some 17594333495294); (Some 17594333495295, Some 17594333495295, Some 17594333495295, Some 17594333495295)])
   The recorded node [PSplit e_atr8 17592186044384 ...] is rebuilt by [top_chain] (PlanRegen.v). *)
Definition chainC_top_0 : Z := 17592186044357.
Definition chainC_lits_0 : list (Z * Z) := [(17594333495289, 17594333495289); (17594333495290, 17594333495290); (17594333495291, 17594333495291); (17594333495292, 17594333495292); (17594333495293, 17594333495293); (17594333495294, 17594333495294); (17594333495295, 17594333495295)].
Definition chainC_top_1 : Z := 17592186044353.
Definition chainC_lits_1 : list (Z * Z) := [(17594333495289, 17594333495289); (17594333495290, 17594333495290); (17594333495291, 17594333495291); (17594333495292, 17594333495292); (17594333495293, 17594333495293); (17594333495294, 17594333495294); (17594333495295, 17594333495295)].
Definition chainC_top (r : Z) : Z := if Z.eqb r 1 then chainC_top_1 else chainC_top_0.
Definition chainC_lits (r : Z) : list (Z * Z) := if Z.eqb r 1 then chainC_lits_1 else chainC_lits_0.
Definition chainC_generic : plan := psh (mapf bpC) startup_plan_qc2.
Definition chainC (r : Z) : plan := top_chain e_atr8 (chainC_top r) chainC_generic
  (map (fun l => respell2 13 14 (fst l) (snd l) chainC_generic) (chainC_lits r)).
Definition planC (r : Z) : plan := pmapH (swap_split e_atr8 17592186044384 (chainC r)) (psh (mapf bpC) startup_plan_segB).

(* ---- plan D (startup_plan_segC): breakpoints read from the start-up probe's printout (the probe text and its output are in the pull request's probe commits), its line
   ("MAPPT asan segC r0", [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400)]%nat) *)
Definition bpD : list (nat * nat) := [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400)]%nat.
Definition planD (r : Z) : plan := psh (mapf bpD) startup_plan_segC.

(* ---- plan 2 (startup2_plan): breakpoints read from the start-up probe's printout (the probe text and its output are in the pull request's probe commits), its line
   ("MAPPT asan s2 r0", [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400); (453, 459)]%nat) *)
Definition bp2 : list (nat * nat) := [(13, 17); (207, 211); (310, 316); (344, 350); (394, 400); (453, 459)]%nat.
Definition plan2 (r : Z) : plan := psh (mapf bp2) startup2_plan.
