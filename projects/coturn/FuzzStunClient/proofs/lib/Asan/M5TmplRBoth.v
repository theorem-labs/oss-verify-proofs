(* SPDX-License-Identifier: MIT *)
(* Main5Both's layer-1 family on image B, one set per r (rsb = true: r = 1; rsb = false: r = 0). Main5's root
   (TO family, TOTmplRBoth) hands HT hole 1 to HO; from HO, t_48 (w0r, class m5_C48) and t_49 (w1r, class m5_C49)
   hand off to holes 10 AR0, 26 REP and 12 HG1. The layer is one [MainCol.mmj_loop] run: holes shared across the
   two nodes, join states collected per plan. Templates, join states and the join-rewritten plans are computed by
   [Eval vm_compute] at each compile; nothing here is trusted, every certificate that names one re-checks it.
   Below this layer the trees are collected node by node by TreeColB.tcol: t_48's subtree from HO (Main5Both.v;
   the layer-wise collection of its layer-2 nodes does not converge) and HG1's
   subtree (TPH1, the W1 tree) from [HG1_r rsb] (Main5W1Both.v). *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth W0BLib W0BStates1 W0BStates2 W0BPlans.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import VarShift MainCol TOTmplRBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition m5_C5 : class := root_class 5.
Definition m5_C48 : class := m5_C5 ++ [(QFlen, QMIN, 65535)].
Definition m5_C49 : class := m5_C5 ++ [(QFlen, 65535 + 1, QMAX)].
Definition m5_CLA : class := [(QLook, 4, 4); (QArgc, 2, 2)].

(* plan ids: joins are keyed by plan *)
Definition M5PL : list plan :=
  [ w0r; w1r; leaf_s; leaf_v; p0z7; p0lt6; p0eq6; p0gt6; p0sec6;                 (*  0 ..  8 *)
    t_d30lt; t_d31lt; tsl; td30eq; td31eq; tse6; td30gt; td31gt; tn_sec; tssec; (*  9 .. 18 *)
    rep26 ].                                                                      (* 19       *)
Definition m5p (k : nat) : plan := pshj (nth k M5PL PExit).   (* join states and invariants renumbered too *)

(* a node: class, start template, plan id *)
Definition m5chk (rsb : bool) (N : list (class * acs * nat)) (i : nat) (HS : nat -> option acs) (f : plan -> plan) : cres :=
  let '(C, st, k) := nth i N (m5_C5, HO_B1, 0%nat) in to_chk_with rsb C (pay_start st C) HS (f (m5p k)).
Definition m5pid (N : list (class * acs * nat)) (i : nat) : nat := let '(_, _, k) := nth i N (m5_C5, HO_B1, 0%nat) in k.
Definition m5run (rsb : bool) (N : list (class * acs * nat)) (seed : list (nat * acs)) : mmj_out :=
  mmj_loop (m5chk rsb N) (m5pid N) (seq 0 (List.length N)) 64%nat seed [] [] [] [].
Definition m5hole (o : mmj_out) (h : nat) (d : acs) : acs := match tlook (mmj_holes o) h with Some t => t | None => d end.

(* ---- layer 1, from HO ---- *)
Definition m5_N1 (rsb : bool) : list (class * acs * nat) := [(m5_C48, HO_r rsb, 0%nat); (m5_C49, HO_r rsb, 1%nat)].
Definition m5_SEED1 : list (nat * acs) := [(10%nat, ash AR0_s); (26%nat, ash REP_s); (12%nat, ash HG1_s)].
Definition M5L1_1 : mmj_out := Eval vm_compute in m5run true (m5_N1 true) m5_SEED1.
Definition M5L1_0 : mmj_out := Eval vm_compute in m5run false (m5_N1 false) m5_SEED1.
Definition REP_B1 : acs := Eval vm_compute in m5hole M5L1_1 26 (ash REP_s).
Definition REP_B0 : acs := Eval vm_compute in m5hole M5L1_0 26 (ash REP_s).
Definition HG1_B1 : acs := Eval vm_compute in m5hole M5L1_1 12 (ash HG1_s).
Definition HG1_B0 : acs := Eval vm_compute in m5hole M5L1_0 12 (ash HG1_s).
Definition REP_r (rsb : bool) : acs := if rsb then REP_B1 else REP_B0.
Definition HG1_r (rsb : bool) : acs := if rsb then HG1_B1 else HG1_B0.

(* ---- the plans, each with its collected join states read back ---- *)
Definition M5J (rsb : bool) : list (nat * acs) :=
  if rsb then mmj_joins M5L1_1 else mmj_joins M5L1_0.
Definition M5P_B1 : list plan := Eval vm_compute in map (fun k => pjs (jof (M5J true) k) (m5p k)) (seq 0 20).
Definition M5P_B0 : list plan := Eval vm_compute in map (fun k => pjs (jof (M5J false) k) (m5p k)) (seq 0 20).
Definition M5P (rsb : bool) (k : nat) : plan := nth k (if rsb then M5P_B1 else M5P_B0) PExit.
