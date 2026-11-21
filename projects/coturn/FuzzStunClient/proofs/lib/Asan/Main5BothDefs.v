(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the hole tables of t_53 and t_49 take the launch rseq layout and hold the collected templates (TOTmplRBoth, M5TmplRBoth), and the r-free tables and recorded node shapes are removed. *)
(* The hole tables of the root t_53 and of t_49 take r and hold the per-r collected templates
   (TOTmplRBoth, M5TmplRBoth); t_48's subtree carries its own collected tables (TreeColB, Main5Both.v), so its
   tables and hole shapes are not here. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth W0BLib W0BStates1 W0BStates2 W0BPlans ArgleafTmplBoth ArgleafContOAllBoth TOTmplRBoth M5TmplRBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_1 (rsb : bool) : list (nat * (nat * acs)) := [(1%nat, (1%nat, HO_r rsb))].
Definition HR_2 (rsb : bool) : list (nat * (shape * acs)) := [(3%nat, (cont_o_all_both_s, TO_both_r rsb))].
Definition HR_4 (rsb : bool) : list (nat * (shape * acs)) := [(26%nat, (SNil, REP_r rsb))].
Definition HT_9 (rsb : bool) : list (nat * (nat * acs)) := [(12%nat, (1%nat, HG1_r rsb))].
