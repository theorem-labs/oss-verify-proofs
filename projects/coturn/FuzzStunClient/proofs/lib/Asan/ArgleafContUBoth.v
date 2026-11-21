(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the U leaf tree starts for each launch rseq layout from the collected template TUTmplRBoth.TU_both_r, with its plans renumbered by VarShift.psh, in place of the recorded certificates; the root trees of ArgleafRootBoth0.v and ArgleafRootBoth1.v decide it. *)
(* The U leaf tree starts from the per-r collected template [TUTmplRBoth.TU_both_r rsb]; its
   plans are renumbered by [VarShift.psh]; the root trees of ArgleafRootBoth0.v and
   ArgleafRootBoth1.v decide it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ArgleafPlansBoth ArgleafTmplBoth VarShift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition CC_u_both : class := [(QLook, 0, 0)].
Definition CONTUBoth : mtree := MSplit QL0 0 (MLeaf 0 (psh cont_u0b)) (MSplit QL0 63 (MLeaf 0 (psh cont_u5b)) (MSplit QL0 64 (MLeaf 0 (psh cont_u64b)) (MSplit QL0 66 (MLeaf 0 (psh cont_u65b)) (MSplit QL0 73 (MLeaf 0 (psh cont_u70b)) (MLeaf 0 (psh cont_u100b)))))).
