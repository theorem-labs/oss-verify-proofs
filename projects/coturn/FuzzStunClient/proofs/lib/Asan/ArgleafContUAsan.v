(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the U leaf tree starts for each launch rseq layout from the collected template TUTmplRAsan.TU_asan_r, with its plans renumbered by VarShift.psh, in place of the recorded certificates; the root trees of ArgleafRootAsan0.v and ArgleafRootAsan1.v decide it. *)
(* The U leaf tree starts from the per-r collected template [TUTmplRAsan.TU_asan_r rsb]; its
   plans are renumbered by [VarShift.psh]; the root trees of ArgleafRootAsan0.v and
   ArgleafRootAsan1.v decide it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ArgleafPlansAsan ArgleafTmplAsan VarShift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition CC_u_asan : class := [(QLook, 0, 0)].
Definition CONTUAsan : mtree := MSplit QL0 0 (MLeaf 0 (psh cont_u0a)) (MSplit QL0 63 (MLeaf 0 (psh cont_u5a)) (MSplit QL0 64 (MLeaf 0 (psh cont_u64a)) (MSplit QL0 66 (MLeaf 0 (psh cont_u65a)) (MSplit QL0 73 (MLeaf 0 (psh cont_u70a)) (MLeaf 0 (psh cont_u100a)))))).
