(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan ArgleafPlansAsan ArgleafTmplAsan ArgleafContOAllAsan ContOAll5Asan ArgR234PlansAsan ArgR4RepAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HR_1 : list (nat * (shape * acs)) := [(3%nat, (cont_o_all_asan_s, TO_asan)); (26%nat, (SNil, REP4_s))].
Definition s_4 : shape := SAlt2 (SHole 3) (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10]] (SExit 2)) (SAlt2 (SHole 26) (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2)) (SHole 26)))).
Definition s_11 : shape := SNil.
