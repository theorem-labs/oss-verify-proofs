(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StartupHooks StartupPlanAsan StartupHSAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_asan_SEGS : list Segment := Asan.M.loaded_segments.
(* [comment removed for export] *)
Definition startup_asan_IT : itab := mk_itab_ranges startup_asan_SEGS startup_plan_ranges.
Definition startup_asan_shape : shape := SCase (EVar 6) 10 (SCase (EVar 5) 524277 (SHole 0) (SHole 0)) (SCase (EVar 5) 524277 (SHole 0) (SHole 0)).

Lemma startup_asan_cert :
  check startup_asan_SEGS startup_asan_IT ASAN NX0 target_alloc_limit XN0 XE0 XB0 HS_asan 0%nat 400000%nat 3000%nat None asan_init startup_plan = COk startup_asan_shape.
Proof. vm_cast_no_check (eq_refl (COk startup_asan_shape)). Qed.
