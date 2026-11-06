(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StartupHooks StartupHSAsan PostPlanAsan StartupHSMainAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition post_asan_SEGS : list Segment := Asan.M.loaded_segments.
(* [comment removed for export] *)
Definition post_asan_IT : itab := mk_itab_ranges post_asan_SEGS post_plan_ranges.
Definition post_asan_shape : shape := SHole 0.

Lemma post_asan_cert :
  check post_asan_SEGS post_asan_IT ASAN NX0 target_alloc_limit XNdA XE0 XB0 HS_mainA 0%nat 400000%nat 3000%nat None HS_asan_0 post_plan = COk post_asan_shape.
Proof. vm_cast_no_check (eq_refl (COk post_asan_shape)). Qed.
