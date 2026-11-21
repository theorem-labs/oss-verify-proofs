(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificate holds for each launch rseq layout (rsb) over that layout's shadow table and computed states, and its segment list and instruction table moved to StartupHSAsan.v. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StartupHooks StartupPlanAsan StartupHSAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* startup_asan_SEGS / startup_asan_IT: StartupHSAsan.v, where the start-up collector runs this same check. *)
Definition startup_asan_shape : shape := SCase (EVar 6) 10 (SCase (EVar 5) 524277 (SHole 0) (SHole 0)) (SCase (EVar 5) 524277 (SHole 0) (SHole 0)).

Lemma startup_asan_cert {rsb : bool} :
  check startup_asan_SEGS startup_asan_IT (ASAN_at (rseq_z rsb)) NX0 target_alloc_limit XN0 XE0 XB0 (HS_asan (rseq_z rsb)) 0%nat 400000%nat 3000%nat None (asan_init (rseq_z rsb)) (startup_plan (rseq_z rsb)) = COk startup_asan_shape.
Proof. destruct rsb; vm_cast_no_check (eq_refl (COk startup_asan_shape)). Qed.
