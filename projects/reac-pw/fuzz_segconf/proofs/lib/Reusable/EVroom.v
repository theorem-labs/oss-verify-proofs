(* copied from proofs/cgif/cgif_file_fuzzer/lib/EVroom.v @ 86aa4177b94 (c-asan, cold/c-asan-nmax-param: F1 / F2 + NMAX-PARAM + EV_MAX value-independence; installs in c5 ~18:30Z), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The one fact about the VALUE of EV_MAX that the Allocate / Deallocate walk files use, image-free.

   YG06.mapped_user_bound bounds the mapped user part of a region by kUserMapSize * EV_MAX.  A walk step that places
   a chunk or a batch object of that part inside the region's 2^32 bytes needs that bound below the region's free
   array, at kFreeArrayOffset.  The step uses [ev_user_room] and does not unfold EV_MAX, so the step holds at every
   EV_MAX that satisfies [ev_user_room]: kUserMapSize * EV_MAX <= kFreeArrayOffset means EV_MAX <= 14336.
   cgif_file's EV_MAX is 8192 (kUserMapSize * EV_MAX = 2^31); fuzz_state's is 11776 (3087007744). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00.
Open Scope Z_scope.

Lemma ev_user_room : 0 < EV_MAX /\ kUserMapSize * EV_MAX <= kFreeArrayOffset.
Proof. unfold EV_MAX, kUserMapSize, kFreeArrayOffset. lia. Qed.
