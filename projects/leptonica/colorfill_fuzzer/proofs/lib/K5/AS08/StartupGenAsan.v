(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the start-up check of K5/AS08/AsanStartupCert.v (BFUEL, KC0, FUEL, IT0, IT0_ok and its check call) moved here and made a function of the CONFIG_RSEQ value, the hand-off table and the join states. *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the ASan image's start-up [check] call at CONFIG_RSEQ value
   [r], as a function of the hole table and the join states ([StartupCoGen]).  The tables it is run
   over are computed per [r] in [StartupGenAsan0] and [StartupGenAsan1]; [AsanStartupCert] certifies
   them.  The recorded [js_0] / [js_3] are only the collector's seeds. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound StartupCoGen.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS08 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS08 Require Import AsanStartup StartupPlanAsan StartupJSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition startup_chk (r : Z) (H : nat -> option acs) (J : nat -> acs) : cres :=
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 H KC0 BFUEL FUEL None (asan_a_init r) (lsub J startup_plan).

(* the join seeds (the recorded states, replaced at the first refusal) and the round budget *)
Definition startup_seedJ : gtab := [(0%nat, js_0, false); (3%nat, js_3, false)].
Definition startup_rounds : nat := 24.
