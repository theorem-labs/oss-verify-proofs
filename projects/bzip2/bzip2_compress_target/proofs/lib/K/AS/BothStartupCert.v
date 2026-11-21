(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up certificate at both values of the CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanTablesB AsanPlanImagesB AsanInit AsanStartup StartupPlanBoth StartupHSBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* LPS 75d69e00 (#38): see AsanStartupCert.v.  [check]'s [rz] slot sits after
   [LIMIT] and this file passed [XN0] into it.  The shape is the one
   [K/A/TopA.v:62-68] and [K/A/TopA_start.v:78-84] require; one certificate per
   value of the flag, joined, with the flag left free. *)
Definition startup_shape (r : Z) : shape := (SHole 0).

Lemma startup_cert0 :
  check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT 0 XN0 XE0 XB0 (HS_both 0) KC0 BFUEL FUEL None
        (asan_b_init 0) (startup_plan 0) = COk (startup_shape 0).
Proof. cert_refl constr:(COk (startup_shape 0)). Qed.

Lemma startup_cert1 :
  check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT 1 XN0 XE0 XB0 (HS_both 1) KC0 BFUEL FUEL None
        (asan_b_init 1) (startup_plan 1) = COk (startup_shape 1).
Proof. cert_refl constr:(COk (startup_shape 1)). Qed.

(* See AsanStartupCert.v for the measurement: the Ltac2 import above puts the file
   in Ltac2 proof mode, where the Ltac1 goal dispatch below does not parse, and the
   unit's own idiom (Bz/AsanKit.v:14, Bz/LinSplit.v:9) is to restore the mode. *)
Set Default Proof Mode "Classic".

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both (rseq_z b)) KC0 BFUEL FUEL None
        (asan_b_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
Proof. intros [|]; [exact startup_cert1 | exact startup_cert0]. Qed.
