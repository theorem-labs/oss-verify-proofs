(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up certificate at both values of the CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanTablesA AsanPlanImages AsanInit AsanStartup StartupPlanAsan StartupHSAsan.
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

(* LPS 75d69e00 (#38).  [check] is discharged as
     check segs IT A nx0 LIMIT rz XN XE XB HS KC bfuel fuel lc cs p
   ([AsanPlan.v:23-31]): the run's CONFIG_RSEQ flag sits after [LIMIT], and
   [asan_a_init] takes the same flag ([AsanTablesA.v:29]).  This file still passed
   [XN0] into the [rz] slot, which is the error the farm prints:
     The term "XN0" has type "nat -> list expr -> acs -> option acs"
     while it is expected to have type "Z".
   The shape the consumers require is not invented here, it is read off
   [K/A/TopA.v:150-154] and [K/A/TopA_start.v:226-230].  Per [AsanPlan.v:30-31] a
   certificate is checked AT ONE LITERAL VALUE of the flag, so it is stated once
   per value and joined; the flag itself stays FREE -- both values are served and
   [kb_rseq] is not pinned. *)
Definition startup_shape (r : Z) : shape := (SHole 0).

Lemma startup_cert0 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT 0 XN0 XE0 XB0 (HS_asan 0) KC0 BFUEL FUEL None
        (asan_a_init 0) (startup_plan 0) = COk (startup_shape 0).
Proof. cert_refl constr:(COk (startup_shape 0)). Qed.

Lemma startup_cert1 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT 1 XN0 XE0 XB0 (HS_asan 1) KC0 BFUEL FUEL None
        (asan_a_init 1) (startup_plan 1) = COk (startup_shape 1).
Proof. cert_refl constr:(COk (startup_shape 1)). Qed.

(* The [From Ltac2 Require Import Ltac2 ...] above puts this file in Ltac2 proof
   mode, where [ t1 | t2 ] is a LIST LITERAL, so the Ltac1 goal dispatch below is a
   syntax error ("';' or ']' expected (in [list_literal])" at the bar).  The port
   added the Ltac2 import for [cert_refl] and did not restore the mode; the defect
   stayed invisible because [startup_cert0] above refused first and Rocq never
   parsed this sentence.  The unit's own idiom is to restore the mode explicitly --
   Bz/AsanKit.v:14 and Bz/LinSplit.v:9 both follow the same Ltac2 import with this
   line and then use the dispatch freely.  Restoring it HERE, after the two Ltac2
   proofs above, leaves them byte-identical. *)
Set Default Proof Mode "Classic".

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
        (asan_a_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
Proof. intros [|]; [exact startup_cert1 | exact startup_cert0]. Qed.
