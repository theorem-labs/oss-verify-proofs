(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag: the start-up certificate at CONFIG_RSEQ = 0, startup_cert_0, taken from K5/AS23/AsanStartupCert.v so that the two certificates are checked in parallel). *)
(* LPS 75d69e00: the start-up certificate at CONFIG_RSEQ = 0 ([AsanStartupCert] has the one over the run's flag). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound StartupCoGen.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanStartup StartupGenAsan StartupHSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_0 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan false) KC0 BFUEL FUEL None (asan_a_init 0) (startup_plan_r false)
  = COk (startup_shape false).
Proof. cert_refl constr:(COk (startup_shape false)). Qed.
