(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag; the recorded proof of startup_cert replaced by plain proof, from the per-value certificates startup_cert_1 and startup_cert_0 in AsanStartupCert1.v and AsanStartupCert0.v). *)
(* LPS 75d69e00: ONE CERTIFICATE PER CONFIG_RSEQ VALUE.  [kb_rseq]
   is free under [Run.valid_input], so the start-up is checked from [asan_a_init 0] and from
   [asan_a_init 1], each over the join and hole tables computed from that state ([StartupHSAsan],
   from [StartupGenAsan0] / [StartupGenAsan1]).  [b] below is the run's flag; [rseq_z b] its 0/1. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound StartupCoGen.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanStartup StartupGenAsan StartupHSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import AsanStartupCert1 AsanStartupCert0.

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan b) KC0 BFUEL FUEL None (asan_a_init (rseq_z b)) (startup_plan_r b)
  = COk (startup_shape b).
(* the file is in Ltac2 mode ([From Ltac2 Require Import Ltac2] above), so the case split is Ltac1 quoted *)
Proof. ltac1:(intros [|]; [exact startup_cert_1 | exact startup_cert_0]). Qed.
