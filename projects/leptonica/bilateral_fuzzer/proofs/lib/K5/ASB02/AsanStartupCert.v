(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one start-up certificate per CONFIG_RSEQ value, each over the join and hole tables computed in the build from that value's start state; the fuel constants and IT0 moved to StartupGenAsan.v; the recorded (KReplay) proof replaced by a checked computation). *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): ONE CERTIFICATE PER CONFIG_RSEQ VALUE.  [kb_rseq]
   is free under [Run.valid_input], so the start-up is checked from [asan_a_init 0] and from
   [asan_a_init 1], each over the join and hole tables computed from that state ([StartupHSAsan],
   from [StartupGenAsan0] / [StartupGenAsan1]).  [b] below is the run's flag; [rseq_z b] its 0/1. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound StartupCoGen.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanStartup StartupGenAsan StartupHSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_1 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan true) KC0 BFUEL FUEL None (asan_a_init 1) (startup_plan_r true)
  = COk (startup_shape true).
Proof. cert_refl constr:(COk (startup_shape true)). Qed.

Lemma startup_cert_0 :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan false) KC0 BFUEL FUEL None (asan_a_init 0) (startup_plan_r false)
  = COk (startup_shape false).
Proof. cert_refl constr:(COk (startup_shape false)). Qed.

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan b) KC0 BFUEL FUEL None (asan_a_init (rseq_z b)) (startup_plan_r b)
  = COk (startup_shape b).
(* a case split, so that each case's type meets its certificate's by [rseq_z]'s value alone: an [exact] of a
   [match] without a return clause made the elaborator unfold [check] (over an hour) *)
Proof. ltac1:(intros [|]; [exact startup_cert_1 | exact startup_cert_0]). Qed.
