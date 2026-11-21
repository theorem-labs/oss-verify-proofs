(* TRIAL NOT-OFFICIAL (a worker ruling (A), the Both start-up chain): AS/BothStartupCertB = our text + a worker's AS/AsanStartupCertB port, carried by a worker's port_by_analogy727_r5 () with --lit StartupHSAsan727=StartupHSBoth727; the old text is kept aside *)
(* a worker : certificate B at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth BothStartupCert AsanRenum StartupHSBoth727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_A.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXB : nat := nx727 207.
Lemma NXB_ge : (NX0 <= NXB)%nat. Proof. vm_compute. lia. Qed.
Definition startup_shapeB : shape := SHole 11.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certB0 :
  check BSEGS ITB BOTH NXB AsanInit.LIMIT 0 (XNS BSEGS BOTH NXB AsanInit.LIMIT) XE0 XB0 (HS727B 0) KC0 BFUEL FUEL None (HS727A_10 0) (plan727 0 startup_plan_both_segA) = COk (startup_shapeB).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeB))). Time Qed.
Lemma startup_certB1 :
  check BSEGS ITB BOTH NXB AsanInit.LIMIT 1 (XNS BSEGS BOTH NXB AsanInit.LIMIT) XE0 XB0 (HS727B 1) KC0 BFUEL FUEL None (HS727A_10 1) (plan727 1 startup_plan_both_segA) = COk (startup_shapeB).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeB))). Time Qed.
Lemma startup_certB : forall b : bool,
  check BSEGS ITB BOTH NXB AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NXB AsanInit.LIMIT) XE0 XB0 (HS727B (rseq_z b)) KC0 BFUEL FUEL None (HS727A_10 (rseq_z b)) (plan727 (rseq_z b) startup_plan_both_segA) = COk (startup_shapeB).
Proof. ltac1:(intros [|]; [exact startup_certB1 | exact startup_certB0]). Qed.
