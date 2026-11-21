(* AS/AsanStartupCertB = our text + 's own edits to theories/Common/AsanStartupCertB.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* certificate B at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan AsanStartupCert AsanRenum StartupHSAsan727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := mk_itab_ranges ASEGS startup_plan_ranges_A.
Lemma ITB_ok : itab_sound ASEGS ITB.
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
  check ASEGS ITB ASAN NXB AsanInit.LIMIT 0 (XNS ASEGS ASAN NXB AsanInit.LIMIT) XE0 XB0 (HS727B 0) KC0 BFUEL FUEL None (HS727A_10 0) (plan727 0 startup_plan_segA) = COk (startup_shapeB).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeB))). Time Qed.
Lemma startup_certB1 :
  check ASEGS ITB ASAN NXB AsanInit.LIMIT 1 (XNS ASEGS ASAN NXB AsanInit.LIMIT) XE0 XB0 (HS727B 1) KC0 BFUEL FUEL None (HS727A_10 1) (plan727 1 startup_plan_segA) = COk (startup_shapeB).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeB))). Time Qed.
Lemma startup_certB : forall b : bool,
  check ASEGS ITB ASAN NXB AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NXB AsanInit.LIMIT) XE0 XB0 (HS727B (rseq_z b)) KC0 BFUEL FUEL None (HS727A_10 (rseq_z b)) (plan727 (rseq_z b) startup_plan_segA) = COk (startup_shapeB).
Proof. ltac1:(intros [|]; [exact startup_certB1 | exact startup_certB0]). Qed.
