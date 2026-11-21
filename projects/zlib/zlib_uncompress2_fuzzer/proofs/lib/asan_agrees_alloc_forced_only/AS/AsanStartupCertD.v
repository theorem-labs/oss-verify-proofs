(* AS/AsanStartupCertD = our text + 's own edits to theories/Common/AsanStartupCertD.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* certificate D at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan AsanStartupCert AsanRenum StartupHSAsan727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITD : itab := mk_itab_ranges ASEGS startup_plan_ranges_C.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXD : nat := nx727 394.
Lemma NXD_ge : (NX0 <= NXD)%nat. Proof. vm_compute. lia. Qed.
Definition startup_shapeD : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certD0 :
  check ASEGS ITD ASAN NXD AsanInit.LIMIT 0 (XNS ASEGS ASAN NXD AsanInit.LIMIT) XE0 XB0 (HS727D 0) KC0 BFUEL FUEL None (HS727C_12 0) (plan727 0 startup_plan_segC) = COk (startup_shapeD).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeD))). Time Qed.
Lemma startup_certD1 :
  check ASEGS ITD ASAN NXD AsanInit.LIMIT 1 (XNS ASEGS ASAN NXD AsanInit.LIMIT) XE0 XB0 (HS727D 1) KC0 BFUEL FUEL None (HS727C_12 1) (plan727 1 startup_plan_segC) = COk (startup_shapeD).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeD))). Time Qed.
Lemma startup_certD : forall b : bool,
  check ASEGS ITD ASAN NXD AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NXD AsanInit.LIMIT) XE0 XB0 (HS727D (rseq_z b)) KC0 BFUEL FUEL None (HS727C_12 (rseq_z b)) (plan727 (rseq_z b) startup_plan_segC) = COk (startup_shapeD).
Proof. ltac1:(intros [|]; [exact startup_certD1 | exact startup_certD0]). Qed.
