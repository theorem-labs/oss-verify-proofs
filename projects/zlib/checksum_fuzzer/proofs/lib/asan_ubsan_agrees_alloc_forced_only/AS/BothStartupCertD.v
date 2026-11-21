(* AS/BothStartupCertD = our text + AS/AsanStartupCertD port, carried by port_by_analogy727_r5 () with --lit StartupHSAsan727=StartupHSBoth727; the old text is kept aside *)
(* certificate D at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth BothStartupCert AsanRenum StartupHSBoth727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITD : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_C.
Lemma ITD_ok : itab_sound BSEGS ITD.
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
  check BSEGS ITD BOTH NXD AsanInit.LIMIT 0 (XNS BSEGS BOTH NXD AsanInit.LIMIT) XE0 XB0 (HS727D 0) KC0 BFUEL FUEL None (HS727C_12 0) (plan727 0 startup_plan_both_segC) = COk (startup_shapeD).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeD))). Time Qed.
Lemma startup_certD1 :
  check BSEGS ITD BOTH NXD AsanInit.LIMIT 1 (XNS BSEGS BOTH NXD AsanInit.LIMIT) XE0 XB0 (HS727D 1) KC0 BFUEL FUEL None (HS727C_12 1) (plan727 1 startup_plan_both_segC) = COk (startup_shapeD).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeD))). Time Qed.
Lemma startup_certD : forall b : bool,
  check BSEGS ITD BOTH NXD AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NXD AsanInit.LIMIT) XE0 XB0 (HS727D (rseq_z b)) KC0 BFUEL FUEL None (HS727C_12 (rseq_z b)) (plan727 (rseq_z b) startup_plan_both_segC) = COk (startup_shapeD).
Proof. ltac1:(intros [|]; [exact startup_certD1 | exact startup_certD0]). Qed.
