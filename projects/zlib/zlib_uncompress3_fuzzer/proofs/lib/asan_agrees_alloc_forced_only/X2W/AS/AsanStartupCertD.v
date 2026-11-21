(* TRIAL NOT-OFFICIAL: AS/AsanStartupCertD = our text + 727298f3's own edits to theories/Common/AsanStartupCertD.v, 3-way merged (proposal md5 866a7251); the old text is kept aside *)
(* an earlier development run 727298f3: certificate D at 727298f3, for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymExec3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanCore OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanSound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanPlanImages OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanInit OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesWJoin OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartup OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupPlanAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCert OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanRenum OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan727.
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
