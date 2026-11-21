(* TRIAL NOT-OFFICIAL: AS/AsanStartupCert = our text + 727298f3's own edits to theories/Common/AsanStartupCert.v, 3-way merged (proposal md5 509b803d); the old text is kept aside *)
(* an earlier development run 727298f3: the start-up certificate (segment 0) at 727298f3, for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymExec3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanCore OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanSound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanPlanImages OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanInit OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesWJoin OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartup OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupPlanAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanRenum OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges_0.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_cert0 :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT 0 (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 (HS727A 0) KC0 BFUEL FUEL None (asan_init 0) (plan727 0 startup_plan) = COk (startup_shape).
Proof. Time (vm_cert_refl constr:(COk (startup_shape))). Time Qed.
Lemma startup_cert1 :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT 1 (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 (HS727A 1) KC0 BFUEL FUEL None (asan_init 1) (plan727 1 startup_plan) = COk (startup_shape).
Proof. Time (vm_cert_refl constr:(COk (startup_shape))). Time Qed.
Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 (HS727A (rseq_z b)) KC0 BFUEL FUEL None (asan_init (rseq_z b)) (plan727 (rseq_z b) startup_plan) = COk (startup_shape).
Proof. ltac1:(intros [|]; [exact startup_cert1 | exact startup_cert0]). Qed.
