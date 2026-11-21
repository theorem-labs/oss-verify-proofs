(* TRIAL NOT-OFFICIAL: AS/AsanStartupCertC = our text + 727298f3's own edits to theories/Common/AsanStartupCertC.v, 3-way merged (proposal md5 a92e649e); the old text is kept aside *)
(* an earlier development run 727298f3: certificate C at 727298f3, for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.AxSymExec3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanCore OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanPlanSound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanPlanImages OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanInit OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanNodesWJoin OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartup OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupPlanAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.AsanStartupCert OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanRenum OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.StartupHSAsan727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITC : itab := mk_itab_ranges ASEGS startup_plan_ranges_B.
Lemma ITC_ok : itab_sound ASEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXC : nat := nx727 344.
Lemma NXC_ge : (NX0 <= NXC)%nat. Proof. vm_compute. lia. Qed.
(* the r30q2 shape; its e_atr8 cases move with the layout (AsanRenum.shape727) *)
Definition startup_shapeC_r30 : shape := SCase (EVar 6) 10 (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))) (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))).
Definition startup_shapeC (r : Z) : shape := shape727 r startup_shapeC_r30.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certC0 :
  check ASEGS ITC ASAN NXC AsanInit.LIMIT 0 (XNS ASEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 (HS727C 0) KC0 BFUEL FUEL None (HS727B_11 0) (plan727 0 startup_plan_segB) = COk (startup_shapeC 0).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeC 0))). Time Qed.
Lemma startup_certC1 :
  check ASEGS ITC ASAN NXC AsanInit.LIMIT 1 (XNS ASEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 (HS727C 1) KC0 BFUEL FUEL None (HS727B_11 1) (plan727 1 startup_plan_segB) = COk (startup_shapeC 1).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeC 1))). Time Qed.
Lemma startup_certC : forall b : bool,
  check ASEGS ITC ASAN NXC AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 (HS727C (rseq_z b)) KC0 BFUEL FUEL None (HS727B_11 (rseq_z b)) (plan727 (rseq_z b) startup_plan_segB) = COk (startup_shapeC (rseq_z b)).
Proof. ltac1:(intros [|]; [exact startup_certC1 | exact startup_certC0]). Qed.
