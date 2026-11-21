(* AS/AsanStartupCert2 = our text + 's own edits to theories/Common/AsanStartupCert2.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* certificate 2 (the hand-off to the main body) at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan StartupPlan2Asan StartupHS2Asan AsanStartupCert AsanRenum StartupHSAsan727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXS2 : nat := nx727 453.
Lemma NXS2_ge : (NX0 <= NXS2)%nat. Proof. vm_compute. lia. Qed.
Definition startup2_shape_r30 : shape := SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (SHole 1) (SHole 2).
Definition startup2_shape (r : Z) : shape := shape727 r startup2_shape_r30.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup2_cert0 :
  check ASEGS IT2 ASAN NXS2 AsanInit.LIMIT 0 (XNS ASEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 (HS727_2 0) KC0 BFUEL FUEL None (HS727D_0 0) (plan727 0 startup2_plan) = COk (startup2_shape 0).
Proof. Time (vm_cert_refl constr:(COk (startup2_shape 0))). Time Qed.
Lemma startup2_cert1 :
  check ASEGS IT2 ASAN NXS2 AsanInit.LIMIT 1 (XNS ASEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 (HS727_2 1) KC0 BFUEL FUEL None (HS727D_0 1) (plan727 1 startup2_plan) = COk (startup2_shape 1).
Proof. Time (vm_cert_refl constr:(COk (startup2_shape 1))). Time Qed.
Lemma startup2_cert : forall b : bool,
  check ASEGS IT2 ASAN NXS2 AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 (HS727_2 (rseq_z b)) KC0 BFUEL FUEL None (HS727D_0 (rseq_z b)) (plan727 (rseq_z b) startup2_plan) = COk (startup2_shape (rseq_z b)).
Proof. ltac1:(intros [|]; [exact startup2_cert1 | exact startup2_cert0]). Qed.
