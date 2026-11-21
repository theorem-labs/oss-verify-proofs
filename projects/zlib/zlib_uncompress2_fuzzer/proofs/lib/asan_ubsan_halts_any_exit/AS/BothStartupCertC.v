(* AS/BothStartupCertC = our text + AS/AsanStartupCertC port, carried by port_by_analogy727_r5 () with --lit StartupHSAsan727=StartupHSBoth727; the old text is kept aside *)
(* certificate C at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth BothStartupCert AsanRenum StartupHSBoth727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITC : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_B.
Lemma ITC_ok : itab_sound BSEGS ITC.
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
  check BSEGS ITC BOTH NXC AsanInit.LIMIT 0 (XNS BSEGS BOTH NXC AsanInit.LIMIT) XE0 XB0 (HS727C 0) KC0 BFUEL FUEL None (HS727B_11 0) (plan727 0 startup_plan_both_segB) = COk (startup_shapeC 0).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeC 0))). Time Qed.
Lemma startup_certC1 :
  check BSEGS ITC BOTH NXC AsanInit.LIMIT 1 (XNS BSEGS BOTH NXC AsanInit.LIMIT) XE0 XB0 (HS727C 1) KC0 BFUEL FUEL None (HS727B_11 1) (plan727 1 startup_plan_both_segB) = COk (startup_shapeC 1).
Proof. Time (vm_cert_refl constr:(COk (startup_shapeC 1))). Time Qed.
Lemma startup_certC : forall b : bool,
  check BSEGS ITC BOTH NXC AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NXC AsanInit.LIMIT) XE0 XB0 (HS727C (rseq_z b)) KC0 BFUEL FUEL None (HS727B_11 (rseq_z b)) (plan727 (rseq_z b) startup_plan_both_segB) = COk (startup_shapeC (rseq_z b)).
Proof. ltac1:(intros [|]; [exact startup_certC1 | exact startup_certC0]). Qed.
