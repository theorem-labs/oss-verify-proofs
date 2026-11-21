(* AS/BothStartupCert = our text + AS/AsanStartupCert port, carried by port_by_analogy727_r5 () with --lit StartupHSAsan727=StartupHSBoth727; the old text is kept aside *)
(* the start-up certificate (segment 0) at , for both rseq values (r = 0 / 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth AsanRenum StartupHSBoth727.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_0.
Lemma IT0_ok : itab_sound BSEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_cert0 :
  check BSEGS IT0 BOTH NX0 AsanInit.LIMIT 0 (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XE0 XB0 (HS727A 0) KC0 BFUEL FUEL None (both_init 0) (plan727 0 startup_plan_both) = COk (startup_shape).
Proof. Time (vm_cert_refl constr:(COk (startup_shape))). Time Qed.
Lemma startup_cert1 :
  check BSEGS IT0 BOTH NX0 AsanInit.LIMIT 1 (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XE0 XB0 (HS727A 1) KC0 BFUEL FUEL None (both_init 1) (plan727 1 startup_plan_both) = COk (startup_shape).
Proof. Time (vm_cert_refl constr:(COk (startup_shape))). Time Qed.
Lemma startup_cert : forall b : bool,
  check BSEGS IT0 BOTH NX0 AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XE0 XB0 (HS727A (rseq_z b)) KC0 BFUEL FUEL None (both_init (rseq_z b)) (plan727 (rseq_z b) startup_plan_both) = COk (startup_shape).
Proof. ltac1:(intros [|]; [exact startup_cert1 | exact startup_cert0]). Qed.
