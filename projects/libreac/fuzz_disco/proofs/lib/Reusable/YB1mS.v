(* YB1m.v's startup_cert, put together from its parts YB1mP, YB1mA, YB1mB and YB1mC with the steps of YB1mW.v.
   Nothing is computed here: each computed fact is a vm_cast lemma of a part, and every step below matches the terms
   of those lemmas as written (no unfolding of the walk or the checker). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h YB12 YB1h YB1l YB05 YB01 YB03 YB1mW.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1mK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YB1mP YB1mA YB1mB YB1mC.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Lemma startup_cert_k :
check TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 3000%nat None (init_acs_of_g TFIB) startup_plan_tfib = COk yb1m_shape.
Proof.
destruct (YB1mW.walk_out (YB1mW.walk TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) 0%nat 400000%nat 1000%nat 3000%nat (init_acs_of_g TFIB) startup_plan_tfib) (bool * cres)
(fun cs : acs => (via_ok NX0G cs JS_tfib_band 292%nat, check TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2847%nat (Some (JC 1%nat JS_tfib_band yb1m_shape (nxt cs) 292%nat)) cs yb1m_karms)) 2848%nat (PVia 1%nat JS_tfib_band 292%nat yb1m_karms startup_plan_tfib_band20) (true, COk yb1m_shape) YB1mP.pre_all) as [H1 H23].
destruct (YB1mW.pair_out _ _ _ _ _ _ H23) as [H2 H3].
refine (eq_trans (YB1mW.walk_step TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 1000%nat 3000%nat (init_acs_of_g TFIB) startup_plan_tfib _ _ _ H1) _).
refine (eq_trans (YB1mW.via_step TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2847%nat _ 1%nat JS_tfib_band 292%nat yb1m_karms startup_plan_tfib_band20 yb1m_shape
H2 _) H3).
refine (eq_trans (YB1mW.walk_step TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 1000%nat 2847%nat JS_tfib_band startup_plan_tfib_band20 _ _ _ YB1mC.band_walk) _).
refine (YB1mW.split_step TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2826%nat yb1m_css (EVar 6) 10
startup_plan_tfib_s2A3 (PSplit (EVar 6) 1802 startup_plan_tfib_s2B6 startup_plan_tfib_s2C19) 0 2047
yb1m_sa (SCase (EVar 6) 1802 yb1m_sb yb1m_sc) eq_refl YB1mC.band_r1 eq_refl YB1mA.part_a _).
exact (YB1mW.split_step TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2825%nat (set_kn yb1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn yb1m_css)) (EVar 6) 1802
startup_plan_tfib_s2B6 startup_plan_tfib_s2C19 11 2047 yb1m_sb yb1m_sc eq_refl YB1mC.band_r2 eq_refl YB1mB.part_b YB1mC.part_c).
Qed.
(* startup_cert_split is startup_cert_k with the table written out, the form of YB1m.startup_cert: YB1m.v then checks
   it by unfolding only its own small definitions (IT0, hole_le_tfib, KC0, BFUEL, FUEL, startup_shape). *)
Lemma yb1m_it_eq : mk_itab_ranges TSEGS startup_plan_tfib_ranges = yb1m_it.
Proof. exact (@eq_refl itab (mk_itab_ranges TSEGS startup_plan_tfib_ranges)). Qed.
Lemma startup_cert_split :
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 3000%nat None (init_acs_of_g TFIB) startup_plan_tfib
= COk yb1m_shape.
Proof. rewrite yb1m_it_eq. exact startup_cert_k. Qed.
