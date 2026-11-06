(* Part of YB1m.v's startup_cert (see YB1mW.v): the walk from the PVia join state to the argc split, the split's
   range facts, and its third case (1803 <= EVar 6), plan startup_plan_tfib_s2C19. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h YB12 YB1h YB1l YB05 YB01 YB03 YB1mW.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1mK.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Lemma band_walk :
YB1mW.walk TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) 0%nat 400000%nat 1000%nat 2847%nat JS_tfib_band startup_plan_tfib_band20 = (2827%nat, yb1m_css, PSplit (EVar 6) 10 startup_plan_tfib_s2A3 (PSplit (EVar 6) 1802 startup_plan_tfib_s2B6 startup_plan_tfib_s2C19)).
Proof. vm_cast_no_check (@eq_refl (nat * acs * plan) (2827%nat, yb1m_css, PSplit (EVar 6) 10 startup_plan_tfib_s2A3 (PSplit (EVar 6) 1802 startup_plan_tfib_s2B6 startup_plan_tfib_s2C19))). Qed.
Lemma band_r1 : erange (kn yb1m_css) (EVar 6) = Some (0, 2047).
Proof. vm_cast_no_check (@eq_refl (option (Z * Z)) (Some (0, 2047))). Qed.
Lemma band_r2 : erange (kn (set_kn yb1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn yb1m_css))) (EVar 6) = Some (11, 2047).
Proof. vm_cast_no_check (@eq_refl (option (Z * Z)) (Some (11, 2047))). Qed.
Lemma part_c :
check TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2825%nat None (set_kn (set_kn yb1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn yb1m_css)) (KRange (EVar 6) (1802 + 1) 2047 :: kn (set_kn yb1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn yb1m_css)))) startup_plan_tfib_s2C19 = COk yb1m_sc.
Proof. vm_cast_no_check (@eq_refl cres (COk yb1m_sc)). Qed.
