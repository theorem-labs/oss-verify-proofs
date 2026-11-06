(* Part of YB1m.v's startup_cert (see YB1mW.v): the argc split's first case (EVar 6 <= 10), plan startup_plan_tfib_s2A3. *)
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
Lemma part_a :
check TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2826%nat None (set_kn yb1m_css (KRange (EVar 6) 0 10 :: kn yb1m_css)) startup_plan_tfib_s2A3 = COk yb1m_sa.
Proof. vm_cast_no_check (@eq_refl cres (COk yb1m_sa)). Qed.
