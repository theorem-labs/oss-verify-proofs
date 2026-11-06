(* Modified by Theorem Labs, 2026-10: image A copy of lib/Reusable/YB1mB.v (a working branch 29ff9194385) for lib/A/AB1m.v; AB05's plan has YB05's structure node for node (they differ only in addresses), so only the module paths and the yb1m_ / YB1m prefixes change. *)
(* Part of AB1m.v's startup_cert (see Reusable/YB1mW.v): the argc split's second case (11 <= EVar 6 <= 1802), plan startup_plan_tfib_s2B6. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB12 AB1h AB1l AB05 AB01 AB03.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1mW.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1mK.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Lemma part_b :
check TSEGS ab1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2825%nat None (set_kn (set_kn ab1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn ab1m_css)) (KRange (EVar 6) 11 1802 :: kn (set_kn ab1m_css (KRange (EVar 6) (10 + 1) 2047 :: kn ab1m_css)))) startup_plan_tfib_s2B6 = COk ab1m_sb.
Proof. vm_cast_no_check (@eq_refl cres (COk ab1m_sb)). Qed.
