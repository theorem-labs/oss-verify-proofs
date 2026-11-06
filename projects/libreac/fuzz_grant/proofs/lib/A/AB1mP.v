(* Part of AB1m.v's startup_cert (see AB1mW.v): one walk (computed once: let) from the start state to the PVia node, its via_ok test and
   its two arms (PCaseDisj; each arm is PX XMemset, then PMerge into the join shape). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB12 AB1h AB1l AB05 AB01 AB03 AB1mW.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1mK.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Lemma pre_all :
(let w := AB1mW.walk TSEGS ab1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) 0%nat 400000%nat 1000%nat 3000%nat (init_acs_of_g TFIB) startup_plan_tfib in
(fst (fst w), snd w, (via_ok NX0G (snd (fst w)) JS_tfib_band 292%nat, check TSEGS ab1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2847%nat (Some (JC 1%nat JS_tfib_band ab1m_shape (nxt (snd (fst w))) 292%nat)) (snd (fst w)) ab1m_karms))) = (2848%nat, PVia 1%nat JS_tfib_band 292%nat ab1m_karms startup_plan_tfib_band20, (true, COk ab1m_shape)).
Proof. vm_cast_no_check (@eq_refl (nat * plan * (bool * cres)) (2848%nat, PVia 1%nat JS_tfib_band 292%nat ab1m_karms startup_plan_tfib_band20, (true, COk ab1m_shape))). Qed.
