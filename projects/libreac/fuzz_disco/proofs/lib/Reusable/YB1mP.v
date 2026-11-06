(* Part of YB1m.v's startup_cert (see YB1mW.v): one walk (computed once: let) from the start state to the PVia node, its via_ok test and
   its two arms (PCaseDisj; each arm is PX XMemset, then PMerge into the join shape). *)
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
Lemma pre_all :
(let w := YB1mW.walk TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) 0%nat 400000%nat 1000%nat 3000%nat (init_acs_of_g TFIB) startup_plan_tfib in
(fst (fst w), snd w, (via_ok NX0G (snd (fst w)) JS_tfib_band 292%nat, check TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 HS_tfib (fun _ _ => true) 0%nat 400000%nat 2847%nat (Some (JC 1%nat JS_tfib_band yb1m_shape (nxt (snd (fst w))) 292%nat)) (snd (fst w)) yb1m_karms))) = (2848%nat, PVia 1%nat JS_tfib_band 292%nat yb1m_karms startup_plan_tfib_band20, (true, COk yb1m_shape)).
Proof. vm_cast_no_check (@eq_refl (nat * plan * (bool * cres)) (2848%nat, PVia 1%nat JS_tfib_band 292%nat yb1m_karms startup_plan_tfib_band20, (true, COk yb1m_shape))). Qed.
