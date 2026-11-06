From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c classify_core_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_classify_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_disco_classify_holds : classify_core_contract -> reac_disco_classify_contract.
Proof.
  intros CC. unfold reac_disco_classify_contract, classify_core_contract, classify_core_spec,
    REAC_DISCO_CLASSIFY, CLASSIFY_CORE in *.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         lo f len u o FB U OB E0 E1 E2 E3 PRE.
  step. step. step. step. step. step.
  eapply CC; [ reflexivity | exact E0 | exact E1 | exact E2 | exact E3 | exact PRE ].
Qed.
