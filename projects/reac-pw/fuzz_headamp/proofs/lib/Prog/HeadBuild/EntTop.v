(** rb_ent_contract (EntCut.v) from memset's, memcpy's and strlen's contracts: the head (EntHead.head_ok) with the
    ten kinds' walks (Ent0 .. Ent9, Ent0P for kind 0's parts). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import EntCut EntFacts EntHead Ent0Cut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Ent0 Ent0P Ent1 Ent2 Ent3 Ent4 Ent5 Ent6 Ent7 Ent8
  Ent9.
Import ListNotations.
Open Scope Z_scope.

Theorem rb_ent_holds : memset_contract -> memcpy_contract -> strlen_contract -> rb_ent_contract.
Proof.
  intros MSET MCPY STRL. unfold rb_ent_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r src pp lo
    -> -> -> -> -> -> -> -> H0 HR HRL H50 H58 H70 H78 HST HLO HSPA HROM HREL HMI.
  assert (HE : ent_pre sp m r src pp lo).
  { exact (conj H0 (conj HR (conj HRL (conj H50 (conj H58 (conj H70 (conj H78 (conj HST (conj HLO (conj HSPA
      (conj HROM (conj HREL HMI)))))))))))). }
  eapply (head_ok sp gp tp s1 s8 F fc m r src pp lo HE MSET).
  all: first [ apply Ent0.case0_nil | apply Ent0.case0_ok | apply Ent1.case1_ok | apply Ent2.case2_ok
             | apply Ent3.case3_ok | apply Ent4.case4_ok | apply Ent5.case5_ok | apply Ent6.case6_ok
             | apply Ent7.case7_ok | apply Ent8.case8_ok | apply Ent9.case9_ok ].
  all: first [ assumption | apply Ent0P.parts_ok; assumption ].
Qed.
