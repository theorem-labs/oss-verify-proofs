(** rb_ent_contract (EntCut.v) from memset's, memcpy's and strlen's contracts: the head (EntHead.head_ok) with the
    walks of the ten kinds and of the empty input (Ent0 .. Ent9). The form is reac-pw/fuzz_role's plain
    lib/Prog/RoleBuild/EntTop.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts EntHead.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Ent0 Ent1 Ent2 Ent3 Ent4 Ent5 Ent6 Ent7 Ent8
  Ent9.
Import ListNotations.
Open Scope Z_scope.

Theorem rb_ent_holds : memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract -> rb_ent_contract.
Proof.
  intros MSET MCPY STRL. unfold rb_ent_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r src pp lo
    -> -> -> -> -> -> -> -> H0 HR HRL H00 H80 HA0 HC8 HD8 HST HLO HSPA HROM HREL HMI.
  assert (HE : ent_pre sp m r src pp lo).
  { exact (conj H0 (conj HR (conj HRL (conj H00 (conj H80 (conj HA0 (conj HC8 (conj HD8 (conj HST (conj HLO
      (conj HSPA (conj HROM (conj HREL HMI))))))))))))). }
  exact (head_ok sp gp tp s3 F fc m r src pp lo HE MSET
    (Ent0.case0_nil_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL)
    (Ent0.case0_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL)
    (Ent1.case1_ok sp gp tp s3 F fc m r src pp lo HE MCPY STRL)
    (Ent2.case2_ok sp gp tp s3 F fc m r src pp lo HE)
    (Ent3.case3_ok sp gp tp s3 F fc m r src pp lo HE)
    (Ent4.case4_ok sp gp tp s3 F fc m r src pp lo HE)
    (Ent5.case5_ok sp gp tp s3 F fc m r src pp lo HE MCPY)
    (Ent6.case6_ok sp gp tp s3 F fc m r src pp lo HE MCPY)
    (Ent7.case7_ok sp gp tp s3 F fc m r src pp lo HE MCPY)
    (Ent8.case8_ok sp gp tp s3 F fc m r src pp lo HE MSET)
    (Ent9.case9_ok sp gp tp s3 F fc m r src pp lo HE MCPY)
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6).
Qed.
