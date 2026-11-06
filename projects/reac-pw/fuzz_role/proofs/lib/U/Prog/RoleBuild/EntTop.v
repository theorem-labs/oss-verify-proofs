(** rb_ent_contract (U/Prog/RoleBuild/EntCut.v) holds: one ent_build turn of the UBSan builder, from the head walk
    (EntHead.v) and the walks of the ten kinds (Ent0.v with the cut of Ent0Mid.v proved in Ent0T.v, Ent1.v .. Ent9.v),
    given memset, memcpy and strlen. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts EntHead Ent0Mid Ent0T
  Ent0 Ent1 Ent2 Ent3 Ent4 Ent5 Ent6 Ent7 Ent8 Ent9.
Import ListNotations.
Open Scope Z_scope.

Theorem rb_ent_holds : memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  rb_ent_contract.
Proof.
  intros MSET MCPY STRL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r src pp lo
    -> -> -> -> -> -> -> -> -> H0 HR HL H8 H50 H68 H78 H80 HST HLO HAL HROM HREL HMI.
  assert (HE : ent_pre sp m r src pp lo).
  { exact (conj H0 (conj HR (conj HL (conj H8 (conj H50 (conj H68 (conj H78 (conj H80 (conj HST (conj HLO (conj HAL
      (conj HROM (conj HREL HMI))))))))))))). }
  exact (head_ok sp gp tp s11 F fc m r src pp lo HE MSET
    (case0_nil_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL (case0_mid_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL))
    (case0_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL (case0_mid_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL))
    (case1_ok sp gp tp s11 F fc m r src pp lo HE MCPY STRL)
    (case2_ok sp gp tp s11 F fc m r src pp lo HE)
    (case3_ok sp gp tp s11 F fc m r src pp lo HE)
    (case4_ok sp gp tp s11 F fc m r src pp lo HE)
    (case5_ok sp gp tp s11 F fc m r src pp lo HE MCPY)
    (case6_ok sp gp tp s11 F fc m r src pp lo HE MCPY)
    (case7_ok sp gp tp s11 F fc m r src pp lo HE MCPY)
    (case8_ok sp gp tp s11 F fc m r src pp lo HE MSET)
    (case9_ok sp gp tp s11 F fc m r src pp lo HE MCPY)
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6).
Qed.
