(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUDrv HUSel HUFam2 UR2GS0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require UR2GCDc0 UR2GCThmc0 UQ2GCDd UQ2GCThmd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition HASHF : kentry := KRange (esub (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (ELit 14695981039346656037) (EExt false 0 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (EExt false 1 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (EVar 11)) 0 0.
Definition LIM : Z := 2147483648.
Definition g_R2GC_c0 : gsel := GS UR2GCDc0.N0 R2G_cs [] UR2GCDc0.a0s
  [LN 98299 102380; LN 102381 104828; LN 104829 106476; LN 106477 110572; LN 110573 114668; LN 114669 118764; LN 118765 122860; LN 122861 126956; LN 126957 131051] (map HUFam2.l2_view UR2GCDc0.leaves2)
  UR2GCDc0.ops UR2GCDc0.shapeB UR2GCDc0.sC2s false.
Definition g_Q2GC_d : gsel := GS UQ2GCDd.N0 R2G_csq R2G_qsub UQ2GCDd.a0s
  [LQ 32 63 0 2028; LQ 32 63 2029 4075; LQ 31 63 4076 4076; LQ 31 63 4077 4095] (map HUFam2.l2_view UQ2GCDd.leaves2)
  UQ2GCDd.ops UQ2GCDd.shapeB UQ2GCDd.sC2s false.
Definition fam : list gsel := [g_R2GC_c0; g_Q2GC_d].
Definition cov : list (Z * Z * nat * nat) := [(98299, 102380, 0%nat, 0%nat); (102381, 104828, 0%nat, 1%nat); (104829, 106476, 0%nat, 2%nat); (106477, 110572, 0%nat, 3%nat); (110573, 114668, 0%nat, 4%nat); (114669, 118764, 0%nat, 5%nat); (118765, 122860, 0%nat, 6%nat); (122861, 126956, 0%nat, 7%nat); (126957, 131051, 0%nat, 8%nat)].
Definition qcov : list (Z * Z * nat * nat) := [(0, 2028, 1%nat, 0%nat); (2029, 4075, 1%nat, 1%nat); (4076, 4076, 1%nat, 2%nat); (4077, 4095, 1%nat, 3%nat)].
Lemma TABLEN : forallb (fun g => Nat.eqb (length (gs_lnums g)) (length (gs_leaves g))) fam = true /\ map (fun g => length (gs_lnums g)) fam = [9%nat; 4%nat].
Proof. split; vm_compute; reflexivity. Qed.
Lemma CHK : HUSel.fam_chk 57 58 59 2 HASHF fam cov qcov 131052 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SHP : forallb (HUSel.shp_chk 57 56) fam = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SIDE : forallb grp_side (map gs_G fam) = true.
Proof. vm_compute. reflexivity. Qed.
Section D.
  Variables (sp : word) (STR0 : Z) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Lemma HG : forall g, In g fam -> grp_stmt sp STR0 LIM fs (gs_G g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [exact (UR2GCThmc0.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (UQ2GCThmd.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg.
  Qed.
  Lemma HBASE : forall g, In g fam -> gs_S0 g = inst_list R2G_cs (gs_sub g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [vm_compute; reflexivity|].
    destruct Hg.
  Qed.
  Theorem K2G_family : forall (PHIb : env -> Prop) t E R FULL model,
    HUSel.tin_ok 2 t -> HUSel.eokx 57 56 58 59 HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E R2G_cs R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc R2G_cs) FULL model) (HUSel.TGT (HUSel.t_n t <? 11) (Z.to_nat (HUSel.t_calls t)) (HUSel.t_cnt t) (m_fs model)).
  Proof.
    exact (HUSel.family_numx sp STR0 LIM fs R2G_cs eq_refl 57 56 58 59 2 HASHF ltac:(lia) fam cov qcov 131052 HG HBASE SIDE CHK SHP).
  Qed.
End D.
Check K2G_family.
