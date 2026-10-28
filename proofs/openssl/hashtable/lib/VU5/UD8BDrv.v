(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUDrv HUSel HUFam2 UD8BS0.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require UD8BCDd UD8BCThmd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition HASHF : kentry := KRange (esub (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (ELit 14695981039346656037) (EExt false 0 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (EExt false 1 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (EVar 11)) 0 0.
Definition LIM : Z := 2147483648.
Definition g_D8BC_d : gsel := GS UD8BCDd.N0 D8B_csq D8B_qsub UD8BCDd.a0s
  [LQ 2040 4095 0 2028; LQ 2040 4095 2029 4076; LQ 2039 4095 4077 4095] (map HUFam2.l2_view UD8BCDd.leaves2)
  UD8BCDd.ops UD8BCDd.shapeB UD8BCDd.sC2s false.
Definition fam : list gsel := [g_D8BC_d].
Definition cov : list (Z * Z * nat * nat) := [].
Definition qcov : list (Z * Z * nat * nat) := [(0, 2028, 0%nat, 0%nat); (2029, 4076, 0%nat, 1%nat); (4077, 4095, 0%nat, 2%nat)].
Lemma TABLEN : forallb (fun g => Nat.eqb (length (gs_lnums g)) (length (gs_leaves g))) fam = true /\ map (fun g => length (gs_lnums g)) fam = [3%nat].
Proof. split; vm_compute; reflexivity. Qed.
Lemma CHK : HUSel.fam_chk 60 61 62 8 HASHF fam cov qcov 131052 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SHP : forallb (HUSel.shp_chk 60 59) fam = true.
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
    destruct Hg as [<-|Hg]; [exact (UD8BCThmd.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg.
  Qed.
  Lemma HBASE : forall g, In g fam -> gs_S0 g = inst_list D8B_cs (gs_sub g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [vm_compute; reflexivity|].
    destruct Hg.
  Qed.
  Theorem D8B_family : forall (PHIb : env -> Prop) t E R FULL model,
    HUSel.tin_ok 8 t -> HUSel.eokx 60 59 61 62 HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E D8B_cs R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc D8B_cs) FULL model) (HUSel.TGT (HUSel.t_n t <? 11) (Z.to_nat (HUSel.t_calls t)) (HUSel.t_cnt t) (m_fs model)).
  Proof.
    exact (HUSel.family_numx sp STR0 LIM fs D8B_cs eq_refl 60 59 61 62 8 HASHF ltac:(lia) fam cov qcov 131052 HG HBASE SIDE CHK SHP).
  Qed.
End D.
Check D8B_family.
