(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0PlanImage H0Atable H0Sinv H0CheckG H0Chain H0Chain2 H0Hop H0Batch H0Fam.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Drv H0Sel H0Fam2 R1GS0.
From OSSVerify.Proofs.openssl.hashtable.lib Require R1GCDc0 R1GCThmc0 R1GCDc1 R1GCThmc1 R1GCDc2 R1GCThmc2 Q1GCDd Q1GCThmd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition HASHF : kentry := KRange (esub (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (ELit 14695981039346656037) (EExt false 0 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (EExt false 1 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (EVar 11)) 0 0.
Definition LIM : Z := 2147483648.
Definition g_R1GC_c0 : gsel := GS R1GCDc0.N0 R1G_cs [] R1GCDc0.a0s
  [LN 32763 36844; LN 36845 37436; LN 37437 40940; LN 40941 43676; LN 43677 45036; LN 45037 49132; LN 49133 52412; LN 52413 53228; LN 53229 57324; LN 57325 61420] (map H0Fam2.l2_view R1GCDc0.leaves2)
  R1GCDc0.ops R1GCDc0.shapeB R1GCDc0.sC2s false.
Definition g_R1GC_c1 : gsel := GS R1GCDc1.N0 R1G_cs [] R1GCDc1.a0s
  [LN 61421 65516; LN 65517 69612; LN 69613 73708; LN 73709 74876; LN 74877 77804; LN 77805 81900; LN 81901 85996; LN 85997 87356; LN 87357 90092; LN 90093 94188] (map H0Fam2.l2_view R1GCDc1.leaves2)
  R1GCDc1.ops R1GCDc1.shapeB R1GCDc1.sC2s false.
Definition g_R1GC_c2 : gsel := GS R1GCDc2.N0 R1G_cs [] R1GCDc2.a0s
  [LN 94189 98284; LN 98285 102380; LN 102381 104828; LN 104829 106476; LN 106477 110572; LN 110573 114668; LN 114669 118764; LN 118765 122860; LN 122861 126956; LN 126957 131051] (map H0Fam2.l2_view R1GCDc2.leaves2)
  R1GCDc2.ops R1GCDc2.shapeB R1GCDc2.sC2s false.
Definition g_Q1GC_d : gsel := GS Q1GCDd.N0 R1G_csq R1G_qsub Q1GCDd.a0s
  [LQ 31 32 4076 4076; LQ 31 32 4077 4095] (map H0Fam2.l2_view Q1GCDd.leaves2)
  Q1GCDd.ops Q1GCDd.shapeB Q1GCDd.sC2s false.
Definition fam : list gsel := [g_R1GC_c0; g_R1GC_c1; g_R1GC_c2; g_Q1GC_d].
Definition cov : list (Z * Z * nat * nat) := [(32763, 36844, 0%nat, 0%nat); (36845, 37436, 0%nat, 1%nat); (37437, 40940, 0%nat, 2%nat); (40941, 43676, 0%nat, 3%nat); (43677, 45036, 0%nat, 4%nat); (45037, 49132, 0%nat, 5%nat); (49133, 52412, 0%nat, 6%nat); (52413, 53228, 0%nat, 7%nat); (53229, 57324, 0%nat, 8%nat); (57325, 61420, 0%nat, 9%nat); (61421, 65516, 1%nat, 0%nat); (65517, 69612, 1%nat, 1%nat); (69613, 73708, 1%nat, 2%nat); (73709, 74876, 1%nat, 3%nat); (74877, 77804, 1%nat, 4%nat); (77805, 81900, 1%nat, 5%nat); (81901, 85996, 1%nat, 6%nat); (85997, 87356, 1%nat, 7%nat); (87357, 90092, 1%nat, 8%nat); (90093, 94188, 1%nat, 9%nat); (94189, 98284, 2%nat, 0%nat); (98285, 102380, 2%nat, 1%nat); (102381, 104828, 2%nat, 2%nat); (104829, 106476, 2%nat, 3%nat); (106477, 110572, 2%nat, 4%nat); (110573, 114668, 2%nat, 5%nat); (114669, 118764, 2%nat, 6%nat); (118765, 122860, 2%nat, 7%nat); (122861, 126956, 2%nat, 8%nat); (126957, 131051, 2%nat, 9%nat)].
Definition qcov : list (Z * Z * nat * nat) := [(4076, 4076, 3%nat, 0%nat); (4077, 4095, 3%nat, 1%nat)].
Lemma TABLEN : forallb (fun g => Nat.eqb (length (gs_lnums g)) (length (gs_leaves g))) fam = true /\ map (fun g => length (gs_lnums g)) fam = [10%nat; 10%nat; 10%nat; 2%nat].
Proof. split; vm_compute; reflexivity. Qed.
Lemma CHK : H0Sel.fam_chk 57 58 59 1 HASHF fam cov qcov 131052 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SHP : forallb (H0Sel.shp_chk 57 56) fam = true.
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
    destruct Hg as [<-|Hg]; [exact (R1GCThmc0.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (R1GCThmc1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (R1GCThmc2.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (Q1GCThmd.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg.
  Qed.
  Lemma HBASE : forall g, In g fam -> gs_S0 g = inst_list R1G_cs (gs_sub g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [vm_compute; reflexivity|].
    destruct Hg.
  Qed.
  Theorem K1G_family : forall (PHIb : env -> Prop) t E R FULL model,
    H0Sel.tin_ok 1 t -> H0Sel.eokx 57 56 58 59 HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E R1G_cs R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc R1G_cs) FULL model) (H0Sel.TGT (H0Sel.t_n t <? 11) (Z.to_nat (H0Sel.t_calls t)) (H0Sel.t_cnt t) (m_fs model)).
  Proof.
    exact (H0Sel.family_numx sp STR0 LIM fs R1G_cs eq_refl 57 56 58 59 1 HASHF ltac:(lia) fam cov qcov 131052 HG HBASE SIDE CHK SHP).
  Qed.
End D.
Check K1G_family.
