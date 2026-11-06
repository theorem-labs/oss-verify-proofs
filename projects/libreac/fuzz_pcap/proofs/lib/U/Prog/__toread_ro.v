From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require __toread.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel StdioRo __toread_c __toread_ro_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __toread_ro_of : __toread_contract -> __toread_ro_contract.
Proof.
  intros H. unfold __toread_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b Fc
    fl md q rb pv nx MF NRh RL FL MD HRO ST NRs L1 L2 L3.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  pose proof (MemNorm.evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) stdio_ro_wx HRO
                (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                   F fc (MemNorm.normalize rsegs m) lo b Fc fl md q rb pv nx
                   (mfile_norm _ _ _ _ _ _ _ _ _ _ HRO MF NRh) RL FL MD (MemNorm.mem_inv_normalize rsegs m)
                   (RoAdapt.stk_norm rsegs m lo (bv_unsigned sp) HRO ST NRs) L1 L2 L3)) as E.
  eapply evt_mono; [exact E|].
  intros s (s0' & P & MR & RS).
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & A0 & MU & WM & MI & ST' & MF').
  destruct s as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem). cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mem.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - unfold MS. subst. reflexivity.
  - exact A0.
  - eapply MemNorm.munch_rel; [exact REL | exact Hmem | exact RS | exact MU].
  - eapply MemNorm.wmono_rel; [exact REL | exact Hmem | exact RS | exact WM].
  - eapply MemNorm.ro_agree_same; [exact HRO | exact RS].
  - exact (RoAdapt.stk_back rsegs mem m' _ _ Hmem ST').
  - exact (mfile_back _ _ _ _ _ _ _ _ _ _ _ Hmem MF').
Qed.

Theorem __toread_ro_holds : __toread_ro_contract.
Proof. exact (__toread_ro_of __toread.__toread_holds). Qed.
