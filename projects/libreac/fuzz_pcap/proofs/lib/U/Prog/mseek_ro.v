From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require mseek.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel StdioRo mseek_c mseek_ro_c.
Import ListNotations.
Open Scope Z_scope.

Theorem mseek_ro_of : mseek_contract -> mseek_ro_contract.
Proof.
  intros H. unfold mseek_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b n
    fl rpos rend md q r pv nx buf RAW NRh R1 R2 R3 A1 A2 GOK HRO ST NRs L1 L2 L3.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  pose proof (MemNorm.evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) stdio_ro_wx HRO
                (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                   F fc (MemNorm.normalize rsegs m) lo b n fl rpos rend md q r pv nx buf
                   (mfile_raw_norm _ _ _ _ _ _ _ _ _ _ _ _ HRO RAW NRh) R1 R2 R3 A1 A2 (guard_ok_norm m HRO GOK)
                   (MemNorm.mem_inv_normalize rsegs m)
                   (RoAdapt.stk_norm rsegs m lo (bv_unsigned sp) HRO ST NRs) L1 L2 L3)) as E.
  eapply evt_mono; [exact E|].
  intros s (s0' & P & MR & RS).
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & A0 & MU & WM & MI & ST' & RAW').
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
  - exact (mfile_raw_back _ _ _ _ _ _ _ _ _ _ _ _ _ Hmem RAW').
Qed.

Theorem mseek_ro_holds : mseek_ro_contract.
Proof. exact (mseek_ro_of mseek.mseek_holds). Qed.
