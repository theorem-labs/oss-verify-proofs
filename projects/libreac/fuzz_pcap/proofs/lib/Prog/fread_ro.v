From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require memcpy __toread mread fread.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel StdioRo fread_c fread_ro_c.
Import ListNotations.
Open Scope Z_scope.

Theorem fread_ro_of : fread_contract -> fread_ro_contract.
Proof.
  intros H. unfold fread_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b Fc
    p pv nx junk HMS NRh A1 K1 RW NRd D1 D2 D3 HRO ST NRs L1 L2 L3.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (RWn : rw_cells rsegs (MemNorm.normalize rsegs m) (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk]).
  { apply RoAdapt.rw_cells_norm; [exact HRO | exact RW |].
    intros i Hi. apply NRd. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia. exact Hi. }
  pose proof (MemNorm.evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) stdio_ro_wx HRO
                (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                   F fc (MemNorm.normalize rsegs m) lo b Fc p pv nx junk
                   (mstl_norm _ _ _ _ _ _ _ HRO HMS NRh) A1 K1 RWn D1 D2 D3 (MemNorm.mem_inv_normalize rsegs m)
                   (RoAdapt.stk_norm rsegs m lo (bv_unsigned sp) HRO ST NRs) L1 L2 L3)) as E.
  eapply evt_mono; [exact E|].
  intros s (s0' & P & MR & RS).
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & A0 & MU & WM & MI & ST' & BD & MS').
  destruct s as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem). cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mem.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - unfold MS. subst. reflexivity.
  - exact A0.
  - eapply MemNorm.munch_rel; [exact REL | exact Hmem | exact RS | exact MU].
  - eapply MemNorm.wmono_rel; [exact REL | exact Hmem | exact RS | exact WM].
  - eapply MemNorm.ro_agree_same; [exact HRO | exact RS].
  - exact (RoAdapt.stk_back rsegs mem m' _ _ Hmem ST').
  - exact (RoAdapt.bytes_at_back rsegs mem m' _ _ Hmem BD).
  - exact (mstl_back _ _ _ _ _ _ _ _ Hmem MS').
Qed.

Theorem fread_ro_holds : fread_ro_contract.
Proof.
  exact (fread_ro_of (fread.fread_holds memcpy.memcpy_holds __toread.__toread_holds (mread.mread_holds memcpy.memcpy_holds))).
Qed.
