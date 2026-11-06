From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strspn_c strcspn_c strtok_r_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strtok_r_ro_c strtok_r.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma strtok_r_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u8arr_ro_norm : forall m A bs, MemNorm.ro_agree rsegs m -> u8arr rsegs m A bs ->
  not_ro rsegs A (Z.of_nat (length bs)) -> u8arr rsegs (MemNorm.normalize rsegs m) A bs.
Proof.
  intros m A bs HR [Hb Hw] Hn. split.
  - apply MemNorm.bytes_at_normalize; assumption.
  - exact (wr_at_norm' rsegs m A _ HR Hw Hn).
Qed.

Lemma u8arr_ro_back : forall m m0 A bs, MemNorm.mem_rel rsegs m m0 -> u8arr rsegs m0 A bs -> u8arr rsegs m A bs.
Proof.
  intros m m0 A bs REL [Hb Hw]. split.
  - exact (bytes_at_back rsegs m m0 A bs REL Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

Theorem strtok_r_ro_of : strtok_r_contract -> strtok_r_ro_contract.
Proof.
  intros H. unfold strtok_r_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m C pv str slack sep lo can
    HRW HNRW HC HSTR HNS HSEP HNSEP HGOT HGUARD HSTK HNSTK HK HA1 HA2 HGS HGDS HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  { eapply MemNorm.evt_normalize; [exact strtok_r_wx | exact HRO | ].
    apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) C pv str slack sep lo can).
    - exact (rw_cells_norm rsegs m _ _ HRO HRW HNRW).
    - exact HC.
    - intros HC0. destruct (HSTR HC0) as (UA & B & X1 & X2 & X3 & NR).
      refine (conj (u8arr_ro_norm m C _ HRO UA _)
                (conj (MemNorm.bytes_at_normalize rsegs m _ _ HRO B) (conj X1 (conj X2 X3)))).
      intros i Hi. apply NR. rewrite length_app in Hi. cbn [length] in Hi. lia.
    - exact HNS.
    - exact (MemNorm.bytes_at_normalize rsegs m _ _ HRO HSEP).
    - exact HNSEP.
    - exact (MemNorm.bytes_at_normalize rsegs m _ _ HRO HGOT).
    - exact (MemNorm.bytes_at_normalize rsegs m _ _ HRO HGUARD).
    - exact (stk_norm rsegs m _ _ HRO HSTK HNSTK).
    - exact HK.
    - exact HA1.
    - exact HA2.
    - exact HGS.
    - exact HGDS.
    - exact (MemNorm.mem_inv_normalize rsegs m). }
  intros s (s0' & P & MR & RS).
  destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                 MU & WM & MI & STK & RW' & CB).
  destruct s as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem). cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mem.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - unfold MS. subst. reflexivity.
  - eapply MemNorm.munch_rel; [exact REL|exact Hmem|exact RS|exact MU].
  - eapply MemNorm.wmono_rel; [exact REL|exact Hmem|exact RS|exact WM].
  - eapply MemNorm.ro_agree_same; [exact HRO|exact RS].
  - exact (stk_back rsegs mem m' lo _ Hmem STK).
  - exact (rw_cells_back rsegs mem m' _ _ Hmem RW').
  - intros HC0. destruct (CB HC0) as [UA B].
    exact (conj (u8arr_ro_back mem m' C _ Hmem UA) (bytes_at_back rsegs mem m' _ _ Hmem B)).
Qed.

Theorem strtok_r_ro_holds : strspn_contract -> strcspn_contract -> strtok_r_ro_contract.
Proof. intros H0 H1. exact (strtok_r_ro_of (strtok_r_holds H0 H1)). Qed.
