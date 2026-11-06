From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT BzBridge BzCallBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_region_is_poisoned_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_thread.
Import ListNotations.
Open Scope Z_scope.

Module BzP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_isPoisoned.
Module BzC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_consts.
Module BzT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_thread.

Theorem asan_region_is_poisoned_holds : asan_region_is_poisoned_contract.
Proof.
  unfold asan_region_is_poisoned_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros HN HP HPN HP7 HA HC HSR HMI HST HK HLO HSP.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL0.
  apply (evt_mono rsegs (fun st => exists st0,
            BzT.frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0
              [(bv_unsigned sp - 80, bv_unsigned sp)] lo (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (evt_normalize_cj rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzP.rip_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) lo).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (acc_normalize m _ _ RO HA).
    + lia.
    + unfold BzC.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
    + exact (m2s_cells_normalize m HMI HC).
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + unfold ASAN_REGION_IS_POISONED_K in HK. lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU].
    + eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM].
    + exact (mem_inv_of_normalized m _ HMI SAME).
    + exact (stk_of_normalized _ _ lo _ E8 ST).
Qed.
