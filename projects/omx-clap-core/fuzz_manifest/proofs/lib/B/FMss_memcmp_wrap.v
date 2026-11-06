(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_memcmp_wrap.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* lib/A/Prog/memcmp_wrap.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8), re-run against the
   local-shadow statement FMss_memcmp_wrap_c.v: the two range checks come from chk_ok_of_loc (FMss_shv.v) and the
   post's shadow facts from shvis_kept; every other line is the original's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0 AsanRT AsanRTFacts BzBridge FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memcmp_wrap_c wrap_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMss_memcmp_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.asan_region_is_poisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_memcmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_memcmpw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_thread.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module ARP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.asan_region_is_poisoned.
Module BzC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_memcmp.
Module BzW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_memcmpw.
Module BzT := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_tramp.
Module BzR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_m2s.
Module BzH := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_thread.
Module BzP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_isPoisoned.

Theorem memcmp_wrap_holds_L : memcmp_wrap_contract_L.
Proof.
  unfold memcmp_wrap_contract_L.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo.
  cbv zeta. intros BUFL BUFR HM HMI HN ADL ADR EAL EAR A7L A7R SEPL SEPR HST HK HLO HSP HC [HSL HSRR] HRM HGCF HF4 HF5.
  unfold MEMCMP_WRAP_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  assert (HM' : BzSF.memcmp_model (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs)
                  (Z.to_nat (bv_unsigned a2)) = Some v) by (rewrite memcmp_model_firstn; exact HM).
  assert (LL : (length (firstn (Z.to_nat (bv_unsigned a2)) ls) <= Z.to_nat (bv_unsigned a2))%nat) by (rewrite length_firstn; lia).
  assert (LR : (length (firstn (Z.to_nat (bv_unsigned a2)) rs) <= Z.to_nat (bv_unsigned a2))%nat) by (rewrite length_firstn; lia).
  assert (BL : bytes_at rsegs m (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) ls)). rewrite firstn_skipn. exact BUFL. }
  assert (BR : bytes_at rsegs m (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) rs)). rewrite firstn_skipn. exact BUFR. }
  apply (evt_mono rsegs (fun st => exists st0,
            BzH.frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v
              [(bv_unsigned sp - 2320, bv_unsigned sp)] lo (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (bz_run _ _ F _ fc m HMI).
    apply BzT.tramp_memcmp.
    apply (BzC.imemcmp_spec BzP.rip_proof mcmp_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
             (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs) v (bv_unsigned sp - 2320) lo).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + unfold BzW.cmp_pre.
      split; [exact LL|]. split; [exact LR|]. split; [exact HM'|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold APPMEM_END in LE; lia|]. split; [unfold APPMEM_END in RE; lia|].
      split.
      { apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE, APPMEM_END in *; lia | exact BL]. }
      split.
      { apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE, APPMEM_END in *; lia | exact BR]. }
      split; [lia|]. split; [lia|].
      split; [exact (chk_ok_of_loc m _ _ HMI HSL ADL EAL A7L HN)|].
      split; [exact (chk_ok_of_loc m _ _ HMI HSRR ADR EAR A7R HN)|].
      split; [exact (ARP.m2s_cells_normalize m HMI HC)|].
      exact (icells_mcmp_norm m HMI HC HGCF HRM HF4 HF5).
    + lia.
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (stack_W_ok (bv_unsigned sp - 2320) (bv_unsigned sp) ltac:(lia) ltac:(lia) ltac:(lia)) as [AW DJ].
    destruct (wrap_post_L [(bv_unsigned sp - 2320, bv_unsigned sp)] m (ms_mem st) m0' lo (bv_unsigned sp)
                HMI HC E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & MK').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [exact ST'|split; [exact HC'|split; [split; [exact (shvis_kept _ _ _ _ HSL MK' (addressable_app _ _ _ ADL)) | exact (shvis_kept _ _ _ _ HSRR MK' (addressable_app _ _ _ ADR))]|split]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 2320, bv_unsigned sp)] m (ms_mem st)); [exact BL | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 2320, bv_unsigned sp)] m (ms_mem st)); [exact BR | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
Qed.
