(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_svc_pending"; "ms_read_byte"; "ms_writable_byte"; "ms_mem"; "write_to_mem"; "@Corelib.Init.Datatypes"; "list"; "option"; "pair"; "Some"; "None"; "nil"; "prod"; "nat"; "app"; "cons"; "length"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_halted"; "event"; "FdEntry"; "m_fds"; "SyscallEffect"; "fd_lookup"; "read_cstr"; "FdFile"; "TASK_SIZE"; "m_fs"; "MemCopy"; "errno_ret"; "mkEffectU"; "syscall_effect_accesses"; "FdChannel"; "FdDir"; "MAX_RW_COUNT"; "fd_insert"; "read_bytes_map"; "with_fds"; "EISDIR"; "ENOTTY"; "m_vm_lazy"; "m_vmmaps"; "VmMaps"; "cstr_result"; "write_accesses"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "bv_add"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkCfg"; "config"; "sys_input"; "advance_past_svc"; "apply_effect"; "SNext"; "sstep"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "cmd32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "wstep"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "closed_model"; "after_sys_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "ranges_avoid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "hid"; "MI"; "md_after"; "mat_equiv"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ldiff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "vm_same"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "openat_reads"; "is_ret"; "is_ret_ci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA.WithSegs"; "read_accesses"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "path"; "file_read"; "fs_lookup"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "open_ignored_flags"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "AT_FDCWD32"; "TIOCGWINSZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "cstr_no_slash"; "openat_post"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess"; "delivered_writes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "sstep_a"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SysOpen SysExtra.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
  Variable segs : list Segment.

  Lemma sstep_run_accA : ltac2:(tb__ "0|3|
SaS31Q40A1M0A1S4S15G0S1aS15SaS17A1S0SbG0A1M1S5R6A1SdG0R4A2A3S0G1S16R6A1SeG0A1M2A3S60S37Vsegs;R8R6A3R7S4fS1aR5R4R3A4A3S0G1S16R5A1G2A3S46Vsegs;R6RbA3S44S45R7RcA2S23R8A1A2S61Vsegs;S35RcRbA2R7S3aS35S38S39RcR9A2A1S47R8S23R9A1A2A2A1A4F_;F_;F_;F_;F_;F_;Fevs;Fm';Feff;Fx8;Fm;Fms;Ftp;").
  Proof using .
    intros tp ms m x8 eff m' evs Hp Hh [Hs Hns] Hh' HMI Hav. unfold sstep_a.
    eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hs | exact (Hns _ _ _ eq_refl ltac:(congruence)) | exact Hh' |].
    exact (proj1 (materialize_prepaid segs m' tp _ HMI Hav)).
  Qed.

  Lemma wstep_run_accA : ltac2:(tb__ "0|4|
SaS31Q40A1M0A1SaS17A1M1S4S15G0S1aS15G1S0SbG0A1M2S5R6A1SdG0R4A2A3S0G2S16R6A1SeG0A1M3A3S60S37Vsegs;R8R6A3R7S4fS1aR5R4R3A4A3S0G2S16R5A1G3A3S46Vsegs;R6RcA3S44S45R7RdA2S23R8A1A2S3fVsegs;ScG1S36RdS35RcRbA2A4ScG1S36S12S17RdR7A3S35S38S39RcR9A2A1S47R8S23R9A1A2A2A4A3F_;F_;F_;F_;F_;F_;Fevs;Fm';Feff;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros. exists evs. split; [|reflexivity]. cbn. eapply sstep_run_accA; eauto.
  Qed.

  Lemma wstep_retci_invA : ltac2:(tb__ "0|4|
SaS31Q40A1M0A1SaS17A1M1S4S15G0G0SaS10G0S11A2A1S15G1S40S0SbG0A1M2S5R8A1SdG0R6A2A3S0G2S16R8A1SeG0A1M3A3S50S1aA1S49S37Vsegs;RbR9A3RaR1A3S53R2R9R8R7R6A5F_;FR;S0G2S16R6A1G3A3S46Vsegs;R7ReA3S44S45R8RfA2R9A2S3fVsegs;ScG1S36RfS35ReRdA2A4R7A3S0S40R8ScG1S36S12S17R10R9A3S35S41RfRcA2S47RaRbA2A2A4A3F_;F_;F_;F_;F_;F_;F_;Fw';Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 r ci m1 evs1 w' Hp Hh Hinv Hh1 HMI Hav Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply Hinv in Hspec. unfold is_ret_ci in Hspec. inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses app] in Hm. rewrite app_nil_r in Hm.
    rewrite (proj1 (materialize_prepaid segs m1 tp ci HMI Hav)) in Hm. injection Hm as <-.
    rewrite advance_apply_ret_ci. reflexivity.
  Qed.

  Lemma wstep_retci_introA : ltac2:(tb__ "0|5|
SaS31Q40A1M0A1SaS17A1M1S4S15G0G0SaS10G0S11A2A1S15G1S0SbG0A1M2S5R7A1SdG0R5A2A3S0G2S16R7A1SeG0A1M3A3S60S37Vsegs;R9R7A3R8S4fS1aS22R6SfS10G0SaS31Q8A1A1A2A1SfS10G0G0A2A1M4G4SfS20A1R5A6R4R3A4A3S0G2S16R5A1G3A3S46Vsegs;R6RdA3S44S45R7ReA2R8A2S3fVsegs;ScG1S36ReS35RdRcA2A4ScG1S36S12S17ReR7A3S35S41RdRaA2S47R8R9A2A2A4A3F_;F_;F_;F_;F_;F_;Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 r ci m1 evs1 Hp Hh Hs Hh1 HMI Hav.
    rewrite <- (advance_apply_ret_ci ms r ci).
    pose proof (@wstep_run_accA tp tr ms m x8 _ m1 evs1 Hp Hh Hs Hh1 HMI) as W.
    unfold syscall_effect_accesses in W. cbn [eff_copyins eff_writes write_accesses app] in W. rewrite app_nil_r in W.
    exact (W Hav).
  Qed.

  Lemma wstep_retci_introA0 : ltac2:(tb__ "0|5|
SaS31Q40A1M0A1SaS17A1M1S4S15G0G0SaS10G0S11A2A1S15S0SbG0A1M2S5R6A1SdG0R4A2A3S0G2S16R6A1SeG0A1M3A3S60S37Vsegs;R8R6A3R7S4fS1aS22R5SfS10G0SaS31Q8A1A1A2A1SfS10G0G0A2A1M4G4SfS20A1R4A6R3SfS17A1A4A3S0G2S16R4A1G3A3S46Vsegs;R5RcA3S44S45R6RdA2R7A2S3fVsegs;ScG1S36RdS35RcRbA2A4ScG1S36RdS35S41RcR9A2S47R7R8A2A2A4A3F_;F_;F_;F_;F_;F_;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 r ci m1 Hp Hh Hs Hh1 HMI Hav.
    pose proof (@wstep_retci_introA tp tr ms m x8 r ci m1 [] Hp Hh Hs Hh1 HMI Hav) as W. rewrite app_nil_r in W. exact W.
  Qed.

  Lemma only_okA_retci : ltac2:(tb__ "0|1|
SaS31Q40A1M0A1S4S15G0G0SaS10G0S11A2A1S15SaS17A1S50S1aA1S49S37Vsegs;R8R6A3R7R1A3S53R2R6R5R4R3A5F_;FR;S46Vsegs;R3R9A3S44S45R4RaA2R5A2S4dS37Vsegs;RaR8A3R9A2F_;F_;F_;Fevs1;Fm1;Fci;Fr;Fx8;Fm;Fms;Ftp;").
  Proof using .
    intros tp ms m x8 r ci m1 evs1 Hinv HMI Hav.
    eapply only_okA_of_inv; [exact Hinv | unfold is_ret_ci; discriminate |].
    intros eff m' evs E _. unfold is_ret_ci in E. inversion E; subst.
    unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. rewrite app_nil_r.
    rewrite (proj1 (materialize_prepaid segs m1 tp ci HMI Hav)). discriminate.
  Qed.

  Lemma md_after_props : ltac2:(tb__ "0|2|
SaS31Q40A1M0A1S15SaS10G0S11A2A1S46Vsegs;R2R3A3S44S45R3R4A2R2A2S1S48Vsegs;R5R4S47R4R3A2M1A4S1S46Vsegs;G1R5A3S1S0SaS10G0S18A2A1S19G1A1S19R4A1A3S1S0S58S1fG1A1S1fR4A1A3S1S0SbG0A1S16G1A1S16R4A1A3S1S0S2eS2dG1A1S2dR4A1A3S0SaS10G0G0A2A1S2cG1A1S2cR4A1A3A2A2A2A2A2A2F_;F_;Faccs;Fm;Ftp;").
  Proof using .
    intros tp m accs HMI Hav. pose proof (materialize_prepaid segs m tp accs HMI Hav) as (_ & Hme & HMI').
    split; [exact Hme|]. split; [exact HMI'|]. unfold md_after. repeat split; reflexivity.
  Qed.

  Lemma openat_rd_casesA : ltac2:(tb__ "0|3|
S4S15S31Q40M0A1M1S50S1aA1S0S3cS32G0R2A2Z38A3S0S3cS4cS32G0S3R5U2A2A2S59A2Z0A3S0G1S3dS3R6U0A2A1S5aA3S5cS1cS6R7A1S3R7U1M2A2A2A1S49S37Vsegs;R8R6A3R7R5A3S2G1G1S2S15S15S1S53R8R2S51S37Vsegs;RbR9A3A1R1SfS17A1A5S5dRaS1cS6RbA1S3RbG2A2A2R2R1A4A2Lm1;A2Lr;A2F_;F_;F_;F_;F_;FR;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 R Hno Hfl Hdir Hns HR.
    destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc.
    - exists (errno_ret ENOENT), m. split; [exact (openat_empty_inv (sys_input segs ms x8) m Hno Hfl _ Hc HR) | cbn; auto].
    - cbn [openat_post]. cbn in Hns. destruct (path_is_dirref (b :: p)) eqn:Hd.
      + destruct (openat_dirref_inv (sys_input segs ms x8) m Hno Hfl Hdir _ (b :: p) Hc Hd HR) as [(e & Hin & E)|(Hfree & E)].
        * exists (errno_ret e), m. split; [exact E | left; exists e; auto].
        * exists (alloc_fd (m_fds m)), (openat_dir_model m). split; [exact E | right; auto].
      + destruct (fs_lookup (m_fs m) (b :: p)) as [data|] eqn:Hfs.
        * destruct (openat_file_inv (sys_input segs ms x8) m Hno Hfl Hdir _ b p data Hc Hd Hns Hfs HR) as [(e & Hin & E)|(Hfree & E)].
          -- exists (errno_ret e), m. split; [exact E | left; exists e; auto].
          -- exists (alloc_fd (m_fds m)), (openat_file_model m (b :: p)). split; [exact E | right; auto].
        * exists (errno_ret ENOENT), m. split; [exact (openat_absent_inv (sys_input segs ms x8) m Hno Hfl Hdir _ b p Hc Hd Hns Hfs HR) | auto].
    - exists (errno_ret ENAMETOOLONG), m. split; [exact (openat_toolong_inv (sys_input segs ms x8) m Hno Hfl _ Hc HR) | cbn; auto].
    - exists (errno_ret EFAULT), m. split; [exact (openat_fault_inv (sys_input segs ms x8) m Hno Hfl _ Hc HR) | cbn; auto].
  Qed.

  Lemma openat_post_vm_same : ltac2:(tb__ "0|1|
S15S2fS31Q40A1M0S15S5dR4R3R2R1A4S1S4eR5R2A2S0SbG0A1S16R2A1S16R5A1A3A2F_;Fmd';Fr;Fc;Fmd;").
  Proof using .
    intros md c r md' H. unfold openat_post in H.
    destruct c as [[|b p]| |]; try (destruct H as [_ ->]; split; [apply vm_same_refl | reflexivity]).
    cbn iota in H. destruct (path_is_dirref (b :: p)).
    - destruct H as [(e & _ & _ & ->)|(_ & _ & ->)]; [split; [apply vm_same_refl | reflexivity]|].
      split; [apply vm_same_with_fds | reflexivity].
    - destruct (fs_lookup (m_fs md) (b :: p)).
      + destruct H as [(e & _ & _ & ->)|(_ & _ & ->)]; [split; [apply vm_same_refl | reflexivity]|].
        split; [apply vm_same_with_fds | reflexivity].
      + destruct H as [_ ->]. split; [apply vm_same_refl | reflexivity].
  Qed.

  Lemma ranges_avoid_vm_same : ltac2:(tb__ "0|1|
S15S15SaS31Q40A1M0A1SaS10G0S11A2A1S4eR4R3A2S44S45R5R3A2R2A2S44S45R5R4A2R3A2F_;F_;Fl;Ftp;Fm';Fm;").
  Proof using . intros m m' tp l Hvs H a n Hin k Hk. rewrite (vm_same_hid m m' tp Hvs). exact (H a n Hin k Hk). Qed.

  Lemma openat_rd_only_okA : ltac2:(tb__ "0|2|
SaS31Q40M0A1M1A1S4S15G1S0SbG1A1S16R2A1SeG1A1A3S46Vsegs;R3R5A3S0S3cS32G0R3A2Z38A3S0S3cS4cS32G0S3R6U2A2A2S59A2Z0A3S0G1S3dS3R7U0A2A1S5aA3S5cS1cS6R8A1S3R8U1A2A2A1S44S45R8RaA2S51S37Vsegs;R9R7A3A1A2S4dS37Vsegs;RaR8A3R9A2F_;F_;F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftp;").
  Proof using .
    intros tp ms m x8 Hh HMI Hno Hfl Hdir Hns Hav. split.
    - intros Hun. destruct (openat_rd_casesA ms m x8 _ Hno Hfl Hdir Hns Hun) as (r & m1 & E & _). unfold is_ret_ci in E. discriminate.
    - intros eff m' evs Hs Hh'. destruct (openat_rd_casesA ms m x8 _ Hno Hfl Hdir Hns Hs) as (r & m1 & E & Hpost).
      unfold is_ret_ci in E. inversion E; subst.
      destruct (openat_post_vm_same _ _ _ _ Hpost) as [Hvs _].
      unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. rewrite app_nil_r.
      rewrite (proj1 (materialize_prepaid segs m1 tp _ (vm_same_MI segs m m1 tp Hvs HMI) (ranges_avoid_vm_same m m1 tp _ Hvs Hav))). discriminate.
  Qed.

  Lemma wstep_openat_rd_invA : ltac2:(tb__ "0|5|
SaS31Q40M0A1M1A1SaS17A1M2S4S15G1S40S0SbG1A1M3S5R4A1SdG1R2A2A3S0G3S16R4A1SeG1A1A3S46Vsegs;R5R8A3S0S3cS32G0R5A2Z38A3S0S3cS4cS32G0S3R8U2A2A2S59A2Z0A3S0G1S3dS3R9U0A2A1S5aA3S5cS1cS6RaA1S3RaU1M4A2A2A1S44S45RaRdA2S51S37Vsegs;RbR9A3A1A2S3fVsegs;ScG2S36RdS35RcRbA2A4R9A3S2G1G1S2S15S15S1S5dReS1cS6RfA1S3RfG4A2A2R2R1A4S0S40RcScG2S36R10S35S41RfR2A2S47R1S51S37Vsegs;RfRdA3A1A2A2A4A3A2Lm';A2Lr;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 w' Hp Hh HMI Hno Hfl Hdir Hns Hav Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    destruct (openat_rd_casesA ms m x8 _ Hno Hfl Hdir Hns Hspec) as (r & m1 & E & Hpost).
    unfold is_ret_ci in E. inversion E; subst.
    exists r, m1. split; [exact Hpost|].
    destruct (openat_post_vm_same _ _ _ _ Hpost) as [Hvs Hh1].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [| rewrite Hh1, Hh in Hcd; discriminate].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses app] in Hm. rewrite app_nil_r in Hm.
    rewrite (proj1 (materialize_prepaid segs m1 tp _ (vm_same_MI segs m m1 tp Hvs HMI) (ranges_avoid_vm_same m m1 tp _ Hvs Hav))) in Hm.
    injection Hm as <-. rewrite advance_apply_ret_ci, app_nil_r. reflexivity.
  Qed.

  Lemma wstep_openat_rd_introA : ltac2:(tb__ "0|5|
SaS31Q40M0A1M1A1SaS17A1M2S4S15G1G1S15S0SbG1A1M3S5R5A1SdG1R3A2A3S0G3S16R5A1SeG1A1A3S46Vsegs;R6R9A3S0S3cS32G0R6A2Z38A3S0S3cS4cS32G0S3R9U2A2A2S59A2Z0A3S0G1S3dS3RaU0A2A1S5aA3S5cS1cS6RbA1S3RbU1M4A2A2A1S44S45RbReA2S51S37Vsegs;RcRaA3A1A2S5dRcS1cS6RdA1S3RdG4A2A2RaR9A4S3fVsegs;ScG2S36RfS35ReRdA2A4ScG2S36RfS35S41ReRbA2S47RaS51S37Vsegs;ReRcA3A1A2A2A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fm';Fr;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 r m' Hp Hh HMI Hno Hfl Hdir Hns Hav Hpost.
    destruct (openat_post_vm_same _ _ _ _ Hpost) as [Hvs Hh1].

    assert (Hs : syscall_spec_ns (sys_input segs ms x8) m (Ok (mkEffectU r [] [] [] [] (openat_reads (sys_input segs ms x8))) m' [])).
    { unfold openat_post in Hpost.
      destruct (read_cstr (ms_read_byte ms) (ms_gpr ms 1)) as [[|b p]| |] eqn:Hc.
      - destruct Hpost as [-> ->]. exact (openat_empty_intro (sys_input segs ms x8) m Hno Hfl Hc).
      - cbn iota in Hpost. cbn in Hns. destruct (path_is_dirref (b :: p)) eqn:Hd.
        + destruct Hpost as [(e & Hin & -> & ->)|(Hfree & -> & ->)].
          * exact (openat_dirref_intro_err (sys_input segs ms x8) m Hno Hfl Hdir e (b :: p) Hc Hd Hin).
          * exact (openat_dirref_intro_ok (sys_input segs ms x8) m Hno Hfl Hdir (b :: p) Hc Hd Hfree).
        + destruct (fs_lookup (m_fs m) (b :: p)) as [data|] eqn:Hfs.
          * destruct Hpost as [(e & Hin & -> & ->)|(Hfree & -> & ->)].
            -- exact (openat_file_intro_err (sys_input segs ms x8) m Hno Hfl Hdir e b p data Hc Hd Hns Hfs Hin).
            -- exact (openat_file_intro_ok (sys_input segs ms x8) m Hno Hfl Hdir b p data Hc Hd Hns Hfs Hfree).
          * destruct Hpost as [-> ->]. exact (openat_absent_intro (sys_input segs ms x8) m Hno Hfl Hdir b p Hc Hd Hns Hfs).
      - destruct Hpost as [-> ->]. exact (openat_toolong_intro (sys_input segs ms x8) m Hno Hfl Hc).
      - destruct Hpost as [-> ->]. exact (openat_fault_intro (sys_input segs ms x8) m Hno Hfl Hc). }
    eapply wstep_retci_introA0; [exact Hp | exact Hh | exact Hs | rewrite Hh1; exact Hh | eapply vm_same_MI; eauto | eapply ranges_avoid_vm_same; eauto].
  Qed.

  Lemma wstep_ret_invEA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40A1M1G1S15G0S40S0SbG1A1M2S5R7A1SdG1R5A2A3S0G2S16R7A1SeG1A1M3A3S50S1aA1S49S37Vsegs;RaR8A3R9R1A3S52R2R8R7R6A4F_;FR;S0G2S16R6A1G3A3S3fVsegs;ScG0S36RcS35RbRaA2A4R5A3S0S40R6ScG0S36S12S17RdR7A3S35S41RcR9A2R8A2A4A3F_;F_;F_;F_;F_;Fw';Fevs1;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m1 evs1 w' Hp Hh Hinv Hh1 Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply Hinv in Hspec. unfold is_ret in Hspec. inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses app] in Hm.
    rewrite materialize_nil in Hm. injection Hm as <-.
    rewrite advance_apply_ret. reflexivity.
  Qed.

  Lemma wstep_ret_introEA : ltac2:(tb__ "0|5|
SaS17A1M0S4S15S31Q40A1M1G1S15G0S0SbG1A1M2S5R6A1SdG1R4A2A3S0G2S16R6A1SeG1A1M3A3S60S37Vsegs;R8R6A3R7S4fS1aS22R5SfS10G1SaS31Q8A1A1A2A1SfS10G1G1A2A1M4G4SfS20A1SfS10G1S11A2A1A6R4R3A4A3S0G2S16R5A1G3A3S3fVsegs;ScG0S36RbS35RaR9A2A4ScG0S36S12S17RbR5A3S35S41RaR7A2R6A2A4A3F_;F_;F_;F_;Fevs1;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m1 evs1 Hp Hh [Hs Hns] Hh1.
    exists evs1. split; [|reflexivity]. cbn. rewrite <- (advance_apply_ret ms r).
    eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hs | exact (Hns _ _ _ eq_refl ltac:(congruence)) | exact Hh1 |].
    unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. apply materialize_nil.
  Qed.

  Lemma wstep_ret_inv0A : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40A1M1G1S15S40S0SbG1A1M2S5R6A1SdG1R4A2A3S0G2S16R6A1SeG1A1M3A3S50S1aA1S49S37Vsegs;R9R7A3R8R1A3S52R2R7R6SfS17A1A4F_;FR;S0G2S16R5A1G3A3S3fVsegs;ScG0S36RbS35RaR9A2A4R5A3S0S40R6ScG0S36RcS35S41RbR8A2R7A2A4A3F_;F_;F_;F_;F_;Fw';Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m1 w' Hp Hh Hinv Hh1 Hw.
    rewrite (@wstep_ret_invEA tr ms m x8 r m1 [] w' Hp Hh Hinv Hh1 Hw). now rewrite app_nil_r.
  Qed.

  Lemma wstep_ret_intro0A : ltac2:(tb__ "0|5|
SaS17A1M0S4S15S31Q40A1M1G1S15S0SbG1A1M2S5R5A1SdG1R3A2A3S0G2S16R5A1SeG1A1M3A3S60S37Vsegs;R7R5A3R6S4fS1aS22R4SfS10G1SaS31Q8A1A1A2A1SfS10G1G1A2A1M4G4SfS20A1SfS10G1S11A2A1A6R3SfS17A1A4A3S0G2S16R4A1G3A3S3fVsegs;ScG0S36RaS35R9R8A2A4ScG0S36RaS35S41R9R6A2R5A2A4A3F_;F_;F_;F_;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 r m1 Hp Hh Hs Hh1.
    pose proof (@wstep_ret_introEA tr ms m x8 r m1 [] Hp Hh Hs Hh1) as W. rewrite app_nil_r in W. exact W.
  Qed.

  Lemma only_okA_ret : ltac2:(tb__ "0|2|
S4S15S31Q40A1M0G0S15SaS17A1S50S1aA1S49S37Vsegs;R7R5A3M1R6R1A3S52R2R5R4R3A4F_;FR;S4dG1R6A2F_;Fevs1;Fm1;Fr;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 r m1 evs1 Hinv.
    eapply only_okA_of_inv; [exact Hinv | unfold is_ret; discriminate |].
    intros eff m' evs E _. unfold is_ret in E. inversion E; subst.
    unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. rewrite materialize_nil. discriminate.
  Qed.

  Lemma wstep_close_invA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2S18S40S0SbG2A1M3S5R5A1SdG2R3A2A3S0G3S16R5A1SeG2A1A3S0S3cS32G1R5A2Z39A3S0SbS18A1S1bS19R7A1S3dS3R8U0A2A1A2SdS18R5A2A3S3fVsegs;ScG0S36RaS35R9R8A2A4R5A3S0S40R6ScG0S36RbS35S41RaS34G1Z0A2A2S42RaR9A2A2A4A3F_;F_;F_;F_;F_;Fw';Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e w' Hp Hh Hno Hfd Hw.
    refine (@wstep_ret_inv0A _ _ _ _ _ _ _ Hp Hh _ _ Hw); [|exact Hh].
    intros R. exact (@close_inv (sys_input segs ms x8) m Hno e R Hfd).
  Qed.

  Lemma wstep_close_introA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2S18S0SbG2A1M3S5R4A1SdG2R2A2A3S0G3S16R4A1SeG2A1A3S0S3cS32G1R4A2Z39A3S0SbS18A1S1bS19R6A1S3dS3R7U0A2A1A2SdS18R4A2A3S3fVsegs;ScG0S36R9S35R8R7A2A4ScG0S36R9S35S41R8S34G1Z0A2A2S42R8R7A2A2A4A3F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hh Hno Hfd.
    refine (@wstep_ret_intro0A tr _ _ _ _ _ Hp Hh _ _); [|exact Hh].
    exact (@close_intro (sys_input segs ms x8) m Hno e Hfd).
  Qed.

  Lemma close_only_okA : ltac2:(tb__ "0|1|
S4S15S31Q40M0A1S18S0S3cS32G0R2A2Z39A3S0SbS18A1S1bS19R4A1S3dS3R5U0A2A1A2SdS18R2A2A3S4dS37Vsegs;R6R4A3R5A2F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hno Hfd. eapply only_okA_ret. intros R. exact (@close_inv (sys_input segs ms x8) m Hno e R Hfd).
  Qed.

  Lemma closed_model_vm_same : ltac2:(tb__ "0|1|
S4S15S1S4eR1S42R2R1A2M0A2S0SbS31Q40A1A1S16G0A1S16R1A1A3A2Fm;Fms;").
  Proof using . intros. unfold closed_model, close_model. split; [apply vm_same_with_fds | reflexivity]. Qed.

  Lemma wstep_ioctl_invA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2G2S40S0SbG2A1M3S5R5A1SdG2R3A2A3S0G3S16R5A1SeG2A1A3S0S3cS32G1R5A2Z1dA3S0SbS18A1S1bS19R7A1S3dS3R8U0A2A1A2SdS18S24R5A1A2A3S0G2S3eS3R9U1A2A1S5bA3S3fVsegs;ScG0S36RbS35RaR9A2A4R6A3S0S40R7ScG0S36RcS35S41RbS21S2bA1A2RaA2A4A3F_;F_;F_;F_;F_;F_;Fw';Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e w' Hp Hh Hno Hfd Hc Hw.
    refine (@wstep_ret_inv0A _ _ _ _ _ _ _ Hp Hh _ Hh Hw).
    intros R. exact (@ioctl_inv (sys_input segs ms x8) m Hno e R Hfd Hc).
  Qed.

  Lemma wstep_ioctl_introA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2G2S0SbG2A1M3S5R4A1SdG2R2A2A3S0G3S16R4A1SeG2A1A3S0S3cS32G1R4A2Z1dA3S0SbS18A1S1bS19R6A1S3dS3R7U0A2A1A2SdS18S24R4A1A2A3S0G2S3eS3R8U1A2A1S5bA3S3fVsegs;ScG0S36RaS35R9R8A2A4ScG0S36RaS35S41R9S21S2bA1A2R8A2A4A3F_;F_;F_;F_;F_;Fe;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 e Hp Hh Hno Hfd Hc.
    refine (@wstep_ret_intro0A tr _ _ _ _ _ Hp Hh _ Hh).
    exact (@ioctl_intro (sys_input segs ms x8) m Hno e Hfd Hc).
  Qed.

  Lemma ioctl_only_okA : ltac2:(tb__ "0|2|
S4S15S31Q40M0A1M1G1S0S3cS32G0R2A2Z1dA3S0SbS18A1S1bS19R4A1S3dS3R5U0A2A1A2SdS18S24R2A1A2A3S0G1S3eS3R6U1A2A1S5bA3S4dS37Vsegs;R7R5A3R6A2F_;F_;F_;Fe;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 e Hno Hfd Hc. eapply only_okA_ret. intros R. exact (@ioctl_inv (sys_input segs ms x8) m Hno e R Hfd Hc).
  Qed.

  Lemma wstep_writev2_invA : forall tp tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 w',
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    (forall k, ranges_avoid (hid m tp) (writev2_reads (sys_input segs ms x8) b1 l1 b2 l2 k)) ->
    wstep segs (tr, mkCfg ms m) w' ->
    exists k, (1 <= k <= length (bs1 ++ bs2))%nat
      /\ w' = (tr ++ map (WriteEv ch) (firstn k (bs1 ++ bs2)),
               mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) (md_after m (writev2_reads (sys_input segs ms x8) b1 l1 b2 l2 k))).
  Proof using .
    intros tp tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 w' Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen Hav Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    destruct (@writev2_inv (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2 Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen _ Hspec) as (k & Hk & E).
    unfold is_ret_ci in E. inversion E; subst.
    exists k. split; [exact Hk|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses app] in Hm. rewrite app_nil_r in Hm.
    rewrite (proj1 (materialize_prepaid segs m tp _ HMI (Hav k))) in Hm. injection Hm as <-.
    rewrite advance_apply_ret_ci. reflexivity.
  Qed.

  Lemma wstep_writev2_intro_prefixA : forall tp tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 k,
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    (1 <= k <= length (bs1 ++ bs2))%nat ->
    ranges_avoid (hid m tp) (writev2_reads (sys_input segs ms x8) b1 l1 b2 l2 k) ->
    wstep segs (tr, mkCfg ms m) (tr ++ map (WriteEv ch) (firstn k (bs1 ++ bs2)),
                                  mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) (md_after m (writev2_reads (sys_input segs ms x8) b1 l1 b2 l2 k))).
  Proof using .
    intros tp tr ms m x8 ch b1 l1 b2 l2 bs1 bs2 k Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen Hk Hav.
    eapply wstep_retci_introA; [exact Hp | exact Hh | | exact Hh | exact HMI | exact Hav].
    exact (@writev2_intro_prefix (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2 Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen k Hk).
  Qed.

  Lemma writev2_only_okA : forall tp ms m x8 ch b1 l1 b2 l2 bs1 bs2,
    m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16) = Some b2 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 16 + 8) = Some l2 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2 ->
    (bv_unsigned (ms_gpr ms 1) + 32 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
    (forall k, ranges_avoid (hid m tp) (writev2_reads (sys_input segs ms x8) b1 l1 b2 l2 k)) ->
    only_okA (sys_input segs ms x8) m.
  Proof using .
    intros tp ms m x8 ch b1 l1 b2 l2 bs1 bs2 Hh HMI Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen Hav.
    split.
    - intros Hun. destruct (@writev2_inv (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2 Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen _ Hun) as (k & _ & E).
      unfold is_ret_ci in E. discriminate.
    - intros eff m' evs Hs Hh'.
      destruct (@writev2_inv (sys_input segs ms x8) m ch b1 l1 b2 l2 bs1 bs2 Hno Hfd Hch Hcnt R1 R2 R3 R4 B1 B2 Hiok Hok1 Hok2 Hlen _ Hs) as (k & _ & E).
      unfold is_ret_ci in E. inversion E; subst.
      unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. rewrite app_nil_r.
      rewrite (proj1 (materialize_prepaid segs _ tp _ HMI (Hav k))). discriminate.
  Qed.

  Lemma wstep_writev1_invA : forall tp tr ms m x8 ch b1 l1 bs1 w',
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    (forall k, ranges_avoid (hid m tp) (writev1_reads (sys_input segs ms x8) b1 l1 k)) ->
    wstep segs (tr, mkCfg ms m) w' ->
    exists k, (1 <= k <= length bs1)%nat
      /\ w' = (tr ++ map (WriteEv ch) (firstn k bs1),
               mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) (md_after m (writev1_reads (sys_input segs ms x8) b1 l1 k))).
  Proof using .
    intros tp tr ms m x8 ch b1 l1 bs1 w' Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen Hav Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    destruct (@writev1_inv (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen _ Hspec) as (k & Hk & E).
    unfold is_ret_ci in E. inversion E; subst.
    exists k. split; [exact Hk|].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses app] in Hm. rewrite app_nil_r in Hm.
    rewrite (proj1 (materialize_prepaid segs m tp _ HMI (Hav k))) in Hm. injection Hm as <-.
    rewrite advance_apply_ret_ci. reflexivity.
  Qed.

  Lemma wstep_writev1_intro_prefixA : forall tp tr ms m x8 ch b1 l1 bs1 k,
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    (1 <= k <= length bs1)%nat ->
    ranges_avoid (hid m tp) (writev1_reads (sys_input segs ms x8) b1 l1 k) ->
    wstep segs (tr, mkCfg ms m) (tr ++ map (WriteEv ch) (firstn k bs1),
                                  mkCfg (after_sys ms (Z_to_bv 64 (Z.of_nat k))) (md_after m (writev1_reads (sys_input segs ms x8) b1 l1 k))).
  Proof using .
    intros tp tr ms m x8 ch b1 l1 bs1 k Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen Hk Hav.
    eapply wstep_retci_introA; [exact Hp | exact Hh | | exact Hh | exact HMI | exact Hav].
    exact (@writev1_intro_prefix (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen k Hk).
  Qed.

  Lemma writev1_only_okA : forall tp ms m x8 ch b1 l1 bs1,
    m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8) = Some l1 ->
    read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1 ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z ->
    (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
    (forall k, ranges_avoid (hid m tp) (writev1_reads (sys_input segs ms x8) b1 l1 k)) ->
    only_okA (sys_input segs ms x8) m.
  Proof using .
    intros tp ms m x8 ch b1 l1 bs1 Hh HMI Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen Hav.
    split.
    - intros Hun. destruct (@writev1_inv (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen _ Hun) as (k & _ & E).
      unfold is_ret_ci in E. discriminate.
    - intros eff m' evs Hs Hh'.
      destruct (@writev1_inv (sys_input segs ms x8) m ch b1 l1 bs1 Hno Hfd Hch Hcnt R1 R2 B1 Hiok Hok1 Hlen _ Hs) as (k & _ & E).
      unfold is_ret_ci in E. inversion E; subst.
      unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app]. rewrite app_nil_r.
      rewrite (proj1 (materialize_prepaid segs _ tp _ HMI (Hav k))). discriminate.
  Qed.

  Lemma wstep_writev01_invA : forall tp tr ms m x8 ch b w',
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    ranges_avoid (hid m tp) (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]) ->
    wstep segs (tr, mkCfg ms m) w' ->
    w' = (tr, mkCfg (after_sys ms (Z_to_bv 64 0)) (md_after m (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]))).
  Proof using .
    intros tp tr ms m x8 ch b w' Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 Hiok Hbok Hav Hw.
    assert (Hinv : forall R, syscall_spec (sys_input segs ms x8) m R ->
                   is_ret_ci R (Z_to_bv 64 0) (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]) m []).
    { intros R. apply (@writev0_inv (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
        [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity]. }
    pose proof (@wstep_retci_invA tp tr ms m x8 _ _ _ _ w' Hp Hh Hinv Hh HMI Hav Hw) as E.
    rewrite app_nil_r in E. exact E.
  Qed.

  Lemma wstep_writev01_introA : forall tp tr ms m x8 ch b,
    ms_svc_pending ms = Some x8 -> m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    ranges_avoid (hid m tp) (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]) ->
    wstep segs (tr, mkCfg ms m) (tr, mkCfg (after_sys ms (Z_to_bv 64 0)) (md_after m (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]))).
  Proof using .
    intros tp tr ms m x8 ch b Hp Hh HMI Hno Hfd Hch Hcnt R1 R2 Hiok Hbok Hav.
    eapply wstep_retci_introA0; [exact Hp | exact Hh | | exact Hh | exact HMI | exact Hav].
    apply (@writev0_intro (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
      [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity].
  Qed.

  Lemma writev01_only_okA : forall tp ms m x8 ch b,
    m_halted m = None -> MI segs m tp ->
    bv_unsigned x8 = 66%Z ->
    fd_lookup (m_fds m) (fd32 (ms_gpr ms 0)) = Some (FdChannel ch) ->
    ch <> Z_to_bv 64 0 ->
    ms_gpr ms 2 = Z_to_bv 64 1 ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1) = Some b ->
    read_u64 (ms_read_byte ms) (ms_gpr ms 1 + 8)%bv = Some (Z_to_bv 64 0) ->
    (bv_unsigned (ms_gpr ms 1) + 16 <= TASK_SIZE)%Z ->
    (bv_unsigned b <= TASK_SIZE)%Z ->
    ranges_avoid (hid m tp) (writev0_reads (sys_input segs ms x8) [(b, Z_to_bv 64 0)]) ->
    only_okA (sys_input segs ms x8) m.
  Proof using .
    intros tp ms m x8 ch b Hh HMI Hno Hfd Hch Hcnt R1 R2 Hiok Hbok Hav.
    eapply only_okA_retci; [| exact HMI | exact Hav].
    intros R. apply (@writev0_inv (sys_input segs ms x8) m ch [(b, Z_to_bv 64 0)] Hno Hfd Hch);
      [cbn; rewrite Hcnt; reflexivity | cbn; unfold IOV_MAX; lia | apply writev01_iovecs_at; assumption | apply access_okb_of_le; autorewrite with sys_input; cbn [length]; lia | apply writev01_bok; exact Hbok | reflexivity].
  Qed.

  Definition read_accesses (buf : word) (bs : list byte) : list (word * nat) := ltac2:(tb__ "0|0|
S30S5fVbuf;Vbs;A2A1").

  Lemma read_accesses_eq : ltac2:(tb__ "0|6|
S31Q40A1M0SaS31Q8A1M1A1M2S0SaS10G0S11A2M3A1M4S54R2R1A2G2G4Lbs;R1SfG3A1M5G1G2S13G3ScG0S11R4S14G1R3A2A4G5A3Ll;Lb;Xax2A3Fbs;Fbuf;").
  Proof using . intros buf [|b bs]; reflexivity. Qed.

  Lemma read_file_model_props : ltac2:(tb__ "0|4|
S4S15S55S31Q40M0A1M1SaS31Q8A1M2A1S1S4eR4S29S27S19R4A1S3dS3R5U0A2A1S1dR3S33G0R2S5eG2R1A2A3A2A3R4A2M3A2S0SbG1A1S16G3A1S16R4A1A3A2Fbs;Foff;Fp;Fm;Fms;").
  Proof using . intros. split; [apply vm_same_with_fds | reflexivity]. Qed.

  Lemma wstep_read_file_invA : ltac2:(tb__ "0|d|
SaS31Q40M0A1M1A1SaS17A1M2S4S15G1S55G1SaS31Q8A1M3A1M4G4S40S0SbG1A1M5S5R8A1SdG1R6A2A3S0G5S16R8A1SeG1A1A3S46Vsegs;R9RcA3S0S3cS32G0R9A2Z3fA3S0SbS18A1S1bS19RbA1S3dS3RcU0M6A2A1A2SdS18S1dR9R8A2A2A3S0SbG4A1M7S57S1fRcA1RaA2SdG4R8A2M8A3S0G7S28S7Vsegs;ReA2S3ReU1M9A2S3ReU2MaA2A3G8A3S4aS32G0S3RfGaA2A2S26A2S4aS4bS32G0S3R10G9A2A2S32G0S3R10GaA2A2A2S1eA2S56RcRdS3R11GaA2A3G4S44S45R11R14A2S54S3R12G9A2R1A2A2S3fVsegs;ScG2S36R14S35R13R12A2A4RcA3S0S40RdScG2S36R15S35S43R14S5eG3R3A2MbS9S8R14A1S3R14G9A2McR3A3A3S47S29S27S19R13A1S3dS3R14G6A2A1S1dR11S33G0R10GbA3A2A3R13A2S54GcR3A2A2A2A4A3F_;F_;Tbs;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw';Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 p off data wdst w' Hp Hh HMI Hno Hfd Hfs Hw Hcnt Hov bs Hav Hst.
    destruct (wstep_pending_inv Hp Hh Hst) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@read_file_inv (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov)) in Hspec.
    unfold file_read_bytes, read_file_model, read_file_eff in Hspec. autorewrite with sys_input in Hspec. fold bs in Hspec.
    inversion Hspec; subst.
    destruct (read_file_model_props ms m p off bs) as [Hvs Hh1].
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [| rewrite Hh1, Hh in Hc; discriminate].
    unfold syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes app] in Hm.
    fold (read_accesses (ms_gpr ms 1) bs) in Hm.
    rewrite (proj1 (materialize_prepaid segs _ tp _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav))) in Hm.
    injection Hm as <-.
    rewrite advance_apply_delivered, app_nil_r. reflexivity.
  Qed.

  Lemma wstep_read_file_introA : ltac2:(tb__ "0|d|
SaS31Q40M0A1M1A1SaS17A1M2S4S15G1S55G1SaS31Q8A1M3A1M4G4S0SbG1A1M5S5R7A1SdG1R5A2A3S0G5S16R7A1SeG1A1A3S46Vsegs;R8RbA3S0S3cS32G0R8A2Z3fA3S0SbS18A1S1bS19RaA1S3dS3RbU0M6A2A1A2SdS18S1dR8R7A2A2A3S0SbG4A1M7S57S1fRbA1R9A2SdG4R7A2M8A3S0G7S28S7Vsegs;RdA2S3RdU1M9A2S3RdU2MaA2A3G8A3S4aS32G0S3ReGaA2A2S26A2S4aS4bS32G0S3RfG9A2A2S32G0S3RfGaA2A2A2S1eA2S56RbRcS3R10GaA2A3G4S44S45R10R13A2S54S3R11G9A2R1A2A2S3fVsegs;ScG2S36R13S35R12R11A2A4ScG2S36R13S35S43R12S5eG3R2A2MbS9S8R12A1S3R12G9A2McR2A3A3S47S29S27S19R11A1S3dS3R12G6A2A1S1dRfS33G0ReGbA3A2A3R11A2S54GcR2A2A2A2A4A3F_;Tbs;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;Ftr;Ftp;").
  Proof using .
    intros tp tr ms m x8 p off data wdst Hp Hh HMI Hno Hfd Hfs Hw Hcnt Hov bs Hav.
    destruct (read_file_model_props ms m p off bs) as [Hvs Hh1].
    pose proof (@read_file_intro (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov)) as Hs.
    unfold file_read_bytes, read_file_model, read_file_eff in Hs. autorewrite with sys_input in Hs. fold bs in Hs.
    pose proof (@wstep_run_accA tp tr ms m x8 _ _ [] Hp Hh Hs) as W. rewrite Hh1 in W.
    specialize (W Hh (vm_same_MI segs _ _ tp Hvs HMI)).
    unfold syscall_effect_accesses in W. cbn [eff_copyins eff_writes app] in W.
    fold (read_accesses (ms_gpr ms 1) bs) in W.
    specialize (W (ranges_avoid_vm_same _ _ tp _ Hvs Hav)).
    rewrite app_nil_r, advance_apply_delivered in W. exact W.
  Qed.

  Lemma read_file_only_okA : ltac2:(tb__ "0|7|
SaS31Q40M0A1M1A1S4S15G1S55G1SaS31Q8A1A1M2G2S0SbG1A1S16R6A1SeG1A1A3S46Vsegs;R7R9A3S0S3cS32G0R7A2Z3fA3S0SbS18A1S1bS19R9A1S3dS3RaU0A2A1A2SdS18S1dR7R6A2A2A3S0SbG2A1M3S57S1fRaA1R8A2SdG2R6A2M4A3S0G3S28S7Vsegs;RcA2S3RcU1M5A2S3RcU2M6A2A3G4A3S4aS32G0S3RdG6A2A2S26A2S4aS4bS32G0S3ReG5A2A2S32G0S3ReG6A2A2A2S1eA2S44S45ReR10A2S54S3RfG5A2S56RaRbS3RfG6A2A3A2A2S4dS37Vsegs;R10ReA3RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwdst;Fdata;Foff;Fp;Fx8;Fm;Fms;Ftp;").
  Proof using .
    intros tp ms m x8 p off data wdst Hh HMI Hno Hfd Hfs Hw Hcnt Hov Hav.
    destruct (read_file_model_props ms m p off (file_read data off (ms_gpr ms 2))) as [Hvs Hh1].
    split.
    - intros Hun. pose proof (@read_file_inv (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov) _ Hun). discriminate.
    - intros eff m' evs Hs Hh'.
      pose proof (@read_file_inv (sys_input segs ms x8) m Hno p off data wdst Hfd Hfs Hw Hcnt (rd_access_ok _ _ Hov) _ Hs) as E.
      unfold file_read_bytes, read_file_model, read_file_eff in E. autorewrite with sys_input in E.
      inversion E; subst.
      unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
      fold (read_accesses (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))).
      rewrite (proj1 (materialize_prepaid segs _ tp _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav))). discriminate.
  Qed.

  Lemma wstep_read_dir_invA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2S40S0SbG2A1M3S5R4A1SdG2R2A2A3S0G3S16R4A1SeG2A1A3S0S3cS32G1R4A2Z3fA3S0SbS18A1S1bS19R6A1S3dS3R7U0A2A1A2SdS18S25A2A3S4aS4bS32G1S3R8U1A2A2S32G1S3R8U2A2A2A2S1eA2S3fVsegs;ScG0S36RaS35R9R8A2A4R6A3S0S40R7ScG0S36RbS35S41RaS21S2aA1A2R9A2A4A3F_;F_;F_;F_;F_;F_;Fw';Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 w' Hp Hh Hno Hfd Hov Hst.
    refine (@wstep_ret_inv0A _ _ _ _ _ _ _ Hp Hh _ Hh Hst).
    intros R. exact (@read_dir_inv (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov) R).
  Qed.

  Lemma wstep_read_dir_introA : ltac2:(tb__ "0|4|
SaS17A1M0S4S15S31Q40M1A1M2S0SbG2A1M3S5R3A1SdG2R1A2A3S0G3S16R3A1SeG2A1A3S0S3cS32G1R3A2Z3fA3S0SbS18A1S1bS19R5A1S3dS3R6U0A2A1A2SdS18S25A2A3S4aS4bS32G1S3R7U1A2A2S32G1S3R7U2A2A2A2S1eA2S3fVsegs;ScG0S36R9S35R8R7A2A4ScG0S36R9S35S41R8S21S2aA1A2R7A2A4A3F_;F_;F_;F_;F_;Fx8;Fm;Fms;Ftr;").
  Proof using .
    intros tr ms m x8 Hp Hh Hno Hfd Hov.
    refine (@wstep_ret_intro0A tr _ _ _ _ _ Hp Hh _ Hh).
    exact (@read_dir_intro (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov)).
  Qed.

  Lemma read_dir_only_okA : ltac2:(tb__ "0|1|
S4S15S31Q40M0A1S0S3cS32G0R1A2Z3fA3S0SbS18A1S1bS19R3A1S3dS3R4U0A2A1A2SdS18S25A2A3S4aS4bS32G0S3R5U1A2A2S32G0S3R5U2A2A2A2S1eA2S4dS37Vsegs;R6R4A3R5A2F_;F_;F_;Fx8;Fm;Fms;").
  Proof using .
    intros ms m x8 Hno Hfd Hov. eapply only_okA_ret.
    intros R. exact (@read_dir_inv (sys_input segs ms x8) m Hno Hfd (rd_access_ok _ _ Hov) R).
  Qed.

End WithSegs.
