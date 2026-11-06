(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "obj_ext"; "@Corelib.Init.Datatypes"; "Some"; "option"; "list"; "pair"; "nat"; "bool"; "length"; "None"; "prod"; "false"; "nil"; "app"; "cons"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "FdEntry"; "event"; "m_fds"; "fd_lookup"; "m_halted"; "FdFile"; "m_fs"; "FdChannel"; "TASK_SIZE"; "read_bytes_aux"; "read_bytes_map"; "read_cstr"; "FdDir"; "read_u64"; "MAX_RW_COUNT"; "errno_ret"; "EISDIR"; "ENOTTY"; "fd_insert"; "iov_prefix_accesses"; "with_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "reg_sv"; "sv"; "eval"; "SLit"; "sobj"; "valuation"; "cell"; "soff"; "mkObj"; "ss_pc"; "ss_objs"; "DUnknown"; "SVar"; "agree_below"; "c_off"; "c_width"; "odefault"; "smatch"; "mkCell"; "sstate"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "smatchA"; "ok_frameA"; "hidz"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "ms_mem"; "ms_read_byte"; "write_to_mem"; "ms_svc_pending"; "ms_writable_byte"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "pow"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "vm_same"; "A_after"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.WithSegs.ReadBufA"; "rbA_bs"; "rbA_md'"; "rhA_rho'"; "rkA_rho'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "model_idle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "range_avoids"; "ranges_avoid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.WithSegs"; "A_after_fresh"; "A_after_hdr"; "A_after_write"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "hid"; "vms"; "MI"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "file_read"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "after_sys_mem"; "closed_model"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "cmd32"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "word_to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "close_md'"; "hdr_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.WithSegs.CloseA"; "closeA'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.WithSegs.IoctlA"; "ioctlA'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.WithSegs.ReadDirA"; "dirA'"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "openat_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "AT_FDCWD_word"; "O_RD_LARGEFILE"; "cstr_no_slash"; "openat_post"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "TIOCGWINSZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "S_after_write"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA"; "read_accesses"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SysOpen SysRead SysExtra.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysStepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatch_model_swap : ltac2:(tb__ "0|1|
S35S43S9S1bA1M0S50S19G0S19S41Vsegs;R7R6SaG0S4bR5S4cR4R3A2A4A4S6dR2A1S41Vsegs;R9R8SaG0S4bR4S4cR6R3A2A4A4F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' Hsm Hi.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch. cbn [fst snd cfg_ms cfg_model] in *. repeat (split; [assumption|]). exact Hfacts.
Qed.

Definition A_after_fresh (A : axst) : axst := ltac2:(tb__ "0|2|
S5VA;S65S3VA;A1M0S3cS2fG0A1M1A1S3aG0A1S61G1A1A4A2").

Lemma A_after_fresh_next : ltac2:(tb__ "0|0|
S4S0S4fS2fS3S70R1A1A1A1S61S2fS3R1A1A1A1A3FA;").
Proof using . intros A. reflexivity. Qed.

Lemma smatchA_after_ret_fresh : ltac2:(tb__ "0|2|
S35S9S15Q40A1M0A1S4S9S1bA1M1S50S19G1S19G0S5dVsegs;R9R8R7SaG1S4bR6S4cR5R4A2A4A5S0S8G0A1S1eR3A1SeG0A1A3S5fR6R4A2S48Vsegs;S64RcS2fS3RaA1A1R4A3RbS70RaA1SaG1S4bR6S4cS7bR8R4A2R5A2A4A5F_;F_;F_;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' r HspA Hh' Hvs. pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  set (rho' := rho_set_rw rho (ss_next (ax_S A)) r).
  assert (Hag : agree_below (ss_next (ax_S A)) rho rho') by (apply agree_below_set_rw; lia).
  split; [|split; [eapply vm_same_MI; eauto | split; [| split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after_fresh ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    apply (smatch_after_ret segs rho (ax_S A) tr (vms md tp ms) (vmd md)); [exact Hsp|].
    apply model_idle_vmd. exact Hh'.
  - eapply axwf_stable; [exact Hwf | cbn; lia | reflexivity | reflexivity].
  - eapply shadow_ok_stable; [exact Hag | exact Hwf | exact (smatch_pendingA_swf segs _ _ _ _ HspA) | reflexivity | reflexivity | | exact Hsh].
    unfold A_after_fresh, ax_setS. cbn [ax_S]. unfold S_after, exts. cbn. reflexivity.
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Lemma triple1_openatA : ltac2:(tb__ "0|6|
S6aOF_;S46S46S4S35S9S15Q40M0A1M1A1S49Vsegs;R6R5A3S5eVsegs;R7R6A3S47Vsegs;S2fS3R5A1A1R7A3S47Vsegs;S61S2fS3R6A1A1A1R7A3S0S8S62A1S73Vsegs;S39S3R7A1A1A2S7S62S63A2A3S0S31S30S3R8A1Z11A2S33Z38M2A1A3S0S31S30S3R9A1ZaA2S33S8eA1A3S0S31S30S3RaA1ZcA2S33S8fA1A3S9S1bA1M3S50S19S5dVsegs;RdRcReSaG3S4bR3S4cR2R1A2A4M4A5R11ReRdR4R2A4S6fS75R3ReA2S8dS4dVsegs;R4S16G0G2A2A3A1A2F_;F_;Fmd;Fms;Ftr;G3S50S19S5dVsegs;ReRdRfG4A5R12RfReR4R2A4S90S25S53R4A1S32R10S30S3R11A1ZbM5A2A2A2A1F_;F_;Fmd;Fms;Ftr;G3S50S19G1S19S5dVsegs;R11R10R12SaG3S4bR5S4cR4R3A2A4A5R15R12R11R6R4A4S91R5S25S53R6A1S32R13S30S3R14A1G5A2A2A2R4R3A4R16S64R14S2fS3R15A1A1R5A3R13R8R4A4F_;F_;F_;Fmd';Fr;Fmd;Fms;Ftr;S6cVsegs;R11S45Vsegs;R10ReRdRcA5S6aS2S35S35S1S3dS2fS3R10A1A1RfR1A3S45Vsegs;R11S70R10A1R1ReR2A6A2Lrho';A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FA;FJ';FJ;Fok;").
Proof using .
  intros ok J J' A rho tp Hokf Hokp Hst Hst' Hi H17 H10 H12 Hpath HNS HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  assert (H56 : bv_unsigned (Z_to_bv 64 56) = 56%Z) by reflexivity.
  assert (Hfl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z) by (rewrite G2; apply ldiff_rd_largefile).
  assert (Hdir : fd32 (ms_gpr ms 0) = AT_FDCWD32) by (rewrite G0; apply fd32_at_fdcwd_word).
  pose proof (Hpath tr ms md Hsp Hk) as Hav.
  pose proof (HNS tr ms md Hsp Hk) as Hns. rewrite <- G1 in Hns.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply openat_rd_only_okA; [exact Hh | exact HMI | exact H56 | exact Hfl | exact Hdir | exact Hns | exact Hav].
  - intros w' Hw.
    destruct (wstep_openat_rd_invA segs tp tr ms md _ w' Hp Hh HMI H56 Hfl Hdir Hns Hav Hw) as (r & md' & Hpost & ->).
    assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) r)) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next (ax_S A)) r). split; [exact Hag|].
    destruct (openat_post_vm_same _ _ _ _ Hpost) as [Hvs Hh'].
    assert (HMI' : MI segs md' tp) by (eapply vm_same_MI; eauto).
    assert (Hav' : ranges_avoid (hid md' tp) (openat_reads (sys_input segs ms (Z_to_bv 64 56)))).
    { intros a n Hin k Hk'. rewrite (vm_same_hid md md' tp Hvs). exact (Hav a n Hin k Hk'). }
    destruct (md_after_props segs tp md' _ HMI' Hav') as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|].
      eapply smatchA_after_ret_fresh; [exact Hsp | rewrite Hh'; exact Hh | exact Hvs].
    + eapply Hst'; [apply agree_below_refl | exact Hme |].
      eapply HK; [exact Hsp | exact Hk |]. rewrite <- G1. exact Hpost.
Qed.

Lemma etriple_openatA : ltac2:(tb__ "0|7|
S46S46S4S35S9S15Q40M0A1M1A1S47Vsegs;S2fS3R3A1A1R5A3S47Vsegs;S61S2fS3R4A1A1A1R5A3S0S8S62A1S73Vsegs;S39S3R5A1A1A2S7S62S63A2A3S0S31S30S3R6A1Z11A2S33Z38M2A1A3S0S31S30S3R7A1ZaA2S33S8eA1A3S0S31S30S3R8A1ZcA2S33S8fA1A3S9S1bA1M3S50S19S5dVsegs;RbRaRcSaG3S4bR3S4cR2R1A2A4M4A5RfRcRbR4R2A4S6fS75R3RcA2S8dS4dVsegs;R4S16G0G2A2A3A1A2F_;F_;Fmd;Fms;Ftr;G3S50S19S5dVsegs;RcRbRdG4A5R10RdRcR4R2A4S1S90S25S53R4A1S32ReS30S3RfA1ZbM5A2A2A2A1S2G1G1S2S19S19S1S91R5S25S53R6A1S32R10S30S3R11A1M6G5A2A2A2R2R1A4R12S64R10S2fG6A1R2A3RfR7R1A4A2Lmd';A2Lr;A2A2F_;F_;Fmd;Fms;Ftr;S6bVsegs;S45Vsegs;RdRbRaR9A5S6aS2S35S35S1S3dS2fS3RdA1A1RcR1A3S45Vsegs;ReS70RdA1R1RbR2A6A2Lrho';A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FA;FJ';FJ;").
Proof using .
  intros J J' A rho tp Hst Hst' Hi H17 H10 H12 Hpath HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  assert (H56 : bv_unsigned (Z_to_bv 64 56) = 56%Z) by reflexivity.
  assert (Hfl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z) by (rewrite G2; apply ldiff_rd_largefile).
  assert (Hdir : fd32 (ms_gpr ms 0) = AT_FDCWD32) by (rewrite G0; apply fd32_at_fdcwd_word).
  pose proof (Hpath tr ms md Hsp Hk) as Hav.
  destruct (HK tr ms md Hsp Hk) as (Hns & r & md' & Hpost & Hk').
  rewrite <- G1 in Hpost. rewrite <- G1 in Hns.
  destruct (openat_post_vm_same _ _ _ _ Hpost) as [Hvs Hh'].
  assert (HMI' : MI segs md' tp) by (eapply vm_same_MI; eauto).
  assert (Hav' : ranges_avoid (hid md' tp) (openat_reads (sys_input segs ms (Z_to_bv 64 56)))).
  { intros a n Hin k Hk''. rewrite (vm_same_hid md md' tp Hvs). exact (Hav a n Hin k Hk''). }
  destruct (md_after_props segs tp md' _ HMI' Hav') as (Hme & _).
  eexists. split; [exact (wstep_openat_rd_introA segs tp tr ms md _ r md' Hp Hh HMI H56 Hfl Hdir Hns Hav Hpost)|].
  assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) r)) by (apply agree_below_set_rw; lia).
  exists (rho_set_rw rho (ss_next (ax_S A)) r). split; [exact Hag|].
  split.
  - eapply smatchA_mat_equiv; [exact Hme|].
    eapply smatchA_after_ret_fresh; [exact Hsp | rewrite Hh'; exact Hh | exact Hvs].
  - eapply Hst'; [apply agree_below_refl | exact Hme | exact Hk'].
Qed.

Definition A_after_write (A : axst) (e : sv) : axst := ltac2:(tb__ "0|0|
S5VA;S93S3VA;A1Ve;A2A2").

Lemma A_after_write_next : ltac2:(tb__ "0|0|
S4S31S0S4fS2fS3S72R2R1A2A1A1S61S2fS3R2A1A1A1A3Fe;FA;").
Proof using . intros A e. reflexivity. Qed.

Lemma smatchA_after_write : ltac2:(tb__ "0|5|
S35S9S15Q40M0A1M1A1S4S9S1bA1M2S50S19G2S19S31S4eSbS5dVsegs;RbRaR9SaG2S4bR8S4cR7R6A2A4A5S0S8G1A1S1eR5A1SeG1A1A3S5fR8R6A2S0ScS44S2fS3RcA1A1R6A2S14A3S0S4eS17G0S32RfR7A2A2R6A3S1S57Z1S59R6A1M3A2S57G3R7A2A2S48Vsegs;S64R11S2fS3RfA1A1S16G0S59R7A1A2M4A3R10S72RfR9A2SaG2S4bRbS4cS7bRdG4A2RaA2A4A5F_;F_;F_;F_;F_;F_;Fk;Fn;Fe;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' e n k HspA Hh' Hvs He Hn Hk. pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  set (rho' := rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat k))).
  assert (Hag : agree_below (ss_next (ax_S A)) rho rho') by (apply agree_below_set_rw; lia).
  split; [|split; [eapply vm_same_MI; eauto | split; [| split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after_write ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    apply (smatch_model_swap _ _ tr _ (vmd md)); [| apply model_idle_vmd; exact Hh'].
    exact (smatch_after_write segs rho (ax_S A) tr (vms md tp ms) (vmd md) tr e n k Hsp He Hn Hk).
  - eapply axwf_stable; [exact Hwf | cbn; lia | reflexivity | reflexivity].
  - eapply shadow_ok_stable; [exact Hag | exact Hwf | exact (smatch_pendingA_swf segs _ _ _ _ HspA) | reflexivity | reflexivity | | exact Hsh].
    unfold A_after_write, ax_setS. cbn [ax_S]. unfold S_after_write, S_after, add_fact, exts. cbn. reflexivity.
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Lemma read_bytes_aux_mono : ltac2:(tb__ "0|6|
S15Q40A1M0S8S15Q8A1M1A1M2F_;M3G3G0G1S0G2R4R2A1S7G1R1A2A3S0G2R4R3A1S7G1R2A2A3F_;Fb;Fa;SbG0S9G1A1M4S0S8G4A1M5S23R6R2R3A3S7G4R1A2A3S0G5S23R6R3R4A3S7G4R2A2A3F_;Fbs;Fa;Fk;F_;Fg;Ff;").
Proof using .
  intros f g Hfg k. induction k as [|k IH]; intros a bs H; cbn in H |- *; [exact H|].
  destruct (f a) as [b|] eqn:Hb; [|discriminate]. rewrite (Hfg _ _ Hb).
  destruct (read_bytes_aux f (a + 1)%bv k) as [r|] eqn:Hr; [|discriminate].
  rewrite (IH _ _ Hr). exact H.
Qed.

Lemma read_bytes_map_mono : ltac2:(tb__ "0|6|
S15Q40A1M0S8S15Q8A1M1A1M2F_;M3G3G0G0S9G1A1M4G0G1S0G2R7R2A1S7G1R1A2A3S0G2R7R3A1S7G1R2A2A3F_;Fb;Fa;S0S8G4A1M5S24R6R4R3A3S7G4R2A2A3S0G5S24R6R5R4A3S7G4R3A2A3F_;F_;Fbs;Flen;Fa;Fg;Ff;").
Proof using . intros f g a len bs Hfg H. rewrite read_bytes_map_eq in H |- *. eapply read_bytes_aux_mono; eauto. Qed.

Lemma read_u64_mono : ltac2:(tb__ "0|5|
S15Q40A1M0S8S15Q8A1M1A1M2F_;M3G3G0G0G0G1S0G2R6R2A1S7G1R1A2A3S0G2R6R3A1S7G1R2A2A3F_;Fb;Fa;S0S8G0A1M4S27R5R3A2S7G0R2A2A3S0G4S27R5R4A2S7G0R3A2A3F_;F_;Fv;Fa;Fg;Ff;").
Proof using .
  intros f g a v Hfg H. unfold read_u64 in H |- *.
  destruct (read_bytes_map f a (Z_to_bv 64 8)) as [bs|] eqn:Hb; [|discriminate].
  rewrite (read_bytes_map_mono f g _ _ _ Hfg Hb). exact H.
Qed.

Lemma vms_read_byte_hid : ltac2:(tb__ "0|3|
S35S9S15Q40A1M0A1S4S9S1bA1M1S50S19G0S15Q8A1M2S5dVsegs;R8R7R6SaG1S4bR5S4cR4R3A2A4A5S0S8G2A1S53S76R4R8R5A3R3A2S7G2R2A2A3S0ScS75R5R9R4A3S10A3F_;F_;Fb;Fa;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md a b HspA H. pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ HspA) as Hsp. pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ HspA) as HMI.
  pose proof (smatch_pending_rom segs _ _ _ _ _ Hsp) as Hrom.
  unfold ms_read_byte in H. rewrite vms_mem in H.
  destruct (hid md tp a) eqn:Hh; [|reflexivity]. exfalso.
  pose proof (Hrom a) as R. rewrite R in H. unfold image_byte in H.
  pose proof (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) a Hh) as Hoff.
  unfold memory_read in H. replace (Z.of_N 1) with 1 in H by reflexivity. rewrite Hoff in H. discriminate.
Qed.

Lemma read_bytes_aux_avoids : ltac2:(tb__ "0|4|
S15Q40A1M0S8S15Q8A1M1A1M2F_;G0ScF_;G0G1S0G2R4R2A1S7G1R1A2A3S0ScR4R3A1S10A3F_;Fb;Fa;SbG0S9G1A1M3S0S8G3A1S23R6R2R3A3S7G3R1A2A3S6eR6R3R4A3F_;Fbs;Fa;Fk;F_;FH;Ff;").
Proof using .
  intros f H Hf k. induction k as [|k IH]; intros a bs Hr i Hi; [lia|].
  cbn in Hr. destruct (f a) as [b|] eqn:Hb; [|discriminate].
  destruct (read_bytes_aux f (a + 1)%bv k) as [r|] eqn:Hr'; [|discriminate].
  destruct i as [|i].
  - rewrite woff_0. exact (Hf _ _ Hb).
  - specialize (IH _ _ Hr' i ltac:(lia)). rewrite woff_succ in IH. exact IH.
Qed.

Lemma read_bytes_aux_length : ltac2:(tb__ "0|3|
S15Q40A1M0S8S15Q8A1M1A1F_;SbG0S9G1A1M2S0S8G2A1S23R4R2R3A3S7G2R1A2A3S0SbSdG1R2A2R4A3F_;Fbs;Fa;Fk;Ff;").
Proof using .
  intros f k. induction k as [|k IH]; intros a bs H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (f a) as [b|]; [|discriminate]. destruct (read_bytes_aux f (a + 1)%bv k) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. cbn. rewrite (IH _ _ Hr). reflexivity.
Qed.

Lemma read_bytes_map_avoids : ltac2:(tb__ "0|4|
S15Q40A1M0S8S15Q8A1M1A1M2F_;G0ScF_;G0G0S9G1A1M3G0G1S0G2R7R2A1S7G1R1A2A3S0ScR7R3A1S10A3F_;Fb;Fa;S0S8G3A1S24R6R4R3A3S7G3R2A2A3S6eR6R5SdG1R3A2A3F_;F_;Fbs;Flen;Fa;FH;Ff;").
Proof using .
  intros f H a len bs Hf Hr. rewrite read_bytes_map_eq in Hr.
  rewrite (read_bytes_aux_length _ _ _ _ Hr). exact (read_bytes_aux_avoids f H Hf _ _ _ Hr).
Qed.

Lemma range_avoids_le : ltac2:(tb__ "0|1|
S15Q40A1M0ScF_;G0SbSbS78R1R2A2S6eR5R4R3A3S6eR6R5R3A3F_;F_;Fm;Fn;Fa;FH;").
Proof using . intros H a n m Hle Hr k Hk. apply Hr. lia. Qed.

Lemma read_u64_avoids : ltac2:(tb__ "0|3|
S15Q40A1M0S8S15Q8A1M1A1M2F_;G0ScF_;G0G0G0G1S0G2R6R2A1S7G1R1A2A3S0ScR6R3A1S10A3F_;Fb;Fa;S0S8G0A1S27R5R3A2S7G0R2A2A3S6eR5R4U8A3F_;F_;Fv;Fa;FH;Ff;").
Proof using .
  intros f H a v Hf Hr. unfold read_u64 in Hr.
  destruct (read_bytes_map f a (Z_to_bv 64 8)) as [bs|] eqn:Hb; [|discriminate].
  pose proof (read_bytes_map_avoids f H a _ bs Hf Hb) as X.
  rewrite read_bytes_map_eq in Hb. rewrite (read_bytes_aux_length _ _ _ _ Hb) in X. exact X.
Qed.

Lemma read_u64x2_avoids16 : forall (f : word -> option byte) (H : word -> bool) a v1 v2,
  (forall a b, f a = Some b -> H a = false) ->
  read_u64 f a = Some v1 -> read_u64 f (a + 8)%bv = Some v2 -> range_avoids H a 16.
Proof using .
  intros f H a v1 v2 Hf H1 H2 k Hk.
  destruct (Nat.lt_ge_cases k 8) as [Hlt|Hge].
  - exact (read_u64_avoids f H a v1 Hf H1 k Hlt).
  - pose proof (read_u64_avoids f H _ v2 Hf H2 (k - 8)%nat ltac:(lia)) as X.
    rewrite <- X. unfold woff. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
    assert (H8 : bv_unsigned (8 : word) = 8%Z) by reflexivity. rewrite H8.
    unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma iov_prefix_accesses_in : ltac2:(tb__ "0|2|
S9SfS15Q40A1M0G0A2M1A1SbG0SbS81SfG0SbA2SaG0SbR2R1A4S2dR4R3A2A3S2G0G0S1S81G1SaG0G0R4R1A4R6A3S78R3S83R1A1A2A2Ll;A2F_;Fn;Fa;Fk;Fiovs;").
Proof using .
  induction iovs as [|[b l] r IH]; intros k a n H.
  - destruct k; cbn in H; contradiction.
  - destruct k as [|k']; [cbn in H; contradiction|].
    cbn [iov_prefix_accesses] in H. rewrite word_to_nat_bounded_eq_min in H.
    destruct (Nat.eqb (Nat.min (word_to_nat l) (S k')) 0) eqn:E.
    + destruct (IH _ _ _ H) as (l' & Hin & Hle). exists l'. split; [right; exact Hin | exact Hle].
    + destruct H as [H|H].
      * injection H as <- <-. exists l. split; [left; reflexivity | lia].
      * destruct (IH _ _ _ H) as (l' & Hin & Hle). exists l'. split; [right; exact Hin | exact Hle].
Qed.

Lemma iov_desc2_avoid : forall rho tp A tr ms md a v1 v2 v3 v4,
  smatch_pendingA segs rho tp A (tr, mkCfg ms md) ->
  read_u64 (ms_read_byte (vms md tp ms)) a = Some v1 ->
  read_u64 (ms_read_byte (vms md tp ms)) (a + 8)%bv = Some v2 ->
  read_u64 (ms_read_byte (vms md tp ms)) (a + 16)%bv = Some v3 ->
  read_u64 (ms_read_byte (vms md tp ms)) (a + 16 + 8)%bv = Some v4 ->
  ranges_avoid (hid md tp) (iov_desc_accesses a 2).
Proof using .
  intros rho tp A tr ms md a v1 v2 v3 v4 HspA R1 R2 R3 R4 a' n Hin.
  cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  - eapply read_u64x2_avoids16; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ HspA Hb) | exact R1 | exact R2].
  - eapply read_u64x2_avoids16; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ HspA Hb) | exact R3 | exact R4].
Qed.

Lemma iov_desc1_avoid : forall rho tp A tr ms md a v1 v2,
  smatch_pendingA segs rho tp A (tr, mkCfg ms md) ->
  read_u64 (ms_read_byte (vms md tp ms)) a = Some v1 ->
  read_u64 (ms_read_byte (vms md tp ms)) (a + 8)%bv = Some v2 ->
  ranges_avoid (hid md tp) (iov_desc_accesses a 1).
Proof using .
  intros rho tp A tr ms md a v1 v2 HspA R1 R2 a' n Hin.
  cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-.
  eapply read_u64x2_avoids16; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ HspA Hb) | exact R1 | exact R2].
Qed.

Lemma ranges_avoid_app : ltac2:(tb__ "0|3|
S15Q40A1M0ScF_;S9SfG0SbA2M1A1M2G2S6fR3R2A2S6fR4R2A2S6fR5S12G1R4R3A3A2F_;F_;Fl2;Fl1;FH;").
Proof using . intros H l1 l2 A1 A2 a n Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (A1 a n Hin) | exact (A2 a n Hin)]. Qed.

Lemma triple1_writev2A : forall (ok : world -> Prop) (J J' : jpredA) A rho tp ch bs1 bs2 e,
  ok_frameA segs ok J -> ok_pframeA segs ok J -> stableA segs (ss_next (ax_S A)) J ->
  stableA segs (Pos.succ (ss_next (ax_S A))) J' ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 2 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next (ax_S A)) e = true ->
  (forall rho' tr md k, agree_below (ss_next (ax_S A)) rho rho' ->
     rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tp tr md -> (1 <= k <= length (bs1 ++ bs2))%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' tp (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k (bs1 ++ bs2))) md) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte (vms md tp ms)) ((eval rho (reg_sv (ax_S A) 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPA segs J A rho tp)
    (fun w => exists rho', agree_below (ss_next (ax_S A)) rho rho' /\ SPA segs J' (A_after_write A e) rho' tp w).
Proof using .
  intros ok J J' A rho tp ch bs1 bs2 e Hokf Hokp Hst Hst' Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & b2 & l2 & R1 & R2 & R3 & R4 & B1 & B2 & Hev & Hiok & Hok1 & Hok2). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  pose proof (read_u64_mono _ _ _ _ LIFT R3) as R3'. pose proof (read_u64_mono _ _ _ _ LIFT R4) as R4'.
  pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B1) as B1'. pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B2) as B2'.
  rewrite <- G1 in R1', R2', R3', R4'.
  assert (Hav : forall k, ranges_avoid (hid md tp) (writev2_reads (sys_input segs ms (Z_to_bv 64 66)) b1 l1 b2 l2 k)).
  { intros k. unfold writev2_reads, writev_reads. autorewrite with sys_input. apply ranges_avoid_app.
    - rewrite G1. eapply iov_desc2_avoid; [exact Hsp | exact R1 | exact R2 | exact R3 | exact R4].
    - intros a n Hin. destruct (iov_prefix_accesses_in _ _ _ _ Hin) as (l & Hinl & Hle).
      destruct Hinl as [E|[E|[]]]; injection E as <- <-.
      + eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B1]].
        rewrite read_bytes_map_eq in B1. rewrite (read_bytes_aux_length _ _ _ _ B1). exact Hle.
      + eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B2]].
        rewrite read_bytes_map_eq in B2. rewrite (read_bytes_aux_length _ _ _ _ B2). exact Hle. }
  assert (Hag1 : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    eapply writev2_only_okA; [exact Hh | exact HMI | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1' | exact R2' | exact R3' | exact R4' | exact B1' | exact B2' | exact Hiok | exact Hok1 | exact Hok2 | exact Hlen | exact Hav].
  - intros w' Hw.
    destruct (wstep_writev2_invA segs tp tr ms md _ _ _ _ _ _ _ _ w' Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' R3' R4' B1' B2' Hiok Hok1 Hok2 Hlen Hav Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    destruct (md_after_props segs tp md _ HMI (Hav k)) as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|].
      eapply smatchA_after_write; [exact Hsp | exact Hh | apply vm_same_refl | exact He | exact Hev | lia].
    + eapply Hst'; [apply agree_below_refl | exact Hme |].
      exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1)).
Qed.

Lemma vms_after_sys_mem_kwrite : ltac2:(tb__ "0|3|
S19S9S15Q40A1M0A1S50G0G0S9S15Q8A1M1A1S6eS75R6R5A2R2SdG1R1A2A3S0S50S76R7R6S7cR5R4S54S52R5A1R3R2A3A3A3S7cS76R7R6R5A3M2R4S54S52G2A1R3R2A3A3A3F_;Fbs;Fbuf;Fr;Fms;Ftp;Fmd;").
Proof using .
  intros md tp ms r buf bs Hav. unfold vms, restrict, after_sys_mem.
  cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite (write_to_mem_restrict (hid md tp) bs (ms_mem ms) buf Hav). reflexivity.
Qed.

Lemma hidz_after_kwrite : ltac2:(tb__ "0|2|
S19S19S9S15Q40A1M0A1S50G0G0S9S15Q8A1M1A1S4aR7R5R4A3S5fR8R7A2S6eS75R9R7A2R4SdG1R3A2A3S4aR9R8S7cR7R6S54S52R7A1R5R4A3A3A3F_;F_;F_;Fbs;Fbuf;Fr;Fms;Ftp;Fmd';Fmd;").
Proof using .
  intros md md' tp ms r buf bs Hhz Hvs Hav a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha.
  rewrite after_sys_memq, (write_to_mem_hidden (hid md tp) bs (ms_mem ms) buf a Hav Ha), (proj1 Hvs). exact (Hhz a Ha).
Qed.

Lemma smatchA_after_kwrite_keep : ltac2:(tb__ "0|4|
S35S9S15Q40M0A1M1A1S4S9S1bA1M2S50S19G2S19G1SbS31S31S31S4eS4eS9S36A1G1S9S15Q8A1M3A1S4eS5dVsegs;R13R12R11SaG2S4bR10S4cRfReA2A4A5S0S8G1A1S1eRdA1SeG1A1A3S5fR10ReA2S0S8S34A1S80S34S3aS3R14A1A1RdA3S7S34S38RcRbRaR7S3bA5A2A3S0S4eS37R17RcA2RaA3S0S4eS37R18RcA2RaA3S0S4eS17G0R9A2S58S17G0S32R19RfA2A2R7A2A3S57RdR8A2S57S58R9S59SdG3RaA2A1A2RdA2S89S36S36S57S58S37R1dS3eR1A1A2S3fR1A1A2RbA2Lc;RdA3S48Vsegs;S64R1dS2fS3R1bA1A1R15A3R1cS70R1bA1SaG2S4bR17S4cS7cR19R15S54S52R19A1RdRcA3A3R16A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' r k base elo ehi lo hi cells buf bs woff HspA Hh' Hvs Hnth Helo Hehi Hbuf Hlo Hhi Hcells.
  pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  assert (Hav : range_avoids (hid md tp) buf (length bs)).
  { eapply (range_in_obj_avoidsA segs rho tp A tr ms md (mkObj base elo ehi cells DUnknown));
      [exact HspA | eapply nth_error_In; exact Hnth | reflexivity | |];
      unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi fst snd]; [rewrite Helo; lia | rewrite Hehi; lia]. }
  set (rho' := rho_set_rw rho (ss_next (ax_S A)) r).
  assert (Hag : agree_below (ss_next (ax_S A)) rho rho') by (apply agree_below_set_rw; lia).
  split; [|split; [eapply vm_same_MI; eauto | split; [| split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after_fresh ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), (vms_after_sys_mem_kwrite md tp ms r buf bs Hav).
    rewrite virt_unfold in Hsp.
    eapply (smatch_after_kwrite_keep segs rho (ax_S A) tr (vms md tp ms) (vmd md) tr' (vmd md') r k base elo ehi lo hi cells buf bs woff);
      [exact Hsp | apply model_idle_vmd; exact Hh' | exact Hnth | exact Helo | exact Hehi | exact Hbuf | exact Hlo | exact Hhi | exact Hcells].
  - eapply axwf_stable; [exact Hwf | cbn; lia | reflexivity | reflexivity].
  - eapply shadow_ok_stable; [exact Hag | exact Hwf | exact (smatch_pendingA_swf segs _ _ _ _ HspA) | reflexivity | reflexivity | | exact Hsh].
    unfold A_after_fresh, ax_setS. cbn [ax_S]. unfold S_after, exts. cbn. reflexivity.
  - cbn [cfg_model cfg_ms snd]. eapply hidz_after_kwrite; [exact Hhz | exact Hvs | exact Hav].
Qed.

Lemma vms_writable_byte_someA : ltac2:(tb__ "0|4|
S35S9S15Q40A1M0A1S4S9S1bA1M1S50S19G0S15Q8A1M2S5dVsegs;R8R7R6SaG1S4bR5S4cR4R3A2A4A5S0S8G2A1M3S56Vsegs;S76R4R8R5A3R3A3S7G2R2A2A3S0G3S56Vsegs;R6R4A3S7G2R3A2A3F_;F_;Fb;Fa;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md a b HspA H. pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ HspA) as HMI.
  unfold ms_writable_byte, wview in H |- *. rewrite vms_mem in H.
  destruct (hid md tp a) eqn:Hh; [|exact H].
  exfalso. rewrite (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) a Hh) in H. discriminate.
Qed.

Definition A_after_hdr (A : axst) (k : nat) (base elo ehi : sv) : axst := ltac2:(tb__ "0|3|
S5VA;S65S3VA;A1M0S3cS61S2fG0A1M1A1M2A1S74S34S3aG0A1Vk;S38Vbase;Velo;Vehi;S13S36S42Velo;Z4S3cG1A1A3S11S36A1A3S3bA5A4S61G2A1A4A2").

Lemma exts_list_set_same : ltac2:(tb__ "0|2|
S9S34A1SbS31S31S31S9S36A1M0G0S40S40S0S8S34A1S80S34R9R8A3S7S34S38R7R6R5R4R2A5A2A3S0S9SfSfS31S31A2S31A2M1A1S8aS34G1S6S74S34RaR9S38R8R7R6R4R2A5A4A4S8aS34G1S6RaA4A3F_;Fd';Fd;Fcells';Fcells;Fehi;Felo;Fbase;Fk;Fobjs;").
Proof using .
  intros objs k base elo ehi cells cells' d d' Hnth. rewrite map_list_set.
  apply list_set_same. rewrite nth_error_map, Hnth. reflexivity.
Qed.

Lemma smatchA_after_kwrite_hdr : ltac2:(tb__ "0|5|
S35S9S15Q40M0A1M1A1S4S9S1bA1M2S50S19G2S19G1SbS31S31S31S4eS4eG1S9S15Q8A1M3A1S5dVsegs;R11R10RfSaG2S4bReS4cRdRcA2A4A5S0S8G1A1S1eRbA1SeG1A1A3S5fReRcA2S0S8S34A1S80S34S3aS3R12A1A1RbA3S7S34S38RaR9R8S11S36A1S3bA5A2A3S0S4eS37R15RaA2R8A3S0S4eS37R16RaA2R8A3S0S4eS17G0R8A2S58S17G0S32R17RdA2A2RaA2A3S57S58RbS59SdG3R8A2A1A2RaA2S78U4SdG3R9A2A2S48Vsegs;S64S64R1aS2fS3R18A1A1M4S85RaA1A3S61G4A1R12A3R19S71R18R11R10RfReA5SaG2S4bR14S4cS7cR16R12S54S52R16A1RbRaA3A3R13A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fbuf;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' r k base elo ehi lo hi buf bs HspA Hh' Hvs Hnth Helo Hehi Hbuf Hhi H4.
  pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  assert (Hav : range_avoids (hid md tp) buf (length bs)).
  { eapply (range_in_obj_avoidsA segs rho tp A tr ms md (mkObj base elo ehi [] DUnknown));
      [exact HspA | eapply nth_error_In; exact Hnth | reflexivity | |];
      unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi fst snd]; [rewrite Helo; lia | rewrite Hehi; lia]. }
  set (h := ss_next (ax_S A)). set (rho' := rho_set_rw (rho_set_rw rho h (hdr_val bs)) (Pos.succ h) r).
  assert (Hag : agree_below h rho rho').
  { subst rho'. eapply agree_below_trans; [apply (agree_below_set_rw rho h (hdr_val bs) h); lia | apply (agree_below_set_rw _ (Pos.succ h) r h); lia]. }
  split; [|split; [eapply vm_same_MI; eauto | split; [| split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after_hdr ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), (vms_after_sys_mem_kwrite md tp ms r buf bs Hav).
    rewrite virt_unfold in Hsp.
    eapply (smatch_after_kwrite_hdr segs rho (ax_S A) tr (vms md tp ms) (vmd md) tr' (vmd md') r k base elo ehi lo hi buf bs);
      [exact Hsp | apply model_idle_vmd; exact Hh' | exact Hnth | exact Helo | exact Hehi | exact Hbuf | exact Hhi | exact H4].
  - eapply axwf_stable; [exact Hwf | cbn; lia | reflexivity | reflexivity].
  - eapply shadow_ok_stable; [exact Hag | exact Hwf | exact (smatch_pendingA_swf segs _ _ _ _ HspA) | reflexivity | reflexivity | | exact Hsh].
    unfold A_after_hdr, ax_setS. cbn [ax_S]. unfold S_after, exts. cbn [ss_objs].
    eapply exts_list_set_same. exact Hnth.
  - cbn [cfg_model cfg_ms snd]. eapply hidz_after_kwrite; [exact Hhz | exact Hvs | exact Hav].
Qed.

Section ReadBufA.
Variable A : axst.
Variable rho : valuation.
Variable tp : list word.
Variable k : nat.
Variables base elo ehi : sv.
Variable cells : list cell.
Variables p data : list byte.
Variable off : Z.
Variable woff : Z.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S8S62A1S73Vsegs;S39S3VA;A1A1A2S7S62S63A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1Z11A2S33Z3fA1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1ZaA2S33Z3A1A3").
Hypothesis Hoff : 0 <= off < 2 ^ 64.

Hypothesis Hcnt : ltac2:(tb__ "0|0|
S57S17Q40S32Vrho;S30S3VA;A1ZcA2A2A2S28A2").
Hypothesis Hov : ltac2:(tb__ "0|2|
S57S58S17Q40M0S32Vrho;S30S3VA;A1M1ZbA2A2A2S17G0S32Vrho;S30G1ZcA2A2A2A2S22A2").
Hypothesis Hnth : ltac2:(tb__ "0|0|
S0S8S34A1S80S34S3aS3VA;A1A1Vk;A3S7S34S38Vbase;Velo;Vehi;Vcells;S3bA5A2A3").
Hypothesis Hbuf : ltac2:(tb__ "0|1|
S0S4eS17Q40M0S32Vrho;S30S3VA;A1ZbA2A2A2S58S17G0S32Vrho;Vbase;A2A2Vwoff;A2A3").
Definition rbA_bs : list byte := ltac2:(tb__ "0|1|
S8bS15Q8A1M0S5cS17Q40S32Vrho;S30S3VA;A1ZcA2A2A2A1S8cG0S5cVoff;A1Vdata;A3A3").
Hypothesis Hlo : ltac2:(tb__ "0|0|
S57S37Vrho;Velo;A2Vwoff;A2").
Hypothesis Hhi : ltac2:(tb__ "0|0|
S57S58Vwoff;S17Q40S32Vrho;S30S3VA;A1ZcA2A2A2A2S37Vrho;Vehi;A2A2").
Hypothesis Hcells : ltac2:(tb__ "0|0|
S89S36S36S57S58S37Vrho;S3eR1A1A2S3fR1A1A2Vwoff;A2Lc;Vcells;A3").

Definition rbA_md' (md : Model) : Model := ltac2:(tb__ "0|1|
S2eS2cS1cVmd;A1S16Q40M0Z3A2S1fVp;S18G0S16G0Voff;A2S82S15Q8A1S66A2A3A2A3Vmd;A2").

Lemma rbA_bs_len : ltac2:(tb__ "0|0|
S57S59SdS15Q8A1S66A2A1S17Q40S32Vrho;S30S3VA;A1ZcA2A2A2A2").
Proof using Hoff. unfold rbA_bs. rewrite length_firstn. pose proof (bv_unsigned_in_range 64 (eval rho (reg_sv (ax_S A) 12))). lia. Qed.

Lemma rbA_md'_vm_same : ltac2:(tb__ "0|1|
S19S1S5fR1S67R1A1M0A2S0S8S15Q40A1A1S1eG0A1S1eR1A1A3A2Fmd;").
Proof using . intros md. split; [apply vm_same_with_fds | reflexivity]. Qed.

Lemma read_buf_coreA : ltac2:(tb__ "0|e|
S9S1bA1M0S50S19S5dVsegs;Vrho;Vtp;VA;SaG0S4bR3S4cR2R1A2A4A5S0S8S1aA1M1S1dS1cR2A1S16Q40M2Z3A2M3A2S7S1aS1fVp;S16G2Voff;A2M4A2A2M5A3S0S8S9S15Q8A1A1M6A1M7S79S20R3A1Vp;A2S7G6Vdata;A2A3S2S15G2A1M8G8S2G6G6S1S0S8G8A1M9S55R7A1S7G8R2A2A3S1S0S4eS17G2R2A2Z3fA3S1S0G9S1eR6A1SeG8A1A3S1S77Vsegs;R6Vtp;A3S1S0G1S1dS1cR6A1S7eS51R7U0A2A1MaA2G5A3S1S0G7S24S56Vsegs;R7A2S51R7U1A2MbS51R7U2A2McA3S7G6R1A2A3S1S57S17G2GcA2MdS28A2S1S57S58S17G2GbA2GdA2S22A2S1S0G6S7aVdata;G4GcA3S66A3S1S0G8GbS32Vrho;S30S3VA;A1ZbA2A2A3S1S0G8GaG3A3S6fS75R6Vtp;A2S94GbS66A2A2A2A2A2A2A2A2A2A2A2A2A2Lwdst;A2Lx8;A2F_;F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hbuf Hcnt Hhi Hlo Hnth Hoff Hov.
  intros tr ms md HspA Hfd Hfs.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ HspA) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ HspA) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ HspA) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 HspA ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 HspA ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 HspA ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ HspA) as Hsp.
  pose proof (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem segs _ _ _ _ _ Hsp) Hnth) as Ho.
  destruct (read_bytes_map (ms_writable_byte segs (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) (eval rho (reg_sv (ax_S A) 12))) as [wdst|] eqn:Ewd.
  2:{ exfalso. apply (writable_range_obj segs rho (vms md tp ms) _ (eval rho (reg_sv (ax_S A) 11)) (eval rho (reg_sv (ax_S A) 12)) woff Ho eq_refl); [cbn [ob_base]; exact Hbuf | unfold obj_lo_of; cbn; exact Hlo | unfold obj_hi_of; cbn; exact Hhi | exact Ewd]. }
  pose proof (read_bytes_map_mono _ _ _ _ _ (fun x b Hb => vms_writable_byte_someA _ _ _ _ _ _ x b HspA Hb) Ewd) as Ewd'.
  rewrite <- G1, <- G2 in Ewd'.
  exists (Z_to_bv 64 63), wdst.
  assert (Hbs : file_read data (Z_to_bv 64 off) (ms_gpr ms 2) = rbA_bs).
  { unfold rbA_bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite G2. f_equal. f_equal. f_equal. apply Z_to_bv_small.
    rewrite two64. exact Hoff. }
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [exact HMI|]. split; [rewrite G0, fd32_3; exact Hfd|]. split; [exact Ewd'|].
  split; [rewrite G2; exact Hcnt|]. split; [rewrite G1, G2; exact Hov|]. split; [exact Hbs|]. split; [exact G1 |].
  split; [rewrite G0, fd32_3; reflexivity|].
  rewrite read_accesses_eq. destruct rbA_bs as [|b0 bs0] eqn:Ebs; [apply ranges_avoid_nil|].
  apply ranges_avoid_cons; [|apply ranges_avoid_nil]. rewrite <- Ebs.
  eapply (range_in_obj_avoidsA segs rho tp A tr ms md (mkObj base elo ehi cells DUnknown));
    [exact HspA | eapply nth_error_In; exact Hnth | reflexivity | |];
    unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi fst snd]; rewrite G1; [lia | pose proof rbA_bs_len; lia].
Qed.

Definition rkA_rho' : valuation := ltac2:(tb__ "0|0|
S64Vrho;S2fS3VA;A1A1S82S15Q8A1S66A2A3").

Theorem triple1_read_keepA : ltac2:(tb__ "0|4|
S6aOF_;S46S46S49Vsegs;R3R2A3S5eVsegs;R4R3A3S47Vsegs;S2fS3VA;A1A1M0R4A3S47Vsegs;S61G0A1R4A3S9S1bA1M1S19R8Vrho;Vtp;R2R1A4S1S0S8S1aA1S1dS1cR2A1S16Q40M2Z3A2A2S7S1aS1fVp;S16G2Voff;A2A2A2A3S0S8S9S15Q8A1A1M3A1S79S20R2A1Vp;A2S7G3Vdata;A2A3A2F_;Fmd;Ftr;G1S19R9Vrho;Vtp;R2R1A4R9S69Vtp;R3S67R2A1A4F_;Fmd;Ftr;S6cVsegs;R9S45Vsegs;R8VA;Vrho;Vtp;A5S45Vsegs;R7S70VA;A1S69Vtp;A5A4F_;F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcells Hcnt Hhi Hi Hlo Hnth Hoff Hov.
  intros ok J J' Hokf Hokp Hst Hst' HJfd HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_coreA tr ms md HspA Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & HMI & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0 & Hav).
  rewrite <- Hbs in Hav.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_okA segs tp ms md x8 p (Z_to_bv 64 off) data wdst Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav).
  - intros w' Hw.
    pose proof (@wstep_read_file_invA segs tp tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav Hw) as ->.
    cbn zeta. rewrite Hbs, G0. fold (rbA_md' md).
    destruct (rbA_md'_vm_same md) as [Hvs Hh1].
    rewrite Hbs in Hav.
    destruct (md_after_props segs tp (rbA_md' md) _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav)) as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|]. unfold rkA_rho'.
      eapply (smatchA_after_kwrite_keep rho tp A tr ms md tr _ (len_word rbA_bs) k base elo ehi (soff rho elo) (soff rho ehi) cells (ms_gpr ms 1) rbA_bs woff HspA);
        [rewrite Hh1; exact Hh | exact Hvs | exact Hnth | reflexivity | reflexivity | rewrite G1; exact Hbuf | exact Hlo | pose proof rbA_bs_len; lia | exact Hcells].
    + eapply Hst'; [apply agree_below_refl | exact Hme |]. apply HK. exact Hk.
Qed.

Theorem etriple_read_keepA : ltac2:(tb__ "0|4|
S46S46S47Vsegs;S2fS3VA;A1A1M0R2A3S47Vsegs;S61G0A1R2A3S9S1bA1M1S19R6Vrho;Vtp;R2R1A4S1S0S8S1aA1S1dS1cR2A1S16Q40M2Z3A2A2S7S1aS1fVp;S16G2Voff;A2A2A2A3S0S8S9S15Q8A1A1M3A1S79S20R2A1Vp;A2S7G3Vdata;A2A3A2F_;Fmd;Ftr;G1S19R7Vrho;Vtp;R2R1A4R7S69Vtp;R3S67R2A1A4F_;Fmd;Ftr;S6bVsegs;S45Vsegs;R6VA;Vrho;Vtp;A5S45Vsegs;R5S70VA;A1S69Vtp;A5A3F_;F_;F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcells Hcnt Hhi Hi Hlo Hnth Hoff Hov.
  intros J J' Hst Hst' HJfd HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_coreA tr ms md HspA Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & HMI & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0 & Hav).
  rewrite <- Hbs in Hav.
  eexists. split; [exact (@wstep_read_file_introA segs tp tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav)|].
  cbn zeta. rewrite Hbs, G0. fold (rbA_md' md).
  destruct (rbA_md'_vm_same md) as [Hvs Hh1].
  rewrite Hbs in Hav.
  destruct (md_after_props segs tp (rbA_md' md) _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav)) as (Hme & _).
  split.
  - eapply smatchA_mat_equiv; [exact Hme|]. unfold rkA_rho'.
    eapply (smatchA_after_kwrite_keep rho tp A tr ms md tr _ (len_word rbA_bs) k base elo ehi (soff rho elo) (soff rho ehi) cells (ms_gpr ms 1) rbA_bs woff HspA);
      [rewrite Hh1; exact Hh | exact Hvs | exact Hnth | reflexivity | reflexivity | rewrite G1; exact Hbuf | exact Hlo | pose proof rbA_bs_len; lia | exact Hcells].
  - eapply Hst'; [apply agree_below_refl | exact Hme |]. apply HK. exact Hk.
Qed.

Hypothesis Hcells0 : cells = [].
Hypothesis Hwoff : ltac2:(tb__ "0|0|
S0S4eVwoff;S37Vrho;Velo;A2A3").
Definition rhA_rho' : valuation := ltac2:(tb__ "0|1|
S64S64Vrho;S2fS3VA;A1A1M0S85S66A1A3S61G0A1S82S15Q8A1S66A2A3").

Theorem triple1_read_hdrA : ltac2:(tb__ "0|5|
S6aOF_;S46S46S49Vsegs;R3R2A3S5eVsegs;R4R3A3S47Vsegs;S2fS3VA;A1A1M0R4A3S47Vsegs;S61S61G0A1A1R4A3S78U4SdS15Q8A1M1S66A2A2S9S1bA1M2S19R9Vrho;Vtp;R2R1A4S1S0S8S1aA1S1dS1cR2A1S16Q40M3Z3A2A2S7S1aS1fVp;S16G3Voff;A2A2A2A3S0S8S9G1A1M4A1S79S20R2A1Vp;A2S7G4Vdata;A2A3A2F_;Fmd;Ftr;G2S19RaVrho;Vtp;R2R1A4RaS68Vtp;R3S67R2A1A4F_;Fmd;Ftr;S6cVsegs;RaS45Vsegs;R9VA;Vrho;Vtp;A5S45Vsegs;R8S71VA;Vk;Vbase;Velo;Vehi;A5S68Vtp;A5A4F_;F_;F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcells Hcells0 Hcnt Hhi Hi Hlo Hnth Hoff Hwoff Hov.
  intros ok J J' Hokf Hokp Hst Hst' H4 HJfd HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_coreA tr ms md HspA Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & HMI & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0 & Hav).
  rewrite <- Hbs in Hav.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_okA segs tp ms md x8 p (Z_to_bv 64 off) data wdst Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav).
  - intros w' Hw.
    pose proof (@wstep_read_file_invA segs tp tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav Hw) as ->.
    cbn zeta. rewrite Hbs, G0. fold (rbA_md' md).
    destruct (rbA_md'_vm_same md) as [Hvs Hh1].
    rewrite Hbs in Hav.
    destruct (md_after_props segs tp (rbA_md' md) _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav)) as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|]. unfold rhA_rho'. subst cells.
      eapply (smatchA_after_kwrite_hdr rho tp A tr ms md tr _ (len_word rbA_bs) k base elo ehi (soff rho elo) (soff rho ehi) (ms_gpr ms 1) rbA_bs HspA);
        [rewrite Hh1; exact Hh | exact Hvs | exact Hnth | reflexivity | reflexivity | rewrite G1, <- Hwoff; exact Hbuf | pose proof rbA_bs_len; lia | exact H4].
    + eapply Hst'; [apply agree_below_refl | exact Hme |]. apply HK. exact Hk.
Qed.

Theorem etriple_read_hdrA : ltac2:(tb__ "0|5|
S46S46S47Vsegs;S2fS3VA;A1A1M0R2A3S47Vsegs;S61S61G0A1A1R2A3S78U4SdS15Q8A1M1S66A2A2S9S1bA1M2S19R7Vrho;Vtp;R2R1A4S1S0S8S1aA1S1dS1cR2A1S16Q40M3Z3A2A2S7S1aS1fVp;S16G3Voff;A2A2A2A3S0S8S9G1A1M4A1S79S20R2A1Vp;A2S7G4Vdata;A2A3A2F_;Fmd;Ftr;G2S19R8Vrho;Vtp;R2R1A4R8S68Vtp;R3S67R2A1A4F_;Fmd;Ftr;S6bVsegs;S45Vsegs;R7VA;Vrho;Vtp;A5S45Vsegs;R6S71VA;Vk;Vbase;Velo;Vehi;A5S68Vtp;A5A3F_;F_;F_;F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcells Hcells0 Hcnt Hhi Hi Hlo Hnth Hoff Hwoff Hov.
  intros J J' Hst Hst' H4 HJfd HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_coreA tr ms md HspA Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & HMI & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0 & Hav).
  rewrite <- Hbs in Hav.
  eexists. split; [exact (@wstep_read_file_introA segs tp tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh HMI H63 Hfd' Hfs Ewd Hc2 Hc3 Hav)|].
  cbn zeta. rewrite Hbs, G0. fold (rbA_md' md).
  destruct (rbA_md'_vm_same md) as [Hvs Hh1].
  rewrite Hbs in Hav.
  destruct (md_after_props segs tp (rbA_md' md) _ (vm_same_MI segs _ _ tp Hvs HMI) (ranges_avoid_vm_same _ _ tp _ Hvs Hav)) as (Hme & _).
  split.
  - eapply smatchA_mat_equiv; [exact Hme|]. unfold rhA_rho'. subst cells.
    eapply (smatchA_after_kwrite_hdr rho tp A tr ms md tr _ (len_word rbA_bs) k base elo ehi (soff rho elo) (soff rho ehi) (ms_gpr ms 1) rbA_bs HspA);
      [rewrite Hh1; exact Hh | exact Hvs | exact Hnth | reflexivity | reflexivity | rewrite G1, <- Hwoff; exact Hbuf | pose proof rbA_bs_len; lia | exact H4].
  - eapply Hst'; [apply agree_below_refl | exact Hme |]. apply HK. exact Hk.
Qed.
End ReadBufA.

Lemma etriple_writev2A : forall (J J' : jpredA) A rho tp ch bs1 bs2 e,
  stableA segs (ss_next (ax_S A)) J -> stableA segs (Pos.succ (ss_next (ax_S A))) J' ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 2 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next (ax_S A)) e = true ->
  (forall rho' tr md k, agree_below (ss_next (ax_S A)) rho rho' ->
     rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tp tr md -> (1 <= k <= length (bs1 ++ bs2))%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' tp (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k (bs1 ++ bs2))) md) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte (vms md tp ms)) ((eval rho (reg_sv (ax_S A) 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  etriple segs (SPA segs J A rho tp)
    (fun w => exists rho', agree_below (ss_next (ax_S A)) rho rho'
              /\ rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat (length (bs1 ++ bs2)))
              /\ SPA segs J' (A_after_write A e) rho' tp w).
Proof using .
  intros J J' A rho tp ch bs1 bs2 e Hst Hst' Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & b2 & l2 & R1 & R2 & R3 & R4 & B1 & B2 & Hev & Hiok & Hok1 & Hok2). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  pose proof (read_u64_mono _ _ _ _ LIFT R3) as R3'. pose proof (read_u64_mono _ _ _ _ LIFT R4) as R4'.
  pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B1) as B1'. pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B2) as B2'.
  rewrite <- G1 in R1', R2', R3', R4'.
  assert (Hav : forall k, ranges_avoid (hid md tp) (writev2_reads (sys_input segs ms (Z_to_bv 64 66)) b1 l1 b2 l2 k)).
  { intros k. unfold writev2_reads, writev_reads. autorewrite with sys_input. apply ranges_avoid_app.
    - rewrite G1. eapply iov_desc2_avoid; [exact Hsp | exact R1 | exact R2 | exact R3 | exact R4].
    - intros a n Hin. destruct (iov_prefix_accesses_in _ _ _ _ Hin) as (l & Hinl & Hle).
      destruct Hinl as [E|[E|[]]]; injection E as <- <-.
      + eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B1]].
        rewrite read_bytes_map_eq in B1. rewrite (read_bytes_aux_length _ _ _ _ B1). exact Hle.
      + eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B2]].
        rewrite read_bytes_map_eq in B2. rewrite (read_bytes_aux_length _ _ _ _ B2). exact Hle. }
  set (n := length (bs1 ++ bs2)).
  assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat n)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md n Hag (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk Hk'].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split.
  { exact (wstep_writev2_intro_prefixA segs tp tr ms md _ _ _ _ _ _ _ _ n Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' R3' R4' B1' B2' Hiok Hok1 Hok2 Hlen ltac:(lia) (Hav n)). }
  exists (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat n))). split; [exact Hag|].
  split; [apply rho_set_rw_at|].
  destruct (md_after_props segs tp md _ HMI (Hav n)) as (Hme & _).
  split.
  - eapply smatchA_mat_equiv; [exact Hme|].
    eapply smatchA_after_write; [exact Hsp | exact Hh | apply vm_same_refl | exact He | exact Hev | lia].
  - eapply Hst'; [apply agree_below_refl | exact Hme | exact Hk'].
Qed.

Lemma triple1_writev1A : forall (ok : world -> Prop) (J J' : jpredA) A rho tp ch bs1 e,
  ok_frameA segs ok J -> ok_pframeA segs ok J -> stableA segs (ss_next (ax_S A)) J ->
  stableA segs (Pos.succ (ss_next (ax_S A))) J' ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 1 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next (ax_S A)) e = true ->
  (forall rho' tr md k, agree_below (ss_next (ax_S A)) rho rho' ->
     rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tp tr md -> (1 <= k <= length bs1)%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' tp (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k bs1)) md) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b1 l1,
       read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPA segs J A rho tp)
    (fun w => exists rho', agree_below (ss_next (ax_S A)) rho rho' /\ SPA segs J' (A_after_write A e) rho' tp w).
Proof using .
  intros ok J J' A rho tp ch bs1 e Hokf Hokp Hst Hst' Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & R1 & R2 & B1 & Hev & Hiok & Hok1). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B1) as B1'.
  rewrite <- G1 in R1', R2'.
  assert (Hav : forall k, ranges_avoid (hid md tp) (writev1_reads (sys_input segs ms (Z_to_bv 64 66)) b1 l1 k)).
  { intros k. unfold writev1_reads, writev_reads. autorewrite with sys_input. apply ranges_avoid_app.
    - rewrite G1. eapply iov_desc1_avoid; [exact Hsp | exact R1 | exact R2].
    - intros a n Hin. destruct (iov_prefix_accesses_in _ _ _ _ Hin) as (l & Hinl & Hle).
      destruct Hinl as [E|[]]; injection E as <- <-.
      eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B1]].
      rewrite read_bytes_map_eq in B1. rewrite (read_bytes_aux_length _ _ _ _ B1). exact Hle. }
  assert (Hag1 : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat 1)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md 1%nat Hag1 (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk _].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    eapply writev1_only_okA; [exact Hh | exact HMI | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1' | exact R2' | exact B1' | exact Hiok | exact Hok1 | exact Hlen | exact Hav].
  - intros w' Hw.
    destruct (wstep_writev1_invA segs tp tr ms md _ _ _ _ _ w' Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' B1' Hiok Hok1 Hlen Hav Hw) as (k & Hk1 & ->).
    assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat k)))) by (apply agree_below_set_rw; lia).
    exists (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat k))). split; [exact Hag|].
    destruct (md_after_props segs tp md _ HMI (Hav k)) as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|].
      eapply smatchA_after_write; [exact Hsp | exact Hh | apply vm_same_refl | exact He | exact Hev | lia].
    + eapply Hst'; [apply agree_below_refl | exact Hme |].
      exact (proj2 (HK _ tr md k Hag (rho_set_rw_at _ _ _) Hk Hk1)).
Qed.

Lemma etriple_writev1A : forall (J J' : jpredA) A rho tp ch bs1 e,
  stableA segs (ss_next (ax_S A)) J -> stableA segs (Pos.succ (ss_next (ax_S A))) J' ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 1 ->
  0 < ch < 2 ^ 32 -> (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  sv_below (ss_next (ax_S A)) e = true ->
  (forall rho' tr md k, agree_below (ss_next (ax_S A)) rho rho' ->
     rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat k) ->
     J rho tp tr md -> (1 <= k <= length bs1)%nat ->
     fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))
     /\ J' rho' tp (tr ++ map (WriteEv (Z_to_bv 64 ch)) (firstn k bs1)) md) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b1 l1,
       read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b1
       /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte (vms md tp ms)) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  etriple segs (SPA segs J A rho tp)
    (fun w => exists rho', agree_below (ss_next (ax_S A)) rho rho'
              /\ rw rho' (ss_next (ax_S A)) = Z_to_bv 64 (Z.of_nat (length bs1))
              /\ SPA segs J' (A_after_write A e) rho' tp w).
Proof using .
  intros J J' A rho tp ch bs1 e Hst Hst' Hi H17 H10 H12 Hch Hlen He HK Hbs.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hbs tr ms md Hsp Hk) as (b1 & l1 & R1 & R2 & B1 & Hev & Hiok & Hok1). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  pose proof (read_bytes_map_mono _ _ _ _ _ LIFT B1) as B1'.
  rewrite <- G1 in R1', R2'.
  assert (Hav : forall k, ranges_avoid (hid md tp) (writev1_reads (sys_input segs ms (Z_to_bv 64 66)) b1 l1 k)).
  { intros k. unfold writev1_reads, writev_reads. autorewrite with sys_input. apply ranges_avoid_app.
    - rewrite G1. eapply iov_desc1_avoid; [exact Hsp | exact R1 | exact R2].
    - intros a n Hin. destruct (iov_prefix_accesses_in _ _ _ _ Hin) as (l & Hinl & Hle).
      destruct Hinl as [E|[]]; injection E as <- <-.
      eapply range_avoids_le; [| eapply read_bytes_map_avoids; [intros x b Hb; exact (vms_read_byte_hid _ _ _ _ _ _ _ _ Hsp Hb) | exact B1]].
      rewrite read_bytes_map_eq in B1. rewrite (read_bytes_aux_length _ _ _ _ B1). exact Hle. }
  set (n := length bs1).
  assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat n)))) by (apply agree_below_set_rw; lia).
  destruct (HK _ tr md n Hag (rho_set_rw_at _ _ _) Hk ltac:(lia)) as [Hlk Hk'].
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact Hlk. }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split.
  { exact (wstep_writev1_intro_prefixA segs tp tr ms md _ _ _ _ _ n Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' B1' Hiok Hok1 Hlen ltac:(lia) (Hav n)). }
  exists (rho_set_rw rho (ss_next (ax_S A)) (Z_to_bv 64 (Z.of_nat n))). split; [exact Hag|].
  split; [apply rho_set_rw_at|].
  destruct (md_after_props segs tp md _ HMI (Hav n)) as (Hme & _).
  split.
  - eapply smatchA_mat_equiv; [exact Hme|].
    eapply smatchA_after_write; [exact Hsp | exact Hh | apply vm_same_refl | exact He | exact Hev | lia].
  - eapply Hst'; [apply agree_below_refl | exact Hme | exact Hk'].
Qed.

Lemma triple1_writev01A : forall (ok : world -> Prop) (J : jpredA) A rho tp ch,
  ok_frameA segs ok J -> ok_pframeA segs ok J -> stableA segs (ss_next (ax_S A)) J ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 1 ->
  0 < ch < 2 ^ 32 ->
  (forall rho tp tr md, J rho tp tr md -> fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b, read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b
          /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some (Z_to_bv 64 0)
          /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 16 <= TASK_SIZE)%Z
          /\ (bv_unsigned b <= TASK_SIZE)%Z) ->
  triple1 segs ok (SPA segs J A rho tp) (SPA segs J (A_after A (SLit 0)) rho tp).
Proof using .
  intros ok J A rho tp ch Hokf Hokp Hst Hi H17 H10 H12 Hch HJ Hrd.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hrd tr ms md Hsp Hk) as (b & R1 & R2 & Hiok & Hbok). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b' Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  rewrite <- G1 in R1', R2'.
  assert (Hav : ranges_avoid (hid md tp) (writev0_reads (sys_input segs ms (Z_to_bv 64 66)) [(b, Z_to_bv 64 0)])).
  { unfold writev0_reads. autorewrite with sys_input. cbn [length]. rewrite G1. eapply iov_desc1_avoid; [exact Hsp | exact R1 | exact R2]. }
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact (HJ rho tp tr md Hk). }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. eapply writev01_only_okA; [exact Hh | exact HMI | exact H66 | exact Hfd' | exact Hch0 | exact G2 | exact R1' | exact R2' | exact Hiok | exact Hbok | exact Hav].
  - intros w' Hw. rewrite (wstep_writev01_invA segs tp tr ms md _ _ b w' Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' Hiok Hbok Hav Hw).
    destruct (md_after_props segs tp md _ HMI Hav) as (Hme & _).
    split.
    + eapply smatchA_mat_equiv; [exact Hme|]. change (SLit 0) with (SLit (bv_unsigned (Z_to_bv 64 0))).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + eapply Hst; [apply agree_below_refl | exact Hme | exact Hk].
Qed.

Lemma etriple_writev01A : forall (J : jpredA) A rho tp ch,
  stableA segs (ss_next (ax_S A)) J ->
  instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
  reg_sv (ax_S A) 17 = SLit 66 -> reg_sv (ax_S A) 10 = SLit ch -> reg_sv (ax_S A) 12 = SLit 1 ->
  0 < ch < 2 ^ 32 ->
  (forall rho tp tr md, J rho tp tr md -> fd_lookup (m_fds md) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch))) ->
  (forall tr ms md, smatch_pendingA segs rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
     exists b, read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11)) = Some b
          /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho (reg_sv (ax_S A) 11) + 8)%bv = Some (Z_to_bv 64 0)
          /\ (bv_unsigned (eval rho (reg_sv (ax_S A) 11)) + 16 <= TASK_SIZE)%Z
          /\ (bv_unsigned b <= TASK_SIZE)%Z) ->
  etriple segs (SPA segs J A rho tp) (SPA segs J (A_after A (SLit 0)) rho tp).
Proof using .
  intros J A rho tp ch Hst Hi H17 H10 H12 Hch HJ Hrd.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2. rewrite H12 in G2. cbn [eval] in G2.
  destruct (Hrd tr ms md Hsp Hk) as (b & R1 & R2 & Hiok & Hbok). rewrite <- G1 in Hiok.
  assert (LIFT : forall x b, ms_read_byte (vms md tp ms) x = Some b -> ms_read_byte ms x = Some b)
    by (intros x b' Hb; exact (vms_read_byte_someA segs _ _ _ _ _ _ _ _ Hsp Hb)).
  pose proof (read_u64_mono _ _ _ _ LIFT R1) as R1'. pose proof (read_u64_mono _ _ _ _ LIFT R2) as R2'.
  rewrite <- G1 in R1', R2'.
  assert (Hav : ranges_avoid (hid md tp) (writev0_reads (sys_input segs ms (Z_to_bv 64 66)) [(b, Z_to_bv 64 0)])).
  { unfold writev0_reads. autorewrite with sys_input. cbn [length]. rewrite G1. eapply iov_desc1_avoid; [exact Hsp | exact R1 | exact R2]. }
  assert (H66 : bv_unsigned (Z_to_bv 64 66) = 66%Z) by reflexivity.
  assert (Hfd' : fd_lookup (m_fds md) (fd32 (ms_gpr ms 0)) = Some (FdChannel (Z_to_bv 64 ch))).
  { rewrite G0, fd32_lit by lia. exact (HJ rho tp tr md Hk). }
  assert (Hch0 : Z_to_bv 64 ch <> Z_to_bv 64 0) by (apply Z_to_bv64_neq; lia).
  eexists. split; [exact (wstep_writev01_introA segs tp tr ms md _ _ b Hp Hh HMI H66 Hfd' Hch0 G2 R1' R2' Hiok Hbok Hav)|].
  destruct (md_after_props segs tp md _ HMI Hav) as (Hme & _).
  split.
  - eapply smatchA_mat_equiv; [exact Hme|]. change (SLit 0) with (SLit (bv_unsigned (Z_to_bv 64 0))).
    eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
  - eapply Hst; [apply agree_below_refl | exact Hme | exact Hk].
Qed.

Section ReadDirA.
Variable A : axst.
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S8S62A1S73Vsegs;S39S3VA;A1A1A2S7S62S63A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1Z11A2S33Z3fA1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1ZaA2S33Z3A1A3").

Hypothesis Hov : ltac2:(tb__ "0|2|
S57S58S17Q40M0S32Vrho;S30S3VA;A1M1ZbA2A2A2S17G0S32Vrho;S30G1ZcA2A2A2A2S22A2").

Definition dirA' : axst := ltac2:(tb__ "0|0|
S60VA;S33S5bS5aZ2Z40A2Z15A2A1A2").

Lemma read_dir_coreA : ltac2:(tb__ "0|6|
S9S1bA1M0S50S19S5dVsegs;Vrho;Vtp;VA;SaG0S4bR3S4cR2R1A2A4A5S0S8S1aA1M1S1dS1cR2A1S16Q40M2Z3A2A2S7S1aS26A2M3A3S2S15G2A1M4G4S1S0S8G4A1M5S55R5A1S7G4R1A2A3S1S0S4eS17G2R1A2Z3fA3S1S0G5S1eR4A1SeG4A1A3S1S0G1S1dS1cR4A1S7eS51R5U0A2A1A2G3A3S1S57S58S17G2S51R5U1A2A2S17G2S51R5U2A2A2A2S22A2S48Vsegs;Vrho;Vtp;S88SaG0S4bR6S4cS7bR5S29S2aA1A2R4A2A4A5A2A2A2A2A2Lx8;A2F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hov.
  intros tr ms md HspA Hfd.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ HspA) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ HspA) as Hh.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 HspA ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 HspA ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 2 HspA ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  exists (Z_to_bv 64 63).
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|].
  split; [rewrite G1, G2; exact Hov|].
  unfold dirA'. rewrite <- errno_EISDIR. eapply smatchA_after_ret_lit; [exact HspA | exact Hh | apply vm_same_refl].
Qed.

Theorem triple1_read_dirA : ltac2:(tb__ "0|1|
S6aOF_;S46S46S49Vsegs;R3R2A3S5eVsegs;R4R3A3S47Vsegs;S2fS3VA;A1A1R4A3S9S1bA1M0S19R7Vrho;Vtp;R2R1A4S0S8S1aA1S1dS1cR2A1S16Q40Z3A2A2S7S1aS26A2A3F_;Fmd;Ftr;G0S19R8Vrho;Vtp;R2R1A4R8Vrho;Vtp;R3R2A4F_;Fmd;Ftr;S6cVsegs;R8S45Vsegs;R7VA;Vrho;Vtp;A5S45Vsegs;R6S88Vrho;Vtp;A5A4F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hi Hov.
  intros ok J J' Hokf Hokp Hst HJfd HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md HspA Hk.
  destruct (read_dir_coreA tr ms md HspA (HJfd tr md Hk)) as (x8 & Hp & H63 & Hh & Hfd' & Hc3 & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_dir_only_okA segs ms md x8 H63 Hfd' Hc3).
  - intros w' Hw.
    pose proof (@wstep_read_dir_invA segs tr ms md x8 w' Hp Hh H63 Hfd' Hc3 Hw) as ->.
    split; [exact Hsm' | apply HK; exact Hk].
Qed.

Theorem etriple_read_dirA : ltac2:(tb__ "0|1|
S46S46S47Vsegs;S2fS3VA;A1A1R2A3S9S1bA1M0S19R5Vrho;Vtp;R2R1A4S0S8S1aA1S1dS1cR2A1S16Q40Z3A2A2S7S1aS26A2A3F_;Fmd;Ftr;G0S19R6Vrho;Vtp;R2R1A4R6Vrho;Vtp;R3R2A4F_;Fmd;Ftr;S6bVsegs;S45Vsegs;R5VA;Vrho;Vtp;A5S45Vsegs;R4S88Vrho;Vtp;A5A3F_;F_;F_;FJ';FJ;").
Proof using H10 H17 Hi Hov.
  intros J J' Hst HJfd HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md HspA Hk.
  destruct (read_dir_coreA tr ms md HspA (HJfd tr md Hk)) as (x8 & Hp & H63 & Hh & Hfd' & Hc3 & Hsm').
  eexists. split; [exact (@wstep_read_dir_introA segs tr ms md x8 Hp Hh H63 Hfd' Hc3)|].
  split; [exact Hsm' | apply HK; exact Hk].
Qed.
End ReadDirA.

Section CloseA.
Variable A : axst.
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S8S62A1S73Vsegs;S39S3VA;A1A1A2S7S62S63A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1Z11A2S33Z39A1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1ZaA2S33Z3A1A3").

Definition closeA' : axst := A_after A (SLit 0).

Lemma close_coreA : ltac2:(tb__ "0|6|
S9S1bA1M0S50S19S1aS5dVsegs;Vrho;Vtp;VA;SaG0S4bR4S4cR3R2A2A4A5S0S8S1aA1M1S1dS1cR3A1S16Q40M2Z3A2A2S7S1aR2A2A3S2S15G2A1M3G3S1S0S8G3A1M4S55R6A1S7G3R1A2A3S1S0S4eS17G2R1A2Z39A3S1S0G4S1eR5A1SeG3A1A3S1S0G1S1dS1cR5A1S7eS51R6U0A2A1A2S7S1aR4A2A3S1S0S19S7dR6R5A2S84R5A1M5A3S48Vsegs;Vrho;Vtp;S86SaG0S4bR7S4cS7bR6S16G2Z0A2A2G5A2A4A5A2A2A2A2A2Lx8;A2F_;F_;Fe;Fmd;Fms;Ftr;").
Proof using H10 H17.
  intros tr ms md e HspA Hfd.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ HspA) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ HspA) as Hh.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 HspA ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  exists (Z_to_bv 64 57).
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|].
  split; [unfold closed_model, close_md'; rewrite G0, fd32_3; reflexivity|].
  unfold closeA'. change 0 with (bv_unsigned (Z_to_bv 64 0)).
  eapply smatchA_after_ret_lit; [exact HspA | | apply vm_same_with_fds]. cbn. exact Hh.
Qed.

Theorem triple1_closeA : ltac2:(tb__ "0|1|
S6aOF_;S46S46S49Vsegs;R3R2A3S5eVsegs;R4R3A3S47Vsegs;S2fS3VA;A1A1R4A3S9S1bA1M0S19R7Vrho;Vtp;R2R1A4S2S1aS1aS0S8S1aA1S1dS1cR3A1S16Q40Z3A2A2S7S1aR1A2A3Le;A2F_;Fmd;Ftr;G0S19R8Vrho;Vtp;R2R1A4R8Vrho;Vtp;R3S84R2A1A4F_;Fmd;Ftr;S6cVsegs;R8S45Vsegs;R7VA;Vrho;Vtp;A5S45Vsegs;R6S86Vrho;Vtp;A5A4F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hi.
  intros ok J J' Hokf Hokp Hst HJfd HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [e Hfd].
  destruct (close_coreA tr ms md e HspA Hfd) as (x8 & Hp & H57 & Hh & Hfd' & Hcm & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@close_only_okA segs ms md x8 e H57 Hfd').
  - intros w' Hw.
    pose proof (@wstep_close_invA segs tr ms md x8 e w' Hp Hh H57 Hfd' Hw) as ->. rewrite Hcm.
    split; [exact Hsm' | apply HK; exact Hk].
Qed.

Theorem etriple_closeA : ltac2:(tb__ "0|1|
S46S46S47Vsegs;S2fS3VA;A1A1R2A3S9S1bA1M0S19R5Vrho;Vtp;R2R1A4S2S1aS1aS0S8S1aA1S1dS1cR3A1S16Q40Z3A2A2S7S1aR1A2A3Le;A2F_;Fmd;Ftr;G0S19R6Vrho;Vtp;R2R1A4R6Vrho;Vtp;R3S84R2A1A4F_;Fmd;Ftr;S6bVsegs;S45Vsegs;R5VA;Vrho;Vtp;A5S45Vsegs;R4S86Vrho;Vtp;A5A3F_;F_;F_;FJ';FJ;").
Proof using H10 H17 Hi.
  intros J J' Hst HJfd HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [e Hfd].
  destruct (close_coreA tr ms md e HspA Hfd) as (x8 & Hp & H57 & Hh & Hfd' & Hcm & Hsm').
  eexists. split; [exact (@wstep_close_introA segs tr ms md x8 e Hp Hh H57 Hfd')|]. rewrite Hcm.
  split; [exact Hsm' | apply HK; exact Hk].
Qed.
End CloseA.

Section IoctlA.
Variable A : axst.
Variable rho : valuation.
Variable tp : list word.
Variable fd : Z.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S8S62A1S73Vsegs;S39S3VA;A1A1A2S7S62S63A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1Z11A2S33Z1dA1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1ZaA2S33Vfd;A1A3").
Hypothesis H11 : ltac2:(tb__ "0|0|
S0S31S30S3VA;A1ZbA2S33Z5413A1A3").
Hypothesis Hfd : 0 <= fd < 2 ^ 31.

Definition ioctlA' : axst := ltac2:(tb__ "0|0|
S60VA;S33S5bS5aZ2Z40A2Z19A2A1A2").

Lemma ioctl_coreA : ltac2:(tb__ "0|5|
S9S1bA1M0S50S19S15Q40M1A1M2S5dVsegs;Vrho;Vtp;VA;SaG0S4bR4S4cR3R2A2A4A5S0S8S1aA1M3S1dS1cR3A1S16G1Vfd;A2A2S7S1aS21R2A1A2A3S2G2G2S1S0S8G2A1M4S55R6A1S7G2R1A2A3S1S0S4eS17G1R1A2Z1dA3S1S0G4S1eR5A1SeG2A1A3S1S0G3S1dS1cR5A1S7eS51R6U0A2A1A2S7S1aS21R4A1A2A3S1S0G2S7fS51R6U1A2A1S92A3S48Vsegs;Vrho;Vtp;S87SaG0S4bR7S4cS7bR6S29S2bA1A2R5A2A4A5A2A2A2A2A2Lx8;A2F_;F_;Fe;Fmd;Fms;Ftr;").
Proof using H10 H11 H17 Hfd.
  intros tr ms md e HspA Hlk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ HspA) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ HspA) as Hh.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 0 HspA ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pendingA_gpr segs _ _ _ _ _ _ 1 HspA ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1. rewrite H11 in G1. cbn [eval] in G1.
  exists (Z_to_bv 64 29).
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_lit by lia; exact Hlk|].
  split; [apply cmd32_TIOCGWINSZ; rewrite G1; reflexivity|].
  unfold ioctlA'. replace (2 ^ 64 - 25) with (bv_unsigned (errno_ret ENOTTY)) by reflexivity.
  eapply smatchA_after_ret_lit; [exact HspA | exact Hh | apply vm_same_refl].
Qed.

Theorem triple1_ioctlA : ltac2:(tb__ "0|3|
S6aOF_;S46S46S49Vsegs;R3R2A3S5eVsegs;R4R3A3S47Vsegs;S2fS3VA;A1A1R4A3S9S1bA1M0S19R7Vrho;Vtp;R2R1A4S2S15Q40M1A1M2G2S0S8S1aA1S1dS1cR3A1S16G1Vfd;A2A2S7S1aS21R1A1A2A3Le;A2F_;Fmd;Ftr;G0S19R8Vrho;Vtp;R2R1A4R8Vrho;Vtp;R3R2A4F_;Fmd;Ftr;S6cVsegs;R8S45Vsegs;R7VA;Vrho;Vtp;A5S45Vsegs;R6S87Vrho;Vtp;A5A4F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H11 H17 Hfd Hi.
  intros ok J J' Hokf Hokp Hst HJfd HK.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [e Hlk].
  destruct (ioctl_coreA tr ms md e HspA Hlk) as (x8 & Hp & H29 & Hh & Hfd' & Hc & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@ioctl_only_okA segs ms md x8 e H29 Hfd' Hc).
  - intros w' Hw.
    pose proof (@wstep_ioctl_invA segs tr ms md x8 e w' Hp Hh H29 Hfd' Hc Hw) as ->.
    split; [exact Hsm' | apply HK; exact Hk].
Qed.

Theorem etriple_ioctlA : ltac2:(tb__ "0|3|
S46S46S47Vsegs;S2fS3VA;A1A1R2A3S9S1bA1M0S19R5Vrho;Vtp;R2R1A4S2S15Q40M1A1M2G2S0S8S1aA1S1dS1cR3A1S16G1Vfd;A2A2S7S1aS21R1A1A2A3Le;A2F_;Fmd;Ftr;G0S19R6Vrho;Vtp;R2R1A4R6Vrho;Vtp;R3R2A4F_;Fmd;Ftr;S6bVsegs;S45Vsegs;R5VA;Vrho;Vtp;A5S45Vsegs;R4S87Vrho;Vtp;A5A3F_;F_;F_;FJ';FJ;").
Proof using H10 H11 H17 Hfd Hi.
  intros J J' Hst HJfd HK.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md HspA Hk. destruct (HJfd tr md Hk) as [e Hlk].
  destruct (ioctl_coreA tr ms md e HspA Hlk) as (x8 & Hp & H29 & Hh & Hfd' & Hc & Hsm').
  eexists. split; [exact (@wstep_ioctl_introA segs tr ms md x8 e Hp Hh H29 Hfd' Hc)|].
  split; [exact Hsm' | apply HK; exact Hk].
Qed.
End IoctlA.

End WithSegs.
