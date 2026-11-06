(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "ms_svc_pending"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "eval"; "ss_next"; "reg_sv"; "ss_objs"; "SLit"; "SVar"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@Corelib.Init.Datatypes"; "bool"; "false"; "pair"; "list"; "true"; "Some"; "option"; "app"; "cons"; "fst"; "nil"; "prod"; "snd"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "ge"; "modulo"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "wstep"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "m_halted"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "mmap_n"; "mmap_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA"; "mmap_obj_sym"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "zero_range"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundM SymSoundR SymSoundL SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
Import ListNotations.
Open Scope Z_scope.

Section G.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Lemma not_refusable_of_place : ltac2:(tb__ "0|1|
S9Q40A1M0G0S3aG0G0S45R5R4R3R2R1A5S0S1fS3fR5R4S44R3A1A3S20A3F_;Fa;Flen;Fm;Fflags;Faddr;").
Proof.
  intros addr flags m len a (Hal & Hpos & Htop & Hfree & Hb).
  unfold mmap_grant_refusable. rewrite Hb. cbn [negb orb].
  apply negb_false_iff. apply vm_gap_available_iff. exists a.
  split; [exact Hal|]. split; [exact Hpos|]. split; [exact Htop|].
  unfold mmap_n in Hfree. exact Hfree.
Qed.

Lemma wstep_mmap_inv_grantedA : ltac2:(tb__ "0|8|
S5S3aS9Q40M0A1M1S0S25G1A1M2S3eR2A1S2cG1A1A3S0S2dS8G0R2A2ZdeA3S3S0G1S4R5U1M3A2SaG0Z0A2A3A1S0S1fS40S4R6U2A2S4R6U3M4A2S4R6U5A2A3S23A3S0S1fS3fS4R7G4A2R6S44S4R7G3A2A1A3S20A3S22S3bA1M5S34S0G2S7RaA1S24G1R8A2A3S37Vsegs;S21G5S38R3S39RbRaA2A4R2A3S2G1G1S1S45S4RdU0A2S4RdG4A2M6RcS4RdG3A2M7R1A5S0S34R4S21G5S38R5S39S56RdR1S57S6RdA1R1S47G7A1A3A3S48G6RcG7R1A4A2A4A3A2La;A2F_;F_;Fw';Ftr;F_;F_;F_;F_;F_;Fx8;Fm;Fms;").
Proof.
  intros ms m x8 Hh Hno Hlen Hsh Hnr tr w' Hp Hw.
  destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
  apply (@mmap_rw_inv_granted (sys_input segs ms x8) m Hno Hlen Hsh _ Hnr) in Hspec.
  destruct Hspec as (a & Hpl & E). inversion E; subst.
  exists a. split; [exact Hpl|].
  destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
  - cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
    injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
  - exfalso. revert Hcd. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
    change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1). rewrite mmap_rw_model_halted. congruence.
Qed.

Theorem triple1_mmap_rw_symA_granted : ltac2:(tb__ "0|10|
S34OF_;S4cS9Q40M0A1M1S4cF_;S1dS18S22G1A1SbS2dS4eVsegs;R8R7A3S52Vsegs;R9R8A3S4dVsegs;SeS19R7A1A1R9A3S0S25S42A1S50Vsegs;S16S19R8A1A1A2S24S42S43A2A3S0SbSfS19R9A1Z11A2S11ZdeA1A3S0SbSfS19RaA1ZbA2R7A3S0S1fS17SeS19RbA1A1R8A2S23A3S0S2dS8G0SdRbR9A2A2R8A3S0S2dS32R9Z1000A2Z0M2A3S1S2eG2RaA2S2eRaS33Z2Z3eA2A2A2S22S3bA1M3S5S3aS51Vsegs;R11R10R12S21G3S38R3S39R2R1A2A4A5R15R12R11R4R2A4S1S0S1fS40S4R4U2A2S4R4U3M4A2M5S4R4U5A2A3S23A3S1S0S1fS41G5A1S20A3S1S31S53R3R12A2R10A2S1S0S1fS3fG5R3S44S4R4U1M6A2A1A3S20A3G1S45S4R5U0A2S4R5G4A2R4S4R5G6A2R1A5S1ScS4fScR1S10S19R17A1A1A3S14S13R17R2A2S21S2dS2dS8G0R4A2M7S2fG7R14A2A4A2F_;Fo;S1G1S1S30S8G0R3A2M8S8G0R1A2M9A2S2eG9S2fG8R13A2A2A2S0S1fS15Vsegs;R2A2S20A3F_;Fx;S1S2aSbSbA2MaS2dS4fGaR2S1aR18A1A3S1S30S8G0SdR18S28SbSbR3A3A2A2MbR2A2S2eR2S2fGbS8G0SdR18S2bSbSbR3A3A2A2A2A2A2S3S1S30S8G0R6A2McS8G0S1eS8G0SdR19S1bR1aA1A2A2R3A2A2MdA2S2eGdS2fGcR16A2A2A2A1F_;F_;Fy;Fr;R17R2S49R15SeS19R16A1A1R2A3R14R7S3dS46S3cR5A1S4R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S36Vsegs;R13S4bVsegs;R12R10RfReA5S34S2G1G1S4bVsegs;R13R1A1S1cR12S4aS19R12A1MeS12SeGeA1MfA1S26ScS10GeA1S27ScS54GfRfA2S29ScA1A3A3S55GfA1A4A2S49R11GfR1A3R10R2A6La;A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo A rho tp elen nlit Hokf Hokp Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & Hnref & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (mmap_only_okA segs ms md _ Hh H222 Hlen Hmodb).
  - intros w' Hw. destruct (wstep_mmap_inv_grantedA ms md _ Hh H222 Hlen Hmodb Hnref tr w' Hp Hw) as (a & Hpl & ->).
    exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj_sym; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Theorem etriple_mmap_rw_symA_granted : ltac2:(tb__ "0|10|
S4cS9Q40M0A1M1S4cF_;S1dS18S22G1A1SbS2dS4dVsegs;SeS19R5A1A1R7A3S0S25S42A1S50Vsegs;S16S19R6A1A1A2S24S42S43A2A3S0SbSfS19R7A1Z11A2S11ZdeA1A3S0SbSfS19R8A1ZbA2R5A3S0S1fS17SeS19R9A1A1R6A2S23A3S0S2dS8G0SdR9R7A2A2R6A3S0S2dS32R7Z1000A2Z0M2A3S1S2eG2R8A2S2eR8S33Z2Z3eA2A2A2S22S3bA1M3S5S3aS51Vsegs;RfReR10S21G3S38R3S39R2R1A2A4A5R13R10RfR4R2A4S1S0S1fS40S4R4U2A2S4R4U3M4A2M5S4R4U5A2A3S23A3S1S0S1fS41G5A1S20A3S1S31S53R3R10A2ReA2S1S0S1fS3fG5R3S44S4R4U1M6A2A1A3S20A3G1S45S4R5U0A2S4R5G4A2R4S4R5G6A2R1A5S1ScS4fScR1S10S19R15A1A1A3S14S13R15R2A2S21S2dS2dS8G0R4A2M7S2fG7R12A2A4A2F_;Fo;S1G1S1S30S8G0R3A2M8S8G0R1A2M9A2S2eG9S2fG8R11A2A2A2S0S1fS15Vsegs;R2A2S20A3F_;Fx;S1S2aSbSbA2MaS2dS4fGaR2S1aR16A1A3S1S30S8G0SdR16S28SbSbR3A3A2A2MbR2A2S2eR2S2fGbS8G0SdR16S2bSbSbR3A3A2A2A2A2A2S3S1S30S8G0R6A2McS8G0S1eS8G0SdR17S1bR18A1A2A2R3A2A2MdA2S2eGdS2fGcR14A2A2A2A1F_;F_;Fy;Fr;R15R2S49R13SeS19R14A1A1R2A3R12R7S3dS46S3cR5A1S4R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S35Vsegs;S4bVsegs;R10ReRdRcA5S34S2G1G1S4bVsegs;R11R1A1S1cR10S4aS19R10A1MeS12SeGeA1MfA1S26ScS10GeA1S27ScS54GfRdA2S29ScA1A3A3S55GfA1A4A2S49RfGfR1A3ReR2A6La;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp elen nlit Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & Hrf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
  change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
  eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
  exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
  - eapply smatchA_after_mmap_obj_sym; eauto.
  - cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End G.
