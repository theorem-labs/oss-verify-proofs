(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "reg_sv"; "SLit"; "eval"; "rm"; "sobj"; "valuation"; "obj_range"; "ranges_disjoint"; "ss_next"; "ss_objs"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "shadow_addr"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "list"; "true"; "option"; "prod"; "Some"; "nil"; "fst"; "snd"; "None"; "cons"; "nat"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "vm_maps"; "Model"; "page_size"; "map_has"; "region_free"; "TASK_SIZE"; "map_contains"; "SyscallEffect"; "alloc_top"; "in_arg"; "m_halted"; "m_vm_lazy"; "map_remove"; "page_in_ranges"; "vm_reserved"; "MemCopy"; "mkEffectU"; "page_base"; "page_mem"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "wstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "after_sys_mem"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "find_segment"; "ms_mem"; "ms_svc_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "mmap_n"; "mmap_nZ"; "mmap_fixed_dead_model"; "munmap_exact_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "smatch_pendingA"; "ok_pframeA"; "only_okA"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA2"; "splice"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapNodesA.N"; "rereserve_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_budget_ok"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "MI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA MmapFixedA MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section N.
Variable segs : list Segment.

Local Notation wstep := (wstep segs).

Section MunmapA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 215%Z.
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S19S1dS11Q40Vaddr;A2S39A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.

  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S1cS1aS11Q40Vaddr;A2S59Vlen;A1A2S3cA2").
  Hypothesis Hhas : ltac2:(tb__ "0|0|
S0S1fS3aS37S36Vm;A1A1Vaddr;Vn;A3S22A3").

  Lemma munmap_model_halted : ltac2:(tb__ "0|1|
S13Q40A1M0G0S0S23G0A1S41S57Vm;R2R1A3A1S41Vm;A1A3Fk;Fa;").
  Proof using .
    intros. unfold munmap_model, with_mmap_destroyed, vm_forget_range. autorewrite with model. reflexivity.
  Qed.

  Let INV : ltac2:(tb__ "0|8|
S67S3eA1M0S0S1fS3aS37S36Vm;A1A1S40S34Vsegs;Vms;Vx8;A3M1U0A2M2S58S40G1U1A2A1M3A3S22A3S68G1Vm;R2A3S0G0R3S66S3eS47S12Q40M4Z0A2S26S24S13G4A1M5S21S13Q8A1A1A2A1S26S24G5G5A2M6A1M7S2aG6S20G5G5G2G3A4G7A3S26S46A1S26S24G5S2bA2A1A6S57Vm;G2G3A3S26S35A1A4A3F_;F_;FR;") := ltac2:(tb__ "0|0|
S5bS34Vsegs;Vms;Vx8;A3Vm;VHno;VHalign;VHlen;VHwrap;A6").

  Lemma munmap_only_okA : ltac2:(tb__ "0|0|
S60S34Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV Hhas.
    eapply only_okA_of_inv; [intros R HR; exact (INV R Hhas HR)| |].
    - intros E; discriminate.
    - intros eff m' evs E _; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_munmap_invA : ltac2:(tb__ "0|3|
S21S35A1M0S4cS0S23S13Q40M1A1M2A1S56Vms;A1S25G2Vx8;A2A3S4fVsegs;S20G0S32R3S33Vms;Vm;A2A4R2A3S0S4cR3S20G0S32R4S33S51Vms;S12G1Z0A2S50S55Vms;A1Vaddr;Vn;A3A3S57Vm;Vaddr;Vn;A3A2A4A3F_;F_;Fw';Ftr;").
  Proof using INV Hh Hhas.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (fun HR => INV _ Hhas HR) in Hspec. inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
    - cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
    - exfalso. revert Hcd. rewrite munmap_model_halted. congruence.
  Qed.

  Lemma wstep_munmap_introA : ltac2:(tb__ "0|3|
S21S35A1M0S0S23S13Q40M1A1M2A1S56Vms;A1S25G2Vx8;A2A3S4fVsegs;S20G0S32R2S33Vms;Vm;A2A4S20G0S32R2S33S51Vms;S12G1Z0A2S50S55Vms;A1Vaddr;Vn;A3A3S57Vm;Vaddr;Vn;A3A2A4A3F_;Ftr;").
  Proof using INV Hh Hhas.
    intros tr Hp.
    pose proof (@munmap_exact_intro (sys_input segs ms x8) m Hno Halign Hlen Hwrap Hhas) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite munmap_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.
End MunmapA.

Lemma munmap_len_lit : ltac2:(tb__ "0|6|
SbS21S13Q40M0A1M1A1S15S21S35A1M2S53S38S19S5eVsegs;R7R6R5S20G2S32R4S33R3R2A2A4A5S0S5S6S14R6A1ZbA2S7R2A1A3S0S19S1dR3Z1000A2Z0M3A3S1S1bG3R4A2S1bR4S1eZ2Z3eA2A2A2S1S2S0G1S52R7U1A2M4S12G0G3A2A3A1S1S0S19S59G4A1R5A3S1S0G1S58G4A1S12G0R5A2M5A3S0S19S11G0G5A2R5A3A2A2A2F_;F_;F_;F_;Fnlit;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md nlit Hsp H11 Hmod Hn.
  destruct (mmap_len_lit segs rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  split; [exact Hlen|]. split; [exact HnZ|]. split; [unfold mmap_n; rewrite HnZ; reflexivity|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Theorem triple1_munmapA : ltac2:(tb__ "0|f|
S4cOF_;S2fS2fS15SbS21S13Q40M0A1M1A1S5S19S31Vsegs;R8R7A3S5fVsegs;R9R8A3S30Vsegs;SeS14R7A1A1R9A3S0S23S4aA1S62Vsegs;S10S14R8A1A1A2S25S4aS4bA2A3S0S5S6S14R9A1Z11A2S7Zd7A1A3S0S5S6S14RaA1ZaA2R7A3S0S5S6S14RbA1ZbA2S7R7A1A3S0S19S1dR8Z1000A2Z0M2A3S1S1bG2R9A2S1bR9S1eZ2Z3eA2A2A2S21S35A1M3S53S38S5eVsegs;R10RfR11S20G3S32R3S33R2R1A2A4A5R14R11R10R4R2A4S52R4U0A2G1S1S0S19S1dS11G0R1A2M4S39A2G2A3S1S1cS1aG4R10A2M5S3cA2S1S0S1fS3aS37S36R4A1A1M6R1S12G0R10A2M7A3S22A3S1G1S2cS24G1G1A2S20G1G1R2R1A4S37S36R5A1A1A3S0G1R2S12G0R12A2A3F_;Fs;S1S0S1fS3bS43G6R1A2R1G7A3S22A3S1SaS2cSaR1SfS14R15A1A1A3SdScR15R2A2S20S19S19S11G0R3A2M8S1aG8R12A2A4A2F_;Fo;S1S24S5S5A2M9S19S2cG9R2S16R16A1A3S1S1cS11G0S8R16S27S5S5R3A3A2A2MaR2A2S1bR2S1aGaS11G0S8R16S28S5S5R3A3A2A2A2A2A2S2S1S1cS11G0R5A2MbS11G0S18S11G0S8R17S17R18A1A2A2R3A2A2McA2S1bGcS1aGbR14A2A2A2A1F_;F_;Fy;Frr;R15S2dR13S50S9R13A1R1G7A3A2S5cG4G5R12A3R6S57R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;S4eVsegs;R12S2eVsegs;R11RfReRdA5S4cS2eVsegs;R11S5dR10S7G2A1A2S2dRfS50S9RfA1S8RfRdA2MdS12G0RcA2A3A2S5cS11G0GdA2MeS1aGeRcA2ReA3R1A6Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fea;Ftp;Frho;FA;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo A rho tp ea nlit Hokf Hokp Hst Hi H17 H10 H11 Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (munmap_only_okA ms md _ H215 Hal Hlen Hwrap' Hhas).
  - intros w' Hw. rewrite (wstep_munmap_invA ms md _ Hh H215 Hal Hlen Hwrap' Hhas tr w' Hp Hw). rewrite HnE. rewrite <- G0.
    split.
    + unfold munmap_model, with_mmap_destroyed. unfold A_after.
      replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
      eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
                (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
        try reflexivity.
      all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
           try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
           try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
           try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
    + cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem etriple_munmapA : ltac2:(tb__ "0|f|
S2fS2fS15SbS21S13Q40M0A1M1A1S5S19S30Vsegs;SeS14R5A1A1R7A3S0S23S4aA1S62Vsegs;S10S14R6A1A1A2S25S4aS4bA2A3S0S5S6S14R7A1Z11A2S7Zd7A1A3S0S5S6S14R8A1ZaA2R5A3S0S5S6S14R9A1ZbA2S7R5A1A3S0S19S1dR6Z1000A2Z0M2A3S1S1bG2R7A2S1bR7S1eZ2Z3eA2A2A2S21S35A1M3S53S38S5eVsegs;ReRdRfS20G3S32R3S33R2R1A2A4A5R12RfReR4R2A4S52R4U0A2G1S1S0S19S1dS11G0R1A2M4S39A2G2A3S1S1cS1aG4ReA2M5S3cA2S1S0S1fS3aS37S36R4A1A1M6R1S12G0ReA2M7A3S22A3S1G1S2cS24G1G1A2S20G1G1R2R1A4S37S36R5A1A1A3S0G1R2S12G0R10A2A3F_;Fs;S1S0S1fS3bS43G6R1A2R1G7A3S22A3S1SaS2cSaR1SfS14R13A1A1A3SdScR13R2A2S20S19S19S11G0R3A2M8S1aG8R10A2A4A2F_;Fo;S1S24S5S5A2M9S19S2cG9R2S16R14A1A3S1S1cS11G0S8R14S27S5S5R3A3A2A2MaR2A2S1bR2S1aGaS11G0S8R14S28S5S5R3A3A2A2A2A2A2S2S1S1cS11G0R5A2MbS11G0S18S11G0S8R15S17R16A1A2A2R3A2A2McA2S1bGcS1aGbR12A2A2A2A1F_;F_;Fy;Frr;R13S2dR11S50S9R11A1R1G7A3A2S5cG4G5R10A3R6S57R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;S4dVsegs;S2eVsegs;RfRdRcRbA5S4cS2eVsegs;RfS5dReS7G2A1A2S2dRdS50S9RdA1S8RdRbA2MdS12G0RaA2A3A2S5cS11G0GdA2MeS1aGeRaA2RcA3R1A6Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fea;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp ea nlit Hst Hi H17 H10 H11 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  eexists. split; [exact (wstep_munmap_introA ms md _ Hh H215 Hal Hlen Hwrap' Hhas tr Hp)|].
  rewrite HnE. rewrite <- G0. split.
  - unfold munmap_model, with_mmap_destroyed. unfold A_after.
    replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
    eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
              (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
      try reflexivity.
    all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
         try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
         try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
         try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Definition rereserve_bytes (tp : list word) : word -> option byte := ltac2:(tb__ "0|2|
S13Q40A1S1fS23S13Q8M0A1M1A1L_;S49S48R1A1Vtp;A2S25G1S12G0Z0A2A2S29G1A1X1fx2Lx;").

Lemma map_contains_In : ltac2:(tb__ "0|5|
S21S24S13Q40M0A1M1G1A2M2A1G1G1S0S1fS3dR3R2R1A3S22A3S3G1G1S3G1G1S1S2cG2S20G1G1R2R1A4R6A3S1S1cS11G0R2A2M3S11G0R5A2M4A2S1cS1aG4S11G0R4A2A2S1aG3S11G0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fn;Fa;Fl;").
Proof.
  intros l a n H. unfold map_contains in H. apply existsb_exists in H as ([b s] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists b, s. split; [exact Hin|]. lia.
Qed.

Lemma rereserve_budget_ok : ltac2:(tb__ "0|4|
S38S21S13Q40M0A1M1A1G1G1G1S6cVsegs;R5R4A3S0S1fS6aR2A1S22A3S0S19S1dS11G0R5A2S39A2Z0M2A3M3G3S1bG2S11G0R6A2A2S1cS1aS11G0R8A2S11G0R7A2A2S1eZ2Z40A2A2S0S1fS69R7RbR9R8A4S22A3F_;F_;F_;F_;F_;F_;Fflags;Fn;Fa;Ftp;Fmd;").
Proof using .
  intros md tp a n flags HMI Hnr Hal Hnl Hpos Hend.
  pose proof HMI as (_ & _ & _ & _ & Hpaid & _ & Hivs & _).
  unfold mmap_fixed_rw_budget_ok, with_mmap_replacement, with_mmap_backing. rewrite Hnr.
  pose proof (used_rereserve_le md (mmap_fixed_rw_next (m_vmmaps md) a n) a n Hivs Hal Hnl Hpos Hend eq_refl eq_refl) as U.
  unfold vm_backing_within_limit.
  set (m' := vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) a n) md))) in *.
  assert (EL : vm_limit (m_vmmaps m') = vm_limit (m_vmmaps md)).
  { unfold m', vm_add_lazy, vm_forget_range. autorewrite with model. reflexivity. }
  rewrite EL. apply Z.leb_le.
  pose proof (filter_length_le (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized md)).
  unfold paid in Hpaid. pose proof page_size_pos. nia.
Qed.

Theorem triple1_mmap_fixed_rereserveA : ltac2:(tb__ "0|14|
S4cOF_;S2fS2fS2fS2fS15SbS21S13Q40M0A1M1A1S5S19S31Vsegs;RaR9A3S5fVsegs;RbRaA3S30Vsegs;SeS14R7A1A1RbA3S0S23S4aA1S62Vsegs;S10S14R8A1A1A2S25S4aS4bA2A3S0S5S6S14R9A1Z11A2S7ZdeA1A3S0S5S6S14RaA1ZaA2R7A3S0S5S6S14RbA1ZbA2S7R7A1A3S0S19S1dR8Z1000A2Z0M2A3S1S1bG2R9A2S1bR9S1eZ2Z3eA2A2A2S0S5S6S14ReA1ZcA2S7Z3A1A3S0S5S6S14RfA1ZdA2S7Z4032A1A3S0S5S6S14R10A1ZeA2S7ZffffffffffffffffA1A3S0S5S6S14R11A1ZfA2S7G2A1A3S21S35A1M3S53S38S5eVsegs;R14R13R15S20G3S32R3S33R2R1A2A4A5R1aR15R14R4R2A4S52R4U0A2G1S12G0R14A2G1S1S0S19S1dS11G0R2A2M4S39A2G2A3S1S1bG2G4A2S1S1cS1aG4R15A2M5S3fS36R5A1M6A1A2S1S0S1fS3bS45G6A1R2R1A3S22A3S1S0S1fS3dS37G6A1R2R1A3S22A3S1S19S1S1cS11G0R3A2M7R1A2S1bR1S1aG7R16A2A2A2S0S23S61A1S54Vsegs;R2Z1A3S29S61A1A3F_;Fz;S1G1S2cG1R1R18A3S1S1cS11G0R4A2M8G4A2S1bG4S1aG8R17A2M9A2A2S0S1fS44R3S42R8A1A2S22A3F_;F_;Fp;S1SaS2cSaR1SfS14R1aA1A1A3SdScR1aR2A2S20S19S19G8G9A4A2F_;Fo;S1S24S5S5A2MaS19S2cGaR2S16R1bA1A3S1S1cS11G0S8R1bS27S5S5R3A3A2A2MbR2A2S1bR2S1aGbS11G0S8R1bS28S5S5R3A3A2A2A2A2A2S2S1S1cS11G0R6A2McS11G0S18S11G0S8R1cS17R1dA1A2A2R3A2A2MdA2S1bGdS1aGcR19A2A2A2A1F_;F_;Fy;Frr;S1R1cR18R17R7R5A4S1R1bS2dR18S63S9R18A1MeS64R17A1R2R1A4A2R17R7S65S52R6U3A2R5R2R1A4A4R1aS2dR18S50GeR2R1A3A2S5cG4G5R17A3R7S5aR5R2R1A3A4A2A2A2A2A2A2A2A2A2A2A2Tn;Ta;F_;F_;Fmd;Fms;Ftr;S4eVsegs;R18S2eVsegs;R17R13R12R11A5S4cS4S2eVsegs;R17S5dR14S7S6bA1A2MfR13R12R1A6S4S2eVsegs;R16S5dR14R11A2S2dR13S63S9R13A1M10S64R12A1S8R13R11A2M11S12G0R10A2M12A4A2R12R1A6S2eVsegs;R15GfS2dR13S50G10G11G12A3A2S5cS11G0G11A2M13S1aG13R10A2R12A3R1A6A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fea;Ftp;Frho;FA;FJd;FJok;FJk;FJ;Fok;").
Proof using .
  intros ok J Jk Jok Jd A rho tp ea nlit Hokf Hokp Hst Hi H17 H10 H11 Hmod Hn H12 H13 H14 H15 HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  destruct (munmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite H10 in G0. rewrite H12 in G2. rewrite H13 in G3. rewrite H14 in G4. rewrite H15 in G5. cbn [eval] in G2, G3, G4, G5.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hpos & Hceil & Hfreeres & Hcont & Hseg & Htl & Hdisj & Hxs & HJk & HJok & HJd).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite HnZ; exact Hceil).
  rewrite <- HnE in Hfreeres, Hcont.
  pose proof (alloc_top_lt (m_vmmaps md)) as CL.
  assert (Hend : bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit) <= 2 ^ 64) by (rewrite Un; unfold two_pow_64 in CL; lia).
  assert (Hsw : swf (ax_S A) = true) by exact (smatch_pendingA_swf segs _ _ _ _ Hsp).
  assert (Hea : sv_below (ss_next (ax_S A)) ea = true).
  { rewrite <- H10. unfold reg_sv. apply (proj1 (forallb_forall _ _) (swf_regs_below _ Hsw)). apply nth_In.
    rewrite (swf_regs_len _ Hsw). cbn. lia. }
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    apply (fixed_rw_commit_only_okA segs ms md _ H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Hal Hpos Hfreeres Hcont).
  - intros w' Hw.
    destruct (wstep_fixed_rw_commit_invA segs ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Hal Hpos Hfreeres Hcont tr w' Hp Hw)
      as [-> | [[Hb ->] | ->]].
    +   left. split; [|exact HJk].
      unfold enomem_ret. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    +   right; left. rewrite HnE. rewrite <- G0. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HJok].
      unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Enr. unfold A_after.
      eapply (smatchA_after_rereserve segs rho _ tp A tr ms md tr (mmap_fixed_rw_next (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
                (ms_gpr ms 0) (Z_to_bv 64 nlit) (ms_gpr ms 0) ea (ss_next (ax_S A)) Hsp); try reflexivity.
      all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
           try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
           try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
           try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
    +   right; right. rewrite HnE. rewrite <- G0. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HJd].
      unfold mmap_fixed_dead_model, with_mmap_destroyed. unfold A_after.
      replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
      eapply (smatchA_after_destroy segs rho _ tp A tr ms md tr (mmap_fixed_dead_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
                (ms_gpr ms 0) (Z_to_bv 64 nlit) _ (SLit enomem_ret) (ss_next (ax_S A)) Hsp); try reflexivity.
      all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
           try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
           try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
           try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
Qed.

Theorem etriple_mmap_fixed_rereserveA : ltac2:(tb__ "0|d|
S2fS2fS15SbS21S13Q40M0A1M1A1S5S19S30Vsegs;SeS14R5A1A1R7A3S0S23S4aA1S62Vsegs;S10S14R6A1A1A2S25S4aS4bA2A3S0S5S6S14R7A1Z11A2S7ZdeA1A3S0S5S6S14R8A1ZaA2R5A3S0S5S6S14R9A1ZbA2S7R5A1A3S0S19S1dR6Z1000A2Z0M2A3S1S1bG2R7A2S1bR7S1eZ2Z3eA2A2A2S0S5S6S14RcA1ZcA2S7Z3A1A3S0S5S6S14RdA1ZdA2S7Z4032A1A3S0S5S6S14ReA1ZeA2S7ZffffffffffffffffA1A3S0S5S6S14RfA1ZfA2S7G2A1A3S21S35A1M3S53S38S5eVsegs;R12R11R13S20G3S32R3S33R2R1A2A4A5R16R13R12R4R2A4S52R4U0A2G1S12G0R12A2G1S1S0S19S1dS11G0R2A2M4S39A2G2A3S1S1bG2G4A2S1S1cS1aG4R13A2S3fS36R5A1M5A1A2S1S0S1fS3bS45G5A1R2R1A3S22A3S1S0S1fS3dS37G5A1R2R1A3S22A3S1S19S1S1cS11G0R3A2M6R1A2S1bR1S1aG6R14A2A2A2S0S23S61A1S54Vsegs;R2Z1A3S29S61A1A3F_;Fz;S1G1S2cG1R1R16A3S1S1cS11G0R4A2M7G4A2S1bG4S1aG7R15A2M8A2A2S0S1fS44R3S42R8A1A2S22A3F_;F_;Fp;S1SaS2cSaR1SfS14R18A1A1A3SdScR18R2A2S20S19S19G7G8A4A2F_;Fo;S1S24S5S5A2M9S19S2cG9R2S16R19A1A3S1S1cS11G0S8R19S27S5S5R3A3A2A2MaR2A2S1bR2S1aGaS11G0S8R19S28S5S5R3A3A2A2A2A2A2S2S1S1cS11G0R6A2MbS11G0S18S11G0S8R1aS17R1bA1A2A2R3A2A2McA2S1bGcS1aGbR17A2A2A2A1F_;F_;Fy;Frr;R18S2dR16S63S9R16A1S64R15A1R2R1A4A2R15R7S65S52R6U3A2R5R2R1A4A4A2A2A2A2A2A2A2A2A2Tn;Ta;F_;F_;Fmd;Fms;Ftr;S4dVsegs;S2eVsegs;R13R11R10RfA5S4cS2eVsegs;R13S5dR12RfA2S2dR11S63S9R11A1S64R10A1S8R11RfA2S12G0ReA2A4A2R10R1A6Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fea;Ftp;Frho;FA;FJok;FJ;").
Proof using .
  intros J Jok A rho tp ea nlit Hst Hi H17 H10 H11 Hmod Hn H12 H13 H14 H15 HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  destruct (munmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite H10 in G0. rewrite H12 in G2. rewrite H13 in G3. rewrite H14 in G4. rewrite H15 in G5. cbn [eval] in G2, G3, G4, G5.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hpos & Hceil & Hfreeres & Hcont & Hseg & Htl & Hdisj & Hxs & HJok).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_fixed_rw_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnrw & Hnnone & Hnfn).
  { rewrite G2. reflexivity. } { rewrite G3. apply mmap_flags_core_16434. reflexivity. }
  { rewrite G5. reflexivity. }
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16434; reflexivity).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite HnZ; exact Hceil).
  rewrite <- HnE in Hfreeres, Hcont.
  pose proof (alloc_top_lt (m_vmmaps md)) as CL.
  assert (Hend : bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit) <= 2 ^ 64) by (rewrite Un; unfold two_pow_64 in CL; lia).
  assert (Hsw : swf (ax_S A) = true) by exact (smatch_pendingA_swf segs _ _ _ _ Hsp).
  assert (Hea : sv_below (ss_next (ax_S A)) ea = true).
  { rewrite <- H10. unfold reg_sv. apply (proj1 (forallb_forall _ _) (swf_regs_below _ Hsw)). apply nth_In.
    rewrite (swf_regs_len _ Hsw). cbn. lia. }
  assert (Hb : mmap_fixed_rw_budget_ok (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite HnE. apply (rereserve_budget_ok md tp); [exact HMI | exact Enr | exact Hal | rewrite Un; unfold page_size; exact Hmod | rewrite Un; lia | exact Hend]. }
  eexists. split.
  { exact (wstep_fixed_rw_commit_intro_okA segs ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Hal Hpos Hfreeres Hcont tr Hp Hb). }
  rewrite HnE. rewrite <- G0. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HJok].
  unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Enr. unfold A_after.
  eapply (smatchA_after_rereserve segs rho _ tp A tr ms md tr (mmap_fixed_rw_next (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
            (ms_gpr ms 0) (Z_to_bv 64 nlit) (ms_gpr ms 0) ea (ss_next (ax_S A)) Hsp); try reflexivity.
  all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
       try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
       try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
       try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
Qed.

End N.
