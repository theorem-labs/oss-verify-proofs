(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "nil"; "prod"; "pair"; "bool"; "cons"; "nat"; "option"; "Some"; "true"; "andb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise"; "madvise_dontneed_next"; "madvise_dontneed_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "SyscallEffect"; "event"; "MemCopy"; "m_vmmaps"; "in_arg"; "m_vm_lazy"; "m_vm_materialized"; "mkEffectU"; "m_fds"; "m_fs"; "m_halted"; "page_outside_range"; "page_size"; "two_pow_64"; "FdEntry"; "VmMaps"; "with_vm_backing"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude"; "check_result"; "CheckReject"; "CheckOk"; "listNN_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_svc_pending"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "int32"; "w_is0"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "MADV_DONTNEED"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vmd"; "@Stdlib.Lists.List"; "filter"; "@LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs"; "check_syscall"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseSpecA"; "madvise_dontneed_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section MadviseDontneed.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 233%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let n := mmap_n len.
  Hypothesis Hadv : ltac2:(tb__ "0|0|
S0S27S2Q40S34S16Vi;U2A2A1A2S36A3").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S27S2dS2Q40Vaddr;A2S1eA2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S2cS2bS2Q40Vaddr;A2S39Vlen;A1A2S1fA2").
  Hypothesis Hok : ltac2:(tb__ "0|0|
S0S8S10S15Vm;A1Vaddr;Vn;A3SdA3").

  Lemma madvise_dontneed_reduce : ltac2:(tb__ "0|8|
S12S0S23S3fVi;R1Vm;A3S12S23Leff;R1S1Q40A1M0S4S6G0S4S1Q8A1A1A2M1A1M2S4S6G0G0A2M3A1M4G4S4S14A1M5S4S6G0SaA2M6A1M7G2S23Leff_writes;R5G4S23Leff_unmaps;R3G5S23Leff_copies;R2G7S23Leff_copyins;R1S8S23L_;SeS35R6A1S26R4S9G3S7G0G0Vaddr;Vn;A4S5G3A1A3A2A2S25SfVm;Vaddr;Vn;A3S5S13A1A2S24X8x2G6G7S24Ll;Lp;X4x2S14G5S24Ll;Lm0;X4x2G3G4S24Ll;Lp;X4x2G1G2S24Ll;Lp;X4x2Leff_copyins;Leff_copies;Leff_unmaps;Lzs;Leff_writes;Lr;X12x1A3Feff;").
  Proof using Hadv Halign Hlen Hno Hok Hwrap.
    intros eff. rewrite (check_syscall_madvise i eff m Hno). unfold check_madvise.
    fold addr. fold len. rewrite Halign. cbn [Z.eqb negb].
    unfold madvise_dontneed_b. rewrite Hadv. cbn [Z.eqb Pos.eqb MADV_DONTNEED negb].
    assert (G : w_is0 len = false) by (destruct (w_is0 len) eqn:E; [apply w_is0_spec in E; contradiction|reflexivity]).
    rewrite G.
    destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z eqn:E1.
    { apply Z.leb_le in E1. unfold mmap_nZ in Hwrap. lia. }
    cbv zeta. unfold n, mmap_n, mmap_nZ in Hok. rewrite Hok. reflexivity.
  Qed.

  Lemma madvise_dontneed_inv : ltac2:(tb__ "0|5|
S2fS12A1M0S30Vi;Vm;R1A3S0G0R2S2eS12S19S3Q40M1Z0A2S5S6S1G1A1M2S4S1Q8A1A1A2A1S9S6G2G2A2M3S7G2G2Vaddr;Vn;A4S5G3A1M4A3G4S5S14A1S5S6G2SaA2A1A6SfVm;Vaddr;Vn;A3S5S13A1A4A3F_;FR;").
  Proof using Hadv Halign Hlen Hno Hok Hwrap.
    intros R Hs. apply spec_check in Hs. destruct R as [eff m' evs|]; cbn in Hs.
    - rewrite madvise_dontneed_reduce in Hs.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate].
      destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r && listNN_eqb zs [(addr, n)]) eqn:G; [|discriminate].
      apply andb_true_iff in G as [G1 G2]. apply w_is0_spec in G1. apply listNN_eqb_eq in G2.
      subst. inversion Hs; subst. reflexivity.
    - exfalso. specialize (Hs probe_eff). rewrite madvise_dontneed_reduce in Hs. unfold probe_eff in Hs.
      cbn in Hs. discriminate.
  Qed.

  Lemma madvise_dontneed_intro_ss : ltac2:(tb__ "0|4|
S30Vi;Vm;S2eS12S19S3Q40M0Z0A2S5S6S1G0A1M1S4S1Q8A1A1A2A1S9S6G1G1A2M2S7G1G1Vaddr;Vn;A4S5G2A1M3A3G3S5S14A1S5S6G1SaA2A1A6SfVm;Vaddr;Vn;A3S5S13A1A4A3").
  Proof using Hadv Halign Hlen Hno Hok Hwrap.
    apply check_spec_ok. rewrite madvise_dontneed_reduce.
    change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  Qed.

  Lemma madvise_dontneed_intro : ltac2:(tb__ "0|4|
S43Vi;Vm;S2eS12S19S3Q40M0Z0A2S5S6S1G0A1M1S4S1Q8A1A1A2A1S9S6G1G1A2M2S7G1G1Vaddr;Vn;A4S5G2A1M3A3G3S5S14A1S5S6G1SaA2A1A6SfVm;Vaddr;Vn;A3S5S13A1A4A3").
  Proof using Hadv Halign Hlen Hno Hok Hwrap.
    intros. split; [eapply madvise_dontneed_intro_ss; eassumption|].
    intros eff0 m0 evs0 Eq Hg. injection Eq; intros ? ? ?; subst eff0 m0 evs0. ns_auto.
  Qed.
End MadviseDontneed.

Lemma dontneed_next_eq : ltac2:(tb__ "0|3|
S11S1Q40M0A1M1G1S0S11SfR3R2R1A3S22S17R3A1S3eG1S1dS2G0R2A2M2S2bG2S2G0R1A2A2A2S18R3A1A3R3A3A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_vmmaps_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0S21S15SfR3R2R1A3A1S15R3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0S4S6G0G0A2A1S17SfR3R2R1A3A1S17R3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_vm_materialized_dontneed_next : ltac2:(tb__ "0|3|
S11S1Q40M0A1M1G1S0S4G1A1S18SfR3R2R1A3A1S3eG1S1dS2G0R2A2M2S2bG2S2G0R1A2A2A2S18R3A1A3A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_halted_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0SbG0A1S1cSfR3R2R1A3A1S1cR3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_fds_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0S4S6G0S20A2A1S1aSfR3R2R1A3A1S1aR3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma m_fs_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0S40S1bSfR3R2R1A3A1S1bR3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.
Lemma vmd_dontneed_next : ltac2:(tb__ "0|1|
S11S1Q40A1M0G0S0S11S3dSfR3R2R1A3A1S3dR3A1A3Fk;Fa;Fm;").
Proof. reflexivity. Qed.

Section W.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Section MadviseA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 233%Z.
  Hypothesis Hadv : ltac2:(tb__ "0|0|
S0S27S2Q40S34S33Vms;U2A2A1A2S36A3").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S27S2dS2Q40Vaddr;A2S1eA2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S2cS2bS2Q40Vaddr;A2S39Vlen;A1A2S1fA2").
  Hypothesis Hok : ltac2:(tb__ "0|0|
S0S8S10S15Vm;A1Vaddr;Vn;A3SdA3").

  Let INV : ltac2:(tb__ "0|8|
S2fS12A1M0S30S2aVsegs;Vms;Vx8;A3M1Vm;R1A3S0G0R2S2eS12S19S3Q40M2Z0A2S5S6S1G2A1M3S4S1Q8A1A1A2A1S9S6G3G3A2M4S7G3G3S16G1U0A2M5S3aS16G1U1A2A1M6A4S5G4A1M7A3G7S5S14A1S5S6G3SaA2A1A6SfVm;G5G6A3S5S13A1A4A3F_;FR;") := ltac2:(tb__ "0|0|
S41S2aVsegs;Vms;Vx8;A3Vm;VHno;VHadv;VHalign;VHlen;VHwrap;VHok;A8").

  Lemma madvise_only_okA : ltac2:(tb__ "0|0|
S42S2aVsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R HR; exact (INV R HR)| |].
    - intros E; discriminate.
    - intros eff m' evs E _; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_madvise_invA : ltac2:(tb__ "0|3|
S4S13A1M0S37S0SbS1Q40M1A1M2A1S32Vms;A1ScG2Vx8;A2A3S38Vsegs;S7G0S28R3S29Vms;Vm;A2A4R2A3S0S37R3S7G0S28R4S29S3bVms;S3G1Z0A2S3cS31Vms;A1Vaddr;Vn;A3A3SfVm;Vaddr;Vn;A3A2A4A3F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec. inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
    - cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
    - exfalso. revert Hcd. rewrite m_halted_dontneed_next. congruence.
  Qed.

  Lemma wstep_madvise_introA : ltac2:(tb__ "0|3|
S4S13A1M0S0SbS1Q40M1A1M2A1S32Vms;A1ScG2Vx8;A2A3S38Vsegs;S7G0S28R2S29Vms;Vm;A2A4S7G0S28R2S29S3bVms;S3G1Z0A2S3cS31Vms;A1Vaddr;Vn;A3A3SfVm;Vaddr;Vn;A3A2A4A3F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp.
    pose proof (@madvise_dontneed_intro (sys_input segs ms x8) m Hno Hadv Halign Hlen Hwrap Hok) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite m_halted_dontneed_next; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End MadviseA.

End W.
