(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "or"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "ms_svc_pending"; "ms_mem"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "nil"; "true"; "prod"; "false"; "list"; "option"; "Some"; "cons"; "nat"; "app"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "in_arg"; "ENOMEM"; "errno_ret"; "SyscallEffect"; "m_vmmaps"; "mkEffectU"; "MemCopy"; "alloc_top"; "page_size"; "region_free"; "vm_maps"; "vm_reserved"; "m_halted"; "map_contains"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_none_model"; "mmap_rw_model"; "is_ret"; "mmap_n"; "mmap_fixed_dead_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "after_sys"; "zero_range"; "unmap_range"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_backed_ok"; "mmap_fixed_noaccess_b"; "mmap_modeled_b"; "mmap_noaccess_b"; "mmap_fixed_rw_b"; "mmap_fixed_rw_budget_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_fixed_fresh_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreplace_noaccess_b"; "mmap_noreplace_rw_b"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "mmap_fixed_none_fresh_inv"; "mmap_fixed_rw_commit_inv"; "mmap_fixed_rw_fresh_inv"; "mmap_noreplace_none_fresh_inv"; "mmap_noreplace_rw_fresh_inv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Section FixedRwFreshA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S6S38S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3S9A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S6S35S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S6S37S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S6S36S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S41S40S16Q40Vaddr;A2S28Vlen;A1A2S1fS1cVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S3dS42S16Q40Vaddr;A2S20A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|2|
S0S6S21S11SaS15Q40A1M0G0A2S23S1cVm;A1M1A1S22G1A1A3Vaddr;Vn;A3S9A3").

  Let INV : ltac2:(tb__ "0|9|
S33S1bA1M0S3eS14Vsegs;Vms;Vx8;A3M1Vm;R1A3S1S2bR2S1aS19A1Vm;S8S17A1M2A4S2S0S6S34S18G1U3A2M3Vm;S28S18G1U1A2M4A1A3S9A3S0G0R2S32S1bS1dS18G1U0A2M5S8SaS15Q40A1M6ScS15Q8A1A1A2A1SfSaG6G6A2M7S7G6G6G5S2cG4A1A4S8G7A1M8A3G8S8S1eA1S8SaG6S10A2A1A6S2aG3Vm;G4G5A4G2A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S46S14Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_fn;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfresh;Ac").

  Lemma fixed_rw_fresh_only_okA : ltac2:(tb__ "0|0|
S3fS14Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | (_ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (_ & E)] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_fixed_rw_fresh_invA : ltac2:(tb__ "0|2|
ScS17A1M0S26S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4R2A3S1S0S26R3S7G0S12R4S13S2fVms;S1aS19A1A2Vm;A2A4A3S2S0S6S34Vflags;Vm;S28Vlen;A1A3S9A3S0S26R3S7G0S12R4S13S2eVms;Vaddr;S30S5Vms;A1Vaddr;Vn;A3A3S2aVflags;Vm;Vlen;Vaddr;A4A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | (Hb & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right. split; [exact Hb|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold flags, len, addr. rewrite (mmap_rw_model_halted m). congruence.
  Qed.

  Lemma wstep_fixed_rw_fresh_intro_failA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S0S6S3aVflags;Vm;S28Vlen;A1A3S9A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4S7G0S12R3S13S2fVms;S1aS19A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hrf. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mmap_fixed_rw_fresh_intro_fail (sys_input segs ms x8) m Hno Hlen Hshape Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfresh Hrf).
  Qed.

  Lemma wstep_fixed_rw_fresh_intro_okA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S0S6S34Vflags;Vm;S28Vlen;A1A3S9A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4S7G0S12R3S13S2eVms;Vaddr;S30S5Vms;A1Vaddr;Vn;A3A3S2aVflags;Vm;Vlen;Vaddr;A4A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb.
    pose proof (@mmap_fixed_rw_fresh_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfresh Hb) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite (mmap_rw_model_halted m); exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End FixedRwFreshA.

Section FixedNoneFreshA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S6S35S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3S9A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S6S37S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S6S36S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S41S40S16Q40Vaddr;A2S28Vlen;A1A2S1fS1cVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S3dS42S16Q40Vaddr;A2S20A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|2|
S0S6S21S11SaS15Q40A1M0G0A2S23S1cVm;A1M1A1S22G1A1A3Vaddr;Vn;A3S9A3").

  Let INV : ltac2:(tb__ "0|8|
S33S1bA1M0S3eS14Vsegs;Vms;Vx8;A3M1Vm;R1A3S1S2bR2S1aS19A1Vm;S8S17A1M2A4S0G0R2S32S1bS1dS18G1U0A2M3S8SaS15Q40A1M4ScS15Q8A1A1A2A1S8SaG4G4A2M5A1M6SfG5S7G4G4G3S2cS18G1U1A2M7A1A4G6A3S8S1eA1S8SaG4S10A2A1A6S29S18G1U3A2Vm;G7G3A4G2A4A3A2F_;FR;") := ltac2:(tb__ "0|0|
S44S14Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfresh;Ab").

  Lemma fixed_none_fresh_only_okA : ltac2:(tb__ "0|0|
S3fS14Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | E]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | E] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_fixed_none_fresh_invA : ltac2:(tb__ "0|2|
ScS17A1M0S26S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4R2A3S1S0S26R3S7G0S12R4S13S2fVms;S1aS19A1A2Vm;A2A4A3S0S26R3S7G0S12R4S13S2eVms;Vaddr;S31S5Vms;A1Vaddr;Vn;A3A3S29Vflags;Vm;Vlen;Vaddr;A4A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | E]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold flags, len, addr. rewrite (mmap_none_model_halted m). congruence.
  Qed.

  Lemma wstep_fixed_none_fresh_intro_okA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R2S13Vms;Vm;A2A4S7G0S12R2S13S2eVms;Vaddr;S31S5Vms;A1Vaddr;Vn;A3A3S29Vflags;Vm;Vlen;Vaddr;A4A2A4A3F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp.
    pose proof (@mmap_fixed_none_fresh_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_none Hnot_rw Hceil Halign Hpos Hfresh) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite (mmap_none_model_halted m); exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.
End FixedNoneFreshA.

Section FixedRwCommitA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S6S38S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3S9A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S6S35S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S6S37S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S6S36S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S41S40S16Q40Vaddr;A2S28Vlen;A1A2S1fS1cVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S3dS42S16Q40Vaddr;A2S20A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S6S21S23S1cVm;A1A1Vaddr;Vn;A3S9A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S6S25S22S1cVm;A1A1Vaddr;Vn;A3S9A3").

  Let INV : ltac2:(tb__ "0|e|
S33S1bA1M0S3eS14Vsegs;Vms;Vx8;A3M1Vm;R1A3S1S2bR2S1aS19A1M2Vm;S8S17A1M3A4S1S2S0S6S39S18G1U3A2M4Vm;S18G1U0A2M5S2cS18G1U1A2A1M6A4S9A3S0G0R2S32S1bS1dG5S8SaS15Q40A1M7ScS15Q8A1A1A2A1M8SfSaG7G7A2M9S7G7G7G5G6A4S8G9A1MaA3MbGaS8S1eA1McS8SaG7S10A2A1MdA6S43G4Vm;G5G6A4G3A4A3A2S0G0R2S32S1bS1dG2G8GaGbGcGdA6S2dVm;G5G6A3G3A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S45S14Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_fn;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfree;VHcont;Ad").

  Lemma mmap_fixed_rw_ok_model_halted : ltac2:(tb__ "0|1|
S15Q40A1M0G0G0S0SdG0A1S24S43R3Vm;R2R1A4A1S24Vm;A1A3Fk;Fa;Ffl;").
  Proof using .
    intros. unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
    destruct (mmap_noreserve_b fl); autorewrite with model; reflexivity.
  Qed.
  Lemma mmap_fixed_dead_model_halted : ltac2:(tb__ "0|1|
S15Q40A1M0G0S0SdG0A1S24S2dVm;R2R1A3A1S24Vm;A1A3Fk;Fa;").
  Proof using .
    intros. unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range. autorewrite with model. reflexivity.
  Qed.

  Lemma fixed_rw_commit_only_okA : ltac2:(tb__ "0|0|
S3fS14Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | [(_ & E) | E]]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | [(_ & E) | E]] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_fixed_rw_commit_invA : ltac2:(tb__ "0|4|
ScS17A1M0S26S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4R2A3S1S0S26R3S7G0S12R4S13S2fVms;S1aS19A1M2A2Vm;A2A4A3S1S2S0S6S39Vflags;Vm;Vaddr;Vn;A4S9A3S0S26R3S7G0S12R4S13S2eVms;Vaddr;S30S5Vms;A1M3Vaddr;Vn;A3A3S43Vflags;Vm;Vaddr;Vn;A4A2A4A3A2S0S26R3S7G0S12R4S13S2eVms;G2S31G3Vaddr;Vn;A3A3S2dVm;Vaddr;Vn;A3A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | [(Hb & E) | E]]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right; left. split; [exact Hb|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold flags, len, addr, n. rewrite mmap_fixed_rw_ok_model_halted. congruence.
    - right; right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold addr, n. rewrite mmap_fixed_dead_model_halted. congruence.
  Qed.

  Lemma wstep_fixed_rw_commit_intro_okA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S0S6S39Vflags;Vm;Vaddr;Vn;A4S9A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4S7G0S12R3S13S2eVms;Vaddr;S30S5Vms;A1Vaddr;Vn;A3A3S43Vflags;Vm;Vaddr;Vn;A4A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb.
    pose proof (@mmap_fixed_rw_commit_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfree Hcont Hb) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mmap_fixed_rw_ok_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End FixedRwCommitA.

Section NoreplaceRwFreshA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S6S3cS3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3S9A3").
  Hypothesis Hnot_nrn : ltac2:(tb__ "0|0|
S0S6S3bS3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_frw : ltac2:(tb__ "0|0|
S0S6S38S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S6S35S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S6S37S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S6S36S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S41S40S16Q40Vaddr;A2S28Vlen;A1A2S1fS1cVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S3dS42S16Q40Vaddr;A2S20A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|2|
S0S6S21S11SaS15Q40A1M0G0A2S23S1cVm;A1M1A1S22G1A1A3Vaddr;Vn;A3S9A3").

  Let INV : ltac2:(tb__ "0|9|
S33S1bA1M0S3eS14Vsegs;Vms;Vx8;A3M1Vm;R1A3S1S2bR2S1aS19A1Vm;S8S17A1M2A4S2S0S6S34S18G1U3A2M3Vm;S28S18G1U1A2M4A1A3S9A3S0G0R2S32S1bS1dS18G1U0A2M5S8SaS15Q40A1M6ScS15Q8A1A1A2A1SfSaG6G6A2M7S7G6G6G5S2cG4A1A4S8G7A1M8A3G8S8S1eA1S8SaG6S10A2A1A6S2aG3Vm;G4G5A4G2A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S48S14Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_nrn;VHnot_frw;VHnot_fn;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfresh;Ae").

  Lemma noreplace_rw_fresh_only_okA : ltac2:(tb__ "0|0|
S3fS14Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | (_ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (_ & E)] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_noreplace_rw_fresh_invA : ltac2:(tb__ "0|2|
ScS17A1M0S26S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4R2A3S1S0S26R3S7G0S12R4S13S2fVms;S1aS19A1A2Vm;A2A4A3S2S0S6S34Vflags;Vm;S28Vlen;A1A3S9A3S0S26R3S7G0S12R4S13S2eVms;Vaddr;S30S5Vms;A1Vaddr;Vn;A3A3S2aVflags;Vm;Vlen;Vaddr;A4A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | (Hb & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right. split; [exact Hb|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold flags, len, addr. rewrite (mmap_rw_model_halted m). congruence.
  Qed.

  Lemma wstep_noreplace_rw_fresh_intro_failA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S0S6S3aVflags;Vm;S28Vlen;A1A3S9A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4S7G0S12R3S13S2fVms;S1aS19A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hrf. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mmap_noreplace_rw_fresh_intro_fail (sys_input segs ms x8) m Hno Hlen Hshape Hnot_nrn Hnot_frw Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfresh Hrf).
  Qed.

  Lemma wstep_noreplace_rw_fresh_intro_okA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S0S6S34Vflags;Vm;S28Vlen;A1A3S9A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4S7G0S12R3S13S2eVms;Vaddr;S30S5Vms;A1Vaddr;Vn;A3A3S2aVflags;Vm;Vlen;Vaddr;A4A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb.
    pose proof (@mmap_noreplace_rw_fresh_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_nrn Hnot_frw Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfresh Hb) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite (mmap_rw_model_halted m); exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End NoreplaceRwFreshA.

Section NoreplaceNoneFreshA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S6S3bS3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3S9A3").
  Hypothesis Hnot_frw : ltac2:(tb__ "0|0|
S0S6S38S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S6S35S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S6S37S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S6S36S3Vms;U2A2S3Vms;U3A2S3Vms;U5A2A3SbA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S41S40S16Q40Vaddr;A2S28Vlen;A1A2S1fS1cVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S3dS42S16Q40Vaddr;A2S20A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfresh : ltac2:(tb__ "0|2|
S0S6S21S11SaS15Q40A1M0G0A2S23S1cVm;A1M1A1S22G1A1A3Vaddr;Vn;A3S9A3").

  Let INV : ltac2:(tb__ "0|8|
S33S1bA1M0S3eS14Vsegs;Vms;Vx8;A3M1Vm;R1A3S1S2bR2S1aS19A1Vm;S8S17A1M2A4S0G0R2S32S1bS1dS18G1U0A2M3S8SaS15Q40A1M4ScS15Q8A1A1A2A1S8SaG4G4A2M5A1M6SfG5S7G4G4G3S2cS18G1U1A2M7A1A4G6A3S8S1eA1S8SaG4S10A2A1A6S29S18G1U3A2Vm;G7G3A4G2A4A3A2F_;FR;") := ltac2:(tb__ "0|0|
S47S14Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_frw;VHnot_fn;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfresh;Ad").

  Lemma noreplace_none_fresh_only_okA : ltac2:(tb__ "0|0|
S3fS14Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | E]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | E] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_noreplace_none_fresh_invA : ltac2:(tb__ "0|2|
ScS17A1M0S26S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R3S13Vms;Vm;A2A4R2A3S1S0S26R3S7G0S12R4S13S2fVms;S1aS19A1A2Vm;A2A4A3S0S26R3S7G0S12R4S13S2eVms;Vaddr;S31S5Vms;A1Vaddr;Vn;A3A3S29Vflags;Vm;Vlen;Vaddr;A4A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | E]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold flags, len, addr. rewrite (mmap_none_model_halted m). congruence.
  Qed.

  Lemma wstep_noreplace_none_fresh_intro_okA : ltac2:(tb__ "0|2|
ScS17A1M0S0SdS15Q40A1M1A1S4Vms;A1SeG1Vx8;A2A3S27Vsegs;S7G0S12R2S13Vms;Vm;A2A4S7G0S12R2S13S2eVms;Vaddr;S31S5Vms;A1Vaddr;Vn;A3A3S29Vflags;Vm;Vlen;Vaddr;A4A2A4A3F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp.
    pose proof (@mmap_noreplace_none_fresh_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_frw Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfresh) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite (mmap_none_model_halted m); exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.
End NoreplaceNoneFreshA.
End M.
