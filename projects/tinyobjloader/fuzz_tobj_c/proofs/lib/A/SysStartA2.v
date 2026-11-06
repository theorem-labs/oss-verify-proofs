(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "pair"; "option"; "Some"; "list"; "bool"; "true"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "mmap_nZ"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_svc_pending"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_halted"; "TASK_SIZE"; "m_vmmaps"; "map_has"; "page_size"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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

Section MunmapExactA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 215%Z.
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S1cS20SeQ40Vaddr;A2S16A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.

  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S1fS1eSeQ40Vaddr;A2SbVlen;A1A2S13A2").
  Hypothesis Hhas : ltac2:(tb__ "0|0|
S0S5S15S17S14Vm;A1A1Vaddr;Vn;A3S6A3").

  Lemma munmap_model_halted : ltac2:(tb__ "0|1|
ScQ40A1M0G0S0S2G0A1S12SaVm;R2R1A3A1S12Vm;A1A3Fk;Fa;").
  Proof using .
    intros. unfold munmap_model, with_mmap_destroyed, vm_forget_range. autorewrite with model. reflexivity.
  Qed.

  Lemma munmap_exact_only_okA : ltac2:(tb__ "0|0|
S1dS9Vsegs;Vms;Vx8;A3Vm;A2").
  Proof using Halign Hhas Hlen Hno Hwrap.
    eapply only_okA_of_inv; [intros R HR; exact (@munmap_exact_inv (sys_input segs ms x8) m Hno Halign Hlen Hwrap R Hhas HR)| |].
    - intros E; discriminate.
    - intros eff m' evs E _; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_munmap_exact_invA : ltac2:(tb__ "0|3|
S4S11A1M0S18S0S2ScQ40M1A1M2A1S10Vms;A1S3G2Vx8;A2A3S19Vsegs;S1G0S7R3S8Vms;Vm;A2A4R2A3S0S18R3S1G0S7R4S8S1aVms;SdG1Z0A2S1bSfVms;A1Vaddr;Vn;A3A3SaVm;Vaddr;Vn;A3A2A4A3F_;F_;Fw';Ftr;").
  Proof using Halign Hh Hhas Hlen Hno Hwrap.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@munmap_exact_inv (sys_input segs ms x8) m Hno Halign Hlen Hwrap _ Hhas) in Hspec.
    inversion Hspec; subst.
    destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
    - cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
    - exfalso. revert Hcd. unfold addr, n. rewrite munmap_model_halted. congruence.
  Qed.

  Lemma wstep_munmap_exact_introA : ltac2:(tb__ "0|3|
S4S11A1M0S0S2ScQ40M1A1M2A1S10Vms;A1S3G2Vx8;A2A3S19Vsegs;S1G0S7R2S8Vms;Vm;A2A4S1G0S7R2S8S1aVms;SdG1Z0A2S1bSfVms;A1Vaddr;Vn;A3A3SaVm;Vaddr;Vn;A3A2A4A3F_;Ftr;").
  Proof using Halign Hh Hhas Hlen Hno Hwrap.
    intros tr Hp.
    pose proof (@munmap_exact_intro (sys_input segs ms x8) m Hno Halign Hlen Hwrap Hhas) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite munmap_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.
End MunmapExactA.
End M.
