(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "false"; "pair"; "prod"; "list"; "cons"; "Some"; "option"; "app"; "fst"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "eval"; "ss_next"; "ss_objs"; "DZero"; "cell"; "mkObj"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "in_arg"; "m_vmmaps"; "event"; "SyscallEffect"; "alloc_top"; "map_contains"; "region_free"; "vm_maps"; "vm_reserved"; "ENOMEM"; "errno_ret"; "MemCopy"; "Model"; "mkEffectU"; "page_size"; "vm_forget_range"; "with_vmmaps"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "ms_svc_pending"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "ge"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "wstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_fixed_commit_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_noaccess_b"; "mmap_fixed_rw_b"; "mmap_fixed_rw_budget_ok"; "mmap_modeled_b"; "mmap_noaccess_b"; "mmap_fixed_rw_next"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "is_ret"; "mmap_nZ"; "mmap_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "after_sys_mem"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA.M"; "mmap_fixed_rw_commit_inv2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA SysCallA MmapA MmapFixedA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Section MmapFixedRwCommit2.
  Variables (i : SyscallInput) (m : Model).
  Hypothesis Hno : bv_unsigned (in_sysno i) = 222%Z.
  Let addr := in_arg i 0.
  Let len := in_arg i 1.
  Let flags := in_arg i 3.
  Let h := m_vmmaps m.
  Let n := mmap_n len.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S4S57S29Vi;U2A2S29Vi;U3A2S29Vi;U5A2A3S5A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S4S56S29Vi;U2A2S29Vi;U3A2S29Vi;U5A2A3S7A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S4S5aS29Vi;U2A2S29Vi;U3A2S29Vi;U5A2A3S7A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S4S59S29Vi;U2A2S29Vi;U3A2S29Vi;U5A2A3S7A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S41S3aQ40Vaddr;A2S62Vlen;A1A2S2dS2aVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S28S44S3aQ40Vaddr;A2S37A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S4S2fS31Vh;A1Vaddr;Vn;A3S5A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S4S2eS30Vh;A1Vaddr;Vn;A3S5A3").
  Hypothesis HB : mmap_fixed_rw_budget_ok flags m addr n = true.

  Lemma mmap_fixed_rw_commit_inv2 : ltac2:(tb__ "0|5|
S5fS2cA1M0S6eVi;Vm;R1A3S2S1S0S4S55Vflags;Vm;Vaddr;Vn;A4S5A3S61R2S33S32A1Vm;S6S2bA1M1A4A2S1S0S4S58Vflags;Vm;Vaddr;Vn;A4S5A3S0G0R2S5eS2cS36Vaddr;S6S9S3bQ40A1M2SaS3bQ8A1A1A2A1SbS9G2G2A2M3S8G2G2Vaddr;Vn;A4S6G3A1M4A3G4S6S34A1S6S9G2S10A2A1A6S5dVflags;Vm;Vaddr;Vn;A4G1A4A3A2A2F_;FR;").
  Proof using Halign Hceil Hcont Hfree Hlen Hno Hnot_fn Hnot_none Hnot_rw Hpos Hshape HB.
    intros R [Hs Hns]. right. split; [exact HB|].
    pose proof (mmap_place_not_errno _ addr (mmap_nZ len) (mmap_nZ_nonneg len) Hceil) as Hna.
    pose proof (mmap_fixed_rw_commit_intro_ok i m Hno Hlen Hshape Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfree Hcont HB) as Hok.
    destruct (mmap_fixed_rw_commit_inv i m Hno Hlen Hshape Hnot_fn Hnot_none Hnot_rw Hceil Halign Hpos Hfree Hcont R Hs)
      as [He | [(_ & E) | E]]; [exfalso | exact E | exfalso].
    - unfold is_ret in He. subst R.
      pose proof (ns_enomem_mmap _ _ _ _ _ _ (Hns _ _ _ eq_refl eq_refl) Hno eq_refl Hok) as X.
      cbn [eff_ret] in X. unfold addr in *. rewrite X in Hna. vm_compute in Hna. discriminate Hna.
    - subst R.
      assert (Hg : m_halted (mmap_fixed_dead_model m addr n) = m_halted m)
        by (unfold mmap_fixed_dead_model, with_mmap_destroyed; autorewrite with model; reflexivity).
      pose proof (ns_enomem_mmap _ _ _ _ _ _ (Hns _ _ _ eq_refl Hg) Hno eq_refl Hok) as X.
      cbn [eff_ret] in X. unfold addr in *. rewrite X in Hna. vm_compute in Hna. discriminate Hna.
  Qed.
End MmapFixedRwCommit2.

Section FixedRwCommitA2.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S4S57S3dVms;U2A2S3dVms;U3A2S3dVms;U5A2A3S5A3").
  Hypothesis Hnot_fn : ltac2:(tb__ "0|0|
S0S4S56S3dVms;U2A2S3dVms;U3A2S3dVms;U5A2A3S7A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S4S5aS3dVms;U2A2S3dVms;U3A2S3dVms;U5A2A3S7A3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S4S59S3dVms;U2A2S3dVms;U3A2S3dVms;U5A2A3S7A3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S42S41S3aQ40Vaddr;A2S62Vlen;A1A2S2dS2aVm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S28S44S3aQ40Vaddr;A2S37A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S4S2fS31S2aVm;A1A1Vaddr;Vn;A3S5A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S4S2eS30S2aVm;A1A1Vaddr;Vn;A3S5A3").
  Hypothesis HB : mmap_fixed_rw_budget_ok flags m addr n = true.

  Let INV : ltac2:(tb__ "0|9|
S5fS2cA1M0S6eS49Vsegs;Vms;Vx8;A3M1Vm;R1A3S2S1S0S4S55S29G1U3A2M2Vm;S29G1U0A2M3S63S29G1U1A2A1M4A4S5A3S61R2S33S32A1Vm;S6S2bA1M5A4A2S1S0S4S58G2Vm;G3G4A4S5A3S0G0R2S5eS2cS36G3S6S9S3bQ40A1M6SaS3bQ8A1A1A2A1SbS9G6G6A2M7S8G6G6G3G4A4S6G7A1M8A3G8S6S34A1S6S9G6S10A2A1A6S5dG2Vm;G3G4A4G5A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S6dS49Vsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_fn;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfree;VHcont;VHB;Ae").

  Lemma wstep_fixed_rw_commit_inv2A : ltac2:(tb__ "0|2|
SaS2bA1M0S4cS0SdS3bQ40A1M1A1S40Vms;A1ScG1Vx8;A2A3S4fVsegs;S8G0S47R3S48Vms;Vm;A2A4R2A3S2S1S0S4S55Vflags;Vm;Vaddr;Vn;A4S5A3S0S4cR3S8G0S47R4S48S6aVms;S33S32A1A2Vm;A2A4A3A2S1S0S4S58Vflags;Vm;Vaddr;Vn;A4S5A3S0S4cR3S8G0S47R4S48S6bVms;Vaddr;S6cS3fVms;A1Vaddr;Vn;A3A3S5dVflags;Vm;Vaddr;Vn;A4A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh HB.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv_ns Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [(RF & E) | (Hb & E)]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact RF|]. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right. split; [exact Hb|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold flags, len, addr, n. rewrite (mmap_fixed_rw_ok_model_halted m). congruence.
  Qed.
End FixedRwCommitA2.

Lemma mmap_flags_50_shape : ltac2:(tb__ "0|3|
S3bQ40M0A1M1G1G1S0S28S3aG0R3A2M2Z3A3S0S28G2Z32A3S0S28G2Z0A3S1S0S4S57R6R5R4A3S5A3S1S0S4S56R6R5R4A3S7A3S1S0S4S5aR6R5R4A3S7A3S1S0S4S59R6R5R4A3S7A3S0S4S5cR5A1S7A3A2A2A2A2F_;F_;F_;Foff;Ff;Fp;").
Proof.
  intros p f off Hp Hf Ho.
  assert (Ep : p = Z_to_bv 64 3) by (apply bv_eq; rewrite Hp; reflexivity).
  assert (Ef : f = Z_to_bv 64 50) by (apply bv_eq; rewrite Hf; reflexivity).
  assert (Eo : off = Z_to_bv 64 0) by (apply bv_eq; rewrite Ho; reflexivity).
  subst. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Theorem triple1_fixed_commitA : ltac2:(tb__ "0|f|
S4cOF_;S51S51S26S21SaS3bQ40M0A1M1A1S12S28S53Vsegs;R8R7A3S68Vsegs;R9R8A3S52Vsegs;S17S22R7A1A1R9A3S0SdS4aA1S65Vsegs;S1fS22R8A1A1A2ScS4aS4bA2A3S0S12S14S22R9A1Z11A2S13ZdeA1A3S0S12S14S22RaA1ZaA2R7A3S0S4S20S17S22RbA1A1R8A2S5A3S0S12S14S22RcA1ZbA2S13R8A1A3S0S12S14S22RdA1ZcA2S13Z3A1A3S0S12S14S22ReA1ZdA2S13Z32A1A3S0S12S14S22RfA1ZeA2S13ZffffffffffffffffA1A3S0S12S14S22R10A1ZfA2S13Z0M2A1M3A3S0S28S44RdZ1000M4A2G2A3S1S43G2ReA2S43ReS46Z2Z3eA2A2A2SaS2bA1M5S3eS35S67Vsegs;R15R14R16S8G5S47R3S48R2R1A2A4A5R19R16R15R4R2A4S16R17R15A2G1S3aG0R1A2M6S28S1S0S28S44R1G4A2G2A3S1S43G2R1A2S1S42S41R1R16A2M7S2dS2aR5A1M8A1A2S1S0S4S2fS31G8A1R2S3cG0R16A2M9A3S5A3S1S0S4S2eS30G8A1MaR2G9A3S5A3S1S42S66GaR1G7A3R16A2S1S45S69R5R18A2R16A2S1S15S54S15R1S18S22R1bA1A1A3S1dS1cR1bR2A2S8S28S28R3S41R3R18A2A4A2F_;Fo;S1G1S1S42R2G6A2S43G6S41R2R17A2A2A2S0S4S1eVsegs;R2A2S7A3F_;Fx;S1S9S12S12A2MbS28S54GbR2S23R1cA1A3S1S42S3aG0S16R1cSfS12S12R3A3A2A2McR2A2S43R2S41GcS3aG0S16R1cS11S12S12R3A3A2A2A2A2A2S3S1S42R5S3aG0S27S3aG0S16R1dS24R1eA1A2A2R3A2A2MdA2S43GdS41R5R1aA2A2A2A1F_;F_;Fy;Frr;R1bR19R18R7S38R1G7S39S5bG8R2G9A3R5A2A3A4A2A2A2A2A2A2A2A2A2A2Tua;Ta;F_;F_;Fmd;Fms;Ftr;S4eVsegs;R17S50Vsegs;R16R14R13R12A5S50Vsegs;R15S25R14S64S22R14A1MeR11SeS15S18GeA1SbS15S1bR11G3S13R10A1S6S1aA1S19A5S6S15A1A3A3S17GeA1A4A2R13R12A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Feb;Ftp;Frho;FA;FJo;FJ;Fok;").
Proof using .
  intros ok J Jo A rho tp eb nlit Hokf Hokp Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite H10 in Q0. rewrite H11 in Q1. rewrite H12 in Q2. rewrite H13 in Q3. rewrite H14 in Q4. rewrite H15 in Q5. cbn [eval] in Q1, Q2, Q3, Q4, Q5.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hpos & Hceil & Hfree & Hcont & Hov & Hroom & Hdisj & Hnro & Hxs & HJo).
  set (a := eval rho eb) in *.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite Q1. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  destruct (mmap_flags_50_shape (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) ltac:(rewrite Q2; apply u64_lit; lia) ltac:(rewrite Q3; apply u64_lit; lia) ltac:(rewrite Q5; apply u64_lit; lia))
    as (Hshape & Hnfn & Hnnone & Hnrw & Hnr).
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { rewrite Q1. unfold mmap_nZ. rewrite u64_lit by lia. unfold page_round_up_Z. change page_size with 4096.
    rewrite (Z.div_mod nlit 4096) at 1 by lia. rewrite Hmod, Z.add_0_r.
    replace (4096 * (nlit / 4096) + 4096 - 1) with (4095 + (nlit / 4096) * 4096) by lia. rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (En : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite Q0, HnZ; exact Hceil).
  assert (Halign' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite Q0; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite Q0; exact Hpos).
  assert (Hfree' : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true) by (rewrite Q0, En; exact Hfree).
  assert (Hcont' : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true) by (rewrite Q0, En; exact Hcont).

  assert (HB : mmap_fixed_rw_budget_ok (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { apply mmap_fixed_rw_budget_ok_commit_intro; [exact Hnr | exact (MI_ivs_wf segs _ _ HMI) |].
    rewrite Q0, En, Un. unfold headroom, paid in Hroom. pose proof page_size_pos. fold a. nia. }
  split.
  - eapply Hokp; [exact Hk | exact Hp |].
    apply (fixed_rw_commit_only_okA segs ms md _ H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign' Hpos' Hfree' Hcont').
  - intros w' Hw.
    destruct (wstep_fixed_rw_commit_inv2A ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign' Hpos' Hfree' Hcont' HB tr w' Hp Hw)
      as [(RF & ->) | (_ & ->)].
    + exfalso. unfold mmap_fixed_commit_refusable in RF. rewrite HB in RF. discriminate RF.
    + unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr, Q0, En, Un.
      split.
      * replace (SLit nlit) with (SLit (bv_unsigned (Z_to_bv 64 nlit))) by (rewrite Un; reflexivity).
        replace (bv_unsigned a + nlit) with (bv_unsigned a + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
        apply (smatchA_after_commit_obj segs rho rho tp A tr ms md tr (mmap_fixed_rw_next (m_vmmaps md) a (Z_to_bv 64 nlit)) a (Z_to_bv 64 nlit) a eb eb (ss_next (ax_S A)) Hsp);
          try reflexivity; try assumption; rewrite ?Un; try assumption.
        all: try (change page_size with 4096; exact Hmod).
        all: try (apply agree_below_refl). all: try (apply Pos.le_refl).
        all: pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; try lia.
      * cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem etriple_fixed_commitA : ltac2:(tb__ "0|f|
S51S51S26S21SaS3bQ40M0A1M1A1S12S28S52Vsegs;S17S22R5A1A1R7A3S0SdS4aA1S65Vsegs;S1fS22R6A1A1A2ScS4aS4bA2A3S0S12S14S22R7A1Z11A2S13ZdeA1A3S0S12S14S22R8A1ZaA2R5A3S0S4S20S17S22R9A1A1R6A2S5A3S0S12S14S22RaA1ZbA2S13R6A1A3S0S12S14S22RbA1ZcA2S13Z3A1A3S0S12S14S22RcA1ZdA2S13Z32A1A3S0S12S14S22RdA1ZeA2S13ZffffffffffffffffA1A3S0S12S14S22ReA1ZfA2S13Z0M2A1M3A3S0S28S44RbZ1000M4A2G2A3S1S43G2RcA2S43RcS46Z2Z3eA2A2A2SaS2bA1M5S3eS35S67Vsegs;R13R12R14S8G5S47R3S48R2R1A2A4A5R17R14R13R4R2A4S16R15R13A2G1S3aG0R1A2M6S28S1S0S28S44R1G4A2G2A3S1S43G2R1A2S1S42S41R1R14A2M7S2dS2aR5A1M8A1A2S1S0S4S2fS31G8A1R2S3cG0R14A2M9A3S5A3S1S0S4S2eS30G8A1MaR2G9A3S5A3S1S42S66GaR1G7A3R14A2S1S45S69R5R16A2R14A2S1S15S54S15R1S18S22R19A1A1A3S1dS1cR19R2A2S8S28S28R3S41R3R16A2A4A2F_;Fo;S1G1S1S42R2G6A2S43G6S41R2R15A2A2A2S0S4S1eVsegs;R2A2S7A3F_;Fx;S1S9S12S12A2MbS28S54GbR2S23R1aA1A3S1S42S3aG0S16R1aSfS12S12R3A3A2A2McR2A2S43R2S41GcS3aG0S16R1aS11S12S12R3A3A2A2A2A2A2S3S1S42R5S3aG0S27S3aG0S16R1bS24R1cA1A2A2R3A2A2MdA2S43GdS41R5R18A2A2A2A1F_;F_;Fy;Frr;R19R17R16R7S38R1G7S39S5bG8R2G9A3R5A2A3A4A2A2A2A2A2A2A2A2A2A2Tua;Ta;F_;F_;Fmd;Fms;Ftr;S4dVsegs;S50Vsegs;R14R12R11R10A5S50Vsegs;R13S25R12S64S22R12A1MeRfSeS15S18GeA1SbS15S1bRfG3S13ReA1S6S1aA1S19A5S6S15A1A3A3S17GeA1A4A2R11R10A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Feb;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp eb nlit Hst Hi H17 H10 Hbel H11 H12 H13 H14 H15 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite H10 in Q0. rewrite H11 in Q1. rewrite H12 in Q2. rewrite H13 in Q3. rewrite H14 in Q4. rewrite H15 in Q5. cbn [eval] in Q1, Q2, Q3, Q4, Q5.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hpos & Hceil & Hfree & Hcont & Hov & Hroom & Hdisj & Hnro & Hxs & HJo).
  set (a := eval rho eb) in *.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite Q1. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  destruct (mmap_flags_50_shape (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) ltac:(rewrite Q2; apply u64_lit; lia) ltac:(rewrite Q3; apply u64_lit; lia) ltac:(rewrite Q5; apply u64_lit; lia))
    as (Hshape & Hnfn & Hnnone & Hnrw & Hnr).
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { rewrite Q1. unfold mmap_nZ. rewrite u64_lit by lia. unfold page_round_up_Z. change page_size with 4096.
    rewrite (Z.div_mod nlit 4096) at 1 by lia. rewrite Hmod, Z.add_0_r.
    replace (4096 * (nlit / 4096) + 4096 - 1) with (4095 + (nlit / 4096) * 4096) by lia. rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (En : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  assert (Hceil' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite Q0, HnZ; exact Hceil).
  assert (Halign' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite Q0; exact Hal).
  assert (Hpos' : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite Q0; exact Hpos).
  assert (Hfree' : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true) by (rewrite Q0, En; exact Hfree).
  assert (Hcont' : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true) by (rewrite Q0, En; exact Hcont).
  assert (HB : mmap_fixed_rw_budget_ok (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { apply mmap_fixed_rw_budget_ok_commit_intro; [exact Hnr | exact (MI_ivs_wf segs _ _ HMI) |].
    rewrite Q0, En, Un. unfold headroom, paid in Hroom. pose proof page_size_pos. fold a. nia. }
  exists (tr, mkCfg (after_sys_mem ms (ms_gpr ms 0) (zero_range (ms_mem ms) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))
                    (mmap_fixed_rw_ok_model (ms_gpr ms 3) md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))).
  split; [exact (wstep_fixed_rw_commit_intro_okA segs ms md _ Hh H222 Hlen Hshape Hnfn Hnnone Hnrw Hceil' Halign' Hpos' Hfree' Hcont' tr Hp HB)|].
  unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr, Q0, En, Un.
  split.
  - replace (SLit nlit) with (SLit (bv_unsigned (Z_to_bv 64 nlit))) by (rewrite Un; reflexivity).
    replace (bv_unsigned a + nlit) with (bv_unsigned a + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
    apply (smatchA_after_commit_obj segs rho rho tp A tr ms md tr (mmap_fixed_rw_next (m_vmmaps md) a (Z_to_bv 64 nlit)) a (Z_to_bv 64 nlit) a eb eb (ss_next (ax_S A)) Hsp);
      try reflexivity; try assumption; rewrite ?Un; try assumption.
    all: try (change page_size with 4096; exact Hmod).
    all: try (apply agree_below_refl). all: try (apply Pos.le_refl).
    all: pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; try lia.
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.
End M.
