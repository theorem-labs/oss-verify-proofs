(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "ms_svc_pending"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "ss_next"; "reg_sv"; "ss_objs"; "valuation"; "SLit"; "obj_range"; "ranges_disjoint"; "SVar"; "ro_addr"; "ss_pc"; "agree_below"; "rm"; "sv_below"; "@Corelib.Init.Datatypes"; "pair"; "list"; "bool"; "option"; "true"; "Some"; "prod"; "nil"; "false"; "cons"; "None"; "app"; "fst"; "snd"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "pow"; "modulo"; "ge"; "div"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "shadow_addr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "advance_past_svc"; "apply_effect"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "m_halted"; "ENOMEM"; "errno_ret"; "vm_maps"; "page_size"; "with_vmmaps"; "SyscallEffect"; "region_free"; "vm_limit"; "vm_noaccess"; "VmMaps"; "page_base"; "MemCopy"; "alloc_top"; "lazy_interior"; "materialize_model_accesses"; "mkEffectU"; "page_in_ranges"; "syscall_effect_accesses"; "vm_add_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "etriple"; "triple1"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "after_sys"; "unmap_range"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "only_okA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "mmap_obj"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_model"; "mmap_none_model"; "mmap_rw_vm"; "mmap_place_ok_none"; "is_ret"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "with_mmap_backing"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "hid"; "vms"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "syscall_spec_ns"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.

Local Notation wstep := (wstep segs).

Lemma wstep_pending_runA : ltac2:(tb__ "0|4|
S1fS42A1M0SaS43S7Q40A1M1S4bS43S43G0S0S21G1A1M2ScR7A1S23G1R5A2A3S0G2S45R7A1S28G1A1M3A3S89S3fVsegs;R9R7A3R8S86S4bR6R5R3A4A3S0G2S45R6A1G3A3S0S21S43A1S54R7S57R8A1A2S23S43R6A2A3S5aVsegs;S1eG0S3dRdS3eRcRbA2A4S1eG0S3dS29S42RdR6A3S3eS40S41RcR9A2A1R7A2A4A3F_;F_;F_;F_;F_;Fevs;Fm'';Fm';Feff;Fx8;Fm;Fms;Ftr;").
Proof using .
  intros tr ms m x8 eff m' m'' evs Hp Hh [Hs Hns] Hh' Hm. exists evs. split; [|reflexivity]. cbn.
  eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hs | exact (Hns _ _ _ eq_refl ltac:(congruence)) | exact Hh' | exact Hm].
Qed.

Lemma wstep_ret_introA : ltac2:(tb__ "0|5|
S1fS42A1M0SaS43S7Q40A1M1G1S43S0S21G1A1M2ScR5A1S23G1R3A2A3S0G2S45R5A1S28G1A1M3A3S89S3fVsegs;R7R5A3R6S86S4bS55R4S25S24G1S1fS7Q8A1A1A2A1S25S24G1G1A2A1M4G4S25S51A1S25S24G1S2cA2A1A6R3S25S42A1A4A3S0G2S45R4A1G3A3S5aVsegs;S1eG0S3dRaS3eR9R8A2A4S1eG0S3dRaS3eS5fR9R6A2R5A2A4A3F_;F_;F_;F_;Fm1;Fr;Fx8;Fm;Fms;Ftr;").
Proof using .
  intros tr ms m x8 r m1 Hp Hh Hs Hh1.
  pose proof (wstep_pending_runA tr ms m x8 _ m1 m1 [] Hp Hh Hs Hh1 (materialize_nil m1)) as W.
  rewrite app_nil_r, advance_apply_ret in W. exact W.
Qed.

Lemma wstep_ret_invA : ltac2:(tb__ "0|4|
S1fS42A1M0SaS43S7Q40A1M1S59G1S43S0S21G1A1M2ScR6A1S23G1R4A2A3S0G2S45R6A1S28G1A1M3A3S87S4bA1S84S3fVsegs;R9R7A3R8R1A3S77R2R6R5S25S42A1A4F_;FR;S0G2S45R4A1G3A3S5aVsegs;S1eG0S3dRbS3eRaR9A2A4R7A3S0S59R8S1eG0S3dRcS3eS5fRbR7A2R6A2A4A3F_;F_;F_;F_;F_;Fm1;Fr;Fw';Fx8;Fm;Fms;Ftr;").
Proof using .
  intros tr ms m x8 w' r m1 Hp Hh Hinv Hh1 Hw.
  destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
  apply Hinv in Hspec. unfold is_ret in Hspec. inversion Hspec; subst.
  destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hc & _)]; [|congruence].
  cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
  injection Hm as <-. rewrite app_nil_r, advance_apply_ret. reflexivity.
Qed.

Section MmapRWA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : ms_gpr ms 1 <> Z_to_bv 64 0.
  Hypothesis Hsh : ltac2:(tb__ "0|0|
S0S20S78S9Vms;U2A2S9Vms;U3A2S9Vms;U5A2A3S22A3").

  Lemma mmap_rw_model_halted : ltac2:(tb__ "0|1|
S7Q40A1M0G0G0S0S21G0A1S45S73R3Vm;R2R1A4A1S45Vm;A1A3Fa;Flen;Fflags;").
  Proof using .
    intros. unfold mmap_rw_model, with_mmap_backing, vm_add_lazy.
    destruct (mmap_noreserve_b flags); [rewrite m_halted_with_vm_backing|]; reflexivity.
  Qed.

  Lemma mmap_only_okA : ltac2:(tb__ "0|0|
S69S3fVsegs;Vms;Vx8;A3Vm;A2").
  Proof using Hh Hno Hlen Hsh.
    eapply only_okA_of_inv; [intros R; exact (@mmap_rw_inv (sys_input segs ms x8) m Hno Hlen Hsh R)| |].
    - intros [E | (a & _ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (a & _ & E)] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_mmap_invA : ltac2:(tb__ "0|4|
S1fS42A1M0S59S0S21S7Q40A1M1A1ScVms;A1S23G1Vx8;A2A3S5aVsegs;S1eG0S3dR3S3eVms;Vm;A2A4R2A3S4S0S59R3S1eG0S3dR4S3eS5fVms;S47S46A1A2Vm;A2A4A3S3G1G1S1S72S9Vms;U0A2S9Vms;U3A2M2Vm;S9Vms;U1A2M3R1A5S0S59R4S1eG0S3dR5S3eS5eVms;R1S61SbVms;A1R1S70G3A1A3A3S73G2Vm;G3R1A4A2A4A3A2La;A2A2F_;F_;Fw';Ftr;").
  Proof using Hh Hno Hlen Hsh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mmap_rw_inv (sys_input segs ms x8) m Hno Hlen Hsh) in Hspec.
    destruct Hspec as [E | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right. exists a. split; [exact Hpl|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
        change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1). rewrite mmap_rw_model_halted. congruence.
  Qed.

  Lemma wstep_mmap_intro_failA : ltac2:(tb__ "0|2|
S1fS42A1M0S0S21S7Q40A1M1A1ScVms;A1S23G1Vx8;A2A3S0S20S7aS9Vms;U3A2Vm;S71S9Vms;U1A2A1A3S22A3S5aVsegs;S1eG0S3dR3S3eVms;Vm;A2A4S1eG0S3dR3S3eS5fVms;S47S46A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using Hh Hno Hlen Hsh.
    intros tr Hp Hrf. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mmap_rw_intro_fail (sys_input segs ms x8) m Hno Hlen Hsh Hrf).
  Qed.

  Lemma wstep_mmap_intro_okA : ltac2:(tb__ "0|4|
S1fS42A1M0S7Q40A1M1S0S21G1A1ScVms;A1S23G1Vx8;A2A3S72S9Vms;U0A2S9Vms;U3A2M2Vm;S9Vms;U1A2M3R2A5S5aVsegs;S1eG0S3dR4S3eVms;Vm;A2A4S1eG0S3dR4S3eS5eVms;R3S61SbVms;A1R3S70G3A1A3A3S73G2Vm;G3R3A4A2A4A3F_;F_;Fa;Ftr;").
  Proof using Hh Hno Hlen Hsh.
    intros tr a Hp Hpl.
    pose proof (@mmap_rw_intro_ok (sys_input segs ms x8) m Hno Hlen Hsh a Hpl) as Hs.
    pose proof (wstep_pending_runA tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mmap_rw_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End MmapRWA.

Lemma pending_argsA : ltac2:(tb__ "0|3|
S14S1fS7Q40A1M0A1S38S1fS42A1M1SaS43S67Vsegs;R6R5R4S1eG1S3dR3S3eR2R1A2A4A5S1S0G0S9R3U0A2SfR7S12S37R5A1M2ZaA2A2A3S1S0G0S9R3U1A2SfR7S12G2ZbA2A2A3S1S0G0S9R3U2A2SfR7S12G2ZcA2A2A3S1S0G0S9R3U3A2SfR7S12G2ZdA2A2A3S1S0G0S9R3U4A2SfR7S12G2ZeA2A2A3S0G0S9R3U5A2SfR7S12G2ZfA2A2A3A2A2A2A2A2F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md H.
  repeat split; (eapply (smatch_pendingA_gpr segs rho tp A tr ms md); [exact H | lia]).
Qed.

Lemma mmap_nw : ltac2:(tb__ "0|3|
S4fS7Q40M0A1M1G1S31S30S6G0R2A2S71R1A1A2S52R3A1A2S1S0S2dS6G0S70R2A1A2S71R2A1M2A3S31S30S6G0R3A2G2A2S32Z2Z40A2A2A2F_;Flen;Fa;Fh;").
Proof using .
  intros h a len Hc. pose proof (alloc_top_lt h) as Hlt. pose proof (mmap_nZ_nonneg len). pose proof (urange a).
  unfold two_pow_64 in Hlt. split; [|lia].
  unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma region_free_app_r : ltac2:(tb__ "0|3|
S1fS24S7Q40A1M0G0A2M1A1M2G2G0G0S0S20S4cS29G1R4R3A3R2R1A3S22A3S0S20S4cR4R3R2A3S22A3F_;Fn;Fa;Fl2;Fl1;").
Proof using .
  induction l1 as [|[b s] l IH]; intros l2 a n H; [exact H|]. cbn [region_free app] in H.
  apply andb_true_iff in H as [_ H]. apply IH. exact H.
Qed.

Lemma smatchA_after_mmap_obj : ltac2:(tb__ "0|f|
S14S1fS7Q40M0A1M1A1S38S1fS42A1M2SaS43G2G1S2dS67Vsegs;R9R8R7S1eG2S3dR6S3eR5R4A2A4A5S0S20S79S9R6U3M3A2A1S26A3S0S2dS71S9R7U1M4A2A1R3A3S1S2fZ0R4A2S2fR4S32Z2Z3eA2A2A2S34S7fR8RcA2R5A2S72S9RaU0A2S9RaG3A2R9S9RaG4A2R7A5S10S5dS10R1S13S37ReA1A1A3S17S16R11R2A2S1eS2dS2dS6G0RaA2M5S30G5R9A2M6A4A2F_;Fo;G1S1S31G5S6G0R1A2M7A2S2fG7G6A2A2S0S20S19Vsegs;R2A2S26A3F_;Fx;S24SeSeA2M8S2dS5dG8R2S39R11A1A3S1S31S6G0SfR14S2aSeSeR3A3A2A2M9R2A2S2fR2S30G9S6G0SfR14S2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0ReA2MaS6G0S3cS6G0SfR15S3aR13A1A2A2R3A2A2MbA2S2fGbS30GaRdA2A2A2A1F_;F_;Fy;Fr;S64Vsegs;S6bR12S11S37R10A1McA1MdRbA3R11S3bR10S6cGcS18GdA1S29S10S13GcA1S27S10S6dGdRaA2S25S10A1A3A3S82GdA1A4A2S1eG2S3dRcS3eS5eReRbS61SbReA1RbS70S9ReG4A2MeA1A3A3S73S9ReG3A2RdGeRbA4A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Fa;Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' a nlit Hsp Hnr HnZ Hn Hroom Hpl Hdisj Hnro Hxs.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof Hpl as (Hal & Hpos & Hceil & Hfree & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
  rewrite HnZ in En, Hnw.
  unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr).
  set (md' := with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md).

  assert (Hvis : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nlit -> hid md tp x = false).
  { intros x Hx. eapply (hid_false_of_region_free md tp a (mmap_n (ms_gpr ms 1)) x (MI_lazy_in_maps segs md tp HMI) (MI_ivs_wf segs md tp HMI)).
    - eapply region_free_app_r. exact Hfree.
    - rewrite En. exact Hx. }
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz).
  split; [|split; [|split; [|split]]].
  *
    unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    assert (Ev : vms md' tp (after_sys_mem ms a (zero_range (ms_mem ms) a (mmap_n (ms_gpr ms 1))))
                 = after_sys_mem (vms md tp ms) a (zero_range (ms_mem (vms md tp ms)) a (mmap_n (ms_gpr ms 1)))).
    { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
      f_equal. apply functional_extensionality. intros x.
      unfold mrestrict. rewrite (hid_ext md md' tp) by reflexivity. rewrite !zero_range_at.
      destruct (in_range a (mmap_n (ms_gpr ms 1)) x) eqn:Ein; [|reflexivity].
      apply in_range_spec in Ein. rewrite En in Ein. rewrite (Hvis x Ein). reflexivity. }
    rewrite Ev. rewrite virt_unfold in Hspv.
    eapply (smatch_after_mmap segs rho (ax_S A) tr (vms md tp ms) (vmd md));
      [exact Hspv | apply (proj2 (model_idle_vmd md')); exact Hh | exact En | lia | exact Hnw | exact Hdisj | exact Hnro].
  *
    unfold md'. eapply (MI_with_vmmaps segs md _ tp nlit HMI); try reflexivity.
    -- cbn. apply ivs_wf_cons; [apply iv_wf_intro; rewrite En; exact Hnw | exact (proj1 (MI_ivs_wf segs md tp HMI))].
    -- cbn. exact (proj1 (proj2 (MI_ivs_wf segs md tp HMI))).
    -- cbn. intros r Hr. right. exact Hr.
    -- rewrite <- En. apply (used_maps_cons_le md _ a (mmap_n (ms_gpr ms 1))); [exact (MI_ivs_wf segs md tp HMI) | apply iv_wf_intro; rewrite En; exact Hnw | reflexivity | reflexivity].
    -- exact Hroom.
  *   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    -- apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) HX r Hr) as Y.
       unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
       apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    -- eapply sv_below_mono; [|exact Hb]. lia.
  *
    assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) a)) by (apply agree_below_set_rw; lia).
    pose proof (shadow_ok_stable A A rho (rho_set_rw rho (ss_next (ax_S A)) a) Hag Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh) as Hsh'.
    apply shadow_ok_transport_objs; [|exact Hsh']. cbn [ax_X ax_base ax_S ax_setS S_after ss_objs].
    intros x Hxw Hout _. apply outside_all_app. split; [exact Hout|]. constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, mmap_obj. cbn [ob_base ob_lo ob_hi eval]. rewrite rho_set_rw_at.
    rewrite !soff_lit_small by lia. rewrite Z.add_0_r.
    assert (Hnl8 : nlit mod 8 = 0).
    { rewrite <- HnZ. unfold mmap_nZ, page_round_up_Z. apply mod8_of_page. apply Z_mod_mult. }
    refine (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) _ Hxs (xword_agree rho _ A x Hag Hwf Hxw)).
    rewrite Z.add_mod, (mod8_of_page _ Hal), Hnl8 by lia. reflexivity.
  *
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite (hid_ext md md' tp) in Hx by reflexivity. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a (mmap_n (ms_gpr ms 1)) x); [left; reflexivity|]. exact (Hhz x Hx).
Qed.

Lemma mmap_len_lit : ltac2:(tb__ "0|5|
S14S1fS7Q40M0A1M1A1S38S1fS42A1M2SaS43S2dS67Vsegs;R7R6R5S1eG2S3dR4S3eR3R2A2A4A5S0SeS12S37R6A1ZbA2S15R2A1A3S0S2dS33R3Z1000A2Z0M3A3S1S2fG3R4A2S2fR4S32Z2Z3eA2A2A2S1S2S0G1S9R7U1A2M4S8G0G3A2A3A1S0S2dS71G4A1R5A3A2F_;F_;F_;F_;Fnlit;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md nlit Hsp H11 Hmod Hn.
  destruct (pending_argsA rho tp A tr ms md Hsp) as (_ & G1 & _). rewrite H11 in G1. cbn [eval] in G1.
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit).
  { rewrite G1, Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  split.
  - intros E. rewrite E in Hlenv. rewrite Z_to_bv_unsigned in Hlenv. change (bv_wrap 64 0) with 0 in Hlenv. lia.
  - unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia.
Qed.

Theorem triple1_mmap_rw_objA : ltac2:(tb__ "0|10|
S59OF_;S63S63S7Q40M0A1M1S63F_;S38S14S1fG1A1S2dS66Vsegs;R8R7A3S6aVsegs;R9R8A3S65Vsegs;S11S37R6A1A1R9A3S0S21S6eA1S85Vsegs;S1aS37R7A1A1A2S23S6eS6fA2A3S0SeS12S37R8A1Z11A2S15ZdeA1A3S0SeS12S37R9A1ZbA2S15R6A1A3S0S2dS33R7Z1000A2Z0M2A3S1S2fG2R8A2S2fR8S32Z2Z3eA2A2A2S1fS42A1M3SaS43S67Vsegs;ReRdRfS1eG3S3dR3S3eR2R1A2A4A5R13RfReR4R2A4S1S0S20S78S9R4U2A2S9R4U3M4A2M5S9R4U5A2A3S22A3S1S0S20S79G5A1S26A3S1S34S7fR3RfA2ReA2S1R13R10RfR5R3A4G1S72S9R5U0A2S9R5G4A2R4S9R5U1M6A2R1A5S1S10S5dS10R1S13S37R14A1A1A3S17S16R14R2A2S1eS2dS2dS6G0R4A2M7S30G7R12A2A4A2F_;Fo;S1G1S1S31S6G0R3A2M8S6G0R1A2M9A2S2fG9S30G8R11A2A2A2S0S20S19Vsegs;R2A2S26A3F_;Fx;S1S24SeSeA2MaS2dS5dGaR2S39R15A1A3S1S31S6G0SfR15S2aSeSeR3A3A2A2MbR2A2S2fR2S30GbS6G0SfR15S2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0R6A2McS6G0S3cS6G0SfR16S3aR17A1A2A2R3A2A2MdA2S2fGdS30GcR14A2A2A2A1F_;F_;Fy;Fr;R14R2S6bR12S11S37R13A1A1R2A3R11R7S4aS75S44R5A1S9R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S5cVsegs;R11S62Vsegs;R10RdRcRbA5S59S4S62Vsegs;R10S68ReS15S6G0S47S46A1A2A1A2RdRcR1A6S3G1G1S62Vsegs;R10R1A1S3bRfS6cS37RfA1MeS18S11GeA1MfA1S29S10S13GeA1S27S10S6dGfRcA2S25S10A1A3A3S82GfA1A4A2S6bReGfR1A3RdR2A6La;A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo A rho tp nlit Hokf Hokp Hst Hi H17 H11 Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (mmap_only_okA ms md _ Hh H222 Hlen Hmodb).
  - intros w' Hw. destruct (wstep_mmap_invA ms md _ Hh H222 Hlen Hmodb tr w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
      * eapply smatchA_after_mmap_obj; eauto.
      * cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Theorem etriple_mmap_rw_objA : ltac2:(tb__ "0|10|
S63S7Q40M0A1M1S63F_;S38S14S1fG1A1S2dS65Vsegs;S11S37R4A1A1R6A3S0S21S6eA1S85Vsegs;S1aS37R5A1A1A2S23S6eS6fA2A3S0SeS12S37R6A1Z11A2S15ZdeA1A3S0SeS12S37R7A1ZbA2S15R4A1A3S0S2dS33R5Z1000A2Z0M2A3S1S2fG2R6A2S2fR6S32Z2Z3eA2A2A2S1fS42A1M3SaS43S67Vsegs;RcRbRdS1eG3S3dR3S3eR2R1A2A4A5R10RdRcR4R2A4S1S0S20S78S9R4U2A2S9R4U3M4A2M5S9R4U5A2A3S22A3S1S0S20S79G5A1S26A3S1S34S7fR3RdA2RcA2S3G1G1S1S72S9R5U0A2S9R5G4A2R4S9R5U1A2M6R1A5S1S10S5dS10R1S13S37R11A1A1A3S17S16R11R2A2S1eS2dS2dS6G0R3A2M7S30G7RfA2A4A2F_;Fo;S1G1S1S31S6G0R2A2M8S6G0R1A2M9A2S2fG9S30G8ReA2A2A2S0S20S19Vsegs;R2A2S26A3F_;Fx;S1S24SeSeA2MaS2dS5dGaR2S39R12A1A3S1S31S6G0SfR12S2aSeSeR3A3A2A2MbR2A2S2fR2S30GbS6G0SfR12S2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0R5A2McS6G0S3cS6G0SfR13S3aR14A1A2A2R3A2A2MdA2S2fGdS30GcR11A2A2A2A1F_;F_;Fy;Fr;R11R1S6bRfS11S37R10A1A1R1A3ReR6S4aS75S44R4A1G6R1A3R4A2A5A2A2A2A2La;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S5bVsegs;S62Vsegs;RdRbRaR9A5S59S3G1G1S62Vsegs;ReR1A1S3bRdS6cS37RdA1MeS18S11GeA1MfA1S29S10S13GeA1S27S10S6dGfRaA2S25S10A1A3A3S82GfA1A4A2S6bRcGfR1A3RbR2A6La;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp nlit Hst Hi H17 H11 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & a & Hpl & Hdisj & Hnro & Hxs & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  eexists. split; [exact (wstep_mmap_intro_okA ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
  exists a. split.
  - eapply smatchA_after_mmap_obj; eauto.
  - cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Theorem etriple_mmap_rw_obj_anyA : ltac2:(tb__ "0|10|
S63S63S7Q40M0A1M1S63F_;S38S14S1fG1A1S2dS65Vsegs;S11S37R4A1A1R7A3S0S21S6eA1S85Vsegs;S1aS37R5A1A1A2S23S6eS6fA2A3S0SeS12S37R6A1Z11A2S15ZdeA1A3S0SeS12S37R7A1ZbA2S15R4A1A3S0S2dS33R5Z1000A2Z0M2A3S1S2fG2R6A2S2fR6S32Z2Z3eA2A2A2S1fS42A1M3SaS43S67Vsegs;RcRbRdS1eG3S3dR3S3eR2R1A2A4A5R11RdRcR4R2A4S1S0S20S78S9R4U2A2S9R4U3M4A2M5S9R4U5A2A3S22A3S1S0S20S79G5A1S26A3S1S34S7fR3RdA2RcA2S1R11ReRdR5R3A4G1S72S9R5U0A2S9R5G4A2R4S9R5U1M6A2R1A5S1S10S5dS10R1S13S37R12A1A1A3S17S16R12R2A2S1eS2dS2dS6G0R4A2M7S30G7R10A2A4A2F_;Fo;S1G1S1S31S6G0R3A2M8S6G0R1A2M9A2S2fG9S30G8RfA2A2A2S0S20S19Vsegs;R2A2S26A3F_;Fx;S1S24SeSeA2MaS2dS5dGaR2S39R13A1A3S1S31S6G0SfR13S2aSeSeR3A3A2A2MbR2A2S2fR2S30GbS6G0SfR13S2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0R6A2McS6G0S3cS6G0SfR14S3aR15A1A2A2R3A2A2MdA2S2fGdS30GcR12A2A2A2A1F_;F_;Fy;Fr;R12R2S6bR10S11S37R11A1A1R2A3RfR7S4aS75S44R5A1S9R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S5bVsegs;S62Vsegs;ReRbRaR9A5S59S4S62Vsegs;ReS68RcS15S6G0S47S46A1A2A1A2RbRaR1A6S3G1G1S62Vsegs;ReR1A1S3bRdS6cS37RdA1MeS18S11GeA1MfA1S29S10S13GeA1S27S10S6dGfRaA2S25S10A1A3A3S82GfA1A4A2S6bRcGfR1A3RbR2A6La;A2A2Lw;A3F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJf;FJ;").
Proof using .
  intros J Jf Jo A rho tp nlit Hst Hi H17 H11 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [exact (wstep_mmap_intro_failA ms md _ Hh H222 Hlen Hmodb tr Hp Hrf)|].
    left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
  - destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
    eexists. split; [exact (wstep_mmap_intro_okA ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
    right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Section MmapNoneA.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : ms_gpr ms 1 <> Z_to_bv 64 0.
  Hypothesis Hsh : ltac2:(tb__ "0|0|
S0S20S7bS9Vms;U2A2S9Vms;U3A2S9Vms;U5A2A3S22A3").
  Hypothesis Hnrw : ltac2:(tb__ "0|0|
S0S20S78S9Vms;U2A2S9Vms;U3A2S9Vms;U5A2A3S26A3").

  Lemma mmap_none_model_halted : ltac2:(tb__ "0|1|
S7Q40A1M0G0G0S0S21G0A1S45S74R3Vm;R2R1A4A1S45Vm;A1A3Fa;Flen;Fflags;").
  Proof using .
    intros. unfold mmap_none_model, with_mmap_backing, vm_add_lazy.
    destruct (mmap_noreserve_b flags); [rewrite m_halted_with_vm_backing|]; reflexivity.
  Qed.

  Lemma mmap_none_only_okA : ltac2:(tb__ "0|0|
S69S3fVsegs;Vms;Vx8;A3Vm;A2").
  Proof using Hh Hno Hlen Hsh Hnrw.
    eapply only_okA_of_inv; [intros R; exact (@mmap_none_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnrw R)| |].
    - intros [E | (a & _ & E)]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | (a & _ & E)] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_mmap_none_invA : ltac2:(tb__ "0|3|
S1fS42A1M0S59S0S21S7Q40A1M1A1ScVms;A1S23G1Vx8;A2A3S5aVsegs;S1eG0S3dR3S3eVms;Vm;A2A4R2A3S4S0S59R3S1eG0S3dR4S3eS5fVms;S47S46A1A2Vm;A2A4A3S3G1G1S1S76S9Vms;U0A2Vm;S9Vms;U1A2M2R1A4S0S59R4S1eG0S3dR5S3eS5eVms;R1S60SbVms;A1R1S70G2A1A3A3S74S9Vms;U3A2Vm;G2R1A4A2A4A3A2La;A2A2F_;F_;Fw';Ftr;").
  Proof using Hh Hno Hlen Hsh Hnrw.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@mmap_none_inv (sys_input segs ms x8) m Hno Hlen Hsh Hnrw) in Hspec.
    destruct Hspec as [E | (a & Hpl & E)]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right. exists a. split; [exact Hpl|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
        change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1). rewrite mmap_none_model_halted. congruence.
  Qed.

  Lemma wstep_mmap_none_intro_failA : ltac2:(tb__ "0|2|
S1fS42A1M0S0S21S7Q40A1M1A1ScVms;A1S23G1Vx8;A2A3S0S20S7cVm;S71S9Vms;U1A2A1A2S22A3S5aVsegs;S1eG0S3dR3S3eVms;Vm;A2A4S1eG0S3dR3S3eS5fVms;S47S46A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using Hh Hno Hlen Hsh Hnrw.
    intros tr Hp Hrf. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mmap_none_intro_fail (sys_input segs ms x8) m Hno Hlen Hsh Hnrw Hrf).
  Qed.

  Lemma wstep_mmap_none_intro_okA : ltac2:(tb__ "0|3|
S1fS42A1M0S7Q40A1M1S0S21G1A1ScVms;A1S23G1Vx8;A2A3S76S9Vms;U0A2Vm;S9Vms;U1A2M2R2A4S5aVsegs;S1eG0S3dR4S3eVms;Vm;A2A4S1eG0S3dR4S3eS5eVms;R3S60SbVms;A1R3S70G2A1A3A3S74S9Vms;U3A2Vm;G2R3A4A2A4A3F_;F_;Fa;Ftr;").
  Proof using Hh Hno Hlen Hsh Hnrw.
    intros tr a Hp Hpl.
    pose proof (@mmap_none_intro_ok (sys_input segs ms x8) m Hno Hlen Hsh Hnrw a Hpl) as Hs.
    pose proof (wstep_pending_runA tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mmap_none_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.
End MmapNoneA.

Lemma vms_after_range_none : ltac2:(tb__ "0|9|
S43S43S1fS7Q40M0A1M1A1SaG1G1G1G1S21S7Q8A1M2A1M3Fx;G1S1S31S6G0R5A2M4S6G0R1A2M5A2S2fG5S30G4S6G0R4A2A2A2A2S4S0S20S80R9R8R2A3S22A3S0G3R3R2A1S28G2A1A3A2F_;Fx;G1S2S1S31S6G0R6A2M6G5A2S2fG5S30G6G4A2M7A2A2A1S1S0S20S80RaR9R2A3S80RbR9R2A3A3S0G3R4R2A1SbR8R2A2A3A2F_;Fx;S31G7S32Z2Z40A2A2S0SaS81RaR9S5eR8R5R4A3A3S5eS81RbR9R8A3M8R5S60SbG8A1R7R6A3A3A3F_;F_;F_;Fmem';Fr;Fn;Fa;Fms;Ftp;Fmd';Fmd;").
Proof using .
  intros md md' tp ms a n r mem' Hin Hout Hnw.
  unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  f_equal. apply functional_extensionality. intros x. unfold mrestrict. rewrite unmap_range_at.
  destruct (in_range a n x) eqn:Ein.
  - apply in_range_spec in Ein. destruct (Hin x Ein) as [-> | E]; [reflexivity|]. rewrite E. destruct (hid md' tp x); reflexivity.
  - assert (Hn : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)).
    { intros H. apply (proj2 (in_range_spec a n x)) in H. congruence. }
    destruct (Hout x Hn) as [-> ->]. reflexivity.
Qed.

Lemma page_base_val : ltac2:(tb__ "0|1|
S7Q40M0A1S0S2dS6G0S50R1A1A2S36S35S6G0R1A2S49A2S49A2A3Fx;").
Proof using .
  intros x. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned. pose proof (urange x). pose proof page_size_pos.
  pose proof (Z.div_mod (bv_unsigned x) page_size ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) page_size ltac:(lia)).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
  split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia] | lia].
Qed.

Lemma in_interior_pages : ltac2:(tb__ "0|7|
S7Q40M0A1M1G1G1S0S2dS33S6G0R3A2S49A2Z0M2A3M3G3S2fG2S6G0R4A2A2S31S30S6G0R6A2M4S6G0R5A2M5A2S32Z2Z40A2A2S5S1S31S6G0R7A2M6G5A2S2fG5S30G6G4A2A2A2S0S20S56S50R5A1S53R7R6A2A2S22A3A2F_;F_;F_;F_;Fx;Fn;Fa;").
Proof using .
  intros a n x Hal Hnl Hpos Hend. rewrite (lazy_interior_aligned a n Hal Hnl Hpos Hend).
  rewrite page_in_ranges_eq. cbn [existsb]. rewrite orb_false_r. unfold page_in_range. cbn [fst snd].
  rewrite andb_true_iff, !Z.leb_le, page_base_val.
  pose proof page_size_pos as Pps. pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof (urange x) as Rx.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(lia)) as Da. rewrite Hal in Da.
  pose proof (Z.div_mod (bv_unsigned n) page_size ltac:(lia)) as Dn. rewrite Hnl in Dn.
  pose proof (Z.div_mod (bv_unsigned x) page_size ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (bv_unsigned x) page_size ltac:(lia)) as Mx.
  set (qa := bv_unsigned a / page_size) in *. set (qn := bv_unsigned n / page_size) in *. set (qx := bv_unsigned x / page_size) in *.
  split.
  - intros [H1 H2].
    assert (qa <= qx) by (unfold qx; apply Z.div_le_lower_bound; lia).
    assert (qx < qa + qn) by (unfold qx; apply Z.div_lt_upper_bound; lia).
    nia.
  - intros [H1 H2]. nia.
Qed.

Lemma smatchA_after_grant_lazy : ltac2:(tb__ "0|e|
S14S14S1fS7Q40M0A1M1A1S38S1fS42A1M2SaS43G2S4fG1G1G1SeS2eS67Vsegs;ReRcRbS1eG2S3dRaS3eR9R8A2A4A5S0S1fS24G1G1A2M3A1M4S48R7A1S27G3S1eG1G1R6R5A4S48S44R9A1A1A3A3S0G4S4eR8A1S4eS44RaA1A1A3S0S2dS4dR9A1S4dS44RbA1A1A3S0S2dS33S6G0R9A2S49A2Z0M5A3M6G6S2fG5S6G0RaA2A2S31S30S6G0RcA2S6G0RbA2A2S32Z2Z40A2A2S0S20S4cS48S44R10A1A1RdRcA3S22A3S2dS1S31S6G0RfA2M7R1A2S2fR1S30G7S6G0ReA2A2A2A2S0S21S7eA1SdVsegs;R2Z1A3S28S7eA1A3F_;Fz;S10S5dS10R1S13S37R16A1A1A3S17S16R1aR2A2S1eS2dS2dS6G0R11A2M8S30G8S6G0R10A2A2A4A2F_;Fo;S24SeSeA2M9S2dS5dG9R2S39R18A1A3S1S31S6G0SfR1cS2aSeSeR3A3A2A2MaR2A2S2fR2S30GaS6G0SfR1cS2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0R14A2MbS6G0S3cS6G0SfR1dS3aR1aA1A2A2R3A2A2McA2S2fGcS30GbS6G0R13A2A2A2A2A1F_;F_;Fy;Frr;S1bS11S37R17A1A1S88R1aS60S1cR1aA1R11R10A3A2R19A3S83S11S37R18A1A1ReA2S0S20S1dRfR10A2S22A3S0G1SfR1cR11A2R12A3S64Vsegs;R1dR1cS3bR1bS6cS37R1bA1MdR12S13GdA1R11A4A2S1eG2S3dR17S3eS5eR19R13S61SbR19A1R15R14A3A3S58R15R14S4aR16R18A2A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e nx Hsp Hmaps Hna Hlim Hal Hnl Hpos Hend Hfree Hseg Hdisj Hxs Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  set (md1 := with_vmmaps h' md). set (md' := vm_add_lazy a n md1).
  assert (Hclr : tp_clear_of tp (lazy_interior a n)).
  { eapply (tp_clear_of_region_free md); [exact Htm | exact (proj1 Hivs) | exact Hfree | exact Hend]. }
  assert (Hvis : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hid md tp x = false).
  { intros x Hx. eapply hid_false_of_region_free; eauto. }

  assert (Hhid' : forall x, hid md' tp x = hid md tp x || page_in_ranges (page_base x) (lazy_interior a n)).
  { intros x. unfold md'. rewrite hid_add_lazy. unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity.
    destruct (page_in_ranges (page_base x) (lazy_interior a n)) eqn:E; [|now rewrite andb_false_l].
    destruct (page_mem (page_base x) tp) eqn:Em; [|reflexivity]. exfalso.
    apply page_mem_In in Em. pose proof (Hclr _ Em). congruence. }
  assert (HIN : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hid md' tp x = true).
  { intros x Hx. rewrite Hhid'. rewrite (proj1 (in_interior_pages a n x Hal Hnl Hpos Hend) Hx). apply orb_true_r. }
  assert (HOUT : forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n) -> hid md' tp x = hid md tp x).
  { intros x Hx. rewrite Hhid'. destruct (page_in_ranges (page_base x) (lazy_interior a n)) eqn:E; [|apply orb_false_r].
    exfalso. apply Hx. apply (proj2 (in_interior_pages a n x Hal Hnl Hpos Hend)). exact E. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    rewrite (vms_after_range_none md md' tp ms a n r (zero_range (ms_mem ms) a n)).
    + pose proof (smatch_pending_reunmap segs rho (ax_S A) tr (vms md tp ms) (vmd md) a n Hspv Hend Hdisj) as Hsp1.
      pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
      rewrite after_sys_mem_with_mem.
      unfold after_sys. eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
      * apply (proj2 (model_idle_vmd md')). unfold md', md1, vm_add_lazy. rewrite m_halted_with_vm_backing. exact Hh.
      * apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx|]. exact (proj1 (forallb_forall _ _) (swf_objs _ (smatch_pendingA_swf segs _ _ _ _ Hsp)) o Ho).
      * apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
      * exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2).
    + intros x Hx. left. exact (HIN x Hx).
    + intros x Hx. split; [exact (HOUT x Hx)|]. rewrite zero_range_at.
      destruct (in_range a n x) eqn:E; [|reflexivity]. exfalso. apply Hx. apply in_range_spec. exact E.
    + exact Hend.
  -
    cbn [cfg_model cfg_ms snd fst]. unfold md', md1. apply (MI_intro segs).
    + exact HW. + exact HT.
    + rewrite m_vm_materialized_vm_add_lazy. exact Hmat.
    + rewrite m_vm_materialized_vm_add_lazy. exact Hsub.
    + rewrite (paid_add_lazy _ a n tp Hclr), paid_with_vmmaps, m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, Hlim.
      pose proof (used_rw_noreserve_le md h' a n Hivs Hal Hnl Hpos Hend Hmaps Hna). lia.
    + rewrite m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps. apply lazy_clear_app; [apply lazy_clear_interior; assumption | exact Hlc].
    + apply model_ivs_wf_vm_add_lazy; [exact Hend|]. apply model_ivs_wf_with_vmmaps; [exact Hivs | |].
      * rewrite Hmaps. apply ivs_wf_cons; [apply iv_wf_intro; exact Hend | exact (proj1 Hivs)].
      * rewrite Hna. exact (proj1 (proj2 Hivs)).
    + apply lazy_in_maps_add_lazy; [apply lazy_in_maps_with_vmmaps_grow; [exact Hlm | rewrite Hmaps; intros rr Hr; right; exact Hr] | exact Hend |].
      exists a, n. rewrite m_vmmaps_with_vmmaps, Hmaps. split; [left; reflexivity | lia].
    + intros p Hp. destruct (Htm p Hp) as (Hpal & b & s0 & Hbs & X). split; [exact Hpal|]. exists b, s0. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, Hmaps.
      split; [right; exact Hbs | exact X].
  -   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  -
    set (rho1 := set_rm rho (unmap_range (rm rho) a n)) in *.
    assert (Hsh1 : shadow_ok rho1 A).
    { eapply (shadow_ok_transport rho rho1 A A); [reflexivity | apply eval_set_rm | intros; unfold rho1; rewrite !eval_set_rm; split; reflexivity | | exact Hsh].
      intros x Hxw Hout Hdef. split; [apply outside_all_set_rm; exact Hout|].
      unfold rho1. cbn [set_rm rm]. rewrite unmap_range_at.
      destruct (in_range a n _) eqn:E; [|reflexivity]. exfalso. apply in_range_spec in E.
      exact (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) (mod8_of_pages _ _ Hal Hnl) Hxs Hxw E). }
    exact (shadow_ok_stable A (ax_setS A (S_after (ax_S A) e (ss_objs (ax_S A)) nx)) rho1 rho' Hag' Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh1).
  -
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a n x) eqn:E; [left; reflexivity|].
    assert (Hn : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)).
    { intros H. apply (proj2 (in_range_spec a n x)) in H. congruence. }
    rewrite (HOUT x Hn) in Hx. unfold md', md1. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps, Hna. exact (Hhz x Hx).
Qed.

Lemma smatchA_after_grant_none : ltac2:(tb__ "0|e|
S14S14S1fS7Q40M0A1M1A1S38S1fS42A1M2SaS43G2S4fG1G1G1G1SeS2eS67Vsegs;RfRdRcS1eG2S3dRbS3eRaR9A2A4A5S0S1fS24G1G1A2M3A1M4S48R8A1S27G3S1eG1G1R6R5A4S48S44RaA1A1A3A3S0G4S4eR9A1S27G3S1eG1G1R7R6A4S4eS44RbA1A1A3A3S0S2dS4dRaA1S4dS44RcA1A1A3S0S2dS33S6G0R9A2S49A2Z0M5A3M6G6S2fG5S6G0RaA2A2S31S30S6G0RcA2S6G0RbA2A2S32Z2Z40A2A2S0S20S4cS48S44R11A1A1RdRcA3S22A3S2dS1S31S6G0RfA2M7R1A2S2fR1S30G7S6G0ReA2A2A2A2S0S21S7eA1SdVsegs;R2Z1A3S28S7eA1A3F_;Fz;S10S5dS10R1S13S37R17A1A1A3S17S16R1bR2A2S1eS2dS2dS6G0R11A2M8S30G8S6G0R10A2A2A4A2F_;Fo;S24SeSeA2M9S2dS5dG9R2S39R19A1A3S1S31S6G0SfR1dS2aSeSeR3A3A2A2MaR2A2S2fR2S30GaS6G0SfR1dS2bSeSeR3A3A2A2A2A2A2S2S1S31S6G0R14A2MbS6G0S3cS6G0SfR1eS3aR1bA1A2A2R3A2A2McA2S2fGcS30GbS6G0R13A2A2A2A2A1F_;F_;Fy;Frr;S1bS11S37R18A1A1S88R1bS60S1cR1bA1R11R10A3A2R1aA3S83S11S37R19A1A1ReA2S0S20S1dRfR10A2S22A3S0G1SfR1dR11A2R12A3S64Vsegs;R1eR1dS3bR1cS6cS37R1cA1MdR12S13GdA1R11A4A2S1eG2S3dR18S3eS5eR1aR13S60SbR1aA1R15R14A3A3S7dR16R15R14S4aR17R19A2A4A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fflags;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' flags a n r e nx Hsp Hmaps Hna Hlim Hal Hnl Hpos Hend Hfree Hseg Hdisj Hxs Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  set (md1 := with_vmmaps h' md). set (md' := with_mmap_backing flags a n md1).
  assert (Hclr : tp_clear_of tp (lazy_interior a n)).
  { eapply (tp_clear_of_region_free md); [exact Htm | exact (proj1 Hivs) | exact Hfree | exact Hend]. }
  assert (Hvis : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hid md tp x = false).
  { intros x Hx. eapply hid_false_of_region_free; eauto. }
  assert (Hwf1 : model_ivs_wf md1).
  { apply model_ivs_wf_with_vmmaps; [exact Hivs | |].
    - rewrite Hmaps. apply ivs_wf_cons; [apply iv_wf_intro; exact Hend | exact (proj1 Hivs)].
    - rewrite Hna. apply ivs_wf_cons; [apply iv_wf_intro; exact Hend | exact (proj1 (proj2 Hivs))]. }

  assert (Hhid' : forall x, hid md' tp x = hid md tp x \/ (hid md' tp x = hid md tp x || page_in_ranges (page_base x) (lazy_interior a n))).
  { intros x. unfold md', with_mmap_backing. destruct (mmap_noreserve_b flags).
    - right. rewrite hid_add_lazy. unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity.
      destruct (page_in_ranges (page_base x) (lazy_interior a n)) eqn:E; [|now rewrite andb_false_l].
      destruct (page_mem (page_base x) tp) eqn:Em; [|reflexivity]. exfalso.
      apply page_mem_In in Em. pose proof (Hclr _ Em). congruence.
    - left. unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity. reflexivity. }
  assert (HOUT : forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n) -> hid md' tp x = hid md tp x).
  { intros x Hx. destruct (Hhid' x) as [E|E]; rewrite E; [reflexivity|].
    destruct (page_in_ranges (page_base x) (lazy_interior a n)) eqn:Ep; [|apply orb_false_r].
    exfalso. apply Hx. apply (proj2 (in_interior_pages a n x Hal Hnl Hpos Hend)). exact Ep. }
  assert (Hh' : m_halted md' = m_halted md).
  { unfold md', md1, with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b flags); [rewrite m_halted_with_vm_backing|]; reflexivity. }
  assert (Hvm' : m_vmmaps md' = h').
  { unfold md', md1, with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b flags); [rewrite m_vmmaps_with_vm_backing|]; reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    rewrite (vms_after_range_none md md' tp ms a n r (unmap_range (ms_mem ms) a n)).
    + pose proof (smatch_pending_reunmap segs rho (ax_S A) tr (vms md tp ms) (vmd md) a n Hspv Hend Hdisj) as Hsp1.
      pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
      rewrite after_sys_mem_with_mem.
      unfold after_sys. eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
      * apply (proj2 (model_idle_vmd md')). rewrite Hh'. exact Hh.
      * apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx|]. exact (proj1 (forallb_forall _ _) (swf_objs _ (smatch_pendingA_swf segs _ _ _ _ Hsp)) o Ho).
      * apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
      * exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2).
    + intros x Hx. right. rewrite unmap_range_at. rewrite (proj2 (in_range_spec a n x) Hx). reflexivity.
    + intros x Hx. split; [exact (HOUT x Hx)|]. rewrite unmap_range_at.
      destruct (in_range a n x) eqn:E; [|reflexivity]. exfalso. apply Hx. apply in_range_spec. exact E.
    + exact Hend.
  -
    cbn [cfg_model cfg_ms snd fst].
    assert (MI1 : MI segs md1 tp).
    { unfold md1. apply (MI_intro segs); model_proj.
      + exact HW. + exact HT. + exact Hmat. + exact Hsub.
      + rewrite paid_with_vmmaps, Hlim. pose proof (used_none_cons_le md h' a n Hivs (iv_wf_intro a n Hend) Hmaps Hna). lia.
      + exact Hlc. + exact Hwf1.
      + apply lazy_in_maps_with_vmmaps_grow; [exact Hlm | rewrite Hmaps; intros rr Hr; right; exact Hr].
      + intros p Hp. destruct (Htm p Hp) as (Hpal & b & s0 & Hbs & X). split; [exact Hpal|]. exists b, s0. rewrite m_vmmaps_with_vmmaps, Hmaps. split; [right; exact Hbs | exact X]. }
    unfold md', with_mmap_backing. destruct (mmap_noreserve_b flags); [|exact MI1].
    apply (MI_add_lazy segs md1 a n tp MI1 Hend Hclr Hseg).
    exists a, n. unfold md1. rewrite m_vmmaps_with_vmmaps, Hmaps. split; [left; reflexivity | lia].
  -   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  -
    set (rho1 := set_rm rho (unmap_range (rm rho) a n)) in *.
    assert (Hsh1 : shadow_ok rho1 A).
    { eapply (shadow_ok_transport rho rho1 A A); [reflexivity | apply eval_set_rm | intros; unfold rho1; rewrite !eval_set_rm; split; reflexivity | | exact Hsh].
      intros x Hxw Hout Hdef. split; [apply outside_all_set_rm; exact Hout|].
      unfold rho1. cbn [set_rm rm]. rewrite unmap_range_at.
      destruct (in_range a n _) eqn:E; [|reflexivity]. exfalso. apply in_range_spec in E.
      exact (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) (mod8_of_pages _ _ Hal Hnl) Hxs Hxw E). }
    exact (shadow_ok_stable A (ax_setS A (S_after (ax_S A) e (ss_objs (ax_S A)) nx)) rho1 rho' Hag' Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh1).
  -
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite after_sys_memq, unmap_range_at. rewrite Hvm', Hna.
    destruct (in_range a n x) eqn:E.
    + right. split; [reflexivity|]. apply in_range_spec in E. cbn [covered existsb]. unfold in_iv, in_rng, ivB, ivS. cbn [fst snd].
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    + assert (Hn : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)).
      { intros H. apply (proj2 (in_range_spec a n x)) in H. congruence. }
      rewrite (HOUT x Hn) in Hx. destruct (Hhz x Hx) as [H0|[H1 H2]]; [left; exact H0 | right].
      split; [exact H1|]. cbn [cfg_model snd] in H2. cbn [covered existsb]. fold (covered (vm_noaccess (m_vmmaps md)) (bv_unsigned x)).
      rewrite H2. apply orb_true_r.
Qed.

End M.
