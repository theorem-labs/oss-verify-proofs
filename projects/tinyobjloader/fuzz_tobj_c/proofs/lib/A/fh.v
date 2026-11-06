(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia Logic.FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA2 MmapBrkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7 e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require CfgGlueA2.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA2.

(* [comment removed for export] *)
Module MuslMalloc40Nodes.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "leb"; "pow"; "sub"; "modulo"; "mul"; "opp"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "rw"; "eval"; "SLit"; "ss_facts"; "sobj"; "ss_regs"; "holds"; "rm"; "ss_next"; "SVar"; "ss_objs"; "obj_range"; "ranges_disjoint"; "rl"; "SPAlign"; "SPUle"; "ob_base"; "ob_lo"; "sprop_below"; "ss_pc"; "sstate"; "sv_eqb"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "nil"; "option"; "Some"; "app"; "cons"; "snd"; "fst"; "false"; "andb"; "orb"; "None"; "nat"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "vm_maps"; "vm_reserved"; "Model"; "vm_brk"; "m_halted"; "region_free"; "with_vmmaps"; "ENOMEM"; "SyscallEffect"; "errno_ret"; "in_arg"; "VmMaps"; "alloc_top"; "vm_limit"; "vm_start_brk"; "map_contains"; "mkEffectU"; "vm_forget_range"; "vm_noaccess"; "MemCopy"; "m_vm_lazy"; "maps_subtract"; "mkVmMapsFull"; "page_size"; "vm_init_sp"; "vm_mmap_base"; "m_vm_materialized"; "two_pow_64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "axst"; "ax_X"; "ax_setS"; "shadow_addr"; "word_byte"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "triple1"; "etriple"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "ms_svc_pending"; "machine_state"; "ms_mem"; "find_segment"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes.Malloc40"; "TOP"; "brk0w"; "brk0"; "mf_res"; "mg"; "n8w"; "reqw"; "pgw"; "mf_exp"; "n2w"; "n3w"; "rho20f"; "Fgrant"; "mg_dead"; "mgrant"; "RM19"; "a4"; "mg_ok"; "rho20"; "tp20"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "D_M"; "facts_M"; "X_M"; "vSP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_nZ"; "mmap_fixed_dead_model"; "mmap_fixed_ok_model"; "is_ret"; "mmap_n"; "mmap_none_vm"; "alloc_ceiling_hi"; "alloc_ceiling_lo"; "brk_eff"; "mmap_fixed_dead_vm"; "mmap_fixed_inv"; "mmap_fixed_ok_vm"; "mmap_rw_vm"; "mprotect_expose_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States"; "E20f"; "E21f"; "N18"; "refuse"; "E20g"; "E19"; "S20f"; "S20g_ko"; "S21f"; "U24"; "S20g_ok"; "cont"; "E18t"; "S18"; "S19f"; "S19g"; "U24c"; "vBRK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_LO"; "band_covered"; "SHADOW_BAND_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "after_sys_mem"; "unmap_range"; "zero_range"; "eff_mem";
"@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes"; "objs_clear_M"; "sp_clear_b"; "obj_clear_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "mmap_obj"; "S_after"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "mprotect_budget_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "vm_same"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_model_next"; "brk_grow_ok"; "mmap_fixed_noaccess_b"; "mmap_modeled_b"; "mmap_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "eblk_clear_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "tp_in_maps"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib"; "img_clear_b"; "lit_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import
  Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA MmapBrkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.MuslMalloc40States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S13S1S5Z0R1A2S7R1SaZ2Z40A2A2A2S0S13SfQ40M0S11G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma grant_facts_none_A : ltac2:(tb__ "0|6|
S10Q40M0A1M1S44G1G1S93R4R3R2R1A4S0S2fS31G1G1A2M2A1S43S40R4A1A1S6eS15A1A3S1S13S1S5SfG0R4A2M3R1A2S7R1S6G3S94R5A1A2A2A2S3S1S5Z10000R2A2S7R2Z646000A2A2A1F_;Fx;G1G1S69G2S30G1G1R2R1A4S42S40R7A1A1A3S13S1S5SfG0R7A2M4R1A2S7R1S6G4S94R8A1A2A2A2S3S1S5SfG0R5A2M5R2A2S7R2S6G5G3A2A2A2A1F_;Fx;F_;Fm;Fb;A2F_;F_;Fa;Flen;Fmd;Faddr;").
Proof.
  intros addr md len a (Hal & Hpos & Hceil & Hfree) Hres.
  destruct (mmap_nw (m_vmmaps md) a len Hceil) as [En _].
  rewrite Hres, segments_reserved_A in Hfree.
  split.
  - intros x Hx Himg. rewrite <- En in Hx.
    assert (R : forall b m, In (b, m) ([(Z_to_bv 64 0x10000, Z_to_bv 64 0x2a000); (Z_to_bv 64 0x3a000, Z_to_bv 64 0xaa000);
                             (Z_to_bv 64 0xe4000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xe9000, Z_to_bv 64 0x55d000)] ++ vm_maps (m_vmmaps md)) ->
                ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned m)).
    { intros b m Hin. exact (region_free_disj _ a (mmap_n len) b m Hfree Hin x Hx). }
    pose proof (R (Z_to_bv 64 0x10000) (Z_to_bv 64 0x2a000) (or_introl eq_refl)) as R1.
    pose proof (R (Z_to_bv 64 0x3a000) (Z_to_bv 64 0xaa000) (or_intror (or_introl eq_refl))) as R2.
    pose proof (R (Z_to_bv 64 0xe4000) (Z_to_bv 64 0x5000) (or_intror (or_intror (or_introl eq_refl)))) as R3.
    pose proof (R (Z_to_bv 64 0xe9000) (Z_to_bv 64 0x55d000) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as R4.
    rewrite !u64_of_lit in R1, R2, R3, R4 by lia. lia.
  - intros b m Hin x Hx. rewrite <- En in Hx. eapply (region_free_disj _ a (mmap_n len) b m Hfree); [|exact Hx].
    apply in_app_iff. right. exact Hin.
Qed.

Lemma smatchA_after_ret_fresh : ltac2:(tb__ "0|4|
S2fScaA1S18S2fS10Q40A1M0A1S64S2fS41A1M1S76S44G1S44G0S2fS17A1Sc6RbRaR9R8S30G1S6bR7S6cR6R5A2A4A5S0S35G0A1S46R4A1S3eG0A1A3Sc9R7R5A2S0S32S6aS17S2bSbcS21S62RbA1A1A1A1R4A3S33A3S7aS17S1fSc0ReS21S62RcA1A1R6A3A1R5A3S61R10Sc0RfS21S62RdA1M2A1M3R7A3ReS66RdSdbR6Sc2G2S22G3A1S23G2A1SbcG3A1A4A2A2S30G1S6bR9S6cSb7RbR7A2R8A2A4A5F_;F_;F_;F_;F_;Fnewfacts;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;Fsegs;").
Proof.
  intros segs rho tp A tr ms md tr' md' r newfacts HspA Hh' Hvs Hfb Hf.
  set (nx := ss_next (ax_S A)) in *. set (rho' := rho_set_rw rho nx r) in *.
  assert (Hag : agree_below nx rho rho') by (unfold rho'; apply agree_below_set_rw; lia).
  pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  pose proof (smatch_pendingA_swf segs _ _ _ _ HspA) as Hswf.
  set (S' := S_after (ax_S A) (SVar nx) (ss_objs (ax_S A)) (Pos.succ nx)).
  assert (S1 : smatch segs rho' S' (virt tp (tr', mkCfg (after_sys ms r) md'))).
  { unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    rewrite virt_unfold in Hsp.
    pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag Hsp) as Hsp2.
    unfold after_sys, S'. eapply smatch_after_sys; [exact Hsp2 | | | | | | |].
    + apply model_idle_vmd. exact Hh'.
    + lia.
    + cbn. apply Pos.ltb_lt. lia.
    + unfold rho'. cbn [eval]. apply rho_set_rw_at.
    + apply forallb_forall. intros o Ho. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) (swf_objs _ Hswf) o Ho)]. lia.
    + apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
    + exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2). }
  split; [|split; [eapply vm_same_MI; eauto | split; [|split]]].
  - cbn [ax_S ax_setS]. unfold add_facts.
    change (mkSS (ss_pc S') (ss_regs S') (ss_fregs S') (ss_fcsr S') (ss_resv S') (ss_objs S') (newfacts ++ ss_facts S') (ss_next S') (ss_lenient S'))
      with (with_facts S' (newfacts ++ ss_facts S')).
    apply smatch_refacts; [exact S1 | |].
    + unfold S'. cbn [ss_next ss_facts S_after]. rewrite forallb_app. apply andb_true_intro. split; [exact Hfb|].
      apply forallb_forall. intros f Hfi. eapply sprop_below_mono; [|exact (proj1 (forallb_forall _ _) (swf_facts _ Hswf) f Hfi)]. lia.
    + apply Forall_app. split; [exact Hf | exact (smatch_facts segs _ _ _ S1)].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply (shadow_ok_stable A _ rho rho' Hag Hwf Hswf eq_refl eq_refl eq_refl Hsh).
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Section BrkA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 214%Z.

  Lemma brk_query_only_okA : ltac2:(tb__ "0|1|
S0S10Q40M0A1S74Vms;U0A2S11G0Z0A2A3Sc5S6dVsegs;Vms;Vx8;A3Vm;A2F_;").
  Proof using Hh Hno.
    intros Hq. eapply only_okA_of_inv; [intros R; exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq)| |].
    - intros E; unfold is_ret in E; discriminate.
    - intros eff m' evs E _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_brk_query_invA : ltac2:(tb__ "0|3|
S2fS41A1M0S70S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0G2S74Vms;U0A2S11G1Z0A2A3S71Vsegs;S30G0S6bR4S6cVms;Vm;A2A4R3A3S0S70R4S30G0S6bR5S6cSb7Vms;S45S40Vm;A1A1A2Vm;A2A4A3F_;F_;F_;Fw';Ftr;").
  Proof using Hh Hno.
    intros tr w' Hp Hq Hw. eapply wstep_ret_invA; [exact Hp | exact Hh | | exact Hh | exact Hw].
    intros R HR. exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq HR).
  Qed.

  Lemma wstep_brk_query_introA : ltac2:(tb__ "0|3|
S2fS41A1M0S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0G2S74Vms;U0A2S11G1Z0A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb7Vms;S45S40Vm;A1A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using Hh Hno.
    intros tr Hp Hq. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@brk_query_intro (sys_input segs ms x8) m Hno Hq).
  Qed.

  Hypothesis Hsb : ltac2:(tb__ "0|2|
S5SfQ40M0S50S40Vm;A1M1A1A2SfG0S45G1A1A2A2").
  Hypothesis Hlt : ltac2:(tb__ "0|1|
S7SfQ40M0S45S40Vm;A1A1A2SfG0S74Vms;U0A2A2A2").

  Lemma brk_grow_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using Hh Hno Hsb Hlt.
    eapply only_okA_of_inv; [intros R; exact (@brk_grow_inv (sys_input segs ms x8) m R Hno Hsb Hlt)| |].
    - intros [(_ & E) | E]; unfold is_ret in E; discriminate.
    - intros eff m' evs [(_ & E) | E] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_brk_grow_invA : ltac2:(tb__ "0|4|
S2fS41A1M0S70S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S1S0S32SceVm;S74Vms;U0A2M2G2A3S33A3S0S70R3S30G0S6bR4S6cSb8Vms;G2SbbVms;S9cS40Vm;A1M3G2G2A3A2A3S48ScdG3G2G2A3Vm;A2A2A4A3A2S0S70R3S30G0S6bR4S6cSb7Vms;S45G3A1A2Vm;A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using Hh Hno Hsb Hlt.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@brk_grow_inv (sys_input segs ms x8) m _ Hno Hsb Hlt) in Hspec.
    destruct Hspec as [(Hg & E) | E]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hg|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app brk_eff] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. rewrite advance_apply_effect, app_nil_r by reflexivity. reflexivity.
      + exfalso. revert Hcd. rewrite m_halted_with_vmmaps. congruence.
    - right. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
  Qed.

  Lemma wstep_brk_grow_intro_failA : forall tr,
    ms_svc_pending ms = Some x8 ->
    brk_grow_ok m (ms_gpr ms 0) (ms_gpr ms 0) = false ->
    wstep segs (tr, mkCfg ms m) (tr, mkCfg (after_sys ms (vm_brk (m_vmmaps m))) m).
  Proof using Hh Hno Hsb Hlt.
    intros tr Hp Hg. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@brk_grow_intro_fail_ns (sys_input segs ms x8) m Hno Hsb Hlt Hg).
  Qed.

  Lemma wstep_brk_grow_intro_okA : forall tr,
    ms_svc_pending ms = Some x8 ->
    brk_grow_ok m (ms_gpr ms 0) (ms_gpr ms 0) = true ->
    wstep segs (tr, mkCfg ms m)
      (tr, mkCfg (after_sys_mem ms (ms_gpr ms 0) (eff_mem ms (brk_eff (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0))))
                 (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)).
  Proof using Hh Hno Hsb Hlt.
    intros tr Hp Hg.
    pose proof (@brk_grow_intro_ok (sys_input segs ms x8) m Hno Hsb Hlt Hg) as Hs.
    assert (HM : materialize_model_accesses (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)
                   (syscall_effect_accesses (brk_eff (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)))
                 = Some (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)).
    { cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app brk_eff]. apply materialize_nil. }
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite m_halted_with_vmmaps; exact Hh) HM) as W.
    rewrite app_nil_r, advance_apply_effect in W by reflexivity. exact W.
  Qed.
End BrkA.

Section FixedNoneA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S32ScfS74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S33A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S32Sd1S74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S3bA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S32Sd0S74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S3bA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S5S6SfQ40Vaddr;A2S94Vlen;A1A2S4eS40Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S13ScSfQ40Vaddr;A2S59A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S32S47S43S40Vm;A1A1Vaddr;Vn;A3S33A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S32S51S42S40Vm;A1A1Vaddr;Vn;A3S33A3").

  Let INV : ltac2:(tb__ "0|d|
SccS4aA1M0Sd5S6dVsegs;Vms;Vx8;A3M1Vm;R1A3S2S97R2S4bS49A1M2Vm;S34S41A1M3A4S2S0G0R2ScbS4aS52S4cG1U0A2M4S34S31S10Q40A1M5S2fS10Q8A1A1A2A1M6S34S31G5G5A2M7A1M8S38G7S30G5G5G4S98S4cG1U1A2A1M9A4G8A3MaS34S55A1MbS34S31G5S3fA2A1McA6S96S4cG1U3A2Vm;G4G9A4G3A4A3S0G0R2ScbS4aS52G2G6G8GaGbGcA6S95Vm;G4G9A3G3A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S9eS6dVsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfree;VHcont;Ac").

  Lemma mmap_fixed_ok_model_halted : ltac2:(tb__ "0|1|
S10Q40A1M0G0G0S0S35G0A1S46S96R3Vm;R2R1A4A1S46Vm;A1A3Fk;Fa;Ffl;").
  Proof using .
    intros. unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
    destruct (mmap_noreserve_b fl); autorewrite with model; reflexivity.
  Qed.
  Lemma mmap_fixed_dead_model_halted' : ltac2:(tb__ "0|1|
S10Q40A1M0G0S0S35G0A1S46S95Vm;R2R1A3A1S46Vm;A1A3Fk;Fa;").
  Proof using .
    intros. unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range. autorewrite with model. reflexivity.
  Qed.

  Lemma fixed_none_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | [E | E]]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | [E | E]] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_fixed_none_invA : ltac2:(tb__ "0|4|
S2fS41A1M0S70S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S0S70R3S30G0S6bR4S6cSb7Vms;S4bS49A1M2A2Vm;A2A4A3S2S0S70R3S30G0S6bR4S6cSb8Vms;Vaddr;Sb9S77Vms;A1Vaddr;Vn;A3M3A3S96Vflags;Vm;Vaddr;Vn;A4A2A4A3S0S70R3S30G0S6bR4S6cSb8Vms;G2G3A3S95Vm;Vaddr;Vn;A3A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | [E | E]]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right; left.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold flags, addr, n, len. rewrite mmap_fixed_ok_model_halted. congruence.
    - right; right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold addr, n, len. rewrite mmap_fixed_dead_model_halted'. congruence.
  Qed.

  Lemma wstep_fixed_none_intro_okA : forall tr,
    ms_svc_pending ms = Some x8 ->
    wstep segs (tr, mkCfg ms m)
      (tr, mkCfg (after_sys_mem ms addr (unmap_range (ms_mem ms) addr n)) (mmap_fixed_ok_model flags m addr n)).
  Proof using Halign Hceil Hcont Hfree Hh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros tr Hp.
    pose proof (@mmap_fixed_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_none Hnot_rw Hceil Halign Hpos Hfree Hcont) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mmap_fixed_ok_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.

End FixedNoneA.

Lemma maps_subtract_noop : ltac2:(tb__ "0|6|
S2fS31S10Q40M0A1M1G1A2M2A1M3S13S13S5R2R1A2G2S69G2R1R5A3S1S7Z0SfG0S39G1G1R2A3A2M4A2S2S5S6SfG0S3aG1G1R2A3A2M5G4A2R5A2S5R4G5A2A2A2F_;Fr;S0G3S57R5R4R3A3R5A3F_;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|].
  cbn [maps_subtract]. rewrite IH by (intros r Hr; apply H; right; exact Hr).
  destruct (H (a, sz) (or_introl eq_refl)) as [Hpos Hdis]. cbn [fst snd] in Hpos, Hdis.
  pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract. destruct Hdis as [Hl | Hr].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma vm_forget_range_noop : ltac2:(tb__ "0|6|
S13S13S44S5R3R2A2S31S10Q40M0A1M1G1A2M2S69G2R1S56R3A1A3S1S7Z0SfG0S39G1G1R2A3A2M3A2S2S5S6SfG0S3aG1G1R2A3A2M4G3A2R6A2S5R5G4A2A2A2F_;Fr;G1S69G1R1S5cR4A1A3S3S1S5R7SfG0R2A2M5A2S7G5R6A2A2A1F_;Fp;S0S44S53R6R5R4A3R4A3F_;F_;F_;Fmd;Fhi;Flo;").
Proof.
  intros lo hi md Hlh Hl Hm. unfold vm_forget_range. rewrite (maps_subtract_noop _ lo hi Hlh Hl).
  replace (List.filter (page_outside_range lo hi) (m_vm_materialized md)) with (m_vm_materialized md).
  - apply with_vm_backing_id.
  - symmetry. apply List.forallb_filter_id. apply forallb_forall. intros p Hp. unfold page_outside_range.
    apply negb_true_iff. apply andb_false_iff. destruct (Z.le_gt_cases lo (bv_unsigned p)); [right; apply Z.ltb_ge | left; apply Z.leb_gt]; pose proof (Hm p Hp); lia.
Qed.

Lemma region_free_shrink : ltac2:(tb__ "0|4|
S2fS31S10Q40M0A1M1G1A2A1G1G1G1G1S0S32S47R5R4R3A3S33A3S5SfG0R5A2M2SfG0R3A2M3A2S5S6SfG0R4A2G3A2S6SfG0R6A2G2A2A2S0S32S47R8R5R4A3S33A3F_;F_;F_;Fn';Fa';Fn;Fa;Fl;").
Proof.
  intros l a n a' n' Hf H1 H2. apply region_free_of_forall. intros b s Hin.
  pose proof (region_free_In _ _ _ _ _ Hf Hin) as Q. unfold iv_overlap in Q |- *.
  apply andb_false_iff in Q. apply andb_false_iff. destruct Q as [Q|Q]; apply Z.ltb_ge in Q; [left|right]; apply Z.ltb_ge; lia.
Qed.

Section MprotectA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 226%Z.
  Hypothesis Hprot : bv_unsigned (ms_gpr ms 2) = 3%Z.
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S13ScSfQ40Vaddr;A2S59A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S7S6SfQ40Vaddr;A2S94Vlen;A1A2S5dA2").
  Hypothesis Hna : ltac2:(tb__ "0|0|
S0S32S51S54S40Vm;A1A1Vaddr;Vn;A3S33A3").
  Hypothesis Hmp : ltac2:(tb__ "0|0|
S0S32S51S42S40Vm;A1A1Vaddr;Vn;A3S33A3").

  Let INV : ltac2:(tb__ "0|9|
SccS4aA1M0Sd5S6dVsegs;Vms;Vx8;A3M1Vm;R1A3S2S97R2S4bS49A1Vm;S34S41A1M2A4S1S0S32Sc4Vm;S4cG1U0A2M3S98S4cG1U1A2A1M4A3S33A3S0G0R2ScbS4aS52S11Q40M5Z0A2S34S31S10G5A1M6S2fS10Q8A1A1A2A1S38S31G6G6A2M7S30G6G6G3G4A4S34G7A1M8A3G8S34S55A1S34S31G6S3fA2A1A6Sc3Vm;G3G4A3G2A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
Sa1S6dVsegs;Vms;Vx8;A3Vm;VHno;VHprot;VHalign;VHlen;VHwrap;VHna;VHmp;A9").

  Lemma mprotect_model_next_halted : ltac2:(tb__ "0|1|
S10Q40A1M0G0S0S35G0A1S46Sc3Vm;R2R1A3A1S46Vm;A1A3Fk;Fa;").
  Proof using . intros. unfold mprotect_model_next. autorewrite with model. reflexivity. Qed.

  Lemma mprotect_expose_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | [_ E]]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | [_ E]] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_mprotect_expose_invA : ltac2:(tb__ "0|3|
S2fS41A1M0S70S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S0S70R3S30G0S6bR4S6cSb7Vms;S4bS49A1A2Vm;A2A4A3S0S70R3S30G0S6bR4S6cSb8Vms;S11G1Z0A2SbaS77Vms;A1Vaddr;Vn;A3A3Sc3Vm;Vaddr;Vn;A3A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | [Hb E]]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold addr, n, len. rewrite mprotect_model_next_halted. congruence.
  Qed.

  Lemma wstep_mprotect_expose_intro_failA : ltac2:(tb__ "0|2|
S2fS41A1M0S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S0S32Sc4Vm;Vaddr;Vn;A3S3bA3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb7Vms;S4bS49A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mprotect_expose_intro_fail (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb).
  Qed.

  Lemma wstep_mprotect_expose_intro_okA : ltac2:(tb__ "0|3|
S2fS41A1M0S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0S32Sc4Vm;Vaddr;Vn;A3S33A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb8Vms;S11G1Z0A2SbaS77Vms;A1Vaddr;Vn;A3A3Sc3Vm;Vaddr;Vn;A3A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb.
    pose proof (@mprotect_expose_intro_ok (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mprotect_model_next_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End MprotectA.

Definition sp_clear_b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|2|
S35S13A1S32Lx;SdaS2aVo;A1A1S13S3cS3cS9SeS8fA1R1A2S9R1SaZ2Z28A2A2A2S3dS2eS29Vo;A1M0S92A2S3cS9Z0M1R1A2SdeVfacts;S92G1G0A4A2A2A2Llo;S3bX35x2").
Definition obj_clear_M (facts : list sprop) (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S3dS3dSd9Vo;A1SbeVfacts;Vo;A2A2Sd3VGe;Vo;A2A2").
Definition objs_clear_M (Ge : list (sv * Z)) (S : sstate) : bool := ltac2:(tb__ "0|0|
S6aS1dSbfS1cVS;A1VGe;A2S23VS;A1A3").

Lemma sp_clear_sound : ltac2:(tb__ "0|2|
S18S2fS17A1S10Q40M0A1S13S13S1dS7aS17S1fR6A1R5A3S0S32SbeR6R2A2S33A3S5Z0R5A2S5S6SfG0R7A2R6A2R5A2S5S6R6S8fA2SfG0S19RaPaA2A2A2S25S24RbR6A2S30S13S13SfG0R9A2M1S6G1R8A2A4A2F_;F_;F_;F_;F_;Fo;Ftop;Fn;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a n top o HF Hb Hn Hceil HSP. unfold sp_clear_b in Hb.
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate]. apply lit_of_sound in Elo.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold D_M in H1.
  assert (HB : bv_unsigned (rw rho 10%positive) - D_M <= bv_unsigned (eval rho (ob_base o)) + lo).
  { apply Bool.orb_prop in H3 as [H3|H3].
    - apply sv_eqb_sound in H3. rewrite H3. unfold vSP. cbn [eval]. unfold D_M in *. lia.
    - apply andb_prop in H3 as [H4 H5]. apply Z.leb_le in H4. pose proof (uleq_sound rho facts _ _ _ HF H5) as U1.
      unfold U, vSP in U1. cbn [eval] in U1. unfold D_M in *. lia. }
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Elo. rewrite soff_lit_small by lia.
  unfold ranges_disjoint. cbn [fst snd]. unfold D_M in *. lia.
Qed.

Lemma objs_clear_M_sound : ltac2:(tb__ "0|6|
S18S2fS31S16S13A2M0A1S2dS10Q40M1A1S13S13S7aS17S1fR6A1S1cR4A1A3S0S32SbdR6R5A2S33A3S5Z0R4A2S5S6SfG1R6A2R5A2R4A2S5S6R5S8fA2SfG1S19RaPaA2A2A2S13S1S5SfG1R9A2M2R1A2S7R1S6G2R8A2A2A2S3S1S5Z10000R2A2S7R2Z646000A2A2A1F_;Fx;S16S13S69G0S30S16S13R2R1A4RdA3S13S1S5SfG1RdA2M3R1A2S7R1S6G3RcA2A2A2S3S1S5SfG1S1aR11R5A2A2M4R2A2S7R2S6G4R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S1dS69S1dR1S23RcA1A3S25S24RfR2A2S30S13S13SfG1RcA2M5S6G5RbA2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;F_;Ftop;Fn;Fa;FS;FGe;Frho;").
Proof.
  intros rho Ge S a n top HF Hb Hn Hceil HSP Hpw HG o Hin.
  pose proof (proj1 (forallb_forall _ _) Hb o Hin) as Ho. unfold obj_clear_M in Ho.
  apply Bool.orb_prop in Ho as [Ho|Ho]; [apply Bool.orb_prop in Ho as [Ho|Ho]|].
  - eapply img_clear_sound; eauto.
  - eapply sp_clear_sound; eauto.
  - eapply eblk_clear_sound; eauto.
Qed.

Lemma band_clear_of_free : ltac2:(tb__ "0|3|
S2fS31S10Q40M0A1M1G1A2A1G1G1Sb5R3Sb4Sb6A3S0S32S47R4R3R2A3S33A3S7Z0SfG0R3A2A2S13S1S5SfG0R6A2M2R1A2S7R1S6G2SfG0R5A2A2A2A2S3S1S5Sb4R2A2S7R2S6Sb4SbSb6Sb4A2A2A2A2A1F_;Fx;F_;F_;F_;Fn;Fa;Fl;").
Proof.
  intros l a n Hb Hf Hn x Hx.
  pose proof (grant_avoids_band l _ _ a n Hb ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) Hf Hn). lia.
Qed.

Lemma band_covered_subtract : ltac2:(tb__ "0|4|
S2fS31S10Q40A1M0G0A2M1A1M2G2S13S13S13S13SdfR5A1S5R5R4A2M3S2S5R3R6A2G3A2Sb5S37G1R9R8A3R5R4A3Sb5S37G1RaS57R9R8R7A3A3R6R5A3F_;F_;F_;F_;Fbhi;Fblo;Fhi;Flo;Fl;Fres;").
Proof.
  intros res l lo hi blo bhi Hwf Hlh Hd H x Hx. destruct (H x Hx) as (b & s & Hin & Hbs).
  apply in_app_iff in Hin as [Hin|Hin].
  - exists b, s. split; [apply in_app_iff; left; exact Hin | exact Hbs].
  - destruct (maps_subtract_keeps l lo hi (b, s) x (x + 1) Hwf Hlh Hin ltac:(cbn [fst]; lia) ltac:(cbn [fst snd]; lia) ltac:(lia) ltac:(lia))
      as ([b' s'] & Hin' & H1 & H2). cbn [fst snd] in H1, H2.
    exists b', s'. split; [apply in_app_iff; right; exact Hin' | lia].
Qed.

Section Malloc40.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S5fS18S2fS10Q40A1A1S2fS41A1M0S44R5R4R3R2R1A4S0G0R3S34S41A1A3F_;Fmd;Ftr;Ftp;Frho;S60S15Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S5fS18S2fS10Q40A1A1S2fS41A1M0S44R5R4R3R2R1A4S0G0R3S34S41A1A3F_;Fmd;Ftr;Ftp;Frho;Sc8S15Vok;R2A3F_;FJ;").
Variables (m : Model) (B : Z).
Definition brk0w : word := vm_brk (m_vmmaps m).
Definition brk0 : Z := bv_unsigned brk0w.
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S2fS31S10Q40A1M0G0A2A1S43S40Vm;A1A1S6eS15A1A3").
Hypothesis Hsb : ltac2:(tb__ "0|1|
S0S10Q40A1S50S40Vm;A1M0A1S45G0A1A3").
Hypothesis Hal : brk0 mod 4096 = 0.
Hypothesis Hlo : 0x646000 <= brk0.
Hypothesis Hhi : brk0 <= 0x80646000.
Hypothesis HB : ltac2:(tb__ "0|0|
S5S6VB;Z3000A2S4fS40Vm;A1A1A2").

Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40Vm;A1M1A1S42G1A1A3Sb4Sb6A3").

Definition TOP : Z := alloc_top (m_vmmaps m).
Lemma TOP_bounds : ltac2:(tb__ "0|0|
S1S5S9bS7bA2S5S7bS9aA2A2").
Proof using Htop. exact (alloc_top_bounds _ Htop). Qed.

Lemma OKFx : ltac2:(tb__ "0|0|
S44S13S60S15Vok;S6fR2R1A2A3FBx;Fmx;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S44S13Sc8S15Vok;S6fR2R1A2A3FBx;Fmx;").
Proof using OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma regs_of_pending : ltac2:(tb__ "0|4|
S18S2fS10Q40A1M0A1S64S2fS41A1M1S76S44Sc6S15R6R5R4S30G1S6bR3S6cR2R1A2A4A5S1S0G0S74R3U0A2S1aR7S79S16UaS1eS62R5A1A1M2S1bZ0A1M3A4A2A3S1S0G0S74R3U1A2S1aR7S79S16UbG2G3A4A2A3S1S0G0S74R3U2A2S1aR7S79S16UcG2G3A4A2A3S1S0G0S74R3U3A2S1aR7S79S16UdG2G3A4A2A3S1S0G0S74R3U4A2S1aR7S79S16UeG2G3A4A2A3S1S0G0S74R3U5A2S1aR7S79S16UfG2G3A4A2A3S0S35G0A1S75R3A1S36G0S1aR7S79S16U11G2G3A4A2A2A3A2A2A2A2A2A2F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband. intros rho tp A tr ms md Hsp. pose proof (pending_argsA segsA rho tp A tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp.
  unfold reg_sv in *. repeat split; assumption.
Qed.

Theorem node18 : ltac2:(tb__ "0|1|
S18S2fS10Q40A1A1S72S15Vok;S5eS15S6fVm;VB;A2M0SaeR2R1A5S5eS15G0SafSc0R2Sa4S7cA3R1A5A4Ftp;Frho;").
Proof using OKF OKP Hal Hlo Hhi.
  clear Htop Hband. intros rho tp. pose proof E18_at as (Hpc & Hecall & R17 & R10).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E18t [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (brk_query_only_okA segsA ms md _ Hh H214 G0)].
  - intros w' Hw. rewrite (wstep_brk_query_invA segsA ms md _ Hh H214 [] w' Hp G0 Hw).
    split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S18, cont. rewrite Evm. fold brk0w.
    assert (HN : ss_next (ax_S E18t) = N18) by reflexivity. rewrite <- HN.
    eapply smatchA_after_ret_fresh; [exact Hsp | exact Hh | apply vm_same_refl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    rewrite HN. unfold F18, vBRK, brk0 in *.
    constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval]; rewrite rho_set_rw_at.
    + split; [lia|]. change (2 ^ 12) with 4096. exact Hal.
    + rewrite (u64_of_lit 0x646000) by lia. lia.
    + rewrite (u64_of_lit 0x80646000) by lia. lia.
Qed.

Lemma xshadow_clear_of_disj : ltac2:(tb__ "0|a|
S18S64S10Q40M0A1S13S13S13S0S2fS31S16S16A2M1A1S65R5A1S91A3S0S16S63R6A1S1bSd2A1A3S7aS17S1fR8A1S1cS62R7A1A1A3S17S69S17R1S90A3S69S17R2S1cS62RaA1A1A3F_;Ff;S5R6Z10006fdf0000A2S5Z10007fff8000S6R7R6A2A2S13S1S5SfG0RbA2M2R1A2S7R1S6G2RaA2A2A2S3S1S5RaR2A2S7R2S6RaR9A2A2A2A1F_;Fx;S1G1S13S69G1R2S65ReA1A3S1S5SfG0S1aR10S3aS16S16R3A3A2A2M3R2A2S7R2S6G3SfG0S1aR10S39S16S16R3A3A2A2A2A2A2S3S1S5SfG0RfA2M4SfG0S67SfG0S1aR11S63R10A1A2A2R3A2A2M5A2S7G5S6G4ReA2A2A2A1F_;F_;Fy;Frr;G1S13S13S69G1R3S65RfA1A3S1S5SfG0S1aR11S3aS16S16R4A3A2A2M6R3A2S7R3S6G6SfG0S1aR11S39S16S16R4A3A2A2A2A2A2S1S5Z0R3A2S7R3Z8M7A2A2S3S1S5SfG0R11A2M8SfG0S68S6SfG0S1aR13S63R12A1A2A2S8R5G7A2A2R4A2A2M9A2S7G9S6G8R10A2A2A2A1F_;F_;F_;Fj;Fy;Frr;A2F_;F_;F_;F_;F_;F_;F_;FsZ;FbZ;FnZ;Fa;FA;Frho;").
Proof.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho A a nZ bZ sZ HX Hb HF Hin Hb1 Hb2 Hdisj. rewrite HX, Hb.
  assert (F1 : holds rho (SPUle (SLit 0x7fff7f000000) vXB)) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F2 : holds rho (SPUle (SAlu ALU_ADD vXB vXL) (SLit (2 ^ 47)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F3 : holds rho (SPUle vXL (SLit (2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F4 : holds rho (SPUle vXB (SLit (2 ^ 48)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  cbn [holds eval] in F1, F2, F3, F4. unfold vXB, vXL in F1, F2, F3, F4. cbn [eval] in F1, F2, F3, F4.
  rewrite (u64_of_lit 0x7fff7f000000) in F1 by lia. rewrite (u64_of_lit (2 ^ 47)) in F2 by lia.
  rewrite (u64_of_lit (2 ^ 40)) in F3 by lia. rewrite (u64_of_lit (2 ^ 48)) in F4 by lia.
  unfold alu64, alu in F2. rewrite bv_add_unsigned in F2.
  rewrite bv_wrap_small in F2 by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange (rw rho 52)); pose proof (urange (rw rho 53)); lia).
  cbn [eval]. unfold SHB. rewrite (u64_of_lit 0x7fff8000) by lia.
  split.
  - intros rr y [<-|[]] Hy. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
    assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
    change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
    unfold shadow_addr. rewrite u64_of_lit by lia. intros Hc. apply (Hdisj (2147450880 + y / 8)); lia.
  - intros rr y j [<-|[]] Hy Hj. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
    assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
    change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
    pose proof (Z.div_mod (2147450880 + y / 8) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (2147450880 + y / 8) 8 ltac:(lia)) as M.
    assert ((2147450880 + y / 8) / 8 <= 17594333495295 / 8) by (apply Z.div_le_mono; lia).
    change (17594333495295 / 8) with 2199291686911 in H.
    unfold word_byte. rewrite u64_of_lit by lia. intros Hc. apply (Hdisj ((2147450880 + y / 8) / 8 * 8 + j)); lia.
Qed.

Definition reqw : word := Z_to_bv 64 (brk0 + 8192).
Definition n2w : word := Z_to_bv 64 8192.

Definition n3w : word := Z_to_bv 64 12288.
Lemma n3w_val : bv_unsigned n3w = 12288.
Proof. reflexivity. Qed.
Definition mg : Model := ltac2:(tb__ "0|0|
S48ScdS40Vm;A1S81S81A3Vm;A2").

Lemma reqw_val : ltac2:(tb__ "0|0|
S0S13SfQ40S81A2S6S7dZ2000A2A3").
Proof using Hlo Hhi. unfold reqw. apply u64_of_lit. unfold brk0 in *. lia. Qed.
Lemma n2w_val : bv_unsigned n2w = 8192.
Proof. reflexivity. Qed.
Lemma req_sub : ltac2:(tb__ "0|1|
S0S10Q40M0A1S12G0S81S7cA3S84A3").
Proof using Hlo Hhi.
  apply bv_eq. rewrite bv_sub_unsigned, reqw_val, n2w_val. unfold brk0.
  replace (bv_unsigned brk0w + 8192 - bv_unsigned brk0w) with 8192 by lia. reflexivity.
Qed.

Lemma brk_model_next_grow : ltac2:(tb__ "0|1|
S4dS0S10Q40A1M0S45R1A1S7cA3S0S4dScdR2S81S81A3S58S43R2A1S38S31G0G0A2S30G0G0S7cS84A4S42R2A1A3S54R2A1S50R2A1S81S4fR2A1S5bR2A1S5aR2A1A8A3F_;Fhh;").
Proof using Hlo Hhi.
  intros hh Hb. pose proof reqw_val as RV. unfold brk_model_next. rewrite Hb.
  rewrite (brk_unmaps_grow reqw brk0w) by (unfold brk0 in *; lia). cbn [maps_subtract_ranges fold_left].
  unfold brk_maps_next. rewrite Hb.
  replace ((0 <? bv_unsigned brk0w) && (bv_unsigned reqw <? bv_unsigned brk0w))%Z%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; unfold brk0 in *; lia).
  unfold brk_grants, brk_is_grow. rewrite (w_is0_pos reqw) by (unfold brk0 in *; lia). cbn [negb andb].
  rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) by (unfold brk0 in *; lia).
  rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) by (unfold brk0 in *; lia). cbn [andb app].
  rewrite req_sub. reflexivity.
Qed.

Lemma mg_vmmaps : ltac2:(tb__ "0|2|
S0S4dS40S7fA1S58S43S40Vm;A1M0A1S38S31S10Q40A1M1G1A2S30G1G1S7cS84A4S42G0A1A3S54G0A1S50G0A1S81S4fG0A1S5bG0A1S5aG0A1A8A3").
Proof using Hlo Hhi. unfold mg. rewrite m_vmmaps_with_vmmaps. apply brk_model_next_grow. reflexivity. Qed.

Lemma objs_clear_E19 : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa7A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma facts_M_in_E19 : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa7A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Definition RM19 (rho rho1 : valuation) : Prop := ltac2:(tb__ "0|8|
S1S14S0S10Q40M0A1M1S19Vrho1;R1A2S19Vrho;R1A2A3Fi;S1S14S0S2fS10Q8M2A1M3A1S26Vrho1;R1A2S26Vrho;R1A2A3Fl;S1G1S3S1S5S7dSfG0R1A2M4A2S7G4S6S7dZ2000A2A2A2M5A1S0S35G3A1M6S20Vrho1;R2A2M7S20Vrho;R2A2A3F_;Fa;G1G5S0G6G7S36G3S11G2Z0A2A2A3F_;Fa;A2A2A2").

Theorem node19 : ltac2:(tb__ "0|5|
S18S2fS10Q40M0A1M1A1S0G1S19R2Sa4A2S7cA3S5S6S7bS8fA2SfG0S19R3PaA2A2A2S72S15Vok;S5eS15S6fVm;VB;A2M2Sa7R4R3A5S70S2S4S18S18S1S5S6S7dZ2000M3A2S7bA2S1S0S32S47S37S31G1G1A2S43S40Vm;A1M4A1S42G4A1A3S7cS85A3S33A3S1S8aR6R1A2S5eS15S6fS7fS6VB;G3A2A2Sb1R1R5R2A6A2A2A2Lrho1;A2S5eS15G2Sb0R5R4R1A6A2Lw;A4F_;F_;Ftp;Frho;").
Proof using OKF OKP Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HN18 HSP. pose proof E19_at as (Hpc & Hecall & R17 & R10 & Hnx).
  pose proof reqw_val as RV. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof n2w_val as NV. pose proof n3w_val as NV3.
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E19 [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0.
  assert (Ereq : ms_gpr ms 0 = reqw).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, RV, (u64_of_lit 8192) by lia. unfold brk0.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). pose proof (urange brk0w). unfold brk0 in *. lia. }
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  assert (Ebrk : vm_brk (m_vmmaps m) = brk0w) by reflexivity.
  assert (Hsb' : bv_unsigned (vm_start_brk (m_vmmaps md)) <= bv_unsigned (vm_brk (m_vmmaps md))) by (rewrite Evm, Hsb; lia).
  assert (Hlt : bv_unsigned (vm_brk (m_vmmaps md)) < bv_unsigned (ms_gpr ms 0)) by (rewrite Evm, Ereq, RV, Ebrk; unfold brk0; lia).
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (brk_grow_only_okA segsA ms md _ Hh H214 Hsb' Hlt)].
  - intros w' Hw.
    destruct (wstep_brk_grow_invA segsA ms md _ Hh H214 Hsb' Hlt [] w' Hp Hw) as [[Hg ->] | ->].
    +   left.
      rewrite Ereq in Hg |- *. rewrite Evm.

      assert (Hgate : brk0 + 8192 <= TOP /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true).
      { unfold brk_grow_ok in Hg. rewrite Evm, Ebrk in Hg.
        rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) in Hg by (unfold brk0 in *; lia).
        rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) in Hg by (rewrite RV; unfold brk0; lia). cbn [andb] in Hg.
        rewrite (page_round_up_Z_id (bv_unsigned brk0w)) in Hg by exact Hal.
        rewrite RV in Hg. rewrite (page_round_up_Z_id (brk0 + 8192)) in Hg
          by (unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal).
        unfold brk0 in Hg. rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned brk0w + 8192))) in Hg by lia.
        apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hc Hf]. apply Z.leb_le in Hc.
        rewrite Z_to_bv_bv_unsigned in Hf. unfold page_size in Hf. replace (bv_unsigned brk0w + 8192 + 4096 - bv_unsigned brk0w) with 12288 in Hf by lia.
        fold n3w in Hf. unfold brk0, TOP. split; [lia | exact Hf]. }
      destruct Hgate as [Hceil Hfree3].
      assert (Hfree : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n2w = true).
      { apply (region_free_shrink _ brk0w n3w); [exact Hfree3 | lia | rewrite NV, NV3; lia]. }
      rewrite (brk_eff_grow_aligned (m_vmmaps m) reqw);
        [| rewrite Ebrk; exact Hal
         | rewrite RV; unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal
         | rewrite Ebrk, RV; unfold brk0 in *; lia].
      rewrite Ebrk, req_sub.
      change (eff_mem ms (mkEffect reqw [] [(brk0w, n2w)])) with (zero_range (ms_mem ms) brk0w n2w).
      pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
      pose proof (xshadow_clear_of_disj rho E19 brk0w 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E19
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [_ HXw].
      set (h' := brk_model_next (m_vmmaps m) reqw reqw).
      set (ms' := after_sys_mem ms reqw (zero_range (ms_mem ms) brk0w n2w)).
      set (md' := with_vmmaps h' md).
      set (Ofull := mkObj vBRK (SLit 0) (SLit (bv_unsigned n2w)) [] DZero).
      set (A1 := ax_setS E19 (S_after (ax_S E19) (SAlu ALU_ADD vBRK (SLit 8192)) (ss_objs (ax_S E19) ++ [Ofull]) (Pos.succ N18))).
      assert (Hfreem : region_free (vm_maps (m_vmmaps md)) brk0w n2w = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Hfree)).
      assert (Hsm1 : smatchA segsA rho tp A1 ([], mkCfg ms' md')).
      { eapply (smatchA_after_grant_obj segsA rho rho tp E19 [] ms md [] h' brk0w n2w reqw (SAlu ALU_ADD vBRK (SLit 8192)) vBRK (Pos.succ N18) Hsp).
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- rewrite NV. lia.
        -- rewrite NV. unfold brk0 in *. lia.
        -- exact Hfreem.
        -- unfold headroom. rewrite Evm, NV. lia.
        -- intros x Hx. apply (grant_no_ro_A brk0w 8192); [intros z Hz; unfold brk0 in *; lia|]. rewrite NV in Hx. exact Hx.
        -- rewrite NV. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E19) brk0w 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E19);
             [lia | unfold brk0 in *; lia | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
        -- rewrite NV. exact HXw.
        -- apply agree_below_refl.
        -- rewrite Hnx. apply Pos.le_refl.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- rewrite <- Ereq, G0. unfold vBRK. cbn [eval]. rewrite HN18. reflexivity.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold vBRK. cbn [eval]. exact HN18. }
      assert (HK1 : KxA mg (B + 8192) rho tp [] md').
      { split; [reflexivity|]. split.
        -- unfold mg, md', h'. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- unfold md'. rewrite paid_with_vmmaps.
           pose proof (used_maps_cons_le md h' brk0w n2w (MI_ivs_wf segsA _ _ HMI)
                        ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite NV; unfold brk0 in *; lia)
                        ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)
                        ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)) as U.
           rewrite NV in U. lia. }

      pose proof (SPA_unobj segsA (KxA mg (B + 8192)) rho A1 (ss_objs (ax_S E19)) [Ofull] tp [] ms' md' eq_refl (conj Hsm1 HK1) (fun K => K)) as HS2.
      cbn zeta in HS2. set (rho1 := rho_absorb rho [Ofull] (vms md' tp ms')) in HS2.
      exists rho1. split; [exact Hceil|]. split; [exact Hfree3|].
      assert (Hrng : obj_range rho Ofull = (brk0, brk0 + 8192)).
      { unfold obj_range, obj_lo_of, obj_hi_of, Ofull, vBRK. cbn [ob_base ob_lo ob_hi eval]. rewrite HN18, NV.
        rewrite !soff_lit_small by lia. unfold brk0. f_equal; lia. }
      split.
      *   unfold RM19, rho1, rho_absorb. cbn [rw rl rm]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split.
        -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin]; [|reflexivity].
           exfalso. destruct Hin as (o & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
        -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin].
           ++ unfold vms, restrict, ms'. cbn [ms_mem]. unfold mrestrict.
              rewrite (hid_ext md md' tp) by reflexivity.
              rewrite (hid_false_of_region_free md tp brk0w n2w a (MI_lazy_in_maps segsA _ _ HMI) (MI_ivs_wf segsA _ _ HMI) Hfreem)
                by (rewrite NV; unfold brk0 in Ha; lia).
              rewrite after_sys_memq, zero_range_at. rewrite (proj2 (in_range_spec brk0w n2w a)) by (rewrite NV; unfold brk0 in Ha; lia). reflexivity.
           ++ exfalso. apply Hnin. exists Ofull. split; [left; reflexivity|]. rewrite Hrng. cbn [fst snd]. exact Ha.
      *
        replace S19g with (ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S E19)))); [exact HS2|].
        unfold S19g, cont, A1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    +   right. split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold S19f, cont. cbn [add_facts app].
      change (add_facts [] (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)))
        with (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)).
      rewrite app_nil_r, <- Hnx. rewrite Evm, Ebrk.
      change (S_after (ax_S E19) vBRK (ss_objs (ax_S E19)) (ss_next (ax_S E19))) with (ax_S (A_after E19 vBRK)).
      eapply (smatchA_after_ret_expr segsA rho tp E19 [] ms md [] md brk0w vBRK Hsp Hh (vm_same_refl md));
        [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold vBRK; cbn [eval]; exact HN18].
Qed.

Theorem enode19_any : forall (rho : valuation) (tp : list word),
  rw rho N18 = brk0w -> TOP + D_M <= bv_unsigned (rw rho 10%positive) ->
  etriple segsA (SPA segsA (KxA m B) E19 rho tp)
    (fun w => (exists rho1, brk0 + 8192 <= TOP /\
                 region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true /\
                 RM19 rho rho1 /\ SPA segsA (KxA mg (B + 8192)) S19g rho1 tp w) \/
              SPA segsA (KxA m B) S19f rho tp w).
Proof using Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HN18 HSP. pose proof E19_at as (Hpc & Hecall & R17 & R10 & Hnx).
  pose proof reqw_val as RV. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof n2w_val as NV. pose proof n3w_val as NV3.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E19 [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0.
  assert (Ereq : ms_gpr ms 0 = reqw).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, RV, (u64_of_lit 8192) by lia. unfold brk0.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). pose proof (urange brk0w). unfold brk0 in *. lia. }
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  assert (Ebrk : vm_brk (m_vmmaps m) = brk0w) by reflexivity.
  assert (Hsb' : bv_unsigned (vm_start_brk (m_vmmaps md)) <= bv_unsigned (vm_brk (m_vmmaps md))) by (rewrite Evm, Hsb; lia).
  assert (Hlt : bv_unsigned (vm_brk (m_vmmaps md)) < bv_unsigned (ms_gpr ms 0)) by (rewrite Evm, Ereq, RV, Ebrk; unfold brk0; lia).
  destruct (brk_grow_ok md (ms_gpr ms 0) (ms_gpr ms 0)) eqn:Hg.
  - eexists. split; [exact (wstep_brk_grow_intro_okA segsA ms md _ Hh H214 Hsb' Hlt [] Hp Hg)|].
    left.
    rewrite Ereq in Hg |- *. rewrite Evm.

    assert (Hgate : brk0 + 8192 <= TOP /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true).
    { unfold brk_grow_ok in Hg. rewrite Evm, Ebrk in Hg.
      rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) in Hg by (unfold brk0 in *; lia).
      rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) in Hg by (rewrite RV; unfold brk0; lia). cbn [andb] in Hg.
      rewrite (page_round_up_Z_id (bv_unsigned brk0w)) in Hg by exact Hal.
      rewrite RV in Hg. rewrite (page_round_up_Z_id (brk0 + 8192)) in Hg
        by (unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal).
      unfold brk0 in Hg. rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned brk0w + 8192))) in Hg by lia.
      apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hc Hf]. apply Z.leb_le in Hc.
      rewrite Z_to_bv_bv_unsigned in Hf. unfold page_size in Hf. replace (bv_unsigned brk0w + 8192 + 4096 - bv_unsigned brk0w) with 12288 in Hf by lia.
      fold n3w in Hf. unfold brk0, TOP. split; [lia | exact Hf]. }
    destruct Hgate as [Hceil Hfree3].
    assert (Hfree : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n2w = true).
    { apply (region_free_shrink _ brk0w n3w); [exact Hfree3 | lia | rewrite NV, NV3; lia]. }
    rewrite (brk_eff_grow_aligned (m_vmmaps m) reqw);
      [| rewrite Ebrk; exact Hal
       | rewrite RV; unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal
       | rewrite Ebrk, RV; unfold brk0 in *; lia].
    rewrite Ebrk, req_sub.
    change (eff_mem ms (mkEffect reqw [] [(brk0w, n2w)])) with (zero_range (ms_mem ms) brk0w n2w).
    pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
    pose proof (xshadow_clear_of_disj rho E19 brk0w 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                  (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E19
                  ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [_ HXw].
    set (h' := brk_model_next (m_vmmaps m) reqw reqw).
    set (ms' := after_sys_mem ms reqw (zero_range (ms_mem ms) brk0w n2w)).
    set (md' := with_vmmaps h' md).
    set (Ofull := mkObj vBRK (SLit 0) (SLit (bv_unsigned n2w)) [] DZero).
    set (A1 := ax_setS E19 (S_after (ax_S E19) (SAlu ALU_ADD vBRK (SLit 8192)) (ss_objs (ax_S E19) ++ [Ofull]) (Pos.succ N18))).
    assert (Hfreem : region_free (vm_maps (m_vmmaps md)) brk0w n2w = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Hfree)).
    assert (Hsm1 : smatchA segsA rho tp A1 ([], mkCfg ms' md')).
    { eapply (smatchA_after_grant_obj segsA rho rho tp E19 [] ms md [] h' brk0w n2w reqw (SAlu ALU_ADD vBRK (SLit 8192)) vBRK (Pos.succ N18) Hsp).
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- rewrite NV. lia.
      -- rewrite NV. unfold brk0 in *. lia.
      -- exact Hfreem.
      -- unfold headroom. rewrite Evm, NV. lia.
      -- intros x Hx. apply (grant_no_ro_A brk0w 8192); [intros z Hz; unfold brk0 in *; lia|]. rewrite NV in Hx. exact Hx.
      -- rewrite NV. intros o Ho.
         apply (objs_clear_M_sound rho [] (ax_S E19) brk0w 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E19);
           [lia | unfold brk0 in *; lia | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      -- rewrite NV. exact HXw.
      -- apply agree_below_refl.
      -- rewrite Hnx. apply Pos.le_refl.
      -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
      -- rewrite <- Ereq, G0. unfold vBRK. cbn [eval]. rewrite HN18. reflexivity.
      -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
      -- unfold vBRK. cbn [eval]. exact HN18. }
    assert (HK1 : KxA mg (B + 8192) rho tp [] md').
    { split; [reflexivity|]. split.
      -- unfold mg, md', h'. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
      -- unfold md'. rewrite paid_with_vmmaps.
         pose proof (used_maps_cons_le md h' brk0w n2w (MI_ivs_wf segsA _ _ HMI)
                      ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite NV; unfold brk0 in *; lia)
                      ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)
                      ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)) as U.
         rewrite NV in U. lia. }

    pose proof (SPA_unobj segsA (KxA mg (B + 8192)) rho A1 (ss_objs (ax_S E19)) [Ofull] tp [] ms' md' eq_refl (conj Hsm1 HK1) (fun K => K)) as HS2.
    cbn zeta in HS2. set (rho1 := rho_absorb rho [Ofull] (vms md' tp ms')) in HS2.
    exists rho1. split; [exact Hceil|]. split; [exact Hfree3|].
    assert (Hrng : obj_range rho Ofull = (brk0, brk0 + 8192)).
    { unfold obj_range, obj_lo_of, obj_hi_of, Ofull, vBRK. cbn [ob_base ob_lo ob_hi eval]. rewrite HN18, NV.
      rewrite !soff_lit_small by lia. unfold brk0. f_equal; lia. }
    split.
    *   unfold RM19, rho1, rho_absorb. cbn [rw rl rm]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split.
      -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin]; [|reflexivity].
         exfalso. destruct Hin as (o & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
      -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin].
         ++ unfold vms, restrict, ms'. cbn [ms_mem]. unfold mrestrict.
            rewrite (hid_ext md md' tp) by reflexivity.
            rewrite (hid_false_of_region_free md tp brk0w n2w a (MI_lazy_in_maps segsA _ _ HMI) (MI_ivs_wf segsA _ _ HMI) Hfreem)
              by (rewrite NV; unfold brk0 in Ha; lia).
            rewrite after_sys_memq, zero_range_at. rewrite (proj2 (in_range_spec brk0w n2w a)) by (rewrite NV; unfold brk0 in Ha; lia). reflexivity.
         ++ exfalso. apply Hnin. exists Ofull. split; [left; reflexivity|]. rewrite Hrng. cbn [fst snd]. exact Ha.
    *
      replace S19g with (ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S E19)))); [exact HS2|].
      unfold S19g, cont, A1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - eexists. split; [exact (wstep_brk_grow_intro_failA segsA ms md _ Hh H214 Hsb' Hlt [] Hp Hg)|].
    right.
    split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S19f, cont. cbn [add_facts app].
    change (add_facts [] (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)))
      with (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)).
    rewrite app_nil_r, <- Hnx. rewrite Evm, Ebrk.
    change (S_after (ax_S E19) vBRK (ss_objs (ax_S E19)) (ss_next (ax_S E19))) with (ax_S (A_after E19 vBRK)).
    eapply (smatchA_after_ret_expr segsA rho tp E19 [] ms md [] md brk0w vBRK Hsp Hh (vm_same_refl md));
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold vBRK; cbn [eval]; exact HN18].
Qed.

Definition pgw : word := Z_to_bv 64 4096.
Definition mg_ok : Model := ltac2:(tb__ "0|0|
S53S7dS6S7dZ1000A2S48S9fS40S7fA1S7cS82A3S7fA2A3").
Definition mg_dead : Model := ltac2:(tb__ "0|0|
S53S7dS6S7dZ1000A2S48S9dS40S7fA1S7cS82A3S7fA2A3").
Definition rho20 (rho : valuation) : valuation := ltac2:(tb__ "0|0|
Sd8Vrho;Sb9S20Vrho;A1S7cS82A3A2").
Definition tp20 (tp : list word) : list word := ltac2:(tb__ "0|0|
Se0S7dS6S7dZ1000A2Vtp;A3").

Lemma objs_clear_E20g : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa6A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E20g : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa6A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma S20g_ok_eq : ltac2:(tb__ "0|0|
S0S64SacSc7Sa6Sb3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S20g_ko_eq : ltac2:(tb__ "0|0|
S0S64Sa9Sc7Sa6S1bSdcA1A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma alloc_top_mg : ltac2:(tb__ "0|0|
S0S13S4eS40S7fA1A1S7bA3").
Proof using Hlo Hhi. unfold TOP, alloc_top. rewrite mg_vmmaps. reflexivity. Qed.

Lemma band_mg : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40S7fA1M1A1S42G1A1A3Sb4Sb6A3").
Proof using Hlo Hhi Hband. rewrite mg_vmmaps. cbn [vm_reserved vm_maps]. apply band_covered_app_cons. exact Hband. Qed.

Theorem node20g : ltac2:(tb__ "0|6|
S18S2fS10Q40M0A1M1A1S13S0G1S19R3Sa4A2S7cA3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S0S32S47S37S31G1G1A2M2S43S40Vm;A1M3A1S42G3A1A3S7cS85A3S33A3S72S15Vok;S5eS15S6fS7fR4A2Sa6R6R5A5S70S2S5eS15S6fS7fR5A2Sa9R7R6R1A6S2S5eS15S6fS8cR5A2SacS8dR7A1M4R6R1A6S1Sb5S37G2S43S40S88A1M5A1S42G5A1A3Sb4Sb6A3S5eS15S6fS88R5A2Sa9G4S8eR6A1R1A6A2A2A2Lw;A4F_;F_;F_;FB1;Ftp;Frho;").
Proof using OKF OKP Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp B1 HN18 HSP Hfree3. pose proof E20g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof alloc_top_mg as ATG. pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof mg_vmmaps as MG.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mg Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20g [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pgw) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, ATG; unfold brk0 in *; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; unfold brk0 in *; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear brk0w pgw b s Hin). unfold brk0 in *; lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite n2w_val, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  pose proof (xshadow_clear_of_disj rho E20g brk0w 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20g
                ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
  assert (Hobjs : forall o, In o (ss_objs (ax_S E20g)) -> ranges_disjoint (obj_range rho o) (bv_unsigned brk0w, bv_unsigned brk0w + 4096)).
  { intros o Ho.
    apply (objs_clear_M_sound rho [] (ax_S E20g) brk0w 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20g);
      [lia | | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      unfold brk0 in *; lia. }
  split.
  - eapply (OKPx mg B1); [exact HK | exact Hp |].
    apply (fixed_none_only_okA segsA ms md _ H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont).
  - intros w' Hw.
    destruct (wstep_fixed_none_invA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] w' Hp Hw)
      as [-> | [-> | ->]].
    +   left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      rewrite S20g_ko_eq. unfold enomem_ret.
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    +   right; left.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
      unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Enr). rewrite HnZ, G0, Upg.
      split.
      * rewrite S20g_ok_eq. unfold A_after.
        eapply (smatchA_after_protnone segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw brk0w vBRK (ss_next (ax_S E20g)) Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact Hal.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. unfold brk0 in *. lia.
        -- rewrite Upg. exact Hobjs.
        -- rewrite Upg. exact HXb.
        -- unfold rho20. apply agree_below_refl.
        -- apply Pos.le_refl.
        -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold rho20, vBRK. cbn [eval rw set_rm]. exact HN18.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold mg_ok. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
           pose proof (used_protnone_le md (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw Hivs ltac:(rewrite Upg; unfold brk0 in *; lia) eq_refl eq_refl) as UP.
           rewrite Upg in UP.
           pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) tp
                         ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3) (MI_nodupT segsA _ _ HMI)) as UF.
           rewrite (unpaid_ext md (with_vmmaps _ md)) in UF by reflexivity.
           unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
    +   right; right.
      unfold mmap_fixed_dead_model, with_mmap_destroyed. rewrite HnZ, G0, Upg.
      split.
      {
        unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_reserved vm_maps].
        rewrite <- Evm, ?Upg.
        apply band_covered_subtract; [exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | lia | | rewrite Evm; exact band_mg].
        unfold brk0 in *. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. right.
        destruct (Z.le_gt_cases (bv_unsigned brk0w + 4096) 0x7fff7000) as [L|L]; [exact L|]. exfalso.
        destruct (Z.le_gt_cases 0x7fff7000 (bv_unsigned brk0w)).
        * apply (HBD (bv_unsigned brk0w)); lia.
        * apply (HBD 0x7fff7000); lia. }
      split.
      * rewrite S20g_ko_eq. unfold A_after.
        eapply (smatchA_after_destroy segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) brk0w pgw _ (SLit enomem_ret) (ss_next (ax_S E20g)) Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact Hal.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. unfold brk0 in *. lia.
        -- rewrite Upg. exact Hobjs.
        -- rewrite Upg. exact HXb.
        -- unfold rho20. apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. unfold enomem_ret. apply Z_to_bv_bv_unsigned.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold mg_dead. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
           unfold paid, tp20.
           pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096)
                         (tp_forget brk0 (brk0 + 4096) tp) ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3)
                         ltac:(unfold tp_forget; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI))) as L.
           rewrite (unpaid_ext md (with_vmmaps _ md)) in L by reflexivity.
           pose proof (used_destroy_le md (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) Hivs ltac:(lia)
                         ltac:(cbn; rewrite Upg; reflexivity) ltac:(cbn; rewrite Upg; reflexivity)) as UD.
           assert (LT : (length (unpaid md (tp_forget brk0 (brk0 + 4096) tp)) <= length (unpaid md tp))%nat).
           { unfold unpaid, tp_forget.
             apply List.NoDup_incl_length; [apply List.NoDup_filter; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI)|].
             intros p Hpin. apply List.filter_In in Hpin as [Hp1 Hp2]. apply List.filter_In in Hp1 as [Hp0 Hp1]. apply List.filter_In. split; [exact Hp0|exact Hp2]. }
           unfold paid in Hpaid. unfold brk0 in *. pose proof page_size_pos. nia.
Qed.

Theorem enode20g_ok : forall (rho : valuation) (tp : list word) (B1 : Z),
  rw rho N18 = brk0w -> TOP + D_M <= bv_unsigned (rw rho 10%positive) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true ->
  etriple segsA (SPA segsA (KxA mg B1) E20g rho tp) (SPA segsA (KxA mg_ok B1) S20g_ok (rho20 rho) tp).
Proof using Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp B1 HN18 HSP Hfree3. pose proof E20g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof alloc_top_mg as ATG. pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof mg_vmmaps as MG.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mg Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20g [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pgw) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, ATG; unfold brk0 in *; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; unfold brk0 in *; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear brk0w pgw b s Hin). unfold brk0 in *; lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite n2w_val, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  pose proof (xshadow_clear_of_disj rho E20g brk0w 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20g
                ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
  assert (Hobjs : forall o, In o (ss_objs (ax_S E20g)) -> ranges_disjoint (obj_range rho o) (bv_unsigned brk0w, bv_unsigned brk0w + 4096)).
  { intros o Ho.
    apply (objs_clear_M_sound rho [] (ax_S E20g) brk0w 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20g);
      [lia | | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      unfold brk0 in *; lia. }
  eexists. split; [exact (wstep_fixed_none_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] Hp)|].
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
  unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Enr). rewrite HnZ, G0, Upg.
  split.
  * rewrite S20g_ok_eq. unfold A_after.
    eapply (smatchA_after_protnone segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw brk0w vBRK (ss_next (ax_S E20g)) Hsp).
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- exact Hal.
    -- rewrite Upg. reflexivity.
    -- rewrite Upg. unfold brk0 in *. lia.
    -- rewrite Upg. exact Hobjs.
    -- rewrite Upg. exact HXb.
    -- unfold rho20. apply agree_below_refl.
    -- apply Pos.le_refl.
    -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    -- unfold rho20, vBRK. cbn [eval rw set_rm]. exact HN18.
  * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
    -- unfold mg_ok. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
    -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
       pose proof (used_protnone_le md (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw Hivs ltac:(rewrite Upg; unfold brk0 in *; lia) eq_refl eq_refl) as UP.
       rewrite Upg in UP.
       pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) tp
                     ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3) (MI_nodupT segsA _ _ HMI)) as UF.
       rewrite (unpaid_ext md (with_vmmaps _ md)) in UF by reflexivity.
       unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.

Definition mgrant (mx : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S48Sa0S40Vmx;A1S82Va;A3Vmx;A2").
Definition Fgrant (nx : positive) : list sprop := ltac2:(tb__ "0|0|
S38S17S27Vnx;ZcA2S38S17S28S22Vnx;A1S1bSbZ7fffff800000Z1000A2A1A2S34S17A1A3A3").

Section RwNode.
Variables (E : axst) (mx : Model) (Bx : Z) (G : list (sv * Z)).
Hypothesis HXE : ax_X E = X_M.
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S16S63VE;A1S1bSd2A1A3").
Hypothesis HFE : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62VE;A1A1A3F_;Ff;").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S35Sd6A1SddS15S2cS62VE;A1A1A2S36Sd6Sd7A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S16S79S16U11S1eS62VE;A1A1S1bZ0A1A4S1bZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|1|
S0S16S79S16UaS1eS62VE;A1A1S1bZ0A1M0A4G0A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S16S79S16UbS1eS62VE;A1A1S1bZ0A1A4S1bZ1000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S16S79S16UcS1eS62VE;A1A1S1bZ0A1A4S1bZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S16S79S16UdS1eS62VE;A1A1S1bZ0A1A4S1bZ22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S16S79S16UeS1eS62VE;A1A1S1bZ0A1A4S1bSbSaZ2Z40A2Z1A2A1A3").
Hypothesis R15 : ltac2:(tb__ "0|1|
S0S16S79S16UfS1eS62VE;A1A1S1bZ0A1M0A4G0A3").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S32SbdVG;S62VE;A1A2S33A3").
Hypothesis Hresx : ltac2:(tb__ "0|1|
S0S2fS31S10Q40A1M0G0A2A1S43S40Vmx;A1A1S6eS15A1A3").
Hypothesis HBx : ltac2:(tb__ "0|0|
S5S6VBx;Z1000A2S4fS40Vmx;A1A1A2").
Hypothesis Htopx : init_sp_ok (m_vmmaps mx).
Hypothesis Hbandx : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40Vmx;A1M1A1S42G1A1A3Sb4Sb6A3").

Theorem node_rw : ltac2:(tb__ "0|8|
S18S2fS10Q40M0A1M1A1S16S13S69S31S16S13A2S30S16S13R2R1A4VG;A3S4G1G1S4G1G1S1S69S31G1G1A2S30G1G1R2R1A4S42S40Vmx;A1M2A1A3S1S5SfG0R2A2M3SfG0S1aR7R5A2A2M4A2S5S6G4R4A2S6G3SfG0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fsz;Fe;S5S6S4eG2A1S8fA2SfG0S19R3PaA2A2A2S72S15Vok;S5eS15S6fVmx;VBx;A2M5VE;R4R3A5S70S2S5eS15G5Sa5VE;A1R5R4R1A6S4G1G1S1S93S11G0Z0A2Vmx;S82R1A4S5eS15S6fS89Vmx;R1A2S6VBx;Z1000M6A2A2SadVE;S22S21S62VE;A1A1M7A1S38S1dSc1G7G6A2S34S1dA1A3S87G7A1SbcG7A1A5Sc0R6G7R1A3R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using OKF OKP HXE HbE HFE Hecall R17 R10 R11 R12 R13 R14 R15 Hclear Hresx HBx Htopx Hbandx.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HG HSP. pose proof (alloc_top_bounds _ Htopx) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  eapply triple1_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (triple1_mmap_rw_objA segsA ok (KxA mx Bx) (KxA mx Bx)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) mx pgw a /\ KxA (mgrant mx a) (Bx + 4096) rho' tp' tr' md')
        E rho tp 4096).
      - apply OKFx. - apply OKPx. - apply stableA_KxA. - exact Hecall.
      - unfold reg_sv. exact R17. - unfold reg_sv. exact R11. - reflexivity. - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md mx Hem) as (Evm & _).
        pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
        destruct (regs_of_pending rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & _).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 4096) with pgw in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        split; [exact HK|].
        intros a Hpl. rewrite G0, G1, G3 in Hpl.
        pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).
        rewrite HnZ in Pceil. rewrite Hn in Pfree.
        assert (Hplx : mmap_place_ok_none (Z_to_bv 64 0) mx pgw a).
        { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
        assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a pgw = true) by exact (region_free_app_r _ _ _ _ Pfree).
        pose proof (grant_facts_A _ _ _ _ _ Hpl ltac:(rewrite Evm; exact Hresx)) as (_ & _ & _ & Himg & Hmaps). rewrite HnZ in Himg, Hmaps.
        pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a pgw ltac:(rewrite Evm; exact Hbandx) Pfree ltac:(rewrite Upg; lia)) as HBD.
        rewrite Upg in HBD.
        pose proof (xshadow_clear_of_disj rho E a 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) HXE HbE
                      (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) HFE
                      ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
        split; [|split; [|split]].
        + intros o Ho.
          apply (objs_clear_M_sound rho G (ax_S E) a 4096 (alloc_top (m_vmmaps mx)) (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear);
            [lia | rewrite <- Evm; exact Pceil | exact HSP | exact Himg | | exact Ho].
          intros i sz Hin x Hx Hblk. destruct (HG i sz Hin) as (b & s0 & Hm & Hb1 & Hb2).
          apply (Hmaps b s0 ltac:(rewrite Evm; exact Hm) x Hx). lia.
        + intros x Hx. apply (grant_no_ro_A a 4096); [exact Himg | exact Hx].
        + exact HXb.
        + split; [exact Hplx|]. rewrite G1. split; [reflexivity|]. split.
          * unfold mgrant, mmap_rw_vm. rewrite Hn, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
          * rewrite paid_with_vmmaps.
            pose proof (used_maps_cons_le md (mmap_rw_vm (m_vmmaps md) pgw a) a pgw (MI_ivs_wf segsA _ _ HMI)
                         ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Upg; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                         ltac:(unfold mmap_rw_vm; rewrite Hn; reflexivity) eq_refl) as U.
            rewrite Upg in U. lia. }
  intros w [Hw | (a & Hsm & Hpl & Hk)]; [left | right; exists a].
  { unfold refuse, enomem_ret. replace (A_after E (SLit (bv_unsigned (errno_ret ENOMEM)))) with (mkAX (S_ret_lit (ax_S E) (errno_ret ENOMEM)) [] (SLit SHB)) || idtac. exact Hw. }
  split; [exact Hpl|].

  unfold cont.
  change (ax_setS E (add_facts (Fgrant (ss_next (ax_S E))) (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E))))))
    with (ax_with_facts (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))
            (Fgrant (ss_next (ax_S E)) ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))).
  apply SPA_refacts; [split; [exact Hsm|exact Hk] | |].
  - cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? Pos.succ (ss_next (ax_S E)))%positive = true) by (apply Pos.ltb_lt; lia).
    apply andb_true_intro. split.
    + unfold Fgrant. cbn. rewrite !X. reflexivity.
    + destruct Hsm as ((W & _) & _). cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil.
    unfold Fgrant. cbn [ax_S ax_setS ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by lia. lia.
Qed.

Theorem enode_rw_any : ltac2:(tb__ "0|8|
S18S2fS10Q40M0A1M1A1S16S13S69S31S16S13A2S30S16S13R2R1A4VG;A3S4G1G1S4G1G1S1S69S31G1G1A2S30G1G1R2R1A4S42S40Vmx;A1M2A1A3S1S5SfG0R2A2M3SfG0S1aR7R5A2A2M4A2S5S6G4R4A2S6G3SfG0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fsz;Fe;S5S6S4eG2A1S8fA2SfG0S19R3PaA2A2A2S73S15S5eS15S6fVmx;VBx;A2M5VE;R4R3A5S70S2S5eS15G5Sa5VE;A1R5R4R1A6S4G1G1S1S93S11G0Z0A2Vmx;S82R1A4S5eS15S6fS89Vmx;R1A2S6VBx;Z1000M6A2A2SadVE;S22S21S62VE;A1A1M7A1S38S1dSc1G7G6A2S34S1dA1A3S87G7A1SbcG7A1A5Sc0R6G7R1A3R5R2A6A2La;A2A2Lw;A3F_;F_;Ftp;Frho;").
Proof using HXE HbE HFE Hecall R17 R10 R11 R12 R13 R14 R15 Hclear Hresx HBx Htopx Hbandx.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HG HSP. pose proof (alloc_top_bounds _ Htopx) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (etriple_mmap_rw_obj_anyA segsA (KxA mx Bx) (KxA mx Bx)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) mx pgw a /\ KxA (mgrant mx a) (Bx + 4096) rho' tp' tr' md')
        E rho tp 4096).
      - apply stableA_KxA. - exact Hecall.
      - unfold reg_sv. exact R17. - unfold reg_sv. exact R11. - reflexivity. - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md mx Hem) as (Evm & _).
        pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
        destruct (regs_of_pending rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & _).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 4096) with pgw in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        split; [exact HK|].
        intros a Hpl. rewrite G0, G1, G3 in Hpl.
        pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).
        rewrite HnZ in Pceil. rewrite Hn in Pfree.
        assert (Hplx : mmap_place_ok_none (Z_to_bv 64 0) mx pgw a).
        { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
        assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a pgw = true) by exact (region_free_app_r _ _ _ _ Pfree).
        pose proof (grant_facts_A _ _ _ _ _ Hpl ltac:(rewrite Evm; exact Hresx)) as (_ & _ & _ & Himg & Hmaps). rewrite HnZ in Himg, Hmaps.
        pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a pgw ltac:(rewrite Evm; exact Hbandx) Pfree ltac:(rewrite Upg; lia)) as HBD.
        rewrite Upg in HBD.
        pose proof (xshadow_clear_of_disj rho E a 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) HXE HbE
                      (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) HFE
                      ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
        split; [|split; [|split]].
        + intros o Ho.
          apply (objs_clear_M_sound rho G (ax_S E) a 4096 (alloc_top (m_vmmaps mx)) (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear);
            [lia | rewrite <- Evm; exact Pceil | exact HSP | exact Himg | | exact Ho].
          intros i sz Hin x Hx Hblk. destruct (HG i sz Hin) as (b & s0 & Hm & Hb1 & Hb2).
          apply (Hmaps b s0 ltac:(rewrite Evm; exact Hm) x Hx). lia.
        + intros x Hx. apply (grant_no_ro_A a 4096); [exact Himg | exact Hx].
        + exact HXb.
        + split; [exact Hplx|]. rewrite G1. split; [reflexivity|]. split.
          * unfold mgrant, mmap_rw_vm. rewrite Hn, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
          * rewrite paid_with_vmmaps.
            pose proof (used_maps_cons_le md (mmap_rw_vm (m_vmmaps md) pgw a) a pgw (MI_ivs_wf segsA _ _ HMI)
                         ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Upg; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                         ltac:(unfold mmap_rw_vm; rewrite Hn; reflexivity) eq_refl) as U.
            rewrite Upg in U. lia. }
  intros w [Hw | (a & Hsm & Hpl & Hk)]; [left | right; exists a].
  { unfold refuse, enomem_ret. replace (A_after E (SLit (bv_unsigned (errno_ret ENOMEM)))) with (mkAX (S_ret_lit (ax_S E) (errno_ret ENOMEM)) [] (SLit SHB)) || idtac. exact Hw. }
  split; [exact Hpl|].

  unfold cont.
  change (ax_setS E (add_facts (Fgrant (ss_next (ax_S E))) (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E))))))
    with (ax_with_facts (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))
            (Fgrant (ss_next (ax_S E)) ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))).
  apply SPA_refacts; [split; [exact Hsm|exact Hk] | |].
  - cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? Pos.succ (ss_next (ax_S E)))%positive = true) by (apply Pos.ltb_lt; lia).
    apply andb_true_intro. split.
    + unfold Fgrant. cbn. rewrite !X. reflexivity.
    + destruct Hsm as ((W & _) & _). cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil.
    unfold Fgrant. cbn [ax_S ax_setS ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by lia. lia.
Qed.
End RwNode.

Lemma find_segment_none_A' : ltac2:(tb__ "0|0|
S13S3S1S5Z10000R1A2S7R1Z646000A2A2A1S0S35ScaA1S78S15R2Z1A3S3eScaA1A3F_;Fz;").
Proof.
  clear. intros z Hz. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 172032%N) with 172032.
  change (Z.of_N 237568%N) with 237568. change (Z.of_N 696320%N) with 696320.
  change (Z.of_N 933888%N) with 933888. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 954368%N) with 954368. change (Z.of_N 5623808%N) with 5623808.
  repeat match goal with |- context [if ?c then _ else _] =>
    destruct c eqn:?C; [apply andb_prop in C as [?C1 ?C2]; apply Z.leb_le in C1; apply Z.leb_le in C2; lia | clear C] end.
  reflexivity.
Qed.

Definition n8w : word := Z_to_bv 64 8192.
Definition mf_res (a : word) : Model := ltac2:(tb__ "0|0|
S48S99S40Vm;A1S80Va;A3Vm;A2").

Definition rho20f (rho : valuation) (a : word) : valuation := ltac2:(tb__ "0|0|
Sc0Sd8Vrho;Sb9S20Vrho;A1Va;S80A3A2SbcSa4A1Va;A3").

Lemma objs_clear_E20f : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa2A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E20f : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa2A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Lemma node20f_core : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S2fS41A1M2S76S44Sc6S15R6R5Sa2S30G2S6bR3S6cR2R1A2A4A5S6fVm;VB;R7R6R4R2A6S1Vok;S30G2S6bR5S6cR4R3A2A4A1S70S71S15S30G2S6bR6S6cR5R4A2A4R1A3S70S2S5eS15S6fVm;VB;A2Sa5Sa2A1RbRaR1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86RcR1A2RbR2A6A2La;A2A2Lw;R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity.
  assert (HnZ : mmap_nZ n8w = 8192) by reflexivity. assert (Hn : mmap_n n8w = n8w) by reflexivity.
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20f [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 8192) with n8w in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as [Hsh Hnrw].
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (mmap_none_only_okA segsA ms md _ Hh H222 Hlen Hsh Hnrw)].
  - intros w' Hw.
    destruct (wstep_mmap_none_invA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold refuse, enomem_ret. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. rewrite G0, G1 in Hpl. rewrite ?G1, ?G3.
      pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil. rewrite Hn in Pfree.
      assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n8w a).
      { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
      split; [exact Hplm|].
      assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n8w = true) by exact (region_free_app_r _ _ _ _ Pfree).
      pose proof (grant_facts_none_A (Z_to_bv 64 0) md n8w a Hpl ltac:(rewrite Evm; exact Hres)) as [Himg Hmaps]. rewrite HnZ in Himg, Hmaps.
      pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n8w ltac:(rewrite Evm; exact Hband) Pfree ltac:(rewrite Un8; lia)) as HBD.
      rewrite Un8 in HBD.
      pose proof (xshadow_clear_of_disj rho E20f a 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20f
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
      assert (Enr34 : mmap_noreserve_b (Z_to_bv 64 34) = false) by (apply mmap_noreserve_b_34; reflexivity).
      unfold mmap_none_model. rewrite Hn. rewrite (with_mmap_backing_plain (Z_to_bv 64 34) a n8w _ Enr34).
      assert (Hsm1 : smatchA segsA (rho20f rho a) tp (ax_setS E20f (S_after (ax_S E20f) (SVar (Pos.succ N18)) (ss_objs (ax_S E20f)) (Pos.succ (Pos.succ N18))))
                       ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n8w)) (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md))).
      { rewrite <- (with_mmap_backing_plain (Z_to_bv 64 34) a n8w (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md) Enr34).
        eapply (smatchA_after_grant_none segsA rho (rho20f rho a) tp E20f [] ms md [] (mmap_none_vm (m_vmmaps md) n8w a) (Z_to_bv 64 34) a n8w a
                  (SVar (Pos.succ N18)) (Pos.succ (Pos.succ N18)) Hsp).
        -- unfold mmap_none_vm. rewrite Hn. reflexivity.
        -- unfold mmap_none_vm. rewrite Hn. reflexivity.
        -- reflexivity.
        -- exact Pal.
        -- rewrite Un8. reflexivity.
        -- rewrite Un8. lia.
        -- rewrite Un8. rewrite Evm in Pceil. unfold TOP in TB. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A'. rewrite Un8 in Hz. exact (Himg z Hz).
        -- rewrite Un8. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E20f) a 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20f);
             [lia | rewrite Evm in Pceil; exact Pceil | exact HSP | exact Himg | intros i sz [] | exact Ho].
        -- rewrite Un8. exact HXb.
        -- unfold rho20f. rewrite Hnx. apply agree_below_set_rw. lia.
        -- rewrite Hnx. lia.
        -- cbn. apply Pos.ltb_lt. lia.
        -- unfold rho20f. cbn [eval]. apply rho_set_rw_at. }
      assert (HSPA : SPA segsA (KxA (mf_res a) B) (ax_setS E20f (S_after (ax_S E20f) (SVar (Pos.succ N18)) (ss_objs (ax_S E20f)) (Pos.succ (Pos.succ N18)))) (rho20f rho a) tp
                      ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n8w)) (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md))).
      { split; [exact Hsm1|]. cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
        -- unfold mf_res. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- rewrite paid_with_vmmaps.
           pose proof (used_none_cons_le md (mmap_none_vm (m_vmmaps md) n8w a) a n8w (MI_ivs_wf segsA _ _ HMI)
                        ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Un8; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                        ltac:(unfold mmap_none_vm; rewrite Hn; reflexivity) ltac:(unfold mmap_none_vm; rewrite Hn; reflexivity)) as U. lia. }

      unfold S20f, cont.
      change (ax_setS E20f (add_facts F20f (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18)))))
        with (ax_with_facts (ax_setS E20f (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18))))
                (F20f ++ ss_facts (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18))))).
      rewrite app_nil_r. unfold vRES.
      apply SPA_refacts; [exact HSPA | |].
      * cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
        assert (X : (Pos.succ N18 <? Pos.succ (Pos.succ N18))%positive = true) by (apply Pos.ltb_lt; lia).
        apply andb_true_intro. split; [unfold F20f; cbn; rewrite !X; reflexivity|].
        destruct HSPA as [[[W _] _] _]. cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
      * intros HF. apply Forall_app. split; [|exact HF].
        unfold F20f, vRES. cbn [ax_S ax_setS ss_next S_after].
        assert (E1 : rw (rho20f rho a) (Pos.succ N18) = a) by (unfold rho20f; apply rho_set_rw_at).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
        -- change (2 ^ 12) with 4096. split; [lia|exact Pal].
        -- rewrite u64_of_lit by lia. rewrite Evm in Pceil. unfold TOP in TB. lia.
Qed.

Theorem node20f : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S72S15Vok;S5eS15S6fVm;VB;A2M2Sa2R3R2A5S70S2S5eS15G2Sa5Sa2A1R4R3R1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86R5R1A2R4R2A6A2La;A2A2Lw;A4F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (_ & Hecall & _).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall | exact (node20f_core rho tp HSP)].
Qed.

Theorem enode20f_any : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S73S15S5eS15S6fVm;VB;A2M2Sa2R3R2A5S70S2S5eS15G2Sa5Sa2A1R4R3R1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86R5R1A2R4R2A6A2La;A2A2Lw;A3F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. destruct (node20f_core rho tp HSP tr ms md Hsp HK) as [_ HQ]. pose proof HK as (Htr & _ & _). subst tr.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E20f [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R15 in G5. cbn [eval] in Hp, G1, G2, G3, G5.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as [Hsh Hnrw].
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  destruct (mmap_reserve_refusable md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - pose proof (wstep_mmap_none_intro_failA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] Hp Hrf) as W. exists (([] : list event), mkCfg (after_sys ms (errno_ret ENOMEM)) md). exact (conj W (HQ _ W)).
  - destruct (@mmap_none_not_refusable_place (sys_input segsA ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok_none (ms_gpr ms 0) md (ms_gpr ms 1) a) in Hpl.
    pose proof (wstep_mmap_none_intro_okA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] a Hp Hpl) as W. eexists. exact (conj W (HQ _ W)).
Qed.

Hypothesis Hlz : ltac2:(tb__ "0|3|
S31S10Q40M0A1M1G1A2M2S69G2R1S56Vm;A1A3S7Z0SfG0S39G1G1R2A3A2A2F_;Fr;").
Hypothesis Hlim : lazy_in_maps m.

Definition a4 (a : word) : word := Z_to_bv 64 (bv_unsigned a + 4096).
Definition mf_exp (a : word) : Model := ltac2:(tb__ "0|0|
Sc3S7eVa;A1S8bVa;A1S82A3").

Lemma objs_clear_E21f : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa3A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E21f : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa3A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma mf_res_vmmaps : ltac2:(tb__ "0|0|
S10Q40A1S0S4dS40S7eR1A1A1S99S40Vm;A1S80R1A3A3Fa;").
Proof. intros a. unfold mf_res. apply m_vmmaps_with_vmmaps. Qed.

Lemma node21f_core : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S2fS41A1M2S76S44Sc6S15RaR9Sa3S30G2S6bR3S6cR2R1A2A4A5S6fS7eR9A1VB;RbRaR4R2A6S1Vok;S30G2S6bR5S6cR4R3A2A4A1S70S71S15S30G2S6bR6S6cR5R4A2A4R1A3S70S2S5eS15S6fS7eRdA1VB;A2Sa5Sa3A1RfReR1A6S5eS15S6fS83RdA1S6VB;Z1000A2A2SaaRfReR1A6A2Lw;R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi, TOP in TB.
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity. assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ8 : mmap_nZ n8w = 8192) by reflexivity. assert (Hn8 : mmap_n n8w = n8w) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ8 in Pceil. rewrite Hn8 in Pfree.
  pose proof (grant_facts_none_A (Z_to_bv 64 0) m n8w a Hpl Hres) as [Himg Hmaps]. rewrite HnZ8 in Himg, Hmaps.
  pose proof (band_clear_of_free _ a n8w Hband Pfree ltac:(rewrite Un8; lia)) as HBD. rewrite Un8 in HBD.
  assert (Ua4 : bv_unsigned (a4 a) = bv_unsigned a + 4096) by (unfold a4; apply u64_of_lit; pose proof (urange a); lia).
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md (mf_res a) Hem) as (Evm & Elz & _ & _). rewrite mf_res_vmmaps in Evm.
  unfold mf_res in Elz. rewrite m_vm_lazy_with_vmmaps in Elz.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E21f [] ms md Hsp) as (G0 & G1 & G2 & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2.
  cbn [eval] in Hp, G0, G1, G2. unfold vRES in G0. cbn [eval] in G0. rewrite Ha in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (Ea4 : ms_gpr ms 0 = a4 a).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096), Ua4 by lia. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). pose proof (urange a). lia. }
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (Hprot : bv_unsigned (ms_gpr ms 2) = 3) by (rewrite G2; reflexivity).
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0).
  { rewrite Ea4, Ua4. unfold page_size in *. replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Pal. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64) by (rewrite Ea4, Ua4, G1, HnZ; unfold two_pow_64 in *; lia).
  assert (Hna : map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_noaccess]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hmp : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  split.
  - eapply (OKPx (mf_res a) B); [exact HK | exact Hp | exact (mprotect_expose_only_okA segsA ms md _ H226 Hprot Halign Hlen Hwrap Hna Hmp)].
  - intros w' Hw.
    destruct (wstep_mprotect_expose_invA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] w' Hp Hw) as [-> | ->].
    + left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold refuse, enomem_ret. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. rewrite Ea4, G1, Hn.
      pose proof (xshadow_clear_of_disj rho E21f (a4 a) 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E21f
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; rewrite Ua4 in Hx; lia)) as [HXb _].

      set (h' := m_vmmaps (mprotect_model_next md (a4 a) pgw)).
      assert (Eh' : h' = mkVmMapsFull (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md))
                           (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw))
                           (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))).
      { unfold h', mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity. }
      assert (Emodel : mprotect_model_next md (a4 a) pgw = with_vmmaps h' md).
      { unfold h', mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity. }
      assert (Hforget : vm_forget_range (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (with_vmmaps h' md) = with_vmmaps h' md).
      { apply vm_forget_range_noop.
        - rewrite Upg. lia.
        - rewrite m_vm_lazy_with_vmmaps, Elz. intros r Hr. split; [exact (Hlz r Hr)|].
          destruct r as [lb ls]. cbn [fst snd]. pose proof (Hlz _ Hr) as Hpos. cbn [snd] in Hpos.
          destruct (Hlim lb ls Hr Hpos) as (b & s0 & Hbin & Hb1 & Hb2).
          pose proof (Hmaps b s0 Hbin) as D. rewrite Ua4, Upg.

          destruct (Z.le_gt_cases (bv_unsigned lb + bv_unsigned ls) (bv_unsigned a + 4096)) as [L|L]; [left; exact L|].
          destruct (Z.le_gt_cases (bv_unsigned a + 4096 + 4096) (bv_unsigned lb)) as [R|R]; [right; exact R|].
          exfalso. pose proof (urange ls).
          destruct (Z.le_gt_cases (bv_unsigned lb) (bv_unsigned a + 4096)) as [C|C].
          * apply (D (bv_unsigned a + 4096)); lia.
          * apply (D (bv_unsigned lb)); lia.
        - rewrite m_vm_materialized_with_vmmaps. intros p Hpm Hin.
          pose proof HMI as (_ & _ & _ & Hsub & _). pose proof (Hsub p Hpm) as Htp_p.
          destruct (Htp p Htp_p) as (_ & b & s0 & Hbin & Hb1 & Hb2). rewrite Ua4, Upg in Hin.
          apply (Hmaps b s0 Hbin (bv_unsigned p)); unfold page_size in *; lia. }
      assert (HOV : overlap_sum (vm_maps (m_vmmaps md)) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) <= bv_unsigned pgw).
      { rewrite Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps].
        match goal with |- overlap_sum (?r :: ?rest) _ _ <= _ => change (r :: rest) with ([] ++ r :: rest) end.
        apply overlap_sum_split_le. cbn [app]. apply (region_free_shrink _ a n8w); [exact (region_free_app_r _ _ _ _ Pfree) | rewrite Ua4; lia | rewrite Ua4, Upg, Un8; lia]. }
      rewrite Emodel, <- Hforget.
      assert (Hsm1 : smatchA segsA rho tp (ax_setS E21f (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [mkObj (SAlu ALU_ADD vRES (SLit 4096)) (SLit 0) (SLit (bv_unsigned pgw)) [] DZero]) (ss_next (ax_S E21f))))
                       ([], mkCfg (after_sys_mem ms (Z_to_bv 64 0) (zero_range (ms_mem ms) (a4 a) pgw))
                                  (vm_forget_range (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (with_vmmaps h' md)))).
      { eapply (smatchA_after_commit_obj segsA rho rho tp E21f [] ms md [] h' (a4 a) pgw (Z_to_bv 64 0) (SLit 0) (SAlu ALU_ADD vRES (SLit 4096)) (ss_next (ax_S E21f)) Hsp).
        -- rewrite Eh'. reflexivity.
        -- rewrite Eh'. reflexivity.
        -- rewrite Eh'. reflexivity.
        -- exact Halign || (rewrite <- Ea4; exact Halign).
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. lia.
        -- rewrite Ua4, Upg. unfold two_pow_64 in *. lia.
        -- exact HOV.
        -- unfold headroom. rewrite Evm, Upg. unfold mmap_none_vm. cbn [vm_limit]. lia.
        -- intros x Hx. apply (grant_no_ro_A (a4 a) 4096); [| rewrite Upg in Hx; exact Hx]. intros z Hz. apply Himg. rewrite Ua4 in Hz. lia.
        -- rewrite Upg. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E21f) (a4 a) 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E21f);
             [lia | unfold TOP; rewrite Ua4; lia | exact HSP | intros x Hx; apply Himg; rewrite Ua4 in Hx; lia | intros e sz [] | exact Ho].
        -- rewrite Upg. exact HXb.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold vRES. cbn [eval]. rewrite Ha. symmetry. rewrite <- Ea4. exact G0. }
      split.
      * unfold S21f, cont. rewrite Hforget.
        replace (ax_setS E21f (add_facts [] (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [O_area_f]) (Pos.succ (Pos.succ N18)))))
          with (ax_setS E21f (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [mkObj (SAlu ALU_ADD vRES (SLit 4096)) (SLit 0) (SLit (bv_unsigned pgw)) [] DZero]) (ss_next (ax_S E21f))));
          [rewrite <- Hforget; exact Hsm1|].
        rewrite Hnx, Upg. reflexivity.
      * cbn [cfg_model w_cfg w_tr fst snd]. rewrite Hforget. split; [reflexivity|]. split.
        -- unfold mf_exp. rewrite (Emodel) || idtac.
           unfold mprotect_model_next. unfold h'. unfold mprotect_model_next. rewrite !m_vmmaps_with_vmmaps.
           rewrite mf_res_vmmaps, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- rewrite paid_with_vmmaps.
           pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs.
           pose proof (used_commit_le md h' (a4 a) pgw Hivs ltac:(rewrite Eh'; reflexivity) ltac:(rewrite Eh'; reflexivity)) as UC.
           rewrite Hforget in UC. rewrite Upg in UC, HOV. lia.
Qed.

Theorem node21f : ltac2:(tb__ "0|2|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S72S15Vok;S5eS15S6fS7eR5A1VB;A2Sa3R7R6A5S70S2S5eS15S6fS7eR6A1VB;A2Sa5Sa3A1R8R7R1A6S5eS15S6fS83R6A1S6VB;Z1000A2A2SaaR8R7R1A6A2Lw;A4F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (_ & Hecall & _).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall | exact (node21f_core rho tp a Ha HSP Hpl Htp)].
Qed.

Theorem enode21f_any : ltac2:(tb__ "0|2|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S73S15S5eS15S6fS7eR5A1VB;A2Sa3R7R6A5S70S2S5eS15S6fS7eR6A1VB;A2Sa5Sa3A1R8R7R1A6S5eS15S6fS83R6A1S6VB;Z1000A2A2SaaR8R7R1A6A2Lw;A3F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & Hnx).
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity. assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ8 : mmap_nZ n8w = 8192) by reflexivity. assert (Hn8 : mmap_n n8w = n8w) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi, TOP in TB.
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ8 in Pceil. rewrite Hn8 in Pfree.
  assert (Ua4 : bv_unsigned (a4 a) = bv_unsigned a + 4096) by (unfold a4; apply u64_of_lit; pose proof (urange a); lia).
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. destruct (node21f_core rho tp a Ha HSP Hpl Htp tr ms md Hsp HK) as [_ HQ].
  pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md (mf_res a) Hem) as (Evm & _ & _ & _). rewrite mf_res_vmmaps in Evm.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E21f [] ms md Hsp) as (G0 & G1 & G2 & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2.
  cbn [eval] in Hp, G0, G1, G2. unfold vRES in G0. cbn [eval] in G0. rewrite Ha in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (Ea4 : ms_gpr ms 0 = a4 a).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096), Ua4 by lia. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). pose proof (urange a). lia. }
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (Hprot : bv_unsigned (ms_gpr ms 2) = 3) by (rewrite G2; reflexivity).
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0).
  { rewrite Ea4, Ua4. unfold page_size in *. replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Pal. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64).
  { rewrite Ea4, Ua4, G1, HnZ; unfold two_pow_64 in *; lia. }
  assert (Hna : map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_noaccess]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hmp : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  destruct (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))) eqn:Hb.
  - pose proof (wstep_mprotect_expose_intro_okA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] Hp Hb) as W. eexists. exact (conj W (HQ _ W)).
  - pose proof (wstep_mprotect_expose_intro_failA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] Hp Hb) as W. eexists. exact (conj W (HQ _ W)).
Qed.

Lemma xwordsZ_clear_of_disj : ltac2:(tb__ "0|5|
S18S64S13S13S13S13S0S2fS31S16S16A2M0A1S65R5A1S91A3S0S16S63R6A1S1bSd2A1A3S7aS17S1fR8A1S1cS62R7A1A1A3S17S69S17R1S90A3S69S17R2S1cS62RaA1A1A3F_;Ff;S5R6Z10006fdf0000A2S5Z10007fff8000S6R7R6A2A2S13S1S5RbR1A2S7R1RaA2A2S3S1S5RaR2A2S7R2S6RaR9A2A2A2A1F_;Fx;G0S13S13S69G0R3S65RfA1A3S1S5SfQ40M1S1aR11S3aS16S16R4A3A2A2M2R3A2S7R3S6G2SfG1S1aR11S39S16S16R4A3A2A2A2A2A2S1S5Z0R3A2S7R3Z8M3A2A2S3S1S5R11S6SdS8S6SfG1S1aR13S63R12A1A2A2S8R5G3A2A2G3A2G3A2R4A2M4A2S7G4R10A2A2A1F_;F_;F_;Fj;Fy;Frr;F_;F_;F_;F_;F_;F_;F_;FsZ;FbZ;Fhi;Flo;FA;Frho;").
Proof.
  clear. intros rho A lo hi bZ sZ HX Hb HF Hin Hb1 Hb2 Hdisj. rewrite HX, Hb.
  assert (F1 : holds rho (SPUle (SLit 0x7fff7f000000) vXB)) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F2 : holds rho (SPUle (SAlu ALU_ADD vXB vXL) (SLit (2 ^ 47)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F3 : holds rho (SPUle vXL (SLit (2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F4 : holds rho (SPUle vXB (SLit (2 ^ 48)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  cbn [holds eval] in F1, F2, F3, F4. unfold vXB, vXL in F1, F2, F3, F4. cbn [eval] in F1, F2, F3, F4.
  rewrite (u64_of_lit 0x7fff7f000000) in F1 by lia. rewrite (u64_of_lit (2 ^ 47)) in F2 by lia.
  rewrite (u64_of_lit (2 ^ 40)) in F3 by lia. rewrite (u64_of_lit (2 ^ 48)) in F4 by lia.
  unfold alu64, alu in F2. rewrite bv_add_unsigned in F2.
  rewrite bv_wrap_small in F2 by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange (rw rho 52)); pose proof (urange (rw rho 53)); lia).
  cbn [eval]. unfold SHB. rewrite (u64_of_lit 0x7fff8000) by lia.
  intros rr y j [<-|[]] Hy Hj. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
  assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
  change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
  pose proof (Z.div_mod (2147450880 + y / 8) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (2147450880 + y / 8) 8 ltac:(lia)) as M.
  assert ((2147450880 + y / 8) / 8 <= 17594333495295 / 8) by (apply Z.div_le_mono; lia).
  change (17594333495295 / 8) with 2199291686911 in H.
  intros Hc. apply (Hdisj ((2147450880 + y / 8) / 8 * 8 + j)); lia.
Qed.

Lemma objs_clear_U24 : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62SabA1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_U24 : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62SabA1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Theorem carve24 : ltac2:(tb__ "0|7|
S5fS18S2fS10Q40M0A1M1A1S70S0G1S19R3Sa4A2S7cA3S5S6S7dZ2000A2M2S7bA2S5S6S7bS8fA2SfG0S19R5PaA2A2A2S0S32S47S37S31G1G1A2S43S40Vm;A1M3A1S42G3A1A3S7cS85A3S33A3G1S1S5S6S7dZ1000A2SfG0R1A2M4A2S7G4G2A2A2S0S35S10Q8M5A1M6A1S20R9R2A2S36G6S11G5Z0A2A2A3F_;Fa;S5eS15R9SabR8R7R6A6S5eS15RaSb2R9R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FJ;").
Proof using Hlo Hhi Htop Hband.
  clear Hres Hsb Hal HB Hlz Hlim.
  intros J rho tp [tr [ms md]] HN18 Hceil HSP Hfree3 Hz HS. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof (SPA_facts_hold segsA J rho U24 tp _ HS) as HF.
  unfold U24c.
  apply (SPA_carve_zero segsA J rho U24 tp tr ms md (SAlu ALU_ADD vBRK (SLit 4096)) 0 4096 (ss_next (ax_S U24)) HS);
    unfold vBRK; cbn [eval]; rewrite ?HN18; unfold alu64, alu; rewrite ?bv_add_unsigned, ?(u64_of_lit 4096) by lia;
    rewrite ?bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold brk0 in *; lia).
  - exact (proj1 U24c_wf).
  - apply Pos.le_refl.
  - lia. - lia. - lia.
  - unfold brk0 in *; lia.
  - unfold brk0 in *; lia.
  - apply Forall_forall. intros o Ho.
    replace (bv_unsigned brk0w + 4096 + 0) with (bv_unsigned (a4 brk0w)) by (unfold a4; rewrite u64_of_lit; unfold brk0 in *; lia).
    replace (bv_unsigned brk0w + 4096 + 4096) with (bv_unsigned (a4 brk0w) + 4096) by (unfold a4; rewrite u64_of_lit; unfold brk0 in *; lia).
    apply (objs_clear_M_sound rho [] (ax_S U24) (a4 brk0w) 4096 TOP HF objs_clear_U24); [lia | | exact HSP | | intros e sz [] | exact Ho];
      unfold a4; rewrite u64_of_lit by (unfold brk0 in *; lia); unfold brk0 in *; [lia|]. intros x Hx. lia.
  - intros z Hzr. apply Hz. rewrite u64_of_lit by (unfold brk0 in *; lia). unfold brk0. lia.
  - apply (xwordsZ_clear_of_disj rho U24 _ _ SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl HF facts_M_in_U24);
      [unfold SHADOW_BAND_LO; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia |].
    intros x Hx. apply HBD. unfold brk0 in *. lia.
Qed.

End Malloc40.
End MuslMalloc40Nodes.

(* [comment removed for export] *)
Module Drv_printf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sv"; "mkCell"; "mkObj"; "sobj"; "DUnknown"; "sprop"; "DImage"; "SVar"; "FcsrFrm0"; "mkSS"; "SAlu"; "SPUle"; "valuation"; "SPAlign"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "nat"; "pair"; "true"; "None"; "false"; "list"; "prod"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "post_regs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "opp"; "sub"; "pow"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "fcell"; "bcell"; "FUELP"; "Pre_pf"; "kok"; "vcuts_pf"; "vexits_pf"; "P_pf"; "X_pf"; "facts_pf"; "objs_pf"; "O_file_after"; "O_sbuf_after"; "Posts_pf"; "add"; "ms16"; "regs_pf"; "O_cflag"; "O_file0"; "O_pwin"; "O_realm"; "O_realv"; "O_rtc2"; "O_rtc3w"; "O_sbsh"; "O_sbuf0"; "O_ssp"; "file_cells_after"; "post_regs_pf"; "sbuf_cells_after"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "SBUF"; "FILE"; "PW"; "emit_entry"; "STDIO_WRITE"; "emit_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PFAddr.
  Definition emit_entry : Z := 0x8c7e8.
  Definition emit_ret : Z := 0x8c82c.
  Definition FMT : Z := 0x14d8b.
  Definition FILE : Z := 0xec350.
  Definition SBUF : Z := 0x644cc8.
  Definition LOWPG : Z := 0x800bc000.
  Definition STDIO_WRITE : Z := 0xd9a4c.
  Definition PW : Z := 12288.
End PFAddr.
Import PFAddr.

Definition add (a b : sv) : sv := SAlu ALU_ADD a b.

Definition O_pwin : sobj := ltac2:(tb__ "0|0|
S4S9PaA1S0S2aS50A1A1S0Z0A1S13S1A1S6A5").
Definition fcell (off : Z) (w : Z) (v : Z) : cell := ltac2:(tb__ "0|0|
S3S0S28S4fVoff;A2A1Vw;S0Vv;A1A3").

Definition file_cells_after (n : Z) : list cell := ltac2:(tb__ "0|6|
S12S1S2eZ0M0Z4M1Z5A3S12S1S2eZ28Z8M2S28S4eS2dZ2M3S2bVn;Z1M4A2A2A2A3S12S1S2eZ38G2S4eA3S12S1S2eZ20G2S28S4eZ400A2A3S12S1S2eZ90G1S2bS2cG3Z40A2G4A2M5A3S12S1S2eZ48G2S52A3S12S1S2eZ10G2G0A3S12S1S2eG2G2G0A3S12S1S2eZ88G1G5A3S13S1A1A3A3A3A3A3A3A3A3A3").
Definition O_file_after (n : Z) : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4fA1S0S28S4fZe8A2A1S49Vn;A1S8A5").
Definition bcell (off : Z) (v : Z) : cell := ltac2:(tb__ "0|0|
S3S0S28S4eVoff;A2A1Z1S0Vv;A1A3").

Definition sbuf_cells_after (n : Z) : list cell := ltac2:(tb__ "0|9|
S14S1aS1A1L_;M0S29Vn;Z1M1A2S12S1S2fZ0Z30M2A2S13S1A1A3M3G0S29Vn;Z2M4A2S12S1S2fG1ZaM5A2G3A3M6G0S29Vn;Z3M7A2S12S1S2fG7G5A2S12S1S2fG4G2A2G6A3A3M8S12S1S2fZ5G5A2S12S1S2fZ4G2A2G8A3A3X14x2X14x2X14x2").
Definition O_sbuf_after (n : Z) : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4eA1S0S28S4eZ400A2A1S4bVn;A1S6A5").

Definition O_file0 : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4fA1S0S28S4fZe8A2A1S13S1A1S8A5").
Definition O_sbuf0 : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4eA1S0S28S4eZ400A2A1S13S1A1S6A5").

Definition O_sbsh : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1M0S0Z800c0998A1M1S0Z800c09a8A1S12S1S3G1Z8M2G0A3S12S1S3S0Z800c09a0A1G2G0A3S13S1A1A3A3S6A5").

Definition O_rtc3w : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1S0Zf20d8A1M0S0Zf20daA1S12S1S3G0Z1M1S0G1A1M2A3S12S1S3S0Zf20d9A1G1G2A3S13S1A1A3A3S6A5").

Definition O_rtc2 : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1M0S0Zf20e0A1M1S0Zf20f8A1S12S1S3G1Z8M2S0Z7fffffffffffA1A3S12S1S3S0Zf20e8A1G2G0A3S12S1S3S0Zf20f0A1G2G0A3S13S1A1A3A3A3S6A5").

Definition O_cflag : sobj := ltac2:(tb__ "0|1|
S4S0Z0A1S0Z182f78A1M0S0Z182f80A1S12S1S3G0Z8S0Z100000000A1A3S13S1A1A3S8A5").
Definition O_realv : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0Ze99d8A1S0Ze99e8A1S13S1A1S8A5").
Definition O_realm : sobj := ltac2:(tb__ "0|2|
S4S0Z0A1S0Ze9ae8A1M0S0Ze9af8A1S12S1S3G0Z8M1S0Zddf74A1A3S12S1S3S0Ze9af0A1G1S0Zde378A1A3S13S1A1A3A3S6A5").

Definition O_ssp : sobj := ltac2:(tb__ "0|1|
S4S0Z0A1S0Z6445f8A1M0S0Z644600A1S12S1S3G0Z8S9PfA1A3S13S1A1A3S8A5").
Definition objs_pf (ofile osbuf : sobj) : list sobj := ltac2:(tb__ "0|0|
S1cS5S12S5S41S12S5Vofile;S12S5Vosbuf;S12S5S46S12S5S45S12S5S44S12S5S3fS12S5S43S12S5S42S12S5S48S13S5A1A3A3A3A3A3A3A3A3A3A3S21A3").

Definition X_pf : list (sv * sv) := ltac2:(tb__ "0|1|
S12S1bS2S2A2M0S16S2S2S0Z14d40A1S0Z80A1A4S12G0S16S2S2S3cS9PaA1S0S2aS50A1A1A2S0S50A1A4S13G0A1A3A3").

Definition ms16 (d : Z) : sprop := ltac2:(tb__ "0|0|
S11S10S60ScS5eScS5fS0Z28A1S3cS9PaA1S0S2aVd;A1A1A2A3S0ZfA1A3S0Z0A1A3A1").
Definition facts_pf : list sprop := ltac2:(tb__ "0|2|
S12S7SfPaM0Z4A2S12S7SdS0S28S20Z10000A2A1S9G0A1M1A2S12S7SdG1S0S2bS2cZ2Z2fA2Z10A2A1A2S12S7S3dZ958A1S12S7S3dZ928A1S13S7A1A3A3A3A3A3").

Definition regs_pf : list sv := ltac2:(tb__ "0|1|
S24S27S12S1bS15S2A2M0S16S15S2U3S0Z10800A1A4S12G0S16S15S2UbS0Z0A1A4S13G0A1A3A3A2").

Definition Pre_pf0 : axst := ltac2:(tb__ "0|0|
S1fSbS51S3eS23SaS18S2A1S38S40S47A2S37S22S19A9S36A2").

Definition Pre_pf (k : Z) : axst := ltac2:(tb__ "0|0|
S1fSbS51S3eS23SaS18S2A1S38S39Vk;A1S3aVk;A1A2S37S22S19A9S36A2").
Definition post_regs_pf : list sv := ltac2:(tb__ "0|1|
S24S26S22A1S12S1bS15S2A2M0S16S15S2U3S0Z10800A1A4S13G0A1A3A2").
Definition P_pf (k : Z) : axst := ltac2:(tb__ "0|1|
S1fSbS53S4aS23SaS18S2A1S38S39S28Vk;Z1A2M0A1S3aG0A1A2S37S25S19A9S36A2").
Definition Posts_pf (k : Z) : list leafA := ltac2:(tb__ "0|0|
S12S59S5aS35Vk;A1S63A2S13S59A1A3").

Definition FUELP : nat := 8000%nat.
Definition vcuts_pf (k : Z) : list vnodeA := ltac2:(tb__ "0|0|
S12S54S55S31Vk;A1Z1S0Z0A1A3S13S54A1A3").
Definition vexits_pf (k : Z) : list vnodeA := ltac2:(tb__ "0|1|
S12S54S55S35Vk;A1Z0M0S0G0A1A3S13S54A1A3").
Lemma echeck_pf1 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z1M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_pf2 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z2M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_pf3 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z3M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition kok (k : Z) : Prop := ltac2:(tb__ "0|0|
S4dS4cS1dVk;Z1A3S4dS4cS1dVk;Z2A3S4cS1dVk;Z3A3A2A2").
Lemma echeck_pf : ltac2:(tb__ "0|0|
S1dS32R1A1S4cS14S57S1eS30S13S1dA1S22S33R2A1S34R2A1A6S17A3F_;Fk;").
Proof. intros k [->|[->| ->]]; [exact echeck_pf1 | exact echeck_pf2 | exact echeck_pf3]. Qed.
Lemma check_pf : ltac2:(tb__ "0|1|
S1dS32R1A1S4cS14S56S1eS30S13S1dA1S22S12S58S31R2A1S13S58A1M0A3S12S58S35R2A1G0A3A6S17A3F_;Fk;").
Proof. intros k Hk. exact (check_cfgA_of_ecfgIA segs FUELP [] NF (vcuts_pf k) (vexits_pf k) [Pre_pf k] [P_pf k] eq_refl eq_refl (echeck_pf k Hk)). Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem printf_sum : ltac2:(tb__ "0|0|
S1dSeS1aS5dQ40A1A1S32R3A1S62S1eVok;S5cS1eVJ;S31R4A1R3R2A5S5bS1eVJ;S22R3R2S3bR4A1A6A4F_;Ftp;Frho;Fk;").
Proof.
  intros k rho tp Hk.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (Pre_pf k) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELP [] NF [Pre_pf k] [P_pf k] (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp (Posts_pf k)) tp HokG HstG (check_pf k Hk)); [|left; reflexivity].
  intros E rhoE [<-|[]]. apply exit_postA. left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.

Theorem printf_sum_ex : ltac2:(tb__ "0|0|
S1dSeS1aS5dQ40A1A1S32R3A1S61S1eS5cS1eVJ;S31R4A1R3R2A5S5bS1eVJ;S22R3R2S3bR4A1A6A3F_;Ftp;Frho;Fk;").
Proof.
  intros k rho tp Hk.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (Pre_pf k) rho tp w Hw) | intros w Hw; exact Hw |].
  change (Pre_pf k) with (vna_state (mkVNA (Pre_pf k) 1 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELP [] NF (vcuts_pf k) (vexits_pf k) (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp (Posts_pf k)) tp HstG); [ | exact (echeck_pf k Hk) | | left; reflexivity].
  { intros m [<-|[]]. cbv; congruence. }
  intros E rhoE [<-|[]].
  apply (eexit_post_IA0 segs J NF rho (vcuts_pf k) (Posts_pf k) (mkVNA (P_pf k) 0 (SLit 0))). left; reflexivity.
Qed.
End SumEx.
End Drv_printf.

(* [comment removed for export] *)
Module Icpt_region.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "bool"; "true"; "prod"; "andb"; "None"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "SPUle"; "cell"; "SPUlt"; "sobj"; "mkCell"; "SPAlign"; "FcsrFrm0"; "SPEq"; "mkSS"; "DUnknown"; "SAlu"; "mkObj"; "SPBranch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "cur"; "shp"; "add"; "gd"; "gu"; "pae"; "vB"; "pab"; "vL"; "F_ae"; "miz_regs"; "miz_state"; "shpk"; "F_ab"; "cnt"; "g8"; "vN"; "E_Ee"; "E_Pe"; "E_We"; "beg"; "s_Ee"; "s_Pe"; "s_We"; "CE_0"; "CP_0"; "CW_0"; "E_Eb"; "E_Pb"; "E_Wb"; "O_rtc2"; "O_stk"; "X_rip"; "base_facts"; "endd"; "stk_cells"; "C0"; "CE"; "CP"; "CW"; "FUEL"; "P_ret"; "RA_MIZ"; "cutpcs_rip"; "g_facts"; "s_Eb"; "s_Pb"; "s_Wb"; "vO"; "F_E"; "F_P"; "F_W"; "KHME"; "cuts_rip"; "exits_rip"; "lastt"; "regs_C0"; "stk_cells8"; "vcuts_rip"; "vexits_rip"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "post_regs"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "miz_epi"; "miz_pro"; "miz_word"; "rip_C0"; "rip_ret"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "segs"; "ACEIL"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module RegionAddr.
  Definition rip_entry : Z := 0x5ff44.
  Definition rip_C0 : Z := 0x60038.
  Definition rip_ret : Z := 0x600e4.
  Definition miz_pro : Z := 0x70278.
  Definition miz_word : Z := 0x70294.
  Definition miz_epi : Z := 0x702b0.
End RegionAddr.
Import RegionAddr.

Definition HSE : Z := 0x10007fff8000.
Definition KHME : Z := 0x7fffffffffff.
Definition M8 : Z := 18446744073709551608.

Definition O_rtc2 : sobj := ltac2:(tb__ "0|3|
S1bSfZ0A1M0SfZf20e0A1M1SfZf20f8A1S0S11S14G1Z8M2SfS51A1A3S0S11S14SfZf20e8A1G2G0A3S0S11S14SfZf20f0A1G2G0A3S3S11A1A3A3A3S19A5").

Definition vB := SVar 15. Definition vL := SVar 16. Definition vO := SVar 17. Definition vN := SVar 18.
Definition gu := SVar 120. Definition gd := SVar 121.
Definition add (a b : sv) : sv := SAlu ALU_ADD a b.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition shp (g : sv) : sv := add g shb.
Definition beg : sv := add vB vO.
Definition endd : sv := add vN beg.
Definition X_rip : list (sv * sv) := ltac2:(tb__ "0|1|
S0S7ScScA2M0S1ScScS23S25A4S3G0A1A3").

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S11S14SfN38A1Z8M0SeP29A1A3S0S11S14SfN30A1G0SeP28A1A3S0S11S14SfN28A1G0SeP27A1A3S0S11S14SfN20A1G0SeP26A1A3S0S11S14SfN18A1G0SeP1dA1A3S0S11S14SfN10A1G0SeP1cA1A3S0S11S14SfN8A1G0SePbA1A3S3S11A1A3A3A3A3A3A3A3").
Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bSePaA1SfN50A1SfZ0A1Vcells;S19A5").

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0SdS10S1fS4dS2dA2S25A2S0SdS10S4dS25A2S0SdS10S2dS25A2S0SdS10S25SfS68Z2M0Z28A2A1A2S0SdS10SfZ1A1S2dA2S0SdS10SfZ1000A1S23A2S0SdS10S1fS23S25A2SfS69S68G0Z2fA2Z8A2A1M1A2S0SdS10S23G1A2S0SdS15PfZ3A2S0SdS15PaM2Z4A2S0SdS10SfS76A1SeG2A1M3A2S0SdS10G3SfS68G0Z3fA2A1A2S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition g_facts : list sprop := ltac2:(tb__ "0|4|
S0SdS10S31S2cS21A1M0A2S0SdS10G0S1fS31SfZ7A1A2A2S0SdS10S2cS20A1M1S3fA2S0SdS10S1fS3fSfN7A1A2G1A2S0SdS10S23G0A2S0SdS10S23G1A2S0SdS10G1S1fS23S25A2A2S0SdS10S21SfS69S68Z2M2Z3dA2Z1A2A1M3A2S0SdS10S20G3A2S0SdS10S20S1fS21SfS68G2Z25A2A1A2A2S3SdA1A3A3A3A3A3A3A3A3A3A3").

Definition regs_C0 : list sv := ltac2:(tb__ "0|1|
S65S66S0S7S2ScA2M0S1S2ScU1SfS70A1A4S0G0S1S2ScU2S1fSePaA1SfN40A1A2A4S0G0S1S2ScU8S31A4S0G0S1S2ScU9S2dA4S0G0S1S2ScUaS1eS20A1A4S0G0S1S2ScU12S3fA4S0G0S1S2ScU13S1eS21A1A4S0G0S1S2ScU14SeP7aA1A4S0G0S1S2ScU15SfZf13f8A1A4S0G0S1S2ScU5SeP7bA1A4S0G0S1S2ScU6SeP7cA1A4S0G0S1S2ScU7SeP7dA1A4S0G0S1S2ScUbSeP7eA1A4S0G0S1S2ScUcSeP7fA1A4S0G0S1S2ScUdSeP80A1A4S0G0S1S2ScUeSeP81A1A4S0G0S1S2ScUfSeP82A1A4S0G0S1S2ScU10SeP83A1A4S0G0S1S2ScU11SeP84A1A4S0G0S1S2ScU1cSeP85A1A4S0G0S1S2ScU1dSeP86A1A4S0G0S1S2ScU1eSeP87A1A4S0G0S1S2ScU1fSeP88A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C0 : axst := ltac2:(tb__ "0|0|
S74S18S70S55S64S16S9ScA1S4S13S0S13S3cS40A1S0S13S3bS3S13A1A3A3S73A3S4SdS49S3eA3P89SaA9S3dA2").

Definition RA_MIZ : Z := 0x600b8.
Definition lastt : sv := add endd (SLit (-1)).
Definition stk_cells8 : list cell := ltac2:(tb__ "0|0|
S0S11S14SfN48A1Z8SfS47A1A3S40A3").
Definition pab := SVar 140. Definition pae := SVar 141. Definition cur := SVar 142. Definition cnt := SVar 143.
Definition shpk (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S1fVg;SfS6aS77Vk;A2A1A2").

Definition miz_regs (a0 a2 a3 a4 a5 a6 : sv) : list sv := ltac2:(tb__ "0|1|
S65S66S0S7S2ScA2M0S1S2ScU1SfS47A1A4S0G0S1S2ScU2S1fSePaA1SfN50A1A2A4S0G0S1S2ScU5SeP7bA1A4S0G0S1S2ScU6SeP7cA1A4S0G0S1S2ScU7SeP7dA1A4S0G0S1S2ScU8S31A4S0G0S1S2ScU9S2dA4S0G0S1S2ScUaVa0;A4S0G0S1S2ScUbSfZ0A1A4S0G0S1S2ScUcVa2;A4S0G0S1S2ScUdVa3;A4S0G0S1S2ScUeVa4;A4S0G0S1S2ScUfVa5;A4S0G0S1S2ScU10Va6;A4S0G0S1S2ScU11SeP84A1A4S0G0S1S2ScU12S54A4S0G0S1S2ScU13S1eS21A1A4S0G0S1S2ScU14SeP7aA1A4S0G0S1S2ScU15SfZf13f8A1A4S0G0S1S2ScU1cSeP85A1A4S0G0S1S2ScU1dSeP86A1A4S0G0S1S2ScU1eSeP87A1A4S0G0S1S2ScU1fSeP88A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition miz_state (pc : Z) (regs : list sv) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S74S18Vpc;Vregs;S64S16S9ScA1S4S13S0S13S3cS56A1S0S13S3bS3S13A1A3A3S73A3S4SdVfacts;S4SdS49S3eA3A3Vnx;SaA9S3dA2").

Definition F_ab : list sprop := ltac2:(tb__ "0|2|
S0SdS10S24S1fS21SfZ7A1M0A2M1A2S0SdS10G1S1fS24G0A2A2S0SdS15P8cZ3A2S3SdA1A3A3A3").
Definition F_ae : list sprop := ltac2:(tb__ "0|0|
S0SdS10S22S20A2S0SdS10S20S1fS22SfZ7A1A2A2S0SdS15P8dZ3A2S3SdA1A3A3A3").

Definition CW_0 : axst := ltac2:(tb__ "0|0|
S28S6fS27S1eS21A1S1eS22A1SeP90A1S1eS20A1S1eS1dA1SeP91A1A6S4SdS2aS26A3P96A4").
Definition F_W : list sprop := ltac2:(tb__ "0|1|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ40A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1A2A1A2S0SdS10S21S1dA2S0SdS12S1dS22A2S0SdS15P8eZ3A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3A3").
Definition CW : axst := ax_add_facts F_W CW_0.

Definition CP_0 : axst := ltac2:(tb__ "0|0|
S28S6eS27S1eS21A1S1eS22A1S29S1dZ1A2S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS26A3P96A4").
Definition F_P : list sprop := ltac2:(tb__ "0|1|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ8A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1A2A1A2S0SdS10S21S1dA2S0SdS12S1dS24A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3").
Definition CP : axst := ax_add_facts F_P CP_0.

Definition CE_0 : axst := ltac2:(tb__ "0|0|
S28S6dS27SeP93A1S1eS1dA1SeP90A1S2bSeP92A1SeP91A1A6S26P96A4").
Definition F_E : list sprop := ltac2:(tb__ "0|3|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ8A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1M1A2A1A2S0SdS10S1fS1dS2bA2M2S20A2S0SdS10S20G2A2S0SdS10SfG1A1S2bA2S0SdS10S2bSfZ7A1A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3A3A3").
Definition CE : axst := ax_add_facts F_E CE_0.

Definition P_ret : axst := ltac2:(tb__ "0|1|
S74S18S71S65S67S63A1S0S7S2ScA2M0S1S2ScUaSfZ0A1A4S3G0A1A3A2S64S16S9ScA1S4S13S0S13S3cS40A1S0S13S3bS3S13A1A3A3S73A3S3eP8cSaA9S3dA2").

Definition E_Pe : axst := ltac2:(tb__ "0|0|
S28S6eS27S1eS21A1S1eS22A1S29S21Z1A2S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS4SdS26S0SdS12S21S20A2S0SdS12S21S24A2S3SdA1A3A3A3A3P96A4").
Definition E_Pb : axst := ltac2:(tb__ "0|2|
S28S6eS27S1eS21A1S1eS22A1S29S1dZ2A2S1eS20A1S1eS24A1S29S1dZ1M0A2A6S4SdS4fS4SdS2aS4SdS26S0SdS12S1fS1dSfG0A1A2M1S24A2S0SdS12G1S20A2S3SdA1A3A3A3A3A3P96A4").
Definition E_We : axst := ltac2:(tb__ "0|0|
S28S6fS27S1eS21A1S1eS22A1SeP90A1S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS4SdS26S0SdS12S24S22A2S3SdA1A3A3A3P96A4").
Definition E_Wb : axst := ltac2:(tb__ "0|1|
S28S6fS27S1eS21A1S1eS22A1SfZ0A1S1eS20A1S29S1dZ8M0A2SeP91A1A6S4SdS50S4SdS2aS4SdS26S0SdS12S1fS1dSfG0A1A2S22A2S3SdA1A3A3A3A3P96A4").
Definition E_Ee : axst := ltac2:(tb__ "0|1|
S28S6dS27SeP93A1S1eS22A1M0SeP90A1S1aS79S1eS20A1G0A3SeP92A1SeP91A1A6S4SdS26S0SdS12S22S20A2S0SdS10S21S22A2S3SdA1A3A3A3P96A4").
Definition E_Eb : axst := ltac2:(tb__ "0|2|
S28S6dS27SfZ0A1M0S29S1dZ1A2SeP90A1S1fS2bSfN1A1A2M1SeP92A1SeP91A1A6S4SdS4eS4SdS26S0SdS1cS7aG1G0A3S3SdA1A3A3A3P96A4").

Definition cuts_rip : list axst := ltac2:(tb__ "0|0|
S0S60S41S0S60S43S0S60S44S0S60S42S3S60A1A3A3A3A3").
Definition exits_rip : list axst := ltac2:(tb__ "0|0|
S0S60S46S0S60S2fS0S60S39S0S60S30S0S60S3aS0S60S2eS0S60S38S3S60A1A3A3A3A3A3A3A3").
Definition cutpcs_rip : list Z := ltac2:(tb__ "0|0|
S0S5aS6eS0S5aS6fS0S5aS6dS3S5aA1A3A3A3").
Definition FUEL : nat := 400%nat.

Definition vcuts_rip : list vnodeA := ltac2:(tb__ "0|0|
S0S5dS5eS41Z32SfZ0A1A3S0S5dS5eS43Z1eS1dA3S0S5dS5eS44Z14S1dA3S0S5dS5eS42ZaS1fS1dSfZ8A1A2A3S3S5dA1A3A3A3A3").
Definition vexits_rip : list vnodeA := ltac2:(tb__ "0|4|
S0S5dS5eS46Z0SfS69S68Z2Z40A2Z1M0A2A1A3S0S5dS5eS2fZ1fM1S21A3S0S5dS5eS39G1S1fS1dSfG0A1A2A3S0S5dS5eS30Z15M2S24A3S0S5dS5eS3aG2S1fS1dSfZ8A1A2A3S0S5dS5eS2eZbM3S20A3S0S5dS5eS38G3S1fS1dSfZ9A1A2A3S3S5dA1A3A3A3A3A3A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
Lemma echeck_rip : ltac2:(tb__ "0|0|
S5bS5S7bS75S45S48S63S57S58A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_rip : ltac2:(tb__ "0|0|
S5bS5S5fS75S45S48S63S52S53A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUEL cutpcs_rip NF vcuts_rip vexits_rip cuts_rip exits_rip eq_refl eq_refl echeck_rip). Qed.

Definition s_Pe : wsub := ltac2:(tb__ "0|0|
S78S63S61S2fA1S61S36A1A3").
Definition s_Pb : wsub := ltac2:(tb__ "0|2|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ1M1A1A2A4S0G0S1S59ScP91S29S1dG1A2A4S3G0A1A3A3").
Definition s_We : wsub := ltac2:(tb__ "0|0|
S78S63S61S30A1S61S37A1A3").
Definition s_Wb : wsub := ltac2:(tb__ "0|1|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ8A1A2A4S0G0S1S59ScP90SfZ0A1A4S3G0A1A3A3").
Definition s_Ee : wsub := ltac2:(tb__ "0|0|
S78S63S61S2eA1S61S35A1A3").
Definition s_Eb : wsub := ltac2:(tb__ "0|1|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ1A1A2A4S0G0S1S59ScP8fS1fS2bSfN1A1A2A4S0G0S1S59ScP93SfZ0A1A4S3G0A1A3A3A3").
Lemma ent_Pe : ltac2:(tb__ "0|0|
S5bS5S62S2fS36S33A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Pb : ltac2:(tb__ "0|0|
S5bS5S62S39S36S4bA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_We : ltac2:(tb__ "0|0|
S5bS5S62S30S37S34A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Wb : ltac2:(tb__ "0|0|
S5bS5S62S3aS37S4cA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ee : ltac2:(tb__ "0|0|
S5bS5S62S2eS35S32A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Eb : ltac2:(tb__ "0|0|
S5bS5S62S38S35S4aA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_rip : ltac2:(tb__ "0|0|
S5bS5S8S8S8S8S8S6cS33S63A2S6cS4bS63A2A2S6cS34S63A2A2S6cS4cS63A2A2S6cS32S63A2A2S6cS4aS63A2A2S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma s_Pe_vals : ltac2:(tb__ "0|5|
S5bSbScA1S72S59ScS6bS33A1S0S59P8cM0S0S59P8dM1S0S59P8eS0S59P78M2S0S59P79M3S3S59A1A3A3A3A3A3A4S0ScSeG0A1S0ScSeG1A1S0ScSeG2A1M4S0ScG4S0ScSeG3A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_We_vals : ltac2:(tb__ "0|5|
S5bSbScA1S72S59ScS6bS34A1S0S59P8cM0S0S59P8dM1S0S59P8eS0S59P78M2S0S59P79M3S3S59A1A3A3A3A3A3A4S0ScSeG0A1M4S0ScSeG1A1S0ScG4S0ScSeG2A1S0ScSeG3A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_Ee_vals : ltac2:(tb__ "0|4|
S5bSbScA1S72S59ScS6bS32A1S0S59P8dM0S0S59P8eS0S59P8fS0S59P78M1S0S59P79M2S3S59A1A3A3A3A3A3A4S0ScSeG0A1M3S0ScG3S0ScS1aS79S1eS20A1S1eS22A1A3S0ScSeG1A1S0ScSeG2A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_glob : ltac2:(tb__ "0|1|
S59S7cR1S63A2S5cS5bScS6bS33R2A2SeR2A1M0A3S5cS5bScS6bS34R2A2G0A3S5bScS6bS32R2A2G0A3A2A2F_;Fv;").
Proof.
  intros v Hv. pose proof ids_rip as H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 _].
  repeat split; apply wsub_get_id with (g := NF); assumption.
Qed.
End Icpt_region.

(* [comment removed for export] *)
Module Str_memchrA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "holds"; "SLit"; "valuation"; "SVar"; "SAlu"; "ss_facts"; "rl"; "rw"; "SPUle"; "SPBranch"; "eval"; "SPNot"; "sobj"; "SPEq"; "FcsrFrm0"; "agree_below"; "mkSS"; "sprop_below"; "ss_next"; "DList"; "cell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "bool"; "true"; "list"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "v120"; "mc_state"; "v122"; "tf"; "inv"; "curs"; "r1"; "C3_0"; "BNZ_eq"; "P_ret_0"; "NOZ"; "T_1j"; "T_23"; "T_23w"; "T_b1"; "T_b2"; "T_b3"; "T_f2"; "T_f3"; "s_f2"; "s_f3"; "BNZ_ne"; "BYTE"; "C1_0"; "FirstNul"; "HI"; "Pre_memchr0"; "base_facts"; "c1"; "inc1"; "svals"; "BZ_eq"; "BZ_ne"; "C1M"; "C2_0"; "C84_0"; "O_str"; "X_2"; "X_3e"; "X_3n"; "X_j"; "r8"; "s_1j"; "s_23"; "s_23w"; "s_b1"; "s_b2"; "s_b3"; "C1"; "C2"; "C3"; "C84"; "C84b"; "FUELM"; "Posts_memchr0"; "c8"; "cutpcs_mc"; "inc8"; "C84b_0"; "HZT"; "P_ret"; "WRD"; "cuts_mc"; "exits_mc"; "step1_vals"; "step8_vals"; "vcuts_mc"; "vexits_mc"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "mkLeafA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "two62"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_EQ"; "ALU_SLTU"; "ALU_AND"; "ALU_OR"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA.MCHAddr"; "memchr_ret"; "memchr_L3"; "memchr_J84"; "memchr_L1"; "memchr_L2"; "memchr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA.ZFacts"; "invZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv HasZero StrBytes CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.

Module MCHAddr.
  Definition memchr_entry : Z := 0xdde78.
  Definition memchr_L1 : Z := 0xdde94.
  Definition memchr_J84 : Z := 0xddebc.
  Definition memchr_L2 : Z := 0xddeec.
  Definition memchr_L3 : Z := 0xddf18.
  Definition memchr_ret : Z := 0xddf30.
End MCHAddr.
Import MCHAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUELM : nat := 400%nat.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S17S5PcA1S3Z0A1S5P11A1S1aS16A1S15P3A1A5").
Definition base_facts : list sprop := ltac2:(tb__ "0|6|
S18S1SbS94S5P10A1M0S5PeA1M1A3S18S1SaS6S8dG0S3Z8A1M2A3S5P11A1M3A2S18S1SaG2G3A2S18S1SaG3S3S77A1M4A2S18S1SaG1G4A2S18S1SaS3Z1A1S5PcA1M5A2S18S1SaG5G4A2S1aS1A1A3A3A3A3A3A3A3").
Definition Pre_memchr0 : axst := ltac2:(tb__ "0|1|
S96S12S9dS78S7bS18S1cS19S0A2M0S1bS19S0UbS3Z0A1A4S1aG0A1A3A2S76S10S20S0A1S18SeS47S1aSeA1A3S3eS75S22A9S1aS1cS0S0A2A1A2").

Definition C1M : Z := 72340172838076672.
Definition HI : Z := 9259542123273814144.

Definition v120 : sv := SVar 120.
Definition v122 : sv := SVar 122.
Definition curs (e : sv) : sv := SAlu ALU_ADD (SVar 12) e.
Definition inv (c r : sv) : list sprop := ltac2:(tb__ "0|3|
S18S1SaVc;S5P10A1A2S18S1SaS6S8dVc;S3Z8A1A3S5P11A1A2S18S1SaVc;S3S77A1M0A2S18S1SaS5PeA1M1S6S8dVc;Vr;A3M2A2S18S1SaG2G1A2S18S1SaVr;G0A2S1aS1A1A3A3A3A3A3A3").

Definition mc_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S96S12Vpc;S78S79S75A1S21S1cS19S0A2M0S18G0S1bS19S0UbS3Z0A1A4S1aG0A1A3Vregs;A3A2S76S10S20S0A1S18SeS47S1aSeA1A3S21S1Vfacts;S3eA3Vnx;S22A9S1aS1cS0S0A2A1A2").

Definition C1_0 : axst := ltac2:(tb__ "0|2|
S24S9bS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UfS28S6S8dS23S3Z1A1M1A3A1A4S18G0S1bS19S0U10G1A4S1aG0A1A3A3A3A3S1aS1A1P87A4").
Definition C84_0 : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UeS6S90S3Z0A1S25A3A4S1aG0A1A3A3A3S1aS1A1P87A4").
Definition C2_0 : axst := ltac2:(tb__ "0|1|
S24S9cS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UdS3S44A1A4S18G0S1bS19S0UeS3S3cA1A4S18G0S1bS19S0UfS3Z0A1A4S18G0S1bS19S0U10S3Z7A1A4S1aG0A1A3A3A3A3A3A3S1aS1A1P87A4").
Definition C3_0 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UdS25A4S1aG0A1A3A3S1aS1A1P87A4").

Definition C84b_0 : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UeS3Z1A1A4S1aG0A1A3A3A3S1aS1A1P87A4").
Definition C1 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S3aA2").
Definition C84 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S46A2").
Definition C84b : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S5dA2").
Definition C2 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S45A2").
Definition C3 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S2aA2").

Definition BYTE (e : sv) : sv := SExt false 8 (SLBytes 3 e 1).
Definition WRD (e : sv) : sv := SLBytes 3 e 8.
Definition BZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
SbS8fS39Ve;A1S3Z0A1A3").
Definition BNZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8fS39Ve;A1S3Z0A1A3A1").
Definition BNZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
SbS8eS39Ve;A1S3Z0A1A3").
Definition BZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8eS39Ve;A1S3Z0A1A3A1").
Definition HZT (e : sv) : sv := ltac2:(tb__ "0|1|
S6S91S6S92S6S93S3S44A1S60Ve;A1M0A3G0A3S3S3cA1A3").
Definition NOZ (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8eS5eVe;A1S3S3cA1A3A1").

Definition c1 : sv := ltac2:(tb__ "0|0|
S6S8dS28S23A1S3Z1A1A3").
Definition r1 : sv := SAlu ALU_ADD v122 (SLit (-1)).
Definition c8 : sv := ltac2:(tb__ "0|0|
S6S8dS28S23A1S3Z8A1A3").
Definition r8 : sv := SAlu ALU_ADD v122 (SLit (-8)).
Definition tf (f : sprop) : list sprop := ltac2:(tb__ "0|0|
S18S1Vf;S27S23S25A2A3").

Definition T_b1 : axst := ltac2:(tb__ "0|2|
S24S9bS18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UcS29A4S18G0S1bS19S0UfS6S8dS28S6S8dS23S3Z1A1M1A3A1G1A3A4S18G0S1bS19S0U10G1A4S1aG0A1A3A3A3A3S26S2bS23A1A1P87A4").
Definition T_1j : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UcS29A4S18G0S1bS19S0UeS6S90S3Z0A1S29A3A4S1aG0A1A3A3A3S26S2bS23A1A1P87A4").

Definition T_b2 : axst := ltac2:(tb__ "0|1|
S24S9cS18S1cS19S0A2M0S1bS19S0UaS5aA4S18G0S1bS19S0UcS4cA4S18G0S1bS19S0UdS3S44A1A4S18G0S1bS19S0UeS3S3cA1A4S18G0S1bS19S0UfS3Z0A1A4S18G0S1bS19S0U10S3Z7A1A4S1aG0A1A3A3A3A3A3A3S26S2dS23A1A1P87A4").
Definition T_23 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UdS29A4S1aG0A1A3A3S26S38S23A1A1P87A4").
Definition T_23w : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS5aA4S18G0S1bS19S0UdS4cA4S1aG0A1A3A3S26S2dS23A1A1P87A4").

Definition T_b3 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UdS29A4S1aG0A1A3A3S26S2bS23A1A1P87A4").

Definition T_f2 : axst := ltac2:(tb__ "0|1|
S24S98S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S1aG0A1A3S26S43S23A1A1P87A4").
Definition T_f3 : axst := ltac2:(tb__ "0|1|
S24S98S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S1aG0A1A3S26S42S23A1A1P87A4").

Definition X_j : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S26SbS8fS6S90G1S25A3G1A3A1P87A4").
Definition X_2 : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SbS8fS4cG1A3S26S2dS23A1A1A3P87A4").
Definition X_3e : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SdSbS8eS29G1A3A1S26S2bS23A1A1A3P87A4").
Definition X_3n : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SdSbS8eS29G1A3A1S26S38S23A1A1A3P87A4").

Definition P_ret_0 : axst := ltac2:(tb__ "0|0|
S96S12S98SaaS0S7aS75A1UaS28S5P8cA1A1A4S76S10S20S0A1S18SeS47S1aSeA1A3S3eP8dS22A9S1aS1cS0S0A2A1A2").
Definition P_ret : axst := ltac2:(tb__ "0|0|
S7eS18S1SfS5P8cA1S5P10A1A2S1aS1A1A3S2cA2").
Definition Posts_memchr0 : list leafA := ltac2:(tb__ "0|0|
S18S6fS70S5fSa9A2S1aS6fA1A3").

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S18S6dS3dS18S6dS53S18S6dS56S18S6dS54S18S6dS55S18S6dS57S1aS6dA1A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S18S6dS31S18S6dS2eS18S6dS32S18S6dS2fS18S6dS30S18S6dS33S18S6dS34S18S6dS35S18S6dS4bS18S6dS48S18S6dS49S18S6dS4aS1aS6dA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S18S73S9bS18S73S9aS18S73S9cS18S73S99S1aS73A1A3A3A3A3").

Definition s_b1 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS31A1S6cS3aA1A3").
Definition s_1j : wsub := ltac2:(tb__ "0|0|
S97S75S6cS2eA1S6cS46A1A3").
Definition s_b2 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS32A1S6cS45A1A3").
Definition s_23 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS2fA1S6cS2aA1A3").
Definition s_23w : wsub := ltac2:(tb__ "0|0|
S97S75S6cS30A1S6cS2aA1A3").
Definition s_b3 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS33A1S6cS2aA1A3").
Definition s_f2 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS34A1S6cS2cA1A3").
Definition s_f3 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS35A1S6cS2cA1A3").

Lemma ent_b1 : ltac2:(tb__ "0|0|
S67S1dS6eS31S3aS50A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_1j : ltac2:(tb__ "0|0|
S67S1dS6eS2eS46S4dA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_b2 : ltac2:(tb__ "0|0|
S67S1dS6eS32S45S51A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_23 : ltac2:(tb__ "0|0|
S67S1dS6eS2fS2aS4eA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_23w : ltac2:(tb__ "0|0|
S67S1dS6eS30S2aS4fA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_b3 : ltac2:(tb__ "0|0|
S67S1dS6eS33S2aS52A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_f2 : ltac2:(tb__ "0|0|
S67S1dS6eS34S2cS36A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_f3 : ltac2:(tb__ "0|0|
S67S1dS6eS35S2cS37A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b1 : ltac2:(tb__ "0|0|
S67S1dS8aS50S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_1j : ltac2:(tb__ "0|0|
S67S1dS8aS4dS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b2 : ltac2:(tb__ "0|0|
S67S1dS8aS51S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_23 : ltac2:(tb__ "0|0|
S67S1dS8aS4eS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_23w : ltac2:(tb__ "0|0|
S67S1dS8aS4fS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b3 : ltac2:(tb__ "0|0|
S67S1dS8aS52S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_f2 : ltac2:(tb__ "0|0|
S67S1dS8aS36S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_f3 : ltac2:(tb__ "0|0|
S67S1dS8aS37S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition svals (s : wsub) : list sv := ltac2:(tb__ "0|0|
S72S74S0S89Vs;A1S18S74P78S18S74P7aS18S74P10S18S74P11S18S74PeS1aS74A1A3A3A3A3A3A4").
Definition step1_vals : list sv := ltac2:(tb__ "0|0|
S18S0S6S8dS5P78A1S3Z1A1A3S18S0S6S8dS5P7aA1S3N1A1A3S18S0S5P10A1S18S0S5P11A1S18S0S5PeA1S1aS0A1A3A3A3A3A3").
Definition step8_vals : list sv := ltac2:(tb__ "0|0|
S18S0S6S8dS5P78A1S3Z8A1A3S18S0S6S8dS5P7aA1S3N8A1A3S18S0S5P10A1S18S0S5P11A1S18S0S5PeA1S1aS0A1A3A3A3A3A3").
Lemma vals_b1 : svals s_b1 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_1j : svals s_1j = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_23 : svals s_23 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_b3 : svals s_b3 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_b2 : svals s_b2 = step8_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_23w : svals s_23w = step8_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_f2 : ltac2:(tb__ "0|1|
S67S1cS0S0A2S1bS0S0S89S36P8cA2S89S36P10M0A2A4S1bS0S0S5P78A1S5G0A1A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_f3 : ltac2:(tb__ "0|1|
S67S1cS0S0A2S1bS0S0S89S37P8cA2S89S37P10M0A2A4S1bS0S0S5P78A1S5G0A1A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FirstNul (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S68S67S73S8cS8Vrho;P3A2M0S80Q40S9Vrho;P10A2A2M1A2Z0M2A3S73S68S82G2R1A2S85R1G1A2A2S69S67S73S8cG0R2A2G2A3A1F_;Fi;A2").

Lemma FirstNul_agree : ltac2:(tb__ "0|1|
S74S4S4SacP10R3A2S11R4R3R2A3S3bR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn (A & B & C) [H1 H2]. unfold FirstNul.
  rewrite <- (A 16%positive Hn), <- B. split; assumption.
Qed.

Lemma two62_mod : ltac2:(tb__ "0|1|
S67S73S86S77S84Z2M0Z40A2A2S84G0Z3eA2A3"). Proof. reflexivity. Qed.
Ltac zholds H := cbn [holds eval branch_taken v120 v122 curs c1 r1 c8 r8] in H; unfold bv_ltu, bv_eqb in H;
  rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod in H; cbn [snorm Z.leb Z.ltb Z.sub Z.add Z.opp] in H;
  repeat match type of H with
    | negb _ = true => apply Bool.negb_true_iff in H
    | ~ negb _ = true => apply Bool.not_true_iff_false in H; apply Bool.negb_false_iff in H
    | Z.ltb _ _ = true => apply Z.ltb_lt in H
    | Z.ltb _ _ = false => apply Z.ltb_ge in H
    | Z.leb _ _ = true => apply Z.leb_le in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end.

Section ZFacts.
Variable rho : valuation.
Let c : Z := bv_unsigned (rw rho 120).
Let r : Z := bv_unsigned (rw rho 122).
Let z : Z := bv_unsigned (rw rho 16).
Let A : Z := bv_unsigned (rw rho 17).
Let n : Z := bv_unsigned (rw rho 14).

Definition invZ : Prop := ltac2:(tb__ "0|3|
S68S82Vc;Vz;A2S68S82S83Vc;Z8M0A2VA;A2S68S82Vc;S84Z2Z3eA2M1A2S68S82Vn;S83Vc;Vr;A2M2A2S68S82G2Vn;A2S68S82Vr;G1A2S68S85Vz;Vn;A2S68S82S83Vz;G0A2VA;A2S68S82VA;G1A2S82Vn;G1A2A2A2A2A2A2A2A2A2A2").

Lemma tf_facts : ltac2:(tb__ "0|0|
S1S71S1S2Vrho;A1S21S1S26R1A1S3eA3A3S68S2Vrho;R2A2Sa5A2F_;Ff;").
Proof using .
  intros f HF. unfold tf, inv, base_facts in HF. cbn [app] in HF.
  repeat match type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF as [? HF] end.
  split; [assumption|].
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (urange (rw rho 16)) as R6. pose proof (urange (rw rho 17)) as R7. pose proof (urange (rw rho 14)) as R4.
  unfold invZ. subst c r z A n.
  repeat match goal with H : holds rho _ |- _ => zholds H end.
  change (snorm 8) with 8 in *.
  change (8 mod 2 ^ 64) with 8 in *.
  rewrite Z.mod_small in H1 by lia. rewrite Z.mod_small in H3 by lia. rewrite Z.mod_small in H4 by lia.
  rewrite Z.mod_small in H7 by lia.
  repeat split; lia.
Qed.
End ZFacts.

Lemma inv_intro : ltac2:(tb__ "0|2|
S4S80Q40M0S9R1P78A2A2S73S80G0S9R2P7aA2A2S73S80G0S9R3P10A2A2S73S80G0S9R4P11A2A2S73S80G0S9R5PeA2A2S73S82R5R3A2S82S83R6Z8A2R3A2S82R7S84Z2Z3eA2M1A2S82R4S83R8R7A2A2S82S83R9R8A2R5A2S82R9G1A2S82R8G1A2S71S1S2RdA1S27S23S25A2A3F_;F_;F_;F_;F_;F_;F_;Tn;TA;Tz;Tr;Tc;Frho';").
Proof.
  intros rho' c r z A n H1 H2 H3 H4 H5 H6 H7. subst c r z A n.
  pose proof (urange (rw rho' 120)) as R0. pose proof (urange (rw rho' 122)) as R2.
  pose proof (urange (rw rho' 17)) as R7. pose proof (urange (rw rho' 14)) as R4.
  unfold inv. repeat constructor; cbn [holds eval v120 v122]; rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod;
    change (snorm 8) with 8; rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma rw_sub : ltac2:(tb__ "0|0|
S4S8bS74S67S81Q40A1S9S88R3R2A2R1A2ScR3S89R2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.
Lemma rl_sub : ltac2:(tb__ "0|0|
S4S8bS67S74S1fS81Q8A1A1F_;S8S88R2R1A2A1S8R2A1A3Fs;Frho;").
Proof. reflexivity. Qed.

Lemma svals_eq : ltac2:(tb__ "0|0|
S8bS0S0S0S0S0S67S1fS0A1S41R6A1S18S0R5S18S0R4S18S0R3S18S0R2S18S0R1S1aS0A1A3A3A3A3A3A3S68S67S0S89R7P78A2R6A3S68S67S0S89R7P7aA2R5A3S68S67S0S89R7P10A2R4A3S68S67S0S89R7P11A2R3A3S67S0S89R7PeA2R2A3A2A2A2A2F_;Fe;Fd;Fc;Fb;Fa;Fs;").
Proof. intros s a b c d e H. unfold svals in H. cbn [map] in H. injection H as -> -> -> -> ->. repeat split; reflexivity. Qed.

Lemma holds_BNZ_eq : ltac2:(tb__ "0|0|
S4S0S6bS2R2S2bR1A1A2S69S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_eq, BYTE. apply holds_BNZ'. Qed.
Lemma holds_BZ_eq : ltac2:(tb__ "0|0|
S4S0S6bS2R2S42R1A1A2S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_eq, BYTE. apply holds_BZ'. Qed.
Lemma holds_BNZ_ne : ltac2:(tb__ "0|0|
S4S0S6bS2R2S38R1A1A2S69S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_ne, BYTE. apply holds_BNZ. Qed.
Lemma holds_BZ_ne : ltac2:(tb__ "0|0|
S4S0S6bS2R2S43R1A1A2S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_ne, BYTE. apply holds_BZ. Qed.
Lemma holds_NOZ_mc : ltac2:(tb__ "0|0|
S4S0S2R2S2dR1A1A2S19Sa4R1U8A2S69S67S73S8cS8R5P3A2S83S80Q40ScR5R4A2A2S87R2A1A2A2Z0A3A1F_;Fk;F_;Fe;Frho;").
Proof.
  intros rho e H. apply StrBytes.holds_NOZ. unfold NOZ, HZT in H. unfold StrBytes.NOZ.
  change (StrBytes.WRD e) with (WRD e). fold C1M HI.
  cbn [holds branch_taken] in H |- *. destruct (bv_eqb _ _); [reflexivity|]. exfalso. apply H. reflexivity.
Qed.

Section WithFirstNul.
Variable rho0 : valuation.
Hypothesis FN : FirstNul rho0.
Let G : valuation -> Prop := ltac2:(tb__ "0|0|
S4S11S75Vrho0;R1A3Lrho;").

Lemma G_FN : ltac2:(tb__ "0|0|
S4VG;R1A1S3bR2A1F_;Frho;").
Proof using FN. intros rho Hg. eapply FirstNul_agree; [| exact Hg | exact FN]. reflexivity. Qed.
Lemma G_trans : ltac2:(tb__ "0|0|
S4S4VG;R2A1S11S75R3R2A3VG;R3A1F_;F_;Fr2;Fr1;").
Proof using rho0. intros r1 r2 H1 H2. eapply agree_below_trans; eauto. Qed.

Lemma glue_step1 : ltac2:(tb__ "0|1|
S8bS1S4S67S1fS0A1S41R3A1S63A3S4S2R1R4A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R3A1S71S1S2R4A1S7S6cS24G0S1aS1cS19S0A2A1S26R5A1P87A4A1A1A3S71S1S2S88R5R7A2A1S27S23S25A2A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; cbn [snorm Z.leb]; change (snorm 1) with 1; change (snorm (-1)) with (-1);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma glue_step8 : ltac2:(tb__ "0|0|
S8bS4S67S1fS0A1S41R2A1S64A3VG;R2A1S71S1S2R3A1S7S6cS24Z0S1aS1cS19S0A2A1S26S2dS23A1A1P87A4A1A1A3S71S1S2S88R4R5A2A1S27S23S25A2A3F_;F_;F_;Frho;Fs;").
Proof using FN.
  intros s rho Hs Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho _ HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hff) as NZ. cbn [eval v120] in NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; change (snorm 8) with 8; change (snorm (-8)) with (-8);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma mc_facts : ltac2:(tb__ "0|2|
S73S1fS1cS19S0A2M0A1S1fS1A1M1S74S67G1S7S6cS24R4R3R2R1A4A1A1S7S6cS24Z0S1aG0A1R2P87A4A1A1A3Fnx;FF;Fregs;Fpc;").
Proof using . reflexivity. Qed.

Lemma BNZ_eq_120 : ltac2:(tb__ "0|0|
S4S2R1S2bS23A1A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_eq in H. exact H. Qed.
Lemma BNZ_ne_120 : ltac2:(tb__ "0|0|
S4S2R1S38S23A1A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_ne in H. exact H. Qed.

Lemma glue_b1 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS31A1A1A3S71S1S2S88R3S50A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b1. rewrite mc_facts. apply glue_step1; [exact vals_b1 | exact BNZ_eq_120]. Qed.
Lemma glue_1j : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS2eA1A1A3S71S1S2S88R3S4dA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_1j. rewrite mc_facts. apply glue_step1; [exact vals_1j | exact BNZ_eq_120]. Qed.
Lemma glue_23 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS2fA1A1A3S71S1S2S88R3S4eA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23. rewrite mc_facts. apply glue_step1; [exact vals_23 | exact BNZ_ne_120]. Qed.
Lemma glue_b3 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS33A1A1A3S71S1S2S88R3S52A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b3. rewrite mc_facts. apply glue_step1; [exact vals_b3 | exact BNZ_eq_120]. Qed.
Lemma glue_b2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS32A1A1A3S71S1S2S88R3S51A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b2. rewrite mc_facts. apply glue_step8. exact vals_b2. Qed.
Lemma glue_23w : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS30A1A1A3S71S1S2S88R3S4fA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23w. rewrite mc_facts. apply glue_step8. exact vals_23w. Qed.

Lemma glue_found : ltac2:(tb__ "0|5|
S8bS1S4S67S1cS0S0A2S1bS0S0S89R3P8cM0A2S89R3P10M1A2A4S1bS0S0S5P78M2A1S5G1A1M3A4A3S4S2R1R4A2S67S73S8cS8R2P3A2S80Q40S9R2G2A2A2A2Z0M4A3F_;Frho;VG;R3A1S71S1S2R4A1S7S6cS24G4S1aS1cS19S0A2A1S26R5A1P87A4A1A1A3S71S1S2S88R5R7A2A1S18S1SfS5G0A1G3A2S1aS1A1A3A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as ZB.
  injection Hs as E140 E16.
  pose proof (fn_found (rl rho 3) (bv_unsigned (rw rho 16)) FN1 (bv_unsigned (rw rho 120)) ltac:(pose proof (urange (rw rho 120)); lia) ltac:(lia) ZB) as EQ.
  constructor; [|constructor]. cbn [holds eval]. rewrite !rw_sub, E140, E16. cbn [eval].
  apply bv_eq. exact EQ.
Qed.
Lemma BZ_ne_120 : ltac2:(tb__ "0|0|
S4S2R1S43S23A1A2S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_ne in H. exact H. Qed.
Lemma BZ_eq_120 : ltac2:(tb__ "0|0|
S4S2R1S42S23A1A2S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_eq in H. exact H. Qed.
Lemma glue_f2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS34A1A1A3S71S1S2S88R3S36A2A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f2. rewrite mc_facts. apply glue_found; [exact vals_f2 | exact BZ_ne_120]. Qed.
Lemma glue_f3 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS35A1A1A3S71S1S2S88R3S37A2A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f3. rewrite mc_facts. apply glue_found; [exact vals_f3 | exact BZ_eq_120]. Qed.

Lemma contra_j : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS4bA1A1A3S6aF_;F_;Frho;").
Proof using rho0.
  intros rho Hg HF. unfold X_j in HF. rewrite mc_facts in HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho _ HF) as [H Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  cbn [holds eval branch_taken v122] in H.
  destruct (sltu0_cases (rw rho 122)) as [[EE BB]|[EE BB]]; rewrite EE in H.
  - vm_compute in H. discriminate.
  - lia.
Qed.
Lemma contra_2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS48A1A1A3S6aF_;F_;Frho;").
Proof using FN.
  intros rho Hg HF. unfold X_2 in HF. rewrite mc_facts in HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  apply Forall_cons_iff in HF as [H8 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hn) as NZ. cbn [eval v120] in NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H8. change (snorm (-8)) with (-8) in H8. change (0 mod 2 ^ 64) with 0 in H8.
  assert (bv_unsigned (rw rho 122) >= 9) by lia.
  rewrite Z.mod_small in H8 by lia. lia.
Qed.
Lemma contra_3 : ltac2:(tb__ "0|1|
S1S4S4S2R1R3A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R2A1S71S1S2R3A1S18S1SdSbS8eS29S3G0A1A3A1S7S6cS24G0S1aS1cS19S0A2A1S26R4A1P87A4A1A1A3A3S6aF_;F_;F_;Frho;Ff;").
Proof using FN.
  intros f rho Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  apply Forall_cons_iff in HF as [H1 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hn) as NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H1. change (snorm (-1)) with (-1) in H1. change (0 mod 2 ^ 64) with 0 in H1.
  assert (bv_unsigned (rw rho 122) >= 2) by lia.
  rewrite Z.mod_small in H1 by lia. lia.
Qed.
Lemma contra_3e : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS49A1A1A3S6aF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3e. rewrite mc_facts. apply contra_3. exact BNZ_eq_120. Qed.
Lemma contra_3n : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS4aA1A1A3S6aF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3n. rewrite mc_facts. apply contra_3. exact BNZ_ne_120. Qed.

End WithFirstNul.

Lemma inv_below : ltac2:(tb__ "0|0|
S67S1dSa3S1S13S14S6cS3aA1A1A1S27S23S25A2A3S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma post_below : ltac2:(tb__ "0|0|
S67S1dSa3S1S13S14S6cS2cA1A1A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition inc1 : sv := SAlu ALU_ADD v120 (SLit 1).
Definition inc8 : sv := SAlu ALU_ADD v120 (SLit 8).
Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|1|
S18S7cS7dS3dZ14S3Z0A1A3S18S7cS7dS53ZaS23A3S18S7cS7dS56Z8M0S23A3S18S7cS7dS54Z6S23A3S18S7cS7dS55Z4S23A3S18S7cS7dS57G0S23A3S1aS7cA1A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|3|
S18S7cS7dS31ZcM0S40A3S18S7cS7dS2eG0S40A3S18S7cS7dS32G0S5cA3S18S7cS7dS2fG0S40A3S18S7cS7dS30G0S5cA3S18S7cS7dS33G0S40A3S18S7cS7dS34Z1M1S23A3S18S7cS7dS35G1S23A3S18S7cS7dS4bZ0M2S23A3S18S7cS7dS48G2S23A3S18S7cS7dS49G2S23A3S18S7cS7dS4aG2S23A3S1aS7cA1A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma echeck_mc : ltac2:(tb__ "0|0|
S67S1dSabS95S58S5bS75S65S66A6S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_mc : ltac2:(tb__ "0|0|
S67S1dS7fS95S58S5bS75S61S62A6S1eA3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Theorem memchr0_sum : ltac2:(tb__ "0|0|
Sa8OF_;Sa0S4S1fS81Q40A1A1Sa2S95R4R3A3Sa1S95S75R4A3S3bR4A1Sa7S95R7S9fS95R6S3dR5R4A5S9eS95R6S75R5R4S59A6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HFN.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memchr0 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_memchr0) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_mc.
  - intros E rhoE HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b1 C1_0 (inv v120 v122) s_b1 tp);
        [right; left; reflexivity | exact ent_b1 | exact id_b1 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b1 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_1j C84_0 (inv v120 v122) s_1j tp);
        [right; right; left; reflexivity | exact ent_1j | exact id_1j | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_1j rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b2 C2_0 (inv v120 v122) s_b2 tp);
        [right; right; right; left; reflexivity | exact ent_b2 | exact id_b2 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b2 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_23 C3_0 (inv v120 v122) s_23 tp);
        [right; right; right; right; left; reflexivity | exact ent_23 | exact id_23 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_23 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_23w C3_0 (inv v120 v122) s_23w tp);
        [right; right; right; right; left; reflexivity | exact ent_23w | exact id_23w | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_23w rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b3 C3_0 (inv v120 v122) s_b3 tp);
        [right; right; right; right; left; reflexivity | exact ent_b3 | exact id_b3 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b3 rho HFN r Hg HF)].
    + apply (exit_post_GA segs ok J NF rho cuts_mc Posts_memchr0 T_f2 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2 tp);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f2 rho HFN r Hg HF)].
    + apply (exit_post_GA segs ok J NF rho cuts_mc Posts_memchr0 T_f3 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3 tp);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f3 rho HFN r Hg HF)].
    + apply (exit_contraA segs ok _ X_j). intros r tp' tr md [Hg _] HF. exact (contra_j rho r Hg HF).
    + apply (exit_contraA segs ok _ X_2). intros r tp' tr md [Hg _] HF. exact (contra_2 rho HFN r Hg HF).
    + apply (exit_contraA segs ok _ X_3e). intros r tp' tr md [Hg _] HF. exact (contra_3e rho HFN r Hg HF).
    + apply (exit_contraA segs ok _ X_3n). intros r tp' tr md [Hg _] HF. exact (contra_3n rho HFN r Hg HF).
  - left; reflexivity.
Qed.

Lemma meas_reenter : ltac2:(tb__ "0|2|
S4S8bS0S1fS0A1M0S67G0S41R3A1S18S0R2R1A3A3S82S80Q40M1ScR5R3A2A2S80G1ScS88R5R4A2S23A2A2A2F_;Frest;Fv;Fs;Frho;").
Proof.
  intros rho s v rest H. unfold svals in H. cbn [map] in H. injection H as H _.
  cbn [eval v120]. rewrite rw_sub, H. lia.
Qed.

Theorem memchr0_sum_ex : ltac2:(tb__ "0|0|
Sa0S4S1fS81Q40A1A1Sa1S95S75R3A3S3bR3A1Sa6S95S9fS95R5S3dR4R3A5S9eS95R5S75R4R3S59A6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HFN.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memchr0 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_memchr0 with (vna_state (mkVNA Pre_memchr0 20 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_memchr0) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_mc in Hin. repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_mc.
  - intros E rhoE HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b1 12 inc1) (mkVNA C1 10 v120) (inv v120 v122) C1_0 s_b1 tp);
        [right; left; reflexivity | reflexivity | exact ent_b1 | exact id_b1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b1 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b1 _ _ vals_b1) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_1j 12 inc1) (mkVNA C84 8 v120) (inv v120 v122) C84_0 s_1j tp);
        [right; right; left; reflexivity | reflexivity | exact ent_1j | exact id_1j | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_1j rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_1j _ _ vals_1j) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b2 12 inc8) (mkVNA C2 6 v120) (inv v120 v122) C2_0 s_b2 tp);
        [right; right; right; left; reflexivity | reflexivity | exact ent_b2 | exact id_b2 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b2 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b2 _ _ vals_b2) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_23 12 inc1) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_23 tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23 | exact id_23 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_23 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_23 _ _ vals_23) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_23w 12 inc8) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_23w tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23w | exact id_23w | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_23w rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_23w _ _ vals_23w) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b3 12 inc1) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_b3 tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_b3 | exact id_b3 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b3 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b3 _ _ vals_b3) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_post_IA segs J NF rho vcuts_mc Posts_memchr0 (mkVNA T_f2 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2 tp);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f2 rho HFN r Hg HF)].
    + apply (eexit_post_IA segs J NF rho vcuts_mc Posts_memchr0 (mkVNA T_f3 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3 tp);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f3 rho HFN r Hg HF)].
    + apply (eexit_contraA segs _ X_j). intros r tp' tr md [Hg _] HF. exact (contra_j rho r Hg HF).
    + apply (eexit_contraA segs _ X_2). intros r tp' tr md [Hg _] HF. exact (contra_2 rho HFN r Hg HF).
    + apply (eexit_contraA segs _ X_3e). intros r tp' tr md [Hg _] HF. exact (contra_3e rho HFN r Hg HF).
    + apply (eexit_contraA segs _ X_3n). intros r tp' tr md [Hg _] HF. exact (contra_3n rho HFN r Hg HF).
  - left; reflexivity.
Qed.
End Str_memchrA.

(* [comment removed for export] *)
Module StartNodes2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "rw"; "SVar"; "eval"; "rm"; "ss_next"; "ss_objs"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "prod"; "true"; "pair"; "Some"; "option"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "alloc_top"; "m_vmmaps"; "map_has"; "map_remove"; "region_free"; "vm_init_sp"; "vm_maps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2.Munmap"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA MmapFixedA MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Munmap.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S32S7S17S10Q40A1A1S17S23A1M0S24R5R4R3R2R1A4S0G0R3S19S23A1A3F_;Fmd;Ftr;Ftp;Frho;S33S16Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S32S7S17S10Q40A1A1S17S23A1M0S24R5R4R3R2R1A4S0G0R3S19S23A1A3F_;Fmd;Ftr;Ftp;Frho;S3fS16Vok;R2A3F_;FJ;").

Variables (E : axst) (v : positive) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition munmap_ok : axst := ltac2:(tb__ "0|1|
S15S3cS13VE;A1M0S5Z0A1SdG0A1Vnxt;A4S19S1aS4S4A2A1S5S2fA1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S4S14VE;A1S5S2fA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1eS2cA1S3dS16SeS13VE;A1A1A2S1dS2cS2dA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1Z11A2S5Zd7A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZaA2S9Vv;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZbA2S5VlenZ;A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S40ScS13VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S18S30VGl;S13VE;A1A2S1bA3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).

Lemma n_valM : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. clear - Hpos Hsmall. unfold n. apply u64_of_lit. lia. Qed.
Lemma mmap_n_lit : ltac2:(tb__ "0|2|
S1S0S10Q40M0A1S37S11G0VlenZ;A2M1A1Vn;A3S0S12S38G1A1VlenZ;A3A2").
Proof using Hnl Hpos Hsmall.
  clear - Hnl Hpos Hsmall.
  assert (E : mmap_nZ (Z_to_bv 64 lenZ) = lenZ).
  { unfold mmap_nZ, page_round_up_Z. change page_size with 4096. rewrite u64_of_lit by lia.
    pose proof Hnl as H. apply Z.mod_divide in H as [k Hk]; [|lia]. rewrite Hk.
    replace (k * 4096 + 4096 - 1) with (4095 + k * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [|exact E]. unfold mmap_n, n. rewrite E. reflexivity.
Qed.

Theorem munmap_node : ltac2:(tb__ "0|8|
S7S17S10Q40M0A1M1A1S8R2Vv;A2G1S0S12S22SfG0R1A2Z1000A2Z0A3S3S20S1fSfG0R2A2M2VlenZ;A2Z10000A2S20Z646000G2A2A2S20S1fSfG0R3A2VlenZ;A2S25S26Vm;A1M3A1A2S0S12SfG0S8R6P1A2A2SfG0S2aG3A1A2A3S0S18S27S2bG3A1M4R5Vn;A3S1bA3G1S34S1aG1G1A2S1cG1G1R7R1A4G4A3S0G1R2Vn;A3F_;Fs;S0S18S29S28G4R7A2R7Vn;A3S1bA3S4S12S34S1aS4S12A2S1cS4S12R2R1A4VGl;A3S12S1S20SfG0RcA2M5R1A2S21R1S1fG5VlenZ;A2A2A2S2S1S20SfG0SaRfR5A2A2M6R2A2S21R2S1fG6R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S36S16Vok;S31S16S2eVm;VB;A2VE;RbRaA5S31S16S2eS39Vm;R9Vn;A3VB;A2S35S3bRbS3aSbRbA1R9Vn;A3A2S3eSfG0R9A2M7S1fG7VlenZ;A2RaA3A5A4F_;F_;F_;F_;F_;F_;F_;F_;Ta;Ftp;Frho;").
Proof using All.
  intros rho tp a Hal Hlo Hceil Hv1 Hhas Huniq Hfree HG. pose proof (alloc_top_lt (m_vmmaps m)) as CL. pose proof n_valM as Nv.
  destruct mmap_n_lit as [MN MNZ].
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & _).
  rewrite R10 in G0. rewrite R11 in G1. cbn [eval] in G0, G1. change (rw rho v) with a in G0.
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros E0. apply (f_equal bv_unsigned) in E0. rewrite u64_of_lit in E0 by lia. rewrite u64_of_lit in E0 by lia. lia. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE).
  { rewrite G0, G1, MNZ. unfold TASK_SIZE. pose proof (alloc_top_bounds _ Htop) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. lia. }
  assert (Hhas' : map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, G1, MN, Evm. exact Hhas. }
  assert (Hal' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  split.
  - eapply (OKP (KxA m B)); [intros; eapply KxA_nil; eassumption | exact HK | exact Hp |].
    apply (munmap_exact_only_okA segsA ms md _ H215 Hal' Hlen Hwrap Hhas').
  - intros w' Hw.
    pose proof (wstep_munmap_exact_invA segsA ms md _ Hh H215 Hal' Hlen Hwrap Hhas' [] w' Hp Hw) as ->.
    rewrite G0, G1, MN.
    set (h' := munmap_vm (m_vmmaps md) a n).
    assert (Emd : munmap_model md a n = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' md)) by reflexivity.
    rewrite Emd. split.
    + unfold munmap_ok. rewrite <- Nv.
      replace (mkAX (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt) [] (SLit SHB)) with (ax_setS E (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt))
        by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      apply (smatchA_after_munmap segsA rho _ tp E [] ms md [] h' a n (Z_to_bv 64 0) (SLit 0) nxt Hsp).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * rewrite Evm. exact Huniq.
      * rewrite Evm. exact Hfree.
      * exact Hal.
      * rewrite Nv. exact Hnl.
      * rewrite Nv. unfold two_pow_64 in CL. lia.
      * intros o Ho. rewrite Nv.
        apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear ltac:(lia) ltac:(right; revert Hceil; unfold alloc_top; rewrite stack_max_size_val, <- Hv1; intros Hceil; exact Hceil)); [|exact HG|exact Ho].
        intros x Hx. lia.
      * rewrite HX. intros rr y [].
      * apply agree_below_refl.
      * exact Hnxt.
      * reflexivity.
      * reflexivity.
    + cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
      * unfold munmap_model, with_mmap_destroyed. unfold h'. rewrite Evm. apply erase_mat_cong_forget. exact Hem.
      *
        pose proof HMI as (HW & HT & Hmat & Hsub & HpaidMI & Hlc & Hivs & Hlm & Htm).
        pose proof (used_munmap_le md h' a n Hivs ltac:(rewrite Evm; exact Hfree) eq_refl eq_refl) as U1.
        set (md1 := with_vmmaps h' md) in *.
        set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
        assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
        assert (HT' : List.NoDup (tp_forget lo (lo + lenZ) tp)) by (unfold tp_forget; apply List.NoDup_filter; exact HT).
        assert (U2 : (length (unpaid (vm_forget_range lo hi md1) (tp_forget lo (lo + lenZ) tp)) <= length (unpaid md tp))%nat).
        { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
          intros p Hpp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
          { unfold unpaid in Hpp |- *. apply filter_In in Hpp as [Hpp Hb]. apply filter_In. split; [|exact Hb].
            unfold tp_forget in Hpp. apply filter_In in Hpp as [Hpp _]. exact Hpp. }
          pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
        unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.
End Munmap.
End StartNodes2.

(* [comment removed for export] *)
Module Str_istrlen.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "true"; "prod"; "None"; "false"; "list"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "valuation"; "holds"; "sobj"; "rw"; "SPUle"; "FcsrFrm0"; "SPBranch"; "agree_below"; "mkSS"; "rl"; "sprop_below"; "ss_facts"; "ss_next"; "DList"; "SPEq"; "SPNot"; "cell"; "eval"; "mkObj"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "two62"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen"; "cur"; "E_back"; "E_ret"; "inv"; "s_back"; "s_ret"; "Pre_isl"; "add"; "base_facts"; "C_0"; "FirstNul"; "O_str"; "P_isl0"; "isl_state"; "BYTE"; "C"; "FUEL_ISL"; "F_post"; "Posts_isl"; "cutpcs_isl"; "P_isl"; "cuts_isl"; "exits_isl"; "vcuts_isl"; "vexits_isl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub"; "wsub_id_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen.ISLAddr"; "isl_loop"; "isl_ret"; "isl_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv HasZero StrBytes CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ISLAddr.
  Definition isl_entry : Z := 0x6fe5c.
  Definition isl_loop : Z := 0x6fe60.
  Definition isl_ret : Z := 0x6fe74.
End ISLAddr.
Import ISLAddr.

Definition FUEL_ISL : nat := 60%nat.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S21SdPcA1SeZ0A1SdP11A1S1S1fA1S1cP3A1A5").
Definition base_facts : list sprop := ltac2:(tb__ "0|3|
S0ScS15S5dSdP10A1SdP11A1M0A3S0ScS13G0SeS28A1M1A2S0ScS13SeZ1A1SdPcA1M2A2S0ScS13G2G1A2S1ScA1A3A3A3A3").
Definition Pre_isl : axst := ltac2:(tb__ "0|0|
S46S17S60S2bS26S14S7SbA1S0S11S37S1S11A1A3S34S25S8A9S1S6SbSbA2A1A2").

Definition cur : sv := SVar 120.
Definition add (a b : sv) : sv := SAlu ALU_ADD a b.
Definition BYTE (e : sv) : sv := SExt false 8 (SLBytes 3 e 1).
Definition inv : list sprop := ltac2:(tb__ "0|0|
S0ScS13S2cSdP10A1A2S1ScA1A3").
Definition isl_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S46S17Vpc;S27S29S25A1Vregs;A2S26S14S7SbA1S0S11S37S1S11A1A3SaScVfacts;S34A3Vnx;S8A9S1S6SbSbA2A1A2").

Definition C_0 : axst := ltac2:(tb__ "0|1|
S39S5eS0S6S2SbA2M0S3S2SbUaSdPcA1A4S0G0S3S2SbUbS2cA4S0G0S3S2SbUcSdP79A1A4S1G0A1A3A3A3S1ScA1P87A4").
Definition C : axst := ax_add_facts inv C_0.

Definition E_back : axst := ltac2:(tb__ "0|2|
S39S5eS0S6S2SbA2M0S3S2SbUaSdPcA1A4S0G0S3S2SbUbS33S2cSeZ1A1A2A4S0G0S3S2SbUcS3aS2cA1M1A4S1G0A1A3A3A3S0ScS15S5cG1SeZ0A1A3S2fA3P87A4").
Definition E_ret : axst := ltac2:(tb__ "0|2|
S39S5fS0S6S2SbA2M0S3S2SbUaS2cA4S0G0S3S2SbUbS33S2cSeZ1A1A2A4S0G0S3S2SbUcS3aS2cA1M1A4S1G0A1A3A3A3S0ScS1eS15S5cG1SeZ0A1A3A1S2fA3P87A4").

Definition P_isl0 : axst := ltac2:(tb__ "0|1|
S46S17S5fS27S2aS25A1S0S6S2SbA2M0S3S2SbUaSdP8cA1A4S1G0A1A3A2S26S14S7SbA1S0S11S37S1S11A1A3S34P8dS8A9S1S6SbSbA2A1A2").
Definition F_post : list sprop := ltac2:(tb__ "0|0|
S0ScS1dSdP8cA1SdP10A1A2S1ScA1A3").
Definition P_isl : axst := ax_add_facts F_post P_isl0.
Definition Posts_isl : list leafA := ltac2:(tb__ "0|0|
S0S4aS4bS40S6cA2S1S4aA1A3").

Definition cuts_isl : list axst := ltac2:(tb__ "0|0|
S0S48S32S0S48S3bS1S48A1A3A3").
Definition exits_isl : list axst := ltac2:(tb__ "0|0|
S0S48S2eS0S48S2dS1S48A1A3A3").
Definition cutpcs_isl : list Z := [isl_loop].

Definition vcuts_isl : list vnodeA := ltac2:(tb__ "0|0|
S0S4cS4dS32Z32SeZ0A1A3S0S4cS4dS3bZ1eS2cA3S1S4cA1A3A3").
Definition vexits_isl : list vnodeA := ltac2:(tb__ "0|0|
S0S4cS4dS2eZ0S2cA3S0S4cS4dS2dZ1fS33S2cSeZ1A1A2A3S1S4cA1A3A3").
Lemma echeck_isl : ltac2:(tb__ "0|0|
S22S4S6dS45S3cS3fS25S43S44A6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_isl : ltac2:(tb__ "0|0|
S22S4S4eS45S3cS3fS25S41S42A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUEL_ISL cutpcs_isl NF vcuts_isl vexits_isl cuts_isl exits_isl eq_refl eq_refl echeck_isl). Qed.

Definition s_back : wsub := ltac2:(tb__ "0|0|
S61S25S47S2dA1S47S35A1A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S61S25S47S2eA1S47S38A1A3").
Lemma ent_back : ltac2:(tb__ "0|0|
S22S4S49S2dS35S30A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_ret : ltac2:(tb__ "0|0|
S22S4S49S2eS38S31A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_isl : ltac2:(tb__ "0|0|
S23S22S4S53S30S25A2S5A3S22S4S53S31S25A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma s_vals : ltac2:(tb__ "0|2|
S23S22SbS50S30P78A2S33S2cSeZ1A1A2A3S23S22SbS50S31P8cA2S2cA3S23S22SbS50S30P10M0A2SdG0A1M1A3S22SbS50S31G0A2G1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma inv_below : ltac2:(tb__ "0|0|
S22S4S68ScS19S1bS47S35A1A1A1S2fA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_post_below : ltac2:(tb__ "0|0|
S22S4S68ScS19S1bS47S38A1A1A1S3dA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FirstNul (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S23S22S54S67S18Vrho;P3A2M0S57Q40S12Vrho;P10A2A2M1A2Z0M2A3S54S23S58G2R1A2S5aR1G1A2A2S24S22S54S67G0R2A2G2A3A1F_;Fi;A2").

Lemma FirstNul_agree : ltac2:(tb__ "0|1|
S55SfSfS6eP10R3A2S16R4R3R2A3S36R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn (A & B & C) [H1 H2]. unfold FirstNul. rewrite <- (A 16%positive Hn), <- B. split; assumption.
Qed.

Lemma two62_mod : ltac2:(tb__ "0|1|
S22S54S5bS28S59Z2M0Z40A2A2S59G0Z3eA2A3"). Proof. reflexivity. Qed.
Lemma rw_sub : ltac2:(tb__ "0|0|
SfS52S55S22S56Q40A1S12S51R3R2A2R1A2S20R3S50R2R1A2A2A3Fi;Fs;Frho;"). Proof. reflexivity. Qed.
Lemma rl_sub : ltac2:(tb__ "0|0|
SfS52S22S55S9S56Q8A1A1F_;S18S51R2R1A2A1S18R2A1A3Fs;Frho;"). Proof. reflexivity. Qed.

Section Glue.
Variable rho0 : valuation.
Hypothesis HFN : FirstNul rho0.

Lemma exit_facts : ltac2:(tb__ "0|3|
SfScS4fScS10R2A1SaScS0ScR1S2fA3S34A3A3S23S10R3R2A2S23S58S57Q40M0S12R3P78A2A2S57G0S12R3P10A2A2M1A2S23S5aG1S57G0S12R3P11A2A2M2A2S58G2S59Z2Z3eA2A2A2A2A2F_;Ff;Frho;").
Proof.
  intros rho f HF. cbn [app inv] in HF.
  apply Forall_cons_iff in HF as [Hf HF]. apply Forall_cons_iff in HF as [Hi HF].
  apply Forall_cons_iff in HF as [Hb1 HF]. apply Forall_cons_iff in HF as [Hb2 _].
  split; [exact Hf|].
  pose proof (urange (rw rho 120)). pose proof (urange (rw rho 16)). pose proof (urange (rw rho 17)).
  cbn [holds eval branch_taken cur] in Hi, Hb1, Hb2. unfold bv_ltu in Hb1.
  rewrite ?lit_unsigned, ?two62_mod in Hb2.
  apply Z.ltb_lt in Hb1. repeat split; lia.
Qed.

Lemma glue_back : ltac2:(tb__ "0|0|
SfS16S25Vrho0;R1A3S4fScS10R2A1S1aS47S2dA1A1A3S4fScS10S51R3S30A2A1S2fA3F_;F_;Frho;").
Proof.
  intros rho Hag HF. pose proof (FirstNul_agree NF rho0 rho ltac:(cbv; reflexivity) Hag HFN) as [FN0 FN1].
  destruct (exit_facts rho _ HF) as (Hb & I1 & I2 & I3). apply holds_BNZ in Hb. change (eval rho cur) with (rw rho 120) in Hb.
  pose proof (urange (rw rho 120)) as R.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) I1 Hb) as ST.
  destruct s_vals as (V1 & _ & V3 & _).
  unfold inv. constructor; [|constructor]. cbn [holds]. unfold cur. cbn [eval]. rewrite !rw_sub, V1, V3. unfold add. cbn [eval].
  rewrite add_val, lit_unsigned. unfold cur. cbn [eval]. change (1 mod 2 ^ 64) with 1. rewrite Z.mod_small by lia. lia.
Qed.

Lemma glue_ret : ltac2:(tb__ "0|0|
SfS16S25Vrho0;R1A3S4fScS10R2A1S1aS47S2eA1A1A3S4fScS10S51R3S31A2A1S3dA3F_;F_;Frho;").
Proof.
  intros rho Hag HF. pose proof (FirstNul_agree NF rho0 rho ltac:(cbv; reflexivity) Hag HFN) as [FN0 FN1].
  destruct (exit_facts rho _ HF) as (Hb & I1 & I2 & I3). apply holds_BZ in Hb. change (eval rho cur) with (rw rho 120) in Hb.
  pose proof (urange (rw rho 120)) as R.
  pose proof (fn_found (rl rho 3) (bv_unsigned (rw rho 16)) FN1 (bv_unsigned (rw rho 120)) ltac:(lia) I1 Hb) as FD.
  destruct s_vals as (_ & V2 & _ & V4).
  unfold F_post. constructor; [|constructor]. cbn [holds eval]. rewrite !rw_sub, V2, V4. unfold cur. cbn [eval]. apply bv_eq. exact FD.
Qed.
End Glue.

Theorem istrlen_sum : ltac2:(tb__ "0|0|
S6bOF_;S64SfS9S56Q40A1A1S66S45R4R3A3S65S45S25R4A3S36R4A1S6aS45R7S63S45R6S32R5R4A5S62S45R6S25R5R4S3eA6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HFN. destruct ids_isl as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_isl rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_ISL cutpcs_isl NF cuts_isl exits_isl (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_isl) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_isl.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (exit_post_GA segs ok J NF rho cuts_isl Posts_isl E_ret P_isl0 F_post s_ret tp);
        [left; reflexivity | exact ent_ret | exact I2 | exact Hst | exact F_post_below | intros r Hag HF; exact (glue_ret rho HFN r Hag HF)].
    + apply (exit_reenterA segs ok _ NF cuts_isl _ E_back C_0 inv s_back tp);
        [right; left; reflexivity | exact ent_back | exact I1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hag _] HF; exact (glue_back rho HFN r Hag HF)].
  - left; reflexivity.
Qed.

Theorem istrlen_sum_ex : ltac2:(tb__ "0|0|
S64SfS9S56Q40A1A1S65S45S25R3A3S36R3A1S69S45S63S45R5S32R4R3A5S62S45R5S25R4R3S3eA6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HFN. destruct ids_isl as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_isl rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_isl with (vna_state (mkVNA Pre_isl 50 (SLit 0))).
  apply (cfg_complete_autoIA segs FUEL_ISL cutpcs_isl NF vcuts_isl vexits_isl (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_isl) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_isl in Hin. repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_isl.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (eexit_post_IA segs J NF rho vcuts_isl Posts_isl (mkVNA E_ret 0 cur) P_isl0 F_post s_ret tp);
        [left; reflexivity | exact ent_ret | exact I2 | exact Hst | exact F_post_below | intros r Hag HF; exact (glue_ret rho HFN r Hag HF)].
    + apply (eexit_reenter_IA segs _ NF vcuts_isl _ (mkVNA E_back 31 (add cur (SLit 1))) (mkVNA C 30 cur) inv C_0 s_back tp);
        [right; left; reflexivity | reflexivity | exact ent_back | exact I1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hag _] HF; split; [exact (glue_back rho HFN r Hag HF) | right; split; [| cbn; lia]]
        | cbn; lia | cbn; lia].
      destruct s_vals as (V1 & _). cbn [vna_var]. unfold cur at 2. cbn [eval]. rewrite rw_sub, V1. lia.
  - left; reflexivity.
Qed.
End Str_istrlen.

