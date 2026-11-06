(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "ss_next"; "ss_objs"; "valuation"; "sv_below"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "DZero"; "cell"; "mkObj"; "rm"; "ro_addr"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "div"; "ge"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "pair"; "list"; "bool"; "prod"; "cons"; "true"; "fst"; "nil"; "snd"; "app"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "vm_noaccess"; "vm_limit"; "Model"; "VmMaps"; "with_vmmaps"; "event"; "maps_subtract"; "vm_backing_used"; "vm_forget_range"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "word_byte"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA MmapFixedA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section B.
Variable segs : list Segment.

Lemma smatchA_after_grant_obj : ltac2:(tb__ "0|11|
SaSaS1fS1Q40M0A1M1A1S3aS1fS30A1M2S40S2dG2S2eG1G1G1S5S5S1dS47Vsegs;RfRdRcS1eG2S3dRbS3eRaR9A2A4A5S2S1fS21G1G1A2M3A1M4S2aR8A1S22G3S1eG1G1R7R6A4S2aS29RaA1A1A3A3S2G4S2bR9A1S2bS29RbA1A1A3S2S1cS2cRaA1S2cS29RcA1A1A3S3S17Z0M5S0G0R9A2M6A2S17G6S18Z2M7Z3eA2A2A2S16S15S0G0RbA2S0G0RaA2A2S18G7Z40A2A2S2S20S35S2aS29RfA1A1RcRbA3S23A3S1aS4bR10R14A2S0G0RcA2A2G1S3S16S0G0RfA2M8S0G0R1A2M9A2S17G9S15G8S0G0ReA2A2A2A2S2S20S14Vsegs;R2A2S28A3F_;Fx;S7S3fS7R1S9S36R16A1A1A3SfSeR1aR2A2S1eS1cS1cS0G0R11A2MaS15GaS0G0R10A2A2A4A2F_;Fo;S21S5S5A2MbS1cS1cS3fGbR3S37R19A1A3S3S16S0G0S6R1dS24S5S5R4A3A2A2McR3A2S17R3S15GcS0G0S6R1dS26S5S5R4A3A2A2A2A2A2S3S16G5R3A2S17R3Z8MdA2A2S4S3S16S0G0R16A2MeS0G0S3cS15S0G0S6R1fS38R1cA1A2A2S19R5GdA2A2R4A2A2MfA2S17GfS15GeS0G0R15A2A2A2A2A1F_;F_;F_;Fj;Fy;Frr;SdS8S36R17A1A1R1aR19A3S48S8S36R18A1A1RdA2S2S20SbReR10A2S23A3S2G1S6R1cR11A2R12A3S2S20SbR10R11A2S23A3S2G1S6R1eR12A2R16A3S46Vsegs;R1fR1eS39R1dS45S36R1dA1M10R14S27S7S9G10A1S22S7S12R13ScG5A1ScGeA1S25S11A1S10A5S25S7A1A3A3R12A4A2S1eG2S3dR19S3eS42R1bR15S44S41R1bA1R17R16A3A3S2fR18R1aA2A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Feb;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e eb nx Hsp Hmaps Hna Hlim Hn Hend Hfree Hroom Hnro Hdisj Hxs Hag Hnx He Hev Heb Hevb.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn.
  set (md' := with_vmmaps h' md).
  assert (Hvis : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hid md tp x = false).
  { intros x Hx. eapply hid_false_of_region_free; eauto. }
  assert (Hhid : hid md' tp = hid md tp) by (unfold md'; apply (hid_ext md); reflexivity).
  assert (Ev : vms md' tp (after_sys_mem ms r (zero_range (ms_mem ms) a n))
               = after_sys_mem (vms md tp ms) r (zero_range (ms_mem (vms md tp ms)) a n)).
  { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    f_equal. apply functional_extensionality. intros x. unfold mrestrict. rewrite Hhid, !zero_range_at.
    destruct (in_range a n x) eqn:Ein; [|reflexivity].
    apply in_range_spec in Ein. rewrite (Hvis x Ein). reflexivity. }
  pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag Hspv) as Hsp2.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp2) as Hswf. pose proof (swf_objs _ Hswf) as Hobjwf.
  assert (Hrng : forall o, In o (ss_objs (ax_S A)) -> obj_range rho' o = obj_range rho o).
  { intros o Ho. eapply obj_range_agree; [exact Hag | exact (proj1 (forallb_forall _ _) Hobjwf o Ho)]. }
  set (newo := mkObj eb (SLit 0) (SLit (bv_unsigned n)) [] DZero).
  assert (Hlo0 : soff rho' (SLit 0) = 0) by (rewrite soff_lit; reflexivity).
  assert (Hhi0 : soff rho' (SLit (bv_unsigned n)) = bv_unsigned n).
  { rewrite soff_lit. unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec (bv_unsigned n) (2 ^ 63)); lia. }
  assert (Hnewr : obj_range rho' newo = (bv_unsigned a, bv_unsigned a + bv_unsigned n)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hevb, Hlo0, Hhi0. f_equal. lia. }
  set (vm := vms md tp ms) in *.
  assert (Hzr : forall x : word, zero_range (ms_mem vm) a n x = if in_range a n x then Some (Z_to_bv 8 0) else ms_mem vm x)
    by (intros x; apply zero_range_at).
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS]. rewrite Ev.
    eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
    + apply (proj2 (model_idle_vmd md')). exact Hh.
    + rewrite forallb_app. apply andb_true_intro. split.
      * apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx | exact (proj1 (forallb_forall _ _) Hobjwf o Ho)].
      * unfold newo, obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb sv_below dflt_wf andb]. rewrite Heb. reflexivity.
    + pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp2) as (Hall & Hpd & Hfr).
      split; [|split].
      * apply Forall_app. split.
        -- apply Forall_forall. intros o Ho.
           pose proof (proj1 (Forall_forall _ _) Hall o Ho) as Hoh.
           eapply (obj_holds_ext segs rho' nx vm); [reflexivity | | eapply obj_wf_mono; [exact Hnx | exact (proj1 (forallb_forall _ _) Hobjwf o Ho)] | exact Hoh].
           intros off Hoff. rewrite after_sys_memq, Hzr.
           pose proof (Hdisj o Ho) as D. rewrite <- (Hrng o Ho) in D.
           pose proof (proj1 Hoh) as HB. unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D. unfold obj_lo_of, obj_hi_of in *.
           destruct (in_range a n _) eqn:Hir; [|reflexivity].
           apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
        -- constructor; [|constructor].
           unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Hevb, Hlo0, Hhi0.
           split; [lia|]. split.
           { intros off Hoff _. rewrite after_sys_memq. unfold wview. rewrite Hzr.
             replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [discriminate|].
             symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia. }
           split; [constructor|]. split; [|exact I].
           intros off Hoff _. cbn [dflt_holds]. unfold rd, ms_read_byte. rewrite after_sys_memq, Hzr.
           replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [reflexivity|].
           symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia.
      * apply pairwise_disjoint_app1; [exact Hpd|].
        apply Forall_forall. intros o Ho. rewrite Hnewr, (Hrng o Ho). exact (Hdisj o Ho).
      * intros x Hout. apply outside_all_app in Hout as [Hout1 Hout2].
        rewrite after_sys_memq, Hzr. destruct (in_range a n x) eqn:Hir.
        -- exfalso. apply in_range_spec in Hir. pose proof (Forall_inv Hout2) as Hx. cbn zeta in Hx. apply Hx. fold newo. rewrite Hnewr. cbn [fst snd]. exact Hir.
        -- apply Hfr. exact Hout1.
    + intros x Hro. rewrite Hzr. destruct (in_range a n x) eqn:Hir.
      * apply in_range_spec in Hir. rewrite (Hnro x Hir) in Hro. discriminate.
      * apply (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2). exact Hro.
  -
    cbn [cfg_model cfg_ms snd fst]. unfold md'. eapply (MI_with_vmmaps segs md _ tp (bv_unsigned n) HMI); try exact Hlim.
    + rewrite Hmaps. apply ivs_wf_cons; [apply iv_wf_intro; exact Hend | exact (proj1 Hivs)].
    + rewrite Hna. exact (proj1 (proj2 Hivs)).
    + rewrite Hmaps. intros rr Hr. right. exact Hr.
    + apply (used_maps_cons_le md _ a n Hivs (iv_wf_intro a n Hend) Hmaps Hna).
    + exact Hroom.
  -   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  -
    pose proof (shadow_ok_stable A A rho rho' Hag Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh) as Hsh'.
    apply shadow_ok_transport_objs; [|exact Hsh']. cbn [ax_X ax_base ax_S ax_setS S_after ss_objs].
    intros x Hxw Hout _. apply outside_all_app. split; [exact Hout|]. constructor; [|constructor]. cbn zeta. rewrite Hnewr. cbn [fst snd].
    exact (xword_avoid rho A _ _ x Hxs (xword_agree rho rho' A x Hag Hwf Hxw)).
  -
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite Hhid in Hx. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a n x); [left; reflexivity|]. unfold md'. rewrite m_vmmaps_with_vmmaps, Hna. exact (Hhz x Hx).
Qed.

Lemma used_protnone_le : ltac2:(tb__ "0|6|
S2dS2eS1Q40M0A1M1G1S4aR4A1S16S15S0G0R3A2S0G0R2A2A2S18Z2Z40A2A2S2S1fS21G1G1A2M2A1M3S2aR5A1S2aS29R6A1A1A3S2G3S2bR6A1S22G2S1eG1G1R5R4A4S31S2bS29R7A1A1S0G0R5A2M4S15G4S0G0R4A2A2A3A3A3S16S32S33S0G0R6A2M5S15G5G4A2S2fR7R8A2A3A1S32R8A1A2F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof using .
  intros m h' a n Hwf Hend Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  pose proof (urange a) as Ra. pose proof (urange n) as Rn.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (Wn' & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (Wl' & _ & Cl).
  assert (Hwf' : model_ivs_wf (vm_forget_range lo hi (with_vmmaps h' m))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [exact Wm | split; [|exact Wl']].
    apply ivs_wf_cons; [apply iv_wf_intro; exact Hend | exact Wn']. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna.
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)). pose proof page_size_pos.
  apply Z.add_le_mono; [|nia].
  apply sum_count_mono. intros x Hx. cbn [app] in Hx.
  change (negb (in_iv (a, n) x || covered (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ++ maps_subtract (m_vm_lazy m) lo hi) x) = true) in Hx.
  rewrite covered_app in Hx. rewrite covered_app. rewrite Cn, Cl in Hx.
  apply negb_true_iff in Hx. apply negb_true_iff.
  apply orb_false_iff in Hx as [Hiv H12]. apply orb_false_iff in H12 as [Hc1 Hc2].

  assert (Hr : in_rng lo hi x = false).
  { unfold in_iv, in_rng, ivB, ivS in Hiv. cbn [fst snd] in Hiv. fold lo in Hiv. fold hi in Hiv. exact Hiv. }
  rewrite Hr, !andb_true_r in Hc1, Hc2. rewrite Hc1, Hc2. reflexivity.
Qed.

Lemma smatchA_after_protnone : ltac2:(tb__ "0|e|
SaSaS1fS1Q40M0A1M1A1S3aS1fS30A1M2S40S2dG2S2eG1G1G1S5S1dS47Vsegs;ReRcRbS1eG2S3dRaS3eR9R8A2A4A5S2S1fS21G1G1A2M3A1M4S2aR7A1S2aS29R9A1A1A3S2G4S2bR8A1S22G3S1eG1G1R7R6A4S31S2bS29RaA1A1S0G0R7A2M5S15G5S0G0R6A2A2A3A3A3S2S1cS2cR9A1S2cS29RbA1A1A3S2S1cS1bS0G0R9A2S34A2Z0A3M6G6S16S15S0G0RbA2S0G0RaA2A2S18Z2Z40A2A2S7S3fS7R1S9S36R13A1A1A3SfSeR17R2A2S1eS1cS1cS0G0ReA2M7S15G7S0G0RdA2A2A4A2F_;Fo;S21S5S5A2M8S1cS3fG8R2S37R15A1A3S3S16S0G0S6R19S24S5S5R3A3A2A2M9R2A2S17R2S15G9S0G0S6R19S26S5S5R3A3A2A2A2A2A2S4S3S16S0G0R11A2MaS0G0S3bS0G0S6R1aS38R17A1A2A2R3A2A2MbA2S17GbS15GaS0G0R10A2A2A2A2A1F_;F_;Fy;Frr;SdS8S36R14A1A1S49R17S43S13R17A1ReRdA3A2R16A3S48S8S36R15A1A1RbA2S2S20SbRcRdA2S23A3S2G1S6R19ReA2RfA3S46Vsegs;R1aR19S39R18S45S36R18A1McRfS9GcA1ReA4A2S1eG2S3dR14S3eS42R16R10S43S41R16A1R12R11A3A3S33S0G0R12A2MdS15GdGaA2S2fR13R15A2A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e nx Hsp Hmaps Hna Hlim Hal Hnl Hend Hdisj Hxs Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  set (md1 := with_vmmaps h' md). set (md' := vm_forget_range lo hi md1).
  assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
  assert (HIN : forall x : word, lo <= bv_unsigned x < hi -> hid md' tp x = false).
  { intros x Hx. destruct (page_in_aligned_range a n x Hal Hnl Hx) as [P1 P2].
    unfold md'. apply hid_forget_in_range; [exact Wl1 | lia | lia]. }
  assert (HOUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> hid md' tp x = hid md tp x).
  { intros x Hx. unfold md'. rewrite (hid_forget_outside md1 lo hi tp x Wl1 ltac:(lia) (page_out_of_aligned_range a n x Hal Hnl Hx)).
    unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity. reflexivity. }
  assert (Hh' : m_halted md' = m_halted md).
  { unfold md', md1, vm_forget_range. rewrite m_halted_with_vm_backing. reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    rewrite (vms_after_range_none md md' tp ms a n r (unmap_range (ms_mem ms) a n)).
    + pose proof (smatch_pending_reunmap segs rho (ax_S A) tr (vms md tp ms) (vmd md) a n Hspv Hend Hdisj) as Hsp1.
      pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
      rewrite after_sys_mem_with_mem. unfold after_sys.
      eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
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
    assert (Hwf1 : model_ivs_wf md1).
    { unfold md1. apply model_ivs_wf_with_vmmaps; [exact Hivs | rewrite Hmaps; exact (proj1 Hivs) |].
      rewrite Hna. apply ivs_wf_cons; [apply iv_wf_intro; exact Hend|]. apply maps_subtract_wf; [exact (proj1 (proj2 Hivs)) | lia]. }
    unfold md'. apply (MI_intro segs).
    + exact HW. + exact HT.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps. apply List.NoDup_filter. exact Hmat.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hsub p Hp).
    + pose proof (used_protnone_le md h' a n Hivs Hend Hmaps Hna) as U1. fold lo hi md1 in U1.
      pose proof (unpaid_forget_le md1 lo hi tp Wl1 HT) as U2.
      assert (U3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite U3 in U2.
      assert (Hl' : vm_limit (m_vmmaps (vm_forget_range lo hi md1)) = vm_limit (m_vmmaps md)).
      { rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps. exact Hlim. }
      rewrite Hl'. unfold paid. unfold paid in Hpaid. nia.
    + rewrite m_vm_lazy_vm_forget_range. unfold md1. rewrite m_vm_lazy_with_vmmaps. apply lazy_clear_pieces; [exact (proj2 (proj2 Hivs)) | exact Hlc].
    + apply model_ivs_wf_vm_forget_range; [lia | exact Hwf1].
    + apply lazy_in_maps_forget; [exact Wl1|]. unfold md1. apply lazy_in_maps_with_vmmaps_grow; [exact Hlm | rewrite Hmaps; intros rr Hr; exact Hr].
    + intros p Hp. destruct (Htm p Hp) as (Hpal & b & s0 & Hbs & X). split; [exact Hpal|]. exists b, s0.
      rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps, Hmaps. split; [exact Hbs | exact X].
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
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite after_sys_memq, unmap_range_at.
    destruct (in_range a n x) eqn:E.
    + apply in_range_spec in E. rewrite (HIN x E) in Hx. discriminate.
    + assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
      rewrite (HOUT x Hn) in Hx. destruct (Hhz x Hx) as [H0|[H1 H2]]; [left; exact H0 | right]. split; [exact H1|].
      unfold md', md1. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, Hna. cbn [cfg_model snd] in H2.
      destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi (proj1 (proj2 Hivs)) ltac:(lia)) as (_ & _ & Cn).
      cbn [covered existsb]. fold (covered (maps_subtract (vm_noaccess (m_vmmaps md)) lo hi) (bv_unsigned x)).
      rewrite Cn, H2. cbn [andb]. apply orb_true_intro. right. apply negb_true_iff. unfold in_rng. apply andb_false_iff.
      destruct (Z_lt_le_dec (bv_unsigned x) lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

End B.
