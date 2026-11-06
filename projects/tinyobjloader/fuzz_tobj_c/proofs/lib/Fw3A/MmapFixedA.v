(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "ge"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "ss_next"; "ss_objs"; "valuation"; "sv_below"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "DZero"; "cell"; "mkObj"; "rm"; "ro_addr"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "page_size"; "vm_maps"; "vm_limit"; "vm_noaccess"; "maps_subtract"; "Model"; "VmMaps"; "event"; "page_base"; "vm_forget_range"; "with_vmmaps"; "page_outside_range"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "prod"; "true"; "fst"; "nil"; "snd"; "app"; "cons"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "filter"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA.F"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section F.
Variable segs : list Segment.

Lemma page_out_of_aligned_range : ltac2:(tb__ "0|7|
S1Q40M0A1M1G1G1S8S1cS5S0G0R3A2M2S25A2Z0A3M3G3SaS9S3S0G0R5A2M4G2A2S4G2S2G4S0G0R4A2A2A2A2A1SbS3S2S0G0S2dR4A1A2M5S25A2S0G0R6A2M6A2S3S2G6G4A2G5A2A2F_;F_;F_;Fx;Fn;Fa;").
Proof using .
  intros a n x Hal Hnl Hx. rewrite page_base_val. pose proof page_size_pos as Pps.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof (urange x) as Rx.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(lia)) as Da. rewrite Hal in Da.
  pose proof (Z.div_mod (bv_unsigned n) page_size ltac:(lia)) as Dn. rewrite Hnl in Dn.
  pose proof (Z.div_mod (bv_unsigned x) page_size ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (bv_unsigned x) page_size ltac:(lia)) as Mx.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [L|L].
  - left. assert (bv_unsigned x / page_size < bv_unsigned a / page_size) by nia. nia.
  - right. assert (bv_unsigned a + bv_unsigned n <= bv_unsigned x) by lia.
    assert (bv_unsigned a / page_size + bv_unsigned n / page_size <= bv_unsigned x / page_size) by nia. nia.
Qed.

Lemma page_in_aligned_range : ltac2:(tb__ "0|7|
S1Q40M0A1M1G1G1S8S1cS5S0G0R3A2M2S25A2Z0A3M3G3S9S3S0G0R5A2M4G2A2S4G2S2G4S0G0R4A2A2A2A2S9S3S0G0R6A2M5S0G0S2dR4A1A2M6A2S3S2G6S25A2S2G5G4A2A2A2F_;F_;F_;Fx;Fn;Fa;").
Proof using .
  intros a n x Hal Hnl Hx. rewrite page_base_val. pose proof page_size_pos as Pps.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof (urange x) as Rx.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(lia)) as Da. rewrite Hal in Da.
  pose proof (Z.div_mod (bv_unsigned n) page_size ltac:(lia)) as Dn. rewrite Hnl in Dn.
  pose proof (Z.div_mod (bv_unsigned x) page_size ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (bv_unsigned x) page_size ltac:(lia)) as Mx.
  assert (bv_unsigned a / page_size <= bv_unsigned x / page_size) by (apply Z.div_le_mono; lia).
  assert (bv_unsigned x / page_size < bv_unsigned a / page_size + bv_unsigned n / page_size) by nia.
  nia.
Qed.

Lemma smatchA_after_commit_obj : ltac2:(tb__ "0|15|
S11S11S31S1Q40M0A1M1A1S22S31S2cA1M2S40S2aG2S2bG1G1G1ScScS1dS47Vsegs;RfRdRcS32G2S3cRbS3dRaR9A2A4A5S8S31S34G1G1A2A1M3S26R8A1S26S24RaA1A1A3S8G3S28R9A1S29S28S24RbA1A1S0G0R8A2M4S2G4S0G0R7A2A2A3A3S8S1cS27RaA1S27S24RcA1A1A3S8S1cS5S0G0RaA2S25A2Z0M5A3M6G6S9S4G5S0G0RbA2M7A2S4G7S6Z2M8Z3eA2A2A2S3S2S0G0RdA2M9S0G0RcA2A2S6G8Z40A2A2S3S4aS26S24R11A1A1S0G0ReA2MaS2GaG9A2A3G9A2S7S4cR12R16A2GaA2G1S9S3S0G0R11A2MbS0G0R1A2McA2S4GcS2GbS0G0R10A2A2A2A2S8S33S1bVsegs;R2A2S3bA3F_;Fx;SeS3eSeR1S10S1eR18A1A1A3S16S15R1cR2A2S32S1cS1cS0G0R13A2MdS2GdS0G0R12A2A2A4A2F_;Fo;S34ScScA2MeS1cS3eGeR2S1fR1aA1A3S9S3S0G0SdR1eS36ScScR3A3A2A2MfR2A2S4R2S2GfS0G0SdR1eS38ScScR3A3A2A2A2A2A2SaS9S3S0G0R16A2M10S0G0S23S0G0SdR1fS20R1cA1A2A2R3A2A2M11A2S4G11S2G10S0G0R15A2A2A2A2A1F_;F_;Fy;Frr;S14SfS1eR19A1A1R1cR1bA3S48SfS1eR1aA1A1RfA2S8S33S12R10R12A2S35A3S8G1SdR1eR13A2R14A3S8S33S12R12R13A2S35A3S8G1SdR20R14A2R18A3S46Vsegs;R21R20S21R1fS45S1eR1fA1M12R16S39SeS10G12A1S3aSeS19R15S13G5A1S13S0G0R18A2M13A1S37S18A1S17A5S37SeA1A3A3R14A4A2S32G2S3cR1bS3dS42R1dR17S44S41R1dA1R19R18A3A3S2eS0G0R19A2M14S2G14G13A2S2fR1aR1cA2A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Feb;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e eb nx Hsp Hmaps Hna Hlim Hal Hnl Hpos Hend Hov Hroom Hnro Hdisj Hxs Hag Hnx He Hev Heb Hevb.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  set (md1 := with_vmmaps h' md). set (md' := vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) md1).
  assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).

  assert (HIN : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hid md' tp x = false).
  { intros x Hx. destruct (page_in_aligned_range a n x Hal Hnl Hx) as [P1 P2].
    unfold md'. apply hid_forget_in_range; [exact Wl1 | lia | lia]. }
  assert (HOUT : forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n) -> hid md' tp x = hid md tp x).
  { intros x Hx. unfold md'. rewrite (hid_forget_outside md1 (bv_unsigned a) (bv_unsigned a + bv_unsigned n) tp x Wl1 ltac:(lia) (page_out_of_aligned_range a n x Hal Hnl Hx)).
    unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity. reflexivity. }

  assert (Ev : vms md' tp (after_sys_mem ms r (zero_range (ms_mem ms) a n))
               = after_sys_mem (vms md tp ms) r (zero_range (ms_mem (vms md tp ms)) a n)).
  { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    f_equal. apply functional_extensionality. intros x. unfold mrestrict. rewrite !zero_range_at.
    destruct (in_range a n x) eqn:Ein.
    - apply in_range_spec in Ein. rewrite (HIN x Ein). reflexivity.
    - assert (Hn : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
      rewrite (HOUT x Hn). reflexivity. }
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
  -
    unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS]. rewrite Ev.
    eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
    + apply (proj2 (model_idle_vmd md')). unfold md', md1. unfold vm_forget_range. rewrite m_halted_with_vm_backing. exact Hh.
    + rewrite forallb_app. apply andb_true_intro. split.
      * apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx | exact (proj1 (forallb_forall _ _) Hobjwf o Ho)].
      * unfold newo, obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb sv_below dflt_wf andb]. rewrite Heb. reflexivity.
    + pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp2) as (Hall & Hpd & Hfr).
      pose proof (smatch_pending_rom segs _ _ _ _ _ Hsp2) as Hrom.
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
    cbn [cfg_model cfg_ms snd fst].
    assert (Hwf1 : model_ivs_wf md1).
    { unfold md1. apply model_ivs_wf_with_vmmaps; [exact Hivs | rewrite Hmaps; exact (proj1 Hivs) |].
      rewrite Hna. apply maps_subtract_wf; [exact (proj1 (proj2 Hivs)) | lia]. }
    unfold md'. apply (MI_intro segs).
    + exact HW. + exact HT.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps. apply List.NoDup_filter. exact Hmat.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hsub p Hp).
    + pose proof (used_commit_le md h' a n Hivs Hmaps Hna) as U1. fold md1 in U1.
      pose proof (unpaid_forget_le md1 (bv_unsigned a) (bv_unsigned a + bv_unsigned n) tp Wl1 HT) as U2.
      assert (U3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite U3 in U2.
      assert (Hl' : vm_limit (m_vmmaps (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) md1)) = vm_limit (m_vmmaps md)).
      { rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps. exact Hlim. }
      rewrite Hl'. unfold paid. unfold headroom, paid in Hroom. unfold paid in Hpaid. nia.
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
    pose proof (shadow_ok_stable A A rho rho' Hag Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh) as Hsh'.
    apply shadow_ok_transport_objs; [|exact Hsh']. cbn [ax_X ax_base ax_S ax_setS S_after ss_objs].
    intros x Hxw Hout _. apply outside_all_app. split; [exact Hout|]. constructor; [|constructor]. cbn zeta. rewrite Hnewr. cbn [fst snd].
    exact (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) (mod8_of_pages _ _ Hal Hnl) Hxs (xword_agree rho rho' A x Hag Hwf Hxw)).
  -
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a n x) eqn:E.
    + apply in_range_spec in E. rewrite (HIN x E) in Hx. discriminate.
    + assert (Hn : ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
      rewrite (HOUT x Hn) in Hx. destruct (Hhz x Hx) as [H0|[H1 H2]]; [left; exact H0 | right]. split; [exact H1|].
      unfold md', md1. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, Hna. cbn [cfg_model snd] in H2.
      destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (proj1 (proj2 Hivs)) ltac:(lia)) as (_ & _ & Cn).
      rewrite Cn, H2. cbn [andb]. apply negb_true_iff. unfold in_rng. apply andb_false_iff.
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Definition tp_forget (lo hi : Z) (tp : list word) : list word := ltac2:(tb__ "0|0|
S3fS1Q40A1S30Vlo;Vhi;A2Vtp;A3").

Lemma smatchA_after_destroy : ltac2:(tb__ "0|f|
S11S11S31S1Q40M0A1M1A1S22S31S2cA1M2S40S2aG2S2bG1G1G1ScS1dS47Vsegs;ReRcRbS32G2S3cRaS3dR9R8A2A4A5S8S31S34G1G1A2A1M3S26R7A1S29S26S24R9A1A1S0G0R6A2M4S2G4S0G0R5A2A2A3A3S8G3S28R8A1S29S28S24RaA1A1S0G0R7A2M5S2G5G4A2A3A3S8S1cS27R9A1S27S24RbA1A1A3S8S1cS5S0G0R9A2S25A2Z0A3M6G6S3S2S0G0RbA2S0G0RaA2A2S6Z2Z40A2A2SeS3eSeR1S10S1eR13A1A1A3S16S15R17R2A2S32S1cS1cS0G0ReA2M7S2G7S0G0RdA2A2A4A2F_;Fo;S34ScScA2M8S1cS3eG8R2S1fR15A1A3S9S3S0G0SdR19S36ScScR3A3A2A2M9R2A2S4R2S2G9S0G0SdR19S38ScScR3A3A2A2A2A2A2SaS9S3S0G0R11A2MaS0G0S23S0G0SdR1aS20R17A1A2A2R3A2A2MbA2S4GbS2GaS0G0R10A2A2A2A2A1F_;F_;Fy;Frr;S14SfS1eR14A1A1S49R17S43S1aR17A1ReRdA3A2R16A3S48SfS1eR15A1A1RbA2S8S33S12RcRdA2S35A3S8G1SdR19ReA2RfA3S46Vsegs;R1aS4bS0G0R12A2McS2GcGaA2MdR19A3S21R18S45S1eR18A1MeRfS10GeA1ReA4A2S32G2S3cR14S3dS42R16R10S43S41R16A1R12R11A3A3S2eGcGdS2fR13R15A2A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e nx Hsp Hmaps Hna Hlim Hal Hnl Hend Hdisj Hxs Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  set (tp' := tp_forget lo hi tp). set (md1 := with_vmmaps h' md). set (md' := vm_forget_range lo hi md1).
  assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).

  assert (TPout : forall x : word, ~ (lo <= bv_unsigned x < hi) -> page_mem (page_base x) tp' = page_mem (page_base x) tp).
  { intros x Hx. destruct (page_out_of_aligned_range a n x Hal Hnl Hx) as [P|P];
    (destruct (page_mem (page_base x) tp) eqn:E;
      [ apply page_mem_In; apply page_mem_In in E; unfold tp', tp_forget; apply filter_In; split; [exact E|];
        unfold page_outside_range; apply negb_true_iff; apply andb_false_iff; fold lo hi
      | apply page_mem_false; apply page_mem_false in E; intros Hin; apply E; unfold tp', tp_forget in Hin; apply filter_In in Hin as [Hin _]; exact Hin ]).
    - left. apply Z.leb_gt. lia.
    - right. apply Z.ltb_ge. lia. }
  assert (HIN : forall x : word, lo <= bv_unsigned x < hi -> hid md' tp' x = false).
  { intros x Hx. destruct (page_in_aligned_range a n x Hal Hnl Hx) as [P1 P2].
    unfold md'. apply hid_forget_in_range; [exact Wl1 | lia | lia]. }
  assert (HOUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> hid md' tp' x = hid md tp x).
  { intros x Hx. unfold md'. rewrite (hid_forget_outside md1 lo hi tp' x Wl1 ltac:(lia) (page_out_of_aligned_range a n x Hal Hnl Hx)).
    unfold md1, hid. rewrite m_vm_lazy_with_vmmaps, (TPout x Hx). reflexivity. }
  assert (Hh' : m_halted md' = m_halted md).
  { unfold md', md1, vm_forget_range. rewrite m_halted_with_vm_backing. reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    rewrite (vms_after_range_none md md' tp' ms a n r (unmap_range (ms_mem ms) a n)).
    + pose proof (smatch_pending_reunmap segs rho (ax_S A) tr (vms md tp ms) (vmd md) a n Hspv Hend Hdisj) as Hsp1.
      pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
      rewrite after_sys_mem_with_mem.
      unfold after_sys.
      assert (Evm : with_mem (vms md tp' ms) (unmap_range (ms_mem (vms md tp' ms)) a n) = with_mem (vms md tp ms) (unmap_range (ms_mem (vms md tp ms)) a n)).
      { unfold vms, restrict, with_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]. f_equal.
        apply functional_extensionality. intros x. rewrite !unmap_range_at. destruct (in_range a n x) eqn:E; [reflexivity|].
        unfold mrestrict, hid. assert (Hx : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
        rewrite (TPout x Hx). reflexivity. }
      rewrite Evm.
      eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
      * apply (proj2 (model_idle_vmd md')). rewrite Hh'. exact Hh.
      * apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx|]. exact (proj1 (forallb_forall _ _) (swf_objs _ (smatch_pendingA_swf segs _ _ _ _ Hsp)) o Ho).
      * apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
      * exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2).
    + intros x Hx. right. rewrite unmap_range_at. rewrite (proj2 (in_range_spec a n x) Hx). reflexivity.
    + intros x Hx. split.
      * rewrite (HOUT x Hx). unfold hid. rewrite (TPout x Hx). reflexivity.
      * rewrite unmap_range_at. destruct (in_range a n x) eqn:E; [|reflexivity]. exfalso. apply Hx. apply in_range_spec. exact E.
    + exact Hend.
  -
    cbn [cfg_model cfg_ms snd fst].
    assert (Hwf1 : model_ivs_wf md1).
    { unfold md1. apply model_ivs_wf_with_vmmaps; [exact Hivs | |].
      - rewrite Hmaps. apply maps_subtract_wf; [exact (proj1 Hivs) | lia].
      - rewrite Hna. apply maps_subtract_wf; [exact (proj1 (proj2 Hivs)) | lia]. }
    assert (HT' : List.NoDup tp') by (unfold tp', tp_forget; apply List.NoDup_filter; exact HT).
    unfold md'. apply (MI_intro segs).
    + exact HW. + exact HT'.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps. apply List.NoDup_filter. exact Hmat.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      intros p Hp. apply filter_In in Hp as [Hp Ho]. unfold tp', tp_forget. apply filter_In. split; [exact (Hsub p Hp) | exact Ho].
    + pose proof (used_destroy_le md h' lo hi Hivs ltac:(lia) Hmaps Hna) as U1. fold md1 in U1.
      assert (U2 : (length (unpaid (vm_forget_range lo hi md1) tp') <= length (unpaid md tp))%nat).
      { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
        intros p Hp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
        { unfold unpaid in Hp |- *. apply filter_In in Hp as [Hp Hb]. apply filter_In. split; [|exact Hb].
          unfold tp', tp_forget in Hp. apply filter_In in Hp as [Hp _]. exact Hp. }
        pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
      assert (Hl' : vm_limit (m_vmmaps (vm_forget_range lo hi md1)) = vm_limit (m_vmmaps md)).
      { rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps. exact Hlim. }
      rewrite Hl'. unfold paid. unfold paid in Hpaid. nia.
    + rewrite m_vm_lazy_vm_forget_range. unfold md1. rewrite m_vm_lazy_with_vmmaps. apply lazy_clear_pieces; [exact (proj2 (proj2 Hivs)) | exact Hlc].
    + apply model_ivs_wf_vm_forget_range; [lia | exact Hwf1].
    + unfold md1. apply (lazy_in_maps_destroy lo hi md h' Hivs ltac:(lia) Hlm Hmaps).
    + unfold md1, tp', tp_forget, lo, hi. apply tp_in_maps_destroy; [exact Hivs | exact Htm | exact Hal | exact Hnl | exact Hmaps].
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
      rewrite Cn, H2. cbn [andb]. apply negb_true_iff. unfold in_rng. apply andb_false_iff.
      destruct (Z_lt_le_dec (bv_unsigned x) lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

End F.
