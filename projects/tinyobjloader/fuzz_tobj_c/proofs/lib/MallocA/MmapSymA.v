(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "eval"; "ss_next"; "ss_objs"; "SVar"; "reg_sv"; "valuation"; "SLit"; "obj_range"; "ranges_disjoint"; "ro_addr"; "sv_below"; "ss_pc"; "DZero"; "cell"; "mkObj"; "smatch"; "sstate"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "pow"; "modulo"; "ge"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "list"; "false"; "true"; "nil"; "app"; "cons"; "fst"; "prod"; "snd"; "Some"; "option"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "ENOMEM"; "errno_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "smatch_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "smatchA"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA.M"; "mmap_obj_sym"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "mmap_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "model_idle"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_nZ"; "mmap_rw_vm"; "mmap_n"; "mmap_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundM SymSoundR SymSoundL SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.

Definition mmap_obj_sym (nxt : positive) (elen : sv) : sobj := ltac2:(tb__ "0|0|
S19SeVnxt;A1S11Z0A1Velen;S30S18A1S17A5").

Lemma smatch_after_mmap_sym : ltac2:(tb__ "0|8|
S10S1bS2dS3cA1M0S1dS3bG0S3bS6Q40M1A1M2G2S9S8S43Vsegs;RbRaS2cG0S38R9S39R8R7A2A4A4S54R6A1S0S2bS15ScRcA1R4A2S2fA3S0S8S5G1SbReR5A2A2R4A3S0S8S5G1R7A2R5A3S25R6S28Z2M3Z3fA2A2S27S26S5G1RaA2R7A2S28G3Z40A2A2SaS3aSaR1SdR12A1A3S13S12R14R2A2S2cS8S8S5G1RdA2M4S26G4RaA2M5A4A2F_;Fo;G2S1S27G4S5G1R1A2M6A2S25G6G5A2A2S0S2bS14Vsegs;R2A2S2eA3F_;Fx;S1aVsegs;S41R14ScR13A1M7RdA3S42R13SeG7A1S31SaSdR13A1S32SaS4eG7RbA2S30SaA1A3A3S4fG7A1A4S2cG0S38RfS39S5cR11RdS5dS1eR11A1RdRcA3A3ReA2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Fn;Fa;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' a n elen nlit Hsp Hh' Hbel Helen Hn Hn63 Hnw Hdisj Hnro.
  pose proof (urange a) as Ha. pose proof (urange n) as Hn0.
  set (nx := ss_next S). set (rho' := rho_set_rw rho nx a).
  assert (Hag : agree_below nx rho rho') by (apply agree_below_set_rw; lia).
  pose proof (smatch_pending_agree segs rho rho' S tr ms md Hag Hsp) as Hsp'.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (swf_objs S Hwf) as Hobjwf.
  assert (Hbase : eval rho' (SVar nx) = a) by (cbn; rewrite Pos.eqb_refl; reflexivity).
  assert (Hlo0 : soff rho' (SLit 0) = 0) by (rewrite soff_lit; reflexivity).
  assert (Helen' : eval rho' elen = eval rho elen) by (symmetry; apply (eval_agree nx rho rho'); [exact Hag | exact Hbel]).
  assert (Hhi0 : soff rho' elen = nlit).
  { unfold soff. rewrite Helen'. rewrite signed_small by lia. exact Helen. }
  assert (Hrng : forall o, In o (ss_objs S) -> obj_range rho' o = obj_range rho o).
  { intros o Hin. eapply obj_range_agree; [exact Hag | exact (proj1 (forallb_forall _ _) Hobjwf o Hin)]. }
  assert (Hzr : forall x : word,
            zero_range (ms_mem ms) a n x = if in_range a n x then Some (Z_to_bv 8 0) else ms_mem ms x)
    by (intros x; apply zero_range_at).
  eapply (smatch_after_sys segs); [exact Hsp' | exact Hh' | lia | | exact Hbase | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - rewrite forallb_app. apply andb_true_intro. split.
    + apply forallb_forall. intros o Hin. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) Hobjwf o Hin)]. lia.
    + unfold mmap_obj_sym, obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
      rewrite (sv_below_mono nx (Pos.succ nx) elen ltac:(lia) Hbel).
      replace (sv_below (Pos.succ nx) (SVar nx)) with true by (cbn; symmetry; apply (proj2 (Pos.ltb_lt nx (Pos.succ nx))); lia).
      reflexivity.
  - pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp') as (Hall & Hpd & Hfr).
    pose proof (smatch_pending_rom segs _ _ _ _ _ Hsp') as Hrom.
    split; [|split].
    + apply Forall_app. split.
      * apply Forall_forall. intros o Hin.
        pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
        pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
        eapply (obj_holds_ext segs rho' nx ms); [reflexivity | | exact Howf | exact Ho].
        intros off Hoff. rewrite after_sys_memq, Hzr.
        pose proof (Hdisj o Hin) as D. rewrite <- (Hrng o Hin) in D.
        pose proof (proj1 Ho) as HB. unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
        unfold obj_lo_of, obj_hi_of in *.
        destruct (in_range a n _) eqn:Hir; [|reflexivity].
        apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
      * constructor; [|constructor].
        unfold obj_holds, obj_lo_of, obj_hi_of, mmap_obj_sym. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Hbase, Hlo0, Hhi0.
        split; [lia|]. split.
        { intros off Hoff. rewrite after_sys_memq. unfold wview. rewrite Hzr.
          replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [discriminate|].
          symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia. }
        split; [constructor|]. split; [|exact I].
        intros off Hoff _. cbn [dflt_holds]. unfold rd, ms_read_byte. rewrite after_sys_memq, Hzr.
        replace (in_range a n (Z_to_bv 64 (bv_unsigned a + off))) with true; [reflexivity|].
        symmetry. apply in_range_spec. rewrite u64_of_sum by lia. lia.
    + apply pairwise_disjoint_app1; [exact Hpd|].
      apply Forall_forall. intros o Hin. rewrite (Hrng o Hin).
      unfold obj_range at 2. unfold obj_lo_of, obj_hi_of, mmap_obj_sym. cbn [ob_base ob_lo ob_hi]. rewrite Hbase, Hlo0, Hhi0, Z.add_0_r.
      exact (Hdisj o Hin).
    + intros x Hout. apply outside_all_app in Hout as [Hout1 Hout2].
      rewrite after_sys_memq, Hzr.
      destruct (in_range a n x) eqn:Hir.
      * exfalso. apply in_range_spec in Hir. pose proof (Forall_inv Hout2) as Hx. cbn zeta in Hx.
        apply Hx. unfold obj_range, obj_lo_of, obj_hi_of, mmap_obj_sym. cbn [ob_base ob_lo ob_hi fst snd]. rewrite Hbase, Hlo0, Hhi0. lia.
      * apply Hfr. exact Hout1.
  - intros x Hro. rewrite Hzr. destruct (in_range a n x) eqn:Hir.
    + apply in_range_spec in Hir. rewrite (Hnro x) in Hro by lia. discriminate.
    + apply (smatch_pending_ro_clear segs _ _ _ _ _ Hsp). exact Hro.
Qed.

Lemma smatchA_after_mmap_obj_sym : ltac2:(tb__ "0|10|
S10S2dS6Q40M0A1M1A1S20S2dS3cA1M2S1dS3bG2G1S9S8S4bVsegs;RaR9R8S2cG2S38R7S39R6R5A2A4A5S0S2bS50S1cR7U3M3A2A1S2eA3S0S2bS15ScS1fRaA1A1R4A2S2fA3S0S8S5G0SbRdR5A2A2R4A3S0S8S29R5Z1000A2Z0M4A3S0S8S57S1cRbU1M5A2A1R6A3S1S25G4R7A2S25R7S28Z2Z3eA2A2A2S2aS5bRcR10A2R8A2S56S1cReU0A2S1cReG3A2RdS1cReG5A2RbA5SaS3aSaR1SdS1fR12A1A1A3S13S12R15R2A2S2cS8S8S5G0ReA2M6S26G6RcA2M7A4A2F_;Fo;G1S1S27G6S5G0R1A2M8A2S25G8G7A2A2S0S2bS14Vsegs;R2A2S2eA3F_;Fx;S34S9S9A2M9S8S3aG9R2S21R15A1A3S1S27S5G0SbR18S33S9S9R3A3A2A2MaR2A2S25R2S26GaS5G0SbR18S35S9S9R3A3A2A2A2A2A2S2S1S27S5G0R12A2MbS5G0S24S5G0SbR19S22R17A1A2A2R3A2A2McA2S25GcS26GbR10A2A2A2A1F_;F_;Fy;Fr;S48Vsegs;S41R16ScS1fR14A1MdA1MeRfA3R15S23R14S42GdSeGeA1S31SaSdGdA1S32SaS4eGeReA2S30SaA1A3A3S4fGeA1A4A2S2cG2S38R10S39S5cR12RfS5dS1eR12A1RfS59S1cR12G5A2MfA1A3A3S5aS1cR12G3A2R11GfRfA4A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Fa;Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' a elen nlit Hsp Hnr Hbel Helen Hmod HnZ Hn Hroom Hpl Hdisj Hnro Hxs.
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
  * unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS].
    assert (Ev : vms md' tp (after_sys_mem ms a (zero_range (ms_mem ms) a (mmap_n (ms_gpr ms 1))))
                 = after_sys_mem (vms md tp ms) a (zero_range (ms_mem (vms md tp ms)) a (mmap_n (ms_gpr ms 1)))).
    { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
      f_equal. apply functional_extensionality. intros x.
      unfold mrestrict. rewrite (hid_ext md md' tp) by reflexivity. rewrite !zero_range_at.
      destruct (in_range a (mmap_n (ms_gpr ms 1)) x) eqn:Ein; [|reflexivity].
      apply in_range_spec in Ein. rewrite En in Ein. rewrite (Hvis x Ein). reflexivity. }
    rewrite Ev. rewrite virt_unfold in Hspv.
    eapply (smatch_after_mmap_sym rho (ax_S A) tr (vms md tp ms) (vmd md));
      [exact Hspv | apply (proj2 (model_idle_vmd md')); exact Hh | exact Hbel | exact Helen | exact En | lia | exact Hnw | exact Hdisj | exact Hnro].
  * unfold md'. eapply (MI_with_vmmaps segs md _ tp nlit HMI); try reflexivity.
    -- cbn. apply ivs_wf_cons; [apply iv_wf_intro; rewrite En; exact Hnw | exact (proj1 (MI_ivs_wf segs md tp HMI))].
    -- cbn. exact (proj1 (proj2 (MI_ivs_wf segs md tp HMI))).
    -- cbn. intros r Hr. right. exact Hr.
    -- rewrite <- En. apply (used_maps_cons_le md _ a (mmap_n (ms_gpr ms 1))); [exact (MI_ivs_wf segs md tp HMI) | apply iv_wf_intro; rewrite En; exact Hnw | reflexivity | reflexivity].
    -- exact Hroom.
  * unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    -- apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) HX r Hr) as Y.
       unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
       apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    -- eapply sv_below_mono; [|exact Hb]. lia.
  * assert (Hag : agree_below (ss_next (ax_S A)) rho (rho_set_rw rho (ss_next (ax_S A)) a)) by (apply agree_below_set_rw; lia).
    pose proof (shadow_ok_stable A A rho (rho_set_rw rho (ss_next (ax_S A)) a) Hag Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh) as Hsh'.
    apply shadow_ok_transport_objs; [|exact Hsh']. cbn [ax_X ax_base ax_S ax_setS S_after ss_objs].
    intros x Hxw Hout _. apply outside_all_app. split; [exact Hout|]. constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, mmap_obj_sym. cbn [ob_base ob_lo ob_hi eval]. rewrite rho_set_rw_at.
    rewrite soff_lit_small by lia.
    assert (Helen' : eval (rho_set_rw rho (ss_next (ax_S A)) a) elen = eval rho elen) by (symmetry; apply (eval_agree (ss_next (ax_S A))); [exact Hag | exact Hbel]).
    unfold soff. rewrite Helen'. rewrite signed_small by lia. rewrite Helen. rewrite Z.add_0_r.
    assert (Hnl8 : nlit mod 8 = 0).
    { pose proof (Z.mod_divide nlit 4096 ltac:(lia)) as [Hd _]. destruct (Hd Hmod) as [q Hq]. rewrite Hq.
      replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
    refine (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) _ Hxs (xword_agree rho _ A x Hag Hwf Hxw)).
    rewrite Z.add_mod, (mod8_of_page _ Hal), Hnl8 by lia. reflexivity.
  * cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite (hid_ext md md' tp) in Hx by reflexivity. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a (mmap_n (ms_gpr ms 1)) x); [left; reflexivity|]. exact (Hhz x Hx).
Qed.

Lemma mmap_len_sym : ltac2:(tb__ "0|5|
S10S2dS6Q40M0A1M1A1S20S2dS3cA1M2S1dS3bS9S8S4bVsegs;R8R7R6S2cG2S38R5S39R4R3A2A4A5S0S9SfS1fR7A1ZbA2R3A3S0S8S5G0SbRaR4A2A2R3A3S0S8S29R4Z1000A2Z0M3A3S1S25G3R5A2S25R5S28Z2Z3eA2A2A2S1S2S0G1S1cR9U1A2M4S7G0G3A2A3A1S0S8S57G4A1R6A3A2F_;F_;F_;F_;F_;Fnlit;Felen;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (_ & G1 & _). rewrite H11 in G1.
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit) by (rewrite G1; exact Helen).
  split.
  - intros E. rewrite E in Hlenv. rewrite Z_to_bv_unsigned in Hlenv. change (bv_wrap 64 0) with 0 in Hlenv. lia.
  - unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia.
Qed.

Theorem triple1_mmap_rw_symA : ltac2:(tb__ "0|10|
S52OF_;S45S45S6Q40M0A1M1S45F_;S20S10S2dG1A1S9S8S47Vsegs;R9R8A3S4dVsegs;RaR9A3S46Vsegs;ScS1fR7A1A1RaA3S0S37S49A1S5eVsegs;S16S1fR8A1A1A2S36S49S4aA2A3S0S9SfS1fR9A1Z11A2S11ZdeA1A3S0S9SfS1fRaA1ZbA2R7A3S0S2bS15ScS1fRbA1A1R8A2S2fA3S0S8S5G0SbRbR9A2A2R8A3S0S8S29R9Z1000A2Z0M2A3S1S25G2RaA2S25RaS28Z2Z3eA2A2A2S2dS3cA1M3S1dS3bS4bVsegs;R11R10R12S2cG3S38R3S39R2R1A2A4A5R16R12R11R4R2A4S1S0S2bS51S1cR4U2A2S1cR4U3M4A2M5S1cR4U5A2A3S2fA3S1S0S2bS50G5A1S2eA3S1S2aS5bR3R12A2R10A2S1R16R13R12R5R3A4G1S56S1cR5U0A2S1cR5G4A2R4S1cR5U1M6A2R1A5S1SaS3aSaR1SdS1fR17A1A1A3S13S12R17R2A2S2cS8S8S5G0R4A2M7S26G7R14A2A4A2F_;Fo;S1G1S1S27S5G0R3A2M8S5G0R1A2M9A2S25G9S26G8R13A2A2A2S0S2bS14Vsegs;R2A2S2eA3F_;Fx;S1S34S9S9A2MaS8S3aGaR2S21R18A1A3S1S27S5G0SbR18S33S9S9R3A3A2A2MbR2A2S25R2S26GbS5G0SbR18S35S9S9R3A3A2A2A2A2A2S2S1S27S5G0R6A2McS5G0S24S5G0SbR19S22R1aA1A2A2R3A2A2MdA2S25GdS26GcR16A2A2A2A1F_;F_;Fy;Fr;R17R2S41R15ScS1fR16A1A1R2A3R14R7S3eS58S3dR5A1S1cR6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S55Vsegs;R14S44Vsegs;R13R10RfReA5S52S4S44Vsegs;R13S4cR11S11S5G0S40S3fA1A2A1A2R10RfR1A6S3G1G1S44Vsegs;R13R1A1S23R12S42S1fR12A1MeSeScGeA1MfA1S31SaSdGeA1S32SaS4eGfRfA2S30SaA1A3A3S4fGfA1A4A2S41R11GfR1A3R10R2A6La;A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo A rho tp elen nlit Hokf Hokp Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. apply (mmap_only_okA segs ms md _ Hh H222 Hlen Hmodb).
  - intros w' Hw. destruct (wstep_mmap_invA segs ms md _ Hh H222 Hlen Hmodb tr w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
      * eapply smatchA_after_mmap_obj_sym; eauto.
      * cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.

Theorem etriple_mmap_rw_symA : ltac2:(tb__ "0|10|
S45S6Q40M0A1M1S45F_;S20S10S2dG1A1S9S8S46Vsegs;ScS1fR5A1A1R7A3S0S37S49A1S5eVsegs;S16S1fR6A1A1A2S36S49S4aA2A3S0S9SfS1fR7A1Z11A2S11ZdeA1A3S0S9SfS1fR8A1ZbA2R5A3S0S2bS15ScS1fR9A1A1R6A2S2fA3S0S8S5G0SbR9R7A2A2R6A3S0S8S29R7Z1000A2Z0M2A3S1S25G2R8A2S25R8S28Z2Z3eA2A2A2S2dS3cA1M3S1dS3bS4bVsegs;RfReR10S2cG3S38R3S39R2R1A2A4A5R13R10RfR4R2A4S1S0S2bS51S1cR4U2A2S1cR4U3M4A2M5S1cR4U5A2A3S2fA3S1S0S2bS50G5A1S2eA3S1S2aS5bR3R10A2ReA2S3G1G1S1S56S1cR5U0A2S1cR5G4A2R4S1cR5U1A2M6R1A5S1SaS3aSaR1SdS1fR14A1A1A3S13S12R14R2A2S2cS8S8S5G0R3A2M7S26G7R11A2A4A2F_;Fo;S1G1S1S27S5G0R2A2M8S5G0R1A2M9A2S25G9S26G8R10A2A2A2S0S2bS14Vsegs;R2A2S2eA3F_;Fx;S1S34S9S9A2MaS8S3aGaR2S21R15A1A3S1S27S5G0SbR15S33S9S9R3A3A2A2MbR2A2S25R2S26GbS5G0SbR15S35S9S9R3A3A2A2A2A2A2S2S1S27S5G0R5A2McS5G0S24S5G0SbR16S22R17A1A2A2R3A2A2MdA2S25GdS26GcR13A2A2A2A1F_;F_;Fy;Fr;R14R1S41R12ScS1fR13A1A1R1A3R11R6S3eS58S3dR4A1G6R1A3R4A2A5A2A2A2A2La;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S53Vsegs;S44Vsegs;R10ReRdRcA5S52S3G1G1S44Vsegs;R11R1A1S23R10S42S1fR10A1MeSeScGeA1MfA1S31SaSdGeA1S32SaS4eGfRdA2S30SaA1A3A3S4fGfA1A4A2S41RfGfR1A3ReR2A6La;A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJ;").
Proof using .
  intros J Jo A rho tp elen nlit Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & a & Hpl & Hdisj & Hnro & Hxs & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
  exists a. split.
  - eapply smatchA_after_mmap_obj_sym; eauto.
  - cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End M.
