(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "of_nat"; "pow"; "sub"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "map_remove"; "vm_noaccess"; "VmMaps"; "page_size"; "vm_forget_range"; "with_vmmaps"; "m_vm_materialized"; "maps_subtract"; "vm_backing_used"; "vm_limit"; "event"; "region_free"; "vm_add_lazy"; "m_vm_lazy"; "page_in_ranges"; "page_outside_range"; "page_base"; "page_mem"; "@Corelib.Init.Datatypes"; "bool"; "list"; "pair"; "true"; "prod"; "length"; "option"; "None"; "fst"; "snd"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "sobj"; "ss_objs"; "valuation"; "ss_next"; "obj_range"; "ranges_disjoint"; "rm"; "agree_below"; "sv_below"; "ro_addr"; "sstate"; "@Stdlib.Lists.List"; "In"; "NoDup"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "sum_count"; "ivs_wf"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA2.F2"; "splice"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "unmap_range"; "in_range"; "zero_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "smatch_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "lazy_in_maps"; "tp_in_maps"; "unpaid"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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

Section F2.
Variable segs : list Segment.

Definition splice (m new : word -> option byte) (a n : word) : word -> option byte := ltac2:(tb__ "0|0|
S1Q40A1S26S2cS1Q8A1A1L_;S55Va;Vn;R1A3Vnew;R1A1Vm;R1A1X26x2Lx;").

Lemma smatch_pending_reframe : ltac2:(tb__ "0|8|
S35S3dS27S1eA1M0S4cS13S1Q40M1A1M2G2G2S2cS1Q8A1M3A1M4F_;S58Vsegs;R8R7S28G0S47R6S48R5R4A2A4A4S8S7S0G1R4A2S0G1R3A2A2ScZ2Z40A2A2S33S3eS33R1S34RaA1A3S38S37RcR2A2S28SfSfS0G1R7A2M5S7G5S0G1R6A2A2M6A4A2F_;Fo;G2S4S8G5S0G1R1A2M7A2S9G7G6A2A2S3S26S3cVsegs;R2A2S29A3S3G4R7R3A1S2dG3A1A3F_;F_;Fx;S58Vsegs;S4fRcS51S39RcA1R5R7R6A4A2RbS28G0S47RaS48S50R9S51S4dR9A1R5R7R6A4A2R8A2A4A4F_;F_;F_;F_;Fnew;Fn;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md a n new Hsp Hnw Hdisj Hnro.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (swf_objs S Hwf) as Hobjwf.
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split; [cbn; rewrite eval_set_rm; exact Hpend|].
  split; [exact Hhalt|]. split; [exact Hrom|].
  split.
  { intros x Hro. cbn [with_mem ms_mem]. unfold splice. destruct (in_range a n x) eqn:Hir.
    - apply in_range_spec in Hir. exact (Hnro x Hir Hro).
    - apply Hroc. exact Hro. }
  split; [intros r Hr; rewrite eval_set_rm; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_set_rm; apply Hfregs|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); [exact Hfcsr | rewrite eval_set_rm; exact Hfcsr]|].
  split; [unfold resv_match in *; cbn [with_mem ms_resv]; destruct (ss_resv S); destruct (ms_resv ms);
          rewrite ?eval_set_rm; exact Hresv|].
  split; [|apply Forall_forall; intros p Hp; apply holds_set_rm; exact (proj1 (Forall_forall _ _) Hfacts p Hp)].
  split; [|split].
  - apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
    pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
    eapply (obj_holds_set_rm_ext segs rho _ ms); [intros ?; reflexivity | | exact Ho].
    intros off Hoff. cbn [with_mem ms_mem]. unfold splice.
    pose proof (Hdisj o Hin) as D. pose proof (proj1 Ho) as HB.
    unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
    destruct (in_range a n _) eqn:Hir; [|reflexivity].
    apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
  - apply pairwise_disjoint_set_rm. exact Hpd.
  - intros x Hout. apply outside_all_set_rm in Hout. cbn [with_mem ms_mem set_rm rm]. unfold splice.
    destruct (in_range a n x); [reflexivity|]. apply Hfr. exact Hout.
Qed.

Lemma sum_count_remove_le : ltac2:(tb__ "0|4|
S27S2aS1Q40M0A1M1G1A2A1G1G1SfS26F_;M2G2S4bR5A1S3S26S1fS14R6R5A2R5R4A3S29A3SfS5S4S8S0G0R7A2M3R1A2S9R1S7G3S0G0R6A2A2A2A2A1S3S26R5R2A1S29A3S3S26R7R3A1S29A3F_;F_;Fx;S8S4aR4S14R8R7A2A2S4aR5R8A2A2F_;F_;F_;FP';FP;Fn;Faddr;Fl;").
Proof using .
  intros l addr n P P' Hwf Hfree HP. unfold map_remove in *.
  induction l as [|[b s] l IH]; [cbn; lia|].
  assert (Wl0 : ivs_wf l) by (intros q Hq; apply Hwf; right; exact Hq).
  pose proof (Hwf (b, s) (or_introl eq_refl)) as Wbs. unfold iv_wf, ivB, ivS in Wbs. cbn [fst snd] in Wbs.
  cbn [List.filter fst] in Hfree |- *.
  pose proof (zcount_nonneg P (ivB (b, s)) (Z.to_nat (ivS (b, s)))) as NN.
  destruct (negb (bv_eqb b addr)) eqn:Eb.
  - cbn [region_free] in Hfree. apply andb_true_iff in Hfree as [Hov Hfree]. cbn [sum_count].
    specialize (IH Wl0 Hfree).
    assert (LE : iv_count P' (b, s) <= iv_count P (b, s)); [|lia].
    unfold iv_count. apply zcount_mono. intros x Hx Hc. unfold ivB, ivS in Hx. cbn [fst snd] in Hx.
    pose proof (urange s). rewrite Z2Nat.id in Hx by lia.
    apply negb_true_iff in Hov. unfold iv_overlap in Hov. cbn [fst snd] in Hov.
    apply (HP x); [|exact Hc]. intros Hin.
    apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
  - cbn [sum_count]. specialize (IH Wl0 Hfree). unfold iv_count in NN |- *. lia.
Qed.

Lemma used_munmap_le : ltac2:(tb__ "0|5|
S13S16S1Q40M0A1M1G1S49R4A1S3S26S1fS14S12S11R5A1A1R3A2R3R2A3S29A3S3S27S2aG1G1A2A1M2S12R5A1S14S12S11R6A1A1R4A2A3S3G2S15R6A1S1bS15S11R7A1A1S0G0R5A2M3S7G3S0G0R4A2A2A3A3S8S1cS18S0G0R6A2M4S7G4G3A2S19R7R8A2A3A1S1cR8A1A2F_;F_;F_;F_;Fn;Faddr;Fh';Fm;").
Proof using .
  intros m h' addr n Hwf Hfree Hmaps Hna. pose proof Hwf as (Wm & Wn & Wl).
  pose proof (urange addr) as Ra. pose proof (urange n) as Rn.
  destruct (maps_subtract_sem _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Wn ltac:(lia)) as (Wn' & _ & Cn).
  destruct (maps_subtract_sem _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Wl ltac:(lia)) as (Wl' & _ & Cl).
  assert (Wm' : ivs_wf (map_remove (vm_maps (m_vmmaps m)) addr)) by (unfold map_remove; apply ivs_wf_filter; exact Wm).
  assert (Hwf' : model_ivs_wf (vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (with_vmmaps h' m))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna. split; [exact Wm' | split; [exact Wn' | exact Wl']]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf). model_proj. rewrite Hmaps, Hna.
  pose proof (filter_length_le (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized m)). pose proof page_size_pos.
  apply Z.add_le_mono; [|nia].
  apply (sum_count_remove_le _ addr n); [exact Wm | exact Hfree |].
  intros x Hx Hc. rewrite covered_app, Cn, Cl in Hc. rewrite covered_app.
  assert (Hr : in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x = false).
  { unfold in_rng. apply andb_false_iff. destruct (Z_lt_le_dec x (bv_unsigned addr)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  rewrite Hr, !andb_true_r in Hc. exact Hc.
Qed.

Lemma lazy_in_maps_munmap : ltac2:(tb__ "0|5|
S13S16S1Q40M0A1M1G1S49R4A1S5cR5A1G1S3eS2aG1G1A2M2S28G1G1R5R1A4S12S11R7A1A1M3A3S3G1R2R5A3F_;Fs;S3S27G2A1S12R6A1S14G3R5A2A3S5cS18S0G0R6A2M4S7G4S0G0R5A2A2S19R7R8A2A3A1F_;F_;F_;F_;Fn;Faddr;Fh';Fm;").
Proof using .
  intros m h' addr n (Wm & _ & Wl) H Huniq Hmaps lz sz Hin Hsz. unfold lazy_in_maps in H. model_proj.
  rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps in Hin. rewrite Hmaps.
  destruct (in_maps_subtract (lz, sz) _ _ _ Hin Wl) as ([b s] & Hr & H1 & H2 & H3). cbn [fst snd] in H1, H2, H3.
  pose proof (urange lz).
  destruct (H b s Hr ltac:(lia)) as (b' & s' & Hbs & X1 & X2).
  exists b', s'. split; [|lia]. unfold map_remove. apply filter_In. split; [exact Hbs|]. cbn [fst].
  destruct (bv_eqb b' addr) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E. subst b'.
  pose proof (Huniq s' Hbs) as ->. lia.
Qed.

Lemma tp_in_maps_munmap : ltac2:(tb__ "0|6|
S13S16S1Q40M0A1M1G1S27G1A1S5dR5R1A2G1S3eS2aG1G1A2M2S28G1G1R5R1A4S12S11R7A1A1A3S3G1R2R5A3F_;Fs;S3SfSaS0G0R5A2S17A2Z0A3M3G3S3S27G2A1S12R8A1S14S12S11R9A1A1R7A2A3S5dS18S0G0R8A2M4S7G4S0G0R7A2A2M5S19R9RaA2A3S59G4G5R6A3A2F_;F_;F_;F_;F_;Ftp;Fn;Faddr;Fh';Fm;").
Proof using .
  intros m h' addr n tp Htm Huniq Hal Hnl Hmaps p Hp. model_proj. rewrite Hmaps.
  unfold tp_forget in Hp. apply filter_In in Hp as [Hp Hout]. destruct (Htm p Hp) as (Hpal & b & s & Hbs & B1 & B2). split; [exact Hpal|].
  pose proof page_size_pos. pose proof (urange n). pose proof (urange addr). pose proof (urange p).
  unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout.
  assert (Hclear : bv_unsigned p + page_size <= bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned p).
  { pose proof (Z.div_mod (bv_unsigned addr) page_size ltac:(lia)) as Da. rewrite Hal in Da.
    pose proof (Z.div_mod (bv_unsigned n) page_size ltac:(lia)) as Dn. rewrite Hnl in Dn.
    pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp. rewrite Hpal in Dp.
    destruct Hout as [Hout|Hout]; [apply Z.leb_gt in Hout; left | apply Z.ltb_ge in Hout; right; exact Hout].
    assert (bv_unsigned p / page_size < bv_unsigned addr / page_size) by nia. nia. }
  exists b, s. split; [|lia]. unfold map_remove. apply filter_In. split; [exact Hbs|]. cbn [fst].
  destruct (bv_eqb b addr) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E. subst b.
  pose proof (Huniq s Hbs) as ->. lia.
Qed.

Lemma smatchA_after_munmap : ltac2:(tb__ "0|10|
S35S35S27S1Q40M0A1M1A1S45S27S1eA1M2S4cS13G2S16G1G1G1S31S10S5bVsegs;ReRcRbS28G2S47RaS48R9R8A2A4A5S3S27S2aG1G1A2M3A1M4S12R7A1S14S12S11R9A1A1R6A2A3S3G4S15R8A1S1bS15S11RaA1A1S0G0R7A2M5S7G5S0G0R6A2A2A3A3S3SfS1dR9A1S1dS11RbA1A1A3G1S3eG3S28G1G1RaR1A4S12S11RdA1A1M6A3S3G1R2RaA3F_;Fs;S3S26S1fS14G6RaA2RaR9A3S29A3S3SfSaS0G0RbA2S17A2Z0A3M7G7S8S7S0G0RdA2S0G0RcA2A2ScZ2Z40A2A2S33S3eS33R1S34S41R15A1A1A3S38S37R19R2A2S28SfSfS0G0R10A2M8S7G8S0G0RfA2A2A4A2F_;Fo;S2aS31S31A2M9SfS3eG9R2S42R17A1A3S4S8S0G0S32R1bS2eS31S31R3A3A2A2MaR2A2S9R2S7GaS0G0S32R1bS2fS31S31R3A3A2A2A2A2A2S5S4S8S0G0R13A2MbS0G0S46S0G0S32R1cS43R19A1A2A2R3A2A2McA2S9GcS7GbS0G0R12A2A2A2A2A1F_;F_;Fy;Frr;S3aS36S41R16A1A1S4fR19S54S39R19A1R10RfA3A2R18A3S5fS36S41R17A1A1RdA2S3S26S3bReRfA2S29A3S3G1S32R1bR10A2R11A3S5aVsegs;R1cS59S0G0R14A2MdS7GdGbA2MeR1bA3S44R1aS57S41R1aA1MfR11S34GfA1R10A4A2S28G2S47R16S48S53R18R12S54S4dR18A1R14R13A3A3S18GdGeS19R15R17A2A3A2A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e nx Hsp Hmaps Hna Hlim Huniq Hfree Hal Hnl Hend Hdisj Hxs Hag' Hnx He Hev.
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
      rewrite after_sys_mem_with_mem. unfold after_sys.
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
      - rewrite Hmaps. unfold map_remove. apply ivs_wf_filter. exact (proj1 Hivs).
      - rewrite Hna. apply maps_subtract_wf; [exact (proj1 (proj2 Hivs)) | lia]. }
    assert (HT' : List.NoDup tp') by (unfold tp', tp_forget; apply List.NoDup_filter; exact HT).
    unfold md'. apply (MI_intro segs).
    + exact HW. + exact HT'.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps. apply List.NoDup_filter. exact Hmat.
    + rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      intros p Hp. apply filter_In in Hp as [Hp Ho]. unfold tp', tp_forget. apply filter_In. split; [exact (Hsub p Hp) | exact Ho].
    + pose proof (used_munmap_le md h' a n Hivs Hfree Hmaps Hna) as U1. fold lo hi md1 in U1.
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
    + unfold md1, lo, hi. apply (lazy_in_maps_munmap md h' a n Hivs Hlm Huniq Hmaps).
    + unfold md1, tp', tp_forget, lo, hi. apply tp_in_maps_munmap; [exact Htm | exact Huniq | exact Hal | exact Hnl | exact Hmaps].
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

Lemma used_rereserve_le : ltac2:(tb__ "0|9|
S13S16S1Q40M0A1M1G1S49R4A1S3SfSaS0G0R3A2S17A2Z0M2A3M3G3S9G2S0G0R4A2A2S8S7S0G0R6A2S0G0R5A2A2ScZ2Z40A2A2S3S27S2aG1G1A2A1M4S12R8A1S12S11R9A1A1A3S3G4S15R9A1S1bS15S11RaA1A1S0G0R8A2M5S7G5S0G0R7A2A2A3A3S8S7S1cS20R9R8S18S0G0R9A2M6S7G6G5A2M7S19RaRbA2A3A3A1SeS17SdSbS2bG1S1aRbA1M8A2A1SbS2bG1S40G1S23G6G7A2G8A3A2A1A2A2A2S1cRbA1A2F_;F_;F_;F_;F_;F_;F_;Fn;Fa;Fh';Fm;").
Proof using .
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl).
  set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
  assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  assert (Hwf' : model_ivs_wf (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))).
  { unfold model_ivs_wf. model_proj. rewrite Hmaps, Hna, Hli.
    split; [exact Wm|split; [apply maps_subtract_wf; assumption|]].
    apply (ivs_wf_cons (a, n)); [exact Hend|apply maps_subtract_wf; assumption]. }
  rewrite (vm_backing_used_sem _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna, Hli.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)). pose proof page_size_pos.
  match goal with |- ?s1 + _ * _ + _ <= ?s2 + _ => assert (SS : s1 <= s2); [|nia] end.
  apply sum_count_mono. intros x Hx.
  rewrite covered_app in Hx. rewrite covered_app in Hx. rewrite Cn, Cl in Hx. rewrite covered_app.
  revert Hx. unfold covered at 2. cbn [existsb]. unfold in_iv, ivB, ivS. cbn [fst snd]. fold lo. fold hi.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence.
Qed.

Lemma unpaid_rereserve_le : ltac2:(tb__ "0|9|
S13S16S1Q40M0A1M1G1S27G1A1S49R5A1S3fG1R2A2S3fG1S1aR7A1A2G1S3eG1R1S1aR9A1A3S3eG1R2R6A3F_;Fp;S3SfSaS0G0R7A2S17A2Z0M2A3M3G3S9G2S0G0R8A2A2S8S7S0G0RaA2S0G0R9A2A2ScZ2Z40A2A2G1S3eG1R1RaA3S3SfSaS0G0R2A2M4S17A2G2A3F_;Fp;G1S3eG1R1RbA3S4S8S0G0ReA2M5G4A2S9G4S7G5S0G0RdA2M6A2A2A2S3S26S22R3S21R11A1A2S29A3F_;F_;Fp;S8SbS2bG1S5eS20RdRcS18G6S7G6S0G0RcA2A2M7S19ReRfA2A3A3RbA2A2A1S7SbS2bG1S5eRfRbA2A2A1SdSbS2bG1S1aRfA1M8A2A1SbS2bG1S40G1S23G6G7A2G8A3A2A1A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Fn;Fa;Fh';Fm;").
Proof using .
  intros m h' a n tp (Wm & Wn & Wl) HT Hmat Hsub Hal Hnl Hpos Hend Htal Htl.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  pose proof (urange n) as Rn. pose proof (urange a) as Ra. pose proof page_size_pos as Pps.
  set (matIn := List.filter (fun p => negb (page_outside_range lo hi p)) (m_vm_materialized m)).
  assert (Hsplit : (length (List.filter (page_outside_range lo hi) (m_vm_materialized m)) + length matIn = length (m_vm_materialized m))%nat).
  { unfold matIn. pose proof (filter_length_split (fun _ : word => true) (page_outside_range lo hi) (m_vm_materialized m)) as X.
    cbn [andb] in X.
    assert (L : forall l : list word, List.filter (fun _ => true) l = l) by (induction l; cbn; [reflexivity | rewrite IHl; reflexivity]).
    rewrite L in X. exact X. }
  assert (INCL : forall p, In p (unpaid (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m))) tp) -> In p (unpaid m tp ++ matIn)).
  { intros p Hp. unfold unpaid in Hp. rewrite m_vm_lazy_vm_add_lazy, m_vm_materialized_vm_add_lazy,
      m_vm_lazy_vm_forget_range, m_vm_materialized_vm_forget_range, m_vm_lazy_with_vmmaps, m_vm_materialized_with_vmmaps in Hp.
    apply filter_In in Hp as [Htp Hb]. apply andb_prop in Hb as [Hlz Hnm]. apply negb_true_iff in Hnm.
    apply in_or_app. destruct (page_mem p (m_vm_materialized m)) eqn:Em.
    - right. unfold matIn. apply filter_In. split; [apply page_mem_In; exact Em|].
      apply page_mem_In in Em. apply page_mem_false in Hnm. apply negb_true_iff.
      destruct (page_outside_range lo hi p) eqn:Eo; [|reflexivity]. exfalso. apply Hnm. apply filter_In. split; [exact Em | exact Eo].
    - left. unfold unpaid. apply filter_In. split; [exact Htp|]. rewrite Em, andb_true_r.
      rewrite page_in_ranges_app in Hlz. apply orb_prop in Hlz as [Hlz|Hlz].
      + apply Htl; [exact Htp|]. pose proof (Z_to_bv_bv_unsigned 64 p) as Ep.

        assert (Hpb : page_base p = p).
        { apply bv_eq. rewrite page_base_val. pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as Dp.
          rewrite (Htal p Htp) in Dp. lia. }
        rewrite <- Hpb in Hlz. apply (proj2 (in_interior_pages a n p Hal Hnl Hpos Hend)) in Hlz. exact Hlz.
      + apply page_in_ranges_spec in Hlz as (q & Hq & Hpq).
        destruct (in_maps_subtract q _ lo hi Hq Wl) as (r & Hr & Q1 & Q2 & _).
        apply page_in_range_spec in Hpq as [P1 P2]. apply page_in_ranges_spec. exists r. split; [exact Hr|]. apply page_in_range_spec. lia. }
  assert (ND : List.NoDup (unpaid (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m))) tp)) by (unfold unpaid; apply List.NoDup_filter; exact HT).
  pose proof (List.NoDup_incl_length ND INCL) as LEN. rewrite length_app in LEN. lia.
Qed.

Lemma smatchA_after_rereserve : ltac2:(tb__ "0|16|
S35S35S27S1Q40M0A1M1A1S45S27S1eA1M2S4cS13G2S16G1G1G1S31S10S5bVsegs;ReRcRbS28G2S47RaS48R9R8A2A4A5S3S27S2aG1G1A2M3A1M4S12R7A1S12S11R9A1A1A3S3G4S15R8A1S1bS15S11RaA1A1S0G0R7A2M5S7G5S0G0R6A2A2A3A3S3SfS1dR9A1S1dS11RbA1A1A3S3SfSaS0G0R9A2S17A2Z0M6A3M7G7S9G6S0G0RaA2A2S8S7S0G0RcA2S0G0RbA2A2ScZ2Z40A2A2S6G1G1S6G1G1S4S3eG3S28G1G1R2R1A4S12S11R12A1A1A3S4S8S0G0R2A2M8S0G0RfA2M9A2S8S7G9S0G0ReA2A2MaS7G8S0G0R1A2A2A2A2A2Ls;A2Lb;A2SfS4S8G9R1A2S9R1GaA2A2S3S2cS52A1S4eVsegs;R2Z1A3S2dS52A1A3F_;Fz;G1S3eG1R1R17A3S4S8S0G0R11A2MbG8A2S9G8S7GbS0G0R10A2A2A2A2S3S26S22R3S21R15A1A2S29A3F_;F_;Fp;S33S3eS33R1S34S41R17A1A1A3S38S37R1bR2A2S28SfSfS0G0R12A2McS7GcGbA2A4A2F_;Fo;S2aS31S31A2MdSfS3eGdR2S42R19A1A3S4S8S0G0S32R1dS2eS31S31R3A3A2A2MeR2A2S9R2S7GeS0G0S32R1dS2fS31S31R3A3A2A2A2A2A2S5S4S8S0G0R15A2MfS0G0S46S0G0S32R1eS43R1bA1A2A2R3A2A2M10A2S9G10S7GfS0G0R14A2A2A2A2A1F_;F_;Fy;Frr;G1S26S2cS1Q8M11A1M12A1M13L_;S25S24R1A1R1aA2S30G12S2G11G6A2A2S2dG12A1X26x2Lx;G1G13Fx;S3aS36S41R19A1A1S4fR1cS51S39R1cA1R1R13R12A4A2R1bA3S5fS36S41R1aA1A1R10A2S3S26S3bR11R12A2S29A3S3G1S32R1eR13A2R14A3S5aVsegs;R1fR1eS44R1dS57S41R1dA1M14R14S34G14A1R13A4A2S28G2S47R19S48S53R1bR15S56S4dR1bA1R17R16A3A3S20R17R16S18S0G0R17A2M15S7G15S0G0R16A2A2S19R18R1aA2A3A3A2A4A5F_;F_;F_;F_;Tnew;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnx;Fe;Fr;Fn;Fa;Fh';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A tr ms md tr' h' a n r e nx Hsp Hmaps Hna Hlim Hal Hnl Hpos Hend Hmap Hseg Htl Hdisj Hxs new Hag' Hnx He Hev.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  pose proof HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  pose proof Hsp as (Hspv & _ & Hwf & Hsh & Hhz). rewrite virt_unfold in Hspv.
  pose proof (urange a) as Ra. pose proof (urange n) as Rn. pose proof page_size_pos as Pps.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  set (md1 := with_vmmaps h' md). set (md2 := vm_forget_range lo hi md1). set (md' := vm_add_lazy a n md2).
  assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
  assert (Hnro : forall x : word, lo <= bv_unsigned x < hi -> ro_addr segs x = false).
  { intros x Hx. unfold ro_addr. rewrite (Hseg (bv_unsigned x) Hx). reflexivity. }

  assert (HIN : forall x : word, lo <= bv_unsigned x < hi -> hid md' tp x = negb (page_mem (page_base x) tp)).
  { intros x Hx. unfold md'. rewrite hid_add_lazy. destruct (page_in_aligned_range a n x Hal Hnl Hx) as [P1 P2].
    unfold md2. rewrite (hid_forget_in_range md1 lo hi tp x Wl1 ltac:(lia) ltac:(lia)). cbn [orb].
    rewrite (proj1 (in_interior_pages a n x Hal Hnl Hpos Hend) Hx). reflexivity. }
  assert (HOUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> hid md' tp x = hid md tp x).
  { intros x Hx. unfold md'. rewrite hid_add_lazy.
    destruct (page_in_ranges (page_base x) (lazy_interior a n)) eqn:Ep.
    { exfalso. apply Hx. apply (proj2 (in_interior_pages a n x Hal Hnl Hpos Hend)). exact Ep. }
    rewrite andb_false_l, orb_false_r. unfold md2. rewrite (hid_forget_outside md1 lo hi tp x Wl1 ltac:(lia) (page_out_of_aligned_range a n x Hal Hnl Hx)).
    unfold md1. rewrite (hid_ext md (with_vmmaps h' md) tp) by reflexivity. reflexivity. }
  assert (Hh' : m_halted md' = m_halted md).
  { unfold md', md2, md1, vm_add_lazy, vm_forget_range. rewrite !m_halted_with_vm_backing. reflexivity. }

  assert (Ev : vms md' tp (after_sys_mem ms r (zero_range (ms_mem ms) a n))
               = after_sys_mem (vms md tp ms) r (splice (ms_mem (vms md tp ms)) new a n)).
  { unfold vms, restrict, after_sys_mem. cbn [ms_regs ms_fregs ms_pc ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    f_equal. apply functional_extensionality. intros x. unfold mrestrict, splice. rewrite zero_range_at.
    destruct (in_range a n x) eqn:Ein.
    - apply in_range_spec in Ein. rewrite (HIN x Ein). unfold new. destruct (page_mem (page_base x) tp); reflexivity.
    - assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
      rewrite (HOUT x Hn). reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS]. rewrite Ev.
    pose proof (smatch_pending_reframe rho (ax_S A) tr (vms md tp ms) (vmd md) a n new Hspv Hend Hdisj
                  ltac:(intros x Hx Hro; rewrite (Hnro x Hx) in Hro; discriminate)) as Hsp1.
    pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag' Hsp1) as Hsp2.
    rewrite after_sys_mem_with_mem. unfold after_sys.
    eapply smatch_after_sys; [exact Hsp2 | | exact Hnx | exact He | exact Hev | | |].
    + apply (proj2 (model_idle_vmd md')). rewrite Hh'. exact Hh.
    + apply forallb_forall. intros o Ho. eapply obj_wf_mono; [exact Hnx|]. exact (proj1 (forallb_forall _ _) (swf_objs _ (smatch_pendingA_swf segs _ _ _ _ Hsp)) o Ho).
    + apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
    + exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2).
  -
    cbn [cfg_model cfg_ms snd fst].
    assert (Hwf1 : model_ivs_wf md1).
    { unfold md1. apply model_ivs_wf_with_vmmaps; [exact Hivs | rewrite Hmaps; exact (proj1 Hivs) |].
      rewrite Hna. apply maps_subtract_wf; [exact (proj1 (proj2 Hivs)) | lia]. }
    assert (Hwf2 : model_ivs_wf md2) by (unfold md2; apply model_ivs_wf_vm_forget_range; [lia | exact Hwf1]).
    unfold md'. apply (MI_intro segs).
    + exact HW. + exact HT.
    + rewrite m_vm_materialized_vm_add_lazy. unfold md2. rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      apply List.NoDup_filter. exact Hmat.
    + rewrite m_vm_materialized_vm_add_lazy. unfold md2. rewrite m_vm_materialized_vm_forget_range. unfold md1. rewrite m_vm_materialized_with_vmmaps.
      intros p Hp. apply filter_In in Hp as [Hp _]. exact (Hsub p Hp).
    + pose proof (used_rereserve_le md h' a n Hivs Hal Hnl Hpos Hend Hmaps Hna) as U1. fold lo hi md1 md2 in U1.
      pose proof (unpaid_rereserve_le md h' a n tp Hivs HT Hmat Hsub Hal Hnl Hpos Hend
                    ltac:(intros p Hp; exact (proj1 (Htm p Hp))) Htl) as U2. fold lo hi md1 md2 in U2.
      assert (Hl' : vm_limit (m_vmmaps (vm_add_lazy a n md2)) = vm_limit (m_vmmaps md)).
      { rewrite m_vmmaps_vm_add_lazy. unfold md2. rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps. exact Hlim. }
      rewrite Hl'. unfold paid. unfold paid in Hpaid. nia.
    + rewrite m_vm_lazy_vm_add_lazy. apply lazy_clear_app; [apply lazy_clear_interior; assumption|].
      unfold md2. rewrite m_vm_lazy_vm_forget_range. unfold md1. rewrite m_vm_lazy_with_vmmaps. apply lazy_clear_pieces; [exact (proj2 (proj2 Hivs)) | exact Hlc].
    + apply model_ivs_wf_vm_add_lazy; [exact Hend | exact Hwf2].
    + apply lazy_in_maps_add_lazy; [| exact Hend |].
      * unfold md2. apply lazy_in_maps_forget; [exact Wl1|]. unfold md1. apply lazy_in_maps_with_vmmaps_grow; [exact Hlm | rewrite Hmaps; intros rr Hr; exact Hr].
      * unfold md2. rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps, Hmaps. exact Hmap.
    + intros p Hp. destruct (Htm p Hp) as (Hpal & b & s0 & Hbs & X). split; [exact Hpal|]. exists b, s0.
      rewrite m_vmmaps_vm_add_lazy. unfold md2. rewrite m_vmmaps_vm_forget_range. unfold md1. rewrite m_vmmaps_with_vmmaps, Hmaps. split; [exact Hbs | exact X].
  -   unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  -
    set (rho1 := set_rm rho (splice (rm rho) new a n)) in *.
    assert (Hsh1 : shadow_ok rho1 A).
    { eapply (shadow_ok_transport rho rho1 A A); [reflexivity | apply eval_set_rm | intros; unfold rho1; rewrite !eval_set_rm; split; reflexivity | | exact Hsh].
      intros x Hxw Hout Hdef. split; [apply outside_all_set_rm; exact Hout|].
      unfold rho1. cbn [set_rm rm]. unfold splice.
      destruct (in_range a n _) eqn:E; [|reflexivity]. exfalso. apply in_range_spec in E.
      exact (xword_avoid_aligned rho A _ _ x (mod8_of_page _ Hal) (mod8_of_pages _ _ Hal Hnl) Hxs Hxw E). }
    exact (shadow_ok_stable A (ax_setS A (S_after (ax_S A) e (ss_objs (ax_S A)) nx)) rho1 rho' Hag' Hwf (smatch_pendingA_swf segs _ _ _ _ Hsp) eq_refl eq_refl eq_refl Hsh1).
  -
    cbn [cfg_model cfg_ms snd]. intros x Hx. rewrite after_sys_memq, zero_range_at.
    destruct (in_range a n x) eqn:E; [left; reflexivity|].
    assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros H; apply (proj2 (in_range_spec a n x)) in H; congruence).
    rewrite (HOUT x Hn) in Hx. destruct (Hhz x Hx) as [H0|[H1 H2]]; [left; exact H0 | right]. split; [exact H1|].
    unfold md', md2, md1. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, Hna. cbn [cfg_model snd] in H2.
    destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi (proj1 (proj2 Hivs)) ltac:(lia)) as (_ & _ & Cn).
    rewrite Cn, H2. cbn [andb]. apply negb_true_iff. unfold in_rng. apply andb_false_iff.
    destruct (Z_lt_le_dec (bv_unsigned x) lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

End F2.