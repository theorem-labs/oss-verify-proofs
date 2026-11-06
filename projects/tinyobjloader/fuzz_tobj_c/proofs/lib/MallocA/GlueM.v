(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "list"; "nat"; "bool"; "option"; "true"; "pair"; "Some"; "app"; "fst"; "nil"; "cons"; "length"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "rm"; "ss_objs"; "eval"; "sstate"; "ss_next"; "agree_below"; "mkSS"; "obj_range"; "rw"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "ranges_disjoint"; "rl"; "pairwise_disjoint"; "rd"; "rom_ok"; "smatch"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "div"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "ax_X"; "ax_base"; "axwf"; "mkAX"; "@Stdlib.Lists.List"; "In"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "carved"; "cells_in_view"; "cells_inside"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM.WithSegs"; "carve_spec"; "rho_sets"; "carve_obj"; "set_next"; "xwords_clear"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "w_tr"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymFrame SymEntail SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma smatchA_agree : ltac2:(tb__ "0|0|
S12S12S1S2aQ40A1A1S3dS0S1S5dA1S5bA2S18S17S3cR2A1A1R5R4A3S3bVsegs;R6R4R3R2A5S3bVsegs;R6R5R4R3A5F_;F_;Fw;FA;Ftp;Frho';Frho;").
Proof using .
  intros rho rho' tp A w Hag (Hsm & HMI & Hwf & Hsh & Hhz).
  split; [eapply smatch_agree; eauto|]. split; [exact HMI|]. split; [exact Hwf|]. split; [|exact Hhz].
  eapply (shadow_ok_stable A A rho rho'); eauto. exact (proj1 Hsm).
Qed.

Lemma SPA_agree : ltac2:(tb__ "0|0|
S3aS12S12S1S2aQ40A1A1S3dS4fS18S17S3cR2A1A1R5R4A3R7R6R4S51R2A1S5aS50R2A1A1A4R8R6R5S51R3A1S5aS50R3A1A1A4F_;S39Vsegs;R8R4R7R5R3A6S39Vsegs;R9R5R7R6R4A6F_;F_;F_;Fw;FA;Ftp;Frho';Frho;FJ;").
Proof using .
  intros J rho rho' tp A w Hag HJ [Hsm Hk]. split; [eapply smatchA_agree; eauto | exact (HJ Hk)].
Qed.

Fixpoint rho_sets (rho : valuation) (l : list (positive * word)) : valuation :=
  match l with [] => rho | (i, v) :: t => rho_sets (rho_set_rw rho i v) t end.

Lemma rm_rho_sets : ltac2:(tb__ "0|1|
S12S1S0SfS2aQ40A1M0A2A1S2dG0S4S2aQ8A1A1F_;S13S4bR2R1A2A1S13R2A1A3Fl;Frho;").
Proof. intros rho l. revert rho. induction l as [|[i v] t IH]; intros rho; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma rl_rho_sets : ltac2:(tb__ "0|0|
S12S1S0SfS2aQ40A1A2A1S2dSfS1S2aQ8A1A1F_;S25S4bR2R1A2A1S25R2A1A3Fl;Frho;").
Proof. intros rho l. revert rho. induction l as [|[i v] t IH]; intros rho; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma rw_rho_sets_other : ltac2:(tb__ "0|3|
S12S1S0SfS2aQ40A1M0A2M1A1SfG0S2fS43G1S6SfG0R2R1A4M2R3A3A1Fv;SfG0S43G1G2R5A3S2fS2dSfR3R5A3A1F_;Fv;Fj;S2dG0S1bS4bR5R4A2R3A2S1bR5R3A2A3F_;F_;Fi;Fl;Frho;").
Proof.
  intros rho l. revert rho. induction l as [|[j v] t IH]; intros rho i Hn Hne; [reflexivity|].
  cbn. rewrite IH.
  - unfold rho_set_rw. cbn. destruct (Pos.eqb i j) eqn:E; [|reflexivity].
    apply Pos.eqb_eq in E. subst. exfalso. exact (Hne j v (or_introl eq_refl) eq_refl).
  - intros v' Hin. exact (Hn v' (or_intror Hin)).
  - intros j' v' Hin. exact (Hne j' v' (or_intror Hin)).
Qed.

Lemma agree_below_rho_sets : ltac2:(tb__ "0|2|
SfS12S1S0SfS2aQ40A1M0A2M1A1SfG0S43G1S6SfG0R2R1A4R3A3S58R6R3A2F_;Fv;Fj;S18R4R3S4bR3R2A2A3F_;Fl;Frho;Fn;").
Proof.
  intros n rho l Hl. split; [|split; [intros; rewrite rl_rho_sets; reflexivity | intros; rewrite rm_rho_sets; reflexivity]].
  intros i Hi. symmetry. apply rw_rho_sets_other.
  - intros v Hin. pose proof (Hl i v Hin). lia.
  - intros j v Hin. pose proof (Hl j v Hin). lia.
Qed.

Lemma rw_rho_sets_in : ltac2:(tb__ "0|2|
S12S1S0SfS2aQ40A1M0A2M1A1SfG0S44SfS53G1SfS9SfG0A2R3A4A2S43G1S6SfG0R3R2A4R4A3S2dG0S1bS4bR6R5A2R4A2R3A3F_;F_;Fv;Fi;Fl;Frho;").
Proof.
  intros rho l. revert rho. induction l as [|[j u] t IH]; intros rho i v Hnd Hin; [destruct Hin|].
  cbn in Hnd. inversion Hnd as [|x ll Hnotin Hnd']; subst.
  destruct Hin as [E|Hin].
  - injection E as -> ->. cbn. rewrite rw_rho_sets_other.
    + unfold rho_set_rw. cbn. rewrite Pos.eqb_refl. reflexivity.
    + intros v' Hin'. apply Hnotin. apply in_map_iff. exists (i, v'). auto.
    + intros j' v' Hin' ->. apply Hnotin. apply in_map_iff. exists (i, v'). auto.
  - cbn. apply IH; assumption.
Qed.

Lemma SPA_select : ltac2:(tb__ "0|3|
S3aS12S3dS1S2A1S1S2aQ40A1A1S4fS39Vsegs;R6R4R5R2R1A6S2dS3S5fR4A1S5A3S2S43S2R1R6A3S59R2ScS10S14S3cR8A1M0A1M1A2M2A2F_;Fi;S2S59R1G2A2S43S2R2R8A3F_;Fi;S39Vsegs;RaS3eR8S61G0S60G1R7A2A2A2R9R6R5A6F_;F_;F_;F_;Fw;Ftp;Fidxs;FA;Frho;FJ;").
Proof using .
  intros J rho A idxs tp w [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hnd Hlt Hcov. split; [|exact Hk].
  split; [|split; [exact HMI | split; [unfold axwf in *; cbn; exact Hwf | split; [|exact Hhz]]]].
  - unfold virt in *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in *. apply smatch_select; assumption.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_setS ax_S ss_objs set_objs].
    intros x _ Hout _. unfold outside_all in *. apply Forall_forall. intros o Ho.
    apply (proj1 (Forall_forall _ _) Hout). eapply select_In; eauto.
Qed.

Definition xwords_clear (rho : valuation) (A : axst) (lo' hi' : Z) : Prop := ltac2:(tb__ "0|5|
S0S11S11A2M0SeSeS43G0R3S3fVA;A1A3S2eS32S2bQ40M1S15Vrho;S9S11S11R4A3A2A2M2R3A2S33R3S31G2S2bG1S15Vrho;SdS11S11R4A3A2A2A2A2A2S2eS32Z0R3A2S33R3Z8M3A2A2S2fS2eS32Vlo';S31S37S36S31S2bG1S15Vrho;S40VA;A1A2A2S36R5G3A2A2G3A2G3A2R4A2M4A2S33G4Vhi';A2A2A1F_;F_;F_;Fj;Fy;Frr;").

Lemma xwords_clear_nil : ltac2:(tb__ "0|0|
S12S16S11SeSeS4eR5S42R4SaS0S11S11A2A1R3A3R2R1A4Fhi;Flo;Fb;FS;Frho;").
Proof. intros rho S b lo hi rr y j Hin. destruct Hin. Qed.

Lemma SPA_carve_obj : ltac2:(tb__ "0|4|
S3aS12S3dS1S2aQ40M0A1A1S4fS11SeSeS1S0S0SeS2A2S11A2A1SfS39Vsegs;RaR8R9R7R6A6S3cR9A1S16S19S20R1A1S21R1A1S1eR1A1S1dR1A1S22R1A1S8S10S14R1A1SbS10S46R7R6R5R4A4SaS10A1A3A3S1cR1A1R3S1fR1A1A9S16S2dS3S23R1A1S5A3S58S17R3A1R5A2S2bG0S15ReRaA2A2SeS32S35S34Z2M1Z3fA2M2A1RaA2S32RbRaA2S33RbG2A2S33S38RcRdA2G2A2S32Z0S31R5ReA2A2S32S31R6ReA2S34G1Z40A2A2S48R10RfReA3S52S10S10S24S1aR17R1A2S6SeSeS31R9R12A2S31R9R11A2A4A2Lo';S14RcA1A3SeS2eS32R13R1A2S33R1R12A2A2S2eS2dS3S49Vsegs;S13R19A1S2cG0S31RbR2A2A2A3S5A3S30S2aQ8A1M3G3S2dS4G3A1S45Vsegs;S13R1aA1S2cG0S31RcR3A2A2A3S7G3R1A2A3Lx;A2A2F_;Foff;S47R18S45Vsegs;S13R18A1A2RaR11A4S4eR19R18S31RbR14A2S31RbR13A2A4S39Vsegs;R1bS3eR19RfA2R1aR18R17A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';TS;F_;Fnx;Fcs;Fhi;Flo;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w base lo hi cs nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx b Hs1 Hs2 Hs3 Hs4 Hlo Hhi Hins Hdisj Hview Hcells Hxs.
  subst S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    exact (smatch_carve_obj segs rho (ax_S A) _ base lo hi cs nx Hsm Hwf' Hs1 Hs2 Hs3 Hs4 Hlo Hhi Hins Hdisj Hview Hcells).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma rm_absorb_out : ltac2:(tb__ "0|0|
S12S1S10A1S54S2aQ40A1S2fS57R4R3R1A3A1S2dS4S2aQ8A1A1S13S56R5R4R3A3R2A2S13R5R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a Hn. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho R a) as [Hi|]; [exfalso; exact (Hn Hi) | reflexivity].
Qed.

Lemma rm_absorb_in : ltac2:(tb__ "0|0|
S12S1S10A1S54S2aQ40A1S57R4R3R1A3S2dS4S2aQ8A1A1S13S56R5R4R3A3R2A2S55R3R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a Hi. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho R a) as [|Hn]; [reflexivity | exfalso; exact (Hn Hi)].
Qed.

Lemma rd_of_absorb_in : ltac2:(tb__ "0|0|
S12S1S10A1S54S2aQ40A1S28Vsegs;R2A2S57R5R4R2A3S2dS4S2aQ8A1A1S45Vsegs;S13S56R6R5R4A3A1R3A3S27R4R3A2A3F_;F_;Fa;Fms;FR;Frho;").
Proof using .
  intros rho R ms a Hrom Hi. unfold rd_of. rewrite (rm_absorb_in rho R ms a Hi).
  unfold rd, ms_read_byte. destruct (ms_mem ms a); [reflexivity|]. symmetry. apply Hrom.
Qed.

Lemma absorb_carved_cells : ltac2:(tb__ "0|5|
S12S16S1S5dA1M0S54S5eS1S10A1M1G1S11SeSeS1S0S0SeS2A2S11A2A1S29Vsegs;RbRaS6G0S5bR9S5cR8R7A2A4A4S2dG1S14RbA1S8S10R7R6A3A3S43S10S46R6R5R4R3A4R7A3S2bQ40M2S15ReR7A2A2SeS32S35S34Z2Z3fA2M3A1R7A2S32R8R7A2S33R8G3A2S48RaR9R8A3S56R13RdR10A3S12S2eS47R1S45Vsegs;S13R1A1A2R6RaA4SeS2eS32RdR1A2S33R1RcA2A2S30S2aQ8A1M4G4S2dS4G4A1S45Vsegs;S13R4A1S2cG2S31R9R3A2A2A3S7G4R1A2A3Lx;A2F_;Foff;A2Trho';F_;F_;F_;F_;Tb;F_;F_;F_;Fcs;Fhi;Flo;Fbase;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md objs R base lo hi cs Hsm Ho Hin b Hs1 Hs3 Hs2 Hins rho'.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
  pose proof (proj1 (Forall_forall _ _) HallR _ Hin) as Hoh.
  unfold obj_holds, obj_lo_of, obj_hi_of, carved in Hoh. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hoh. fold b in Hoh.
  rewrite !soff_lit_small in Hoh by lia.
  destruct Hoh as (Hbnd & Hwv & Hcl & Hdf & _).
  assert (RNG : forall off, lo <= off < hi -> in_ranges rho R (Z_to_bv 64 (b + off))).
  { intros off Hoff. exists (carved base lo hi cs). split; [exact Hin|].
    unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi]. fold b.
    rewrite !soff_lit_small by lia. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  split.
  - unfold cells_in_view. apply Forall_forall. intros [[off k] v] Hc' j Hj.
    assert (Hinl : In (mkCell (SLit off) (Z.of_nat k) v) (lit_cells cs)).
    { clear -Hc'. induction cs as [|[[o' k'] v'] t IH]; [destruct Hc'|]. destruct Hc' as [E|Hc']; [injection E as -> -> ->; left; reflexivity | right; apply IH; exact Hc']. }
    pose proof (proj1 (Forall_forall _ _) Hcl _ Hinl) as Hch. unfold cell_holds in Hch. cbn [c_off c_width c_val] in Hch.
    pose proof (proj1 (Forall_forall _ _) Hins _ Hc') as Hci. cbn beta iota zeta in Hci. destruct Hci as (Hci1 & Hci2 & Hci3).
    rewrite !soff_lit_small in Hch by lia. destruct Hch as (Hc1 & Hc2 & Hrb). rewrite Nat2Z.id in Hrb.
    unfold rho'. rewrite eval_absorb.
    rewrite (rd_of_absorb_in rho R ms _ Hrom) by (replace (b + off + Z.of_nat j) with (b + (off + Z.of_nat j)) by lia; apply RNG; lia).
    pose proof (rd_bytes_nth ms k (oaddr rho base off) _ j Hrb Hj) as X.
    rewrite oaddr_unsigned in X by lia. fold b in X.
    replace (b + off + Z.of_nat j) with (b + off + Z.of_nat j) in X by lia. apply X. lia.
  - intros off Hoff. unfold rho'. rewrite (rd_of_absorb_in rho R ms _ Hrom (RNG off Hoff)).
    destruct (covered_dec rho (lit_cells cs) off) as [Hcov|Hncov].
    +
      unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hic).
      pose proof (proj1 (Forall_forall _ _) Hcl _ Hcin) as Hch. unfold cell_holds, in_cell in Hch, Hic.
      destruct Hch as (Hc1 & Hc2 & Hrb).
      pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho base (soff rho (c_off c))) _ (Z.to_nat (off - soff rho (c_off c))) Hrb ltac:(lia)) as X.
      rewrite oaddr_unsigned in X by lia. fold b in X.
      replace (b + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c)))) with (b + off) in X by lia.
      eexists. apply X. lia.
    + exact (Hdf off Hoff Hncov).
Qed.

Definition set_next (S : sstate) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S19S20VS;A1S21VS;A1S1eVS;A1S1dVS;A1S22VS;A1S14VS;A1S1cVS;A1Vnx;S1fVS;A1A9").

Lemma SPA_set_next : ltac2:(tb__ "0|0|
S3aS12S3dSfS1S2aQ40A1A1S4fS39Vsegs;R6R4R5R2R1A6S2dS3S41S3eR5S4dS3cR5A1R4A2A2A1S5A3S2dS3S23S4dS3cR6A1R5A2A1S5A3S39Vsegs;R9S3eR7S4dS3cR7A1R6A2A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fnx;FA;Frho;FJ;").
Proof using .
  intros J rho A nx tp w [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hax Hswf. split; [|exact Hk].
  split; [|split; [exact HMI | split; [exact Hax | split; [|exact Hhz]]]].
  - unfold virt in *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in *.
    destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
    unfold smatch. cbn. repeat (split; [assumption|]). exact Hfa.
  - unfold shadow_ok in *. cbn. exact Hsh.
Qed.

Definition carve_spec : Type := ltac2:(tb__ "0|0|
S0S0S0S11SeA2SeA2S1S0S0SeS2A2S11A2A1A2").
Definition carve_obj (k : carve_spec) : sobj := ltac2:(tb__ "0|3|
S0S0S0S11SeA2M0SeA2M1S1S0S0SeS2A2S11A2A1M2A2S10Lk;Vk;G1G2G1S10Lp;R2G0SeG0S10Lp0;R2S11SeS46R2R1R3R5A4Llo;Lbase;X0x1Lhi;Lp0;X0x1Lcs;Lp;X0x1").

Lemma SPA_carve_list : ltac2:(tb__ "0|9|
S3aS12S3dS1S2aQ40M0A1A1S4fS1S4aA1SfS39Vsegs;R7R5R6R4R3A6S3cR6A1S16S19S20R1A1S21R1A1S1eR1A1S1dR1A1S22R1A1S8S10S14R1A1S53S4aS10S4cR4A4A3S1cR1A1R3S1fR1A1A9S16S2dS3S23R1A1S5A3S58S17R3A1R5A2S52S4aS4aS0S0S0S11SeA2M1SeA2M2S1S0S0SeS2A2S11A2A1M3A2OLk;R1G2G3G2OLp;R2G1SeG1OLp0;R2S11SeS2bG0S15R12R2A2A2SeS2eS32S35S34Z2M4Z3eA2M5A1R2A2S2eS32R2R4A2S2eS33R4G5A2S2eS32Z0S31R1R2A2M6A2S2eS32S31R1R4A2M7S34G4Z40A2A2S2eS48R2R4R6A3S2eSeS2eS32R3R1A2S33R1R5A2A2S2eS2dS3S49Vsegs;S13R15A1S2cG0S31R3R2A2A2A3S5A3S30S2aQ8A1M8G8S2dS4G8A1S45Vsegs;S13R16A1S2cG0S31R4R3A2A2A3S7G8R1A2A3Lx;A2A2F_;Foff;S2eS47R13S45Vsegs;S13R13A1A2R1R6A4S4eR13R12G6G7A4A2A2A2A2A2A2A2A2Tb;Llo;Lbase;X0x1Lhi;Lp0;X0x1Lcs;Lp;X0x1Lk;R7A3S52S10S10S52S10S10S24S1aReR1A2S1aReR2A2A2Lo';S14R6A1A3Lo;S53S4aS10S4cR8A4A3S26RdS53S4aS10S4cR9A4A2S39Vsegs;RfS3eRdR6A2ReRcRbA6F_;F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;FA;Frho;FJ;").
Proof using .
  intros J rho A tp w N nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S S' Hwf' Hnx HN HX HP. subst S.
  split; [|exact Hk].
  destruct w as [tr [ms md]].
  assert (Hrom : rom_ok segs (vms md tp ms)).
  { unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). }
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_extend_objs segs rho (ax_S A) tr (vms md tp ms) (vmd md) (map carve_obj N) nx Hsm Hwf'); [|exact HX|exact HP].
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk').
    pose proof (proj1 (Forall_forall _ _) HN k Hk') as K. destruct k as [[[base lo] hi] cs]. cbn [carve_obj].
    destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & _).
    apply obj_holds_frame_lit; auto.
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HXw Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HXw rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk').
    pose proof (proj1 (Forall_forall _ _) HN k Hk') as K. destruct k as [[[base lo] hi] cs]. cbn [carve_obj].
    destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & Hxs). cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

End WithSegs.
