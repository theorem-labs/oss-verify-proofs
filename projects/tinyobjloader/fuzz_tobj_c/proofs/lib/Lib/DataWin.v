(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "cell"; "SLit"; "c_off"; "c_width"; "valuation"; "rom_ok"; "DImage"; "ob_cells"; "rd"; "rd_bytes"; "rm"; "smatch"; "ss_objs"; "sstate"; "agree_below"; "mkObj"; "mkSS"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_range"; "obj_wf"; "ranges_disjoint"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sv_eqb"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "andb"; "bool"; "false"; "true"; "option"; "list"; "orb"; "app"; "cons"; "nat"; "nil"; "pair"; "prod"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "le"; "add"; "lt"; "pow"; "ltb"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.DW"; "win_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin"; "cell_in"; "cell_out"; "subwin"; "subwin_ok"; "@Stdlib.Lists.List"; "forallb"; "filter"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCall SymBytes SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cell_in (lo hi : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S3S2cLx;S7Vc;A1S0S2bS38Vlo;R1A2S38S3aR1S8Vc;A1A2Vhi;A2A2Lo;S1S2dLi;S45S3S3S2dLb;La;M0Lop;M1G1S46G0Lop;M2G2S2cS2S3S2dLa;Lw;Lsgn;S1S3S0S2dLk;Li;Ll;X3x8").

Definition cell_out (lo hi : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S3S2cLx;S7Vc;A1S0S31S38S3aR1S8Vc;A1A2Vlo;A2S38Vhi;R1A2A2Lo;S1S2dLi;S45S3S3S2dLb;La;M0Lop;M1G1S46G0Lop;M2G2S2cS2S3S2dLa;Lw;Lsgn;S1S3S0S2dLk;Li;Ll;X3x8").

Definition subwin (OD : sobj) (lo hi : Z) : sobj := ltac2:(tb__ "0|0|
S14S6Z0A1S6Vlo;A1S6Vhi;A1S4cS5S47Vlo;Vhi;A2ScVOD;A1A3SbA5").

Definition subwin_ok (OD : sobj) (lo hi : Z) : bool := ltac2:(tb__ "0|c|
S2bS2bS2bS2bS25S16VOD;A1S6Z0M0A1A2S51S17VOD;A1SbA2A2S3S2cLx;M1S19VOD;A1S0G1S18VOD;A1S0S2bS2bS2bS2bS38G0R2A2S38R2Vlo;A2A2S38Vlo;Vhi;A2A2S38Vhi;R1A2A2S3dR1S3cZ2Z3eA2A2M2A2Lh;S1S2dLi;M3S45S3S3S2dLb;La;M4Lop;M5G5S46G4Lop;M6G6S2cS2S3S2dLa;Lw;Lsgn;M7S1S3S0S2dLk;Li;M8Ll0;X3x8Ll;G3G5G5G6G6G7S1G8Ll;M9X3x8A2S4bS5S5S31S47Vlo;Vhi;R1A3S48Vlo;Vhi;R1A3A2Lc;ScVOD;A1MaA3A2S4bS5S5S2bS2bG1S7R1A1S0S2bS38G0R1A2G2A2Lo;G3G5G5G6G6G7G9X3x8S38Z1S8R1A1MbA2A2S38GbZ8A2A2Lc;GaA3A2").

Lemma mod64' : bv_modulus 64 = 2 ^ 64. Proof. reflexivity. Qed.

Section DW.
Variable segs : list Segment.

Definition win_facts (rho : valuation) (msD : machine_state) (OD : sobj) (P : Z -> Prop) : Prop := ltac2:(tb__ "0|1|
S28S3fQ40M0A1VP;S40G0R1A2A1S27S2fS3fQ8A1A1SfVrho;R2A2S42VmsD;R2A2A3F_;Fa;S28S1aVsegs;Vrho;VmsD;VOD;A4SaVsegs;VmsD;A2A2A2").

Lemma win_facts_mono : ltac2:(tb__ "0|1|
S9S41S4S0OF_;M0G0S0R2R1A1R4R2A1F_;Fa;S44R6R5R4R3A4S44R7R6R5R3A4F_;F_;FQ;FP;FOD;FmsD;Frho;").
Proof using . intros rho msD OD P Q HPQ (A & B & C). split; [intros a Ha; apply A, HPQ, Ha | split; assumption]. Qed.

Lemma win_facts_agree : ltac2:(tb__ "0|0|
S1S9S9S41S4S0OF_;S13R6R5R4A3S27S2cS1cR7R3A2S2eA3S44R7R5R4R3A4S44R7R6R5R4A4F_;F_;F_;FP;FOD;FmsD;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' msD OD P Hag Hb (A & B & C). split; [|split; [|exact C]].
  - intros a Ha. rewrite <- (proj2 (proj2 Hag)). apply A. exact Ha.
  - exact (obj_holds_agree segs n rho rho' msD OD Hag Hb B).
Qed.

Lemma win_facts_rm : ltac2:(tb__ "0|3|
S9S3fQ40M0A1M1S2fS3fQ8A1A1M2Fx;S41S4S0OFx;S27S2cS52S1S2eL_;R2A2S2eA3G1R3S40G0R1A2A1S27G2R7R2A1SfR8R2A2A3F_;Fa;S44R7R5R4R3A4S44S50R8R7A2R6R5R4A4F_;F_;F_;FP;FOD;FmsD;Fm';Frho;").
Proof using .
  intros rho m' msD OD P Hv Hm (A & B & C). split; [|split; [|exact C]].
  - intros a Ha. cbn [set_rm rm]. rewrite (Hm a Ha). apply A. exact Ha.
  - apply (obj_holds_agree_vars segs (fun _ => true) rho (set_rm rho m') msD OD); [intros; reflexivity | intros; reflexivity | exact Hv | exact B].
Qed.

Lemma wview_ext' : ltac2:(tb__ "0|3|
S3fQ40A1M0S2fS3fQ8A1A1M1F_;M2G2G0S27G1R3R1A1R2R1A1A3S27G1S43Vsegs;R4R2A3S43Vsegs;R3R2A3A3F_;Fa;Fm';Fm;").
Proof using . intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rd_ext : ltac2:(tb__ "0|2|
S41S41S3fQ40A1S27S2fS3fQ8A1A1M0S42R3R1A2S42R2R1A2A3SaVsegs;R4A2M1G1S27G0SdR6R4A2SdR5R4A2A3F_;F_;F_;Fa;Fms';Fms;").
Proof using .
  intros ms ms' a Hm Hr Hr'. unfold rd, ms_read_byte. rewrite Hm, (Hr a), (Hr' a). reflexivity.
Qed.

Lemma rd_bytes_ext : ltac2:(tb__ "0|5|
S34S41S41S3fQ40M0A1M1S0S0G1S28S39R3S40G0R1A2M2A2S3bG2R2A2A2S27S2fS3fQ8A1M3A1S42R7R2A2S42R6R2A2A3F_;Fx;S39R3S40G0R4A2A2S39S3aS40G0R5A2S3eR8A1A2R3A2S39R4S3cZ2Z40A2A2SaVsegs;R9A2M4G4S27S2fS30G3A1A1SeRbR9RcA3SeRaR9RcA3A3F_;F_;F_;F_;F_;F_;Fhi;Flo;Fa;Fms';Fms;Fk;").
Proof using .
  induction k as [|k IH]; intros ms ms' a lo hi Hm Hlo Hhi H64 Hr Hr'; [reflexivity|]. cbn [rd_bytes].
  rewrite (rd_ext ms ms' a (Hm a ltac:(lia)) Hr Hr').
  destruct k as [|k'].
  - reflexivity.
  - assert (Ha1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
    { rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. rewrite mod64'. apply Z.mod_small.
      pose proof (bv_unsigned_in_range 64 a) as R. rewrite mod64' in R. lia. }
    rewrite (IH ms ms' (a + 1)%bv lo hi Hm ltac:(rewrite Ha1; lia) ltac:(rewrite Ha1; lia) H64 Hr Hr'). reflexivity.
Qed.

Lemma cell_in_sound : ltac2:(tb__ "0|0|
S0S0S5S27S2cS47R3R2R1A3S2eA3S29S0S0S28S27S3S7R3A1S6R1A1A3S28S39R5R1A2S39S3aR1S8R3A1A2R4A2A2A2Lo;A2F_;Fc;Fhi;Flo;").
Proof using .
  intros lo hi [off w v] H. unfold cell_in in H. cbn [c_off c_width] in *.
  destruct off; try discriminate. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
Qed.

Lemma cell_out_sound : ltac2:(tb__ "0|0|
S0S0S5S27S2cS48R3R2R1A3S2eA3S29S0S0S28S27S3S7R3A1S6R1A1A3S2aS39S3aR1S8R3A1A2R5A2S39R4R1A2A2A2Lo;A2F_;Fc;Fhi;Flo;").
Proof using .
  intros lo hi [off w v] H. unfold cell_out in H. cbn [c_off c_width] in *.
  destruct off; try discriminate. apply Bool.orb_true_iff in H as [H|H]; apply Z.leb_le in H; eauto.
Qed.

Theorem smatch_carve_subwin : ltac2:(tb__ "0|0|
S9S12S37S30S4fA1S4eA2S41S4S0OF_;S0S0S1S10Vsegs;R9R8R7A4S44RaR7R6R5A4S27S2cS4aR7R5R4A3S2eA3S0S28S39R7R1A2S3bR1R6A2A2R9R2A1F_;Fa;S4dS4S4S1dS1bReR1A2S36S0S0R8R7A4A2Lo';S11RcA1A3S15S22RdA1S23RdA1S20RdA1S1fRdA1S24RdA1S32S4S11RdA1S33S4S49RaR8R7A3S35S4A1A3A3S1eRdA1R6S21RdA1A9S12S27S2cS26R1A1S2eA3S10Vsegs;R10R2ReA4F_;TS';F_;F_;F_;F_;F_;Fnx;Fhi;Flo;FP;FOD;FmsD;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] msD OD P lo hi nx Hsm (HP & HOD & HromD) Hok HPin Hdisj S' Hwf.

  unfold subwin_ok in Hok.
  apply andb_prop in Hok as [Hok Hw8]. apply andb_prop in Hok as [Hok Hcells]. apply andb_prop in Hok as [Hok Hrng].
  apply andb_prop in Hok as [Hbase Hdf]. apply sv_eqb_sound in Hbase. apply odefault_eqb_sound in Hdf.
  destruct (ob_lo OD) as [l| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi OD) as [h| | | | | | |] eqn:Ehi; try discriminate.
  repeat (apply andb_prop in Hrng; destruct Hrng as [Hrng ?]).
  apply Z.leb_le in Hrng. repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).

  pose proof HOD as (HbD & HwD & HcD & HdD & _).
  unfold obj_lo_of, obj_hi_of in HbD, HwD, HcD, HdD. rewrite Hbase, Elo, Ehi in HbD, HwD, HcD, HdD.
  rewrite Hdf in HwD, HdD. cbn [eval] in HbD, HwD, HcD, HdD.
  rewrite !soff_lit_small in HbD, HwD, HcD, HdD by lia.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 in HbD, HwD, HdD by reflexivity.

  assert (OUT : forall a, lo <= a < hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite Z_to_bv_small by (rewrite mod64'; lia). exact Ha. }
  assert (MEM : forall a, lo <= a < hi -> ms_mem ms (Z_to_bv 64 a) = ms_mem msD (Z_to_bv 64 a)).
  { intros a Ha. rewrite (Hfr _ (OUT a Ha)). apply HP. rewrite Z_to_bv_small by (rewrite mod64'; lia). apply HPin. exact Ha. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs].
  assert (RNG : obj_range rho (subwin OD lo hi) = (lo, hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, subwin. cbn [ob_base ob_lo ob_hi eval].
    rewrite !soff_lit_small by lia. reflexivity. }
  split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, subwin. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval].
    rewrite !soff_lit_small by lia. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
    split; [lia|]. split.
    { intros off Hoff _. rewrite (wview_ext' (ms_mem ms) (ms_mem msD)) by (apply MEM; lia). apply HwD; [lia | reflexivity]. }
    split.
    {
      apply Forall_forall. intros c Hc'. apply filter_In in Hc' as [HcIn Hcin].
      destruct (cell_in_sound lo hi c Hcin) as (o & Eoff & Ho1 & Ho2).
      pose proof (proj1 (Forall_forall _ _) HcD c HcIn) as (C1 & C2 & C3).
      pose proof (proj1 (forallb_forall _ _) Hw8 c HcIn) as W8. cbn beta in W8. rewrite Eoff in W8.
      apply andb_prop in W8 as [W8 W8b]. apply andb_prop in W8 as [W8o W8a]. apply andb_prop in W8o as [W8l W8h].
      apply Z.leb_le in W8a. apply Z.leb_le in W8b. apply Z.leb_le in W8l. apply Z.ltb_lt in W8h.
      unfold cell_holds in C1, C2, C3 |- *. rewrite Eoff in C1, C2, C3 |- *. rewrite !soff_lit_small in C1, C2, C3 |- * by lia.
      split; [lia|]. split; [lia|].
      rewrite <- C3.
      assert (Hoa : bv_unsigned (oaddr rho (SLit 0) o) = o).
      { unfold oaddr. cbn [eval]. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
        rewrite Z_to_bv_small by (rewrite mod64'; lia). lia. }
      apply (rd_bytes_ext _ ms msD _ lo hi); [| lia | rewrite Hoa; lia | lia | exact Hrom | exact HromD].
      intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply MEM. exact Hx. }
    split; [|exact I].
    intros off Hoff Hnc. cbn [dflt_holds].
    replace (Z_to_bv 64 (0 + off)) with (Z_to_bv 64 off) by (f_equal; lia). rewrite (MEM off) by lia.
    apply (HdD off); [lia|].

    intros Hcov. apply Hnc. unfold covered in *. apply Exists_exists in Hcov as (c & HcIn & Hin).
    apply Exists_exists. exists c. split; [|exact Hin].
    apply filter_In. split; [exact HcIn|].
    pose proof (proj1 (forallb_forall _ _) Hcells c HcIn) as Hc2. cbn beta in Hc2. apply Bool.orb_true_iff in Hc2 as [Hc2|Hc2]; [exact Hc2|].
    exfalso. destruct (cell_out_sound lo hi c Hc2) as (o & Eoff & Hout).
    pose proof (proj1 (forallb_forall _ _) Hw8 c HcIn) as W8. cbn beta in W8. rewrite Eoff in W8.
    apply andb_prop in W8 as [W8 _]. apply andb_prop in W8 as [W8o _]. apply andb_prop in W8o as [W8l W8h].
    apply Z.leb_le in W8l. apply Z.ltb_lt in W8h.
    unfold in_cell in Hin. rewrite Eoff in Hin. rewrite soff_lit_small in Hin by lia. lia.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite RNG. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

End DW.
