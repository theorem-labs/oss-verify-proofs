(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "andb"; "prod"; "option"; "cons"; "nil"; "pair"; "false"; "negb"; "@Corelib.Init.Logic"; "eq"; "iff"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "smatch"; "rw"; "sstate"; "rl"; "rm"; "sobj"; "sprop"; "valuation"; "SLit"; "cell"; "eval"; "holds"; "obj_holds"; "obj_range"; "odefault"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "c_off"; "c_val"; "mkSS"; "mkVal"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_lenient"; "ss_next"; "ss_pc"; "swf"; "tfact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib"; "sv_vl_all"; "obj_vl_all"; "sprop_vl_all"; "state_vl_all"; "dflt_vl_all"; "no_facts"; "set_rl"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.Lists.List"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "subst_state"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymFrame SymEntail SymObj SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint sv_vl_all (f g : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => f i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_vl_all f g a && sv_vl_all f g b
  | SExt _ _ a => sv_vl_all f g a
  | SLBytes l i _ => g l && sv_vl_all f g i
  end.

Fixpoint sprop_vl_all (f g : positive -> bool) (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => sv_vl_all f g a && sv_vl_all f g b
  | SPNot q => sprop_vl_all f g q
  | SPTrue => true
  | SPAlign i _ => f i
  end.

Definition dflt_vl_all (f g : positive -> bool) (d : odefault) : bool := ltac2:(tb__ "0|1|
S1eS1Ld;Vd;S0S0S0SdVg;R1A1Ll;M0G0SeSfS2S4SeSeA2A1S2S33A1S9Ltmpl;Lflds;Lcnt;Lesz;X1ex6").

Definition obj_vl_all (f g : positive -> bool) (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3S3S3S34Vf;Vg;S29Vo;A1A3S34Vf;Vg;S2dVo;A1A3A2S34Vf;Vg;S2cVo;A1A3A2S3dS19S19S3S34Vf;Vg;S25R1A1A3S34Vf;Vg;S26R1A1A3A2Lc;S2aVo;A1A3A2S38Vf;Vg;S2bVo;A1A3A2").

Definition state_vl_all (f g : positive -> bool) (S : sstate) : bool := ltac2:(tb__ "0|2|
S3S3S3S3S3S3dSfS34Vf;Vg;A2M0S23VS;A1A3S3dSfG0S21VS;A1A3A2S1fS1Lx;S20VS;A1S0SfS34Vf;Vg;R1A3Lv;M1X1fx2A2S5SfA1S1Lx;S24VS;A1G1S0X5x2A2S3dS15S35Vf;Vg;A2S22VS;A1A3A2S3dS16S36Vf;Vg;A2S2eVS;A1A3A2").

Section VL.
Variables (f g : positive -> bool) (rho rho' : valuation).
Hypothesis Hv : ltac2:(tb__ "0|0|
SdSbS1Vf;R1A1S0A3SbS3bQ40A1S11Vrho;R2A2S11Vrho';R2A2A3F_;Fv;").
Hypothesis Hl : ltac2:(tb__ "0|0|
SdSbS1Vg;R1A1S0A3SbS2S3bQ8A1A1S13Vrho;R2A2S13Vrho';R2A2A3F_;Fl;").

Lemma eval_agree_vl : ltac2:(tb__ "0|0|
SfSbS1S34Vf;Vg;R1A3S0A3SbS3bQ40A1S1aVrho;R2A2S1aVrho';R2A2A3F_;Fe;").
Proof.
  induction e; cbn; intros H; try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2)); try reflexivity.
  - apply Hv. exact H.
  - rewrite (IHe H). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (Hl _ H1), (IHe H2). reflexivity.
Qed.

Lemma holds_agree_vl : ltac2:(tb__ "0|0|
S16SbS1S36Vf;Vg;R1A3S0A3ScS1bVrho;R2A2S1bVrho';R2A2A2F_;Fp;").
Proof.
  induction p; cbn; intros H;
    try (apply andb_prop in H as [H1 H2]; rewrite (eval_agree_vl _ H1), (eval_agree_vl _ H2)); try (split; intros X; exact X).
  - specialize (IHp H). split; intros X Y; apply X; apply IHp; exact Y.
  - rewrite (Hv i H). split; intros X; exact X.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma obj_holds_agree_vl : ltac2:(tb__ "0|0|
S43S15SbS1S35Vf;Vg;R1A3S0A3S1cVsegs;Vrho;R3R2A4S1cVsegs;Vrho';R4R3A4F_;F_;Fo;Fms;").
Proof using Hv Hl.
  intros ms o Ho (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_vl_all in Ho. apply andb_prop in Ho as [Ho Hdv]. apply andb_prop in Ho as [Ho Hcells]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
  pose proof (eval_agree_vl _ Hbase) as EB.
  assert (ELO : obj_lo_of rho' o = obj_lo_of rho o) by (unfold obj_lo_of, soff; rewrite (eval_agree_vl _ Hlo); reflexivity).
  assert (EHI : obj_hi_of rho' o = obj_hi_of rho o) by (unfold obj_hi_of, soff; rewrite (eval_agree_vl _ Hhi); reflexivity).
  assert (EC : forall c, In c (ob_cells o) -> soff rho' (c_off c) = soff rho (c_off c) /\ eval rho' (c_val c) = eval rho (c_val c)).
  { intros c Hin. pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as W. apply andb_prop in W as [W1 W2].
    unfold soff. rewrite (eval_agree_vl _ W1), (eval_agree_vl _ W2). auto. }
  assert (COV : forall off, covered rho' (ob_cells o) off <-> covered rho (ob_cells o) off).
  { intros off. unfold covered. rewrite !Exists_exists. split; intros (c & Hin & Hic); exists c; split; auto;
      unfold in_cell in *; destruct (EC c Hin) as [E1 _]; [rewrite <- E1 | rewrite E1]; exact Hic. }
  unfold obj_holds. rewrite <- EB, ELO, EHI. split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (A & B & C).
    destruct (EC c Hin) as [E1 E2]. unfold cell_holds, oaddr in *. rewrite E1, E2, <- EB. repeat split; assumption.
  - intros off Hoff Hnc. specialize (Hd off Hoff ltac:(intros X; apply Hnc; apply COV; exact X)).
    destruct (ob_dflt o); cbn in *; try exact Hd; try discriminate; rewrite <- (Hl _ Hdv); exact Hd.
  - destruct (ob_dflt o); cbn in *; try exact Hdl; try discriminate; rewrite <- (Hl _ Hdv); exact Hdl.
Qed.

Lemma obj_range_agree_vl : ltac2:(tb__ "0|0|
S15SbS1S35Vf;Vg;R1A3S0A3SbS4SeSeA2S1dVrho';R2A2S1dVrho;R2A2A3F_;Fo;").
Proof using Hv Hl.
  intros o Ho.
  unfold obj_vl_all in Ho. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_agree_vl _ Hbase), (eval_agree_vl _ Hlo), (eval_agree_vl _ Hhi). reflexivity.
Qed.

Lemma smatch_agree_vl : ltac2:(tb__ "0|0|
S12S4S2S3fA1S3eA2SbS3bQ40A1S5S3bQ8A1A1F_;S14Vrho;A1S14Vrho';A1A3SbS1S37Vf;Vg;R3A3S0A3S10Vsegs;Vrho;R4R3A4S10Vsegs;Vrho';R5R4A4F_;F_;F_;Fw;FS;").
Proof using Hv Hl.
  intros S [tr [ms md]] Hm Hs Hsm.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold state_vl_all in Hs.
  apply andb_prop in Hs as [Hs Hfa]. apply andb_prop in Hs as [Hs Hob]. apply andb_prop in Hs as [Hs Hrv].
  apply andb_prop in Hs as [Hs Hfc]. apply andb_prop in Hs as [Hrg Hfr].
  assert (NTH : forall (l : list sv) n, forallb (sv_vl_all f g) l = true -> sv_vl_all f g (nth n l (SLit 0)) = true).
  { intros l. induction l as [|x t IH]; intros n Hfl; destruct n; cbn in *; try reflexivity;
      apply andb_prop in Hfl as [A B]; [exact A | apply IH; exact B]. }
  assert (EREG : forall r, eval rho' (reg_sv S r) = eval rho (reg_sv S r)).
  { intros r. unfold reg_sv. destruct (Z.eqb r 0); [reflexivity|]. symmetry. apply eval_agree_vl. apply NTH. exact Hrg. }
  assert (EFREG : forall r, eval rho' (freg_sv S r) = eval rho (freg_sv S r)).
  { intros r. unfold freg_sv. symmetry. apply eval_agree_vl. apply NTH. exact Hfr. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split. { intros r Hr. rewrite EREG. apply Hregs. exact Hr. }
  split. { intros r. rewrite EFREG. apply Hfregs. }
  split. { destruct (ss_fcsr S); cbn in *; [exact Hfcsr|]. rewrite <- (eval_agree_vl _ Hfc). exact Hfcsr. }
  split. { unfold resv_match in *. destruct (ss_resv S); destruct (ms_resv ms); try exact Hresv.
           rewrite <- (eval_agree_vl _ Hrv). exact Hresv. }
  split.
  { destruct Hmem as (Hall & Hpd & Hfrm). split; [|split].
    - apply Forall_forall. intros o Hin. apply obj_holds_agree_vl; [exact (proj1 (forallb_forall _ _) Hob o Hin) | exact (proj1 (Forall_forall _ _) Hall o Hin)].
    - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
      erewrite map_ext_in; [exact Hpd|]. intros o Hin. apply obj_range_agree_vl. exact (proj1 (forallb_forall _ _) Hob o Hin).
    - intros a Ha. rewrite <- Hm. apply Hfrm. unfold outside_all in *.
      apply Forall_forall. intros o Hin. cbn zeta.
      rewrite <- (obj_range_agree_vl o (proj1 (forallb_forall _ _) Hob o Hin)).
      exact (proj1 (Forall_forall _ _) Ha o Hin). }
  apply Forall_forall. intros p Hin. apply (holds_agree_vl p (proj1 (forallb_forall _ _) Hfa p Hin)).
  exact (proj1 (Forall_forall _ _) Hfacts p Hin).
Qed.
End WithSegs.
End VL.

Definition set_rl (rho : valuation) (l : positive) (bs : list byte) : valuation := ltac2:(tb__ "0|0|
S28S11Vrho;A1SdS1S2S3bQ8A1A1L_;S42R1Vl;A2Vbs;S13Vrho;R1A2X1x2Ll';S14Vrho;A1A3").

Lemma smatch_set_rl : ltac2:(tb__ "0|0|
S2S40A1S17S12S4S2S3fA1S3eA2SdS2S3bQ8A1A1SbS1S37SdS0L_;SdSaS42R1R3A2A1Ll';R4A3S0A3S10R7R6R5R4A4S10R8S3aR7R4R3A3R6R5A4F_;F_;Fbs;Fl;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w l bs Hs Hsm.
  apply (smatch_agree_vl (fun _ => true) (fun l' => negb (Pos.eqb l' l)) rho (set_rl rho l bs)); try reflexivity; try assumption.
  intros l' Hl'. unfold set_rl. cbn [rl]. destruct (Pos.eqb l' l); [discriminate | reflexivity].
Qed.

Definition no_facts (S : sstate) : sstate := ltac2:(tb__ "0|0|
S27S31VS;A1S23VS;A1S21VS;A1S20VS;A1S24VS;A1S22VS;A1S7S16A1S30VS;A1S2fVS;A1A9").

Lemma smatch_drop_facts : ltac2:(tb__ "0|0|
S2S40A1S17S12S4S2S3fA1S3eA2S10R4R3R2R1A4S10R5R4S39R3A1R2A4F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S [tr [ms md]] Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch, no_facts. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  split.
  { unfold swf in Hwf |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
    repeat (apply andb_prop in Hwf as [Hwf ?]). repeat (apply andb_true_intro; split); try assumption; reflexivity. }
  repeat (split; [assumption|]). constructor.
Qed.

Lemma smatch_fold_const : ltac2:(tb__ "0|3|
S2S40A1S17S12S4S2S3fA1S3eA2SdSeSdSbS3bQ40M0A1S11R6R3A2S3cG0R2A2A3SbS1S32S41S6S4SdSfA2M1S8SdSfR4S18R3A1A4S7G1A1M2A3R6R2A3A1S0A3S10R9R8R7R6A4S10RaR9S41S6G1S8SdSfR6S18R5A1A4G2A3R8R4A3R7A4F_;F_;F_;Fnx;Fz;Fi;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w i z nx Hi Hwf Hsm.
  apply smatch_subst_intro; [exact Hwf|].
  apply (smatch_agree segs rho); [|exact Hsm].
  split; [|split; [intros l; reflexivity | intros a; reflexivity]].
  intros j _. unfold rho_sub. cbn [rw wsub_get]. destruct (Pos.eqb j i) eqn:E; [|reflexivity].
  apply Pos.eqb_eq in E. subst j. cbn [eval]. exact Hi.
Qed.
