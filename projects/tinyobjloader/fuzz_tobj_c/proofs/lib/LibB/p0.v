(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA.

(* [comment removed for export] *)
Module ObjZeroFillB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sstate"; "cell"; "c_off"; "c_width"; "ob_base"; "ob_hi"; "ob_lo"; "valuation"; "SLit"; "c_val"; "obj_holds"; "odefault"; "smatch"; "swf"; "DZero"; "mkObj"; "ob_cells"; "ob_dflt"; "ss_objs"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "false"; "bool"; "option"; "andb"; "Some"; "list"; "nat"; "None"; "prod"; "true"; "S"; "app"; "cons"; "negb"; "orb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB"; "zf_small63"; "zero_fill_obj"; "zero_fill_at"; "zf_range"; "zf_covers"; "zf_is_z1"; "zf_keep"; "zf_z1_at"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "add"; "leb"; "ltb"; "le"; "lt"; "of_nat"; "opp"; "pow"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "existsb"; "In"; "filter"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "seq"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zf_small63 (z : Z) : bool := ltac2:(tb__ "0|1|
S1cS36S3bS3cZ2Z3fA2M0A1Vz;A2S37Vz;G0A2A2").

Definition zf_is_z1 (c : cell) : bool := ltac2:(tb__ "0|8|
S0S1aLx;M0S4Vc;A1S16G0SbVc;A1S16S16S1aLz;R1S1cS34S5Vc;A1Z1A2S2aR2A1A2S17S19Lp;M1G1X16x3Lz;S17S19Li;M2S32S0S0S19Lb;La;M3Lop;M4G4S33G3Lop;M5G5S1aS18S0S19La;Lw;Lsgn;M6S17S0S16S19Lk;Li;Ll;M7X0x8Loff;G2G4G4G5G5G6G7X0x8").
Definition zf_z1_at (off : Z) (c : cell) : bool := ltac2:(tb__ "0|8|
S0S1aLx;M0S4Vc;A1S16G0SbVc;A1S16S16S1aLz;R1S1cS1cS34S5Vc;A1Z1A2S34R2Voff;A2A2S2aR2A1A2S17S19Lp;M1G1X16x3Lz;S17S19Li;M2S32S0S0S19Lb;La;M3Lop;M4G4S33G3Lop;M5G5S1aS18S0S19La;Lw;Lsgn;M6S17S0S16S19Lk;Li;Ll;M7X0x8Loc;G2G4G4G5G5G6G7X0x8").

Definition zf_covers (off : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S0S1aLx;S4Vc;A1S16S1cS1cS36R1Voff;A2S37Voff;S35R1S5Vc;A1A2A2A2S2aR1A1A2Loc;S17S19Li;S32S0S0S19Lb;La;M0Lop;M1G1S33G0Lop;M2G2S1aS18S0S19La;Lw;Lsgn;S17S0S16S19Lk;Li;Ll;X0x8").
Definition zf_keep (cells : list cell) : list cell := ltac2:(tb__ "0|0|
S43S3S3S26S2fR1A1A1Lc;Vcells;A3").
Definition zf_range (lo hi : Z) : list Z := ltac2:(tb__ "0|0|
S47S1fS16S1fS35Vlo;S3aR1A1A2Lk;S48U0S3eS3dVhi;Vlo;A2A1A2A4").

Definition zero_fill_obj (o : sobj) : option sobj := ltac2:(tb__ "0|c|
S0S1bS1A1M0Lx;M1S8Vo;A1S16G1S7Vo;A1S16SdG0Lx;S13Vo;A1S1aG0L_;S1cS1cS44S16S16S27S41S3S2eR1A1S30S12Vo;A1M2A1M3A3S41S3S31R1A1G2A3A2Loff;S2dR2R1A2A3S2aR2A1A2S2aR1A1A2S1dS1S11S6Vo;A1SaR2A1SaR1A1G3S10A5A2S20S1A1M4X1ax2G4G4S17G4Ll;M5G5S16S0S1eS21S16S16A2A1S1eS15A1G4Ltmpl;Lflds;Lcnt;Lesz;Xdx6Lhi;S17G4Li;M6S32S0S0G4Lb;La;M7Lop;M8G8S33G7Lop;M9G9S1aS18S0G4La;Lw;Lsgn;MaS17S0S16G4Lk;Li;Ll;MbX0x8Llo;G6G8G8G9G9GaGbX0x8").

Definition zero_fill_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S1bS1A1S1bS2A1Lx;M0S45S1S14VS;A1M1Vi;A3S1G0S2bR1A1S1S1dS2S4eVS;S24S1S46S1Vi;G1A3S25S1R1S49S1S23Vi;A1G1A3A3A3A2A2Lo';S20S2A1M2X1bx2Lo;G2X1bx2").

Section WithSegs.
Variable segs : list Segment.

Lemma zf_range_in : ltac2:(tb__ "0|0|
S16S16S16S29S38R3R1A2S39R1R2A2A2S42S16R2S2dR4R3A2A3F_;Foff;Fhi;Flo;").
Proof using .
  intros lo hi off H. unfold zf_range. apply in_map_iff. exists (Z.to_nat (off - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma zero_fill_obj_holds : ltac2:(tb__ "0|0|
S9S4aS1S1S28S1bS1A1S2bR2A1S1dS1R1A2A3ScVsegs;R5R4R3A4ScVsegs;R6R5R3A4F_;F_;Fo';Fo;Fms;Frho;").
Proof using .
  intros rho ms o o' Hz Hoh.
  unfold zero_fill_obj in Hz.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  destruct (ob_dflt o) eqn:Ed; try discriminate.
  match type of Hz with (if ?b then _ else _) = _ => destruct b eqn:Hall0; [|discriminate] end. injection Hz as <-.
  apply andb_prop in Hall0 as [Hall0 Shi]. apply andb_prop in Hall0 as [Hall Slo].
  unfold zf_small63 in Slo, Shi. apply andb_prop in Slo as [Slo1 Slo2]. apply andb_prop in Shi as [Shi1 Shi2].
  apply Z.leb_le in Slo1. apply Z.ltb_lt in Slo2. apply Z.leb_le in Shi1. apply Z.ltb_lt in Shi2.
  pose proof Hoh as (Hrg & Hwr & Hcells & Hd & Hinv).
  assert (Elo' : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Elo; apply soff_lit_small; lia).
  assert (Ehi' : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Ehi; apply soff_lit_small; lia).
  assert (Elo2 : soff rho (SLit lo) = lo) by (apply soff_lit_small; lia).
  assert (Ehi2 : soff rho (SLit hi) = hi) by (apply soff_lit_small; lia).
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite Elo2, Ehi2.
  rewrite Elo', Ehi' in Hrg, Hwr, Hcells. rewrite Ed in Hwr.
  split; [exact Hrg|]. split; [intros off Hoff _; apply Hwr; [exact Hoff | reflexivity]|]. split; [|split; [|exact I]].
  - unfold zf_keep. apply Forall_forall. intros c Hin. apply filter_In in Hin as [Hin _].
    exact (proj1 (Forall_forall _ _) Hcells c Hin).
  - intros off Hoff Hnc. cbn [dflt_holds].
    pose proof (proj1 (forallb_forall _ _) Hall off (zf_range_in lo hi off Hoff)) as Hb.
    apply orb_prop in Hb as [Hb|Hb].
    + exfalso. apply Hnc. apply existsb_exists in Hb as (c & Hin & Hc). unfold covered. apply Exists_exists. exists c. split; [exact Hin|].
      unfold zf_covers in Hc. destruct (c_off c) as [oc| | | | | | |] eqn:Eoc; try discriminate.
      apply andb_prop in Hc as [Hc Hs]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      unfold zf_small63 in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
      unfold in_cell. rewrite Eoc. rewrite (soff_lit_small rho oc) by lia. lia.
    + apply existsb_exists in Hb as (c & Hin & Hc).
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (_ & _ & Hrd).
      unfold zf_z1_at in Hc. destruct (c_off c) as [oc| | | | | | |] eqn:Eoc; try discriminate.
      destruct (c_val c) as [v| | | | | | |] eqn:Ev; try discriminate. destruct v; try discriminate.
      apply andb_prop in Hc as [Hc Hs]. apply andb_prop in Hc as [Hw Ho]. apply Z.eqb_eq in Hw. apply Z.eqb_eq in Ho. subst oc.
      unfold zf_small63 in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
      rewrite Hw, (soff_lit_small rho off) in Hrd by lia. unfold oaddr in Hrd.
      change (Z.to_nat 1) with 1%nat in Hrd. cbn [rd_bytes] in Hrd.
      destruct (rd ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))) as [b|] eqn:Eb; [|discriminate].
      injection Hrd as Hb0. rewrite Hb0. reflexivity.
Qed.

Lemma zero_fill_obj_shape : ltac2:(tb__ "0|0|
S1S1S28S1bS1A1S2bR2A1S1dS1R1A2A3S29S28S0S6R2A1S6R3A1A3S29S28S0S8R2A1S8R3A1A3S28S0S7R2A1S7R3A1A3A2A2F_;Fo';Fo;").
Proof using .
  intros o o' Hz. unfold zero_fill_obj in Hz.
  destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate. destruct (ob_dflt o); try discriminate.
  match type of Hz with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection Hz as <-. cbn. repeat split; reflexivity.
Qed.

Theorem smatch_zero_fill : ltac2:(tb__ "0|0|
S9S2S1fS2S21S1eS4cA1S4bA2S28S1bS2A1S2cR4R3A2S1dS2R2A2A3S28S1aSfR3A1S22A3SeVsegs;R7R6R3A4SeVsegs;R8R5R4A4F_;F_;F_;Fw;FS';Fi;FS;Frho;").
Proof using .
  intros rho S i S' [tr [ms md]] Hz HwfS' Hsm.
  unfold zero_fill_at in Hz.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_fill_obj o) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as <-.
  pose proof (zero_fill_obj_shape o o' Ho') as (Eb & Elo & Ehi).
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. reflexivity. }
  pose proof (zero_fill_obj_holds rho ms o o' Ho' Hoh) as Hoh'.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact HwfS'|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPA_zero_fill : ltac2:(tb__ "0|0|
S40S9S51S1fS2S1eS52Q40A1A1S4dS28S1bS2A1S2cS4fR5A1R4A2S1dS2R3A2A3S28S1aSfR4A1S22A3S3fVsegs;R9R7R8R4R3A6S3fVsegs;RaS50R8R6A2R9R5R4A6F_;F_;F_;Fw;Ftp;FS';Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i S' tp [tr [ms md]] Hz HwfS' [(Hsm & HMI & Hwf' & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_zero_fill rho (ax_S A) i S' _ Hz HwfS' Hsm) as Hsm'.
  unfold zero_fill_at in Hz.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_fill_obj o) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as E'.
  pose proof (zero_fill_obj_shape o o' Ho') as (Eb & Elo & Ehi).
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  split; [exact Hsm'|]. split; [exact HMI|].
  assert (EN : ss_next S' = ss_next (ax_S A)) by (rewrite <- E'; reflexivity).
  split; [unfold axwf in Hwf' |- *; cbn [ax_S ax_X ax_base ax_setS] in Hwf' |- *; rewrite EN; exact Hwf'|].
  split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  rewrite <- E'. cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *. rewrite Eb, Elo, Ehi in Hx. exact Hx.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

End WithSegs.
End ObjZeroFillB.

(* [comment removed for export] *)
Module ObjRetileB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "option"; "andb"; "Some"; "list"; "false"; "pair"; "true"; "None"; "app"; "nat"; "S"; "cons"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "sobj"; "sstate"; "SLit"; "valuation"; "ob_base"; "ob_hi"; "ob_lo"; "c_off"; "c_val"; "c_width"; "enc_bytes"; "obj_holds"; "odefault"; "smatch"; "swf"; "cell_holds"; "eval"; "mkObj"; "ob_cells"; "ob_dflt"; "rd"; "ss_objs"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "leb"; "lt"; "ltb"; "to_nat"; "pow"; "opp"; "eqb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "rt_lit"; "retile_obj"; "rt_seq"; "rt_small63"; "retile_at"; "rt_byte"; "rt_check_drop"; "rt_check_new"; "rt_covers"; "rt_dflt_ok"; "rt_just"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "In"; "nth_error"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition rt_small63 (z : Z) : bool := ltac2:(tb__ "0|1|
S6S2fS34S33Z2Z3fA2M0A1Vz;A2S31Vz;G0A2A2").

Definition rt_lit (c : cell) : option (Z * Z * Z) := ltac2:(tb__ "0|c|
S12S5S4S4S0S0A2M0S0A2M1A1M2Lx;M3S1bVc;A1S0G3S1cVc;A1S0S3G2L_;S6S3aR2A1S31Z0S1dVc;A1M4A2A2S7G1SaG0S0SaS0S0R2G4A4R1A4A2ScG1A1M5X3x2Lv;S1G5Li;M6S4eS12S12G5Lb;La;M7Lop;M8G8S4fG7Lop;M9G9S3S2S12G5La;Lw;Lsgn;MaS1S12S0G5Lk;Li;Ll;MbX12x8Lo;G6G8G8G9G9GaGbX12x8").

Definition rt_byte (w v j : Z) : Z := ltac2:(tb__ "0|1|
S44Q8M0S4aS43G0A1S32Vj;A1S1eS32Vw;A1S42Q40Vv;A2A2S42G0Z0A2A4A2").
Definition rt_seq (w : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat w)).
Definition rt_just (olds : list cell) (off : Z) (b : Z) : bool := ltac2:(tb__ "0|2|
S46S13S13S5S4S4S0S0A2M0S0A2M1A1S3Lx;S37R1A1G1G1S3Lp;R1G0S0G0S3Lp0;R2S0S0S6S6S2fR2Voff;A2S31Voff;S2dR2R1A2A2A2S35S3cR1R3S36Voff;R2A2A3Vb;A2A2Lw;Lo;X4x1Lv;Lp0;X4x1Lp;S9X5x2Lc;Volds;A3").
Definition rt_covers (off : Z) (c : cell) : bool := ltac2:(tb__ "0|2|
S5S4S4S0S0A2M0S0A2M1A1S3Lx;S37Vc;A1G1G1S3Lp;R1G0S0G0S3Lp0;R2S0S0S6S2fR2Voff;A2S31Voff;S2dR2R1A2A2A2Lw;Lo;X4x1Lz;Lp0;X4x1Lp;S9X5x2").
Definition rt_check_new (lo hi : Z) (olds : list cell) (c : cell) : bool := ltac2:(tb__ "0|2|
S5S4S4S0S0A2M0S0A2M1A1S3Lx;S37Vc;A1G1G1S3Lp;R1G0S0G0S3Lp0;R2S0S0S6S6S2fVlo;R2A2S2fS2dR2R1A2Vhi;A2A2S45S0S0S41Volds;S2dR3R1A2S3cR2R4R1A3A3Lj;S39R1A1A3A2Lw;Lo;X4x1Lv;Lp0;X4x1Lp;S9X5x2").
Definition rt_check_drop (news : list cell) (c : cell) : bool := ltac2:(tb__ "0|2|
S5S4S4S0S0A2M0S0A2M1A1S3Lx;S37Vc;A1G1G1S3Lp;R1G0S0G0S3Lp0;R2S0S0S45S0S0S46S13S3fS2dR3R1A2A1Vnews;A3Lj;S39R1A1A3Lw;Lo;X4x1Lz;Lp0;X4x1Lp;S9X5x2").
Definition rt_dflt_ok (d : odefault) : bool := ltac2:(tb__ "0|1|
S20S3Ld;Vd;SbSbS9S1S9Ll;M0G0S0S12S8S4S0S0A2A1S8S2aA1S9Ltmpl;Lflds;Lcnt;Lesz;X20x6").

Definition retile_obj (o : sobj) (dropf : cell -> bool) (news : list cell) : option sobj := ltac2:(tb__ "0|b|
S12S5S14A1M0Lx;M1S1aVo;A1S0G1S19Vo;A1S0S3G0L_;S6S6S6S6S3aR2A1S3aR1A1A2S40S27Vo;A1M2A1A2S45S13S3eR2R1S26Vo;A1M3A3Vnews;A3A2S45S13S3dVnews;A1S47S13Vdropf;G3A3A3A2S7S14S25S18Vo;A1S16R2A1S16R1A1SdS13Vnews;S47S13S13S11Vdropf;R1A1A1Lc;G3A3A3G2A5A2ScS14A1M4X3x2Lhi;S1G4Li;M5S4eS12S12G4Lb;La;M6Lop;M7G7S4fG6Lop;M8G8S3S2S12G4La;Lw;Lsgn;M9S1S12S0G4Lk;Li;Ll;MaX12x8Llo;G5G7G7G8G8G9GaX12x8").

Definition retile_at (S : sstate) (i : nat) (dropf : cell -> bool) (news : list cell) : option sstate := ltac2:(tb__ "0|3|
S5S14A1S5S15A1Lx;M0S49S14S29VS;A1M1Vi;A3S14G0S38R1Vdropf;Vnews;A3S14S7S15S55VS;SdS14S4bS14Vi;G1A3S10S14R1S4cS14SfVi;A1G1A3A3A3A2A2Lo';ScS15A1M2X5x2Lo;G2X5x2").

Section WithSegs.
Variable segs : list Segment.

Lemma rt_seq_in : ltac2:(tb__ "0|0|
S0S0S2cS2eZ0R1A2S30R1R2A2A2S48S0R2S39R3A1A3F_;Fj;Fw;").
Proof using . intros w j H. unfold rt_seq. apply in_map_iff. exists (Z.to_nat j). split; [lia|]. apply in_seq. lia. Qed.

Lemma rt_lit_inv : ltac2:(tb__ "0|3|
S13S0S0S0S2bS5S4S4S0S0A2M0S0A2M1A1S37R4A1S7G1SaG0S0SaS0S0R3R2A4R1A4A2A3S2cS2bS12S1bR5A1S16R4A1A3S2cS2bS12S1cR5A1S16R2A1A3S2cS2bS0S1dR5A1R3A3S2cS2cS2eS34S33Z2Z3fA2M2A1R4A2S30R4G2A2A2S30Z0R3A2A2A2A2A2F_;Fv;Fw;Fo;Fc;").
Proof using .
  intros c o w v H. unfold rt_lit in H.
  destruct (c_off c) as [o0| | | | | | |] eqn:Eo; try discriminate. destruct (c_val c) as [v0| | | | | | |] eqn:Ev; try discriminate.
  destruct (rt_small63 o0 && (0 <? c_width c)) eqn:Hb; [|discriminate]. injection H as <- <- <-.
  apply andb_prop in Hb as [Hs Hw]. unfold rt_small63 in Hs. apply andb_prop in Hs as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in Hw. repeat split; auto; lia.
Qed.

Lemma rt_cell_byte : ltac2:(tb__ "0|6|
S17S4dS12S0S0S13S0S0S0S0S0S2eZ0M0S2dR1R8A2A2S2eS2dR2R8A2S33Z2Z40A2A2S2bS0R3S44Q40M1S24RdRbA2A2A3S23ReRcRbRaRdR9A6S2bS5S4S4S0S0A2M2S0A2M3A1S37RaA1S7G3SaG2S0SaS0S0R9R8A4R7A4A2A3S2cS2eG0R7A2S30R7R9A2A2S2bS5S43Q8M4A1M5A1S28R10S42G1S2dS2dR7RbA2R8A2A2A2S7G5S4aG5S32R8A1S1eS32RaA1S42G1R9A2A2S42G4G0A2A4A2A3F_;F_;F_;F_;F_;F_;Fb;Fj;Fv;Fw;Fo;Fc;Fhi;Flo;Fbase;Fms;Frho;").
Proof using .
  intros rho ms base lo hi c o w v j b Hb0 Hb1 Eb (Hlo & Hhi & Hrd) Hl Hj.
  destruct (rt_lit_inv _ _ _ _ Hl) as (Eo & Ev & Ew & Hs & Hw). rewrite Eo, Ev, Ew in *.
  rewrite (soff_lit_small rho o Hs) in *. cbn [eval] in Hrd. unfold oaddr in Hrd. rewrite <- Eb in Hrd.
  assert (EA : bv_unsigned (Z_to_bv 64 (b + o)) = b + o) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; lia).
  pose proof (rd_bytes_nth ms (Z.to_nat w) (Z_to_bv 64 (b + o)) _ (Z.to_nat j) Hrd ltac:(lia) ltac:(rewrite EA; lia)) as H.
  rewrite EA in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma retile_obj_holds : ltac2:(tb__ "0|0|
S17S4dS14S13S3F_;S8S13A1S14S2bS5S14A1S38R4R3R2A3S7S14R1A2A3S1fVsegs;R7R6R5A4S1fVsegs;R8R7R3A4F_;F_;Fo';Fnews;Fdropf;Fo;Fms;Frho;").
Proof using .
  intros rho ms o dropf news o' Hz Hoh. unfold retile_obj in Hz.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  match type of Hz with (if ?b then _ else _) = _ => destruct b eqn:Hall0; [|discriminate] end. injection Hz as <-.
  apply andb_prop in Hall0 as [Hall0 Hdrop]. apply andb_prop in Hall0 as [Hall0 Hnew]. apply andb_prop in Hall0 as [Hall0 Hdf].
  apply andb_prop in Hall0 as [Slo Shi].
  unfold rt_small63 in Slo, Shi. apply andb_prop in Slo as [Slo1 Slo2]. apply andb_prop in Shi as [Shi1 Shi2].
  apply Z.leb_le in Slo1. apply Z.ltb_lt in Slo2. apply Z.leb_le in Shi1. apply Z.ltb_lt in Shi2.
  pose proof Hoh as (Hrg & Hwr & Hcells & Hd & Hinv).
  assert (Elo' : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Elo; apply soff_lit_small; lia).
  assert (Ehi' : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Ehi; apply soff_lit_small; lia).
  assert (Elo2 : soff rho (SLit lo) = lo) by (apply soff_lit_small; lia).
  assert (Ehi2 : soff rho (SLit hi) = hi) by (apply soff_lit_small; lia).
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite Elo2, Ehi2.
  rewrite Elo', Ehi' in Hrg, Hwr, Hcells, Hd, Hinv.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  destruct Hrg as (Hb0 & Hb1 & Hlh & Hsz).
  split; [repeat split; assumption|]. split; [exact Hwr|]. split; [|split].
  - apply Forall_app. split.
    + apply Forall_forall. intros c' Hin'.
      pose proof (proj1 (forallb_forall _ _) Hnew c' Hin') as Hc. unfold rt_check_new in Hc.
      destruct (rt_lit c') as [[[o' w'] v']|] eqn:El'; [|discriminate].
      destruct (rt_lit_inv _ _ _ _ El') as (Eo & Ev & Ew & Hs & Hw).
      apply andb_prop in Hc as [Hc Hj]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      unfold cell_holds. rewrite Eo, Ev, Ew. rewrite (soff_lit_small rho o' Hs). split; [lia|]. split; [lia|].
      cbn [eval]. unfold oaddr. fold b.
      assert (EA : bv_unsigned (Z_to_bv 64 (b + o')) = b + o') by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; lia).
      apply rd_bytes_of_nth; [apply enc_bytes_length | rewrite EA; lia |].
      intros j Hjn. rewrite EA.
      pose proof (proj1 (forallb_forall _ _) Hj (Z.of_nat j) (rt_seq_in w' (Z.of_nat j) ltac:(lia))) as Hjj.
      unfold rt_just in Hjj. apply existsb_exists in Hjj as (c & Hin & Hcj).
      destruct (rt_lit c) as [[[oc wc] vc]|] eqn:Elc; [|discriminate].
      apply andb_prop in Hcj as [Hcj Hbyte]. apply andb_prop in Hcj as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2. apply Z.eqb_eq in Hbyte.
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as Hch.
      pose proof (rt_cell_byte rho ms (ob_base o) lo hi c oc wc vc (o' + Z.of_nat j - oc) b Hb0 Hb1 eq_refl Hch Elc ltac:(lia)) as Hr.
      replace (b + oc + (o' + Z.of_nat j - oc)) with (b + o' + Z.of_nat j) in Hr by lia. rewrite Hr. f_equal.
      unfold rt_byte in Hbyte. rewrite Nat2Z.id in Hbyte. apply bv_eq. exact Hbyte.
    + apply Forall_forall. intros c Hin. apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) Hcells c Hin).
  - intros off Hoff Hnc. apply Hd; [exact Hoff|]. intros Hcov. apply Hnc. unfold covered in *.
    apply Exists_exists in Hcov as (c & Hin & Hic). apply Exists_exists.
    destruct (dropf c) eqn:Edc.
    + assert (Hind : In c (List.filter dropf (ob_cells o))) by (apply filter_In; split; assumption).
      pose proof (proj1 (forallb_forall _ _) Hdrop c Hind) as Hcd. unfold rt_check_drop in Hcd.
      destruct (rt_lit c) as [[[oc wc] vc]|] eqn:Elc; [|discriminate].
      destruct (rt_lit_inv _ _ _ _ Elc) as (Eo & Ev & Ew & Hs & Hw).
      unfold in_cell in Hic. rewrite Eo, Ew in Hic. rewrite (soff_lit_small rho oc Hs) in Hic.
      pose proof (proj1 (forallb_forall _ _) Hcd (off - oc) (rt_seq_in wc (off - oc) ltac:(lia))) as Hex.
      apply existsb_exists in Hex as (c2 & Hin2 & Hc2). exists c2. split; [apply in_or_app; left; exact Hin2|].
      unfold rt_covers in Hc2. destruct (rt_lit c2) as [[[o2 w2] v2]|] eqn:El2; [|discriminate].
      destruct (rt_lit_inv _ _ _ _ El2) as (Eo2 & _ & Ew2 & Hs2 & _).
      apply andb_prop in Hc2 as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
      unfold in_cell. rewrite Eo2, Ew2. rewrite (soff_lit_small rho o2 Hs2). lia.
    + exists c. split; [apply in_or_app; right; apply filter_In; split; [exact Hin | rewrite Edc; reflexivity] | exact Hic].
  - destruct (ob_dflt o); try discriminate; exact I.
Qed.

Lemma retile_obj_shape : ltac2:(tb__ "0|0|
S14S13S3F_;S8S13A1S14S2bS5S14A1S38R4R3R2A3S7S14R1A2A3S2cS2bS12S18R2A1S18R5A1A3S2cS2bS12S1aR2A1S1aR5A1A3S2bS12S19R2A1S19R5A1A3A2A2F_;Fo';Fnews;Fdropf;Fo;").
Proof using .
  intros o dropf news o' Hz. unfold retile_obj in Hz.
  destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate.
  match type of Hz with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection Hz as <-. cbn. repeat split; reflexivity.
Qed.

Theorem smatch_retile : ltac2:(tb__ "0|0|
S17S15SeS13S3F_;S8S13A1S15S4S8S53A1S52A2S2bS5S15A1S3bR6R5R4R3A4S7S15R2A2A3S2bS3S22R3A1SbA3S21Vsegs;R9R8R3A4S21Vsegs;RaR5R4A4F_;F_;F_;Fw;FS';Fnews;Fdropf;Fi;FS;Frho;").
Proof using .
  intros rho S i dropf news S' [tr [ms md]] Hz HwfS' Hsm.
  unfold retile_at in Hz.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (retile_obj o dropf news) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as <-.
  pose proof (retile_obj_shape o dropf news o' Ho') as (Eb & Elo & Ehi).
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. reflexivity. }
  pose proof (retile_obj_holds rho ms o dropf news o' Ho' Hoh) as Hoh'.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact HwfS'|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPA_retile : ltac2:(tb__ "0|0|
S51S17S58SeS13S3F_;S8S13A1S15S8S43Q40A1A1S54S2bS5S15A1S3bS56R7A1R6R5R4A4S7S15R3A2A3S2bS3S22R4A1SbA3S50Vsegs;RbR9RaR4R3A6S50Vsegs;RcS57RaR6A2RbR5R4A6F_;F_;F_;Fw;Ftp;FS';Fnews;Fdropf;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i dropf news S' tp [tr [ms md]] Hz HwfS' [(Hsm & HMI & Hwf' & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_retile rho (ax_S A) i dropf news S' _ Hz HwfS' Hsm) as Hsm'.
  unfold retile_at in Hz.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (retile_obj o dropf news) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as E'.
  pose proof (retile_obj_shape o dropf news o' Ho') as (Eb & Elo & Ehi).
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  split; [exact Hsm'|]. split; [exact HMI|].
  assert (EN : ss_next S' = ss_next (ax_S A)) by (rewrite <- E'; reflexivity).
  split; [unfold axwf in Hwf' |- *; cbn [ax_S ax_X ax_base ax_setS] in Hwf' |- *; rewrite EN; exact Hwf'|].
  split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  rewrite <- E'. cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *. rewrite Eb, Elo, Ehi in Hx. exact Hx.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

End WithSegs.
End ObjRetileB.

