(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "false"; "nat"; "option"; "andb"; "pair"; "fst"; "snd"; "Some"; "app"; "cons"; "nil"; "None"; "length"; "negb"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sprop"; "ss_next"; "SLit"; "holds"; "ss_facts"; "rm"; "SVar"; "ob_base"; "ss_objs"; "cell"; "obj_range"; "ss_lenient"; "sstate"; "sv_below"; "agree_below"; "mkCell"; "dflt_writable"; "eval"; "ob_dflt"; "ob_hi"; "ob_lo"; "SPUle"; "SPUlt"; "ob_cells"; "soff"; "ext_low"; "mkSS"; "rd_bytes"; "rl"; "rw"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "sv_eqb"; "swf"; "DUnknown"; "SAlu"; "mkObj"; "oaddr"; "obj_hi_of"; "obj_lo_of"; "rom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "ax_base"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "NDA"; "tvinA"; "amode"; "am_subst"; "fr_sub_eqb"; "TPA"; "frinA"; "JLA"; "am_eqb"; "fbinA"; "ffinA"; "JA"; "ok_frameKA"; "JAi"; "frv"; "nodeIA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "eqb"; "sub"; "ltb"; "opp"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF.WithSegs.Sum.Phis"; "efnode"; "fnode"; "ef_state"; "ef_var"; "VK"; "ef_rank"; "phiK"; "echeckJAF"; "efdrop"; "nodeIAF"; "eecheckJAF"; "enodeIAF"; "echeckJAF_pf"; "ef_k"; "ef_nd"; "efmeasA"; "ejcertAF"; "jcertAF"; "eecheckJAF_pf"; "eecheckJAF_ref"; "ejcertAF_ref"; "jcertAF_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "lform"; "bd_nn"; "bsumK"; "bsumV"; "bd_subst"; "batom"; "wformK"; "wformV"; "ASv"; "BUD"; "bi_c"; "bi_f"; "bi_k"; "bi_v"; "lf_neg"; "lf_nonneg"; "lf_nonneg_p"; "bival"; "bxt"; "item_le"; "item_le_p"; "item_nonneg"; "item_nonneg_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "jnodeA"; "enodeA"; "edge_okA"; "cfg_edgesA"; "cfg_edgesA_pf"; "eedge_okA"; "ena_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF.WithSegs.Sum"; "JAF"; "V_below"; "bud_le2"; "bud_pay2_p"; "bud_pay2_ref"; "bitem_eqb"; "bud_le_pos2"; "bud_le_pos2_p"; "carve_site_ok"; "echeckJA2"; "item_nn2"; "wsub_id_on"; "bud_le2_pf"; "bud_le2_ref"; "bud_pay2"; "carve_objs_chk"; "echeckJA2_pf"; "item_nn2_p"; "lform_eqb"; "phi_reads"; "robj_ownframe_off"; "robj_stackN"; "xrs47_chk"; "carve_ent_stateA"; "carve_site_chk"; "ent_cells"; "ent_obj"; "xr_lit47";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "aa_live"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "HIGH_SHADOW_END"; "fs_frame_size"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "remove_nth"; "FBx"; "tv_sub_eqb"; "tvd"; "T_ok"; "tvv"; "T0"; "robj_tracked"; "svT"; "tnz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "pfacts"; "mk_pf"; "prove_sprop_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "le"; "ltb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "sv_subst"; "rho_absorb"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "list_set"; "uleq"; "LROk"; "load_fresh"; "load_res"; "obj_add_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF.WithSegs"; "JAF"; "add_cell8_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "is_shadowZ"; "robj_stackA"; "xr_tracked"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "le_bytes_to_word"; "bytes_le_to_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "drop_lastA"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF.WithSegs.PostsP"; "JLAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robj_image"; "robj_ownframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Lemma U_le_bytes_to_word8 : ltac2:(tb__ "0|1|
S1S72Q8A1M0A1S16S5S10G0R1A2U8A3S16S13S73Q40S118R2A1A2S119R2A1A3F_;Fbs;").
Proof.
  intros bs L. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  change (8 * Z.of_nat 8) with 64 in B. apply bv_wrap_small. exact B.
Qed.

Lemma rd64_of_listed : ltac2:(tb__ "0|5|
S72Q40M0A1S6S72Q8M1A1M2A1M3F_;S13S1G2A1S16S5S10G2R1A2U8M4A3S5S123R1G4A2S16G3R6S74G0S68R5S71R2A1A2A2A1SbG2SabG2R2R4S74G1Z0A2A4A2A3F_;Fj;S16S6S13A1Se4R5R4A2SbS13S119R3A1A2A3F_;F_;Fbs;Fa;Fm;").
Proof.
  intros m a bs L H. unfold rd64. rewrite (bytes_at_of_nth m 8 a bs L H). reflexivity.
Qed.

Lemma rd64_bytes_eq : ltac2:(tb__ "0|5|
S72Q40M0A1S6S72Q8A1A1M1F_;M2G2S13S13S16S6S13A1M3Se4R4R2A2SbS13R1A2A3S16G3Se4R4R3A2SbS13R2A2A3S13S17S67R5R1A2S69R1S68R5Z8A2A2A2S16G1R8S74G0R2A2M4A1R7G4A1A3F_;Fz;F_;F_;Fv;Fa;Fm2;Fm1;").
Proof.
  intros m1 m2 a v H1 H2 z Hz. replace z with (a + Z.of_nat (Z.to_nat (z - a))) by lia.
  rewrite (rd64_enc_bytes m1 a v H1) by lia. rewrite (rd64_enc_bytes m2 a v H2) by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.

Definition add_cell8_state (S : sstate) (i : nat) (o : sobj) (off : sv) : sstate := ltac2:(tb__ "0|1|
S39S3fVS;A1S40VS;A1S3eVS;A1S3dVS;A1S41VS;A1S10cS1eS27VS;A1Vi;S111Vo;Voff;Z8S25S20VS;A1M0A1A4A4S23VS;A1SfeG0A1S2aVS;A1A9").

Lemma load_fresh_eq8 : ltac2:(tb__ "0|0|
S2bS5S1eS1cS16S0S2fS31R2A1A1S3A3S16S110S10fR5R4R3R2Z8S4Q40A7S10eS25S20R5A1A1S114R5R4R3R2A4A2A3F_;Foff;Fo;Fi;FS;").
Proof using .
  intros S i o off Hw. unfold load_fresh, fresh. rewrite Hw. reflexivity.
Qed.

Lemma SPA_add_cell8 : ltac2:(tb__ "0|6|
Sa6S1dS1S72Q40M0A1M1A1S4bS5S1eS1cS1Sc1A1M2S101Sc0Sa7Vsegs;S20S4cR7A1A1RaA3S16S6S1eA1SadS1eS27S4cR8A1A1R7A3SbS1eR6A2A3S16S0S2fS31R7A1A1S3A3S16S0S2cS20S4cRaA1A1R7A2S3A3S67S49RdR9A2S37RdR8A2A2S67S68S37ReR9A2Z8A2S48ReRaA2A2Sa5Vsegs;R10RdRfReS8G2Se2R9Se3R8R7A2A4A6S1aS1S72Q8A1A1M3G3S1aS1dS1dS17S16S6G3A1S3aS112RaR11RbA3S47R12S26ReA1S37R12RdA2A3U8A3SbG3R2A2A3S17S2dS20S4cR10A1M4A1M5R12R1A3S17S16G1S30R1S25G5A1A2S38S4G0S118R2A1A3A3Sa5Vsegs;R13S4dR10S114G4RfReRdA4A2R1R11S8G2Se2RcSe3RbRaA2A4A6A2A2A2Lrho';A2Lbs;A2F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Foff;Fo;Fi;FA;Ftp;Frho;FJ;").
Proof using .
  intros J rho tp A i o off tr ms md Hst Hnth Hw Hoff Hlo Hhi [(Hsm & HMI & Hax & Hsh & Hz) HJ].
  pose proof (smatch_swf _ _ _ _ Hsm) as Hswf.
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  assert (Hall : Forall (obj_holds segs rho (vms md tp ms)) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  pose proof (proj1 (Forall_forall _ _) Hall o (nth_error_In _ _ Hnth)) as Hoh.
  pose proof (swf_obj_nth _ _ _ Hswf Hnth) as Howf.
  pose proof (load_fresh_sound segs rho (ax_S A) tr (vms md tp ms) (vmd md) i o off 8 false (SVar (ss_next (ax_S A))) (add_cell8_state (ax_S A) i o off)
                Hsm ltac:(lia) Hnth Hoh Howf Hoff Hlo Hhi (load_fresh_eq8 _ _ _ _ Hw)) as LP.
  destruct LP as (bs & rho' & Hrd & Hag & Hle & Hsm' & Hev & _).
  exists bs, rho'. split; [exact Hrd|]. split; [exact Hag|]. split; [exact Hev|].
  split.
  - split; [|split; [exact HMI | split; [|split; [|exact Hz]]]].
    + unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS]. exact Hsm'.
    +
      unfold axwf in Hax |- *. cbn [ax_S ax_X ax_base ax_setS add_cell8_state ss_next].
      apply andb_prop in Hax as [HX Hb]. apply andb_true_intro. split.
      * apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
        unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
        apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
      * eapply sv_below_mono; [|exact Hb]. lia.
    +
      eapply (shadow_ok_stable A (ax_setS A (add_cell8_state (ax_S A) i o off)) rho rho' Hag Hax Hswf eq_refl eq_refl); [|exact Hsh].
      unfold exts. cbn [ax_S ax_setS add_cell8_state ss_objs].
      revert Hnth. clear. generalize (ss_objs (ax_S A)) as l. intros l. revert i.
      induction l as [|a l IH]; intros [|i] Hn; cbn in Hn |- *; try discriminate.
      * injection Hn as ->. unfold obj_add_cell, obj_ext. destruct o; reflexivity.
      * f_equal. apply IH. exact Hn.
  - eapply Hst; [exact Hag | | exact HJ]. apply mat_equiv_refl.
Qed.

Lemma add_cell8_value : ltac2:(tb__ "0|7|
S1dS1dS101S72Q40M0A1M1S1S72Q8A1M2A1M3S1cS4aVsegs;R4A2S16S6G3A1S3aR5R4U8A3SbG3R3A2A3S67Se5S73G0R5A2A2S67S68S73G0R6A2Z8M4A2S6bZ2Z3fA2A2S13S17S67S73G0R8A2M5R1A2S69R1S68G5G4A2A2A2S16S6G2A1S102RaS74G0R2A2M6A2S24RcG6A2A3F_;Fz;S16G1S30RaR6A2S38S4G0S118R7A1A3A3S16S6S13A1Se4S24RcA1S73G0R9A2A2SbS13S73G0S30RbR7A2A2A2A3F_;F_;F_;F_;F_;F_;Fx;Fbs;Fa;Fms;Frho';Frho;").
Proof using HTOP.
  intros rho rho' ms a bs x Hrom Hrd Hlo Hhi Hfr Hev.
  pose proof (rd_bytes_length _ _ _ _ Hrd) as L. pose proof (bv_urange a) as Ra.
  rewrite Hev, ext_low_64, (U_le_bytes_to_word8 bs L).
  apply (rd64_of_listed (rm rho) (bv_unsigned a) bs L). intros j Hj.
  rewrite <- (Hfr (bv_unsigned a + Z.of_nat j)) by lia.
  pose proof (rd_bytes_nth ms 8 a bs j Hrd Hj ltac:(lia)) as RB.
  rewrite (rd_high segs HTOP) in RB; [exact RB | exact Hrom | rewrite u64_of_sum by lia; lia].
Qed.

Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
SdeS1dS1S72Q40A1A1Sc0OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S126Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S13S121VCST;R1A2S17S67Z0R2A2S69R2Se5A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S13S121VXGL;R1A2S17S67Z0R2A2S69R2Se5A2A2F_;Fa;").

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2S13S13A2S13A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Hypothesis HNP : NP_okA NP.

Let JAi : ltac2:(tb__ "0|0|
S51SdeS13Sa6Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S64VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S51Sa6Fnd;") := ltac2:(tb__ "0|0|
S62VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma tracked_block_facts : ltac2:(tb__ "0|6|
SdeS1dS1S72Q40A1A1Sc0S1S2S1cS1cA2M0A1S5G0VAInv;R7R6R5R4A4S58VFB;R8R7R4A4Sf2R8R5A2SeeR9R6A2S16S6G0A1SadG0R7R6A3SbG0R5A2A3S69Z0SaS13S13Sf4RbR6A2A3A2S17Sf8RcR7A2S17SacS2S13S13A2M1Sf4RcR7A2M2Se1RdA1A3S17S19SacG1G2VFB;A3A1S17S19SacG1G2Sf0VFB;RcSefG0R8R9A3A3A3A1S17S67S68Se5Z1000A2S9S13S13G2A3M3A2S17S67S68S68G3SaS13S13G2A3A2M4Z800A2Se0SdfRdA1A1M5A2S17S18S67G4Se6A2S67Se7G3A2A2S67G5Z7fffff800000A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;Ft;Fj;Ftv;Fmd;Ftp;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho tp md tv j t HM HN HD HZ Hj Hpos. pose proof (nth_error_In _ _ Hj) as Hin.
  assert (Hnz : tnz rho t).
  { intros Hz0. pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz0)) as Z0. lia. }
  destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (_ & Hlive & Hnfb).
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & HBl & _).
  destruct (tvv rho t) as [b n] eqn:Et. cbn [fst snd] in *.
  destruct (HBl b n Hlive) as (G1 & G2 & G3 & G4 & (G5 & G6 & G7 & G8)).
  split; [exact Hnz|]. split; [exact Hlive|]. split; [exact Hnfb|]. split.
  - intros HinX. apply In_FBx in HinX as [HinX|(t' & Ht' & Hnz' & Heq)]; [exact (Hnfb HinX)|].
    apply (tvd_nth_distinct rho tv j t t' HD Hj Ht' Hnz Hnz'). rewrite Et. exact Heq.
  - repeat split; (exact G6 || lia).
Qed.

Lemma tracked_block_free : ltac2:(tb__ "0|3|
SdeS1dS1S72Q40A1A1Sc0S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S5G0S13VAInv;R9R8R7R6A4S60VFB;RaA2S61VFF;RbA2S5cVrho0;RcA2S58VFB;RdRcR9A4Sf2RdRaA2SeeReRbA2S5dVFF;R10RfRbA4S16S6G0A1SadG0RdRbA3SbG0RaA2A3S69Z0SaS13S13Sf4R11RbA2A3A2S17S67S9S13S13Sf4R12RcA2M1A3M2RbA2S69RbS68G2SaS13S13G1A3A2A2A2S19S109VCST;Vrho0;Sf0VFB;R13SefG0ReR10A3A3S10aVFF;R13RfA3RcA5A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Ft;Fj;Ffr;Ftv;Fmd;Ftp;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho tp md tv fr j t a HM HB HFF HT HN HD HZ HFR Hj Hpos Ha Hp.
  destruct (tracked_block_facts Ai rho tp md tv j t HM HN HD HZ Hj Hpos) as (Hnz & Hlive & Hnfb & HnX & _).
  assert (HNr : tvinA FB Ai rho (remove_nth j tv ++ [])).
  { rewrite app_nil_r. unfold tvinA in HN |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht'. }
  destruct (tvv rho t) as [b n] eqn:Et. cbn [fst snd] in *.
  eapply (live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md (FBx FB rho (remove_nth j tv)) (FFx FF rho fr) b n a HM);
    [apply (fbinA_FBx FB Ai rho (remove_nth j tv) []); [exact HB | exact HNr] | apply ffinA_FFx; [exact HFF | exact HFR] | exact HT | exact Hlive | exact HnX | exact Ha | exact Hp].
Qed.

Definition carve_site_ok (A : axst) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (j : nat) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
SdeS1S72Q40A1A1Sc0SaaS1fS22Vrho;A1S23S4cVA;A1M0A1A3VP0f;Vrho0;A1S11dVNP;Vrho0;Vrho;A3VAInv;R6Vrho;R5R4A4S5cVrho0;R7A2Sf3Vrho;Se0SdfR8A1A1A2S60VFB;R9A2S61VFF;RaA2S58VFB;RbVrho;Vtv;A4Sf2Vrho;Vtv;A2SeeVrho;Vtv;A2S5dVFF;ReVrho;Vfr;A4S17S1eS13SacS1eR2S27G0A1A3S17S67S9S13S13S29Vrho;R3A2M1A3R2A2S69R2SaS13S13G1A3A2A2S18S109VCST;Vrho0;Sf0VFB;Vrho;SefS2S1cS1cA2Vj;Vtv;A3A3S10aVFF;Vrho;Vfr;A3R3A5S18S17S67Z0R3A2S69R3Se5A2A2S115R3A1A2A2F_;F_;Fa;Fo;S11cVrho;S4eVA;A1A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;FAi;").

Lemma JA_carve_tr : ltac2:(tb__ "0|c|
S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S1S8cA1S59S5S1cS1cS1cS1cS4bS1dS1S72Q40M1A1A1S1Sc1A1M2S101Sc0S16S6G0A1SadG0RfRbA3SbG0S8S1cS1cRaR9A4A2A3S16S1cS4fR7A1S21Se6A1A3S16S0S43S4cS11aR8RaR9A3A1A1S3A3S1dSaaS1fS22R1A1S23S4cRaA1A1A3S17S67S8bR2RfA2M3S8bR2RdA2M4A2S17S67S68G4S8bR2RcA2M5A2S68G3S8bR2ReA2A2A2S69Z0G5A2A2A2F_;Fr;ScaRaR13R12RfR9A5S13S17S67S8bRbReA2M6R1A2S69R1S68G6S8bRbRdA2A2A2A2S19S16S6S72Q8A1M7A1M8S24RcS74G1R2A2M9A2SfG7A1A3A1F_;Fz;Sa5Vsegs;VJA;S57R15R14R13R12A4A1RcRbRaS8G2Se2R9Se3R8R7A2A4A6S17Sa5Vsegs;VJA;S57R16R15R14R13A4A1S11aRdRfReA3RcRbS8G2Se2RaSe3R9R8A2A4A6S17S13S17S67S8bRdR10A2MaR1A2S69R1S68GaS8bRdRfA2A2A2A2S16G8S102S112RaRdRbA3G9A2S24ReG9A2A3F_;Fz;S17S67S68Se5Z1000A2S8bRcRfA2MbA2S67S68S68GbS8bRcReA2A2Z800A2S6bZ2Z2fA2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA;Fsz;Fbase;Ftsz;Ftd;Fj;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HNP.
  intros tv fr bd am j td tsz base sz A rho tp tr ms md Hnth Hbase Hwf HIN HSITE Hdef [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HIN rho HF) as (S1 & S2 & S3).
  destruct (HSITE Ai tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as [HROK HX47].
  set (t := (td, tsz)) in Hnth.
  assert (Et : tvv rho t = (uval rho td, uval rho tsz)) by reflexivity.
  pose proof (uval_range rho base) as Rb. pose proof (uval_range rho td) as Rd. pose proof (uval_range rho tsz) as Rsz. pose proof (uval_range rho sz) as Rn.
  assert (Hpos : 0 < snd (tvv rho t)) by (rewrite Et; cbn [snd]; lia).
  destruct (tracked_block_facts Ai rho tp md tv j t HM HN HD HZ Hnth Hpos) as (Hnz & Hlive & Hnfb & HnX & G5 & G4 & G6 & G8).
  rewrite Et in G5, G4, G6. cbn [fst snd] in G5, G4, G6. top_rng G4.
  set (n := uval rho sz) in *. set (b := uval rho base) in *.
  enough (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho o') (b, b + n)) (ss_objs (ax_S A))).
  { split; [split; [|exists Ai, kc; exact HJ]|split; [|lia]].
    2: { intros z Hz. pose proof Hsm as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _) & _).
         cbn [virt fst snd cfg_ms cfg_model] in Hfr. apply Hfr. unfold outside_all. apply Forall_forall. intros o Ho.
         pose proof (proj1 (Forall_forall _ _) DISJ o Ho) as D. cbv beta in D. unfold ranges_disjoint in D. cbn [fst snd] in D.
         rewrite u64_of_sum by lia. lia. }
  pose proof (SPA_carve_plain segs (JAi (NDA tv fr bd am) Ai kc) rho A tp (tr, mkCfg ms md) base sz (ss_next (ax_S A)) (conj Hsm HJ)) as SP.
  cbn zeta in SP. change (bv_unsigned (eval rho sz)) with n in SP. change (bv_unsigned (eval rho base)) with b in SP.
  specialize (SP ltac:(unfold carve_stateA in Hwf; exact Hwf) ltac:(lia) ltac:(lia) ltac:(lia)).
  specialize (SP DISJ ltac:(intros z Hz; destruct (rm rho (Z_to_bv 64 z)) as [x|] eqn:Ex; [exists x; reflexivity | exfalso; exact (Hdef z Hz Ex)])).
  assert (XCL : xwords_clear rho A b (b + n)).
  { intros rr y jj Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    pose proof (HX47 rr y Hr Hy) as Hy47.
    pose proof (word_byte_of_shadow (Sh y) jj (Sh_is_shadow y Hy47) Hj) as WS.
    destruct (word_byte_range (Sh y) jj ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
    rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
    unfold is_shadowZ, HIGH_SHADOW_END in WS, G6. lia. }
  specialize (SP XCL).
  assert (EQS : ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                               (ss_objs (ax_S A) ++ [plain_obj base sz]) (ss_facts (ax_S A)) (ss_next (ax_S A)) (ss_lenient (ax_S A)))
                = carve_stateA A base sz).
  { destruct A as [S X bb]. destruct S. reflexivity. }
  rewrite EQS in SP. exact (proj1 SP). }
  apply Forall_forall. intros o Ho'. destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
  destruct (HROK o a Ho' ltac:(rewrite Eo; exact Ha1)) as [Hp|[Himg|Hsh]].
  - exact (tracked_block_free Ai rho tp md tv fr j t a HM HB HFF HT HN HD HZ HFR Hnth Hpos ltac:(rewrite Et; cbn [fst snd]; lia) Hp).
  - unfold IMG_HI in *. lia.
  - unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in Hsh, G6. lia.
Qed.

Definition ent_cells (x : positive) : list cell := ltac2:(tb__ "0|1|
SdS28S2eS21Z8M0A1G0S25SfeVx;A1A1A3SdS28S2eS21Z0A1G0S25Vx;A1A3SeS28A1A3A3").
Definition ent_obj (base : sv) (x : positive) : sobj := ltac2:(tb__ "0|0|
S46Vbase;S21Z0A1S21Z10A1SdbVx;A1S44A5").
Definition carve_ent_stateA (A : axst) (base : sv) : axst := ltac2:(tb__ "0|1|
S4cVA;A1S2bS4dVA;S39S3fR1A1S40R1A1S3eR1A1S3dR1A1S41R1A1ScS1eS27R1A1SdS1eSdcVbase;S20R1A1M0A2SeS1eA1A3A3S23R1A1SfeSfeG0A1A1S2aR1A1A9A2TS;").

Lemma ax_S_setS : ltac2:(tb__ "0|0|
S4bS2bS16S2bS4cS4dR2R1A2A1R1A3FS;FA;").
Proof. intros [a b c] S. reflexivity. Qed.
Lemma ax_setS_setS : ltac2:(tb__ "0|0|
S4bS2bS2bS16S4bS4dS4dR3R2A2R1A2S4dR3R1A2A3FS';FS;FA;").
Proof. intros [a b c] S S'. reflexivity. Qed.

Lemma list_set_last {T} : ltac2:(tb__ "0|2|
S1VT;A1M0VT;VT;S16G0S10cVT;ScVT;R3SdVT;R2SeVT;A1M1A3A3S10VT;R3A2R1A4ScVT;R3SdVT;R1G1A3A3A3Fy;Fx;Fl;").
Proof. induction l as [|a l IH]; intros x y; cbn; [reflexivity | f_equal; apply IH]. Qed.
Lemma nth_error_last {T} : ltac2:(tb__ "0|0|
S1VT;A1VT;S16S6VT;A1SadVT;ScVT;R2SdVT;R1SeVT;A1A3A3S10VT;R2A2A3SbVT;R1A2A3Fx;Fl;").
Proof. intros l x. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma JA_carve_ent : ltac2:(tb__ "0|c|
S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S1S8cA1S59S5S1cS1cS1cS4bS1dS1S72Q40M1A1A1S1Sc1A1M2S101Sc0S16S6G0A1SadG0ReRaA3SbG0S8S1cS1cR9R8A4A2A3S16S1cS4fR7A1S21Se6A1A3S16S0S43S4cS11aR8R9S21Z10M3A1A3A1A1S3A3SffVNP;S20S4cR9A1A1A2S16S0S52S20S4cRaA1A1S57R12R11R10RfA4A2S3A3S1dSaaS1fS22R1A1S23S4cRcA1A1A3S17S67S8bR2R10A2M4S8bR2ReA2M5A2S67S68G5G3A2S68G4S8bR2RfA2A2A2A2F_;Fr;ScaRcR14R13R10RbA5S13S17S67S8bRdRfA2M6R1A2S69R1S68G6G3A2A2A2S19S16S6S72Q8A1M7A1S24ReS74G1R2A2A2SfG7A1A3A1F_;Fz;Sa5Vsegs;VJA;S57R16R15R14R13A4A1ReRdRcS8G2Se2RbSe3RaR9A2A4A6S1aS1dS1dS17S2dS20S4cR10A1A1M8RfR1A3S17S16S6S13A1M9Se4S24RfA1MaS8bRfR11A2MbA2SbS13S8bR1S25G8A1A2A2A3S17S16G9Se4GaS68GbZ8A2A2SbS13S8bR1S25SfeG8A1A1A2A2A3Sa5Vsegs;VJA;S57R18R17R16R15A4A1Sd9R10R11A2R1ReS8G2Se2RdSe3RcRbA2A4A6A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA;Fbase;Ftsz;Ftd;Fj;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HNP HKc HTOP.
  intros tv fr bd am j td tsz base A rho tp tr ms md Hnth Hbase Hwf Hnp Hnb HIN HSITE Hdef HS.
  pose proof (proj1 (proj1 HS)) as Hsm0.
  destruct (JA_carve_tr tv fr bd am j td tsz base (SLit 16) A rho tp tr ms md Hnth Hbase Hwf
              ltac:(intros r Hr; rewrite (uval_lit r 16) by lia; destruct (HIN r Hr); lia) HSITE ltac:(rewrite (uval_lit rho 16) by lia; exact Hdef) HS) as (SP0 & FR & Hlo & Hhi).
  rewrite (uval_lit rho 16) in FR, Hhi by lia.
  set (nx := ss_next (ax_S A)) in *.
  set (A0 := carve_stateA A base (SLit 16)) in *.
  set (objs := ss_objs (ax_S A)). set (o := plain_obj base (SLit 16)). set (i := length objs).
  assert (Hobjs0 : ss_objs (ax_S A0) = objs ++ [o]) by reflexivity.
  assert (Hnx0 : ss_next (ax_S A0) = nx) by reflexivity.
  assert (Hb : sv_below nx base = true).
  { pose proof (swf_obj_nth (ax_S A0) i o Hwf ltac:(rewrite Hobjs0; apply nth_error_last)) as W. rewrite Hnx0 in W.
    unfold obj_wf in W. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. exact W. }
  pose proof (uval_range rho base) as Rb.

  destruct (SPA_add_cell8 (JA (NDA tv fr bd am)) rho tp A0 i o (SLit 0) tr ms md) as (bs0 & rho1 & Hrd0 & Hag0 & Hev0 & SP1).
  { rewrite Hnx0. apply (stableA_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA); [exact Hnp | exact Hnb]. }
  { rewrite Hobjs0. apply nth_error_last. }
  { reflexivity. }
  { reflexivity. }
  { unfold obj_lo_of, o, plain_obj. cbn [ob_lo]. rewrite !soff_lit_small by lia. lia. }
  { unfold obj_hi_of, o, plain_obj. cbn [ob_hi]. rewrite !soff_lit_small by lia. lia. }
  { exact SP0. }
  set (A1 := ax_setS A0 (add_cell8_state (ax_S A0) i o (SLit 0))) in SP1.
  set (o1 := obj_add_cell o (SLit 0) 8 (SVar nx)).
  assert (Hobjs1 : ss_objs (ax_S A1) = objs ++ [o1]).
  { subst A1. rewrite ax_S_setS. unfold add_cell8_state. cbn [ss_objs]. rewrite Hobjs0, Hnx0. apply list_set_last. }
  assert (Hnx1 : ss_next (ax_S A1) = Pos.succ nx).
  { subst A1. rewrite ax_S_setS. unfold add_cell8_state. cbn [ss_next]. rewrite Hnx0. reflexivity. }

  destruct (SPA_add_cell8 (JA (NDA tv fr bd am)) rho1 tp A1 i o1 (SLit 8) tr ms md) as (bs1 & rho2 & Hrd1 & Hag1 & Hev1 & SP2).
  { rewrite Hnx1. apply (stableA_mono segs nx); [lia|]. apply (stableA_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA); [exact Hnp | exact Hnb]. }
  { rewrite Hobjs1. apply nth_error_last. }
  { reflexivity. }
  { reflexivity. }
  { unfold obj_lo_of, o1, o, plain_obj, obj_add_cell. cbn [ob_lo]. rewrite !soff_lit_small by lia. lia. }
  { unfold obj_hi_of, o1, o, plain_obj, obj_add_cell. cbn [ob_hi]. rewrite !soff_lit_small by lia. lia. }
  { exact SP1. }
  rewrite Hnx1 in Hag1, Hev1.
  exists rho2.
  assert (Hag : agree_below nx rho rho2).
  { eapply agree_below_trans; [exact Hag0|]. eapply agree_below_le; [|exact Hag1]. lia. }
  pose proof Hsm0 as (_ & _ & _ & _ & Hrom & _). cbn [virt fst snd cfg_ms cfg_model] in Hrom.
  assert (Eb0 : bv_unsigned (oaddr rho (ob_base o) (soff rho (SLit 0))) = uval rho base).
  { unfold o, plain_obj. cbn [ob_base]. rewrite soff_lit_small by lia. rewrite oaddr_unsigned by (unfold uval in *; lia). unfold uval. lia. }
  assert (Eb1 : bv_unsigned (oaddr rho1 (ob_base o1) (soff rho1 (SLit 8))) = uval rho base + 8).
  { unfold o1, o, plain_obj, obj_add_cell. cbn [ob_base]. rewrite soff_lit_small by lia.
    rewrite oaddr_unsigned by (rewrite <- (eval_agree nx rho rho1 base Hag0 Hb); unfold uval in *; lia).
    rewrite <- (eval_agree nx rho rho1 base Hag0 Hb). reflexivity. }
  split; [exact Hag|]. split; [|split].
  - rewrite <- Eb0. apply (add_cell8_value rho rho2 (vms md tp ms) _ bs0 (SVar nx) Hrom Hrd0); rewrite ?Eb0; [lia | lia | |].
    + intros z Hz. apply FR. lia.
    + rewrite <- Hev0. symmetry. apply (eval_agree (Pos.succ nx) rho1 rho2 (SVar nx) Hag1). cbn. apply Pos.ltb_lt. lia.
  - rewrite <- Eb1. apply (add_cell8_value rho rho2 (vms md tp ms) _ bs1 (SVar (Pos.succ nx)) Hrom Hrd1); rewrite ?Eb1; [lia | lia | |].
    + intros z Hz. apply FR. lia.
    + exact Hev1.
  - enough (EQS : ax_setS A1 (add_cell8_state (ax_S A1) i o1 (SLit 8)) = carve_ent_stateA A base) by (rewrite <- EQS; exact SP2).
    subst A1 A0. unfold carve_stateA, carve_ent_stateA, add_cell8_state. rewrite !ax_S_setS. cbn. rewrite !ax_setS_setS. cbn.
    subst i o1 o. rewrite !list_set_last. reflexivity.
Qed.

Lemma JA_absorb_tr : ltac2:(tb__ "0|10|
S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S1S8cA1S59S5S1cS1cS4bS1S1eA1M1S1eS1cS1dS1S72Q40M2A1M3A1S1Sc1A1M4S101Sc0S16G1S27S4cR9A1A1ScS1eR8SdS1eR7SeS1eA1M5A3A3A3S16S6G0A1SadG0R11RdA3SbG0S8S1cS1cRcRbA4A2A3S16S1cS33R9A1S21Z0M6A1A3S16S1cS32RaA1R9A3S16S0S2fS31RbA1A1S3A3S1dSaaS1fS22R1A1S23S4cRfA1A1A3S17S67S8bR2R12A2M7S8bR2S26ReA1A2M8A2S17S67S68G8S8bR2RdA2M9A2S68G7S8bR2R11A2A2A2S69G6G9A2A2A2F_;Fr;Sa5Vsegs;VJA;S57R16R15R14R13A4A1RfRbRaS8G4Se2R9Se3R8R7A2A4A6S107RcSdS1eReG5A3S112R8RbR9A3A3S1dS17Sa5Vsegs;VJA;S57R18R17R16R15A4A1S11bR11R10A2R1RcS8G4Se2RbSe3RaR9A2A4A6S17G3S19S17S67S8bReS26R10A1A2MaS73G2R1A2MbA2S69GbS68GaS8bReRfA2A2McA2A2A1S16S6S72Q8A1MdA1MeS24R3R2A2S24RfR2A2A3F_;Fa;S17S13S17S67GaR1A2S69R1GcA2A2S19S16GeS24R3S74G2R2A2A2SfGdA1A3A1F_;Fz;S13S1cSacS28S2eS21R2A1Z8MfR1A3S36R11A1A3S67G6R3A2S67S68R4GfA2S8bR11R12A2A2S16S6S13A1Se4S24R6A1S68S8bR12S26R14A1A2R5A2A2SbS13S8bR12R4A2A2A3F_;F_;F_;Fv;Foff;A2A2A2Trho';F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fsz;Fo;Fobjs;FA;Ftsz;Ftd;Fj;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HTOP.
  intros tv fr bd am j td tsz A objs o sz rho tp tr ms md Hobjs Hnth Hl Hh Hdw HIN [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF. destruct (HIN rho HF) as (S1 & S2 & S3).
  set (t := (td, tsz)) in Hnth.
  assert (Et : tvv rho t = (uval rho td, uval rho tsz)) by reflexivity.
  pose proof (uval_range rho (ob_base o)) as Rb. pose proof (uval_range rho td) as Rd. pose proof (uval_range rho tsz) as Rsz. pose proof (uval_range rho sz) as Rn.
  assert (Hpos : 0 < snd (tvv rho t)) by (rewrite Et; cbn [snd]; lia).
  destruct (tracked_block_facts Ai rho tp md tv j t HM HN HD HZ Hnth Hpos) as (Hnz & Hlive & Hnfb & HnX & G5 & G4 & G6 & G8).
  rewrite Et in G5, G4, G6, Hlive, Hnfb, HnX. cbn [fst snd] in G5, G4, G6, Hlive, Hnfb. top_rng G4.
  assert (Hnz' : uval rho td <> 0) by (unfold tnz in Hnz; exact Hnz).
  set (d := uval rho td) in *. set (bsz := uval rho tsz) in *. set (b := uval rho (ob_base o)) in *. set (n := uval rho sz) in *.
  assert (Hrng : obj_range rho o = (b, b + n)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hl, Hh. rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
    change (bv_unsigned (eval rho sz)) with n. destruct (Zsigned_spec n) as [[_ X]|[X _]]; [rewrite X; subst b; unfold uval; f_equal; lia | exfalso; lia]. }
  intros rho'.
  assert (OUT : forall a, ~ (b <= bv_unsigned a < b + n) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. exact (Ha Hr). }
  destruct (released_bytesA segs HTOP rho A objs [o] o tp tr ms md Hobjs ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold IMG_HI in *; lia) ltac:(rewrite Hrng; cbn [snd]; lia)) as [BY CELLS].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY, CELLS.
  assert (OUTB : forall a, ~ (d <= bv_unsigned a < d + bsz) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. lia. }
  assert (EV : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  destruct (core_block_write segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho rho' tp md tv fr d bsz HM HB HFF HT HN HD HZ HFR HK0 Hlive Hnfb EV OUTB)
    as (HM' & HTV' & HFR' & HK').
  split; [|split; [exact OUT | split; [exact BY | intros off v Hc Ho1 Ho2; exact (CELLS off v Hc ltac:(lia))]]].
  split; [exact (smatchA_unobj segs rho A objs [o] tp tr ms md Hobjs Hsm)|].
  assert (Hav' : agree_vals NP rho0 rho') by (unfold rho'; cbn; exact Hav).

  assert (TVS : tvals rho' tv = tvals rho tv) by (unfold tvals; apply map_ext; intros t'; unfold tvv; rewrite !EV; reflexivity).
  assert (OTHER : forall b2 n2 z, In (b2, n2) (aa_live Ai) -> untrackedZ (tvals rho tv) (b2, n2) -> b2 <= z < b2 + n2 -> ~ (d <= z < d + bsz)).
  { intros b2 n2 z Hb2 Hut Hz Hz'.
    assert (Hne : (d, bsz) <> (b2, n2)).
    { apply (Hut (d, bsz)); [|cbn [fst]; exact Hnz'].
      unfold tvals. apply in_map_iff. exists t. split; [symmetry; exact Et | exact (nth_error_In _ _ Hnth)]. }
    destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & _ & _).
    apply In_nth_error in Hb2 as [i2 Hi2]. pose proof Hlive as Hl1. apply In_nth_error in Hl1 as [i1 Hi1].
    destruct (Nat.eq_dec i1 i2) as [->|Hne12]; [rewrite Hi1 in Hi2; injection Hi2 as E1 E2; apply Hne; rewrite E1, E2; reflexivity|].
    assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (d, bsz)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
    assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (b2, n2)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
    pose proof (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne12) as D. cbn [fst snd] in D. lia. }
  destruct (XAz_transport FB FB (am_eval rho am) Ai Ai (rm rho) (rm rho') (tvals rho tv) (tvals rho tv) kc HXA) as [XA' PIMP].
  { intros b2 n2 H1 H2 H3. auto. }
  { intros b2 n2 z H1 H2 H3 Hz. destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b2 n2 H1) as (_ & _ & B3 & B4 & _).
    apply OUTB. rewrite u64_of_sum by lia. exact (OTHER b2 n2 z H1 H3 Hz). }
  { intros b2 n2 a H1 H2 H3 Ha. destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b2 n2 H1) as (_ & _ & B3 & B4 & _).
    top_rng B4. assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as SS. split.
    - intros _. rewrite shadow_addr_Sh. apply OUTB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
      unfold is_shadowZ, HIGH_SHADOW_END in SS, G6. lia.
    - intros jj Hj Hdx. rewrite OUTB; [exact Hdx|]. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
      pose proof (word_byte_of_shadow (Sh a) jj SS Hj) as WS. unfold is_shadowZ, HIGH_SHADOW_END in WS, G6. lia. }
  {   intros bn H1 _ H3 H4. auto. }
  assert (EP : apot am rho' = apot am rho).
  { unfold apot. rewrite (am_eval_exteq am rho rho' ltac:(intros e _; apply EV)). exact PIMP. }
  clearbody rho'. exists Ai, kc.
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HTV'|]. split; [exact HFR'|]. split; [exact HK'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. split; [|split; [|exact (conj HPA (conj HCKi (capN_ext _ _ rho rho' _ EV HCNi)))]].
  - unfold XA. rewrite (am_eval_exteq am rho rho' ltac:(intros e _; apply EV)). rewrite TVS. exact XA'.
  - rewrite EP. destruct (bsum_eval_ext bd rho' rho EV) as [E1 E2]. unfold BUD in HBU |- *. rewrite E1, E2.
    destruct HBU as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV.
Qed.

Lemma JA_absorb_ent_same : ltac2:(tb__ "0|c|
S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S1S8cA1S59S5S1cS1cS4bS1S1eA1M1S1eS1cS1cS1dS1S72Q40A1M2A1S1Sc1A1M3S101Sc0S16G1S27S4cRaA1A1ScS1eR9SdS1eR8SeS1eA1M4A3A3A3S16S6G0A1SadG0R12ReA3SbG0S8S1cS1cRdRcA4A2A3S16S1cS33RaA1S21Z0A1M5A3S16S1cS32RbA1S21Z10M6A1A3S16S0S2fS31RcA1A1S3A3SacS28S2eG5Z8M7RcA3S36RdA1A3SacS28S2eS21G7A1G7RcA3S36ReA1A3S1dSaaS1fS22R1A1S23S4cR12A1A1A3S17S67S8bR2R15A2M8S8bR2S26R11A1M9A2MaA2S67S68GaG6A2S68G8S8bR2R14A2A2A2A2F_;Fr;S16S6S13A1MbSe4S24RdA1S8bRdS26R10A1A2A2SbS13S8bRdRfA2A2A3S16GbSe4S24ReA1S68S8bReG9A2G7A2A2SbS13S8bReRfA2A2A3Sa5Vsegs;VJA;S57R1bR1aR19R18A4A1R14RfReS8G3Se2RdSe3RcRbA2A4A6S107R10SdS1eR13G4A3S112RcRfRdA3A3S1dS17Sa5Vsegs;VJA;S57R1dR1cR1bR1aA4A1S11bR16R15A2R1R10S8G3Se2RfSe3ReRdA2A4A6G2S16S6S72Q8A1A1S24R2R1A2S24R12R1A2A3Fa;A2Trho';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fv1;Fv0;Fo;Fobjs;FA;Ftsz;Ftd;Fj;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HTOP.
  intros tv fr bd am j td tsz A objs o v0 v1 rho tp tr ms md Hobjs Hnth Hl Hh Hdw Hc0 Hc1 HIN R0 R1 HS.
  destruct (JA_absorb_tr tv fr bd am j td tsz A objs o (SLit 16) rho tp tr ms md Hobjs Hnth Hl Hh Hdw
              ltac:(intros r Hr; rewrite (uval_lit r 16) by lia; destruct (HIN r Hr); lia) HS) as (SP & OUT & BY & CELLS).
  rewrite (uval_lit rho 16) in OUT, BY, CELLS by lia.
  intros rho'. split; [exact SP|].
  intros a. pose proof (bv_urange a) as Ra. set (b := uval rho (ob_base o)) in *.
  destruct (Z_lt_dec (bv_unsigned a) b) as [L1|L1]; [apply OUT; lia|].
  destruct (Z_lt_dec (bv_unsigned a) (b + 16)) as [L2|L2]; [|apply OUT; lia].
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  destruct (Z_lt_dec (bv_unsigned a) (b + 8)) as [L3|L3].
  - pose proof (CELLS 0 v0 Hc0 ltac:(lia) ltac:(lia)) as C0. rewrite Z.add_0_r in C0.
    apply (rd64_bytes_eq (rm rho') (rm rho) b (uval rho v0)); [exact C0 | exact R0 | lia].
  - apply (rd64_bytes_eq (rm rho') (rm rho) (b + 8) (uval rho v1)); [exact (CELLS 8 v1 Hc1 ltac:(lia) ltac:(lia)) | exact R1 | lia].
Qed.

Definition robj_ownframe_off (fr : list (sv * Z * sv)) (o : sobj) : bool := ltac2:(tb__ "0|11|
S1cS0Lx;M0S26Vo;A1S13S4Lz;S14S4Li;M1Se9S1cS1cSe9S0Lop;R3S1cS0Lb0;R1S13G0S33Vo;A1S13G0S32Vo;A1S13S0S0L_;M2S6aZ0M3R3A2SafS2S2S1cS13A2M4S1cA2M5G5G2S42R6S9S1cS13S9G4S1cR1A3M6A3A2G2S6aG3S68R4R3A2A2G2S6aR3R2A2G2S6aS68R4R2A2Se8SaS1cS13G6A3M7A1M8A2G2S6aR4G8A2G2S6aG3G7A2S6aG7Z6A2S4X0x2S4X0x2S4X0x2S4X0x2S4X0x2S4X0x2Lx;Vfr;A3S4X0x2Lhi;G1Se9S1cS1cS4Lb1;La;M9Lop0;MaGaSeaG9Lop0;MbGbS0S15S1cS4La;Lw;Lsgn;McS14S1cS13S4Lk0;Li;Ll;MdX1cx8Llo;G1GaGaGbGbGcGdX1cx8Lk;G1GaGaGbGbGcS14S1cS13S4Lk;Li;Ll;MeX1cx8S4S4S4S4S4S4S4S4S4Xe9xaLb0;Lb;Lop;Se9S1cS1cS4Lb;La;MfLop;SeaGfLop;M10G10GcGeX1cx8").
Definition robj_stackN (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|b|
S1cS0Lx;M0S33Vo;A1S13G0S32Vo;A1S13S0S0L_;M1S6aS6fS6bZ2M2Z28A2A1R2A2G1S6aR2R1A2G1S6aR1Z0M3A2G1S10dVfacts;Sf7S6fR2A1S26Vo;A1M4A4S10dVfacts;G4G3S21S6bG2Z2fA2A1A4S4X0x2S4X0x2S4X0x2S4X0x2Lhi;S14S4Li;M5Se9S1cS1cS4Lb;La;M6Lop;M7G7SeaG6Lop;M8G8S0S15S1cS4La;Lw;Lsgn;M9S14S1cS13S4Lk;Li;Ll;MaX1cx8Llo;G5G7G7G8G8G9GaX1cx8").

Lemma robj_ownframe_off_sound : ltac2:(tb__ "0|6|
S1S2S2S1cS13A2M0S1cA2M1A1S1eS1dS13S16S0Sd6R4R3A2S3A3S17S67S9S13S13S29R3R4A2M2A3R2A2S69R2SaS13S13G2A3A2A2S1aG1G1S17SacG1R1R7A3S17S17S67Z0SaS1cS13S9G0S1cR1A3A3M3A2S67G3Z6A2A2S18S17S67S9S13S13S65R5R1A2M4A3M5R4A2S69R4S68G5SaS13S13G4A3A2A2A2S67S6dS6bZ2Z40A2Z1000A2G5A2A2A2A2Lx;A2F_;F_;Fa;Frho;Fo;Ffr;").
Proof using .
  intros fr o rho a H Hr. unfold robj_ownframe_off in H.
  destruct (ob_base o) as [v|z|op b1 b2| | | | |] eqn:Eb; try discriminate. destruct op; try discriminate. destruct b2 as [k| | | | | | |]; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
  apply lazy_andb_prop in H as [Hk H]. apply Z.leb_le in Hk.
  apply existsb_exists in H as (x & Hx & Hc).
  apply lazy_andb_prop in Hc as [Hb Hc]. apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 Hc].
  apply lazy_andb_prop in Hc as [H3 Hc]. apply lazy_andb_prop in Hc as [H6 Hc]. apply lazy_andb_prop in Hc as [H4 H5].
  apply sv_eqb_sound in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
  exists x. split; [exact Hx|]. split; [lia|]. subst b1.
  pose proof (fs_frame_size_bounds' (snd (fst x)) ltac:(lia)) as Bsz.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia.
  unfold frv. cbn [fst snd]. unfold uval. set (f := bv_unsigned (eval rho (fst (fst x)))) in *.
  pose proof (bv_urange (eval rho (fst (fst x)))) as Rf. change (bv_modulus 64) with (2 ^ 64) in Rf. fold f in Rf.
  rewrite U_add in Hr. fold f in Hr. rewrite U_lit in Hr. unfold M64v in Hr. rewrite (Z.mod_small k) in Hr by lia.
  destruct (Z_lt_dec (f + k) (2 ^ 64)) as [L|L].
  - left. rewrite Z.mod_small in Hr by lia. lia.
  - right. lia.
Qed.

Lemma robj_stackN_sound : ltac2:(tb__ "0|1|
S1S1fA1S1dS13S1eS13SaaS1fS22R4A1R5A3Sf3R5R4A2S16S0Sd7R7R4A2S3A3S17S67S9S13S13S29R7R5A2M0A3R4A2S69R4SaS13S13G0A3A2A2S17S67R7R5A2S69R5S6bZ2Z2fA2A2A2F_;F_;F_;F_;Fa;Fo;FT;Frho;Ffacts;").
Proof using .
  intros facts rho T o a HF [HT HT2] H Hr. unfold robj_stackN in H.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H5].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (uleq_sound rho facts _ _ _ HF H4) as U4. pose proof (uleq_sound rho facts _ 0 _ HF H5) as U5.
  unfold U in U4, U5. unfold svT in U4. cbn [eval] in U4. rewrite HT in U4. rewrite U_lit in U5. unfold M64v in U5.
  change ((2 ^ 47) mod 18446744073709551616) with (2 ^ 47) in U5.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite El, Eh in Hr. cbn [fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Definition carve_objs_chk (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (extra : sobj -> bool) (objs : list sobj) : bool := ltac2:(tb__ "0|2|
SaeS1eS1eS0S0L_;M0Vextra;R1A1S3G0S124R1A1S3G0Sf6Vtv;SfS5A1M1R1A3S3G0S125Vfr;U0G1R1A4S3G0Sd6Vfr;R1A2S3G0Sd7Vfacts;R1A2S3S116Vfacts;R1A2X0x2X0x2X0x2X0x2X0x2X0x2Lo;Vobjs;A3").

Definition xr_lit47 (r : sv * sv) : bool := ltac2:(tb__ "0|b|
S2S1cS1cA2S0Lr;Vr;S1cS1cS1cS0Ls;R2S13S1cS0Ls0;R2S13S0S0L_;M0S6aZ0M1R2A2G0S6aG1R1A2S6aS68R2R1A2S6bZ2Z2fA2A2S4X0x2S4X0x2Ll;S14S4Li;M2Se9S1cS1cS4Lb0;La;M3Lop;M4G4SeaG3Lop;M5G5S0S15S1cS4La;Lw;Lsgn;M6S14S1cS13S4Lk;Li;Ll;M7X1cx8Lb;G2Se9S1cS1cS4Lb;La;M8Lop;M9G9SeaG8Lop;MaGaG6G7X1cx8Ls0;Ls;X2x1").
Definition xrs47_chk (facts : list sprop) (tv : list (sv * sv)) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|6|
SaeS2S1cS1cA2M0G0S0S0L_;M1SddR1A1S3G1S117Vtv;SfS5A1R1A3S3G1S10bVfacts;S34S45SebS9S1cS1cR1A3M2SaS1cS1cR1A3M3A3S21S6bZ2M4Z2fA2A1M5A2A2G1S10bVfacts;S34G3S21S6bG4Z28A2A1A2A2S10bVfacts;S34G2G5A2A2S4X0x2S4X0x2X0x2X0x2Lr;VX;A3").

Lemma xrs47_chk_sound : ltac2:(tb__ "0|1|
SdeS1dS1S1fA1S1S2S1cS1cA2A1M0G0S1dS1S72Q40A1A1Sc0VAInv;R8R3R2R1A4SaaS1fS22R8A1R7A3S58VFB;RaR9R7A4SeeRaR8A2S16S0Sd8RaR9R8A3S3A3S11cRcR9A2F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv X rho1 tp1 md1 HM HF HN HZ H r a Hr Ha.
  pose proof (proj1 (forallb_forall _ _) H r Hr) as Hc. cbv beta in Hc.
  pose proof (uval_range rho (fst r)) as R1. pose proof (uval_range rho (snd r)) as R2.
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { unfold xr_lit47 in Hc. destruct r as [rb rl]. destruct rb as [b| | | | | | |]; try discriminate. destruct rl as [l| | | | | | |]; try discriminate.
    apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H3 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [fst snd] in Ha. unfold uval in Ha. cbn [eval] in Ha. rewrite (u64_lit b), (u64_lit l) in Ha by lia. lia. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { unfold xr_tracked in Hc. destruct (robj_tracked_sound tv None _ Hc) as (j & t & Hj & _ & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
    pose proof (nth_error_In _ _ Hj) as Hin.
    assert (Er : tvv rho t = (uval rho (fst r), uval rho (snd r))) by (unfold tvv, uval; rewrite Hb, Hh; reflexivity).
    destruct (Z.eq_dec (uval rho (fst r)) 0) as [Hz0|Hnz0].
    { exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
      unfold tnz in Z0. rewrite <- Hb in Z0. unfold uval in *. specialize (Z0 ltac:(lia)). lia. }
    assert (Hnz : tnz rho t) by (unfold tnz; rewrite <- Hb; unfold uval in Hnz0; exact Hnz0).
    destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (_ & Hlive & _). rewrite Er in Hlive.
    destruct (law_blocks' segs AInv CST ALA HCST Ai rho1 tp1 md1 HM) as (_ & HBl & _). destruct (HBl _ _ Hlive) as (_ & _ & G3 & G4 & (_ & _ & _ & G8)). lia. }
  apply lazy_andb_prop in Hc as [P1 P2]. apply lazy_andb_prop in P2 as [P2 P3].
  pose proof (prove_sprop_sound rho _ _ HF P1) as Q1. pose proof (prove_sprop_sound rho _ _ HF P2) as Q2. pose proof (prove_sprop_sound rho _ _ HF P3) as Q3.
  cbn [holds] in Q1, Q2, Q3. rewrite U_add, !U_lit in Q1. rewrite U_lit in Q2. rewrite U_lit in Q3. unfold M64v in Q1, Q2, Q3.
  change (2 ^ 40 mod 18446744073709551616) with (2 ^ 40) in Q2. change (2 ^ 47 mod 18446744073709551616) with (2 ^ 47) in Q1, Q3.
  unfold uval in *. rewrite Z.mod_small in Q1 by lia. lia.
Qed.

Lemma tvinA_sublist : ltac2:(tb__ "0|2|
SdeS1dS1S2S1cS1cA2M0A1M1G1G0SacG0R1R2A3SacG0R2R4A3F_;Ft;S58VFB;R5R4R3A4S58VFB;R6R5R3A4F_;F_;Ftv';Ftv;Frho;FAi;").
Proof using . intros Ai rho tv tv' Hs HN. unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). exact (Hs t Ht). Qed.
Lemma tvz_sublist : ltac2:(tb__ "0|2|
S1dS1S2S1cS1cA2M0A1M1G1G0SacG0R1R2A3SacG0R2R4A3F_;Ft;SeeR4R3A2SeeR5R3A2F_;F_;Ftv';Ftv;Frho;").
Proof using . intros rho tv tv' Hs HZ. unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). exact (Hs t Ht). Qed.

Lemma carve_objs_chk_sound : ltac2:(tb__ "0|6|
SdeS1dS1S1fA1S1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S5S1eS0F_;S1S1eA1S1S72Q40A1A1Sc0VAInv;RaR9R2R1A4SaaS1fS22RaA1R9A3S5cVrho0;RcA2Sf3RcSf5Vrho0;A1A2S58VFB;ReRdRbA4Sf2ReRcA2SeeRfRdA2S5dVFF;R11R10RdA4S16S0Sd1R10SefG0RdRfA3ReRcRbA5S3A3S1eS13SacS1eR2ReA3S16S0R10R3A1S3A3S17S67S9S13S13S29R16R4A2M1A3R3A2S69R3SaS13S13G1A3A2A2S18S109VCST;Vrho0;Sf0VFB;R17SefG0R13R15A3A3M2S10aVFF;R17R14A3M3R4A5S18S17S67Z0M4R4A2S69R4Se5A2A2S115R4A1A2A2F_;F_;F_;Fa;Fo;S1eS13SacS1eR2RfA3S17S67S9S13S13S29R16R3A2M5A3R2A2S69R2SaS13S13G5A3A2A2S18S109VCST;Vrho0;G2G3R3A5S18S17S67G4R3A2S69R3Se5A2A2S115R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Fobjs;Fextra;Fj;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr j extra objs tp1 md1 HM HF HT HT0 HN HD HZ HFR Hchk Hextra o a Ho Hr.
  unfold carve_objs_chk in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbv beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (Hextra o a Ho Hc Hr)|].
  set (tv' := remove_nth j tv) in *.
  assert (HN' : tvinA FB Ai rho tv') by (apply (tvinA_sublist Ai rho tv tv'); [intros t Ht; eapply remove_nth_In; exact Ht | exact HN]).
  assert (HD' : tvd rho tv') by (apply tvd_remove; exact HD).
  assert (HZ' : tvz rho tv') by (apply (tvz_sublist rho tv tv'); [intros t Ht; eapply remove_nth_In; exact Ht | exact HZ]).
  apply lazy_orb_prop in Hc as [Hc|Hc].
  {   right; left. revert Hc Hr. clear. intros Hc Hr. unfold robj_image in Hc.
    destruct (ob_base o) as [b0| | | | | | |] eqn:Eb; try discriminate. destruct b0; try discriminate.
    destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
    apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [eval fst snd] in Hr. unfold IMG_HI in *.
    rewrite (u64_lit 0), !soff_lit_small in Hr by lia. lia. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  {   destruct (robjs_checkF_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv' fr None (fun _ => false) [o] rho tp1 md1 HM HF HT0 HN' HD' HZ' HFR
             ltac:(rewrite robjs_checkF_ref_eq; unfold robjs_checkF_ref; cbn [forallb]; rewrite Hc; destruct (robj_stackA facts o); reflexivity) ltac:(intros o' a' _ HE _; discriminate HE) o a ltac:(left; reflexivity) Hr)
      as [P|P]; [left; exact P | right; left; exact P]. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  {   destruct (robjs_checkF_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv' fr None (fun _ => false) [o] rho tp1 md1 HM HF HT0 HN' HD' HZ' HFR
             ltac:(rewrite robjs_checkF_ref_eq; unfold robjs_checkF_ref; cbn [forallb]; rewrite Hc; destruct (robj_stackA facts o), (robj_tracked tv' None o); reflexivity)
             ltac:(intros o' a' _ HE _; discriminate HE) o a ltac:(left; reflexivity) Hr)
      as [P|P]; [left; exact P | right; left; exact P]. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  {   left. destruct (robj_ownframe_off_sound fr o rho a Hc Hr) as (x & Hx & Hc6 & Hax).
    destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp1 md1 fr x HM HT HFR Hx) as (X1 & _ & _ & _ & _ & _ & X5 & _).
    destruct Hax as [Hax|Hax]; [|exfalso; unfold frv in X5, Hax; cbn [fst snd] in X5, Hax; pose proof (fs_frame_size_bounds' _ Hc6); lia].
    right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split; [|exact Hax].
    apply In_FFx. right. exists x. split; [exact Hx | reflexivity]. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { left; left. exact (robj_stackN_sound facts rho _ o a HF HT0 Hc Hr). }
  left; left. exact (robj_stackA_sound facts rho _ o a HF HT0 Hc Hr).
Qed.

Definition carve_site_chk (A : axst) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (j : nat) (extra : sobj -> bool) : bool := ltac2:(tb__ "0|2|
S7Sd1S23S4cVA;A1M0A1M1SefS2S1cS1cA2Vj;Vtv;A3Vfr;Vextra;S27G0A1A5Sd8G1Vtv;S4eVA;A1A3A2").

Lemma carve_site_chk_sound : ltac2:(tb__ "0|2|
S4bS1S2S1cS1cA2M0A1S1S2S2S1cS13A2S1cA2A1S5S1eS0F_;S1dS16S0SdaR6R5R4R3R2A5S3A3SdeS1S72Q40A1A1Sc0SaaS1fS22R5A1S23S4cRaA1A1A3VP0f;Vrho0;A1S11dVNP;Vrho0;R7A3VAInv;R6R8R5R4A4S5cVrho0;R7A2Sf3RaSe0SdfR8A1A1A2S60VFB;R9A2S61VFF;RaA2S58VFB;RbRdR11A4Sf2ReR12A2SeeRfR13A2S5dVFF;ReR10R13A4S1eS13SacS1eR2S27S4cR18A1A1A3S16S0R15R3A1S3A3S17S67S9S13S13S29R15R4A2M1A3R3A2S69R3SaS13S13G1A3A2A2S18S109VCST;Vrho0;Sf0VFB;R16SefG0R18R1aA3A3S10aVFF;R16R19A3R4A5S18S17S67Z0R4A2S69R4Se5A2A2S115R4A1A2A2F_;F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;FAi;ScaR8R7R6R5R3A5F_;F_;Frho;Fextra;Fj;Ffr;Ftv;FA;").
Proof using ALA HCST.
  intros A tv fr j extra rho H Hextra Ai tp1 md1 HF HP0 Hav HM HT HTK HB HFF HN HD HZ HFR.
  unfold carve_site_chk in H. apply andb_prop in H as [H1 H2]. split.
  - exact (carve_objs_chk_sound Ai rho _ tv fr j extra _ tp1 md1 HM HF HT (T_ok_T0 rho0 rho Ai HT HTK) HN HD HZ HFR H1
             (Hextra Ai tp1 md1 HF HP0 Hav HM HT HTK HB HFF HN HD HZ HFR)).
  - exact (xrs47_chk_sound Ai rho _ tv _ rho tp1 md1 HM HF HN HZ H2).
Qed.

Fixpoint lform_eqb (f g : lform) : bool :=
  match f, g with
  | [], [] => true
  | (c, a) :: r, (c', a') :: r' => (c =? c') && batom_eqb a a' && lform_eqb r r'
  | _, _ => false
  end.
Lemma lform_eqb_sound : ltac2:(tb__ "0|0|
S8eS8eS16S0Sd4R2R1A2S3A3S16S8eR3R2A3F_;Fg;Ff;").
Proof.
  induction f as [|[c a] r IH]; intros [|[c' a'] r'] H; cbn [lform_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hc Ha]. apply Z.eqb_eq in Hc. apply batom_eqb_sound in Ha. rewrite (IH r' Hr). subst. reflexivity.
Qed.
Definition bitem_eqb (i j : bitem) : bool := ltac2:(tb__ "0|0|
S7S7S7S6cS9bVi;A1S9bVj;A1A2S6cS9aVi;A1S9aVj;A1A2A2Sd4S99Vi;A1S99Vj;A1A2A2S6cS98Vi;A1S98Vj;A1A2A2").
Lemma bitem_eqb_sound : ltac2:(tb__ "0|0|
S8cS8cS16S0Sc7R2R1A2S3A3S16S8cR3R2A3F_;Fj;Fi;").
Proof.
  intros [v k f c] [v' k' f' c'] H. unfold bitem_eqb in H. cbn [bi_v bi_k bi_f bi_c] in H.
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hf]. apply andb_prop in H as [Hv Hk].
  apply Z.eqb_eq in Hv. apply Z.eqb_eq in Hk. apply Z.eqb_eq in Hc. apply lform_eqb_sound in Hf. subst. reflexivity.
Qed.

Definition item_nn2 (facts : list sprop) (bfrom : list bitem) (i : bitem) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0SafS8cSc7Vi;A1Vbfrom;A3S3G0Sa3Vfacts;Vi;A2S3SafS8cS8cSa1Vfacts;R1Vi;A3Lj;Vbfrom;A3X0x2X0x2").

Definition bud_pay2_ref (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S8dVbfrom;A1G0S8dVbto;A1G0SaeS8cSccVfacts;Vbfrom;A2Vbto;A3G0S6aZ0VcostK;A2G0S2S8eS13A2S0Lx;M1S95Vbfrom;A1S8eS13G1S95Vbto;A1S8eS13S9dVfacts;ScS2S13S93A2M2R4ScG2S9cR2A1M3SdG2S8S13S93N1S96VcostV;A1A4SeG2A1A3A3A3S6dR3R1A2M4A3Ltc;Ltf;X2x1Lfc;Lff;X2x1G1S94Vbfrom;A1S8eS13G1S94Vbto;A1S8eS13S9dVfacts;ScG2R4G3A3S6dG4VcostK;A2A3Ltc;Ltf;X2x1Lfc;Lff;X2x1S4X0x2S4X0x2S4X0x2S4X0x2S4X0x2").
Lemma item_nn2_sound : ltac2:(tb__ "0|0|
S1S1fA1S1S8cA1S8cS1dSaaS1fS22R1A1R4A3S8fR4R2A2S16S0SccR6R5R4A3S3A3S67Z0S9fR4R5A2A2F_;F_;F_;Frho;Fi;Fbfrom;Ffacts;").
Proof using .
  intros facts bfrom i rho HF Hn H. unfold item_nn2 in H. apply lazy_orb_prop in H as [H|H].
  - apply existsb_exists in H as (j & Hj & He). apply bitem_eqb_sound in He. subst j. exact (proj1 (Forall_forall _ _) Hn i Hj).
  - apply lazy_orb_prop in H as [H|H]; [eapply item_nonneg_sound; eauto|].
    apply existsb_exists in H as (j & Hj & Hle). pose proof (item_le_sound facts j i rho HF Hle).
    assert (X : 0 <= bival rho j) by exact (proj1 (Forall_forall _ _) Hn j Hj). lia.
Qed.
Lemma bud_pay2_ref_sound : ltac2:(tb__ "0|4|
S1S1fA1S1cS13S1S8cA1M0G0S1dSaaS1fS22R1A1R6A3S8fR4R2A2S16S0Sc6R8R7R6R5R4A5S3A3S17S67S68S8bR4R8A2S91R5R4A2M1A2S91R6R4A2A2S17S67S68R7S90R5R4A2M2A2S90R6R4A2A2S17S67Z0M3G1A2S17S67G3G2A2S17S67G3R7A2S17S8fR5R4A2S17S16S0S8dR5A1S3A3S16S0S8dR6A1S3A3A2A2A2A2A2A2A2F_;F_;F_;Frho;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using .
  intros facts costV costK bfrom bto rho HF Hnf H. unfold bud_pay2_ref in H.
  apply lazy_andb_prop in H as [Hw1 H]. apply lazy_andb_prop in H as [Hw2 H]. apply lazy_andb_prop in H as [Hnn H]. apply lazy_andb_prop in H as [Hc H].
  apply lazy_andb_prop in H as [HV HK]. apply Z.leb_le in Hc.
  assert (NN : bd_nn bto rho).
  { unfold bd_nn. apply Forall_forall. intros it Hit. eapply item_nn2_sound; [exact HF|exact Hnf|]. exact (proj1 (forallb_forall _ _) Hnn it Hit). }
  pose proof (bsum_nonneg bto rho Hw2 NN) as [N1 N2].
  destruct (wformV bfrom) as [ff fc] eqn:E1. destruct (wformV bto) as [tf tc] eqn:E2.
  destruct (wformK bfrom) as [ffk fck] eqn:E3. destruct (wformK bto) as [tfk tck] eqn:E4.
  pose proof (lf_nonneg_sound facts _ _ rho HF HV) as XV. pose proof (lf_nonneg_sound facts _ _ rho HF HK) as XK.
  rewrite !lfval_app in XV. rewrite !lfval_app in XK. rewrite lfval_neg in XV. rewrite lfval_neg in XK. cbn [lfval aval] in XV.
  pose proof (wformV_val bfrom rho) as W1. rewrite E1 in W1. pose proof (wformV_val bto rho) as W2. rewrite E2 in W2.
  pose proof (wformK_val bfrom rho) as W3. rewrite E3 in W3. pose proof (wformK_val bto rho) as W4. rewrite E4 in W4.
  cbn [fst snd] in W1, W2, W3, W4. repeat (split; [lia|]). split; [exact NN|]. auto.
Qed.

Fixpoint bud_le_pos2 (facts : list sprop) (ball bto bfrom : list bitem) : bool :=
  match bto, bfrom with
  | [], _ => bd_wpos bfrom
  | i :: r, j :: r' =>
      ((bitem_eqb i j &&& ((0 <=? bi_v i) &&& (0 <=? bi_k i)))
       ||| ((0 <=? bi_v i) &&& ((bi_v i <=? bi_v j) &&& ((0 <=? bi_k i) &&& ((bi_k i <=? bi_k j) &&& (item_le facts i j &&& item_nn2 facts ball i))))))
      &&& bud_le_pos2 facts ball r r'
  | _ :: _, [] => false
  end.

Lemma bud_le_pos2_sound : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0G0S1dSaaS1fS22R1A1R5A3S8fR5R2A2S8fR4R3A2S16S0Sc8R8R7R6R5A4S3A3S17S67S91R7R5A2S91R6R5A2A2S17S67S90R7R5A2S90R6R5A2A2S17S8fR7R5A2S17S16S0S8dR7A1S3A3S16S0S8dR6A1S3A3A2A2A2A2F_;F_;F_;F_;Frho;Fbfrom;Fbto;Fball;Ffacts;").
Proof using .
  intros facts ball bto. induction bto as [|i r IH]; intros [|j r'] rho HF Hall Hn H; cbn [bud_le_pos2] in H; try discriminate.
  - cbn. split; [lia|]. split; [lia|]. split; [constructor|]. split; [reflexivity|]. exact H.
  - pose proof (bsum_nonneg (j :: r') rho H Hn) as [A B]. cbn [bsumV bsumK] in A, B |- *. split; [lia|]. split; [lia|]. split; [constructor|]. split; [reflexivity|]. exact H.
  - apply lazy_andb_prop in H as [H Hr]. inversion Hn as [|j0 r0 Hj Hr' E1]; subst.
    destruct (IH r' rho HF Hall Hr' Hr) as (IH1 & IH2 & IH3 & IH4 & IH5). cbn [bsumV bsumK].
    assert (CORE : 0 <= bi_v i <= bi_v j /\ 0 <= bi_k i <= bi_k j /\ 0 <= bival rho i /\ bival rho i <= bival rho j).
    { apply lazy_orb_prop in H as [H|H].
      - apply lazy_andb_prop in H as [He H]. apply lazy_andb_prop in H as [Hv1 Hk1]. apply bitem_eqb_sound in He. subst j.
        apply Z.leb_le in Hv1. apply Z.leb_le in Hk1. lia.
      - apply lazy_andb_prop in H as [Hv1 H]. apply lazy_andb_prop in H as [Hv2 H]. apply lazy_andb_prop in H as [Hk1 H]. apply lazy_andb_prop in H as [Hk2 H].
        apply lazy_andb_prop in H as [Hle Hnn].
        apply Z.leb_le in Hv1. apply Z.leb_le in Hv2. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
        pose proof (item_le_sound facts i j rho HF Hle) as L.
        pose proof (item_nn2_sound facts ball i rho HF Hall Hnn) as N. lia. }
    destruct CORE as (Cv & Ck & N & L).
    split; [nia|]. split; [nia|]. split; [constructor; assumption|].
    unfold bd_wpos. cbn. rewrite (proj2 (Z.leb_le _ _) (proj1 Cv)), (proj2 (Z.leb_le _ _) (proj1 Ck)).
    assert (Jv : 0 <= bi_v j) by lia. assert (Jk : 0 <= bi_k j) by lia.
    rewrite (proj2 (Z.leb_le _ _) Jv), (proj2 (Z.leb_le _ _) Jk). cbn.
    unfold bd_wpos in IH4, IH5. auto.
Qed.

Definition bud_le2_ref (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
S0S0L_;Sc8Vfacts;Vbfrom;Vbto;Vbfrom;A4S3Sc6Vfacts;S21Z0M0A1G0Vbfrom;Vbto;A5X0x2").

Lemma bud_le2_ref_sound : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0S1dSaaS1fS22R1A1R4A3S8fR3R2A2S16S0ScfR6R5R4A3S3A3S17S67S91R6R4A2S91R5R4A2A2S17S67S90R6R4A2S90R5R4A2A2S17S8fR6R4A2S17S16S0S8dR6A1S3A3S16S0S8dR5A1S3A3A2A2A2A2F_;F_;F_;Frho;Fbfrom;Fbto;Ffacts;").
Proof using .
  intros facts bto bfrom rho HF Hn H. unfold bud_le2_ref in H. apply lazy_orb_prop in H as [H|H].
  - exact (bud_le_pos2_sound facts bfrom bto bfrom rho HF Hn Hn H).
  - destruct (bud_pay2_ref_sound facts (SLit 0) 0 bfrom bto rho HF Hn H) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    pose proof (uval_range rho (SLit 0)). repeat (split; [lia|]). auto.
Qed.

Definition item_nn2_p (pf : pfacts) (facts : list sprop) (bfrom : list bitem) (i : bitem) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0SafS8cSc7Vi;A1Vbfrom;A3S3G0Sa4Vpf;Vfacts;Vi;A3S3SafS8cS8cSa2Vpf;Vfacts;R1Vi;A4Lj;Vbfrom;A3X0x2X0x2").
Definition bud_pay2_p (pf : pfacts) (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S8dVbfrom;A1G0S8dVbto;A1G0SaeS8cSd3Vpf;Vfacts;Vbfrom;A3Vbto;A3G0S6aZ0VcostK;A2G0S2S8eS13A2S0Lx;M1S95Vbfrom;A1S8eS13G1S95Vbto;A1S8eS13S9eVpf;Vfacts;ScS2S13S93A2M2R4ScG2S9cR2A1M3SdG2S8S13S93N1S96VcostV;A1A4SeG2A1A3A3A3S6dR3R1A2M4A4Ltc;Ltf;X2x1Lfc;Lff;X2x1G1S94Vbfrom;A1S8eS13G1S94Vbto;A1S8eS13S9eVpf;Vfacts;ScG2R4G3A3S6dG4VcostK;A2A4Ltc;Ltf;X2x1Lfc;Lff;X2x1S4X0x2S4X0x2S4X0x2S4X0x2S4X0x2").
Fixpoint bud_le_pos2_p (pf : pfacts) (facts : list sprop) (ball bto bfrom : list bitem) : bool :=
  match bto, bfrom with
  | [], _ => bd_wpos bfrom
  | i :: r, j :: r' =>
      ((bitem_eqb i j &&& ((0 <=? bi_v i) &&& (0 <=? bi_k i)))
       ||| ((0 <=? bi_v i) &&& ((bi_v i <=? bi_v j) &&& ((0 <=? bi_k i) &&& ((bi_k i <=? bi_k j) &&& (item_le_p pf facts i j &&& item_nn2_p pf facts ball i))))))
      &&& bud_le_pos2_p pf facts ball r r'
  | _ :: _, [] => false
  end.
Lemma item_nn2_p_eq : ltac2:(tb__ "0|0|
S1S1fA1S1S8cA1S8cS16S0Sd3SfaR3A1R3R2R1A4SccR3R2R1A3A3Fi;Fbfrom;Ffacts;").
Proof using .
  intros facts bfrom i. unfold item_nn2_p, item_nn2. rewrite item_nonneg_p_eq.
  replace (existsb (fun j => item_le_p (mk_pf facts) facts j i) bfrom) with (existsb (fun j => item_le facts j i) bfrom); [reflexivity|].
  induction bfrom as [|b r IH]; [reflexivity|]. cbn [existsb]. rewrite item_le_p_eq, IH. reflexivity.
Qed.
Lemma bud_pay2_p_eq : ltac2:(tb__ "0|1|
S1S1fA1S1cS13S1S8cA1M0G0S16S0Sc5SfaR5A1R5R4R3R2R1A6Sc6R5R4R3R2R1A5A3Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using .
  intros. unfold bud_pay2_p, bud_pay2_ref.
  replace (forallb (item_nn2_p (mk_pf facts) facts bfrom) bto) with (forallb (item_nn2 facts bfrom) bto)
    by (induction bto as [|b r IH]; [reflexivity | cbn [forallb]; rewrite item_nn2_p_eq, IH; reflexivity]).
  destruct (wformV bfrom) as [ff fc]; destruct (wformV bto) as [tf tc]; destruct (wformK bfrom) as [ffk fck]; destruct (wformK bto) as [tfk tck].
  rewrite !lf_nonneg_p_eq. reflexivity.
Qed.

Definition bud_pay2 (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : bool := ltac2:(tb__ "0|0|
Sc5SfcVfacts;A1Vfacts;VcostV;VcostK;Vbfrom;Vbto;A6").
Lemma bud_pay2_ref_eq : ltac2:(tb__ "0|1|
S1S1fA1S1cS13S1S8cA1M0G0S16S0Sd0R5R4R3R2R1A5Sc6R5R4R3R2R1A5A3Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using . intros. unfold bud_pay2. rewrite DigFastA.mk_pf_f_eq. apply bud_pay2_p_eq. Qed.
Lemma bud_pay2_sound : ltac2:(tb__ "0|4|
S1S1fA1S1cS13S1S8cA1M0G0S1dSaaS1fS22R1A1R6A3S8fR4R2A2S16S0Sd0R8R7R6R5R4A5S3A3S17S67S68S8bR4R8A2S91R5R4A2M1A2S91R6R4A2A2S17S67S68R7S90R5R4A2M2A2S90R6R4A2A2S17S67Z0M3G1A2S17S67G3G2A2S17S67G3R7A2S17S8fR5R4A2S17S16S0S8dR5A1S3A3S16S0S8dR6A1S3A3A2A2A2A2A2A2A2F_;F_;F_;Frho;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using .
  intros facts costV costK bfrom bto rho HF Hnf H. rewrite bud_pay2_ref_eq in H. exact (bud_pay2_ref_sound facts costV costK bfrom bto rho HF Hnf H).
Qed.
Lemma bud_le_pos2_p_eq : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0G0S16S0Sc9SfaR4A1R4R3R2R1A5Sc8R4R3R2R1A4A3Fbfrom;Fbto;Fball;Ffacts;").
Proof using .
  intros facts ball bto. induction bto as [|i r IH]; intros [|j r']; cbn [bud_le_pos2_p bud_le_pos2]; try reflexivity.
  rewrite item_le_p_eq, item_nn2_p_eq, IH. reflexivity.
Qed.
Definition bud_le2 (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
SfcVfacts;A1Sf9S0S0L_;Sc9R1Vfacts;Vbfrom;Vbto;Vbfrom;A5S3Sc5R1Vfacts;S21Z0M0A1G0Vbfrom;Vbto;A6X0x2Tpf;").
Lemma bud_le2_ref_eq : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0S16S0Sc4R3R2R1A3ScfR3R2R1A3A3Fbfrom;Fbto;Ffacts;").
Proof using . intros. unfold bud_le2, bud_le2_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq, bud_le_pos2_p_eq, bud_pay2_p_eq. reflexivity. Qed.
Lemma bud_le2_sound : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0S1dSaaS1fS22R1A1R4A3S8fR3R2A2S16S0Sc4R6R5R4A3S3A3S17S67S91R6R4A2S91R5R4A2A2S17S67S90R6R4A2S90R5R4A2A2S17S8fR6R4A2S17S16S0S8dR6A1S3A3S16S0S8dR5A1S3A3A2A2A2A2F_;F_;F_;Frho;Fbfrom;Fbto;Ffacts;").
Proof using .
  intros facts bto bfrom rho HF Hn H. rewrite bud_le2_ref_eq in H. exact (bud_le2_ref_sound facts bto bfrom rho HF Hn H).
Qed.

Lemma BUD_transfer2 : ltac2:(tb__ "0|1|
S1S1fA1S104S1S8cA1M0G0S2S13S13A2S13S13S13S1dSaaS1fS22R1A1R9A3S16S0Sc4RaS92R9R8A2R7A3S3A3S97R8R7R6R5R4R3A6S97RaR8R7R6R5S103R4RbA2A6F_;F_;F_;Frho;FKf;FKm;FV;FBXv;Fbfrom;Fbto;Fs;Ffacts;").
Proof using .
  intros facts s bto bfrom BXv V Km Kf rho HF Hle H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  destruct (bud_le2_sound facts _ _ rho HF Hn Hle) as (L1 & L2 & L3 & L4 & L5). rewrite bsumV_subst in L1. rewrite bsumK_subst in L2.
  rewrite bd_wpos_subst in L4. apply bd_nn_subst in L3.
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.

Lemma JAi_transfer2 : ltac2:(tb__ "0|0|
S104S14S1S1fA1S51S51SdeS13S1dS1dS1S72Q40A1A1S1Sc1A1Sc0S16S0S105RcVNP;A2S3A3SffVNP;RcA2S16S0S52RdRbA2S3A3S16S0Sf1RfS56RcA1S56RbA1A3S3A3S16S0S5bR10S55RdA1S55RcA1A3S3A3S16S0Sc4RfS92R11S54RdA1A2S54ReA1A3S3A3S16S59S5aR12S53ReA1A2S53RfA1A3S2dR12RcRbA3SaaS1fS22RcA1R12A3VJAi;R12R10RfReRcRbRaA7VJAi;R12R11R10S103ReR16A2RdRcRbA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fndj;Fndi;Ffacts;Fn;Fs;").
Proof using ALA.
  intros s n facts ndi ndj Ai kc rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HF HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  pose proof (rho_sub_agree s NP rho' H1) as Hids.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [|split; [exact Hk|split; [|split; [exact HT|split; [exact HB|split; [exact HFF|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [|split; [|exact (conj HPA (conj HCKi (capN_map BX Ai rho' (rho_sub rho' s) _ _ M1 (capN_agree n BX Ai rho rho' _ Hav' Hbt HCNi))))]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact H2|exact Hav']|].
    apply agree_below_vals. exact Hids.
  - eapply (law_vars _ _ _ ALA); [exact HM|]. apply functional_extensionality. exact Hrm.
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - eapply fr_sub_eqb_sound; [exact H6|]. eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR].
  - eapply keptFA_eq_r; [exact HK | exact Hrm].
  - eapply XA_subst; [exact M1 |]. rewrite Ham. eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA].
  - rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer2; [exact HF | exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
Qed.

Lemma JA_transfer2 : ltac2:(tb__ "0|0|
S104S14S1S1fA1S51S51S1dS1dS1S72Q40A1A1S1Sc1A1Sc0S16S0S105RaVNP;A2S3A3SffVNP;RaA2S16S0S52RbR9A2S3A3S16S0Sf1RdS56RaA1S56R9A1A3S3A3S16S0S5bReS55RbA1S55RaA1A3S3A3S16S0Sc4RdS92RfS54RbA1A2S54RcA1A3S3A3S16S59S5aR10S53RcA1A2S53RdA1A3S2dR10RcRbA3SaaS1fS22RcA1R10A3VJA;R10ReRcRbRaA5VJA;R10S103ReR14A2RdRcRbA5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fndj;Fndi;Ffacts;Fn;Fs;").
Proof using ALA.
  intros s n facts ndi ndj rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HF (Ai & kc & HJ). exists Ai, kc. eapply JAi_transfer2; eauto.
Qed.

Lemma SPA_entails_JA2 : ltac2:(tb__ "0|1|
S4bS4bS104S51S51S1dS1S72Q40A1A1Sb0S16S0S50R8R7R6A3S3A3S16S0S105R7VNP;A2S3A3S16S0SfdVNP;S20S4cRaA1A1A2S3A3S16S0S52S20S4cRbA1A1R8A2S3A3S16S0Sf1RaS56R9A1S56R8A1A3S3A3S16S0S5bRbS55RaA1S55R9A1A3S3A3S16S0Sc4S23S4cReA1A1S92RcS54RaA1A2S54RbA1A3S3A3S16S0S5fS5aRdS53RbA1A2S53RcA1A2S3A3Sa5Vsegs;VJA;RdA1M0R10RbRaR9A6Sa5Vsegs;G0R10S103RcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;").
Proof using ALA HKc.
  intros L T s ndi ndj rho tp w He Hid Hnp Hnb Htv Hfr Hbd Ham [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ |- *.
  eapply (JA_transfer2 s (ss_next (ax_S L)) (ss_facts (ax_S L)));
    [exact Hid | exact Hnp | exact Hnb | exact Htv | exact Hfr | exact Hbd | exact Ham | apply agree_below_refl | | exact HJ].
  exact (smatchA_facts segs _ _ _ _ Hsm).
Qed.

Definition echeckJA2 (nodes : list (axst * ndesc)) (e : edgeA) : bool := ltac2:(tb__ "0|4|
S6S2S4bS51A2M0A1S0Lx;M1SadG0Vnodes;Sb6Ve;A1A3G0G0S0Lp;R1S4bS51G1SadG0Vnodes;Sb8Ve;A1A3G0G0S0Lp0;R1S4bS51S7S7S7S7S7S7S105Sb7Ve;A1M2VNP;A2SfdVNP;S20S4cR5A1A1M3A2A2S52G3R4A2A2Sf1G2S56R4A1S56R1A1A3A2S5bG2S55R4A1S55R1A1A3A2Sc4S23S4cSb5Ve;A1A1A1S92G2S54R1A1A2S54R4A1A3A2S5fS5aG2S53R1A1A2S53R4A1A2A2Lndj;LTj;X2x1Lp0;S4X6x2Lndi;LTi;X2x1Lp;S4X6x2").

Definition bud_le2_pf (pf : pfacts) (facts : list sprop) (bto bfrom : list bitem) : bool := ltac2:(tb__ "0|1|
S0S0L_;Sc9Vpf;Vfacts;Vbfrom;Vbto;Vbfrom;A5S3Sc5Vpf;Vfacts;S21Z0M0A1G0Vbfrom;Vbto;A6X0x2").
Lemma bud_le2_pf_eq : ltac2:(tb__ "0|1|
S1S1fA1S1S8cA1M0G0S16S0SceSfcR3A1R3R2R1A4Sc4R3R2R1A3A3Fbfrom;Fbto;Ffacts;").
Proof using . intros. reflexivity. Qed.
Definition echeckJA2_pf (pf : pfacts) (nodes : list (axst * ndesc)) (e : edgeA) : bool := ltac2:(tb__ "0|4|
S6S2S4bS51A2M0A1S0Lx;M1SadG0Vnodes;Sb6Ve;A1A3G0G0S0Lp;R1S4bS51G1SadG0Vnodes;Sb8Ve;A1A3G0G0S0Lp0;R1S4bS51S7S7S7S7S7S7S105Sb7Ve;A1M2VNP;A2SfdVNP;S20S4cR5A1A1M3A2A2S52G3R4A2A2Sf1G2S56R4A1S56R1A1A3A2S5bG2S55R4A1S55R1A1A3A2SceVpf;S23S4cSb5Ve;A1A1A1S92G2S54R1A1A2S54R4A1A4A2S5fS5aG2S53R1A1A2S53R4A1A2A2Lndj;LTj;X2x1Lp0;S4X6x2Lndi;LTi;X2x1Lp;S4X6x2").
Lemma echeckJA2_pf_eq : ltac2:(tb__ "0|0|
S1S2S4bS51A2A1Sb4S16S0Sd2SfcS23S4cSb5R1A1A1A1A1R2R1A3ScbR2R1A2A3Fe;Fnodes;").
Proof using . intros. reflexivity. Qed.

Lemma echeckJA2_sound : ltac2:(tb__ "0|1|
S1S2S4bS51A2M0A1Sb4S16S0ScbR2R1A2S3A3SbbSa9G0Sb9S66VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;AbR3A4R2A2F_;Fe;Fnodes;").
Proof using ALA.
  intros nodes e H Ti Tj Hi Hj rho rho' tp tr md Hag HJ HF.
  unfold echeckJA2 in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [[Si ndi]|]; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [[Sj ndj]|]; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-. cbn [nodeIA fst snd] in *.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H2. apply am_eqb_sound in H8.
  eapply JA_transfer2; eauto.
Qed.

Definition phi_reads (V : list positive) (Phi : valuation -> Prop) : Prop := ltac2:(tb__ "0|3|
S1dS1dS14SacS14R1VV;A3S16S72Q40A1M0S3cR4R2A2S3cR3R2A2A3F_;Fv;S14S16S1S72Q8A1M1A1S3bR4R1A2S3bR3R1A2A3Fl;G0S16S6G1A1S24R5R1A2S24R4R1A2A3Fa;VPhi;R5A1M2G2F_;F_;F_;F_;Frho';Frho;").
Definition V_below (n : positive) (V : list positive) : bool := ltac2:(tb__ "0|0|
SaeS14S14S100R1Vn;A2Lv;VV;A3").
Definition wsub_id_on (V : list positive) (s : wsub) : bool := ltac2:(tb__ "0|0|
SaeS14S14S42S108Vs;R1A2S25R1A1A2Lv;VV;A3").

Definition JAF (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1dS1S72Q40A1A1S1Sc1A1Sc0S17VJA;Vnd;R4R3R2R1A5VPhi;R4A1A2Lmd;Ltr;Ltp;Lrho;").

Section Phi.
Variable V : list positive.
Variable Phi : valuation -> Prop.
Hypothesis HPhi : phi_reads V Phi.

Lemma phi_agree : ltac2:(tb__ "0|1|
S14S1dS1dS16S0Sc3R3VV;A2S3A3S2dR4R3R2A3VPhi;R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using HPhi.
  intros n rho rho' HV (A & B & C) H. eapply HPhi; [| exact B | exact C | exact H].
  intros v Hv. apply A. pose proof (proj1 (forallb_forall _ _) HV v Hv) as X. apply Pos.ltb_lt in X. exact X.
Qed.

Lemma phi_sub : ltac2:(tb__ "0|0|
S104S1dS16S0ScdVV;R2A2S3A3VPhi;R2A1VPhi;S103R3R4A2A1F_;F_;Frho;Fs;").
Proof using HPhi.
  intros s rho Hs H. eapply HPhi; [| | | exact H]; [|reflexivity|reflexivity].
  intros v Hv. pose proof (proj1 (forallb_forall _ _) Hs v Hv) as X. apply sv_eqb_sound in X. cbn [rho_sub rw]. rewrite X. reflexivity.
Qed.

Lemma stableA_JAF : ltac2:(tb__ "0|0|
S14S51SffVNP;R2A2S16S0S52R3R2A2S3A3S16S0Sc3R4VV;A2S3A3Sa7Vsegs;R5Sc2VPhi;R4A2A3F_;F_;F_;Fnd;Fn;").
Proof using ALA HKc HPhi.
  intros n nd Hn Hb HV rho rho' tp tr md md' Hag Hme [HJ HP]. split.
  - exact (stableA_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n nd Hn Hb rho rho' tp tr md md' Hag Hme HJ).
  - exact (phi_agree n rho rho' HV Hag HP).
Qed.

Lemma ok_frameA_JAF : ltac2:(tb__ "0|0|
Sb0OF_;S51S63Vsegs;VKc;R2A3Sa8Vsegs;R3Sc2VPhi;R2A2A3F_;Fnd;Fok;").
Proof using .
  intros ok nd H rho tp tr ms md msv' [HJ _] HMI Hh Hp Hs. exact (ok_frameA_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA ok nd H rho tp tr ms md msv' HJ HMI Hh Hp Hs).
Qed.

Lemma SPA_JAF_intro : ltac2:(tb__ "0|0|
S51S4bS1dS1S72Q40A1A1Sb0Sa5Vsegs;VJA;R5A1R4R3R2R1A6VPhi;R4A1Sa5Vsegs;Sc2VPhi;R7A2R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;").
Proof using . intros nd A rho tp [tr [ms md]] [Hsm HJ] HP. split; [exact Hsm | split; [exact HJ | exact HP]]. Qed.
Lemma SPA_JAF_elim : ltac2:(tb__ "0|0|
S51S4bS1dS1S72Q40A1A1Sb0Sa5Vsegs;Sc2VPhi;R5A2R4R3R2R1A6S17Sa5Vsegs;VJA;R6A1R5R4R3R2A6VPhi;R4A1A2F_;Fw;Ftp;Frho;FA;Fnd;").
Proof using . intros nd A rho tp [tr [ms md]] [Hsm [HJ HP]]. split; [split; [exact Hsm | exact HJ] | exact HP]. Qed.

Lemma triple_JAF : ltac2:(tb__ "0|0|
Sb0OF_;S51S4bS1dS1S72Q40A1A1Sb3VPhi;R3A1Sb2Vsegs;R7Sa5Vsegs;VJA;R6A1R5R4R3A5R2A4F_;Sb2Vsegs;R7Sa5Vsegs;Sc2VPhi;R6A2R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;Fnd;Fok;").
Proof using .
  intros ok nd A rho tp Q H n Hg w Hw. destruct (SPA_JAF_elim nd A rho tp w Hw) as [Hw' HP]. exact (H HP n Hg w Hw').
Qed.
Lemma etriple_JAF : ltac2:(tb__ "0|0|
S51S4bS1dS1S72Q40A1A1Sb0OF_;VPhi;R3A1Sb1Vsegs;Sa5Vsegs;VJA;R6A1R5R4R3A5R2A3F_;Sb1Vsegs;Sa5Vsegs;Sc2VPhi;R6A2R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;Fnd;").
Proof using .
  intros nd A rho tp Q H w Hw. destruct (SPA_JAF_elim nd A rho tp w Hw) as [Hw' HP]. exact (H HP w Hw').
Qed.

Lemma triple_JAF_in : ltac2:(tb__ "0|0|
Sb0OF_;S51S4bS1dS1S72Q40A1A1Sb3VPhi;R3A1Sb2Vsegs;R7Sa5Vsegs;Sc2VPhi;R6A2R5R4R3A5R2A4Sb2Vsegs;R8Sa5Vsegs;VJA;R7A1R6R5R4A5R3A4F_;F_;FQ;Ftp;Frho;FA;Fnd;Fok;").
Proof using .
  intros ok nd A rho tp Q HP H n Hg w Hw. exact (H n Hg w (SPA_JAF_intro nd A rho tp w Hw HP)).
Qed.
Lemma etriple_JAF_in : ltac2:(tb__ "0|0|
S51S4bS1dS1S72Q40A1A1Sb0OF_;VPhi;R3A1Sb1Vsegs;Sa5Vsegs;Sc2VPhi;R6A2R5R4R3A5R2A3Sb1Vsegs;Sa5Vsegs;VJA;R7A1R6R5R4A5R3A3F_;F_;FQ;Ftp;Frho;FA;Fnd;").
Proof using .
  intros nd A rho tp Q HP H w Hw. exact (H w (SPA_JAF_intro nd A rho tp w Hw HP)).
Qed.

End Phi.

Section Phis.
Variable Phis : ltac2:(tb__ "0|0|
S1S2S1S14A1S1dOF_;A2A1").
Hypothesis HPhis : ltac2:(tb__ "0|3|
SaaS2S1S14A1M0S1dOF_;M1A2M2G2Sd5S9G0G1R1A3SaG0G1R1A3A2Lp;VPhis;A3").
Definition VK (k : nat) : list positive := ltac2:(tb__ "0|2|
SabS1S14A1M0Vk;Sa9S2G0S1dOF_;M1A2G0S9G0G1A2VPhis;A4SeS14A1A4").
Definition phiK (k : nat) : valuation -> Prop := ltac2:(tb__ "0|2|
SabS1dOF_;M0Vk;Sa9S2S1S14A1M1G0A2G0SaG1G0A2VPhis;A4S1dS1bL_;A4").
Lemma phiK_reads : ltac2:(tb__ "0|0|
S5Sd5S79R1A1S7bR1A1A2Fk;").
Proof using HPhis.
  intros k. unfold VK, phiK. revert k. induction Phis as [|p r IH]; intros [|k]; cbn [nth map].
  - intros rho rho' _ _ _ H. exact H.
  - intros rho rho' _ _ _ H. exact H.
  - exact (Forall_inv HPhis).
  - apply IH. exact (Forall_inv_tail HPhis).
Qed.

Definition fnode : Type := ltac2:(tb__ "0|0|
S2S2S4bS51A2S5A2").
Definition nodeIAF (n : fnode) : jnodeA := ltac2:(tb__ "0|2|
S8S4bSa6S9S4bS51S9S2S4bS51A2M0S5Vn;A3M1A3Sc2S7bSaG0S5Vn;A3A1SaS4bS51G1A3A2A4").

Definition echeckJAF (nodes : list fnode) (e : edgeA) : bool := ltac2:(tb__ "0|4|
S7ScbSa9S2S2S4bS51A2M0S5A2M1G0S9G0S5A2Vnodes;A4Ve;A2S6S76A1S0Lx;M2SadS76Vnodes;Sb6Ve;A1A3S76G1S0Lf;R1G0S5G0S0Lp;R2S4bS51G2SadS76Vnodes;Sb8Ve;A1A3S76G1S0Lf0;R1G0S5G0S0Lp0;R2S4bS51S7S7S122R8R3A2ScdS79R8A1M3Sb7Ve;A1A2A2Sc3S20S4cR7A1A1G3A2A2Ln0;La;X2x1Lkj;Lp0;X2x1Lf0;S4X6x2Ln;LTi;X2x1Lki;Lp;X2x1Lf;S4X6x2A2").

Definition echeckJAF_pf (pf : pfacts) (nodes : list fnode) (e : edgeA) : bool := ltac2:(tb__ "0|4|
S7Sd2Vpf;Sa9S2S2S4bS51A2M0S5A2M1G0S9G0S5A2Vnodes;A4Ve;A3S6S76A1S0Lx;M2SadS76Vnodes;Sb6Ve;A1A3S76G1S0Lf;R1G0S5G0S0Lp;R2S4bS51G2SadS76Vnodes;Sb8Ve;A1A3S76G1S0Lf0;R1G0S5G0S0Lp0;R2S4bS51S7S7S122R8R3A2ScdS79R8A1M3Sb7Ve;A1A2A2Sc3S20S4cR7A1A1G3A2A2Ln0;La;X2x1Lkj;Lp0;X2x1Lf0;S4X6x2Ln;LTi;X2x1Lki;Lp;X2x1Lf;S4X6x2A2").
Lemma echeckJAF_pf_eq : ltac2:(tb__ "0|0|
S1S76A1Sb4S16S0S81SfcS23S4cSb5R1A1A1A1A1R2R1A3S7cR2R1A2A3Fe;Fnodes;").
Proof using . intros. reflexivity. Qed.

Lemma echeckJAF_sound : ltac2:(tb__ "0|0|
S1S76A1Sb4S16S0S7cR2R1A2S3A3SbbSa9S76Sb9S7eR3A4R2A2F_;Fe;Fnodes;").
Proof using ALA HPhis.
  intros nodes e H Ti Tj Hi Hj rho rho' tp tr md Hag HJF HF.
  unfold echeckJAF in H. apply andb_prop in H as [HE H].
  pose proof (echeckJA2_sound (map fst nodes) e HE) as EOK.
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [[[Si ndi] ki]|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [[[Sj ndj] kj]|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-. cbn [nodeIAF fst snd] in *. destruct HJF as [HJ HP].
  apply andb_prop in H as [H HV]. apply andb_prop in H as [Hk HS]. apply Nat.eqb_eq in Hk. subst kj.
  assert (Hi' : nth_error (map (nodeIA AInv CST XGL NP Kc rho0 P0f FB FF BX PA) (map fst nodes)) (ea_src e) = Some (Si, JA ndi)).
  { rewrite map_map, nth_error_map. cbn [option_map]. setoid_rewrite Ei. reflexivity. }
  assert (Hj' : nth_error (map (nodeIA AInv CST XGL NP Kc rho0 P0f FB FF BX PA) (map fst nodes)) (ea_tgt e) = Some (Sj, JA ndj)).
  { rewrite map_map, nth_error_map. cbn [option_map]. setoid_rewrite Ej. reflexivity. }
  split.
  - exact (EOK (Si, JA ndi) (Sj, JA ndj) Hi' Hj' rho rho' tp tr md Hag HJ HF).
  - apply (phi_sub (VK ki) (phiK ki) (phiK_reads ki)); [exact HS|]. exact (phi_agree (VK ki) (phiK ki) (phiK_reads ki) _ rho rho' HV Hag HP).
Qed.

Lemma echeckJAF_all : ltac2:(tb__ "0|0|
S1S76A1S1Sb4A1S16S0SaeSb4S7cR2A1R1A3S3A3SaaSb4SbbSa9S76Sb9S7eR3A4A1R2A3F_;Fes;Fnodes;").
Proof using ALA HPhis.
  intros nodes es H. apply Forall_forall. intros e He. apply echeckJAF_sound. exact (proj1 (forallb_forall _ _) H e He).
Qed.

Definition jcertAF_ref (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list fnode) : bool := ltac2:(tb__ "0|8|
S7SaeS76S76S7S7S7S11S2aS4cS9S4bS51S9S2S4bS51A2M0S5R1A3M1A3M2A1M3A1A1S52S20G3A1M4SaS4bS51G1A3A2A2SfdVNP;G4A2A2Sc3G4S79SaG0S5R1A3A1A2A2Ln;VcutsD;A3S6S1Sb4A1M5A1S0Lx;SbcVsegs;Vfuel;Vcutpcs;Vg;Sa9S2G0S5A2M6S4bG6G2Ln;M7VcutsD;A4Sa9G6S4bG7VexitsD;A4A6G5SaeSb4S7cScS76VcutsD;VexitsD;A3A1R1A3Les;S4X6x2A2").

Definition jcertAF (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list fnode) : bool := ltac2:(tb__ "0|9|
S7SaeS76S76S7S7S7S11S2aS4cS9S4bS51S9S2S4bS51A2M0S5R1A3M1A3M2A1M3A1A1S52S20G3A1M4SaS4bS51G1A3A2A2SfdVNP;G4A2A2Sc3G4S79SaG0S5R1A3A1A2A2Ln;VcutsD;A3S6S1S2Sb4Sf9A2M5A1M6A1S0Lx;SbdVsegs;Vfuel;Vcutpcs;Vg;Sa9S2G0S5A2M7S4bG7G2Ln;M8VcutsD;A4Sa9G7S4bG8VexitsD;A4A6G6SaeG5G5S81SaSb4Sf9R1A3ScS76VcutsD;VexitsD;A3S9Sb4Sf9R1A3A3Lep;R1A3Leps;S4X6x2A2").
Lemma jcertAF_ref_eq : ltac2:(tb__ "0|1|
S5S1S13A1S14S1S76A1M0G0S16S0S86R5R4R3R2R1A5S8aR5R4R3R2R1A5A3FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros. unfold jcertAF, jcertAF_ref. rewrite cfg_edgesA_pf_eq.
  destruct (cfg_edgesA segs fuel cutpcs g (map (fun n => fst (fst n)) cutsD) (map (fun n => fst (fst n)) exitsD)) as [es|]; cbn [option_map]; [|reflexivity].
  rewrite (forallb_map_addpf (echeckJAF (cutsD ++ exitsD)) (fun pf e => echeckJAF_pf pf (cutsD ++ exitsD) e) es (echeckJAF_pf_eq (cutsD ++ exitsD))). reflexivity.
Qed.

Lemma map_fst_nodeIAF : ltac2:(tb__ "0|2|
S1S76A1S16S1S4bA1Sa9S2S4bSa6A2S4bS9S4bSa6A2Sa9S76Sb9S7eR1A4A4Sa9S2S2S4bS51A2M0S5A2M1S4bG1S9S4bS51S9G0S5R1A3A3Ln;R1A4A3Fl;").
Proof using . intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Theorem cfg_sound_JAF : ltac2:(tb__ "0|6|
S5S1S13A1S14S1S76A1M0G0Sb0OF_;Sb3S63Vsegs;VKc;R2A3S16S0S86R8R7R6R5R4A5S3A3S4bS51S5S1dS1S72Q40A1A1M1SacS2S2S4bS51A2M2S5A2M3S8G2S5S8S4bS51R5R4A4R3A4M4RaA3Sb2Vsegs;RaSa5Vsegs;Sc2S7bR4A1R5A2R6R3R2A5M5Sb0S18S11fVsegs;Sa9S76Sb9S7eRdA4R1A3RaR1A1A2Lw;A4F_;Ftp;Frho;FkX;FndX;FX;S4bS51S5S1dG1SacG3G4RcA3Sb2Vsegs;RbG5RaA4F_;Ftp;Frho;FkT;FndT;FT;F_;F_;F_;FQ;Fok;FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof using ALA HKc HPhis.
  intros fuel cutpcs g cutsD exitsD ok Q Hok Hc Hexits T ndT kT rho tp HinT.
  rewrite jcertAF_ref_eq in Hc. unfold jcertAF_ref in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edgesA segs fuel cutpcs g (map (fun n => fst (fst n)) cutsD) (map (fun n => fst (fst n)) exitsD)) as [es|] eqn:Hes; [|discriminate].
  apply (cfg_sound_genTA segs fuel cutpcs g (map nodeIAF cutsD) (map nodeIAF exitsD) es ok Q).
  - intros T' J' Hin. apply in_map_iff in Hin as ([[S k] kk] & Heq & _). cbn in Heq. injection Heq as <- <-.
    apply ok_frameA_JAF. exact Hok.
  - intros T' J' Hin. apply in_map_iff in Hin as ([[S k] kk] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. cbn [fst snd] in X.
    apply andb_prop in X as [X HV]. apply andb_prop in X as [X Hn]. apply andb_prop in X as [_ Hb]. apply Pos.leb_le in Hn.
    apply (stableA_JAF (VK kk) (phiK kk) (phiK_reads kk)); [exact Hn | exact Hb | exact HV].
  - rewrite !map_fst_nodeIAF. exact Hes.
  - rewrite <- map_app. apply echeckJAF_all. exact Hc.
  - intros X JX rho' tp' Hin. apply in_map_iff in Hin as ([[S k] kk] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    exact (Hexits S k kk rho' tp' Hin).
  - exact (in_map nodeIAF cutsD (T, ndT, kT) HinT).
Qed.

Definition efnode : Type := ltac2:(tb__ "0|0|
S2S2S2S4bS51A2S5A2S2S13S1cA2A2").
Definition ef_state (n : efnode) : axst := fst (fst (fst n)).
Definition ef_nd (n : efnode) : ndesc := snd (fst (fst n)).
Definition ef_k (n : efnode) : nat := snd (fst n).
Definition ef_rank (n : efnode) : Z := fst (snd n).
Definition ef_var (n : efnode) : sv := snd (snd n).
Definition efmeasA (n : efnode) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S68S70S7aVn;A1S6bZ2Z40A2A2S73Q40S30Vrho;S78Vn;A1A2A2A2").
Definition enodeIAF (n : efnode) : enodeA := ltac2:(tb__ "0|0|
S8S2S4bSa6A2S1dS13Frho;S8S4bSa6S77Vn;A1Sc2S7bS82Vn;A1A1S83Vn;A1A2A4S84Vn;A1A4").
Definition efdrop (n : efnode) : fnode := fst n.

Definition eecheckJAF_ref (nodes : list efnode) (e : edgeA) : bool := ltac2:(tb__ "0|4|
S7S7cSa9S75S76S7dVnodes;A4Ve;A2S6S75A1S0Lx;M0SadS75Vnodes;Sb6Ve;A1A3S75G0SadS75Vnodes;Sb8Ve;A1A3S75S7S7S2cS20S4cS77R2A1A1A1S78R2A1M1A2S6aZ0S7aR1A1M2A2A2S12S6eG2S7aR2A1M3A2S7S6cG2G3A2S10bS23S4cSb5Ve;A1A1A1S35S106Sb7Ve;A1S78R1A1A2G1A2A2A2A2A2Lnj;S4X6x2Lni;S4X6x2A2").

Definition eecheckJAF (nodes : list efnode) (e : edgeA) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S7cSa9S75S76S7dVnodes;A4Ve;A2S6S75A1S0Lx;M1SadS75Vnodes;Sb6Ve;A1A3S75G1SadS75Vnodes;Sb8Ve;A1A3S75G0S2cS20S4cS77R2A1A1A1S78R2A1M2A2G0S6aZ0S7aR1A1M3A2G0S6eG3S7aR2A1M4A2S3G0S6cG3G4A2SfbSfcS23S4cSb5Ve;A1A1A1A1S35S106Sb7Ve;A1S78R1A1A2G2A2A2S4X0x2X0x2S4X0x2S4X0x2Lnj;S4X6x2Lni;S4X6x2S4X0x2").

Definition eecheckJAF_pf (pf : pfacts) (nodes : list efnode) (e : edgeA) : bool := ltac2:(tb__ "0|5|
S0S0L_;M0S81Vpf;Sa9S75S76S7dVnodes;A4Ve;A3S6S75A1S0Lx;M1SadS75Vnodes;Sb6Ve;A1A3S75G1SadS75Vnodes;Sb8Ve;A1A3S75G0S2cS20S4cS77R2A1A1A1S78R2A1M2A2G0S6aZ0S7aR1A1M3A2G0S6eG3S7aR2A1M4A2S3G0S6cG3G4A2SfbVpf;S35S106Sb7Ve;A1S78R1A1A2G2A2A2S4X0x2X0x2S4X0x2S4X0x2Lnj;S4X6x2Lni;S4X6x2S4X0x2").
Lemma eecheckJAF_pf_eq : ltac2:(tb__ "0|0|
S1S75A1Sb4S16S0S87SfcS23S4cSb5R1A1A1A1A1R2R1A3S7fR2R1A2A3Fe;Fnodes;").
Proof using . intros. reflexivity. Qed.
Lemma eecheckJAF_ref_eq : ltac2:(tb__ "0|0|
S1S75A1Sb4S16S0S7fR2R1A2S88R2R1A2A3Fe;Fnodes;").
Proof using .
  intros nodes e. unfold eecheckJAF, eecheckJAF_ref.
  destruct (echeckJAF (map efdrop nodes) e); [|reflexivity]. cbn [andb].
  destruct (nth_error nodes (ea_src e)) as [ni|]; [|reflexivity]. destruct (nth_error nodes (ea_tgt e)) as [nj|]; [|reflexivity].
  rewrite DigFastA.mk_pf_f_eq, prove_sprop_pf_eq.
  destruct (sv_below (ss_next (ax_S (ef_state ni))) (ef_var ni)); [|reflexivity]. destruct (0 <=? ef_rank nj); [|reflexivity].
  destruct (ef_rank nj <? ef_rank ni); [reflexivity|]. destruct (ef_rank nj =? ef_rank ni); reflexivity.
Qed.

Lemma eecheckJAF_sound : ltac2:(tb__ "0|0|
S1S75A1Sb4S16S0S7fR2R1A2S3A3SbeSa9S75SbaS80R3A4R2A2F_;Fe;Fnodes;").
Proof using ALA HPhis.
  intros nodes e H ni nj Hi Hj rho rho' tp tr md Hag HJ HF.
  rewrite eecheckJAF_ref_eq in H. unfold eecheckJAF_ref in H. apply andb_prop in H as [HE H].
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [di|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [dj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [Hvb Hr0]. apply Z.leb_le in Hr0.
  pose proof (echeckJAF_sound (map efdrop nodes) e HE) as EOK.
  assert (Hi' : nth_error (map nodeIAF (map efdrop nodes)) (ea_src e) = Some (ef_state di, JAF (phiK (ef_k di)) (ef_nd di))).
  { rewrite !nth_error_map, Ei. destruct di as [[[a b] c] d]. reflexivity. }
  assert (Hj' : nth_error (map nodeIAF (map efdrop nodes)) (ea_tgt e) = Some (ef_state dj, JAF (phiK (ef_k dj)) (ef_nd dj))).
  { rewrite !nth_error_map, Ej. destruct dj as [[[a b] c] d]. reflexivity. }
  cbn [enodeIAF ena_state ena_pred ena_meas fst snd] in *.
  split; [exact (EOK _ _ Hi' Hj' rho rho' tp tr md Hag HJ HF)|].
  unfold efmeasA. rewrite <- eval_subst.
  pose proof (bv_urange (eval (rho) (ef_var di))) as R1.
  pose proof (bv_urange (eval rho' (sv_subst (ea_sub e) (ef_var dj)))) as R2.
  assert (EV : eval rho' (ef_var di) = eval rho (ef_var di)).
  { symmetry. eapply eval_agree_vals; [apply agree_below_vals; exact Hag | exact Hvb]. }
  apply orb_prop in Hdec as [Hlt|Heq].
  - apply Z.ltb_lt in Hlt. nia.
  - apply andb_prop in Heq as [Heq Hp]. apply Z.eqb_eq in Heq. rewrite Heq.
    pose proof (prove_sprop_sound rho' _ _ HF Hp) as X. cbn [holds] in X. rewrite EV in X. nia.
Qed.

Definition ejcertAF_ref (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list efnode) : bool := ltac2:(tb__ "0|3|
S7SaeS75S75S7S7S7S7S11S2aS4cS77R1A1A1M0A1A1S52S20G0A1M1S83R1A1A2A2SfdVNP;G1A2A2S2cG1S78R1A1A2A2Sc3G1S79S82R1A1A1A2A2Ln;VcutsE;A3S6S1Sb4A1M2A1S0Lx;SbcVsegs;Vfuel;Vcutpcs;Vg;Sa9S75S4bS77VcutsE;A4Sa9S75S4bS77VexitsE;A4A6G2SaeSb4S7fScS75VcutsE;VexitsE;A3A1R1A3Les;S4X6x2A2").

Definition ejcertAF (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list efnode) : bool := ltac2:(tb__ "0|4|
S7SaeS75S75S7S7S7S7S11S2aS4cS77R1A1A1M0A1A1S52S20G0A1M1S83R1A1A2A2SfdVNP;G1A2A2S2cG1S78R1A1A2A2Sc3G1S79S82R1A1A1A2A2Ln;VcutsE;A3S6S1S2Sb4Sf9A2M2A1M3A1S0Lx;SbdVsegs;Vfuel;Vcutpcs;Vg;Sa9S75S4bS77VcutsE;A4Sa9S75S4bS77VexitsE;A4A6G3SaeG2G2S87SaSb4Sf9R1A3ScS75VcutsE;VexitsE;A3S9Sb4Sf9R1A3A3Lep;R1A3Leps;S4X6x2A2").
Lemma ejcertAF_ref_eq : ltac2:(tb__ "0|1|
S5S1S13A1S14S1S75A1M0G0S16S0S85R5R4R3R2R1A5S89R5R4R3R2R1A5A3FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros. unfold ejcertAF, ejcertAF_ref. rewrite cfg_edgesA_pf_eq.
  destruct (cfg_edgesA segs fuel cutpcs g (map ef_state cutsE) (map ef_state exitsE)) as [es|]; cbn [option_map]; [|reflexivity].
  rewrite (forallb_map_addpf (eecheckJAF (cutsE ++ exitsE)) (fun pf e => eecheckJAF_pf pf (cutsE ++ exitsE) e) es (eecheckJAF_pf_eq (cutsE ++ exitsE))). reflexivity.
Qed.

Lemma map_ef_state : ltac2:(tb__ "0|0|
S1S75A1S16S1S4bA1Sa9SbaS4bSbfSa9S75SbaS80R1A4A4Sa9S75S4bS77R1A4A3Fl;").
Proof using . intros l. rewrite map_map. apply map_ext. intros [[[a b] c] d]. reflexivity. Qed.

Theorem cfg_complete_JAF : ltac2:(tb__ "0|8|
S5S1S13A1S14S1S75A1M0G0Sb0OF_;S16S0S85R6R5R4R3R2A5S3A3S4bS51S5S2S13S1cA2M1S1dS1S72Q40A1A1M2SacS2S2S2S4bS51A2M3S5A2M4G1A2M5S8G4G1S8G3S5S8S4bS51R6R5A4R4A4R3A4M6R9A3Sb1Vsegs;Sa5Vsegs;Sc2S7bR5A1R6A2R7R3R2A5M7Sb0S18S11eVsegs;Sa9S75SbaS80RcA4S84S8G4G1S8G3S5S8S4bS51R8R7A4R6A4R5A4R4A2R1A4RaR1A1A2Lw;A3F_;Ftp;Frho;Frv;FkX;FndX;FX;S4bS51S5G1S1dG2SacG5G6RbA3Sb1Vsegs;G7RaA3F_;Ftp;Frho;Frv;FkT;FndT;FT;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ALA HKc HPhis.
  intros fuel cutpcs g cutsE exitsE Q Hc Hexits T ndT kT rv rho tp HinT.
  rewrite ejcertAF_ref_eq in Hc. unfold ejcertAF_ref in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edgesA segs fuel cutpcs g (map ef_state cutsE) (map ef_state exitsE)) as [es|] eqn:Hes; [|discriminate].
  apply (cfg_complete_genTA segs fuel cutpcs g (map enodeIAF cutsE) (map enodeIAF exitsE) es Q) with (n := enodeIAF (T, ndT, kT, rv)).
  - intros n Hin. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X.
    apply andb_prop in X as [X HV]. apply andb_prop in X as [X _]. apply andb_prop in X as [X Hn]. apply andb_prop in X as [_ Hb]. apply Pos.leb_le in Hn.
    cbn [enodeIAF ena_state ena_pred fst snd]. apply (stableA_JAF (VK (ef_k d)) (phiK (ef_k d)) (phiK_reads (ef_k d))); [exact Hn | exact Hb | exact HV].
  - intros n rho1 rho2 Hin Hag. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ Hvb].
    cbn [enodeIAF ena_state ena_meas fst snd] in *. unfold efmeasA.
    rewrite (eval_agree_vals _ rho1 rho2 _ (agree_below_vals _ _ _ Hag) Hvb). reflexivity.
  - rewrite !map_ef_state. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply eecheckJAF_sound. exact (proj1 (forallb_forall _ _) Hc e He).
  - intros X rho' tp' Hin. apply in_map_iff in Hin as ([[[S k] kk] r] & <- & Hin). cbn [enodeIAF ena_state ena_pred ena_meas ef_state ef_nd ef_k fst snd].
    exact (Hexits S k kk r rho' tp' Hin).
  - exact (in_map enodeIAF cutsE _ HinT).
Qed.

Lemma ejcertAF_jcertAF : ltac2:(tb__ "0|1|
S5S1S13A1S14S1S75A1M0G0S16S0S85R5R4R3R2R1A5S3A3S16S0S86R6R5R4Sa9S75S76S7dR3A4Sa9S75S76S7dR2A4A5S3A3F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cutsE exitsE H. rewrite ejcertAF_ref_eq in H. rewrite jcertAF_ref_eq. unfold ejcertAF_ref in H. unfold jcertAF_ref.
  apply andb_prop in H as [Hs H].
  assert (E1 : forall l, map (fun n : fnode => fst (fst n)) (map efdrop l) = map ef_state l).
  { intros l. rewrite map_map. apply map_ext. intros [[[a b] c] d]. reflexivity. }
  rewrite !E1.
  destruct (cfg_edgesA segs fuel cutpcs g (map ef_state cutsE) (map ef_state exitsE)) as [es|]; [|discriminate].
  apply andb_true_intro. split.
  - apply forallb_forall. intros n Hin. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hs d Hin) as X. apply andb_prop in X as [X HV]. apply andb_prop in X as [X _].
    destruct d as [[[a b] c] dd]. cbn [efdrop fst snd ef_state ef_nd ef_k] in *. rewrite X, HV. reflexivity.
  - rewrite <- map_app. apply forallb_forall. intros e He. pose proof (proj1 (forallb_forall _ _) H e He) as X.
    rewrite eecheckJAF_ref_eq in X. unfold eecheckJAF_ref in X. apply andb_prop in X as [X _]. exact X.
Qed.

Lemma reenter_cutJAF : ltac2:(tb__ "0|1|
Sb0OF_;S1S76A1S4bS51S5Sb3S1dS1S72Q40A1A1SacS2S2S4bS51A2M0S5A2S8G0S5S8S4bS51R6R5A4R4A4R7A3S7bR5R3A2Sb2Vsegs;RaSa5Vsegs;VJA;R7A1R8R4R3A5Sb0S18S11fVsegs;Sa9S76Sb9S7eRaA4R1A3R6R1A1A2Lw;A4F_;F_;Ftp;Frho;FQ;Fk;Fnd;FT;FcutsD;Fok;").
Proof using .
  intros ok cutsD T nd k Q rho tp Hin HP. apply (triple_JAF_in (phiK k) ok nd T rho tp _ HP). apply reenter_cutGTA. exact (in_map nodeIAF cutsD (T, nd, k) Hin).
Qed.

Lemma ereenter_cutJAF : ltac2:(tb__ "0|4|
S1S75A1S4bS51S5S2S13S1cA2M0Sb0OF_;S13S1dS1S72Q40A1A1SacS2S2S2S4bS51A2M1S5A2M2G0A2S8G2G0S8G1S5S8S4bS51R8R7A4R6A4R5A4R9A3S7bR7R3A2S17S67Z0S84S8G2G0S8G1S5S8S4bS51RaR9A4R8A4R7A4R4A2M3A2S69G3R5A2A2Sb1Vsegs;Sa5Vsegs;VJA;RaA1RbR5R4A5Sb0S18S11eVsegs;Sa9S75SbaS80RdA4R7R1A4R8R1A1A2Lw;A3F_;F_;F_;Ftp;Frho;Fbound;FQ;Frv;Fk;Fnd;FT;FcutsE;").
Proof using .
  intros cutsE T nd k rv Q bound rho tp Hin HP Hm. apply (etriple_JAF_in (phiK k) nd T rho tp _ HP).
  apply (ereenter_cutETA segs (map enodeIAF cutsE) (enodeIAF (T, nd, k, rv)) Q bound rho tp (in_map enodeIAF cutsE _ Hin) Hm).
Qed.
End Phis.

End Sum.

Section PostsP.
Variable NP : positive.
Variable Kc : KcA.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2S13S13A2S13A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Let JA : ltac2:(tb__ "0|1|
S1dS1dOF_;S1S2S13S13A2M0A1S1S2G0S13A2A1Sa0SdeOF_;S51Sa6Fnd;FPA;FBX;FFF;FFB;FP0f;Frho0;") := ltac2:(tb__ "0|0|
S62VAInv;VCST;VXGL;VNP;VKc;A5").

Definition JLAP (nd : ndesc) (Psi : valuation -> valuation -> Prop) : jpostA := ltac2:(tb__ "0|1|
S1dS1S72Q40A1A1M0S1dG0S1Sc1A1Sc0S17S5eVAInv;VCST;VXGL;VKc;VP0f;VFB;VFF;VBX;VPA;Vnd;R6R5R4R3R2R1A10VPsi;R6R4A2A2Lmd;Ltr;Ltp;Lrho;Ltp0;Lr0;").

Lemma exit_postGAF : ltac2:(tb__ "0|3|
Sb0OF_;S1dS1S72Q40A1A1M0S1dOF_;M1S1dG1F_;S51S1S2S4bSecA2M2A1S4bSb3SacG2S8S4bSecR2S120R4R5A2A4R3A3S1dR8R1A1R8RbR2A2F_;Frho;S1dG0Sb2Vsegs;RdSa5Vsegs;S113VNP;VKc;RcVP0f;VFB;VFF;VBX;VPA;RaR8AaR6R2R1A5Sb0S18R6R1A1SedVsegs;VNP;RdRcR8R1A6A2Lw;A4Ftp;Frho;F_;F_;FX;FP;FPosts;Fnd;FPsi;FPhi;Ftp0;Frho0;Fok;").
Proof using .
  intros ok rho0 tp0 Phi Psi nd Posts P X Hin HPsi. apply (exit_postPA segs ok _ NP rho0 tp0 Posts P (JLAP nd Psi) X Hin).
  intros rho tp tr md [(Ai & kc & Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA) HP]. split; [exact Hav|].
  split; [|exact (HPsi rho HP)]. split; [exact Hk|]. exists Ai, kc. repeat (split; [assumption|]). exact HPA.
Qed.

Lemma eexit_postGAF : ltac2:(tb__ "0|3|
S1dS1S72Q40A1A1M0S1dOF_;M1S1dG1F_;S51S1S2S4bSecA2M2A1S4bSb0OF_;SacG2S8S4bSecR2S120R4R5A2A4R3A3S1dR8R1A1R8RbR2A2F_;Frho;S1dG0Sb1Vsegs;Sa5Vsegs;S113VNP;VKc;RcVP0f;VFB;VFF;VBX;VPA;RaR8AaR6R2R1A5Sb0S18R6R1A1SedVsegs;VNP;RdRcR8R1A6A2Lw;A3Ftp;Frho;F_;F_;FX;FP;FPosts;Fnd;FPsi;FPhi;Ftp0;Frho0;").
Proof using .
  intros rho0 tp0 Phi Psi nd Posts P X Hin HPsi. apply (eexit_postPA segs _ NP rho0 tp0 Posts P (JLAP nd Psi) X Hin).
  intros rho tp tr md [(Ai & kc & Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA) HP]. split; [exact Hav|].
  split; [|exact (HPsi rho HP)]. split; [exact Hk|]. exists Ai, kc. repeat (split; [assumption|]). exact HPA.
Qed.

Lemma exit_postGA_F : ltac2:(tb__ "0|2|
Sb0OF_;S1dS1S72Q40A1A1M0S1dOF_;S51S1S2S4bSecA2M1A1S4bSb3SacG1S8S4bSecR2S5eVAInv;VCST;VXGL;VKc;VP0f;VFB;VFF;VBX;VPA;R4AaA4R3A3S1dG0Sb2Vsegs;RbSa5Vsegs;S113VNP;VKc;RaVP0f;VFB;VFF;VBX;VPA;R8R7AaR5R2R1A5Sb0S18R5R1A1SedVsegs;VNP;RbRaR7R1A6A2Lw;A4Ftp;Frho;F_;FX;FP;FPosts;Fnd;FPhi;Ftp0;Frho0;Fok;").
Proof using .
  intros ok rho0 tp0 Phi nd Posts P X Hin rho tp. apply (triple_JAF NP Kc rho0 P0f FB FF BX PA Phi ok nd P rho tp). intros _.
  exact (exit_postGA segs AInv CST XGL NP Kc P0f FB FF BX PA ok rho0 tp0 nd Posts P X Hin rho tp).
Qed.
Lemma eexit_postGA_F : ltac2:(tb__ "0|2|
S1dS1S72Q40A1A1M0S1dOF_;S51S1S2S4bSecA2M1A1S4bSb0OF_;SacG1S8S4bSecR2S5eVAInv;VCST;VXGL;VKc;VP0f;VFB;VFF;VBX;VPA;R4AaA4R3A3S1dG0Sb1Vsegs;Sa5Vsegs;S113VNP;VKc;RaVP0f;VFB;VFF;VBX;VPA;R8R7AaR5R2R1A5Sb0S18R5R1A1SedVsegs;VNP;RbRaR7R1A6A2Lw;A3Ftp;Frho;F_;FX;FP;FPosts;Fnd;FPhi;Ftp0;Frho0;").
Proof using .
  intros rho0 tp0 Phi nd Posts P X Hin rho tp. apply (etriple_JAF NP Kc rho0 P0f FB FF BX PA Phi nd P rho tp). intros _.
  exact (eexit_postGA segs AInv CST XGL NP Kc P0f FB FF BX PA rho0 tp0 nd Posts P X Hin rho tp).
Qed.
End PostsP.

End WithSegs.
