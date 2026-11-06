(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.

(* [comment removed for export] *)
Module ErrnoA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "prod"; "true"; "app"; "cons"; "length"; "nat"; "nil"; "option"; "None"; "S"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "ss_objs"; "rl"; "rm"; "rw"; "obj_range"; "ranges_disjoint"; "SLit"; "image_byte"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "ax_base"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA"; "errno_blind"; "errno_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "errno_addrA"; "KcA"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "ndesc"; "JA"; "JAi"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymSoundR SymFrame SymEntail SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA GlueA3 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model Iface RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition errno_obj : sobj := unknown_obj (SLit ERRNO_A) 0 4.

Definition errno_blind (J : jpredA) : Prop := ltac2:(tb__ "0|3|
S13S13S2S21Q40M0A1M1A1S2S34A1S33SfS1G1F_;S17R4A1S17R5A1A3SfS1S2S21Q8A1M2A1F_;S15R5A1S15R6A1A3G1S11S2cS22G0R1A2A1A1SfScG2A1S16R8R2A2S16R9R2A2A3F_;Fa;VJ;R8R6R5R4A4VJ;R8R7R6R5A4F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;").

Lemma errno_obj_range : ltac2:(tb__ "0|0|
S13SfS5S0S0A2S18R1S2bA2S3S0S0S24S30S24Z4A2A4A3Frho;").
Proof.
  intros rho. unfold obj_range, obj_lo_of, obj_hi_of, errno_obj, unknown_obj. cbn [ob_base ob_lo ob_hi eval].
  rewrite !soff_lit_small by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold ERRNO_A; rewrite two64; lia). f_equal; lia.
Qed.

Lemma range_off_errno : ltac2:(tb__ "0|0|
S0S0S0S10S31R3R1A2S32R1R2A2A2S11S2cR2A1A1F_;Fa;S19S3S0S0R3R2A4S3S0S0S24S30S24Z4A2A4A2F_;Fhi;Flo;").
Proof.
  intros lo hi H. unfold ranges_disjoint. cbn [fst snd].
  destruct (Z_le_gt_dec hi lo) as [E|E]; [left; exact E|]. right; right.
  destruct (Z_le_gt_dec hi ERRNO_A) as [E1|E1]; [left; exact E1|]. right.
  destruct (Z_le_gt_dec (ERRNO_A + 4) lo) as [E2|E2]; [exact E2|]. exfalso.
  apply (H (Z.max lo ERRNO_A)); unfold errno_addrA; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma SPA_errno_drop : ltac2:(tb__ "0|3|
S29S1fS2SaA1S2S12A1M0S13S2S21Q40A1A1S2S34A1M1S40S33S2aR9A1SfS4S37S9S12S14S1dR9A1A1A2R8A2S6A3SfG0S35S14S1dRaA1A1R9A2S7S12R8S8S12S2bSbS12A1A3M2A3A3S28Vsegs;RcRbR8R7S3G1S38R6S39R5R4A2A4A6S28Vsegs;RdS1eRcS36S1dRcA1RaA2A2S42R9G2S43R5R8R6A3A3R8S3G1S38R7S39R6R5A2A4A6F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fobjs;Fidxs;FC;FJ;").
Proof using .
  intros J C idxs objs rho tp tr ms md HJ Hok Hsel Hw.
  pose proof (SPA_select segs J rho C idxs tp _ Hok Hw) as Hw1. rewrite Hsel in Hw1.
  pose proof (SPA_unobj segs J rho (ax_setS C (set_objs (ax_S C) (objs ++ [errno_obj]))) objs [errno_obj] tp tr ms md eq_refl Hw1) as Hw2.
  cbv zeta in Hw2. apply Hw2. intros Hj. apply (HJ rho); [reflexivity | reflexivity | | exact Hj].
  intros a Ha. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho [errno_obj] a) as [Hin|Hn]; [|reflexivity].
  exfalso. apply Ha. destruct Hin as (o & [<-|[]] & Hr). rewrite errno_obj_range in Hr. exact Hr.
Qed.

Lemma SPA_errno_recarve : ltac2:(tb__ "0|8|
S29S1fS2SaA1S13S2S21Q40M0A1M1A1S27SfS1cS20R5A1S1aS45A1A3S0S10S31Z0R1A2S32R1Z4M2A2A2S10S11SfScS21Q8A1M3A1M4S41Vsegs;G1SdG3A1M5L_;S23G0S30S24R2A2A2M6A3G5A3A1S11SfG4S1bVsegs;G6A2G5A3A1A2F_;Foff;S3fS12S12S19S18R6R1A2S3S0S0S24S30S24G2A2A4A2Lo;S14S1dR7A1A1A3SfS4S37SeS9S12S14S1dR8A1A1A2A1R7A2S6A3S28Vsegs;RaR9R7R6R5A6S28Vsegs;RbS1eRaS36S1dRaA1M7S35S7S12S14G7A1S8S12S2bSbS12A1A3A3R9A2A2A2R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fidxs;FT;FJ;").
Proof using .
  intros J T idxs rho tp [tr [ms md]] Hbase Himg Hdis Hok Hw.
  assert (Eb : bv_unsigned (eval rho (SLit ERRNO_A)) = ERRNO_A) by (cbn [eval]; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold ERRNO_A; rewrite two64; lia); reflexivity).
  pose proof (SPA_carve_unknown_w segs J rho T (SLit ERRNO_A) 0 4 tp tr ms md Hw) as Hc. cbv zeta in Hc. rewrite Eb in Hc.
  assert (Hw1 : SPA segs J (ax_setS T (set_objs (ax_S T) (ss_objs (ax_S T) ++ [unknown_obj (SLit ERRNO_A) 0 4]))) rho tp (tr, mkCfg ms md)).
  { apply Hc; try (unfold ERRNO_A; lia); [reflexivity | | |].
    - intros off Hoff. exact (Himg off Hoff).
    - rewrite Z.add_0_r. exact Hdis.
    -
      intros x (r & y & j & _ & Hy & Hj & Hr & ->) Hx. rewrite Hbase in Hr, Hx. cbn [eval] in Hr, Hx.
      rewrite Z_to_bv_unsigned, bv_wrap_small in Hr, Hx by (unfold SHADOW_OFF; rewrite two64; lia).
      pose proof (bv_unsigned_in_range _ (eval rho (fst r))) as [R0 _].
      assert (Y0 : 0 <= y / 8) by (apply Z.div_pos; lia).
      unfold word_byte in Hx. set (z := SHADOW_OFF + y / 8) in *.
      assert (Z8 : SHADOW_OFF <= z / 8 * 8).
      { assert (SHADOW_OFF / 8 <= z / 8) by (apply Z.div_le_mono; unfold z; lia). unfold SHADOW_OFF in *. change (2147450880 / 8) with 268431360 in *. lia. }
      pose proof (Z.mul_div_le z 8 ltac:(lia)) as Z9.
      assert (Z10 : z / 8 * 8 <= 2 ^ 64 - 8).
      { assert (z / 8 <= (2 ^ 64 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 64 - 1) / 8) with 2305843009213693951 in *. lia. }
      rewrite Z_to_bv_unsigned, bv_wrap_small in Hx by (rewrite two64; lia). unfold SHADOW_OFF, ERRNO_A in *. lia. }
  assert (Hok' : select_ok (length (ss_objs (ax_S (ax_setS T (set_objs (ax_S T) (ss_objs (ax_S T) ++ [unknown_obj (SLit ERRNO_A) 0 4])))))) idxs = true).
  { cbn [ax_S ax_setS ss_objs set_objs]. rewrite length_app, Nat.add_comm. exact Hok. }
  exact (SPA_select segs J rho _ idxs tp _ Hok' Hw1).
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S26S26S26S27R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS26S26R3VTR;R3R2A2F_;VTR;S27S10R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Theorem errno_drop_T : ltac2:(tb__ "0|4|
S29S1fS2SaA1S2S12A1M0S26S13S2S21Q40M1A1M2A1S2aR7A1SfS4S37S9S12S14S1dR7A1A1A2R6A2S6A3SfG0S35S14S1dR8A1A1R7A2S7S12R6S8S12S2bSbS12A1A3A3A3S13SfS1G2F_;S17R1A1S17R6A1A3SfS1S2S21Q8A1M3A1F_;S15R2A1S15R7A1A3G2S11S2cS22G1R1A2A1A1SfScG3A1S16R5R2A2S16RaR2A2A3F_;Fa;VTR;S28Vsegs;ReS1eRdS36S1dRdA1RbA2A2R4R8A5RaA2F_;F_;F_;Frho1;VTR;S28Vsegs;RbRaR6R5A5R7A2F_;F_;F_;F_;Ftp;Frho;FQ;Fobjs;Fidxs;FC;FJ;").
Proof using TR_pre TR_exw TR_pureh.
  intros J C idxs objs Q rho tp HJ Hok Hsel HT.
  apply (TR_pre (fun w => exists rho1, (rw rho1 = rw rho /\ rl rho1 = rl rho /\ (forall a, ~ errno_addrA (bv_unsigned a) -> rm rho1 a = rm rho a))
                                       /\ SPA segs J (ax_setS C (set_objs (ax_S C) objs)) rho1 tp w)).
  - intros [tr [ms md]] Hw. exists (rho_absorb rho [errno_obj] (vms md tp ms)). split.
    + split; [reflexivity|]. split; [reflexivity|]. intros a Ha. unfold rho_absorb. cbn [rm].
      destruct (in_ranges_dec rho [errno_obj] a) as [Hin|Hn]; [|reflexivity].
      exfalso. apply Ha. destruct Hin as (o & [<-|[]] & Hr). rewrite errno_obj_range in Hr. exact Hr.
    + exact (SPA_errno_drop J C idxs objs rho tp tr ms md HJ Hok Hsel Hw).
  - apply TR_exw. intros rho1. apply TR_pureh. intros (E1 & E2 & E3). exact (HT rho1 E1 E2 E3).
Qed.
End T.

Section J.
Variable AInv : ltac2:(tb__ "0|0|
S2fS13S2S21Q40A1A1S33OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S2eVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S25VCST;R1A2S10S31Z0R2A2S32R2S44A2A2F_;Fa;").
Hypothesis HERR : ltac2:(tb__ "0|0|
S0S2cR1A1S25VCST;R2A2F_;Fa;").

Lemma JAi_errno_blind : ltac2:(tb__ "0|1|
S1S2dS13S13OF_;S2S5S0S0A2M0A1S2S5G0S0A2A1S3aS2fOF_;S1S3cS2fS0SfS4S3bR4R3A2S6A3S2aS3eVAInv;VCST;VXGL;RdRcRbRaR9R8R7R6R4R3R2AeA1F_;Fkc;FAi;Fnd;Fn;FPA;FBX;FFF;FFB;FP0f;Frho0;FKc;FNP;").
Proof using ALA HCST HERR.
  intros NP Kc rho0 P0f FB FF BX PA n nd Ai kc Hnb rho rho' tp tr md E1 E2 E3 HJ.
  exact (JAi_errno_havoc segs AInv CST XGL ALA HCST NP Kc rho0 P0f FB FF BX PA n nd Ai kc rho rho' tp tr md Hnb HERR E1 E2 E3 HJ).
Qed.
Lemma JA_errno_blind : ltac2:(tb__ "0|1|
S1S2dS13S13OF_;S2S5S0S0A2M0A1S2S5G0S0A2A1S3aS2fOF_;S1S3cSfS4S3bR2R1A2S6A3S2aS3dVAInv;VCST;VXGL;RbRaR9R8R7R6R5R4R2AcA1F_;Fnd;Fn;FPA;FBX;FFF;FFB;FP0f;Frho0;FKc;FNP;").
Proof using ALA HCST HERR.
  intros NP Kc rho0 P0f FB FF BX PA n nd Hnb rho rho' tp tr md E1 E2 E3 (Ai & kc & HJ). exists Ai, kc.
  exact (JAi_errno_blind NP Kc rho0 P0f FB FF BX PA n nd Ai kc Hnb rho rho' tp tr md E1 E2 E3 HJ).
Qed.
End J.
End WithSegs.
End ErrnoA.

(* [comment removed for export] *)
Module TobjJAC.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "sobj"; "ss_facts"; "sprop"; "holds"; "SLit"; "SPUle"; "sv_eqb"; "obj_range"; "rw"; "SAlu"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "False"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "app"; "fst"; "pair"; "snd"; "option"; "Some"; "cons"; "andb"; "nil"; "nat"; "false"; "None"; "S"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "NoDup"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "aa_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_tv"; "nd_bd"; "nd_fr"; "NDA"; "ffinA"; "TPA"; "fbinA"; "nd_am"; "frinA"; "tvinA"; "am_subst"; "nd_below"; "pclFA"; "JA_pre"; "am_eqb"; "amode"; "frv"; "ok_frameKA"; "JA"; "JAi"; "keptFA"; "pclSA"; "untracked"; "untrackedZ"; "JAk"; "JLA"; "am_svs"; "cntS"; "fcensus"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_subst"; "BXok_d"; "bd_below"; "bd_wpos"; "bxt"; "TVMAXn"; "bd_vars_all"; "bsumK"; "bsumV"; "bxK"; "bxN"; "bxS"; "bxV"; "mkBX"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "call_linkP"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "entails_frA"; "call_checkPA"; "LQPA"; "import_subA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "remove_nth"; "T_ok"; "tvd"; "tvz"; "import_tv"; "tv_sub_eqb"; "ivar_ok"; "tvv"; "new_objs_tv"; "patchf"; "rho_patch"; "tvL_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.WithSegs.Client"; "pdescA"; "FFx"; "pclMA"; "T_afterA3"; "xrs_inclb"; "PostsC"; "pd_okA"; "robjs_okF"; "xrs_okF"; "BXx"; "amL_ok"; "bdL_ok"; "xr_eqb"; "xr_post_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "payA"; "cmaddrA"; "xr_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Pre_stack_free"; "L_stack_free"; "V_FL"; "V_TOP"; "JL_stack_free"; "J_stack_free_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "errno_addrA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_postA3"; "import_okPA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.WithSegs"; "FFx"; "T_afterA3"; "pclMA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.WithSegs.Frames"; "robjs_okL"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S31S3S16S68Q40A1A1S56OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb0Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0Sb6VCST;R1A2S10S77Z0R2A2S79R2Sc0A2A2F_;Fa;").
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0Sb6VXGL;R1A2S10S77Z0R2A2S79R2Sc0A2A2F_;Fa;").

Section Client.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S16S17S17S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Context {dC : Z}.

Variable P0c : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17G0S0A2A1S3OF_;F_;F_;").

Variable PAc : AA -> Prop.
Hypothesis HPAc0 : ltac2:(tb__ "0|0|
S31VPA;R1A1VPAc;R2A1F_;FA;").
Hypothesis HPAc : ltac2:(tb__ "0|0|
S31S31VPA;R2A1VPAc;R2A1VPA;R3A1F_;F_;FA';FA;").
Variable PreC : axst.
Variable ndC : ndesc.
Definition pdescA : Type := (axst * ndesc)%type.
Variable PD : list pdescA.
Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
SfS1S4S29VPreC;A1A1VNPc;A3").
Hypothesis HfrC : nd_fr ndC = [].
Hypothesis HbaseC : ltac2:(tb__ "0|0|
SfS2S2bVPreC;A1S9Sc1A1A3").

Let JAi : ltac2:(tb__ "0|0|
S35S31S0S54Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S35S54Fnd;") := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let payA : ltac2:(tb__ "0|1|
S16S7A1S2S0S16S59A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
Sa5VNP;Vrho0;VP0f;A3").

Definition PostsC (FBc : list (Z * Z)) (FFc : list (Z * Z * Z)) (BXc : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S84S17S28S35A2M0S17S28S7dA2G0S1cS28S7dS1bS28S35R1A3S4fVAInv;VCST;VXGL;VKc;VP0c;VFBc;VFFc;A2VFBc;VFFc;VBXc;VPAc;S1dS28S35R1A3AaA4Ld;VPD;A4").

Definition FFx (rho : valuation) (fr : list (sv * Z * sv)) : list (Z * Z * Z) := ltac2:(tb__ "0|5|
S1aS17S17S0S0A2M0S0A2M1VFF;S84S17S17S2S0A2M2S2A2M3G1G3S1cG0S0S1cS0S0S1bS0S0S46Vrho;R1A2M4A3S1dS0S0G4A3A4S58Vrho;S1dG2S2R1A3A2A4Lx;Vfr;A4A3").

Definition BXx (rho : valuation) (brest : list bitem) (kept : list (sv * sv)) : bxt := ltac2:(tb__ "0|1|
S67S1cS0S0S78S7cZ0M0S62Vbrest;Vrho;A2A2S66VBX;A1A2S78S7cG0S61Vbrest;Vrho;A2A2S63VBX;A1A2A4S65VBX;A1S78S64VBX;A1S51Vrho;Vkept;A2A2A3").
Lemma BXx_nonneg : ltac2:(tb__ "0|2|
S0S3S16S59A1S16S17S2S2A2M0A1SfS18S21S7aZ1M1R4A2S7aS78R4G1A2VdF;A2A2S19A3Sc2S27G0R2A2S5fA2S5bR6S9fR5R4R3A3A2F_;F_;Fkept;Fbrest;Frho;Fd;").
Proof using HBX. clear HnextPre HfrC HbaseC. intros d rho brest kept Hd Hlen. pose proof HBX as ([[H1 H2] H3] & _).
  pose proof (cntS_bounds rho kept) as CB. pose proof (cntS_le_TVMAX rho kept Hlen) as CL.
  apply (BXok_d_mono dF d BX); [exact HBX | reflexivity | unfold BXx, bxV; cbn [bx2 fst]; unfold bxV in H1; lia | unfold BXx, bxK; cbn [bx2 snd]; unfold bxK in H2; lia
                              | unfold BXx; cbn [bxN]; lia | exact Hd].
Qed.

Lemma In_FFx : ltac2:(tb__ "0|5|
S3S16S17S17S2S0A2M0S2A2M1A1S17S17S0S0A2M2S0A2M3S14S2cG3R1S97R3R2A2A3S13S2cG3R1VFF;A3S11G1G1S10S2cG1R1R3A3SfG3R2S1cG2S0S1cS0S0S1bS0S0S46R4R1A2M4A3S1dS0S0G4A3A4S58R4S1dG0S2R1A3A2A4A3A2Lx;A2A2A2Fy;Ffr;Frho;").
Proof using .
  intros rho fr y. unfold FFx. rewrite in_app_iff, in_map_iff. split.
  - intros [H|(x & Hx & Hin)]; [left; exact H | right; exists x; auto].
  - intros [H|(x & Hin & ->)]; [left; exact H | right; exists x; auto].
Qed.

Definition pclMA (FBc : list (Z * Z)) (FFc : list (Z * Z * Z)) (a : Z) : Prop := ltac2:(tb__ "0|1|
S13S10S77S89Vrho0;A1Va;A2S79Va;S7bZ2Z2fA2A2A2S13S10Sb6VCST;Va;A2S12Sb1Va;A1A1A2S13S11S0S0S11S0S0S10S2cS17S0S0A2M0S1cS0S0R2R1A4VFBc;A3S10S77R2Va;A2S79Va;S78R2R1A2A2A2A2Ln;A2Lb;A2S11S0S0S11S0S0S11S0S0S10S2cS17G0S0A2S1cG0S0S1cS0S0R3R2A4R1A4VFFc;A3S10S77R3Va;A2S79Va;S78R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2").

Lemma pclMA_pclFA : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17G0S0A2A1S0S98R3R2R1A3S42VCST;Vrho0;R4R3R2A5F_;Fa;FFFc;FFBc;").
Proof using .
  intros FBc FFc a [H|[H|[H|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
  right; right; right. exists f, s, fl. auto.
Qed.

Lemma T0_calleeA : ltac2:(tb__ "0|0|
S74S3S16S5A1S76S6eVNP;Vrho0;R3A3SfS18Sa4VNP;R5A2S19A3SfS0S89S73S72R5R4R3A3R6A2A1S89Vrho0;A1A3F_;F_;Fms;FRb;Frho;Fs;").
Proof using .
  clear. intros s rho Rb ms [Hw _] H. unfold call_checkTA in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [E30 N30].
  apply sv_eqb_sound in E30. apply Pos.ltb_lt in N30. unfold T0. change Contract.V_TOP with Iface.V_TOP.
  rewrite rw_call', E30. cbn [eval]. rewrite <- (Hw _ N30). reflexivity.
Qed.
Lemma TPA_calleeA : ltac2:(tb__ "0|0|
S31S74S3S16S5A1S76S6eVNP;Vrho0;R3A3SfS18Sa4VNP;R5A2S19A3S14S3bS73S72R5R4R3A3R6A2R7A2S3bVrho0;R7A2A2F_;F_;Fms;FRb;Frho;Fs;FA;").
Proof using .
  clear. intros A s rho Rb ms Hav H. unfold TPA. rewrite (T0_calleeA s rho Rb ms Hav H).
  destruct Hav as [Hw _]. unfold call_checkTA in H. apply andb_prop in H as [H _]. apply andb_prop in H as [E24 N24].
  apply sv_eqb_sound in E24. apply Pos.ltb_lt in N24. rewrite rw_call', E24. cbn [eval]. rewrite <- (Hw _ N24). tauto.
Qed.

Lemma T0_agreeA : ltac2:(tb__ "0|0|
S1S3S6eR2Vrho0;R1A3SfS18Sb5SabR3A2S19A3SfS0S89Vrho0;A1S69Q40SdR3SabA2A2A3F_;F_;Frho;Fn;").
Proof using .
  clear. intros n rho [Hw _] Hn. apply Pos.ltb_lt in Hn. unfold T0. change Contract.V_TOP with Iface.V_TOP. rewrite (Hw _ Hn). reflexivity.
Qed.

Lemma T_ok_rw : ltac2:(tb__ "0|1|
S3S0S8bR2R1A2S10SfS0S69Q40SdR3SabA2A2R2A3S10S77S7bZ2M0Z2eA2R2A2S79R2S7bG0Z3fA2A2A2A2F_;FT;Frho;").
Proof using . clear. intros rho T [H R]. split; [exact H | exact R]. Qed.
Lemma pclFA_reT : ltac2:(tb__ "0|1|
S3S3S16S17S0S0A2M0A1S16S17G0S0A2A1S0SfS0S89R4A1S89R5A1A3S42VCST;R6R4R3R2A5S42VCST;R6R5R4R3A5F_;F_;Fa;FFFc;FFBc;Fr2;Fr1;").
Proof using . clear. intros r1 r2 FBc FFc a ET [H|H]; [left; rewrite ET; exact H | right; exact H]. Qed.
Lemma pclSA_reT : ltac2:(tb__ "0|1|
S3S3S16S17S0S0A2M0A1S16S17G0S0A2A1S0SfS0S89R4A1S89R5A1A3S4bVCST;VXGL;R6R4R3R2A6S4bVCST;VXGL;R6R5R4R3A6F_;F_;Fa;FFFc;FFBc;Fr2;Fr1;").
Proof using . clear. intros r1 r2 FBc FFc a ET (x & Hx & [H|H] & E0); exists x; (split; [exact Hx|]); (split; [|exact E0]); [left; exact (pclFA_reT r1 r2 FBc FFc x ET H) | right; exact H]. Qed.
Lemma keptFA_reT : ltac2:(tb__ "0|2|
S3S3S16S17S0S0A2M0A1S16S17G0S0A2A1S68Q40A1S1eS68Q8A1A1F_;M1G1SfS0S89R5A1S89R6A1A3S14S4aVCST;VXGL;R7R5R4R3R2A7S4aVCST;VXGL;R6R5R4R3R2A7A2F_;Fm1;Fm0;FFFc;FFBc;Fr2;Fr1;").
Proof using .
  clear. intros r1 r2 FBc FFc m0 m1 ET. unfold keptFA.
  assert (EF : forall a, pclFA CST r1 FBc FFc a <-> pclFA CST r2 FBc FFc a) by (intros a; split; apply pclFA_reT; [exact ET | symmetry; exact ET]).
  assert (ES : forall a, pclSA CST XGL r1 FBc FFc a <-> pclSA CST XGL r2 FBc FFc a) by (intros a; split; apply pclSA_reT; [exact ET | symmetry; exact ET]).
  split; intros [K1 K2]; split.
  - intros a Ha Hp. apply K1; [exact Ha|]. destruct Hp as [Hp|[Hp Hd]]; [left; apply EF; exact Hp | right; split; [apply ES; exact Hp | exact Hd]].
  - intros a j Ha Hp. apply K2; [exact Ha|]. apply ES; exact Hp.
  - intros a Ha Hp. apply K1; [exact Ha|]. destruct Hp as [Hp|[Hp Hd]]; [left; apply EF; exact Hp | right; split; [apply ES; exact Hp | exact Hd]].
  - intros a j Ha Hp. apply K2; [exact Ha|]. apply ES; exact Hp.
Qed.
Lemma pclMA_pclFA_callee : ltac2:(tb__ "0|1|
S74S3S16S5A1S76S16S17S0S0A2M0A1S16S17G0S0A2A1S0S6eVNP;Vrho0;R6A3SfS18Sa4VNP;R8A2S19A3S98R5R4R3A3S42VCST;S73S72R9R8R7A3RaA2R6R5R4A5F_;F_;F_;Fa;FFFc;FFBc;Fms;FRb;Frho;Fs;").
Proof using .
  intros s rho Rb ms FBc FFc a Hav H Hp. apply (pclFA_reT rho0); [apply T0_calleeA; assumption | apply pclMA_pclFA; exact Hp].
Qed.

Lemma pclMA_cmaddrA : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17G0S0A2A1S31S0S3cR4R2A2S3aR4R3A2S3bVrho0;R4A2S98R7R6R4A3Sa6VCST;R6S25S0A1R5A4F_;F_;F_;F_;Fa;FAi;FFFc;FFBc;").
Proof using .
  intros FBc FFc Ai a HB HFF HT [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]].
  - left. rewrite (TPA_top rho0 Ai HT). exact H.
  - right; left; exact H.
  - right; right; left. exists b, n. split; [exact (HB _ Hin)|]. split; [discriminate | exact Hr].
  - right; right; right. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | exact Hr].
Qed.

Definition robjs_okF (rho : valuation) (kept : list (sv * sv)) (fr : list (sv * Z * sv)) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S5S0S2cS5R2VR;A3S10S77S1bS0S0ScVrho;R3A2M0A3R2A2S79R2S1dS0S0G0A3A2A2S98S88VFB;Vrho;Vkept;A3S97Vrho;Vfr;A2R3A3F_;F_;Fa;Fo;").
Definition xrs_okF (rho : valuation) (kept : list (sv * sv)) (fr : list (sv * Z * sv)) (X : list (sv * sv)) : Prop := ltac2:(tb__ "0|2|
S17S2S2A2M0S0S2cG0R2VX;A3S10S77S58Vrho;S1bS2S2R3A3A2M1R2A2S79R2S78G1S58Vrho;S1dS2S2R3A3A2A2A2A2S13S98S88VFB;Vrho;Vkept;A3S97Vrho;Vfr;A2R3A3Sb6VXGL;R3A2A2F_;F_;Fa;Fr;").

Lemma fbinA_FBx : ltac2:(tb__ "0|2|
S31S3S16S17S2S2A2M0A1M1G1S3cVFB;R4A2S3fVFB;R5R4S1aG0R3R2A3A4S3cS88VFB;R5R4A3R6A2F_;F_;Fpassed;Fkept;Frho;FAi;").
Proof using .
  intros Ai rho kept passed HB HN bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Hnz & <-)]; [exact (HB _ Hbn)|].
  destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (_ & X & _). exact X.
Qed.

Lemma ffinA_FFx : ltac2:(tb__ "0|0|
S31S3S16S17S17S2S0A2S2A2A1S3aVFF;R3A2S3eVFF;R4R3R2A4S3aS97R4R3A2R5A2F_;F_;Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr HFF [HFR _] f s fl Hin. apply In_FFx in Hin as [Hin|(x & Hx & E0)]; [exact (HFF _ _ _ Hin)|].
  pose proof (proj1 (Forall_forall _ _) HFR x Hx) as (X1 & X2 & X3). injection E0 as E1 E2 E3. subst f s fl.
  change (uval rho (fst (fst x)), fs_frame_size (snd (fst x))) with (frv rho x). split; [exact X1 | exact X2].
Qed.

Lemma fcensus_FFx : ltac2:(tb__ "0|3|
S31S3S16S17S17S2S0A2S2A2M0A1S3S3eVFF;R4R3R2A4S10S52S97R4R3A2R5R2S22G0A1M1A4S2fS17S0S0A2M2S84G0G2S46R2A1G1A4A2A2F_;Frho';Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr rho' [_ [HC _]]. split; [|constructor]. intros x Hx. left. destruct (HC x Hx) as [(fl & Hin)|Hin].
  - exists fl. apply In_FFx. left. exact Hin.
  - apply in_map_iff in Hin as (y & <- & Hy). exists (uval rho (snd y)). apply In_FFx. right. exists y. split; [exact Hy | reflexivity].
Qed.

Definition bdL_ok (s : wsub) (nc : positive) (L : axst) (bd : list bitem) : bool := ltac2:(tb__ "0|0|
S60S90VNPc;Vs;Vnc;S29VL;A1A4Vbd;A2").
Definition xr_post_ok (L : axst) (tvL : list (sv * sv)) (r : sv * sv) : bool := ltac2:(tb__ "0|6|
S18S18L_;M0Sa7VtvL;S25S23A1Vr;A3S19G0Sb9S6S29VL;A1A1M1SaSeSc3S1bS2S2Vr;A3M2S1dS2S2Vr;A3M3A3S9S7bZ2M4Z2fA2A1M5A2A2G0Sb9G1SaG3S9S7bG4Z28A2A1A2A2Sb9G1SaG2G5A2A2S24X18x2S24X18x2X18x2").

Definition amL_ok (s : wsub) (nc : positive) (L : axst) (am : amode) : bool := ltac2:(tb__ "0|0|
S2dS2S71S90VNPc;Vs;Vnc;S29VL;A1A4A1S50Vam;A1A3").
Definition pd_okA (s : wsub) (nc : positive) (d : pdescA) : bool := ltac2:(tb__ "0|6|
S21S21S21S21S21S21S95VNPc;Vs;Vnc;S29S1bS28S35Vd;A3M0A1M1S36S1dS28S35Vd;A3M2A1M3A5S92S29VPreC;A1G1G3A3A2S16S17S17S2S0A2S2A2M4A1M5S18Lx;S38G2A1S19G4G5S24Ll;Lp;X16x2A2Sa1Vs;Vnc;G0S37G2A1A4A2S2dS17S2S2A2Sa3G0G3A2S2aG0A1A3A2SbS2bG0A1S9Sc1A1A2A2Sa0Vs;Vnc;G0S3dG2A1A4A2").

Definition xr_eqb (r r' : sv * sv) : bool := ltac2:(tb__ "0|0|
S21SbS1bS2S2Vr;A3S1bS2S2Vr';A3A2SbS1dS2S2Vr;A3S1dS2S2Vr';A3A2A2").
Definition xrs_inclb (Xk X : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S2dS17S2S2A2M0G0S30G0Sa2R1A1VX;A3Lr;VXk;A3").
Lemma xrs_inclb_sound : ltac2:(tb__ "0|2|
S16S17S2S2A2M0A1M1G1SfS18S9aR2R1A2S19A3G0S2cG0R1R4A3S2cG0R2R4A3F_;Fr;F_;FX;FXk;").
Proof using .
  intros Xk X H r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as EX. apply existsb_exists in EX as (r' & Hr' & Heq).
  unfold xr_eqb in Heq. apply andb_prop in Heq as [A B]. apply sv_eqb_sound in A. apply sv_eqb_sound in B.
  destruct r, r'; cbn in A, B; subst; exact Hr'.
Qed.
Definition T_afterA3 (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) (Xk : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
Sc5S6S29VCl;A1A1Sb7Vs;VPre;VL;VCl;VR;VXk;A6A2").

Lemma cont_smatchA3 : ltac2:(tb__ "0|3|
S28S28S28S74S16S5A1M0S16S17S2S2A2A1S3S3S16S68Q40A1A1M1G1S16S57A1M2S76S56S17G2Sb2A2SfS1eG0A1S7eReRdRbA3S1fG0RaA2A3S55Vsegs;R9R7RfS1cG2Sb2R5Sb3R4R3A2A4A5S6eS4S29R10A1A1RaR9A3S55Vsegs;RaR8Sb7ReR10RfR11RdRcA6R4A5S55Vsegs;S94RbS93RcRbReA3A2R9S99R11R12RfReR10RdA6R5A5F_;F_;F_;F_;Fw;Fmd;Fms;Ftr;FtpL;Ftp;Frho';Frho;FXk;FR;Fs;FL;FPre;FCl;").
Proof using .
  clear HnextPre HfrC HbaseC. intros Cl Pre L s R Xk rho rho' tp tpL tr ms md w He Hsm Hag' Hsm'.
  unfold T_afterA3. apply smatchA_add_facts.
  - apply smatchA_patch; [exact Hsm'|]. intros a Hout. unfold patchf.
    destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|reflexivity]. exfalso.
    destruct Hi as (oR & HinR & Hr).
    unfold import_postA3, import_post in Hout. cbn [ax_S ss_objs set_objs subst_state] in Hout.
    apply outside_all_app_iff in Hout as [_ Hout].
    pose proof (proj1 (Forall_forall _ _) Hout oR HinR) as X. cbv beta zeta in X.
    rewrite (R_ranges_agreeA segs Cl Pre s R rho rho' tp tr ms md He Hsm Hag' oR HinR) in X. lia.
  - apply Forall_forall. intros p Hp. apply holds_patch.
    pose proof (proj1 Hsm) as HsmS.
    apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' p Hag').
    + exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp).
    + eapply (proj1 (Forall_forall _ _) (smatch_facts segs _ _ _ HsmS)). exact Hp.
  - apply forallb_forall. intros p Hp. pose proof (proj1 Hsm) as HsmS.
    eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp)].
    unfold import_postA3, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

Lemma live_not_pclMA : ltac2:(tb__ "0|1|
S31S3S16S68Q40A1A1S56S16S17S0S0A2M0A1S16S17G0S0A2A1S0S0S0VAInv;R9R8R7R6A4S3cR6RaA2S3aR6RbA2S3bVrho0;RcA2S2cG0S1cS0S0R7R6A4S34RdA1A3S12S2cG0S1cS0S0R8R7A4RaA3A1S10S77R9R7A2S79R7S78R9R8A2A2A2S98RcRbR8A3S15F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fn';Fp;FFFc;FFBc;Fmd1;Ftp1;Frho1;FA;").
Proof using ALA HCST.
  clear HnextPre HfrC HbaseC. intros A rho1 tp1 md1 FBc FFc p n' a HM HB' HFF' HTA HinN HninF Ha Hc.
  destruct (law_blocks _ _ _ ALA A _ _ _ HM) as (HPD' & HBl' & HFr').
  destruct (HBl' p n' HinN) as (G1 & G2 & G3 & G4 & G5). top_rng G4. rewrite (TPA_top rho0 A HTA) in G4.
  destruct Hc as [Hc|[Hc|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]].
  - lia.
  - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG in Hc. unfold IMG_HI in G5. lia.
  - pose proof (HB' _ Hb) as HbA'.
    assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
    apply In_nth_error in HbA' as [i Hi]. apply In_nth_error in HinN as [j Hj].
    assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; congruence).
    assert (Hi' : nth_error (aa_live A ++ aa_frames A) i = Some (b, m)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
    assert (Hj' : nth_error (aa_live A ++ aa_frames A) j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
    pose proof (pd_elems _ i j _ _ HPD' Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
  - destruct (HFF' _ _ _ Hf) as [HfA' _].
    apply In_nth_error in HfA' as [k Hkk]. apply In_nth_error in HinN as [j Hj].
    assert (Hj' : nth_error (aa_live A ++ aa_frames A) j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
    assert (Hk' : nth_error (aa_live A ++ aa_frames A) (length (aa_live A) + k) = Some (f, sz)).
    { rewrite nth_error_app2 by lia. replace (length (aa_live A) + k - length (aa_live A))%nat with k by lia. exact Hkk. }
    assert (Hjl : (j < length (aa_live A))%nat) by (apply nth_error_Some; congruence).
    pose proof (pd_elems _ j _ _ _ HPD' Hj' Hk' ltac:(lia)) as D. cbn [fst snd] in D.
    destruct (HFr' f sz (proj1 (HFF' _ _ _ Hf))) as (_ & _ & G64 & _). lia.
Qed.

Lemma untracked_kept_FBx : ltac2:(tb__ "0|4|
S3S16S17S2S2A2M0A1M1G1S0S0S4cR5S1aG0R4R3A3S1cS0S0R2R1A4A3S12S2cS17S0S0A2M2S1cS0S0R3R2A4VFB;A3A1S10S12S2cG2S1cS0S0R4R3A4M3S88VFB;R7R6A3A3A1S4dS84G0G2S91R7A1R5A4G3A2A2F_;F_;Fn;Fb;Fpassed;Fkept;Frho;").
Proof using .
  intros rho kept passed b n Hut0 Hnfb. pose proof (proj1 (untracked_tv rho (kept ++ passed) (b, n)) Hut0) as Hut. split.
  - intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (Hnfb Hin)|].
    exact (Hut t ltac:(apply in_or_app; left; exact Ht) Hnz Heq).
  - intros v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht). apply Hut; [apply in_or_app; right; exact Ht | exact Hnz].
Qed.

Lemma untracked_FBx_kept : ltac2:(tb__ "0|3|
S3S16S17S2S2A2M0A1M1G1S17S0S0A2M2S12S2cG2R1S88VFB;R4R3A3A3A1S4dS84G0G2S91R5A1R3A4R2A2S10S12S2cG2R3VFB;A3A1S4cR6S1aG0R5R4A3R3A3A2F_;F_;Fbn;Fpassed;Fkept;Frho;").
Proof using .
  intros rho kept passed bn Hnx Hup. split; [intros Hin; apply Hnx; apply In_FBx; left; exact Hin|].
  apply (proj2 (untracked_tv rho (kept ++ passed) bn)). intros t Ht Hnz Heq. apply in_app_or in Ht as [Ht|Ht].
  - apply Hnx. apply In_FBx. right. exists t. auto.
  - apply (Hup (tvv rho t)); [apply in_map; exact Ht | exact Hnz | exact Heq].
Qed.

Section CallTC.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S54S28S3S16S68Q40A1A1S6aS85S7S8R3A1S6S29R4A1A1A3VTR;S53Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S6aS6aS6aS6dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S54S54S28S28S74S16S5A1M0S16S17S28S7dA2M1A1S16S17S2S2A2M2A1S6aS3S16S68Q40A1A1M3G2S2cG2R1R5A3S2cG2R2S2aRbA1A3F_;Fr;SfS1eG0A1S7eRaR9R8A3S1fG0R7A2A3SfS18S7fRbRaR9R8S84G1S28S1bS28S7dA2R7A4A5S19A3S3G3VTR;S53Vsegs;RfRdR2R1A5S80Vsegs;S4S29RdA1A1R2R1RaA5A2Ftp1;Frho1;S16S57A1M4S76S56S55Vsegs;R9R8R10S1cG4Sb2R3Sb3R2R1A2A4A5R13RaR9R4R2A4R13S73S72RbRfS83R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S28S7dG4S76S56S3G3G4S76S56S2cG1S1cS28S7dRaR9A4R14A3S55Vsegs;R12R11R19S1cG4Sb2R9Sb3R8R7A2A4A5R1cR13R12RaR8A4S6eS4S29R1aA1A1S73S72R14R18S83R9R13RaA3A3R19A2R8A3S55Vsegs;R9R8ReS1cG4Sb2R7Sb3R6R5A2A4A5ReS73S72R16R1aS83RbR15RcA3A3R1bA2R15RaR9R8R6A6S10Sb8R17S83RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S70R18S83RdR17ReA3R1cR1dS29R1eA1S29R1fA1S29R11A1R1RcA9VTR;S53Vsegs;S82R11S73S72R19R1dS83ReR18RfA3A3R1eA2R18RdRcA5Sb7R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S53Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17G0S0A2A1S5eS3S16S68Q40A1A1S5bVdC;R3A2VTR;S53Vsegs;S43VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S80Vsegs;VNPc;R3R2S9bR6R5R4A3A5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis Hdd : ltac2:(tb__ "0|1|
SfS18S21S7aZ1M0VdC;A2S7aS78VdC;G0A2VdF;A2A2S19A3").

Theorem client_callT : ltac2:(tb__ "0|9|
S28S74S16S5A1M0S16S17S2S2A2M1A1M2S3S16S68Q40A1A1M3G2G2S16S17S17S2S0A2S2A2A1S16S59A1M4G4S45S6aSfS18S9aRaS2aRdA1A2S19A3SfS1eG0A1S7eReVPreC;RdA3S1fG0RcA2A3SfS18S7fRfVPreC;ReRdS84S17S28S35A2S28S1bS28S35A2VPD;A4A5S19A3SfS18Sa4VNP;RfA2S19A3SfS18S6fR10VNPc;A2S19A3SfS18Sb4VNP;S4S29R12A1A1A2S19A3SfS18S41S4S29R13A1A1S39S1aG1RdRcA3RbRaR8A4A2S19A3SfS18S5cS4S29R14A1A1RaA2S19A3SfS18S8fR14ReS36VndC;A1A3S19A3SfS18S44S40R15S3dVndC;A1A2RbA2S19A3VpayA;S6S29R17A1A1S9Z0M5A1G5ReS1aS59S5aR16S37VndC;A1A2RdA3A5SfS18S2dS96S9cR17S4S29R18A1A1A2VPD;A3S19A3S31S76S85S7S8R17A1S6S29R1bA1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R19A3S3cVFB;R5A2S3aVFF;R6A2S3fVFB;R7R1cS1aG1R1aR19A3A4S8cR1dS1aG1R1bR1aA3A2S8dR1eS1aG1R1cR1bA3A2S3eVFF;RaR1fR1bA4S11S3S3S11G3G3S11S56S56VAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RcA2S8bR22S33S32RdA1A1A2S10S9dR23R21R1fR25A4S10S9eR23R21R1fR24A4VP0c;S88VFB;R23R21A3S97R23R1fA2S73S72R23R25RdA3R26A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S96S3G3S2cS96R3VPD;A3S6eS4S29R1eA1A1R1aR3A3VTR;S53Vsegs;VJA;S39S1aG1R19S8eS81R1eVPreC;S1bS28S35R5A3M6R1fA4M7S36S1dS28S35R5A3M8A1A2A3R17S1aS59S5aG7S37G8A1A2R15A3S40G7S3dG8A1A2A4A1S99VPreC;R1fR1eR1dG6R1cA6R4R3A5R13A2F_;F_;Ftp';Frho';Fd;VTR;S53Vsegs;VJA;S39S1aG1R15R14A3R13R12R10A4A1R1bR17R16A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMT Hdd TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R Xk rho tp kept passed fr bd brest am Q HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass Ham HPAY Hpd HIN Tcont.
  pose proof (xrs_inclb_sound _ _ HXk) as HXk'. apply am_eqb_sound in Ham.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA (kept ++ passed) fr bd am))). intros Ai.
  apply (TR_ex Z (JAi (NDA (kept ++ passed) fr bd am) Ai)). intros kc.
  pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbt, Hbf, Hbb, Hba. clear Hnb.

  assert (PASS : forall ms, map (tvv (rho_sub (rho_absorb rho R ms) s)) (nd_tv ndC) = map (tvv rho) passed
                 /\ forall k t t', nth_error passed k = Some t -> nth_error (nd_tv ndC) k = Some t' -> (tnz (rho_sub (rho_absorb rho R ms) s) t' <-> tnz rho t)).
  { intros ms. destruct (tv_sub_eqb_sound s passed (nd_tv ndC) (rho_absorb rho R ms) Hpass) as [M1 M2].
    assert (EA : forall l, map (tvv (rho_absorb rho R ms)) l = map (tvv rho) l).
    { intros l. apply map_ext. intros t. unfold tvv. rewrite !eval_absorb. reflexivity. }
    split; [rewrite M1; apply EA|]. intros k t t' Ht Ht'. rewrite (M2 k t t' Ht Ht'). unfold tnz. rewrite eval_absorb. tauto. }
  assert (EVA : forall ms e, eval (rho_sub (rho_absorb rho R ms) s) e = eval (rho_sub rho s) e).
  { intros ms e. rewrite <- !eval_subst. apply eval_absorb. }
  eapply (TR_callP (JAi (NDA (kept ++ passed) fr bd am) Ai kc) (JA_pre AInv CST XGL Kc (P0c (FBx FB rho kept) (FFx rho fr)) (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept) PAc ndC)
            Cl PreC s R (PostsC (FBx FB rho kept) (FFx rho fr) (BXx rho brest kept)) Xk Q rho tp HXk' He).
  - unfold PostsC. rewrite map_map. cbn [fst]. exact Hchk.
  - intros rho1 tp1. rewrite HnextPre. apply SUMT. apply (BXx_nonneg dC rho brest kept Hdd).
    pose proof (nd_below_len _ _ Hnb0) as HL0. cbn [nd_tv] in HL0. rewrite length_app in HL0. lia.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & HPc).
    destruct (PASS (vms md tp ms)) as [PM PZ].
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (RNOTSH0 : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }

    assert (EAM : am_eval (rho_sub (rho_absorb rho R (vms md tp ms)) s) (nd_am ndC) = am_eval rho am).
    { rewrite <- am_eval_subst, Ham. apply am_eval_exteq. intros e _. apply eval_absorb. }
    destruct (XAz_transport FB (FBx FB rho kept) (am_eval rho am) Ai Ai (rm rho) (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s)) (tvals rho (kept ++ passed)) (map (tvv rho) passed) kc HXA) as [XEXP PEXP].
    { intros b n H1 H2 H3. split; [exact H1|]. exact (untracked_kept_FBx rho kept passed b n H3 H2). }
    { intros b n z H1 H2 H3 Hz. apply rm_absorb_out. intros Hin. destruct Hin as (o & Ho & Hr).
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      eapply (live_not_pclMA Ai rho tp md (FBx FB rho kept) (FFx rho fr) b n z HM FBX FFX HT H1 (proj1 (untracked_kept_FBx rho kept passed b n H3 H2))); [exact Hz|].
      apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
    { intros b n a H1 H2 H3 Ha.
      destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl0 & _). destruct (HBl0 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
      assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
      split.
      - intros _. apply rm_absorb_out. intros Hin. apply (RNOTSH0 _ Hin). rewrite shadow_addr_Sh, Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
      - intros j Hj Hdef. rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH0 _ Hin).
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
    {
      intros bn H1 _ H3 H4. destruct (untracked_FBx_kept rho kept passed bn H3 H4) as [G1 G2]. split; [exact H1 | split; [exact G1 | exact G2]]. }
    split; [exact Hk|]. exists Ai, kc.
    split; [eapply AInv_absorb; eauto|].
    split; [exact (proj2 (TPA_calleeA Ai s rho R (vms md tp ms) Hav Htp) HT)|].
    split; [exact FBX|]. split; [exact FFX|].
    split; [split; [|split]| split; [rewrite HfrC; split; [constructor | exact (fcensus_FFx Ai rho fr _ HFR)] | split; [apply keptFA_refl | split; [exact HPc|split; [unfold XA, tvals; rewrite EAM, PM; exact XEXP|split; [|split; [exact (HPAc0 _ HPA) | split; [exact HCKi|

      unfold capN in *; cbn [nd_tv] in HCNi; rewrite cntS_app in HCNi; unfold BXx; cbn [bxN]; rewrite (cntS_map _ _ _ _ PM); lia]]]]]]]].
    +
      unfold tvinA. apply Forall_forall. intros tc Htc Hnz.
      destruct (In_nth_error _ _ Htc) as [k Hk'].
      assert (exists tq, nth_error passed k = Some tq) as [tq Htq].
      { pose proof (Forall2_map_eq _ _ _ _ PM) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
        exfalso. apply nth_error_None in En. assert (k < length (nd_tv ndC))%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k tq tc PM Htq Hk'). apply (proj1 (PZ k tq tc Htq Hk')) in Hnz.
      pose proof (nth_error_In _ _ Htq) as HinP.
      destruct (proj1 (Forall_forall _ _) HN tq ltac:(apply in_or_app; right; exact HinP) Hnz) as (X0 & X1 & X2).
      split; [exact X0|]. split; [exact X1|]. intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnzt & Heq)]; [exact (X2 Hin)|].
      exact (tvd_app_cross rho kept passed t tq HD Ht HinP Hnzt Hnz Heq).
    + eapply tvd_map; [exact PM | exact PZ | exact (tvd_app_r rho kept passed HD)].
    + eapply tvz_map; [exact PM | exact PZ |]. unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. exact Ht.
    +
      destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [B1 [Wr0 Nr0]].
      pose proof (bsum_nonneg brest rho Wr0 Nr0) as [BN1 BN2].
      assert (EP : apot (nd_am ndC) (rho_sub (rho_absorb rho R (vms md tp ms)) s) = apot am rho) by (unfold apot; rewrite EAM; exact PEXP).
      rewrite EP. unfold BXx, bxa, bxV, bxK. cbn [bx2]. rewrite (Z.max_r 0 (bsumV brest rho)) by lia. rewrite (Z.max_r 0 (bsumK brest rho)) by lia.
      unfold BUD in B1 |- *. rewrite bsumV_subst, bsumK_subst, bd_wpos_subst in B1. unfold bxa in B1. cbn [fst snd] in B1 |- *.
      assert (AG : forall b, bsumV b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumV b (rho_sub rho s)
                            /\ bsumK b (rho_sub (rho_absorb rho R (vms md tp ms)) s) = bsumK b (rho_sub rho s)).
      { intros b. apply bsum_eval_ext. exact (EVA (vms md tp ms)). }
      destruct (AG (nd_bd ndC)) as [-> ->]. destruct B1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
      split; [|split; lia].
      apply bd_nn_subst in Q7. eapply bd_nn_eval_ext; [|exact Q7]. intros e. symmetry. apply EVA.
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
    unfold PostsC in HinL. apply in_map_iff in HinL as ([Ld ndL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
    destruct (HIN Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & HPc).
    pose proof (proj1 (forallb_forall _ _) Hpd _ Hd) as Hpdd. unfold pd_okA in Hpdd. cbn [fst snd] in Hpdd.
    apply andb_prop in Hpdd as [Hpdd HamL].
    apply andb_prop in Hpdd as [Hpdd HbaseL]. apply sv_eqb_sound in HbaseL.
    apply andb_prop in Hpdd as [Hpdd HpostX]. apply andb_prop in Hpdd as [Hpdd HbdL]. apply andb_prop in Hpdd as [Hpdd HfrL]. apply andb_prop in Hpdd as [HtvL Hnew].
    destruct HJL as (HkL & A' & kcL & HM' & HT' & HB' & HFF' & (HNc & HDc & HZc) & HFRc & [HKc1 HKc2] & HP0c & HXAc & HBUc).
    pose proof (fbinA_FBx Ai rho kept passed HB HN) as FBX. pose proof (ffinA_FFx Ai rho fr HFF HFR) as FFX.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [exact FBX | exact FFX | exact HT | exact (HRok o a Ho Hr)]. }
    assert (HRokA' : forall a, in_ranges rho R a -> cmaddrA CST A' None (bv_unsigned a)).
    { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB' | exact HFF' | exact (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT') | exact (HRok o _ Ho Hr)]. }
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He) as HbC.
    destruct (law_blocks _ _ _ ALA A' _ _ _ HM') as (HPD' & HBl' & HFr').
    assert (XR47 : forall r a, In r Xk -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> 0 <= a < 2 ^ 47).
    { intros r a Hr Ha. destruct (HX r a Hr Ha) as [Hp|Hg]; [|apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia].
      exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md a HM FBX FFX HT (pclMA_pclFA _ _ _ Hp)). }

    assert (NEWOBJ : forall o', In o' (new_objs (ax_S PreC) (ax_S Ld)) ->
              exists p n', fst (obj_range rhoL o') = p /\ (snd (obj_range rhoL o') <= p \/ (snd (obj_range rhoL o') = p + n'
                           /\ In (p, n') (aa_live A') /\ ~ In (p, n') (FBx FB rho kept) /\ 0 < n'))).
    { intros o' Hin'.
      unfold new_objs_tv in Hnew. pose proof (proj1 (forallb_forall _ _) Hnew o' Hin') as Ho'.
      apply existsb_exists in Ho' as ([vd vsz] & Hvn & Heqs). cbn [fst snd] in Heqs.
      apply andb_prop in Heqs as [Heqs E3]. apply andb_prop in Heqs as [E1 E2].
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      destruct o' as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in E1, E2, E3. subst ob olo ohi.
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
      set (p := bv_unsigned (eval rhoL vd)). set (n' := bv_unsigned (eval rhoL vsz)).
      exists p, n'. split; [lia|].
      destruct (Z.eq_dec n' 0) as [Hz|Hnz0]; [left; rewrite Hz; cbn; lia|].
      assert (Hnz : tnz rhoL (vd, vsz)).
      { intros Hz. pose proof (proj1 (Forall_forall _ _) HZc _ Hvn (fun H => H Hz)) as Z0. unfold tvv in Z0. cbn [fst snd] in Z0. fold n' in Z0. lia. }
      destruct (proj1 (Forall_forall _ _) HNc _ Hvn Hnz) as (Npos & HinN & HninF). unfold tvv in HinN, HninF, Npos. cbn [fst snd] in HinN, HninF, Npos.
      fold p n' in HinN. fold p n' in HninF. fold n' in Npos.
      destruct (HBl' p n' HinN) as (_ & _ & _ & G4 & _). top_rng G4.
      right. pose proof (bv_urange (eval rhoL vsz)) as Rn. fold n' in Rn. pose proof (bv_urange (eval rhoL vd)) as Rp. fold p in Rp.
      destruct (Zsigned_spec n') as [[X8 X]|[X8 X]]; rewrite X; [|exfalso; lia]. repeat split; auto; lia. }

    assert (NEWFREE : forall p n' a, In (p, n') (aa_live A') -> ~ In (p, n') (FBx FB rho kept) -> 0 < n' -> p <= a < p + n' ->
              pclMA (FBx FB rho kept) (FFx rho fr) a -> False).
    { intros p n' a HinN HninF Hn' Ha Hc.
      destruct (HBl' p n' HinN) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      rewrite (TPA_top rho0 A' (proj1 (TPA_calleeA A' s rho R (vms md tp ms) Hav Htp) HT')) in G4.
      destruct Hc as [Hc|[Hc|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]].
      - lia.
      - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
      - pose proof (HB' _ Hb) as HbA'.
        assert (Hne : (b, m) <> (p, n')) by (intros Heq; apply HninF; rewrite <- Heq; exact Hb).
        apply In_nth_error in HbA' as [i Hi]. apply In_nth_error in HinN as [j Hj].
        assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; congruence).
        assert (Hi' : nth_error (aa_live A' ++ aa_frames A') i = Some (b, m)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        pose proof (pd_elems _ i j _ _ HPD' Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
      - destruct (HFF' _ _ _ Hf) as [HfA' _].
        apply In_nth_error in HfA' as [k Hkk]. apply In_nth_error in HinN as [j Hj].
        assert (Hj' : nth_error (aa_live A' ++ aa_frames A') j = Some (p, n')) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
        assert (Hk' : nth_error (aa_live A' ++ aa_frames A') (length (aa_live A') + k) = Some (f, sz)).
        { rewrite nth_error_app2 by lia. replace (length (aa_live A') + k - length (aa_live A'))%nat with k by lia. exact Hkk. }
        assert (Hjl : (j < length (aa_live A'))%nat) by (apply nth_error_Some; congruence).
        pose proof (pd_elems _ j _ _ _ HPD' Hj' Hk' ltac:(lia)) as D. cbn [fst snd] in D.
        destruct (HFr' f sz (proj1 (HFF' _ _ _ Hf))) as (_ & _ & G64 & _). lia. }
    assert (RNOTSH : forall a, in_ranges rho R a -> ~ is_shadowZ (bv_unsigned a)).
    { intros a Hin. eapply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None _ rho tp md HM). destruct Hin as (o & Ho & Hr). exact (HRokA o _ Ho Hr). }
    split.
    +
      split; [split|split].
      *   intros a Hina. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        apply HKc1; [apply bv_urange |]. left. apply (pclMA_pclFA_callee s rho R (vms md tp ms)); [exact Hav | exact Htp |]. destruct Hina as (o & Ho & Hr). exact (HRok o _ Ho Hr).
      *
        intros o' oR Hin' HinR. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]).
        -- unfold ranges_disjoint. rewrite Elo. cbn [fst snd]. destruct (obj_range rho oR); cbn [fst snd]. lia.
        -- destruct (obj_range rhoL o') as [lo hi] eqn:Eo. cbn [fst snd] in Elo, Ehi. subst lo hi.
           destruct (obj_range rho oR) as [lo2 hi2] eqn:HR2.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE p n' a HinN HninF Hn' Ha1).
           apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      *
        intros r a j oR Hr Ha Hj HoR Hrng.
        pose proof (proj1 (forallb_forall _ _) HpostX r Hr) as HPX. unfold xr_post_ok in HPX.
        assert (Ha47 : 0 <= a < 2 ^ 47).
        { apply lazy_orb_prop in HPX as [HPX|HPX].
          - unfold xr_tracked in HPX. destruct (robj_tracked_sound (nd_tv ndL) None _ HPX) as (jj & t & Hjt & _ & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
            pose proof (nth_error_In _ _ Hjt) as Hint.
            assert (Er : tvv rhoL t = (bv_unsigned (eval rhoL (fst r)), bv_unsigned (eval rhoL (snd r)))) by (unfold tvv; rewrite Hb, Hh; reflexivity).
            destruct (Z.eq_dec (bv_unsigned (eval rhoL (fst r))) 0) as [Hz0|Hnz0].
            { exfalso. pose proof (proj1 (Forall_forall _ _) HZc t Hint) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
              unfold tnz in Z0. rewrite <- Hb in Z0. specialize (Z0 ltac:(lia)). lia. }
            assert (Hnz : tnz rhoL t) by (unfold tnz; rewrite <- Hb; exact Hnz0).
            destruct (proj1 (Forall_forall _ _) HNc t Hint Hnz) as (Tpos & Tin & _). rewrite Er in Tin.
            destruct (HBl' _ _ Tin) as (_ & _ & G3 & G4 & _). top_rng G4. lia.
          - apply lazy_andb_prop in HPX as [P1 P2]. apply lazy_andb_prop in P2 as [P2 P3].
            pose proof (smatchA_facts segs _ _ _ _ HsmL) as HFL.
            pose proof (prove_sprop_sound rhoL _ _ HFL P1) as Q1. pose proof (prove_sprop_sound rhoL _ _ HFL P2) as Q2.
            pose proof (prove_sprop_sound rhoL _ _ HFL P3) as Q3. cbn [holds] in Q1, Q2, Q3.
            rewrite U_add, !U_lit in Q1. rewrite U_lit in Q2. rewrite U_lit in Q3. unfold M64v in Q1, Q2, Q3.
            change (2 ^ 40 mod 18446744073709551616) with (2 ^ 40) in Q2. change (2 ^ 47 mod 18446744073709551616) with (2 ^ 47) in Q1, Q3.
            pose proof (bv_urange (eval rhoL (fst r))). pose proof (bv_urange (eval rhoL (snd r))).
            rewrite Z.mod_small in Q1 by lia. unfold uval in Ha. lia. }
        apply (RNOTSH (word_byte (bv_unsigned (eval rhoL (ax_base Ld)) + a / 8) j)).
        -- exists oR. split; [exact HoR | exact Hrng].
        --
           assert (EbL : bv_unsigned (eval rhoL (ax_base Ld)) = SHADOW_OFF) by (rewrite HbaseL; cbn [eval]; rewrite lit_unsigned; reflexivity).
           rewrite EbL. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Ha47 | exact Hj].
      *
        intros r a Hr Ha. rewrite (HbC HbaseC). cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
        pose proof (XR47 r a Hr Ha) as Ha47. pose proof (Sh_is_shadow a Ha47) as HSa.
        assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
        assert (PS : pclSA CST XGL (rho_sub (rho_absorb rho R (vms md tp ms)) s) (FBx FB rho kept) (FFx rho fr) (Sh a)).
        { exists a. split; [lia|]. split; [|reflexivity]. destruct (HX r a Hr Ha) as [Hp|Hg]; [left; apply pclMA_pclFA_callee; [exact Hav | exact Htp | exact Hp] | right; exact Hg]. }
        split; [|split; [intros jj Hjj | intros jj o' Hjj]].
        -- assert (NRS : ~ in_ranges rho R (Z_to_bv 64 (Sh a))).
           { intros Hin. apply (RNOTSH _ Hin). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia]. }
           rewrite shadow_addr_Sh. rewrite (HKc1 (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
           ++ apply rm_absorb_out. exact NRS.
           ++ right. split; [exact PS|]. rewrite rm_absorb_out by exact NRS. rewrite <- shadow_addr_Sh.
              exact (smatchA_X_defined segs rho tp Cl _ r a Hsm (HbC HbaseC) (HXk' r Hr) Ha).
        -- intros Hdef. rewrite <- EW in Hdef |- *.
           apply (HKc2 (Sh a) jj); [unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia | exact PS | exact Hjj |].
           rewrite rm_absorb_out; [exact Hdef|]. intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [exact HSa | exact Hjj].
        -- intros Hin' Hrng. destruct (NEWOBJ o' Hin') as (p & n' & Elo & [Hemp|(Ehi & HinN & HninF & Hn')]); [lia|].
           pose proof (word_byte_of_shadow (Sh a) jj HSa Hjj) as WS. rewrite EW in WS.

           eapply (client_not_shadow segs AInv CST ALA HCST A'); [exact HM' | | exact WS]. left; right; left. exists p, n'. split; [exact HinN | lia].
    +
      intros rho' Hlink.
      assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by (destruct Hlink as (A & _); exact A).
      set (rho'' := rho_patch rho' (patchf rho rho' R)).
      assert (Hag'' : agree_vals (ss_next (ax_S Cl)) rho rho'') by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      eapply TR_pre; [ | apply (Tcont (Ld, ndL) rho'' tpL Hd Hag'')].
      intros w [Hsm' HJ']. cbn [J_ofPA fst snd] in HJ' |- *.
      destruct HJ' as (Hk2 & A2 & kc2 & HM2 & HT2 & HB2 & HFF2 & (HN2 & HD2 & HZ2) & HFR2 & [HK21 HK22] & _ & HXA2 & HBU2 & HPAc2 & HCK2 & HCN2).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      assert (Hnbk : tv_below (ss_next (ax_S Cl)) kept = true).
      { unfold tv_below in *. rewrite forallb_app in Hbt. apply andb_prop in Hbt as [A _]. exact A. }
      set (isub := import_subA s PreC Ld Cl) in *.
      pose proof Hlink as (L1 & L2 & L3 & L4).
      assert (EI : forall e, sv_vars_all (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) e = true -> eval rho'' (sv_subst isub e) = eval rhoL e).
      { intros e Hev. subst rho''. rewrite eval_patch, eval_subst. symmetry.
        apply (eval_agree_vars (ivar_ok NPc s (ss_next (ax_S Cl)) (ax_S Ld)) rhoL (rho_sub rho' isub) e); [| |exact Hev].
        - intros u Hu. unfold ivar_ok in Hu. apply andb_prop in Hu as [Hu1 Hu2]. apply Pos.ltb_lt in Hu2.
          cbn [rho_sub rw]. subst isub. unfold import_subA. apply L4; [rewrite HnextPre; exact Hu1 | lia].
        - intros l. cbn [rho_sub rl]. rewrite <- (proj2 L3 l). cbn [rho_sub rho_absorb rl]. exact (proj2 L1 l). }
      assert (IM : map (tvv rho'') (import_tv isub (nd_tv ndL)) = map (tvv rhoL) (nd_tv ndL)
                   /\ forall k t t', nth_error (nd_tv ndL) k = Some t -> nth_error (import_tv isub (nd_tv ndL)) k = Some t' -> (tnz rho'' t' <-> tnz rhoL t)).
      { unfold tvL_ok in HtvL. revert HtvL. clear - EI. generalize (nd_tv ndL) as tvL. intros tvL HtvL.
        induction tvL as [|t r IH]; [split; [reflexivity | intros [|k] ? ? H; discriminate]|].
        cbn in HtvL. apply andb_prop in HtvL as [Ht Hr]. apply andb_prop in Ht as [Ht1 Ht2]. destruct (IH Hr) as [IH1 IH2].
        split.
        - cbn [map import_tv]. f_equal; [|exact IH1]. unfold tvv. cbn [fst snd]. rewrite (EI _ Ht1), (EI _ Ht2). reflexivity.
        - intros [|k] a b Ha Hb; cbn in Ha, Hb; [|exact (IH2 k a b Ha Hb)].
          injection Ha as <-. injection Hb as <-. unfold tnz. cbn [fst]. rewrite (EI _ Ht1). tauto. }
      destruct IM as [IM1 IM2].
      assert (IB : bsumV (bd_subst isub (nd_bd ndL)) rho'' = bsumV (nd_bd ndL) rhoL /\ bsumK (bd_subst isub (nd_bd ndL)) rho'' = bsumK (nd_bd ndL) rhoL).
      { unfold bdL_ok in HbdL. exact (bsum_vars_ext _ _ _ _ _ HbdL EI). }
      destruct IB as [IB1 IB2].
      split; [exact (cont_smatchA3 Cl PreC _ s R Xk rho rho' tp tpL tr ms md _ He Hsm Hag' Hsm')|].
      exists A2, kc2.
      pose proof (proj1 (TPA_calleeA A2 s rho R (vms md tp ms) Hav Htp) HT2) as HT2'.
      assert (HsubR : forall a, in_ranges rho R a -> cmaddrA CST A2 None (bv_unsigned a)).
      { intros a (o & Ho & Hr). eapply pclMA_cmaddrA; [exact HB2 | exact HFF2 | exact HT2' | exact (HRok o _ Ho Hr)]. }

      assert (EAM2 : am_eval rho'' (am_subst isub (nd_am ndL)) = am_eval rhoL (nd_am ndL)).
      { rewrite am_subst_as_map. apply (am_eval_ext (sv_subst isub)). intros e Hine. apply EI. unfold amL_ok in HamL. exact (proj1 (forallb_forall _ _) HamL e Hine). }
      assert (TVK : tvals rho'' kept = tvals rho kept).
      { unfold tvals. apply map_ext_in. intros t Ht. apply (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag''). exact (proj1 (forallb_forall _ _) Hnbk t Ht). }
      destruct (XAz_transport (FBx FB rho kept) FB (am_eval rhoL (nd_am ndL)) A2 A2 (rm rhoL) (rm rho'') (tvals rhoL (nd_tv ndL)) (tvals rho kept ++ tvals rhoL (nd_tv ndL)) kc2 HXA2) as [XIMP PIMP].
      { intros b n H1 H2 H3. split; [exact H1|]. split; [intros Hin; apply H2; apply In_FBx; left; exact Hin|].
        intros v Hv Hnz. apply in_app_or in Hv as [Hv|Hv]; [|exact (H3 v Hv Hnz)].
        unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht). intros Heq. apply H2. apply In_FBx. right. exists t. auto. }
      { intros b n z H1 H2 H3 Hz. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn]; [|apply L2].
        exfalso. destruct Hi as (o & Ho & Hr).
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        eapply (live_not_pclMA A2 _ _ _ (FBx FB rho kept) (FFx rho fr) b n z HM2 HB2 HFF2 HT2' H1 H2 Hz).
        apply (HRok o _ Ho). rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). exact Hr. }
      { intros b n a H1 H2 H3 Ha.
        destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (_ & HBl2 & _). destruct (HBl2 b n H1) as (Gn & _ & G3 & G4 & _). top_rng G4.
        assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
        subst rho''. cbn [rho_patch rm]. unfold patchf. split.
        - intros _. rewrite shadow_addr_Sh. destruct (in_ranges_dec rho R (Z_to_bv 64 (Sh a))) as [Hi|Hn]; [|apply L2].
          exfalso. apply (RNOTSH _ Hi). rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HSa | rewrite two64; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia].
        - intros j Hj Hdef. replace (SHADOW_OFF + a / 8) with (Sh a) in * by (unfold Sh; lia).
          destruct (in_ranges_dec rho R (word_byte (Sh a) j)) as [Hi|Hn]; [|rewrite L2; exact Hdef].
          exfalso. apply (RNOTSH _ Hi). apply word_byte_of_shadow; [exact HSa | exact Hj]. }
      {
        intros bn H1 _ H3 H4. split; [exact H1|]. split.
        - intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (H3 Hin)|].
          apply (H4 (tvv rho t)); [apply in_or_app; left; unfold tvals; apply in_map; exact Ht | exact Hnz | exact Heq].
        - intros v Hv Hnz. apply H4; [apply in_or_app; right; exact Hv | exact Hnz]. }
      split; [|split; [exact Hk2|split; [|split; [|split; [|split; [|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [cbn [nd_am nd_tv]; unfold XA; rewrite EAM2; unfold tvals in TVK, XIMP |- *; rewrite map_app, IM1, TVK; exact XIMP|split; [|split; [exact (HPAc _ _ HPA HPAc2) | split; [exact HCK2|

      unfold capN in *; unfold BXx in HCN2; cbn [bxN nd_tv] in HCN2 |- *; rewrite cntS_app, (cntS_map _ _ _ _ IM1);
      unfold cntS at 1; rewrite TVK; fold (cntS rho kept); lia]]]]]]]]]]]]]].
      * eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hnf | exact Hag''].
      *
        assert (HM2' : AInv A2 (mkVal (rw rho') (rl rho') (rm rhoL)) tpL mdw).
        { eapply (law_vars _ _ _ ALA); [exact HM2 | reflexivity]. }
        eapply (law_frame _ _ _ ALA); [exact HM2'| |].
        -- intros a Hnm _. subst rho''. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|apply L2].
           exfalso. apply Hnm. eapply cmaddrA_mut. exact (HsubR a Hi).
        -- intros a Hsh Hdef. subst rho''. cbn [rho_patch rm] in *. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|rewrite L2; exact Hdef].
           exfalso. apply (RNOTSH a Hi). destruct Hsh as (f & sz & Hin & Hr).
           destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2') as (_ & _ & HFr2). destruct (HFr2 f sz Hin) as (_ & _ & G64 & Ghs & Gce & _).
           top_rng Gce.
           pose proof (Sh_is_shadow f ltac:(unfold IMG_HI in Ghs; lia)) as S1.
           pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold IMG_HI in Ghs; lia)) as S2.
           unfold is_shadowZ in *. lia.
      *   exact HT2'.
      * intros bn Hbn. apply HB2. apply In_FBx. left. exact Hbn.
      * intros f sz fl Hin. apply HFF2. apply In_FFx. left. exact Hin.
      *
        unfold tvinA. apply Forall_app. split.
        -- apply Forall_forall. intros t Ht Hnz.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in *. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [|exact X2]. apply HB2. apply In_FBx. right. exists t. auto.
        -- eapply tvinA_map; [exact IM1 | exact IM2 |].
           unfold tvinA in HN2 |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN2 t Ht Hnz) as (X0 & X1 & X2).
           split; [exact X0|]. split; [exact X1|]. intros Hin. apply X2. apply In_FBx. left. exact Hin.
      *
        apply tvd_app.
        -- apply (tvd_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). exact (tvd_app_l rho kept passed HD).
        -- eapply tvd_map; [exact IM1 | exact IM2 | exact HD2].
        -- intros t t' Ht Ht' Hnz Hnz' Heq.
           pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt0.
           rewrite (tvv_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0) in Heq. apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho rho'' t Hag'' Hbt0)) in Hnz.
           destruct (In_nth_error _ _ Ht') as [k Hk'].
           assert (exists t0, nth_error (nd_tv ndL) k = Some t0) as [t0 Ht0].
           { pose proof (Forall2_map_eq _ _ _ _ IM1) as L. destruct (nth_error (nd_tv ndL) k) eqn:En; [eexists; reflexivity|].
             exfalso. apply nth_error_None in En. assert (k < length (import_tv isub (nd_tv ndL)))%nat by (apply nth_error_Some; congruence). lia. }
           rewrite (map_nth2 _ _ _ _ k t0 t' IM1 Ht0 Hk') in Heq. apply (proj1 (IM2 k t0 t' Ht0 Hk')) in Hnz'.
           destruct (proj1 (Forall_forall _ _) HN2 t0 (nth_error_In _ _ Ht0) Hnz') as (_ & _ & X2).
           apply X2. apply In_FBx. right. exists t. auto.
      *
        unfold tvz. apply Forall_app. split.
        -- apply (tvz_agree (ss_next (ax_S Cl)) rho rho'' kept Hag'' Hnbk). unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
        -- eapply tvz_map; [exact IM1 | exact IM2 | exact HZ2].
      *
        eapply frinA_agree; [exact Hag'' | exact Hbf |]. destruct HFR as [HFR HCEN]. split.
        -- unfold frinA0 in HFR |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR x Hx) as (X1 & X2 & X3).
           destruct (HFF2 (fst (frv rho x)) (snd (frv rho x)) (uval rho (snd x)) ltac:(apply In_FFx; right; exists x; auto)) as [Y1 Y2].
           rewrite <- surjective_pairing in Y1, Y2. auto.
        -- destruct HCEN as [HCEN HND]. split; [| exact HND].
           intros x Hx. destruct HFR2 as [_ [HC2 _]]. destruct (HC2 x Hx) as [(fl & Hin)|Hin2].
           2: { exfalso. revert Hin2 HfrL. clear. destruct (nd_fr ndL); [intros [] | intros _ H; discriminate H]. }
           apply In_FFx in Hin as [Hin|(y & Hy & Ey)]; [left; exists fl; exact Hin | right].
           apply in_map_iff. exists y. split; [|exact Hy]. injection Ey as E1 E2 E3. destruct x as [x1 x2]. cbn [fst snd] in E1, E2. subst x1 x2.
           symmetry. apply surjective_pairing.
      *
        pose proof (T0_calleeA s rho R (vms md tp ms) Hav Htp) as ET0.
        split.
        -- intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply (proj1 HK0); assumption|].
           rewrite L2. transitivity (rm (rho_sub (rho_absorb rho R (vms md tp ms)) s) (Z_to_bv 64 a)).
           ++ pose proof Hp as Hp0. apply HKc1; [exact Ha|]. destruct Hp as [Hp|[Hs0 Hd0]].
              ** left. destruct Hp as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
              ** right. split; [|rewrite rm_absorb_out by exact Hn'; rewrite (proj1 HK0 _ Ha Hp0); exact Hd0].
                 destruct Hs0 as (y & Hy & Hpy & ->). exists y. split; [exact Hy|]. split; [|reflexivity].
                 destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
                 destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
                 { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
                 { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj1 HK0); assumption.
        -- intros a jj Ha Hp Hjj Hdef. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct Hp as (y & Hy & Hpy & ->).
           assert (Hy47 : 0 <= y < 2 ^ 47).
           { destruct Hpy as [Hpy|Hg]; [exact (pclFA_range segs AInv CST ALA HCST _ _ _ Ai rho tp md y HM HB HFF HT Hpy)|]. apply HXGL in Hg. unfold IMG_HI, LOW_SHADOW_BEG in Hg. lia. }
           assert (NW : ~ in_ranges rho R (word_byte (Sh y) jj)).
           { intros Hin. apply (RNOTSH _ Hin). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Hy47 | exact Hjj]. }
           destruct (in_ranges_dec rho R (word_byte (Sh y) jj)) as [Hi|Hn']; [exfalso; exact (NW Hi)|].
           rewrite L2. apply (HKc2 (Sh y) jj); [pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia | | exact Hjj |].
           ++ exists y. split; [lia|]. split; [|reflexivity]. destruct Hpy as [Hpy|Hg]; [left|right; exact Hg].
              destruct Hpy as [H|[H|[(b & m & Hb & Hr)|(f & sz & fl & Hf & Hr)]]]; [left; rewrite ET0; exact H | right; left; exact H | |].
              { right; right; left. exists b, m. split; [apply In_FBx; left; exact Hb | exact Hr]. }
              { right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hf | exact Hr]. }
           ++ rewrite rm_absorb_out by exact Hn'. apply (proj2 HK0); try assumption. exists y. auto.
      *
        destruct (BUD_splitF (TobjJAM.preA NP rho0 P0f) (ss_facts (ax_S Cl)) bd (bd_subst s (nd_bd ndC)) brest _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho HF (conj HP0 Hav) HPAY HBU) as [_ Nr].
        pose proof HBU as (BX1 & BX2 & _). unfold bxa in BX1, BX2. cbn [fst snd] in BX1, BX2.
        pose proof (apot_range am rho) as [PR1 PR2]. pose proof (XA_kc_nonneg FB _ _ _ _ _ HXA) as KC0.
        pose proof (apot_range (nd_am ndL) rhoL) as [PR3 PR4]. pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA2) as KC2.
        assert (EP2 : apot (am_subst isub (nd_am ndL)) rho'' = apot (nd_am ndL) rhoL) by (unfold apot; rewrite EAM2; exact PIMP).
        cbn [nd_am nd_bd]. rewrite EP2.
        apply (BUD_join (bd_subst isub (nd_bd ndL)) brest _ (aa_V A2) (aa_Km A2) (aa_Kf A2) rho rho'').
        -- unfold BXx, bxa, bxV, bxK in HBU2. cbn [bx2] in HBU2. pose proof (bsum_nonneg brest rho (proj1 Nr) (proj2 Nr)) as [BN1 BN2].
           rewrite (Z.max_r 0 (bsumV brest rho)) in HBU2 by lia. rewrite (Z.max_r 0 (bsumK brest rho)) in HBU2 by lia.
           unfold BUD in HBU2 |- *. unfold bxa. cbn [fst snd] in HBU2 |- *. rewrite IB1, IB2, bd_wpos_subst.
           destruct HBU2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
           split; [lia|]. split; [lia|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
           split; [|split; lia].
           unfold bdL_ok in HbdL. exact (bd_nn_vars_ext _ _ _ _ _ HbdL EI Q7).
        -- symmetry. symmetry. apply (bsumV_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- apply (bsumK_agree (ss_next (ax_S Cl))); [exact Hag'' | exact Hbr].
        -- exact (proj1 Nr).
        -- eapply bd_nn_agree; [exact Hag'' | exact Hbr | exact (proj2 Nr)].
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
        -- unfold bxa. cbn [fst snd]. pose proof (BXok_d_pair _ BX HBX) as [HX1 HX2]. lia.
Qed.
End CallTC.

Hypothesis SUM : ltac2:(tb__ "0|1|
S6dOF_;S16S17S0S0A2M0A1S16S17G0S0A2A1S5eS3S16S68Q40A1A1S47Vsegs;VKc;R6A3S5bVdC;R4A2S6cVsegs;R8S53Vsegs;S43VAInv;VCST;VXGL;VKc;VP0c;R7R6A2R7R6R5VPAc;VndC;AaVPreC;R4R3A5S80Vsegs;VNPc;R4R3S9bR7R6R5A3A5A4F_;F_;Ftp1;Frho1;FBXc;FFFc;FFBc;Fok;").
Hypothesis SUMX : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17G0S0A2A1S5eS3S16S68Q40A1A1S5bVdC;R3A2S6bVsegs;S53Vsegs;S43VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S80Vsegs;VNPc;R3R2S9bR6R5R4A3A5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis HddA : ltac2:(tb__ "0|1|
SfS18S21S7aZ1M0VdC;A2S7aS78VdC;G0A2VdF;A2A2S19A3").

Theorem client_callA : ltac2:(tb__ "0|9|
S6dOF_;S28S74S16S5A1M0S16S17S2S2A2M1A1M2S3S16S68Q40A1A1M3G2G2S16S17S17S2S0A2S2A2A1S16S59A1M4G4S45S6aS47Vsegs;VKc;ReA3SfS18S9aRbS2aReA1A2S19A3SfS1eG0A1S7eRfVPreC;ReA3S1fG0RdA2A3SfS18S7fR10VPreC;RfReS84S17S28S35A2S28S1bS28S35A2VPD;A4A5S19A3SfS18Sa4VNP;R10A2S19A3SfS18S6fR11VNPc;A2S19A3SfS18Sb4VNP;S4S29R13A1A1A2S19A3SfS18S41S4S29R14A1A1S39S1aG1ReRdA3RcRbR9A4A2S19A3SfS18S5cS4S29R15A1A1RbA2S19A3SfS18S8fR15RfS36VndC;A1A3S19A3SfS18S44S40R16S3dVndC;A1A2RcA2S19A3VpayA;S6S29R18A1A1S9Z0M5A1G5RfS1aS59S5aR17S37VndC;A1A2ReA3A5SfS18S2dS96S9cR18S4S29R19A1A1A2VPD;A3S19A3S31S76S85S7S8R18A1S6S29R1cA1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R1aA3S3cVFB;R5A2S3aVFF;R6A2S3fVFB;R7R1dS1aG1R1bR1aA3A4S8cR1eS1aG1R1cR1bA3A2S8dR1fS1aG1R1dR1cA3A2S3eVFF;RaR20R1cA4S11S3S3S11G3G3S11S56S56VAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RcA2S8bR23S33S32RdA1A1A2S10S9dR24R22R20R26A4S10S9eR24R22R20R25A4VP0c;S88VFB;R24R22A3S97R24R20A2S73S72R24R26RdA3R27A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S96S3G3S2cS96R3VPD;A3S6eS4S29R1fA1A1R1bR3A3S6cVsegs;R21S53Vsegs;VJA;S39S1aG1R1aS8eS81R1fVPreC;S1bS28S35R5A3M6R20A4M7S36S1dS28S35R5A3M8A1A2A3R18S1aS59S5aG7S37G8A1A2R16A3S40G7S3dG8A1A2A4A1S99VPreC;R20R1fR1eG6R1dA6R4R3A5R14A4F_;F_;Ftp';Frho';Fd;S6cVsegs;R1dS53Vsegs;VJA;S39S1aG1R16R15A3R14R13R11A4A1R1cR18R17A5R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;Fok;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUM HddA.
  intros ok Cl s R Xk rho tp kept passed fr bd brest am Q Hok.
  apply (client_callT (triple segs ok) (triple_factsA segs ok) (triple_SPA_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundPA3 segs ok)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUM; [exact Hok | exact HB0].
Qed.

Theorem client_callA_ex : ltac2:(tb__ "0|9|
S28S74S16S5A1M0S16S17S2S2A2M1A1M2S3S16S68Q40A1A1M3G2G2S16S17S17S2S0A2S2A2A1S16S59A1M4G4S45S6aSfS18S9aRaS2aRdA1A2S19A3SfS1eG0A1S7eReVPreC;RdA3S1fG0RcA2A3SfS18S7fRfVPreC;ReRdS84S17S28S35A2S28S1bS28S35A2VPD;A4A5S19A3SfS18Sa4VNP;RfA2S19A3SfS18S6fR10VNPc;A2S19A3SfS18Sb4VNP;S4S29R12A1A1A2S19A3SfS18S41S4S29R13A1A1S39S1aG1RdRcA3RbRaR8A4A2S19A3SfS18S5cS4S29R14A1A1RaA2S19A3SfS18S8fR14ReS36VndC;A1A3S19A3SfS18S44S40R15S3dVndC;A1A2RbA2S19A3VpayA;S6S29R17A1A1S9Z0M5A1G5ReS1aS59S5aR16S37VndC;A1A2RdA3A5SfS18S2dS96S9cR17S4S29R18A1A1A2VPD;A3S19A3S31S76S85S7S8R17A1S6S29R1bA1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R19A3S3cVFB;R5A2S3aVFF;R6A2S3fVFB;R7R1cS1aG1R1aR19A3A4S8cR1dS1aG1R1bR1aA3A2S8dR1eS1aG1R1cR1bA3A2S3eVFF;RaR1fR1bA4S11S3S3S11G3G3S11S56S56VAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RcA2S8bR22S33S32RdA1A1A2S10S9dR23R21R1fR25A4S10S9eR23R21R1fR24A4VP0c;S88VFB;R23R21A3S97R23R1fA2S73S72R23R25RdA3R26A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S96S3G3S2cS96R3VPD;A3S6eS4S29R1eA1A1R1aR3A3S6bVsegs;S53Vsegs;VJA;S39S1aG1R19S8eS81R1eVPreC;S1bS28S35R5A3M6R1fA4M7S36S1dS28S35R5A3M8A1A2A3R17S1aS59S5aG7S37G8A1A2R15A3S40G7S3dG8A1A2A4A1S99VPreC;R1fR1eR1dG6R1cA6R4R3A5R13A3F_;F_;Ftp';Frho';Fd;S6bVsegs;S53Vsegs;VJA;S39S1aG1R15R14A3R13R12R10A4A1R1bR17R16A5RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fbrest;Fbd;Ffr;Fpassed;Fkept;Ftp;Frho;FXk;FR;Fs;FCl;").
Proof using ALA HCST HXGL HKc HBX HnextPre HfrC HbaseC HPAc HPAc0 SUMX HddA.
  intros Cl s R Xk rho tp kept passed fr bd brest am Q.
  apply (client_callT (etriple segs) (etriple_factsA segs) (etriple_SPA_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completePA3 segs)); [|exact HddA].
  intros FBc FFc BXc rho1 tp1 HB0. apply SUMX. exact HB0.
Qed.
End Client.

Section Frames.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S16S17S17S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Let JAi : ltac2:(tb__ "0|0|
S35S31S0S54Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S35S54Fnd;") := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S35S31S54FAi;Fnd;") := ltac2:(tb__ "0|0|
S4eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let payA : ltac2:(tb__ "0|1|
S16S7A1S2S0S16S59A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
Sa5VNP;Vrho0;VP0f;A3").

Definition robjs_okL (rho : valuation) (tv : list (sv * sv)) (frs : list (sv * Z * sv)) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S5S0S2cS5R2VR;A3S10S77S1bS0S0ScVrho;R3A2M0A3R2A2S79R2S1dS0S0G0A3A2A2SbcVrho0;S88VFB;Vrho;Vtv;A3SbaVFF;Vrho;Vfrs;A3R3A4F_;F_;Fa;Fo;").
Definition xrs_okL (rho : valuation) (tv : list (sv * sv)) (frs : list (sv * Z * sv)) (X : list (sv * sv)) : Prop := ltac2:(tb__ "0|2|
S17S2S2A2M0S0S2cG0R2VX;A3S10S77S58Vrho;S1bS2S2R3A3A2M1R2A2S79R2S78G1S58Vrho;S1dS2S2R3A3A2A2A2A2S13SbcVrho0;S88VFB;Vrho;Vtv;A3SbaVFF;Vrho;Vfrs;A3R3A4Sb6VXGL;R3A2A2F_;F_;Fa;Fr;").

Lemma ffinA_FFx_sub : ltac2:(tb__ "0|2|
S31S3S16S17S17S2S0A2S2A2M0A1M1G1S3aVFF;R4A2S3eVFF;R5R4R3A4G0S2cG0R1R4A3S2cG0R2R6A3F_;Fx;S3aSbaVFF;R6R4A3R7A2F_;F_;F_;Ffrs;Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr frs HFF [HFR _] Hsub f s fl Hin. apply In_FFx in Hin as [Hin|(x & Hx & E0)]; [exact (HFF _ _ _ Hin)|].
  pose proof (proj1 (Forall_forall _ _) HFR x (Hsub x Hx)) as (X1 & X2 & X3). injection E0 as E1 E2 E3. subst f s fl.
  change (uval rho (fst (fst x)), fs_frame_size (snd (fst x))) with (frv rho x). split; [exact X1 | exact X2].
Qed.

Lemma In_remove_nth {T} : ltac2:(tb__ "0|0|
S16VT;A1S23VT;S2cVT;R1S8aVT;R2R3A3A3S2cVT;R2R4A3F_;Fx;Fi;Fl;").
Proof using .
  clear. induction l as [|a l IH]; intros [|i] x H; cbn in H; try contradiction.
  - right. exact H.
  - destruct H as [->|H]; [left; reflexivity | right; eapply IH; exact H].
Qed.
Lemma remove_nth_split {T} : ltac2:(tb__ "0|3|
S16VT;A1M0S23VT;SfS1eVT;A1S2eVT;R3R2A3S1fVT;R1A2A3S10SfG0R4S1aVT;S86VT;R3R4A3M1S20VT;R2S87VT;S26R3A1R4A3M2A3A3A3SfG0S8aVT;R3R4A3S1aVT;G1G2A3A3A2F_;Fx;Fi;Fl;").
Proof using .
  clear. induction l as [|a l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. split; reflexivity.
  - destruct (IH i x H) as [A B]. cbn. rewrite <- A, <- B. split; reflexivity.
Qed.

Lemma nodup_split_unique {T} : ltac2:(tb__ "0|1|
S16VT;A1M0G0G0G0VT;S2fVT;S1aVT;R5S20VT;R1R3A3A3A2SfG0S1aVT;R6S20VT;R2R4A3A3S1aVT;R5S20VT;R2R3A3A3A3S10SfG0R7R6A3SfG0R5R4A3A2F_;F_;Fx;Fk2;Fl2;Fk1;Fl1;").
Proof using .
  clear. induction l1 as [|a l1 IH]; intros [|b k1] l2 k2 x ND E; cbn in E.
  - injection E as ->. auto.
  - injection E as Exb El2. exfalso. subst. cbn in ND. inversion ND as [|? ? Hnin Hnd']. apply Hnin. apply in_or_app. right. left. reflexivity.
  - injection E as Eax Ek2. exfalso. subst. cbn in ND. inversion ND as [|? ? Hnin Hnd']. apply Hnin. apply in_or_app. right. left. reflexivity.
  - injection E as Eab E2. subst. cbn in ND. inversion ND as [|? ? Hnin Hnd']. destruct (IH k1 l2 k2 x Hnd' E2) as [-> ->]. auto.
Qed.

Section CallTF.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S54S28S3S16S68Q40A1A1S6aS85S7S8R3A1S6S29R4A1A1A3VTR;S53Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S6aS6aS6aS6dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S54S54S28S28S74S16S5A1M0S16S17S28S7dA2M1A1S16S17S2S2A2M2A1S6aS3S16S68Q40A1A1M3G2S2cG2R1R5A3S2cG2R2S2aRbA1A3F_;Fr;SfS1eG0A1S7eRaR9R8A3S1fG0R7A2A3SfS18S7fRbRaR9R8S84G1S28S1bS28S7dA2R7A4A5S19A3S3G3VTR;S53Vsegs;RfRdR2R1A5S80Vsegs;S4S29RdA1A1R2R1RaA5A2Ftp1;Frho1;S16S57A1M4S76S56S55Vsegs;R9R8R10S1cG4Sb2R3Sb3R2R1A2A4A5R13RaR9R4R2A4R13S73S72RbRfS83R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S28S7dG4S76S56S3G3G4S76S56S2cG1S1cS28S7dRaR9A4R14A3S55Vsegs;R12R11R19S1cG4Sb2R9Sb3R8R7A2A4A5R1cR13R12RaR8A4S6eS4S29R1aA1A1S73S72R14R18S83R9R13RaA3A3R19A2R8A3S55Vsegs;R9R8ReS1cG4Sb2R7Sb3R6R5A2A4A5ReS73S72R16R1aS83RbR15RcA3A3R1bA2R15RaR9R8R6A6S10Sb8R17S83RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S70R18S83RdR17ReA3R1cR1dS29R1eA1S29R1fA1S29R11A1R1RcA9VTR;S53Vsegs;S82R11S73S72R19R1dS83ReR18RfA3A3R1eA2R18RdRcA5Sb7R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S53Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem sfree_callT : ltac2:(tb__ "0|a|
S0S28S74S16S5A1M0S16S17S2S2A2M1A1S3S16S68Q40A1A1M2S35S23S17S17S2S0A2M3S2A2M4S6aS31S3G2VTR;S53Vsegs;SadVAInv;ReR3VKc;A4Sa8VE;ReA2M5R2R1A5S80Vsegs;Sc4R2R1S20S17S28S7dA2M6S1cS28S7dSa9VE;ReA2SacVAInv;VCST;VXGL;ReR3VKc;A6A4S22G6A1A3A5A2Ftp1;Frho1;FAi;S10S77Z0RcA2S77RcZ6A2A2G1S2cG1R1RaA3S2cG1R2S2aReA1A3F_;Fr;SfS1eG0A1S7eRdG5RcA3S1fG0RbA2A3SfS18S7fReSa8VE;RfA2RdRcS20S28Sa9VE;RfA2S22S28A1A3A5S19A3SfS18Sa4VNP;ReA2S19A3SfS18Sb4VNP;S4S29R10A1A1A2S19A3SfS18S41S4S29R11A1A1RbA2S19A3SfS18S5dS37RcA1A1S19A3SfS1eG4A1S2eG4S38RdA1RcA3S1fG4RbA2A3SfS0S1dS2S0S1bG3S2RcA3A3R15A3S31S31VPA;R2A1M7G7F_;FA';FA;S31S85S7S8R13A1S6S29R17A1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R15A3S3cVFB;R4A2S3aVFF;R5A2S3fVFB;R6R18S36R16A1A4S8cR19S36R17A1A2S8dR1aS36R18A1A2S3eVFF;R9R1bS38R19A1A4S11S3S3S11G2G2S11S56S56VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RbA2S8bR1eS33S32RcA1A1A2S10SbeR1fS36R1dA1M8S8aG4R1cS38R1dA1A3M9R21A4S10SbfR1fG8G9R20A4S10SfS0S58R1fS75R22PcA2A2S58R1fS1bS2S0S1bG3S2R1bA3A3A2A3SfS0S58R1fS75R22SaaA2A2S58R1fS1dG3S2R1bA3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S3G2VTR;S53Vsegs;VJA;S39S36R13A1S8aG4R12S38R13A1A3S37R13A1S3dR13A1A4A1SbbSa8VE;R1aA2R19R18R17Sa9VE;R1aA2R16A6R2R1A5R10A2Ftp';Frho';VTR;S53Vsegs;VJA;R12A1R18R14R13A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ffe;Fi;Fnd;Ftp;Frho;FXk;FR;Fs;FCl;Fc;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros c Cl s R Xk rho tp nd i fe Q CALLEE Hc6 HXk He Hchk Htp Hnf Hnb Hwp Hnth Hcls HPAK HSITE Tcont.
  assert (Hc : 0 <= c) by lia.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  set (sz := fs_frame_size c) in *. assert (Esz : sz = fs_frame_size c) by reflexivity.
  eapply (TR_callP (JAi nd Ai kc) (J_stack_free_pre AInv c Ai Kc) Cl (Pre_stack_free E c) s R
            [(L_stack_free E c, JL_stack_free AInv CST XGL c Ai Kc)] Xk Q rho tp HXk He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & Hf & Hfl).
    pose proof HFR as HFRc. destruct HFRc as (HFR0 & HCEN & HND). pose proof (proj1 (Forall_forall _ _) HFR0 fe (nth_error_In _ _ Hnth)) as (E1 & E2 & E3).
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [ | | exact HT | exact (HRok o a Ho Hr)].
      - apply (fbinA_FBx FB Ai rho (nd_tv nd) []). exact HB. rewrite app_nil_r. exact HN.
      - apply (ffinA_FFx_sub Ai rho (nd_fr nd)); [exact HFF | exact HFR | intros x Hx; eapply In_remove_nth; exact Hx]. }
    split; [eapply (AInv_absorb segs AInv CST ALA HCST); [exact HM | exact HRokA]|]. split; [exact Hk|].
    split; [eapply (tp_of_TPA NP rho0); eauto|].
    pose proof (top_of_TPA NP rho0 Ai s rho R (vms md tp ms) Hav HT Htp) as HTV.
    unfold frv in E1, E2. rewrite Hcls in E1, E2. fold sz in E1, E2.
    cbn [fst snd]. rewrite !rw_call'. change (bv_unsigned (eval rho (wsub_get s 12))) with (uval rho (wsub_get s 12)).
    change (bv_unsigned (eval rho (wsub_get s V_FL))) with (uval rho (wsub_get s V_FL)). rewrite Hf, Hfl. split; [exact E1 | split; [exact E2 | exact HTV]].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & Hf & Hfl).
    pose proof HFR as HFRc. destruct HFRc as (HFR0 & HCEN & HND). pose proof (proj1 (Forall_forall _ _) HFR0 fe (nth_error_In _ _ Hnth)) as (E1 & E2 & E3).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    cbn [In] in HinL. destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & Htp2).

    assert (Efe : frv rho fe = (bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive), fs_frame_size c)).
    { unfold frv. rewrite Hcls, rw_call'. change (bv_unsigned (eval rho (wsub_get s 12))) with (uval rho (wsub_get s 12)). rewrite Hf. reflexivity. }
    rewrite <- Efe in HLi.
    assert (HRokA : robjs_okA CST Ai None rho R).
    { intros o a Ho Hr. eapply pclMA_cmaddrA; [ | | exact HT | exact (HRok o a Ho Hr)].
      - apply (fbinA_FBx FB Ai rho (nd_tv nd) []). exact HB. rewrite app_nil_r. exact HN.
      - apply (ffinA_FFx_sub Ai rho (nd_fr nd)); [exact HFF | exact HFR | intros x Hx; eapply In_remove_nth; exact Hx]. }
    destruct (remove_nth_split (nd_fr nd) i fe Hnth) as [SP1 SP2].

    assert (OTHER : forall x, In x (remove_nth i (nd_fr nd)) -> frv rho x <> frv rho fe).
    { intros x Hx Ex. rewrite SP1 in HND. rewrite map_app in HND. cbn [map] in HND.
      apply (NoDup_remove_2 _ _ _ HND). rewrite <- map_app, <- Ex. apply in_map. rewrite <- SP2. exact Hx. }

    assert (SURV : forall A', aa_frames A' = l1 ++ l2 -> aa_geom A' = aa_geom Ai ->
              ffinA (FFx FF rho (remove_nth i (nd_fr nd))) A'
              /\ (forall f s0 fl, In (f, s0, fl) FF -> In (f, s0) (aa_frames A'))
              /\ frinA0 FF A' rho (remove_nth i (nd_fr nd))).
    { intros A' HF' HG'.
      assert (FFin : forall f s0 fl, In (f, s0, fl) FF -> In (f, s0) (aa_frames A')).
      { intros f s0 fl Hin. destruct (HFF _ _ _ Hin) as [HinA _].
        rewrite HLi in HinA. apply in_mid_cases in HinA as [Ex|HinA]; [|rewrite HF'; exact HinA].
        exfalso. apply (E3 _ Hin). cbn [fst]. rewrite <- Ex. reflexivity. }
      assert (FR0 : frinA0 FF A' rho (remove_nth i (nd_fr nd))).
      { unfold frinA0. apply Forall_forall. intros x Hx.
        pose proof (proj1 (Forall_forall _ _) HFR0 x (In_remove_nth _ _ _ Hx)) as (X1 & X2 & X3).
        rewrite HG'. split; [|split; [exact X2 | exact X3]].
        rewrite HLi in X1. apply in_mid_cases in X1 as [Ex|X1]; [exfalso; exact (OTHER x Hx Ex) | rewrite HF'; exact X1]. }
      split; [|split; [exact FFin | exact FR0]].
      intros f s0 fl Hin. apply In_FFx in Hin as [Hin|(x & Hx & E0)].
      - split; [exact (FFin _ _ _ Hin) | rewrite HG'; exact (proj2 (HFF _ _ _ Hin))].
      - injection E0 as Ef Es Efl. subst f s0 fl.
        pose proof (proj1 (Forall_forall _ _) FR0 x Hx) as (X1 & X2 & X3).
        change (uval rho (fst (fst x)), fs_frame_size (snd (fst x))) with (frv rho x). split; [exact X1 | exact X2]. }
    assert (ROK2 : forall A', aa_frames A' = l1 ++ l2 -> aa_geom A' = aa_geom Ai -> aa_live A' = aa_live Ai -> robjs_okA CST A' None rho R).
    { intros A' HF' HG' HL' o a Ho Hr. destruct (SURV A' HF' HG') as (S1 & _ & _). eapply pclMA_cmaddrA; [ | exact S1 | exact (TPA_kept rho0 Ai A' HG' HT) | exact (HRok o a Ho Hr)].
      apply (fbinA_FBx FB A' rho (nd_tv nd) []); [intros b Hb; rewrite HL'; exact (HB b Hb)|]. rewrite app_nil_r.
      unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Y0 & Y1 & Y2).
      rewrite HL'. auto. }
    assert (XOK : forall A', (A' = Ai \/ (aa_frames A' = l1 ++ l2 /\ aa_geom A' = aa_geom Ai /\ aa_live A' = aa_live Ai)) -> xrs_okA CST XGL A' None rho Xk).
    { intros A' HA r a Hr Ha. destruct (HX r a Hr Ha) as [Hp|Hg]; [left | right; exact Hg].
      destruct HA as [-> | (HF' & HG' & HL')].
      - eapply pclMA_cmaddrA; [ | | exact HT | exact Hp].
        + apply (fbinA_FBx FB Ai rho (nd_tv nd) []). exact HB. rewrite app_nil_r. exact HN.
        + apply (ffinA_FFx_sub Ai rho (nd_fr nd)); [exact HFF | exact HFR | intros x Hx; eapply In_remove_nth; exact Hx].
      - destruct (SURV A' HF' HG') as (S1 & _ & _). eapply pclMA_cmaddrA; [ | exact S1 | exact (TPA_kept rho0 Ai A' HG' HT) | exact Hp].
        apply (fbinA_FBx FB A' rho (nd_tv nd) []); [intros b Hb; rewrite HL'; exact (HB b Hb)|]. rewrite app_nil_r.
        unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Y0 & Y1 & Y2).
        rewrite HL'. auto. }
    assert (NONEW : forall o', In o' (new_objs (ax_S (Pre_stack_free E c)) (ax_S (L_stack_free E c))) -> False).
    { intros o' Ho'. cbn in Ho'. exact Ho'. }
    split.
    + split; [split; [exact (KEPT_stepA2 segs AInv CST XGL ALA Ai A2 None rho rhoL _ s R _ _ _ HM HRokA (ROK2 A2 HF2 HG2 HL2) Hkept2)|]|split].
      * intros o' oR Ho' _. exfalso. exact (NONEW o' Ho').
      * intros r a j oR Hr. cbn [ax_X L_stack_free mkA] in Hr. destruct Hr.
      * exact (caller_X_kept2 segs AInv CST XGL ALA HCST HXGL Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl (Pre_stack_free E c) (L_stack_free E c) Xk _ _ _ Hsm HXk
                 HM HRokA (XOK Ai (or_introl eq_refl)) (XOK A2 (or_intror (conj HF2 (conj HG2 HL2))))
                 (xrs_range segs AInv CST XGL ALA HCST HXGL Ai None rho tp md Xk HM (XOK Ai (or_introl eq_refl)))
                 HbC Hkept2 (fun o' Ho' w _ => False_ind _ (NONEW o' Ho')) eq_refl).
    +
      intros rho' Hlink.
      eapply TR_pre; [ | apply (Tcont (rho_patch rho' (patchf rho rho' R)) tpL)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & Htp3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA3 Cl (Pre_stack_free E c) _ s R Xk rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      rewrite <- Efe in HLi3.

      assert (EK : k1 ++ k2 = l1 ++ l2).
      { assert (ND : List.NoDup (aa_frames Ai)) by (eapply (frames_nodup segs AInv CST ALA); exact HM).
        rewrite HLi in ND. destruct (nodup_split_unique l1 k1 l2 k2 (frv rho fe) ND ltac:(rewrite <- HLi; exact HLi3)) as [-> ->]. reflexivity. }
      rewrite EK in HF3.
      assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & _).
      assert (Hbf' : fr_below (ss_next (ax_S Cl)) (remove_nth i (nd_fr nd)) = true).
      { unfold fr_below in Hbf |- *. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) Hbf x (In_remove_nth _ _ _ Hx)). }
      assert (EMF : map (frv (rho_patch rho' (patchf rho rho' R))) (remove_nth i (nd_fr nd)) = map (frv rho) (remove_nth i (nd_fr nd))).
      { eapply frv_map_agree; [exact HagP | exact Hbf']. }
      assert (HPAY : payA (ss_facts (ax_S Cl)) (SLit 0) 0 (nd_bd nd) (nd_bd nd)).
      { split; [exact Hwp|]. split; [lia|]. intros r _ _ _ Hnn. split; [unfold uval; rewrite U_lit; change (0 mod M64v) with 0; lia|]. split; [lia | exact Hnn]. }
      destruct (SURV A3 HF3 HG3) as (S1 & S2 & S3).
      pose proof (HPAK Ai A3 HPA) as HPA2.
      eapply (cont_JAi_fr segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA Cl (Pre_stack_free E c) (L_stack_free E c) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                (nd_tv nd) _ (nd_bd nd) (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRokA Hlink HM3 Hk3 (ROK2 A3 HF3 HG3 HL3)); try assumption.
      * intros b Hb. rewrite HL3. exact (HB b Hb).
      * rewrite HV3. unfold uval. rewrite U_lit. change (0 mod M64v) with 0. lia.
      * rewrite HKm3, HKf3. lia.
      * cbn zeta. split; [|split].
        -- apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
           unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL3; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
        -- apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      *
        eapply (frinA_agree FF A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbf' |].
        split; [exact S3 | split].
        -- intros x Hx. rewrite HF3 in Hx.
           assert (HxA : In x (aa_frames Ai)) by (rewrite HLi; apply in_app_mid; exact Hx).
           destruct (HCEN x HxA) as [H|H]; [left; exact H | right].
           rewrite SP1, map_app in H. cbn [map] in H. rewrite SP2, map_app. apply in_mid_cases in H as [Ex|H]; [|exact H].
           exfalso. assert (ND : List.NoDup (aa_frames Ai)) by (eapply (frames_nodup segs AInv CST ALA); exact HM).
           rewrite HLi in ND. apply (NoDup_remove_2 _ _ _ ND). rewrite <- Ex. exact Hx.
        -- rewrite SP1 in HND. rewrite map_app in HND. cbn [map] in HND. rewrite SP2, map_app. exact (NoDup_remove_1 _ _ _ HND).
      * intros b m Hb _ _. rewrite HL3. exact Hb.
      * cbn zeta; intros ? ? _ _ Hut.
        eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut].
        exact (proj1 (nd_below_split _ _ Hnb)).
      * cen_same_tvG Hlink Hnb HL3.
      * capK_sameG HCKi HL3 HV3.
      * capN_sameG HCNi Hlink Hnb HL3.
Qed.
End CallTF.

Theorem sfree_callA : ltac2:(tb__ "0|7|
S6dOF_;S0S28S74S16S5A1M0S16S17S2S2A2A1S3S16S68Q40A1A1M1S35S23S17S17S2S0A2M2S2A2M3S6aS47Vsegs;VKc;RcA3SaeVsegs;VE;VAInv;VCST;VXGL;A5S2cS0RdS20S0Z5S20S0Z6S22S0A1A3A3A3SfS18SbdRaS2aRdA1A2S19A3SfS1eG0A1S7eReSa8VE;RfA2RdA3S1fG0RcA2A3SfS18S7fRfSa8VE;R10A2ReRdS20S28Sa9VE;R10A2S22S28A1A3A5S19A3SfS18Sa4VNP;RfA2S19A3SfS18Sb4VNP;S4S29R11A1A1A2S19A3SfS18S41S4S29R12A1A1RcA2S19A3SfS18S5dS37RdA1A1S19A3SfS1eG3A1S2eG3S38ReA1RdA3S1fG3RcA2A3SfS0S1dS2S0S1bG2S2RdA3A3R16A3S31S31VPA;R2A1M4G4F_;FA';FA;S31S85S7S8R14A1S6S29R18A1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R16A3S3cVFB;R4A2S3aVFF;R5A2S3fVFB;R6R19S36R17A1A4S8cR1aS36R18A1A2S8dR1bS36R19A1A2S3eVFF;R9R1cS38R1aA1A4S11S3S3S11G1G1S11S56S56VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RbA2S8bR1fS33S32RcA1A1A2S10SbeR20S36R1eA1M5S8aG3R1dS38R1eA1A3M6R22A4S10SbfR20G5G6R21A4S10SfS0S58R20S75R23PcA2A2S58R20S1bS2S0S1bG2S2R1cA3A3A2A3SfS0S58R20S75R23SaaA2A2S58R20S1dG2S2R1cA3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S3G1S6cVsegs;R1cS53Vsegs;VJA;S39S36R14A1S8aG3R13S38R14A1A3S37R14A1S3dR14A1A4A1SbbSa8VE;R1bA2R1aR19R18Sa9VE;R1bA2R17A6R2R1A5R11A4Ftp';Frho';S6cVsegs;R1bS53Vsegs;VJA;R13A1R19R15R14A5R10A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ffe;Fi;Fnd;Ftp;Frho;FXk;FR;Fs;FCl;Fc;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok c Cl s R Xk rho tp nd i fe Q Hok AC Hin HXk.
  assert (Hc6 : 0 <= c <= 6) by (cbn in Hin; lia).
  apply (sfree_callT (triple segs ok) (triple_factsA segs ok) (triple_SPA_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundPA3 segs ok) c Cl s R Xk rho tp nd i fe Q);
    [ | exact Hc6 | exact (xrs_inclb_sound _ _ HXk)].
  intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC c Hin); [exact HKc|].
  intros r p t ms m msv' Hj HMI Hh Hp Hs. eapply (proj1 Hok r p t ms m msv'); eauto. exact (proj1 (proj2 Hj)).
Qed.

Theorem sfree_callA_ex : ltac2:(tb__ "0|7|
S0S28S74S16S5A1M0S16S17S2S2A2A1S3S16S68Q40A1A1M1S35S23S17S17S2S0A2M2S2A2M3S6aSafVsegs;VE;VAInv;VCST;VXGL;A5S2cS0RcS20S0Z5S20S0Z6S22S0A1A3A3A3SfS18SbdR9S2aRcA1A2S19A3SfS1eG0A1S7eRdSa8VE;ReA2RcA3S1fG0RbA2A3SfS18S7fReSa8VE;RfA2RdRcS20S28Sa9VE;RfA2S22S28A1A3A5S19A3SfS18Sa4VNP;ReA2S19A3SfS18Sb4VNP;S4S29R10A1A1A2S19A3SfS18S41S4S29R11A1A1RbA2S19A3SfS18S5dS37RcA1A1S19A3SfS1eG3A1S2eG3S38RdA1RcA3S1fG3RbA2A3SfS0S1dS2S0S1bG2S2RcA3A3R15A3S31S31VPA;R2A1M4G4F_;FA';FA;S31S85S7S8R13A1S6S29R17A1A1A3VP0f;Vrho0;A1S6eVNP;Vrho0;R15A3S3cVFB;R4A2S3aVFF;R5A2S3fVFB;R6R18S36R16A1A4S8cR19S36R17A1A2S8dR1aS36R18A1A2S3eVFF;R9R1bS38R19A1A4S11S3S3S11G1G1S11S56S56VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3bVrho0;RbA2S8bR1eS33S32RcA1A1A2S10SbeR1fS36R1dA1M5S8aG3R1cS38R1dA1A3M6R21A4S10SbfR1fG5G6R20A4S10SfS0S58R1fS75R22PcA2A2S58R1fS1bS2S0S1bG2S2R1bA3A3A2A3SfS0S58R1fS75R22SaaA2A2S58R1fS1dG2S2R1bA3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S3G1S6bVsegs;S53Vsegs;VJA;S39S36R13A1S8aG3R12S38R13A1A3S37R13A1S3dR13A1A4A1SbbSa8VE;R1aA2R19R18R17Sa9VE;R1aA2R16A6R2R1A5R10A3Ftp';Frho';S6bVsegs;S53Vsegs;VJA;R12A1R18R14R13A5RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ffe;Fi;Fnd;Ftp;Frho;FXk;FR;Fs;FCl;Fc;").
Proof using ALA HCST HXGL HKc.
  intros c Cl s R Xk rho tp nd i fe Q ACX Hin HXk.
  assert (Hc6 : 0 <= c <= 6) by (cbn in Hin; lia).
  apply (sfree_callT (etriple segs) (etriple_factsA segs) (etriple_SPA_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completePA3 segs) c Cl s R Xk rho tp nd i fe Q);
    [ | exact Hc6 | exact (xrs_inclb_sound _ _ HXk)].
  intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX c Hin). exact HKc.
Qed.
End Frames.
End WithSegs.
End TobjJAC.

(* [comment removed for export] *)
Module TobjJAM2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "andb"; "option"; "Some"; "None"; "false"; "fst"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sobj"; "sv"; "SLit"; "ss_facts"; "sprop"; "sv_eqb"; "holds"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "xs_framed"; "J_ofPA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "nd_tv"; "JA"; "JAi"; "JAk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "J_pure_pre"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S20S12S4S3cQ40A1A1S2bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4fVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1bS50VCST;R1A2S10S52Z0R2A2S53R2S4bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1bS50VXGL;R1A2S10S52Z0R2A2S53R2S4bA2A2F_;Fa;").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S8S8S1bS1bA2S1bA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Let JAi : ltac2:(tb__ "0|0|
S2dS20S1bS1eFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S35VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S2dS1eFnd;") := ltac2:(tb__ "0|0|
S34VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S2dS20S1eFAi;Fnd;") := ltac2:(tb__ "0|0|
S36VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let site_okA : ltac2:(tb__ "0|0|
S0S39S4S14A1S12S2dSaS1bA1S20S27OF_;F_;OFextra;Fx;Fnd;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;A8").
Let payA : ltac2:(tb__ "0|1|
S4S18A1S15S1bS4S45A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S48VNP;Vrho0;VP0f;A3").
Let call_checkTA := call_checkTA NP.
Let cmaddrA := cmaddrA CST.
Let robjs_okA := robjs_okA CST.

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1eS0S12S4S3cQ40A1A1S28S41S18S1aR3A1S17S1R4A1A1A3VTR;S1dVsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S28S28S28S29R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S1eS1eS0S0S39S4S14A1M0S4S8S0S21A2M1A1S4S8S15S15A2M2A1S28S12S4S3cQ40A1A1M3G2S3aG2R1R5A3S3aG2R2S3RbA1A3F_;Fr;SfSaG0A1S24RaR9R8A3SbG0R7A2A3SfS5S23RbRaR9R8S40G1S0SeS0S21A2R7A4A5S6A3S12G3VTR;S1dVsegs;RfRdR2R1A5S22Vsegs;S13S1RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S2cA1M4S27S2bS1fVsegs;R9R8R10S7G4S3dR3S3eR2R1A2A4A5R13RaR9R4R2A4R13S38S37RbRfS2aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S21G4S27S2bS12G3G4S27S2bS3aG1S7S0S21RaR9A4R14A3S1fVsegs;R12R11R19S7G4S3dR9S3eR8R7A2A4A5R1cR13R12RaR8A4S42S13S1R1aA1A1S38S37R14R18S2aR9R13RaA3A3R19A2R8A3S1fVsegs;R9R8ReS7G4S3dR7S3eR6R5A2A4A5ReS38S37R16R1aS2aRbR15RcA3A3R1bA2R15RaR9R8R6A6S10S54R17S2aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S12S44R18S2aRdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9VTR;S1dVsegs;S26R11S38S37R19R1dS2aReR18RfA3A3R1eA2R18RdRcA5S55R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1dVsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem purec_callT_ag_xp : ltac2:(tb__ "0|5|
S20S12OF_;F_;S0S4S0A1S0S39S4S14A1M0S12S4S3cQ40A1A1M1S2dS4S45A1S28S20S12G1VTR;S1dVsegs;S12G1S4S2cA1M2S2bS10S4eVAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5S22Vsegs;S3fR2R1S40S0S8S0S21A2S0S7S0S21R1S4dVAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;SfS1cS13S1RbA1A1S3fA3SfS15S2RcA1S16S4cA1A3SfSaG0A1S24RbRdRaA3SbG0R9A2A3SfS5S23RcReRbRaRdA5S6A3SfS5Vcall_checkTA;RcA1S6A3SfS5S51VNP;S13S1ReA1A1A2S6A3SfS5S31S13S1RfA1A1RaA2S6A3SfS5S46S13S1R10A1A1RaA2S6A3VpayA;S17S1R11A1A1S16Z0M3A1G3S30RcA1RbA5SfS5S3bS0S0S9S9G0S5Lx;S43S1R15A1S1R1A1A2S6S14G0SdLl;Ls0;X4x2S25R15R1A2A2S19S2R1A1S2R15A1A2A2LL;R13A3S6A3Vsite_okA;R13R12R11R10ReScS1bA1M4S20S27S11Lms;LAi;A7S20G2S27S2bS1fVsegs;R15R14R18S7G2S3dR3S3eR2R1A2A4A5VAInv;R5R16R15R2A4S4aVCST;VXGL;R6G4R17S3R1aA1A6R1eR7S38S37R18R19S2aR4R17R5A3A3R1aA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S0S12G1S3aS0R3R19A3S42S13S1R19A1A1R16R3A3VTR;S1dVsegs;VJA;S2eS33R15A1S32R15A1R14S2fR15A1A4A1S47R1cR1aR19R18R5A5R4R3A5R13A2F_;F_;Ftp';Frho';FL;VTR;S1dVsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;FXP;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros XP Pre Ls Cl s R rho tp nd bd' Q CALLEE HNF HbP He Hchk Htp Hnf Hnb Hbb HPAY Hshape HSITE HXP Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_pure_pre AInv Ai Kc r p t m /\ XP Ai r) Cl Pre s R
            (map (fun L => (L, JL_pure AInv CST XGL Ai Kc)) Ls) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_map. cbn [fst]. rewrite map_id. exact Hchk.
  - intros rho1 tp1. rewrite HNF. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    split; [|exact (HXP Ai tr ms md Hsm HM HX)].
    split; [eapply (AInv_absorb segs AInv CST ALA HCST); [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply (tp_of_TPA NP rho0); eauto | exact (top_of_TPA NP rho0 Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He HbP) as HbC.
    apply in_map_iff in HinL as (L0 & Heq & HinL). injection Heq as HJLe HL. subst L JL.
    pose proof (proj1 (forallb_forall _ _) Hshape L0 HinL) as HS. apply andb_prop in HS as [HS HbL]. apply andb_prop in HS as [Hnonew Hxf].
    apply sv_eqb_sound in HbL. rewrite HbP in HbL.
    assert (NONEW : forall o', In o' (new_objs (ax_S Pre) (ax_S L0)) -> False).
    { intros o' Hin'. destruct (new_objs (ax_S Pre) (ax_S L0)); [destruct Hin' | discriminate]. }
    destruct HJL as (HM2 & Htp2 & Hkept2 & Hk2).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA Ai None a) by (intros a H; exact H).
    split.
    * split; [split; [exact (KEPT_stepA segs AInv CST XGL ALA Ai Ai None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. exact (NONEW o' Hin').
      --
         intros r a j oR Hr Ha Hj HoR Hrng.
         unfold xs_framed in Hxf. pose proof (proj1 (forallb_forall _ _) Hxf r Hr) as Hrp. apply existsb_exists in Hrp as (rp & HinP & Heqr).
         apply xr_eqb_sound in Heqr. subst rp.
         pose proof Hsm as (HsmS & _ & HwfC & HshC & _).
         assert (HXcov : forallb (fun r0 => xr_covered (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r0)) (ax_X Pre) = true /\ axwf Pre = true).
         { clear - He. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S Cl) (ax_S Pre) s); [|discriminate].
           match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
           apply andb_prop in Hc as [Hc Hwf]. apply andb_prop in Hc as [Hc _]. auto. }
         destruct HXcov as [HXcov HwfP].
         pose proof (xr_covered_sound rho (ss_facts (ax_S Cl)) (ss_objs (ax_S Cl)) (bv_unsigned (eval rho (ax_base Cl))) (ax_X Cl) (xr_subst s r)
                       HF (proj1 (forallb_forall _ _) HXcov r HinP) HshC) as Hok.
         unfold axwf in HwfP. apply andb_prop in HwfP as [HwfX _]. pose proof (proj1 (forallb_forall _ _) HwfX r HinP) as Hrb.
         unfold xr_below in Hrb. apply andb_prop in Hrb as [Hrb1 Hrb2].
         assert (EV : forall e, sv_below (ss_next (ax_S Pre)) e = true -> eval rhoL e = eval rho (sv_subst s e)).
         { intros e He0. rewrite <- (eval_agree_vals _ _ _ e Hag1 He0). rewrite <- eval_subst. apply eval_absorb. }
         destruct r as [b l]. cbn [fst snd] in Ha, Hrb1, Hrb2. rewrite (EV b Hrb1), (EV l Hrb2) in Ha.
         unfold xr_ok, xr_subst in Hok. cbn [fst snd] in Hok. rewrite <- !eval_subst in Hok || idtac.
         destruct Hok as (_ & _ & Hok). destruct (Hok a ltac:(rewrite !eval_subst; rewrite !eval_subst in Ha || idtac; exact Ha)) as (_ & _ & Hwd & _).
         destruct (Hwd j Hj) as [Hout _].
         rewrite HbL in Hrng. rewrite HbC in Hout. cbn [eval] in Hrng, Hout.
         exact (proj1 (Forall_forall _ _) Hout oR (proj2 (proj2 (proj2 (proj2 (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm)))) oR HoR) Hrng).
      -- eapply (caller_X_kept segs AInv CST XGL ALA HCST HXGL Ai Ai None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         all: try (eapply (xrs_range segs AInv CST XGL ALA HCST HXGL); eauto). all: intros o' Hin'; exfalso; exact (NONEW o' Hin').
    * intros rho' Hlink.
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      eapply TR_pre; [ | apply (Tcont L0 (rho_patch rho' (patchf rho rho' R)) tpL HinL HagP)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (HM3 & Htp3 & Hkept3 & Hk3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact ((cont_smatchA segs) Cl Pre _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists Ai, kc.
      destruct (law_budget _ _ _ ALA Ai _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      eapply (cont_JAi segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA Cl Pre L0 s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc Ai None
                _ bd' (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub); try assumption; try reflexivity.
      -- pose proof (uval_range rho (SLit 0)). lia.
      -- lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB Ai (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HN].
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      -- intros b m Hb _ _. exact Hb.
      -- chain_same_tv Hlink Hnb0.
      -- cen_same_tvG Hlink Hnb0 (eq_refl (aa_live Ai)).
      -- capN_sameG HCNi Hlink Hnb0 (eq_refl (aa_live Ai)).
Qed.

Theorem purec_callT_ag : ltac2:(tb__ "0|3|
S0S4S0A1S0S39S4S14A1M0S12S4S3cQ40A1A1M1S2dS4S45A1S28S20S12G1VTR;S1dVsegs;S4eVAInv;R3VKc;A3RdR2R1A5S22Vsegs;S3fR2R1S40S0S8S0S21A2S0S7S0S21R1S4dVAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;SfS1cS13S1RbA1A1S3fA3SfS15S2RcA1S16S4cA1A3SfSaG0A1S24RbRdRaA3SbG0R9A2A3SfS5S23RcReRbRaRdA5S6A3SfS5Vcall_checkTA;RcA1S6A3SfS5S51VNP;S13S1ReA1A1A2S6A3SfS5S31S13S1RfA1A1RaA2S6A3SfS5S46S13S1R10A1A1RaA2S6A3VpayA;S17S1R11A1A1S16Z0M2A1G2S30RcA1RbA5SfS5S3bS0S0S9S9G0S5Lx;S43S1R15A1S1R1A1A2S6S14G0SdLl;Ls0;X4x2S25R15R1A2A2S19S2R1A1S2R15A1A2A2LL;R13A3S6A3Vsite_okA;R13R12R11R10ReScS1bA1S20S27S11Lms;LAi;A7S0S12G1S3aS0R3R18A3S42S13S1R18A1A1R15R3A3VTR;S1dVsegs;VJA;S2eS33R14A1S32R14A1R13S2fR14A1A4A1S47R1bR19R18R17R5A5R4R3A5R12A2F_;F_;Ftp';Frho';FL;VTR;S1dVsegs;VJA;R10A1R15R12R11A5ReA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros Pre Ls Cl s R rho tp nd bd' Q CALLEE. intros.
  eapply (purec_callT_ag_xp (fun _ _ => True)); eauto.
  intros Ai rho1 tp1. eapply TR_pre; [|apply CALLEE]. intros w [Hsm [HJ _]]. exact (conj Hsm HJ).
Qed.

End CallT.
End Sum.
End WithSegs.
End TobjJAM2.

