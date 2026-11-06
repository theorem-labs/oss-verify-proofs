(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie m7 SegQtr SpineMallocI.

(* [comment removed for export] *)
Module UnwT_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "SVar"; "cell"; "ss_next"; "valuation"; "ss_objs"; "DUnknown"; "mkCell"; "mkObj"; "mkSS"; "obj_range"; "ranges_disjoint"; "rm"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "agree_below"; "outside_all"; "sv"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "list"; "Some"; "app"; "bool"; "option"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "le"; "add"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "xwords_clear"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "PRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue.WithSegs"; "carve_link_state"; "carve_plain_state"; "link_cells"; "link_obj"; "link_plain"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.

Definition link_plain (b : sv) : sobj := ltac2:(tb__ "0|0|
S9Vb;S1N10A1S1Z0A1S1fS3A1S7A5").
Definition link_cells (x : positive) : list cell := ltac2:(tb__ "0|1|
S1eS3S8S1N8A1Z8M0S2S2aVx;A1A1A3S1eS3S8S1N10A1G0S2Vx;A1A3S1fS3A1A3A3").
Definition link_obj (b : sv) (x : positive) : sobj := ltac2:(tb__ "0|0|
S9Vb;S1N10A1S1Z0A1S42Vx;A1S7A5").
Definition carve_plain_state (A : axst) (b : sv) : axst := ltac2:(tb__ "0|0|
S1bVA;A1S15S1cVA;SaS12R1A1S13R1A1S10R1A1SfR1A1S14R1A1S23S0S6R1A1S1eS0S44Vb;A1S1fS0A1A3A3SeR1A1S4R1A1S11R1A1A9A2TS;").

Definition carve_link_state (A : axst) (b : sv) : axst := ltac2:(tb__ "0|1|
S1bVA;A1S15S1cVA;SaS12R1A1S13R1A1S10R1A1SfR1A1S14R1A1S23S0S6R1A1S1eS0S43Vb;S4R1A1M0A2S1fS0A1A3A3SeR1A1S2aS2aG0A1A1S11R1A1A9A2TS;").

Lemma outside_of_disjoint : ltac2:(tb__ "0|2|
S5S21S0A1S1aS1aS38Q40M0A1S31S0S0ScSbR6R1A2S20S1aS1aR4R3A4A2Lo';R4A3S27S2cR4S39G0R2A2M1A2S2eG1R3A2A2S17R7R6R3A3F_;F_;Fa;Fhi;Flo;Fobjs;Frho;").
Proof.
  intros rho objs lo hi a HD Ha. unfold outside_all. eapply Forall_impl; [|exact HD].
  intros o Ho. cbv beta zeta. unfold ranges_disjoint in Ho. cbn [fst snd] in Ho. lia.
Qed.

Lemma carve_link : ltac2:(tb__ "0|6|
S35S1dS18S5S21S38Q40A1A1S21S3cA1M0S3aS3bS36Vsegs;S4S1bR7A1A1R8A3S28S24S19S1bS41R8R7A2A1A1S26A3S30R7R8A2S1aS2cS2dS3eZ10M1A2R1A2S2cR2S2fZ2Z3eA2A2S31S0S0ScSbRbR1A2S20S1aS1aS2bR4G1A2M2R4A4A2Lo';S6S1bRcA1A1A3S3fVsegs;SdRbA1G2R4A4S3dRcReS2bR5G1A2R5A4S34Vsegs;R10RfRdRcS20G0S32RbS33RaR9A2A4A6S29S5S5S27S16S4S1bR11A1A1M3RfR1A3S27S28S25S1aA1M4S37SdRfA1M5S2bR8G1A2A2S22S1aS30R1S2G3A1A2A2A3S27S28G4S37G5S2bR8Z8A2A2S22S1aS30R1S2S2aG3A1A1A2A2A3S34Vsegs;R12S40R11R10A2R1ReS20G0S32RdS33RcRbA2A4A6A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;TB;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fb;FA;FJ;").
Proof using HTOP.
  intros J A b rho tp tr ms md Hst Hwf B HBlo HBhi HD HP HX HS.
  pose proof (proj1 (proj1 HS)) as Hsm0.
  set (nx := ss_next (ax_S A)) in *.
  set (A0 := carve_plain_state A b) in *.
  set (objs := ss_objs (ax_S A)) in *. set (o := link_plain b). set (i := length objs).
  assert (Hobjs0 : ss_objs (ax_S A0) = objs ++ [o]) by (subst A0; destruct A; reflexivity).
  assert (Hnx0 : ss_next (ax_S A0) = nx) by (subst A0; destruct A; reflexivity).
  assert (Hb : sv_below nx b = true).
  { pose proof (swf_obj_nth (ax_S A0) i o Hwf ltac:(rewrite Hobjs0; apply nth_error_last)) as W. rewrite Hnx0 in W.
    unfold obj_wf in W. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. apply andb_prop in W as [W _]. exact W. }
  pose proof (uval_range rho b) as Rb.
  assert (Sm16 : forall r, soff r (SLit (-16)) = -16) by (intros r; apply soff_lit_small; lia).
  assert (S0 : forall r, soff r (SLit 0) = 0) by (intros r; apply soff_lit_small; lia).
  assert (Sm8 : forall r, soff r (SLit (-8)) = -8) by (intros r; apply soff_lit_small; lia).

  assert (FR : forall z, B - 16 <= z < B -> ms_mem (vms md tp ms) (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz. unfold virt in Hsm0. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm0.
    destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). apply Hfr.
    apply (outside_of_disjoint rho objs (B - 16) B); [exact HD|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite Z.mod_small by (change (2 ^ Z.of_N 64) with (2 ^ 64); unfold IMG_HI in HBlo; lia). exact Hz. }

  assert (SP0 : SPA segs J A0 rho tp (tr, mkCfg ms md)).
  { subst A0. unfold carve_plain_state.
    apply (SPA_carve_unk segs J rho A tp (tr, mkCfg ms md) b (SLit (-16)) (SLit 0) nx HS); try exact Hwf.
    - lia.
    - rewrite Sm16, S0. lia.
    - rewrite Sm16, S0. lia.
    - rewrite Sm16. fold (uval rho b). fold B. unfold IMG_HI in HBlo. lia.
    - rewrite S0. fold (uval rho b). fold B. lia.
    - rewrite Sm16, S0. fold (uval rho b). fold B. replace (B + -16) with (B - 16) by lia. replace (B + 0) with B by lia. exact HD.
    - rewrite Sm16, S0. fold (uval rho b). fold B. replace (B + -16) with (B - 16) by lia. replace (B + 0) with B by lia. exact HP.
    - rewrite Sm16, S0. fold (uval rho b). fold B. replace (B + -16) with (B - 16) by lia. replace (B + 0) with B by lia. exact HX. }

  destruct (SPA_add_cell8 segs J rho tp A0 i o (SLit (-16)) tr ms md) as (bs0 & rho1 & Hrd0 & Hag0 & Hev0 & SP1).
  { rewrite Hnx0. exact Hst. }
  { rewrite Hobjs0. apply nth_error_last. }
  { reflexivity. }
  { reflexivity. }
  { unfold obj_lo_of, o, link_plain. cbn [ob_lo]. rewrite !Sm16. lia. }
  { unfold obj_hi_of, o, link_plain. cbn [ob_hi]. rewrite Sm16, S0. lia. }
  { exact SP0. }
  set (A1 := ax_setS A0 (add_cell8_state (ax_S A0) i o (SLit (-16)))) in SP1.
  set (o1 := obj_add_cell o (SLit (-16)) 8 (SVar nx)).
  assert (Hobjs1 : ss_objs (ax_S A1) = objs ++ [o1]).
  { subst A1. rewrite ax_S_setS. unfold add_cell8_state. cbn [ss_objs]. rewrite Hobjs0, Hnx0. apply list_set_last. }
  assert (Hnx1 : ss_next (ax_S A1) = Pos.succ nx).
  { subst A1. rewrite ax_S_setS. unfold add_cell8_state. cbn [ss_next]. rewrite Hnx0. reflexivity. }

  destruct (SPA_add_cell8 segs J rho1 tp A1 i o1 (SLit (-8)) tr ms md) as (bs1 & rho2 & Hrd1 & Hag1 & Hev1 & SP2).
  { rewrite Hnx1. apply (stableA_mono segs nx); [lia | exact Hst]. }
  { rewrite Hobjs1. apply nth_error_last. }
  { reflexivity. }
  { reflexivity. }
  { unfold obj_lo_of, o1, o, link_plain, obj_add_cell. cbn [ob_lo]. rewrite Sm16, Sm8. lia. }
  { unfold obj_hi_of, o1, o, link_plain, obj_add_cell. cbn [ob_hi]. rewrite Sm8, S0. lia. }
  { exact SP1. }
  rewrite Hnx1 in Hag1, Hev1.
  exists rho2.
  assert (Hag : agree_below nx rho rho2).
  { eapply agree_below_trans; [exact Hag0|]. eapply agree_below_le; [|exact Hag1]. lia. }
  pose proof Hsm0 as (_ & _ & _ & _ & Hrom & _). cbn [virt fst snd cfg_ms cfg_model] in Hrom.
  assert (Eb0 : bv_unsigned (oaddr rho (ob_base o) (soff rho (SLit (-16)))) = B - 16).
  { unfold o, link_plain. cbn [ob_base]. rewrite Sm16. rewrite oaddr_unsigned by (fold (uval rho b); fold B; unfold IMG_HI in HBlo; lia). fold (uval rho b). fold B. lia. }
  assert (Eb1 : bv_unsigned (oaddr rho1 (ob_base o1) (soff rho1 (SLit (-8)))) = B - 8).
  { unfold o1, o, link_plain, obj_add_cell. cbn [ob_base]. rewrite Sm8.
    rewrite oaddr_unsigned by (rewrite <- (eval_agree nx rho rho1 b Hag0 Hb); fold (uval rho b); fold B; unfold IMG_HI in HBlo; lia).
    rewrite <- (eval_agree nx rho rho1 b Hag0 Hb). fold (uval rho b). fold B. lia. }
  split; [exact Hag|]. split; [|split].
  - rewrite <- Eb0. apply (add_cell8_value segs HTOP rho rho2 (vms md tp ms) _ bs0 (SVar nx) Hrom Hrd0); rewrite ?Eb0; [unfold IMG_HI in *; lia | lia | |].
    + intros z Hz. apply FR. lia.
    + rewrite <- Hev0. symmetry. apply (eval_agree (Pos.succ nx) rho1 rho2 (SVar nx) Hag1). cbn. apply Pos.ltb_lt. lia.
  - rewrite <- Eb1. apply (add_cell8_value segs HTOP rho rho2 (vms md tp ms) _ bs1 (SVar (Pos.succ nx)) Hrom Hrd1); rewrite ?Eb1; [unfold IMG_HI in *; lia | lia | |].
    + intros z Hz. apply FR. lia.
    + exact Hev1.
  - enough (EQS : ax_setS A1 (add_cell8_state (ax_S A1) i o1 (SLit (-8))) = carve_link_state A b) by (rewrite <- EQS; exact SP2).
    subst A1 A0. unfold carve_plain_state, carve_link_state, add_cell8_state. rewrite !ax_S_setS. cbn. rewrite !ax_setS_setS. cbn.
    subst i o1 o. fold objs. rewrite !list_set_last. reflexivity.
Qed.
End WithSegs.
End UnwT_glue.

(* [comment removed for export] *)
Module SegQI_side.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "N"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "le"; "add"; "pow"; "mul"; "div"; "lt"; "sub"; "eqb"; "land"; "leb"; "lxor"; "of_N"; "of_nat"; "lor"; "odd"; "shiftr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sv"; "valuation"; "SAlu"; "SExt"; "SAluW"; "SMdW"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "HIGH_SHADOW_END"; "kUserSpaceSize"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "cons"; "list"; "nat"; "nil"; "pair"; "prod"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "zsext"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_AND"; "ALU_OR"; "ALU_XOR"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side"; "ACQ"; "QI_side"; "szbig_z"; "zseq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "PostQI"; "PreQI"; "bgv"; "cls2T"; "dI1a"; "dI1b"; "dI2"; "dI6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "JQ"; "@Stdlib.NArith.BinNat.N"; "le"; "lt"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@LinuxProcessSemantics.Riscv.Sem"; "low32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side.Side"; "szbig_u"; "@Stdlib.Lists.List"; "In"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Notation UE rho e := (bv_unsigned (eval rho e)).

Definition ACQ : Z := 140737479966720.
Lemma alloc_ceiling_valQ : ACQ = 140737479966720. Proof. reflexivity. Qed.

Lemma U_and2 : ltac2:(tb__ "0|1|
S1cS1bS1bS3S0S7Q40M0S1aR3S1dS3bR2R1A3A2A2S12S7G0S1aR3R2A2A2S7G0S1aR3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.
Lemma U_or2 : ltac2:(tb__ "0|1|
S1cS1bS1bS3S0S7Q40M0S1aR3S1dS3cR2R1A3A2A2S17S7G0S1aR3R2A2A2S7G0S1aR3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_or_unsigned. reflexivity. Qed.
Lemma U_xor2 : ltac2:(tb__ "0|1|
S1cS1bS1bS3S0S7Q40M0S1aR3S1dS3dR2R1A3A2A2S14S7G0S1aR3R2A2A2S7G0S1aR3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.
Lemma U_sll2 : ltac2:(tb__ "0|3|
S1cS1bS1bS3S0S7Q40M0S1aR3S1dS3aR2R1A3A2A2S9SdS7G0S1aR3R2A2A2ScZ2M1S9S7G0S1aR3R1A2A2Z40M2A2A2A2ScG1G2A2A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 63) with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  unfold bv_wrap. reflexivity.
Qed.

Lemma low32_unsigned : ltac2:(tb__ "0|1|
S8Q40M0A1S3S0S7Q20S53R1A1A2S9S7G0R1A2ScZ2Z20A2A2A3Fv;").
Proof. intros v. unfold low32. rewrite bv_extract_0_unsigned. reflexivity. Qed.
Lemma sext64_unsigned : ltac2:(tb__ "0|2|
S8Q20M0A1S3S0S7Q40M1S52G0G1R1A3A2S31Z20S7G0R1A2A2A3Fv;").
Proof.
  intros v. unfold sext, zsext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ (32 - 1)) with (2 ^ 31).
  pose proof (bv_unsigned_in_range _ v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32) with (2 ^ 32) in R. unfold M64v.
  destruct (Z.ltb_spec (bv_unsigned v) (2 ^ 31)).
  - rewrite (Z.mod_small (bv_unsigned v + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small; lia.
  - replace ((bv_unsigned v + 2 ^ 31) mod 2 ^ 32) with (bv_unsigned v + 2 ^ 31 - 2 ^ 32).
    2:{ symmetry. rewrite <- (Z.mod_add _ (-1)) by lia. apply Z.mod_small. lia. }
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.
Lemma U_zext_e : ltac2:(tb__ "0|1|
S1cS1S1bS50R2Q40M0A2S3S0S7G0S1aR4S1eS2fR3R2A3A2A2S9S7G0S1aR4R2A2A2ScZ2S15R3A1A2A2A3F_;Fa;Fw;Frho;").
Proof. intros. cbn [eval]. apply U_zext_w. assumption. Qed.
Lemma U_sext_e : ltac2:(tb__ "0|2|
S1cS1S1bS51Q0R2A2S50R3Q40M0A2S3S0S7G0S1aR5S1eS27R4R3A3A2A2S31S15R4A1M1S9S7G0S1aR5R3A2A2ScZ2G1A2A2A2A3F_;F_;Fa;Fw;Frho;").
Proof. intros. cbn [eval]. apply U_sext_w; assumption. Qed.
Lemma U_sllw : ltac2:(tb__ "0|4|
S1cS1bS1bS3S0S7Q40M0S1aR3S1fS3aR2R1A3A2A2S31Z20M1S9SdS9S7G0S1aR3R2A2A2ScZ2M2G1A2M3A2ScG2S9S9S7G0S1aR3R1A2A2G3A2G1A2A2A2G3A2A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. rewrite sext64_unsigned. f_equal. unfold alu32, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 32 31) with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  unfold bv_wrap. reflexivity.
Qed.
Lemma U_divuw : ltac2:(tb__ "0|3|
S1cS1bS1bS6S3S0S9S7Q40M0S1aR3R1A2A2ScZ2Z20M1A2M2A2Z0A3A1S3S0S7G0S1aR4S20S3eR3R2A3A2A2S31G1SeS9S7G0S1aR4R3A2A2G2A2S9S7G0S1aR4R2A2A2G2A2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b Hb. cbn [eval]. rewrite sext64_unsigned. f_equal. unfold mul_div. rewrite !low32_unsigned.
  destruct (Z.eqb_spec (bv_unsigned (eval rho b) mod 2 ^ 32) 0) as [E|NE]; [contradiction|].
  cbn [Z.eqb]. destruct (bv_unsigned (eval rho b) mod 2 ^ 32 =? 0) eqn:E2; [apply Z.eqb_eq in E2; contradiction|].
  rewrite bv_divu_unsigned, !low32_unsigned. reflexivity.
Qed.

Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Lemma In_zseq : ltac2:(tb__ "0|0|
S2bS0S0S5S58S0R1S46R2R3A2A3S4SaR2R1A2SfR1SbR2S16R3A1A2A2A2A2Fz;Flo;Fn;").
Proof.
  induction n as [|n IH]; intros lo z; cbn [zseq].
  - split; [intros [] | intros; lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec lo z); [left; assumption | right]. apply IH. lia.
Qed.
Lemma range_check : ltac2:(tb__ "0|0|
S0S26F_;S0S2bS3S26S59S0R3S46R2R1A2A3S27A3S0S4SaR4R1A2SfR1SbR4S16R3A1A2A2A2S3S26R6R2A1S27A3F_;Fc;F_;Fn;Flo;FP;").
Proof. intros P lo n H c Hc. exact (proj1 (forallb_forall _ _) H c (proj2 (In_zseq n lo c) Hc)). Qed.

Definition size_ok (c : Z) : bool := ltac2:(tb__ "0|2|
S28S28S13Z10M0S23Vc;A1M1A2S13G1Z10000A2A2S11S9G1G0A2Z0A2A2").
Lemma size_ok_all : ltac2:(tb__ "0|2|
S0S4SaZ1R1A2SaR1Z1eA2A2S4S4SaZ10M0S23R2A1M1A2SaG1Z10000A2A2S3S0S9G1G0A2Z0A3A2F_;Fc;").
Proof.
  intros c Hc. pose proof (range_check size_ok 1 30 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) c ltac:(cbn; lia)) as H.
  unfold size_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Definition szbig_z (c : Z) : Z := ltac2:(tb__ "0|1|
SdZ200ScZ2M0SeS10Vc;Z10A2G0A2A2A2S0SbS26S0L_;S18Vc;A1SeR1G0A2Z0X26x2R1A2Tt;").
Definition szbig_ok (c : Z) : bool := ltac2:(tb__ "0|0|
S11S45Vc;A1S23Vc;A1A2").
Lemma szbig_all : ltac2:(tb__ "0|0|
S0S4SaZ11R1A2SaR1Z1eA2A2S3S0S45R2A1S23R2A1A3F_;Fc;").
Proof. intros c Hc. apply Z.eqb_eq. exact (range_check szbig_ok 17 14 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) c ltac:(cbn; lia)). Qed.

Lemma lxor3_low : ltac2:(tb__ "0|1|
S0SaZ0R1A2S3S0S9R2Z4A2Z3M0A3S3S0S14R3G0A2S10R3G0A2A3F_;F_;Fv;").
Proof.
  intros v Hv H3.
  assert (L : Z.land (v - 3) 3 = 0). { change 3 with (Z.ones 2) at 2. rewrite Z.land_ones by lia. change (2 ^ 2) with 4. lia. }
  replace v with ((v - 3) + 3) at 1 by lia. rewrite (Z.add_nocarry_lxor (v - 3) 3 L).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Section Side.
Variable rho : valuation.
Let U (i : positive) : Z := bv_unsigned (rw rho i).
Variables (x d : Z).
Hypothesis Hc : 1 <= U V_CLS <= 30.
Hypothesis Hsz : ltac2:(tb__ "0|0|
S3S0VU;S34A1S23VU;S33A1A1A3").
Hypothesis Hx : 0 <= x.
Hypothesis Hd : ltac2:(tb__ "0|0|
S4SaZ0Vd;A2SfVd;VU;S34A1A2A2").
Hypothesis Hm : ltac2:(tb__ "0|0|
S3S0VU;PdA1SbSbSbVU;P9bA1SdVU;S33A1ScZ2Z20A2A2A2SdVU;S34A1Vx;A2A2Vd;A2A3").
Hypothesis Hmu : ltac2:(tb__ "0|1|
SaSbSdVU;S34A1M0Vx;A2G0A2VU;P8aA1A2").
Hypothesis Hmu2 : U 138%positive <= kUserSpaceSize.
Hypothesis Hsb : HIGH_SHADOW_END <= U 155%positive.
Hypothesis Hceil : ltac2:(tb__ "0|0|
SaSbSbVU;PdA1Z10A2VU;P91A1A2S43A2").
Hypothesis Hm16 : U 13%positive mod 16 = 0.
Hypothesis Hhw : ltac2:(tb__ "0|1|
S4SfVU;P8bA1M0ScZ2Z20A2A2S3S0S9G0Z100A2Z3A3A2").
Hypothesis Hnlo : U 141%positive < 2 ^ 32.
Let nQ : Z := ltac2:(tb__ "0|1|
SbSdSeVU;P8bA1ScZ2M0Z10A2A2ScG0Z20A2A2VU;P8dA1A2").
Hypothesis Hn8 : ltac2:(tb__ "0|1|
S3S0VU;P91A1SdSeSbVnQ;Z7A2Z8M0A2G0A2A3").

Lemma Size_bounds : ltac2:(tb__ "0|2|
S4S4SaZ10M0VU;S34A1M1A2SaG1Z10000A2A2S3S0S9G1G0A2Z0A3A2").
Proof. rewrite Hsz. apply size_ok_all. exact Hc. Qed.

Let off : Z := ltac2:(tb__ "0|0|
SbSdVU;S34A1Vx;A2Vd;A2").
Lemma off_lt : 0 <= off < 2 ^ 32.
Proof. pose proof Size_bounds. unfold off, kUserSpaceSize, kRegionSize, kFreeArraySize in *. nia. Qed.
Lemma dm_val : ltac2:(tb__ "0|0|
S3S0S10VU;PdA1VU;P9bA1A2SbSdVU;S33A1ScZ2Z20A2A2Voff;A2A3").
Proof. unfold off. rewrite Hm. lia. Qed.
Lemma m_lt : U 13%positive < 2 ^ 47. Proof. pose proof alloc_ceiling_valQ. pose proof (urange (rw rho 145%positive)). unfold U in *. lia. Qed.
Lemma sb_lt : U 155%positive < 2 ^ 47. Proof. pose proof m_lt. pose proof off_lt. pose proof dm_val. nia. Qed.
Lemma land31 : ltac2:(tb__ "0|0|
S0SaZ0R1A2S3S0S12R2Z1fA2S9R2Z20A2A3F_;Fv;").
Proof. intros v Hv. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma cls2_val : ltac2:(tb__ "0|0|
S3S0S7Q40S1aVrho;S4aA2A2VU;S33A1A3").
Proof.
  unfold cls2T, dmS, vSB. rewrite U_srl_lit, U_sub. cbn [eval]. fold (U 13%positive) (U 155%positive). change (32 mod 64) with 32.
  pose proof dm_val as D. pose proof off_lt. pose proof m_lt. pose proof sb_lt. unfold M64v. rewrite Z.mod_small by lia. rewrite D.
  rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma side0 : diffs_ok rho dI0.
Proof.
  unfold diffs_ok, dI0. constructor; [|constructor; [|constructor]]; cbn [fst snd]; apply bv_eq.
  - unfold clsT. rewrite U_and2, U_lit. fold cls2T. rewrite cls2_val. change (31 mod M64v) with 31. rewrite land31 by (unfold U; apply urange).
    rewrite Z.mod_small; [reflexivity | lia].
  - rewrite cls2_val. reflexivity.
Qed.

Definition szsmall_ok (c : Z) : bool := ltac2:(tb__ "0|0|
S11S9SdVc;ScZ2Z5A2A2S30A2S23Vc;A1A2").
Lemma side1b : ltac2:(tb__ "0|0|
SfVU;S33A1Z11A2S35Vrho;S4cA2F_;").
Proof.
  intros H17. unfold diffs_ok, dI1b. constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
  unfold szSmallT, vCLS, vSZ. rewrite U_sll_lit. cbn [eval]. fold (U V_CLS) (U V_SIZE). rewrite Hsz. change (5 mod 64) with 5.
  apply Z.eqb_eq. exact (range_check szsmall_ok 1 16 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) (U V_CLS) ltac:(cbn; lia)).
Qed.

Definition szbig_u (c : Z) : Z := ltac2:(tb__ "0|4|
S9SbS12S9S19S32S9SdVc;ScZ2M0Z3fM1A2A2S30A2A1G1A2S30A2SeS9SdZ200ScG0S9SeS9SbVc;S9N10S30A2A2S30A2ScG0Z1A2M2A2Z40A2A2A2S30A2M3G2A2A2G3A2S30A2").
Definition szbigu_ok (c : Z) : bool := ltac2:(tb__ "0|0|
S11S57Vc;A1S23Vc;A1A2").
Lemma side1a : ltac2:(tb__ "0|0|
SaZ11VU;S33A1A2S35Vrho;S4bA2F_;").
Proof.
  intros H17. unfold diffs_ok, dI1a. constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
  unfold szBigT, add, vCLS, vSZ. rewrite U_add, U_and2, U_sra_lit, U_sll_lit, U_srl_lit, !U_sll2, !U_srl_lit, !U_add, !U_lit. cbn [eval]. fold (U V_CLS) (U V_SIZE).
  rewrite Hsz. apply Z.eqb_eq. exact (range_check szbigu_ok 17 14 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) (U V_CLS) ltac:(cbn; lia)).
Qed.

Lemma side3 : diffs_ok rho dI3.
Proof.
  pose proof m_lt as M.
  assert (E : forall k, 0 <= k < 2 ^ 31 -> UE rho (SAluW ALU_SLL (SLit k) m8T) = k).
  { intros k Hk. unfold m8T. rewrite U_sllw, U_sll_lit, U_lit. cbn [eval]. fold (U 13%positive). change (3 mod 64) with 3.
    set (sh := (((U 13%positive * 2 ^ 3) mod M64v) mod 2 ^ 32) mod 32). replace sh with 0 by (subst sh; unfold M64v; lia).
    rewrite Z.pow_0_r, Z.mul_1_r. unfold M64v. rewrite !Z.mod_small by lia. unfold zsext. change (2 ^ (32 - 1)) with (2 ^ 31).
    destruct (Z.ltb_spec k (2 ^ 31)); lia. }
  unfold diffs_ok, dI3. constructor; [|constructor; [|constructor]]; cbn [fst snd]; apply bv_eq; unfold sh3T, sh255T; rewrite E, U_lit; try reflexivity; lia.
Qed.

Lemma side5 : diffs_ok rho dI5.
Proof.
  pose proof m_lt as M. pose proof alloc_ceiling_valQ. pose proof (urange (rw rho 145%positive)) as R145. pose proof (urange (rw rho 13%positive)) as R13.
  assert (N8 : U 145%positive mod 8 = 0) by (rewrite Hn8; apply Z.mod_mul; lia).
  unfold diffs_ok, dI5. constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
  unfold lenT, LENq, add, vN8. rewrite U_sub, U_add, !U_srl_lit, !U_add, !U_lit. cbn [eval]. fold (U 13%positive) (U 145%positive).
  change (3 mod 64) with 3. change ((-8) mod M64v) with (M64v - 8). change (16 mod M64v) with 16. change (1 mod M64v) with 1.
  unfold U in *. set (m := bv_unsigned (rw rho 13%positive)) in *. set (n := bv_unsigned (rw rho 145%positive)) in *.
  rewrite (Z.mod_small (m + 16)) by (unfold M64v; lia). rewrite (Z.mod_small (m + 16 + n)) by (unfold M64v; lia).
  replace (m + 16 + n + (M64v - 8)) with (m + 8 + n + 1 * M64v) by lia. rewrite Z.mod_add by (unfold M64v; lia).
  rewrite (Z.mod_small (m + 8 + n)) by (unfold M64v; lia).
  replace ((m + 8 + n) / 2 ^ 3 + 1) with ((m + 16) / 2 ^ 3 + n / 2 ^ 3) by lia.
  rewrite (Z.mod_small (_ + _)) by (unfold M64v; lia).
  replace ((m + 16) / 2 ^ 3 + n / 2 ^ 3 - (m + 16) / 2 ^ 3) with (n / 2 ^ 3) by lia. apply Z.mod_small. unfold M64v; lia.
Qed.

Lemma side4 : diffs_ok rho dI4.
Proof.
  pose proof Hhw as [W1 W2]. assert (R139 : 0 <= U 139%positive < 2 ^ 64) by exact (urange _). assert (R141 : 0 <= U 141%positive < 2 ^ 64) by exact (urange _).
  assert (R145 : 0 <= U 145%positive < 2 ^ 64) by exact (urange _).
  unfold diffs_ok, dI4. constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
  unfold rup8T. rewrite (U_and_hmask rho _ 18446744073709551608 8 eq_refl). unfold nT, hw', add, vHW, vNlo, vN8.
  rewrite !U_add, !U_or2, !U_sll_lit, !U_zext_e, !U_srl_lit, !U_xor2, !U_sext_e, !U_lit by lia. cbn [eval]. fold (U 139%positive) (U 141%positive) (U 145%positive).
  change (Z.of_N 32) with 32. change (Z.of_N 16) with 16. change (16 mod 64) with 16. change (32 mod 64) with 32. change (3 mod M64v) with 3. change (7 mod M64v) with 7.
  rewrite (Z.mod_small (U 139%positive)) by lia. rewrite (Z.mod_small (U 141%positive)) by lia.
  assert (V : 3 <= zsext 32 (U 139%positive) /\ (zsext 32 (U 139%positive)) mod 4 = 3 /\ ((zsext 32 (U 139%positive) - 3) / 2 ^ 16) mod 2 ^ 16 = U 139%positive / 2 ^ 16).
  { unfold zsext, M64v. change (2 ^ (32 - 1)) with (2 ^ 31). destruct (Z.ltb_spec (U 139%positive) (2 ^ 31)).
    - split; [lia|]. split; [lia|]. rewrite Z.mod_small; lia.
    - split; [lia|]. split; [lia|].
      replace (U 139%positive + 18446744073709551616 - 2 ^ 32 - 3) with ((U 139%positive - 3) + (2 ^ 32 - 1) * 2 ^ 16 * 2 ^ 16) by lia.
      rewrite Z.div_add, Z.mod_add by lia. rewrite Z.mod_small; lia. }
  destruct V as (V1 & V2 & V3). rewrite lxor3_low by lia. rewrite V3.
  unfold M64v. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia.
  rewrite lor_disjoint_add; [| lia | lia | rewrite Z.land_comm; apply land_low_high; lia].
  fold nQ. rewrite !Z.mod_small by lia. unfold U in *. lia.
Qed.
Variable vb : bool.
Hypothesis Hbg : ltac2:(tb__ "0|0|
S3S0S7Q40S1aVrho;S49Vvb;A1A2A2S10VU;PdA1Vd;A2A3").

Lemma side6 : ltac2:(tb__ "0|0|
S35Vrho;S4eVvb;A1A2").
Proof.
  pose proof m_lt as M. pose proof sb_lt as SBL. pose proof off_lt as OL. pose proof dm_val as D.
  unfold diffs_ok, dI6. constructor; [|constructor]. cbn [fst snd]. apply bv_eq.
  unfold clsQCT, vSB. rewrite U_srl_lit, U_sll_lit, U_sub, Hbg. cbn [eval]. fold (U 155%positive) (U V_CLS). change (27 mod 64) with 27. change (59 mod 64) with 59.
  replace (U 13%positive - d - U 155%positive) with (U V_CLS * 2 ^ 32 + (off - d)) by lia.
  assert (0 <= off - d < 2 ^ 32) by (unfold off in *; nia). clearbody off. unfold M64v.
  rewrite (Z.mod_small (_ + _)) by lia.
  replace ((U V_CLS * 2 ^ 32 + (off - d)) * 2 ^ 27) with ((off - d) * 2 ^ 27 + U V_CLS * 2 ^ 59) by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma side2 : ltac2:(tb__ "0|0|
S35Vrho;S4dVvb;A1A2").
Proof.
  pose proof m_lt as M. pose proof sb_lt as SBL. pose proof off_lt as OL. pose proof dm_val as D. pose proof Size_bounds as (SZ1 & SZ2).
  assert (R138 : 0 <= U 138%positive < 2 ^ 64) by exact (urange _). assert (R155 : 0 <= U 155%positive < 2 ^ 64) by exact (urange _).
  unfold diffs_ok, dI2. constructor; [|constructor]. cbn [fst snd]. apply bv_eq. rewrite Hbg.
  assert (Q : UE rho qT = x).
  { unfold qT, dmS, vSB, vSZ. rewrite U_srl_lit, U_sll_lit, U_divuw, U_sub; cbn [eval]; fold (U 13%positive) (U 155%positive) (U V_SIZE).
    2:{ rewrite Z.mod_small; lia. }
    change (32 mod 64) with 32. unfold M64v. rewrite (Z.mod_small (U 13%positive - _)) by lia. rewrite D.
    rewrite Z.add_comm, Z.mod_add by lia. rewrite (Z.mod_small off) by lia. rewrite (Z.mod_small (U V_SIZE)) by lia.
    replace (off / U V_SIZE) with x. 2:{ unfold off. rewrite Z.mul_comm, Z.div_add_l, Z.div_small by lia. lia. }
    assert (X : 0 <= x < 2 ^ 28) by (unfold off in OL; nia).
    unfold zsext, M64v. change (2 ^ (32 - 1)) with (2 ^ 31). destruct (Z.ltb_spec x (2 ^ 31)); [|lia].
    rewrite Z.mod_small by lia. apply Z.div_mul. lia. }
  unfold s2T, add, vMU, vSZ, vCLS, vSB. rewrite U_and2, !U_add, U_sltu, !U_add, !U_mul, U_sll_lit, !U_lit, Q. cbn [eval].
  fold (U 13%positive) (U 155%positive) (U V_SIZE) (U V_CLS) (U 138%positive). change (32 mod 64) with 32. change ((-1) mod M64v) with (Z.ones 64).
  unfold off in *. set (o := U V_SIZE * x) in *. assert (0 <= o) by (subst o; nia). clearbody o. unfold M64v.
  rewrite (Z.mod_small o) by lia. rewrite (Z.mod_small (o + _)) by lia.
  destruct (Z.ltb_spec (U 138%positive) (o + U V_SIZE)); [lia|]. change (0 + Z.ones 64) with (Z.ones 64). change ((Z.ones 64) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small (U V_CLS * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + U 155%positive)) by lia.
  rewrite (Z.mod_small (_ + o)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Side.

Definition QI_side (rho : valuation) (vb : bool) (x d : Z) : Prop := ltac2:(tb__ "0|f|
S2S7Q40M0S21Vrho;R1A2A2Li;S2S0Fi;S4S4SaZ1R1S33A1M1A2SaG1Z1eA2A2S4S3S0R1S34A1M2S23G1A1A3S4SaZ0M3Vx;A2S4S4SaG3Vd;A2SfVd;G2A2A2S4S3S0R1PdA1M4SbSbSbR1P9bA1M5SdG1ScZ2M6Z20A2M7A2A2SdG2Vx;A2M8A2Vd;A2A3S4SaSbG8G2A2R1P8aA1M9A2S4SaG9S25A2S4SaS24G5A2S4SaSbSbG4Z10MaA2R1P91A1MbA2S43A2S4S3S0S9G4GaA2G3A3S4S4SfR1P8bA1McG7A2S3S0S9GcZ100A2Z3A3A2S4SfR1P8dA1MdG7A2S4S3S0GbSdSeSbSbSdSeGcScG6GaA2A2G7A2GdA2Z7A2Z8MeA2GeA2A3S3S0S7G0S1aVrho;S49Vvb;A1A2A2S10G4Vd;A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2TU;").

Theorem seg_QI_sound_clean : ltac2:(tb__ "0|1|
S26S40S56OF_;S1cS2aS8Q40A1A1S0S0S42S22R5R6A3S41S22S39R7A3S44R6R9R4R3A4S55S22R8S3fS22R9S48RaA1R7R6A5S38S22S39R7R6S29S2eS36S37A2M0S2dS36S37S47RaA1S4fR9A1A4S2cG0A1A3A5A4F_;F_;F_;Fd;Fx;Ftp;Frho;Fok;FJ;Fvb;").
Proof.
  intros vb J ok rho tp x d HOK HST (Hc & Hsz & Hx & Hd & Hm & Hmu & Hmu2 & Hsb & Hceil & Hm16 & Hhw & Hnlo & Hn8 & Hbg).
  apply (seg_QI_sound vb J ok rho tp HOK HST).
  - apply (side0 rho x d); assumption.
  - intros H17. apply (side1a rho x d); assumption.
  - intros H17. apply (side1b rho x d); assumption.
  - apply (side2 rho x d); assumption.
  - apply (side3 rho x d); assumption.
  - apply (side4 rho x d); assumption.
  - apply (side5 rho x d); assumption.
  - apply (side6 rho x d); assumption.
Qed.
Theorem seg_QI_complete_clean : ltac2:(tb__ "0|1|
S26S40S1cS2aS8Q40A1A1S0S0S41S22S39R5A3S44R5R7R3R2A4S54S22S3fS22R7S48R8A1R6R5A5S38S22S39R6R5S29S2eS36S37A2M0S2dS36S37S47R8A1S4fR7A1A4S2cG0A1A3A5A3F_;F_;Fd;Fx;Ftp;Frho;FJ;Fvb;").
Proof.
  intros vb J rho tp x d HST (Hc & Hsz & Hx & Hd & Hm & Hmu & Hmu2 & Hsb & Hceil & Hm16 & Hhw & Hnlo & Hn8 & Hbg).
  apply (seg_QI_complete vb J rho tp HST).
  - apply (side0 rho x d); assumption.
  - intros H17. apply (side1a rho x d); assumption.
  - intros H17. apply (side1b rho x d); assumption.
  - apply (side2 rho x d); assumption.
  - apply (side3 rho x d); assumption.
  - apply (side4 rho x d); assumption.
  - apply (side5 rho x d); assumption.
  - apply (side6 rho x d); assumption.
Qed.
End SegQI_side.

(* [comment removed for export] *)
Module SegQ3_post.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "bool"; "true"; "None"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "FcsrFrm0"; "mkSS"; "sobj"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3_post"; "PostQ3r"; "PostsQ3"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "NXQ"; "post_ru"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel"; "PostQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "JLQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "RETR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "F_T0"; "regs3"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PostQ3r : axst := ltac2:(tb__ "0|0|
S24S11S26S21S28S1cA2S20S10SbSfA1S5S12S25S23A3S27S1bScA9S6S8SfSfA2A1A2").
Definition PostsQ3 (K : AA -> jpredA) (A : AA) : list (axst * jpostA) := ltac2:(tb__ "0|2|
S5S8S0S3A2M0S7S0S3S1dS1eSeVK;VA;A3M1A4S5G0S7S0S3S15G1A4S6G0A1A3A3").
Lemma PostQ3r_wf : ltac2:(tb__ "0|0|
S18S17S9S2S15A1SaA3S17S9S13S1S15A1A1SaA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma LQPA_PostsQ3 : ltac2:(tb__ "0|1|
S19S22F_;S19S14SdS29Q40A1A1S1fS4SeS1aR3R2S5S8S0S3A2M0S7S0S3S1dS1eSeR5R4A3A4S6G0A1A3R1A6S4SeS1aR4R3S16R6R5A2R2A6F_;Fw;Ftp;Frho;FA;FK;").
Proof. intros K A rho tp w (L & JL & rho' & tp' & [E|[]] & H). injection E as <- <-. exists PostQ3, (JLQ3 segsA K A), rho', tp'. split; [left; reflexivity | exact H]. Qed.
End SegQ3_post.

(* [comment removed for export] *)
Module SegQ3RM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "bool"; "true"; "list"; "app"; "false"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "ss_next"; "SLit"; "SVar"; "cell"; "ss_lenient"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "PreR2"; "idm"; "MH"; "MS1"; "Ts0M"; "TsP2"; "TskM"; "runP2"; "M0"; "MPM"; "Mk"; "regsR2"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "Head0"; "Headk"; "LEXIT"; "LHEAD"; "MERGE"; "PD"; "QCHK"; "Xg"; "F_R"; "PH"; "PM"; "PX"; "STK"; "SW00"; "Ts0"; "Tsk"; "mkR"; "run0"; "runS1"; "runk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "LSLOW"; "vGB"; "vGF"; "vGN"; "vGS"; "NX3"; "O_gmax"; "O_gq"; "O_mtx"; "RECY"; "vMIN"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition idm (l : list positive) : vmap := ltac2:(tb__ "0|0|
S30S9S3S9S14A2S9S1S9S14R1S19R1A1A4Lv;Vl;A4").

Definition regsR2 : list sv := setregs regs3 re_ru.
Definition PreR2 : axst := ltac2:(tb__ "0|1|
S43S50S2dS7S16S3fS2S1aA1S40A2S0S16S4fS18Z100A1A1S0S16S4dS2S16A1M0A3A3A3S0S16S4eS4aS49S48S4bA4G0A3S3bS4cA6").
Definition runP2 : list leafA := ltac2:(tb__ "0|0|
S31U258S0SaS36S0SaS35S0SaS37S0SaS47S0SaS39S2SaA1A3A3A3A3A3S22A3").
Lemma runP2_eq : ltac2:(tb__ "0|0|
S12S6SeA1S31U258S0SaS36S0SaS35S0SaS37S0SaS47S0SaS39S2SaA1A3A3A3A3A3S22A3S29A3"). Proof. unfold runP2. reflexivity. Qed.
Definition MH : vmap := ltac2:(tb__ "0|1|
S0S3S9S14A2M0S1S9S14Pa0S4aA4S0G0S1S9S14Pa1S49A4S0G0S1S9S14Pa2S48A4S0G0S1S9S14Pa3S4bA4S0G0S1S9S14Pd0S51A4S2G0A1A3A3A3A3A3").
Definition MPM : vmap := ltac2:(tb__ "0|0|
S23S0S9PccS0S9PcdS0S9PceS0S9PcfS0S9Pd0S2S9A1A3A3A3A3A3A1").
Definition TsP2 : list (axst * vmap) := ltac2:(tb__ "0|3|
S0S3SbSfA2M0S1SbSfS3eS24A4M1S0G0S1SbSfS3cS24A4M2S0G0G1S0G0G2S0G0S1SbSfS3dS2bA4S2G0A1A3A3A3A3A3").
Lemma chkP2 : ltac2:(tb__ "0|0|
S12S4S10S17ScS22A1A1S29S27A3S5A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxP2 : ltac2:(tb__ "0|1|
S13S12S4S1bScS22A1M0A1S8A3S52S32S17G0A1A2A2").
Proof. split; [reflexivity | unfold Pos.le; cbn; discriminate]. Qed.
Lemma preR2_wf : ltac2:(tb__ "0|0|
S13S12S4SdS22A1S5A3S12S4S1cScS22A1A1S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition M0 : vmap := ltac2:(tb__ "0|0|
S23S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pa3S0S9Pa4S0S9Pa5S0S9Pd0S2S9A1A3A3A3A3A3A3A3A1").
Definition Mk : vmap := ltac2:(tb__ "0|0|
S23S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pa3S0S9Pa4S0S9Pa5S0S9Pa6S0S9Pa7S0S9Pa8S0S9Pa9S0S9PaaS0S9Pc0S0S9Pc1S0S9Pd0S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1").
Definition MS1 : vmap := ltac2:(tb__ "0|0|
S23S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A1").
Definition Ts0M : list (axst * vmap) := ltac2:(tb__ "0|0|
S30SbS3SbSfA2SbS1SbSfR1S2aA4LT;S41A4").
Definition TskM : list (axst * vmap) := ltac2:(tb__ "0|0|
S30SbS3SbSfA2SbS1SbSfR1S2cA4LT;S42A4").
Lemma chk0M : ltac2:(tb__ "0|0|
S12S4S10S17ScS33A1A1S44S26A3S5A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkkM : ltac2:(tb__ "0|0|
S12S4S10S17ScS34A1A1S46S28A3S5A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkS1M : ltac2:(tb__ "0|1|
S12S4S10S17ScS3aA1A1S45S0S3SbSfA2M0S1SbSfS38S25A4S2G0A1A3A3S5A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_R_P2 : ltac2:(tb__ "0|0|
S1eS15S6S2fQ40A1A1S21VQ;VX;R3A3SbSfS15S2eS3SbSfA2S1SbSfR3R2A4S27A3S11R3R7R2A3S20VQ;VX;S1dS1fR9R5R3R7A5A3F_;F_;Frho';FM;FT;S20VQ;VX;S1dS1fR5S22R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 600%nat _ PreR2 runP2 TsP2 runP2_eq chkP2 (proj1 nxP2) (proj2 nxP2) J rho tp HJ HC). Qed.
Theorem seg_R_I0M : ltac2:(tb__ "0|0|
S1eS15S6S2fQ40A1A1S21VQ;VX;R3A3SbSfS15S2eS3SbSfA2S1SbSfR3R2A4S26A3S11R3R7R2A3S20VQ;VX;S1dS1fR9R5R3R7A5A3F_;F_;Frho';FM;FT;S20VQ;VX;S1dS1fR5S33R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ Head0 run0 Ts0M run0_eq chk0M (proj1 (proj1 (proj2 nxs))) (proj2 (proj1 (proj2 nxs))) J rho tp HJ HC). Qed.
Theorem seg_R_IkM : ltac2:(tb__ "0|0|
S1eS15S6S2fQ40A1A1S21VQ;VX;R3A3SbSfS15S2eS3SbSfA2S1SbSfR3R2A4S28A3S11R3R7R2A3S20VQ;VX;S1dS1fR9R5R3R7A5A3F_;F_;Frho';FM;FT;S20VQ;VX;S1dS1fR5S34R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ Headk runk TskM runk_eq chkkM (proj1 (proj1 (proj2 (proj2 nxs)))) (proj2 (proj1 (proj2 (proj2 nxs)))) J rho tp HJ HC). Qed.
Theorem seg_R_S1M : ltac2:(tb__ "0|1|
S1eS15S6S2fQ40A1A1S21VQ;VX;R3A3SbSfS15S2eS3SbSfA2M0S1SbSfR3R2A4S0G0S1SbSfS38S25A4S2G0A1A3A3S11R3R7R2A3S20VQ;VX;S1dS1fR9R5R3R7A5A3F_;F_;Frho';FM;FT;S20VQ;VX;S1dS1fR5S3aR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ Xg runS1 [(PD, MS1)] runS1_eq chkS1M (proj1 (proj1 (proj2 (proj2 (proj2 nxs))))) (proj2 (proj1 (proj2 (proj2 (proj2 nxs))))) J rho tp HJ HC). Qed.
End TR.
End SegQ3RM.

(* [comment removed for export] *)
Module SpineMallocS1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "land"; "modulo"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "SVar"; "swf"; "SLit"; "agree_below"; "rm"; "sprop_below"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "true"; "pair"; "app"; "cons"; "nil"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C1g"; "F_gen"; "V_ND"; "V_RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "rzf_rz"; "rzf_hi"; "rzf_lo"; "F_hi"; "F_lo"; "F_s1"; "neededx"; "s1_cuts"; "s1_exits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1.SPINE1"; "JG"; "d_k"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Wcan"; "ulink"; "AE_A"; "J_alloc_preT"; "Kc_ok"; "Pre_mallocI"; "UStopLeOrPc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "needed8"; "rhoM_of"; "sa_m"; "sb_m"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.Lists.List"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "d_k"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rz_fam : ltac2:(tb__ "0|0|
S7S7S6S0Z0R2A2S0R2Z7A2A2S6S0S25R3A1R2A2S1R2S24R3A1A2A2S5S7S4eR3A1S23R4A1A3F_;F_;Fn;Fk;").
Proof.
  intros k n Hk Hn. unfold rz, rz_log.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as C by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [rzf_lo rzf_hi rzf_rz] in Hn |- *;
    repeat match goal with |- context [n <=? ?c] => destruct (Z.leb_spec n c); try lia end; reflexivity.
Qed.
Lemma needed8_fam : ltac2:(tb__ "0|1|
S7S7S6S0Z1R2A2S0R2Z7M0A2A2S6S0S25R3A1R2A2S1R2S24R3A1A2A2S5S7S40R3A1S2S3S2R3G0A2Zfffffffffffffff8A2S23R4A1A2A3F_;F_;Fn;Fk;").
Proof.
  intros k n Hk Hn. unfold needed8. rewrite (rz_fam k n) by lia.
  assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  assert (9 <= n < 64513) by (destruct C as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [rzf_lo rzf_hi] in Hn; lia).
  rewrite Z.max_l by lia. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia.
  unfold round_up. change (2 ^ 3) with 8.
  pose proof (Z_div_mod_eq_full (n + 7) 8). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia.
Qed.
Lemma needed8_0 : ltac2:(tb__ "0|0|
S7S6S0Z1R1A2S1R1Z9A2A2S5S7S40R2A1Z18A3F_;Fn;").
Proof.
  intros n Hn. unfold needed8. rewrite (rz_fam 0 n) by (cbn; lia). rewrite Z.max_r by lia. reflexivity.
Qed.
Lemma needed8_bounds : ltac2:(tb__ "0|2|
S7S7S6S0Z0M0R2A2S0R2Z7A2A2S6S0S25R3A1R2A2S1R2S24R3A1A2A2S6S6S0Z18S40R3A1M1A2S0G1Z10000A2A2S6S5S7S4G1Z8A2G0A3S0S2R3S23R4A1A2G1A2A2A2F_;F_;Fn;Fk;").
Proof.
  intros k n Hk Hn. destruct (Z.eq_dec k 0) as [->|Hk0].
  - cbn [rzf_lo rzf_hi] in Hn. rewrite needed8_0 by lia. cbn. lia.
  - rewrite (needed8_fam k n) by lia. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3).
    assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct C as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [rzf_lo rzf_hi rzf_rz] in Hn |- *; rewrite land_high_mask by lia; change (2 ^ 3) with 8;
      pose proof (Z_div_mod_eq_full (n + 7) 8); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia));
      (split; [lia|]); (split; [|lia]);
      replace (n + 7 - (n + 7) mod 8) with (8 * ((n + 7) / 8)) by lia; rewrite <- Z.add_mod_idemp_l by lia;
      rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity.
Qed.

Section SPINE1.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S37VAInv;VW;Vst;VA;VKc;SbPcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S3fSaS11S45Q40A1A1S48VAInv;R4R3R2R1A4S50S52Vsegs;SfR4A1A2S51Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Definition JG (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) (rho : valuation) : jpredA := ltac2:(tb__ "0|0|
S4aSaSeS46S41VA;Vrho;A2R1A3Lr;VJ;VW;Vst;VA;VKc;A4A2").

Variable nW : nat.
Variable st : ustop.
Variable tmax : Z.
Let W : list ulink := Wcan nW.

Definition d_k (k : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S17S13S8S8A2M0S15S8S8S29Vk;A1SbS1eA1A4M1S17G0G1S17G0S15S8S8SdS23Vk;A1A1SbS1fA1A4S18G0A1A3A3A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S5S12ScS1bS1cVW;Vst;Vtmax;A3A1A1S14A3").
Hypothesis DC1 : ltac2:(tb__ "0|3|
S7S6S0Z0R1A2S0R1Z7A2A2S5S1aS13S11S13S8S8A2A1M0S11S9A1M1A2M2A1S31S1bS22VW;Vst;Vtmax;R2A4A1S1bS1cVW;Vst;Vtmax;A3A1A2S19G2S15G0G1S2dR2A1S1dA4A2A3F_;Fk;").

Lemma e_s1_c1g : ltac2:(tb__ "0|0|
S7S3fS33SaS11S45Q40A1A1S2fSaS6S0Z0R7A2S0R7Z7A2A2S20Vsegs;S2cVW;Vst;R7R6R5A5S22VW;Vst;Vtmax;R8A4R2R4R3A6S20Vsegs;S2cVW;Vst;R8R7R6A5S1cVW;Vst;Vtmax;A3R3R5R4A6F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fk;").
Proof.
  intros k A Kc rho tp w rhoE Hk H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.

  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HF : Forall (holds rhoE) (F_fam tmax k)).
  { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S E_s1]. apply in_or_app. right. exact Hp. }
  unfold F_fam in HF. pose proof (Forall_inv HF) as F1. pose proof (Forall_inv (Forall_inv_tail HF)) as F2.
  cbn [holds eval] in F1, F2. rewrite E12 in F1, F2. fold nv in F1, F2.
  assert (KB : 0 <= rzf_lo k <= 64513 /\ 0 <= rzf_hi k <= 64513 /\ 16 <= rzf_rz k <= 1024 /\ rzf_rz k mod 16 = 0).
  { assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn; lia. }
  destruct KB as (Rlo & Rhi & RZB1 & RZB2).
  rewrite u64_lit in F1 by lia. rewrite u64_lit in F2 by lia.
  pose proof (needed8_bounds k nv Hk (conj F1 F2)) as (NB & NA & NR). pose proof (rz_fam k nv Hk (conj F1 F2)) as RZ.
  assert (Hnv64 : nv <= 64512) by lia.
  change (C1g W st tmax) with (ax_setS (E_s1 W st tmax k) (ax_S (C1g W st tmax))).
  eapply SPA_restate; [exact WC1 | exact (DC1 k Hk) | reflexivity | | | exact H].
  -
    assert (EN : eval rhoE (neededx k) = Z_to_bv 64 (needed8 nv)).
    { unfold neededx. destruct (Z.eq_dec k 0) as [->|Hk0].
      - cbn [Z.eqb eval]. rewrite needed8_0 by (cbn in F1, F2; lia). reflexivity.
      - replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (k =? 8) with false by (symmetry; apply Z.eqb_neq; lia).
        unfold rup8. cbn [eval]. rewrite E12. apply bv_eq. rewrite add_val, and_val, add_val, !u64_lit by lia. fold nv.
        rewrite (Z.mod_small (nv + 7)) by lia. rewrite (needed8_fam k nv) by lia.
        change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia.
        pose proof (Z.mod_pos_bound (nv + 7) (2 ^ 3) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
    unfold diffs_ok, d_k, V_ND, V_RZ.
    apply Forall_cons; [cbn [fst snd]; rewrite EN; cbn [eval]; rewrite E157; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite EN; cbn [eval]; rewrite E157; reflexivity|].
    apply Forall_cons; [cbn [fst snd eval]; rewrite E150, RZ; reflexivity|]. apply Forall_nil.
  -
    unfold F_gen, V_RZ, V_ND. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E150, ?E157, ?E12, ?RZ; fold nv;
      rewrite ?u64_lit by lia; try lia.
    + rewrite add_val, !u64_lit by lia. fold nv. rewrite Z.mod_small by lia. lia.
Qed.

Hypothesis Cert1 : ltac2:(tb__ "0|0|
S5S12S49S4fUfa0S17S7Z40bacS18S7A1A3S46S2aVnW;Vst;A2S2bVnW;Vst;Vtmax;A3A6S14A3").

Theorem spine_s1 : ltac2:(tb__ "0|8|
S2fOF_;S3fS33SaS11S45Q40A1A1S30S5S3eVst;S3aA3S5S11S35A1VW;S18S35A1A3F_;S44VW;Vst;A2S38R6A1S21Vsegs;R9VJ;VW;Vst;R8R7A4A3S5S12ScS42VW;Vst;A2M0A1S14A3S5S1aS13S11S13S8S8A2M1A1M2S11S9A1M3A2M4A1S31S1bS39S36VW;Vst;A3M5A1G0A2S19G4S15G2G3S17G1S15S8S8SbP18A1SdS4dA1A4S18G1A1A3S18S9A1A4A2A3S5S12ScS43VW;Vst;A2A1S14A3S5S12S47S9S10S4cA1M6S16S9S16S9S16S9S16S9S3dVW;Vst;A2S3cS3bA1A3S4bA3S28A3M7S26A3A3S14A3S5S12S47S9G6S16S9G7S27A3A3S14A3SaS2eVsegs;R10S20Vsegs;S2cVW;Vst;RfReRdA5S1cVW;Vst;Vtmax;A3R1RcA5RbA4FrhoE;SaS2eVsegs;R11S20Vsegs;S2cVW;Vst;R10RfReA5S22VW;Vst;Vtmax;Z8A4R1RdA5RcA4FrhoE;S2eVsegs;R11S20Vsegs;VJ;VW;Vst;R10RfA4G5ReRdA5RcA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HW HUS HKc Hokf Wa Da Wb Fbh Fbl HC1 HSEC.
  eapply triple_conseq; [intros w Hw; exact (m_instantiate law_die W st A Kc rho tp w HW HUS Wa Da Wb Fbh Fbl Hw) | intros w Hw; exact Hw |].
  set (P0 := P0_s1 W st (if Z_lt_dec (bv_unsigned (rw rho 12%positive)) 64513 then F_lo else F_hi)).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW P0 (rhoM_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x40bac] GW (s1_cuts nW st) (s1_exits nW st tmax) (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert1.
  - intros E rhoE HinE. unfold s1_exits in HinE. cbn [map] in HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
    9: { eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HSEC]. }
    all: eapply triple_conseq; [intros w Hw; eapply (e_s1_c1g _ A Kc rho tp w rhoE); [|exact Hw]; lia | intros w Hw; right; exact Hw | apply HC1].
  - unfold s1_cuts, P0. destruct (Z_lt_dec _ _); [right; left; reflexivity | left; reflexivity].
Qed.
End SPINE1.

Lemma WC1_0 : ltac2:(tb__ "0|0|
S5S12ScS1bS1cS34U0A1S32Z2A3A1A1S14A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_0 : ltac2:(tb__ "0|5|
S7S6S0Z0R1A2S0R1Z7A2A2S5S1aS13S11S13S8S8A2A1M0S11S9A1M1A2M2A1S31S1bS22S34U0A1M3S32Z2M4R2A4A1S1bS1cG3S32G4A3A1A2S19G2S15G0G1S53R2A1S1dA4A2A3F_;Fk;").
Proof.
  intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
End SpineMallocS1.

(* [comment removed for export] *)
Module CallocBase.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "sprop"; "@Corelib.Init.Datatypes"; "list"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "unwind_stopJ"; "ustop"; "chain_pre"; "unwind_factsS"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Iface ContractFreeNull SpineMallocI.
Import ListNotations.
Open Scope Z_scope.

Definition stopJ_w (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
S1S1S4SeR1SbA2SaS10Q40A1S0R3R2A2S0R4R2A2A3F_;Fi;S6VW;Vst;R3A3M0G0F_;F_;Frho';Frho;").
Lemma stopJ_w_le : forall W, stopJ_w W UStopLe.
Proof. intros W rho rho' _ H. unfold unwind_stopJ in *. destruct W; exact I. Qed.
Lemma stopJ_w_nil : forall st, stopJ_w [] st.
Proof. intros st rho rho' _ H. exact H. Qed.
Lemma stopJ_w_1pc : stopJ_w (Wcan 1) UStopLeOrPc.
Proof.
  intros rho rho' He H. unfold unwind_stopJ, Wcan, Wcan_from, last_link, link_var in *. cbn [nth eval] in *.
  rewrite !He by (unfold NF; first [lia | discriminate]). exact H.
Qed.
Lemma stopJ_w_stable : ltac2:(tb__ "0|0|
S3S5A1S7ScR2R1A2S11R3R2A2F_;Fst;FW;").
Proof. intros W st H rho rho' (Hw & _ & _) HU. apply (H rho rho'); [|exact HU]. intros i Hi. symmetry. exact (Hw i Hi). Qed.

Lemma stopJ_w_ge : ltac2:(tb__ "0|0|
S3S5A1S7S4ScR3R2A2SfSbR2A2S1S1S4SeR1R6A2SaS10Q40A1S0R3R2A2S0R4R2A2A3F_;Fi;S6R8R7R3A3S6R9R8R3A3F_;F_;Frho';Frho;F_;F_;Fg;Fst;FW;").
Proof. intros W st g H Hg rho rho' He HU. apply (H rho rho'); [|exact HU]. intros i Hi. apply He. lia. Qed.

Lemma chain_pre_factsS' : ltac2:(tb__ "0|0|
S3S5A1S7S2SdS2R1S8R3A1A3SdS2R2S9R4R3A2A3F_;Fp;Fst;FW;").
Proof. intros W st p Hp. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l W']; [apply chain_pre_in; exact Hp | exact Hp]. Qed.

Ltac hw_discharge := first [ apply stopJ_w_le | exact stopJ_w_1pc | apply stopJ_w_nil | (let E := fresh "E" in intros E; discriminate E) ].
End CallocBase.

