(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "sprop"; "obj_range"; "holds"; "SLit"; "ob_base"; "ob_hi"; "ob_lo"; "sv_eqb"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "nat"; "option"; "false"; "fst"; "snd"; "None"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "ltb"; "add"; "leb"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "tvinA"; "frinA"; "fbinA"; "ffinA"; "TPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "xrs_okL"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "remove_nth"; "T_ok"; "tvz"; "tvd"; "T0"; "robj_tracked"; "robj_stack"; "tnz"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.WithSegs"; "robj_stackA2"; "robj_tpiece"; "robjs_checkP"; "robj_stackA2_p"; "robjs_checkP_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "uleq_pf"; "mk_pf"; "pfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "xrs_okA"; "cmaddrA"; "is_shadowZ"; "robjs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "xrs_ok47"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robj_ownframe"; "robjs_checkF"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "robj_stack_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymDigFast SymObjFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV XformFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S24S5SfS33Q40A1A1S2fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S58Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S46VCST;R1A2S18S1cZ0R2A2S1dR2S45A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S46VXGL;R1A2S18S1cZ0R2A2S1dR2S45A2A2F_;Fa;").
Variable rho0 : valuation.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SfS10S10S0S0A2S0A2A1").

Definition robj_stackA2 (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|9|
SeSeL_;M0S3cVfacts;Vo;A2S3SeLx;SbVo;A1S0G0S21Z0M1R1A2G0S1fR1S1eZ2M2Z28A2M3A2S3fVfacts;SaVo;A1M4G1S9S23S1eG2Z2fA2M5R1A2A1A4S14Xex2G0S1fS22G3A1R1A2S3fVfacts;G4G1S9G5A1A4S14Xex2Xex2Lhi;S1S14Li;S47S3S3S14Lb;La;M6Lop;M7G7S48G6Lop;M8G8SeS2S3S14La;Lw;Lsgn;S1S3S0S14Lk;Li;Ll;X3x8S14Xex2").

Lemma robj_stackA2_sound : ltac2:(tb__ "0|1|
SfS6A1S5S0S4S0S34S6S8R4A1R5A3S37R5R4A2S19SeS40R7R4A2S11A3S18S1cS15S0S0S7R7R5A2M0A3R4A2S1dR4S16S0S0G0A3A2A2S18S1cR7R5A2S1dR5S1eZ2Z2fA2A2A2F_;F_;F_;F_;Fa;Fo;FT;Frho;Ffacts;").
Proof using .
  clear. intros facts rho T o a HF HT H Hr. unfold robj_stackA2 in H. apply lazy_andb_prop in H as [H1 H2].
  split; [exact (robj_stack_sound facts rho T o a HF HT H1 Hr)|].
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Ehi in Hr. cbn [fst snd] in Hr.
  destruct (Z.leb_spec 0 hi) as [H0|H0].
  - apply lazy_andb_prop in H2 as [H4 H5]. apply Z.ltb_lt in H4.
    pose proof (uleq_sound rho facts _ 0 _ HF H5) as U5. unfold U in U5. rewrite U_lit in U5. unfold M64v in U5.
    rewrite Z.mod_small in U5 by lia. rewrite (soff_lit_small rho hi) in Hr by lia. lia.
  - apply lazy_andb_prop in H2 as [H4 H5]. apply Z.ltb_lt in H4.
    pose proof (uleq_sound rho facts _ 0 _ HF H5) as U5. unfold U in U5. rewrite U_lit in U5. unfold M64v in U5.
    rewrite Z.mod_small in U5 by lia. rewrite (soff_lit_small rho hi) in Hr by lia. lia.
Qed.

Definition robj_tpiece (facts : list sprop) (tv : list (sv * sv)) (o : sobj) : bool := ltac2:(tb__ "0|4|
S32S10S3S3A2M0G0SeSeL_;M1SdSaVo;A1S15S3S3R1A3A2G1S3fVfacts;ScVo;A1Z0M2SbVo;A1M3A4S3fVfacts;G3G2S16S3S3R1A3A4S14Xex2S14Xex2Lt;Vtv;A3").

Lemma robj_tpiece_sound : ltac2:(tb__ "0|4|
S24S5SfS33Q40A1A1S2fSfS6A1S5SfS10S3S3A2M0A1S4S0VAInv;R9R8R7R6A4S34S6S8R5A1R6A3S27VFB;RbR6R5A4S38R7R6A2S19SeS41R9R7R6A3S11A3S18S1cS15S0S0S7R9R7A2M1A3R6A2S1dR6S16S0S0G1A3A2A2S1bG0G0S18S30G0R1RaA3S18S3dRbR1A2S18S1cS15S0S0S3eRbR1A2M2A3M3R8A2S1dR8S20G3S16S0S0G2A3A2A2A2A2A2Lt;A2F_;F_;F_;F_;F_;F_;Fa;Fo;Ftv;Frho;Ffacts;Fmd1;Ftp1;Frho1;FAi;").
Proof using ALA.
  intros Ai rho1 tp1 md1 facts rho tv o a HM HF HN HZ H Hr.
  unfold robj_tpiece in H. apply existsb_exists in H as (t & Ht & Hc).
  apply lazy_andb_prop in Hc as [Hb Hc]. apply lazy_andb_prop in Hc as [H1 H2]. apply sv_eqb_sound in Hb.
  pose proof (uleq_sound rho facts _ 0 _ HF H1) as U1. pose proof (uleq_sound rho facts _ 0 _ HF H2) as U2. unfold U in U1, U2.

  assert (Hsz : bv_unsigned (eval rho (snd t)) < 2 ^ 62).
  { destruct (Z.eq_dec (bv_unsigned (eval rho (fst t))) 0) as [Z0|NZ].
    - pose proof (proj1 (Forall_forall _ _) HZ t Ht) as Z1. cbv beta in Z1. unfold tnz, tvv in Z1. cbn [snd] in Z1. rewrite (Z1 ltac:(lia)). lia.
    - destruct (proj1 (Forall_forall _ _) HN t Ht NZ) as (_ & Hin & _).
      destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & HBl & _). destruct (HBl _ _ Hin) as (B1 & _ & B3 & B4 & _).
      top_rng B4. unfold tvv in B4. cbn [fst snd] in B4. unfold tvv in B3. cbn [fst] in B3. lia. }
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb in Hr. cbn [fst snd] in Hr.
  rewrite (soff_smallu rho (ob_hi o)) in Hr by (unfold uval; lia). rewrite (soff_smallu rho (ob_lo o)) in Hr by (unfold uval; lia).
  unfold uval in Hr.
  exists t. split; [exact Ht|].
  assert (Hnz : tnz rho t).
  { intros Z0. pose proof (proj1 (Forall_forall _ _) HZ t Ht) as Z1. cbv beta in Z1. unfold tvv in Z1. cbn [snd] in Z1.
    unfold tnz in Z1. specialize (Z1 (fun H => H Z0)). pose proof (bv_urange (eval rho (ob_lo o))). lia. }
  split; [exact Hnz|]. unfold tvv. cbn [fst snd]. pose proof (bv_urange (eval rho (ob_lo o))). lia.
Qed.

Definition robjs_checkP_ref (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat)
           (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S31S4S4SeSeL_;M0S40Vfacts;R1A2S11G0S3bVtv;S17S12A1R1A3S11G0S41Vfacts;Vtv;R1A3S11G0S53Vfr;U0Vskip;R1A4S11Vextra;R1A1Xex2Xex2Xex2Xex2Lo;VR;A3").

Definition robj_stackA2_p (pf : pfacts) (o : sobj) : bool := ltac2:(tb__ "0|9|
SeSeL_;M0S57Vpf;Vo;A2S3SeLx;SbVo;A1S0G0S21Z0M1R1A2G0S1fR1S1eZ2M2Z28A2M3A2S49Vpf;SaVo;A1M4G1S9S23S1eG2Z2fA2M5R1A2A1A4S14Xex2G0S1fS22G3A1R1A2S49Vpf;G4G1S9G5A1A4S14Xex2Xex2Lhi;S1S14Li;S47S3S3S14Lb;La;M6Lop;M7G7S48G6Lop;M8G8SeS2S3S14La;Lw;Lsgn;S1S3S0S14Lk;Li;Ll;X3x8S14Xex2").
Lemma robj_stackA2_p_eq : ltac2:(tb__ "0|0|
SfS6A1S4S19SeS43S4aR2A1R1A2S40R2R1A2A3Fo;Ffacts;").
Proof using . intros facts o. unfold robj_stackA2_p, robj_stackA2. rewrite robj_stack_p_eq. reflexivity. Qed.
Definition robjs_checkP (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat)
           (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S56Vfacts;A1S4bS31S4S4SeSeL_;M0S43R2R1A2S11G0S3bVtv;S17S12A1R1A3S11G0S41Vfacts;Vtv;R1A3S11G0S53Vfr;U0Vskip;R1A4S11Vextra;R1A1Xex2Xex2Xex2Xex2Lo;VR;A3Tpf;").
Lemma robjs_checkP_ref_eq : ltac2:(tb__ "0|0|
SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2A1S13S12A1S4SeF_;SfS4A1S19SeS42R6R5R4R3R2R1A6S44R6R5R4R3R2R1A6A3FR;Fextra;Fskip;Ffr;Ftv;Ffacts;").
Proof using .
  intros facts tv fr skip extra R. unfold robjs_checkP, robjs_checkP_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq.
  induction R as [|o r IH]; cbn [forallb]; [reflexivity|]. rewrite robj_stackA2_p_eq, IH. reflexivity.
Qed.

Lemma robjs_checkP_ref_sound : ltac2:(tb__ "0|7|
S24S5SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2M0A1M1S13S12A1M2S4SeF_;SfS4A1S5SfS33Q40A1A1S2fVAInv;RbR3R2R1A4S34S6S8RbA1RaA3S37RcS3aVrho0;A1A2S27VFB;ReRdRbA4S39ReRcA2S38RfRdA2S28VFF;R11R10RdA4S19SeS44R10RfReRdRcRbA6S11A3G2G1Lskip;ReS12S36G0R1R10A3Li;RfX13x2G1S4S0S30S4R2RfA3S19SeR11R3A1S11A3S18S1cS15S0S0S7R17R4A2M3A3R3A2S1dR3S16S0S0G3A3A2A2S2cVCST;Vrho0;S35VFB;R18R16A3M4S2dVFF;R18R6A3M5R4A5F_;F_;F_;Fa;Fo;S4S0S30S4R2R10A3S18S1cS15S0S0S7R17R3A2M6A3R2A2S1dR2S16S0S0G6A3A2A2S2cVCST;Vrho0;G4G5R3A5F_;F_;Fa;Fo;F_;Tfrs;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk frs Hextra o a Ho Hr.
  unfold robjs_checkP_ref in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; exact (robj_stackA2_sound facts rho _ o a HF HT0 Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { destruct (robj_tracked_sound tv None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
    destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha Hpos]. pose proof (nth_error_In _ _ Hj) as Hin.
    assert (Hnz : tnz rho t) by (intros Hz0; pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz0)); lia).
    right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
    apply In_FBx. right. exists t. rewrite <- surjective_pairing. auto. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { destruct (robj_tpiece_sound Ai rho1 tp1 md1 facts rho tv o a HM HF HN HZ Hc Hr) as (t & Ht & Hnz & Ha).
    right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
    apply In_FBx. right. exists t. rewrite <- surjective_pairing. auto. }
  apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra o a Ho Hc Hr)].
  destruct (robj_ownframe_sound fr 0 skip o Hc) as (j & x & lo & hi & Hj & Hsk & Hb & Hl & Hh & H1 & H2 & H3 & Hc6). rewrite Nat.add_0_l in Hsk.
  pose proof (nth_error_In _ _ Hj) as Hinx.
  pose proof (proj1 (Forall_forall _ _) (proj1 HFR) x Hinx) as (X1 & _ & _).
  destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFrl).
  destruct (HFrl _ _ X1) as (_ & _ & _ & F4 & F5 & _). top_rng F5.
  assert (Hin' : In x frs).
  { subst frs. destruct skip as [i|]; [|exact Hinx]. eapply In_remove_nth_ne; [exact Hj | intros ->; apply Hsk; reflexivity]. }
  right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split.
  - apply In_FFx. right. exists x. split; [exact Hin' | reflexivity].
  - unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
    pose proof (fs_frame_size_bounds (snd (fst x))) as B.
    unfold frv in *. cbn [fst snd] in *. unfold uval in *. unfold IMG_HI, HIGH_SHADOW_END in *.
    pose proof (fs_frame_size_bounds' (snd (fst x)) Hc6) as Bsz.
    rewrite !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. lia.
Qed.

Lemma robjs_checkP_sound : ltac2:(tb__ "0|7|
S24S5SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2M0A1M1S13S12A1M2S4SeF_;SfS4A1S5SfS33Q40A1A1S2fVAInv;RbR3R2R1A4S34S6S8RbA1RaA3S37RcS3aVrho0;A1A2S27VFB;ReRdRbA4S39ReRcA2S38RfRdA2S28VFF;R11R10RdA4S19SeS42R10RfReRdRcRbA6S11A3G2G1Lskip;ReS12S36G0R1R10A3Li;RfX13x2G1S4S0S30S4R2RfA3S19SeR11R3A1S11A3S18S1cS15S0S0S7R17R4A2M3A3R3A2S1dR3S16S0S0G3A3A2A2S2cVCST;Vrho0;S35VFB;R18R16A3M4S2dVFF;R18R6A3M5R4A5F_;F_;F_;Fa;Fo;S4S0S30S4R2R10A3S18S1cS15S0S0S7R17R3A2M6A3R2A2S1dR2S16S0S0G6A3A2A2S2cVCST;Vrho0;G4G5R3A5F_;F_;Fa;Fo;F_;Tfrs;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk. rewrite robjs_checkP_ref_eq in Hchk.
  exact (robjs_checkP_ref_sound Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk).
Qed.

Lemma pclMA_lt47 : ltac2:(tb__ "0|1|
S24S5SfS33Q40A1A1S2fSfS10S0S0A2M0A1SfS10G0S0A2A1S0VAInv;R7R6R5R4A4S29R4R8A2S2aR4R9A2S2cVCST;Vrho0;R6R5R4A5S18S1cZ0R5A2S1dR5S1eZ2Z2fA2A2A2F_;F_;F_;F_;Fa;FFFc;FFBc;Fmd1;Ftp1;Frho1;FAi;").
Proof using ALA HCST.
  intros Ai rho1 tp1 md1 FBc FFc a HM HB HFF [H|[H|[(b & n & Hin & Hr)|(f & sz & fl & Hin & Hr)]]].
  - unfold T0 in H. pose proof (bv_urange (rw rho0 Contract.V_TOP)). lia.
  - pose proof (HCST a (proj1 H)). unfold IMG_HI, LOW_SHADOW_BEG in *. lia.
  - destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & HBl & _). destruct (HBl b n (HB _ Hin)) as (B1 & _ & B3 & B4 & _).
    top_rng B4. lia.
  - destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFr). destruct (HFr f sz (proj1 (HFF _ _ _ Hin))) as (_ & _ & F3 & F4 & F5 & _).
    top_rng F5. unfold IMG_HI in F4. lia.
Qed.

Lemma fbinA_FBx_node : ltac2:(tb__ "0|0|
S24S5SfS10S3S3A2A1S29VFB;R3A2S27VFB;R4R3R2A4S29S35VFB;R4R3A3R5A2F_;F_;Ftv;Frho;FAi;").
Proof using . intros Ai rho tv HB HN. apply (fbinA_FBx FB Ai rho tv []); [exact HB | rewrite app_nil_r; exact HN]. Qed.

Lemma ffinA_FFx_node : ltac2:(tb__ "0|3|
S24S5SfS10S10S3S0A2S3A2M0A1M1S13S12A1M2S2aVFF;R4A2S28VFF;R5R4R3A4S2aS2dVFF;R5G2G1Lskip;R3S12S36G0R1R5A3Li;R4X13x2A3R6A2F_;F_;Fskip;Ffr;Frho;FAi;").
Proof using .
  intros Ai rho fr skip HFF HFR. apply (ffinA_FFx_sub FF Ai rho fr); [exact HFF | exact HFR |].
  destruct skip as [i|]; [|intros x Hx; exact Hx]. intros x Hx. exact (In_remove_nth _ _ _ Hx).
Qed.

Lemma pclMA_cmaddrA_node : ltac2:(tb__ "0|3|
S24S5SfS10S3S3A2A1SfS10S10S3S0A2S3A2M0A1M1S13S12A1M2S0S29VFB;R6A2S2aVFF;R7A2S2bVrho0;R8A2S27VFB;R9R8R7A4S28VFF;RaR9R7A4S2cVCST;Vrho0;S35VFB;RaR9A3S2dVFF;RaG2G1Lskip;R7S12S36G0R1R9A3Li;R8X13x2A3R6A5S4eVCST;RcS17S0A1R7A4F_;F_;F_;F_;F_;F_;Fa;Fskip;Ffr;Ftv;Frho;FAi;").
Proof using .
  intros Ai rho tv fr skip a HB HFF HT HN HFR H.
  exact (pclMA_cmaddrA CST rho0 _ _ Ai a (fbinA_FBx_node Ai rho tv HB HN) (ffinA_FFx_node Ai rho fr skip HFF HFR) HT H).
Qed.

Lemma robjsP_okA : ltac2:(tb__ "0|4|
S24S5SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2M0A1M1S13S12A1M2S4SeF_;SfS4A1S5SfS33Q40A1A1S2fVAInv;RbR3R2R1A4S34S6S8RbA1RaA3S2bVrho0;RdA2S37RdS26S25ReA1A1A2S29VFB;RfA2S2aVFF;R10A2S27VFB;R11R10ReA4S39R11RfA2S38R12R10A2S28VFF;R14R13R10A4S19SeS42R13R12R11R10RfReA6S11A3S4S0S30S4R2R11A3S19SeR13R3A1S11A3S18S1cS15S0S0S7R19R4A2M3A3R3A2S1dR3S16S0S0G3A3A2A2S2cVCST;Vrho0;S35VFB;R1aR18A3S2dVFF;R1aG2G1Lskip;R16S12S36G0R1R18A3Li;R17X13x2A3R4A5F_;F_;F_;Fa;Fo;S50VCST;R17S17S0A1R16R10A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF HT HTK HB HFF HN HD HZ HFR Hchk Hextra o a Ho Hr.
  apply (pclMA_cmaddrA_node Ai rho tv fr skip a HB HFF HT HN HFR).
  exact (robjs_checkP_sound Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF (T_ok_T0 rho0 rho Ai HT HTK) HN HD HZ HFR Hchk Hextra o a Ho Hr).
Qed.

Lemma robjsP_okF : ltac2:(tb__ "0|1|
S24S5SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2A1S4SeF_;SfS4A1S5SfS33Q40A1A1S2fVAInv;RaR3R2R1A4S34S6S8RaA1R9A3S2bVrho0;RcA2S37RcS26S25RdA1A1A2S27VFB;ReRdRbA4S39ReRcA2S38RfRdA2S28VFF;R11R10RdA4S19SeS54R10RfReS17S12A1RdRcA6S11A3S4S0S30S4R2RfA3S19SeR11R3A1S11A3S18S1cS15S0S0S7R16R4A2M0A3R3A2S1dR3S16S0S0G0A3A2A2S2cVCST;Vrho0;S35VFB;R17R15A3S2dVFF;R17R14A3R4A5F_;F_;F_;Fa;Fo;S52VCST;Vrho0;VFB;VFF;R13R11R10ReA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk Hextra o a Ho Hr.
  apply (robjs_checkF_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv fr None extra R rho1 tp1 md1 HM HF (T_ok_T0 rho0 rho Ai HT HTK) HN HD HZ HFR Hchk) with (o := o); [|exact Ho|exact Hr].
  intros o' a' Ho' HE Hr'. left. exact (Hextra o' a' Ho' HE Hr').
Qed.

Lemma robjsP_hse : ltac2:(tb__ "0|4|
S24S5SfS6A1SfS10S3S3A2A1SfS10S10S3S0A2S3A2A1S4SeF_;SfS4A1S5SfS33Q40A1A1S2fVAInv;RaR3R2R1A4S34S6S8RaA1R9A3S2bVrho0;RcA2S37RcS26S25RdA1A1A2S27VFB;ReRdRbA4S39ReRcA2S38RfRdA2S28VFF;R11R10RdA4S19SeS54R10RfReS17S12A1RdRcA6S11A3S4S0S30S4R2RfA3S19SeR11R3A1S11A3S18S1cS15S0S0S7R16R4A2M0A3R3A2S1dR3S16S0S0G0A3A2A2S2cVCST;Vrho0;S35VFB;R17R15A3M1S2dVFF;R17R14A3M2R4A5F_;F_;F_;Fa;Fo;S4S0S30S4R2R10A3S18S1cS15S0S0S7R16R3A2M3A3R2A2S1dR2S16S0S0G3A3A2A2S1aS2cVCST;Vrho0;G1G2R3A5S1aS18S1cZ0R3A2S1dR3S45A2A2S4fR3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk Hextra o a Ho Hr.
  destruct (robjsP_okF Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk Hextra o a Ho Hr) as [H|H]; [left; exact H|].
  right. left. exact H.
Qed.

Lemma xrs_okL_okA : ltac2:(tb__ "0|4|
S24S5SfS10S3S3A2A1M0SfS10S10S3S0A2S3A2M1A1M2S13S12A1M3G0S29VFB;R6A2S2aVFF;R7A2S2bVrho0;R8A2S27VFB;R9R8R7A4S28VFF;RaR9R7A4S2eVCST;VXGL;Vrho0;VFB;VFF;RaR9G3G2Lskip;R7S12S36G1R1R9A3Li;R8X13x2R6A9S4dVCST;VXGL;RcS17S0A1RbR7A6F_;F_;F_;F_;F_;F_;FX;Fskip;Ffr;Ftv;Frho;FAi;").
Proof using .
  intros Ai rho tv fr skip X HB HFF HT HN HFR HX r a Hr Ha. destruct (HX r a Hr Ha) as [H|H]; [|right; exact H].
  left. exact (pclMA_cmaddrA_node Ai rho tv fr skip a HB HFF HT HN HFR H).
Qed.

Lemma xrs_okL_ok47 : ltac2:(tb__ "0|4|
S24S5SfS33Q40A1A1S2fS5SfS10S3S3A2A1M0SfS10S10S3S0A2S3A2M1A1M2S13S12A1M3G0VAInv;R9R8R7R6A4S29VFB;RaA2S2aVFF;RbA2S27VFB;RcR8R7A4S28VFF;RdR9R7A4S2eVCST;VXGL;Vrho0;VFB;VFF;RaR9G3G2Lskip;R7S12S36G1R1R9A3Li;R8X13x2R6A9S51RbR7A2F_;F_;F_;F_;F_;F_;FX;Fskip;Ffr;Ftv;Frho;Fmd1;Ftp1;Frho1;FAi;").
Proof using ALA HCST HXGL.
  intros Ai rho1 tp1 md1 rho tv fr skip X HM HB HFF HN HFR HX r a Hr Ha. destruct (HX r a Hr Ha) as [H|H].
  - exact (pclMA_lt47 Ai rho1 tp1 md1 _ _ a HM (fbinA_FBx_node Ai rho tv HB HN) (ffinA_FFx_node Ai rho fr skip HFF HFR) H).
  - pose proof (HXGL a H). unfold IMG_HI, LOW_SHADOW_BEG in *. lia.
Qed.

Lemma xrs_checkL_okA : ltac2:(tb__ "0|6|
S24S5SfS6A1SfS10S3S3A2M0A1M1SfS10S10S3S0A2S3A2M2A1M3S13S12A1M4SfS4A1G0SeF_;G1S5SfS33Q40A1A1S2fVAInv;RcR3R2R1A4S34S6S8RcA1RbA3S2bVrho0;ReA2S37ReS26S25RfA1A1A2S29VFB;R10A2S2aVFF;R11A2S27VFB;R12R11RfA4S39R12R10A2S38R13R11A2S28VFF;R15R14R11A4S19SeS55VXGL;R14R13R12R11R10RfReA8S11A3G0S0S30G0R2R11A3S19SeR13R3A1S11A3S18S1cS4cR1aS15S3S3R4A3A2M5R3A2S1dR3S20G5S4cR1aS16S3S3R4A3A2A2A2A2S1aS2cVCST;Vrho0;S35VFB;R1bR19A3S2dVFF;R1bG4G3Lskip;R17S12S36G2R1R19A3Li;R18X13x2A3R4A5S46VXGL;R4A2A2F_;F_;F_;Fa;Fr;S18S4dVCST;VXGL;R18S17S0A1R17R10A6S51R17R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fextra;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST HXGL.
  intros Ai rho facts tv fr skip objs extra X rho1 tp1 md1 HM HF HT HTK HB HFF HN HD HZ HFR Hchk Hextra.
  pose proof (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extra X rho1 tp1 md1 HM HF (T_ok_T0 rho0 rho Ai HT HTK) HN HD HZ HFR Hchk Hextra) as HX.
  split; [exact (xrs_okL_okA Ai rho tv fr skip X HB HFF HT HN HFR HX) | exact (xrs_okL_ok47 Ai rho1 tp1 md1 rho tv fr skip X HM HB HFF HN HFR HX)].
Qed.
End WithSegs.
