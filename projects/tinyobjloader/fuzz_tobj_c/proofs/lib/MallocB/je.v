(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu ji.

(* [comment removed for export] *)
Module RebuildR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_mapped_user"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "AA"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Datatypes"; "length"; "option"; "Some"; "nat"; "app"; "bool"; "list"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "Sh"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "region_info"; "@Stdlib.Lists.List"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "bandtp_inv"; "live_ids"; "model_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ"; "envR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "refillA"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma view_rm_off : ltac2:(tb__ "0|2|
S26Q40M0A1S1fS26Q8A1A1M1F_;S0SbS2Z0R1A2S3R1S6Z2Z40A2A2A2SeS3R2S2aA2S2S29R2A2A2ScG1S9S3dR4R3A3R4S27G0R3A2A1A3F_;F_;Fa;Ff;").
Proof.
  intros f a Ha Hoff. rewrite view_in by exact Ha. unfold rd_of.
  destruct (f (Z_to_bv 64 a)) as [b|]; [reflexivity|]. apply image_byte_A_off2; [exact Ha|]. unfold IMG_LO, IMG_HI in Hoff. lia.
Qed.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma refill_rebuild : ltac2:(tb__ "0|d|
S15S1dS1dS24S26Q40M0A1A1M1G1S28S28S0S0OF_;VAInv;R9R8R6R4A4SbS2Z1R3A2S2R3Zfc00A2A2ScS23S17RbA1S25A3S18RcA1S1bS1aR1A1S0S19R2A1S0S44R8A1S0S45R10R9A2S16S41R2R1A2S16S40R12R3A2S15S1S1R6Zd0A2S5Z50R4A2A2S0S37R6R5A2S0S34R7R6A2S0S36R8R7A2S0S9Vsegs;S1cR15A1A2SaS9Vsegs;S1cR17A1A2SaS3fRaR8S22S0S3bRdR19RaA3S42RdS43R19A1RaA3A3A3S2S12RaA1S12R9A1A2S2S10RbA1S10RaA1A2S2S11RcA1S11RbA1A2S2S4S1eS0S13RcA1A2A1S35ReA1A2S0SeR17R1A1M2SdG2A1A2Fz;S0R18R1A1S3eR13R14R12S4S1eS0S14R11A1A2A1S10R11A1R2A6F_;Fz;S0SdR19R1A1A1ScS1fS26Q8A1M3A1M4RbR2A1RaR2A1A3F_;Fz;S0R1aR1A1SfG3G3ScG4RdR3A1S20G3R1A2A3Lb;A2F_;Fz;S0SbS2S2aR1A2S3R1S29A2A2ScG4S1cR22S27G0R2A2M5A2S1cR23G5A2A3F_;Fa;S7RcS8S1RfS32A2U8M6Z0M7A3A2S7RdS8S1R10S33A2G6S4S1eS0S14R13A1A2A1A3A2S7ReS8S1R11S2fA2G6S11R14A1A3A2S7RfS8S1R12S2dA2G6S12R15A1A3A2S7R10S8S1R13S2cA2G6G7A3A2S7R11S8S1R14S31A2G6S10R17A1A3A2S7R12S8S1R15S30A2G6G7A3A2S7R13S8S1R16S2eA2U1G7A3A2S21S0ScS1fS0A1M8S38S0S14R1cA1R2A3S20S0R1A2M9A3S7R17S8S1R19S5Z4S4R3A1A2MaA2U4MbR2A3A2F_;Fx;Fi;S7R15S8R19GbS4S1eS0S13R1bA1A2A1A3A2S21S0ScG8S38S0S13R1eA1R2A3G9A3S7R19S8S1S1R1dZ10A2GaA2GbR2A3A2F_;Fx;Fi;S0SbS2S1R19S10R1fA1McA2R1A2S3R1S1R19S10R1eA1A2A2A2R28R2A1F_;Fz;S0SbS2S2bS1R1aS10R20A1A2A1R1A2S3R1S2bS1R1aGcA2A1A2A2R29R2A1F_;Fz;S0SbS2S1R1cS11R21A1A2R1A2S3R1S1R1cS11R20A1A2A2A2R2aR2A1F_;Fz;S3cVsegs;R1fR2dR2bA4S3aR1bR2eA2SbVAInv;R21R31R2fR2dA4S39VCST;VXGL;R33R21S1cR32A1S1cR31A1A6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Trb;Tfa;Tri;Tpce;TAr;TcsR;Tcs;Tc;TSB;TT;TG;F_;F_;F_;FZN;Fnv;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md nv ZN HA Hnv Hini G T SB c cs csR Ar pce ri fa rb v3 vE
         HPURE HAUm HMUm HMFm HKC ZND HZE VO PRES HRMI R1' R2' R3' R4' R5' R6' R7' R8' HFA HCN HCC HNU HNS HNF HMD HBT.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). fold c in C1, C2, C3, C4.
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.
  assert (GS : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ SB mod 2 ^ 16 = 0
               /\ (ag_fsb G + 11571200 <= SB \/ SB + 2 ^ 37 + 4096 <= ag_fsb G)).
  { pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X. fold SB in X. clear -X. tauto. }
  destruct GS as (S1 & S2 & S3 & S4).
  pose proof (geom_bands _ HG) as (WF & TB & CB & DB & TI & CTI & DTI). fold G T in TB, TI. fold G in WF, CB, DB, CTI, DTI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in WF, TB, CB, DB, TI, CTI, DTI. rewrite FS_total_val in WF.
  pose proof HI3 as HI3c. destruct HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3). fold G in SG3, SEC3, Q3, DEP3.
  pose proof SG3 as SG3c. destruct SG3 as (T3 & CTX3 & DTLS3 & PAB3 & PABT3 & _). rewrite kSpaceSize_val in T3, CTX3, DTLS3, PAB3, SEC3. fold T in T3, PABT3. fold SB in T3, CTX3, DTLS3, PAB3.

  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & Hia & HTH & Hmisc). pose proof Hprim as Hprim0.
  destruct Hprim as (PL & P0 & P31 & PC).
  pose proof (PC c C1) as PCc. fold G in PCc. change (nthZ (aa_cls A) c cs_empty) with cs in PCc.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (mu := cs_mapped_user cs) in *.
  unfold class_repr in PCc. cbv zeta in PCc. fold SB in PCc. fold ri fa rb in PCc. fold mu nf in PCc.
  destruct PCc as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & R9 & PR & N7 & PU & PSH & PE & ND & LV & CI & CN' & TI10 & CV10 & MC10 & FC10).
  destruct (cap_facts c C1) as (SZc & SZ16 & MCU & _ & FCU & _).
  destruct HPURE as (Q1 & Q2 & Q3' & Q4 & Q4' & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  assert (GEO : geoR SB T (topG G)).
  { unfold geoR. clear -S1 S2 TG G4 G5 T3 TB. lia. }
  assert (ENVB : 0 <= nf /\ 0 <= mu <= 2 ^ 32 - 2 ^ 29).
  { unfold nf. pose proof (Zle_0_nat (length (cs_free_array cs))). unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N3. clear -H N2 N3. lia. }
  destruct ENVB as (NF0 & MUB).
  assert (NF4 : 4 * nf <= 2 ^ 29) by (unfold kFreeArraySize in N6; clear -N6; lia).
  assert (NZE : forall z, ~ envR SB T c nf mu z -> v3 z = vE z) by (intros z Hz; apply VO; intros Hc; exact (Hz (HZE z Hc))).

  assert (ENVF : forall z, envR SB T c nf mu z -> fs_footb G z = false).
  { intros z Hz. destruct (env_where SB T (topG G) c nf mu z GEO C1 NF0 MUB Hz) as [W|[W|[W _]]].
    - apply fs_footb_space; [exact HG0 | rewrite kSpaceSize_val; fold G SB; clear -W; lia].
    - apply fs_footb_thread; [exact HG0 | fold G T; clear -W; lia].
    - apply fs_footb_space_sh; [exact HG0 | rewrite kSpaceSize_val; fold G SB].
      pose proof (Geometry.Sh_mono (SB + 2 ^ 37) (SB + 2 ^ 37 + 4096) ltac:(clear; lia)) as SM. clear -W SM. lia. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ envR SB T c nf mu z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (NZE z Hz)]. }
  assert (CHm : forall z, envR SB T c nf mu z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (ENVF z Hz). }
  assert (MSP : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_space; [exact HG0 | rewrite kSpaceSize_val; fold G SB; exact Hz]. }
  assert (MTH : forall z, T <= z < T + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_thread; [exact HG0 | fold G T; clear -Hz; lia]. }
  fold mE in Hlive, PC, Hsec, Hq, Hdep, Hia, HTH, Hmisc, R1, R2, R3, R4, R5, R6, R7, R8, PRI, R9, PR, PU, PSH, PE, CI.
  assert (PRES3 : forall z, ZN z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite (CHm z (HZE z Hz)). exact (PRES z Hz). }
  assert (AGZ : forall z, ~ ZN z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGZ z Hn); exact (Hp z Hz)]. }
  assert (PRESB : forall lo hi L, present_but mE lo hi L -> present_but m3 lo hi L).
  { intros lo hi L Hp z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGZ z Hn); exact (Hp z Hz HL)]. }
  assert (CELL : forall a w v, (forall k, (k < w)%nat -> ~ envR SB T c nf mu (a + Z.of_nat k)) -> cell_ok mE (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). }

  assert (Hlenc : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; clear -C1; lia).
  assert (ECS' : nthZ (aa_cls Ar) c cs_empty = csR).
  { unfold Ar, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlenc. reflexivity. }
  assert (ECSo : forall c', c' <> c -> 0 <= c' -> nthZ (aa_cls Ar) c' cs_empty = nthZ (aa_cls A) c' cs_empty).
  { intros c' Hc' Hc'0. unfold Ar, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_other; [reflexivity|]. clear -Hc' Hc'0 C1. lia. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  assert (HQP : q_pure A) by exact (proj1 (quarantine_repr_pure mE A HG Hq)).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }

  assert (NE_img : forall z, IMG_LO <= z < IMG_HI -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. unfold IMG_LO, IMG_HI in Hz.
    apply (env_out SB T (topG G) c nf mu 65536 6565888 z GEO C1 NF0 MUB Hz); [clear -S1; lia | clear -TI; lia | clear; lia | exact Hc]. }
  assert (NE_T : forall z, (T <= z < T + 208 \/ T + 2688 <= z < T + 4096) -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. destruct Hz as [Hz|Hz].
    - apply (env_out SB T (topG G) c nf mu T (T + 208) z GEO C1 NF0 MUB Hz); [clear -T3; lia | clear; lia | clear -TB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (T + 2688) (T + 4096) z GEO C1 NF0 MUB Hz); [clear -T3; lia | clear; lia | clear -TB; lia | exact Hc]. }
  assert (NE_sec : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> ~ envR SB T c nf mu z).
  { intros i ch z Hi Hz Hc. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D8.
    destruct D10 as (D10a & D10l & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
    destruct Hz as [Hz|Hz].
    - apply (env_out SB T (topG G) c nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO C1 NF0 MUB Hz); [clear -E1; lia | clear -E2; lia | clear -D10b; lia | exact Hc].
    - apply (env_sh_out SB T (topG G) c nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO C1 NF0 MUB Hz); [clear -D10a; lia | clear -D12 TG; lia | clear -E1; lia | exact Hc]. }

  assert (LIVE_OUT : forall b n z, In (b, n) (aa_live A) ->
            (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> ~ envR SB T c nf mu z).
  { intros b n z Hin Hz Hc. destruct (is_primary n) eqn:HP.
    - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hin HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & _ & CZ). fold SB in O0, OM, OE, CZ.
      set (c' := ClassID (needed n)) in *. set (o' := b - rz n - (SB + c' * 2 ^ 32)) in *.
      pose proof (PC c' D1) as PC'. fold G in PC'. unfold class_repr in PC'.
      destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV' & _).
      destruct (LV' b n Hin HP eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3. unfold region_beg, kRegionSize in V1, V2, V3. fold o' in V2, V3.
      pose proof (CZ z Hz) as CZz. unfold czone in CZz. cbn zeta in CZz.
      apply (slot_out SB T (topG G) c nf mu c' o' (Size c') z GEO C1 NF0 MUB D1 O0 ltac:(destruct (Size_facts c' D1) as [X _]; clear -X; lia) OE); [|exact CZz|exact Hc].
      destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC].
      assert (EAU : cs_allocated_user (nthZ (aa_cls A) c' cs_empty) = cs_allocated_user cs) by (rewrite EC; reflexivity).
      rewrite EAU in V3. rewrite EC in V3 |- *. unfold mu. clear -V3 N2. lia.
    - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hin HP) as (i & ch & Hi & Eb & RZ & Hn1 & BN & D6 & D0 & DI). unfold PG in Eb, D6.
      apply (NE_sec i ch z Hi); [|exact Hc]. destruct Hz as [Hz|Hz]; [left; clear -Hz Eb RZ BN; lia | right].
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Sh_add_le b (n + 7) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eb DI; destruct DI as (X & _); lia) ltac:(clear -Hn1; lia) ltac:(clear -BN; lia)) as M2.
      clear -Hz M1 M2. lia. }

  assert (QF_OUT : forall z, q_foot A z -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. destruct (qfoot_cases A mE HG HI3c HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
    - destruct (q_ids_valid A c' (o' / 16) D1 HQP IDin) as (_ & _ & V3).
      destruct (Size_facts c' D1) as (SZ' & SM').
      rewrite (id16_of o' (Size c') ltac:(clear -SZ'; lia) SM' OM) in V3.
      unfold czone in CZ. cbn zeta in CZ. fold SB in CZ.
      apply (slot_out SB T (topG G) c nf mu c' o' (Size c') z GEO C1 NF0 MUB D1 O0 ltac:(clear -SZ'; lia) OE); [|exact CZ|exact Hc].
      destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC].
      rewrite EC in V3 |- *. change (nthZ (aa_cls A) c cs_empty) with cs in V3. unfold mu. clear -V3 N2. lia.
    - exact (NE_sec i ch z Hi Hr Hc). }
  assert (NE_cls : forall c' z, 1 <= c' <= 30 -> c' <> c -> cls_foot G c' (nthZ (aa_cls A) c' cs_empty) z -> ~ envR SB T c nf mu z).
  { intros c' z Hc' Hne Hz Hc. pose proof (PC c' Hc') as PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _).
    pose proof (Zle_0_nat (length (cs_free_array (nthZ (aa_cls A) c' cs_empty)))) as L0.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
    unfold cls_foot in Hz. cbv zeta in Hz. unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz. fold G in Hz. fold SB T in Hz.
    apply (clsfoot_out SB T (topG G) c nf mu c' (cs_mapped_free_array (nthZ (aa_cls A) c' cs_empty)) (cs_mapped_user (nthZ (aa_cls A) c' cs_empty)) z GEO C1 NF0 MUB Hc' Hne
             ltac:(clear -M6 L0; lia) ltac:(clear -M2 M3; lia)); [|exact Hc].
    clear -Hz. destruct Hz as [H|[H|[H|[H|H]]]]; [left | right; left | right; right; left | right; right; right; left | right; right; right; right]; lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply NZE. intros Hc.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NE_img z K Hc).
    - apply (NE_T z); [left; fold T in K; clear -K; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_ctx G) (ag_ctx G + 4096) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -CTX3; lia | clear -G13; lia | clear -CB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_dtls G) (ag_dtls G + 4096) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -DTLS3; lia | clear -G14; lia | clear -DB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_fsb G) (ag_fsb G + 11571200) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -S4; lia | clear -G10; lia | clear -WF; lia | exact Hc]. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) Ar).
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply NZE; intros Hc; rewrite (ENVF z Hc) in Hz; discriminate).
    exact HF. }
  assert (HLS : live_sep Ar) by exact Hsep.
  assert (HLB : live_block_repr m3 Ar).
  { apply (live_block_repr_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [unfold Ar, refillA; cbn [aa_cls]; rewrite length_list_upd; exact PL|].
    split; [rewrite (ECSo 0) by (clear -C1; lia); exact P0|]. split; [rewrite (ECSo 31) by (clear -C1; lia); exact P31|].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    2: { rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)).
         apply (class_repr_agree mE m3 G A Ar c' _ Hc'); [exact (eq_sym Hini) | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (PC c' Hc')].
         intros z Hz. apply AGm. exact (NE_cls c' z Hc' Hne Hz). }

    rewrite ECS'. unfold class_repr. cbv zeta. fold SB. fold ri fa rb.
    change (live_ids G Ar c) with (live_ids G A c). change (qall Ar) with (qall A). change (aa_live Ar) with (aa_live A).
    assert (RIS : forall off w, 0 <= off -> off + Z.of_nat w <= 128 -> forall k, (k < w)%nat -> m3 (ri + off + Z.of_nat k) = v3 (ri + off + Z.of_nat k)).
    { intros off w Ho Hw k Hk. apply MSP. unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -Ho Hw Hk C1. lia. }
    assert (CRI : forall off w v, 0 <= off -> off + Z.of_nat w <= 128 -> cell_ok v3 (mkACell (ri + off) w v) -> cell_ok m3 (mkACell (ri + off) w v)).
    { intros off w v Ho Hw Hcv. eapply cell_ok_agree; [|exact Hcv]. cbn [c_addr c_w]. intros k Hk. exact (RIS off w Ho Hw k Hk). }
    split; [apply CRI; [unfold RI_mutex; clear; lia | unfold RI_mutex; cbn; clear; lia | exact R1']|].
    split; [apply CRI; [unfold RI_num_freed; clear; lia | unfold RI_num_freed; cbn; clear; lia | exact R2']|].
    split; [apply CRI; [unfold RI_mapped_free_array; clear; lia | unfold RI_mapped_free_array; cbn; clear; lia | exact R3']|].
    split; [apply CRI; [unfold RI_allocated_user; clear; lia | unfold RI_allocated_user; cbn; clear; lia | exact R4']|].
    split; [apply CRI; [unfold RI_allocated_meta; clear; lia | unfold RI_allocated_meta; cbn; clear; lia | exact R5']|].
    split; [apply CRI; [unfold RI_mapped_user; clear; lia | unfold RI_mapped_user; cbn; clear; lia | exact R6']|].
    split; [apply CRI; [unfold RI_mapped_meta; clear; lia | unfold RI_mapped_meta; cbn; clear; lia | exact R7']|].
    split; [apply CRI; [unfold RI_exhausted; clear; lia | unfold RI_exhausted; cbn; clear; lia | exact R8']|].
    split; [apply PRESX; exact PRI|].
    split; [exact Q1|]. split; [exact Q2|].
    split; [unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *; clear -Q10 MCU; lia|].
    split; [exact Q3'|]. split; [exact Q4|].
    split; [split; [exact Q5 | unfold kFreeArraySize in *; clear -Q11 FCU; lia]|].
    assert (FAR : SB + 2 ^ 32 <= fa /\ fa + 2 ^ 29 <= SB + 2 ^ 37).
    { unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -C1. lia. }
    split.
    { intros i x Hi. eapply cell_ok_agree; [|exact (HFA i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply MSP.
      pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold kFreeArraySize in *. clear -L Hk FAR Q5 Q11 FCU. lia. }
    split.
    {
      intros z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (fa + cs_mapped_free_array cs)) as [LT|GE]; [|exfalso; apply Hn; apply HNF; clear -Hz GE; lia].
      destruct (Z_lt_dec z (fa + 4 * nf)) as [LT2|GE2]; [|apply PR; clear -LT GE2; lia].
      assert (Hz0 : fa <= z) by (pose proof (Zle_0_nat (length (cs_free_array csR))); clear -Hz H; lia).
      set (i := Z.to_nat ((z - fa) / 4)).
      assert (Hi : (i < length (cs_free_array cs))%nat).
      { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; clear -Hz0; lia). fold nf. apply Z.div_lt_upper_bound; clear -LT2 Hz0; lia. }
      pose proof (R9 i _ (nth_error_nth' (cs_free_array cs) 0 Hi)) as Hcell.
      assert (Ei : Z.of_nat i = (z - fa) / 4) by (unfold i; apply Z2Nat.id; apply Z.div_pos; clear -Hz0; lia).
      pose proof (Z.div_mod (z - fa) 4 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (z - fa) 4 ltac:(clear; lia)) as MB.
      specialize (Hcell (Z.to_nat ((z - fa) mod 4)) ltac:(cbn [c_w]; clear -MB; lia)). cbn [c_addr c_w] in Hcell.
      rewrite Z2Nat.id in Hcell by (clear -MB; lia). rewrite Ei in Hcell.
      replace (fa + 4 * ((z - fa) / 4) + (z - fa) mod 4) with z in Hcell by (clear -DM; lia).
      eexists. exact Hcell. }
    split.
    { intros x Hx. destruct (Q6 x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X1 & X2 & X3).
      unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 4) with 16. replace (x * 16) with (16 * x) by (clear; lia).
      split; [exact X1|]. split; [exact X2 | exact X3]. }
    split.
    {
      intros z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (rb + mu)) as [LT|GE]; [apply PU; [clear -Hz LT; lia | exact HL] | exfalso; apply Hn; apply HNU; fold mu; clear -Hz GE; lia]. }
    split.
    { intros z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (Sh (rb + mu))) as [LT|GE]; [apply PSH; clear -Hz LT; lia | exfalso; apply Hn; apply HNS; fold mu; clear -Hz GE; lia]. }
    split; [apply PRESX; exact PE|].
    split; [exact (proj2 (NoDup_ListNoDup _) Q7)|].
    split; [intros b n Hin Hp Hcl; destruct (LV b n Hin Hp Hcl) as (V1 & V2 & V3); split; [exact V1|]; split; [exact V2 | clear -V3 HAUm; lia]|].
    split.
    { intros _. destruct (CI Hini) as (K1 & K2 & K3 & K4 & K5). fold T in K1, K2, K3, K4 |- *. fold pce in K1, K2, K3, K4 |- *.
      assert (PCB : T + 288 <= pce /\ pce + 80 <= T + 2688) by (unfold pce; clear -C1; lia).
      split; [eapply cell_ok_agree; [|exact HCN]; cbn [c_addr c_w]; intros k Hk; apply MTH; clear -Hk PCB; lia|].
      split; [apply CELL; [|exact K2]; intros k Hk Hc; apply (own_out SB T (topG G) c nf mu (pce + 4 + Z.of_nat k) GEO C1 NF0 NF4 MUB); [|exact Hc];
              right; right; right; unfold pce; clear -Hk; lia|].
      split; [apply CELL; [|exact K3]; intros k Hk Hc; apply (own_out SB T (topG G) c nf mu (pce + 8 + Z.of_nat k) GEO C1 NF0 NF4 MUB); [|exact Hc];
              right; right; right; unfold pce; clear -Hk; lia|].
      split; [|exact HKC].
      intros i x Hi. eapply cell_ok_agree; [|exact (HCC i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply MTH.
      pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (max_count_le16 c C1) as M16. clear -L Hk PCB HKC M16. unfold pce in *. lia. }
    split; [intros X; discriminate X|].
    split; [exact Q8|].
    split; [unfold slots; rewrite Q9, length_app; f_equal; clear; lia|].
    exact (conj Q10 Q11). }
  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live Ar) z) by (intros z Hz; exact Hz).
  assert (HSR : secondary_repr m3 Ar).
  { refine (secondary_repr_agree mE m3 A Ar eq_refl eq_refl eq_refl _ _ _ LIVM Hsec).
    - intros i ch z Hi Hz. apply AGm. exact (NE_sec i ch z Hi Hz).
    - intros z Hz. apply AGm. intros Hc. destruct Hsec as (_ & _ & SC2 & _ & SC45 & _). fold G in SC45, Hz. destruct SC45 as [_ (SC4a & _ & SC5 & _ & SC4)].
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SC4. unfold kPtrArrayReserve in SC2, SC4, PAB3, PABT3.
      apply (env_out SB T (topG G) c nf mu (ag_pab G) (ag_pab G + 2 ^ 23) z GEO C1 NF0 MUB ltac:(clear -Hz SC2; lia)); [clear -PAB3; lia | clear -PABT3; lia | clear -SC4; lia | exact Hc].
    - intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HQR : quarantine_repr m3 Ar).
  { refine (quarantine_repr_agreeR mE m3 A Ar eq_refl eq_refl eq_refl eq_refl _ _ _ _ Hq).
    - intros c'. unfold Ar, refillA, nthZ. cbn [aa_cls]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
      + rewrite <- E. rewrite nth_list_upd_same by exact Hlenc. exact HAUm.
      + rewrite nth_list_upd_other by exact NE. clear; lia.
    - intros z Hz. apply AGm. exact (QF_OUT z Hz).
    - intros z Hz. apply AGm. apply NE_T. left. fold G T in Hz. clear -Hz. lia.
    - intros z Hz. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI in *. clear -Hz. lia. }
  assert (HIA : ia_inv m3 Ar).
  { refine (ia_inv_agree mE m3 A Ar eq_refl _ Hia). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold G T in TH1, TH2. unfold thread_inv. fold T. split.
    - rewrite AGm; [exact TH1|]. apply NE_T. right. clear. lia.
    - apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HDEP : depot_wf m3 Ar).
  { unfold depot_wf in Hdep |- *. change (aa_depot Ar) with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm. intros Hc.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> False).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST. fold SB in SS.
      destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
      apply (env_out SB T (topG G) c nf mu bb (bb + L) a GEO C1 NF0 MUB Hab); [clear -SS; lia | clear -ST; lia | clear -WB; lia | exact Hc]. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply (NE_img a); [|exact Hc]. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HI3' : inv3 Ar).
  { pose proof HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split; [exact X2'|]. split; [exact X3'|].
    split.
    { intros z Hz. destruct (X4' z Hz) as [Y1 Y2]. split; [exact Y1|].
      intros c' x' Hc' Hx'. destruct (Z.eq_dec c' c) as [->|Hne]; [|rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)) in Hx'; exact (Y2 c' x' Hc' Hx')].
      rewrite ECS' in Hx'.
      destruct (Q6 x' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hx')) as (V1 & V2 & V3).
      apply (qfoot_slot_out A mE HG HI3c HQP Hsec HAU c x' z C1 V1 V2); [| |exact Hz].
      - unfold kUserSpaceSize, kRegionSize, kFreeArraySize in MCU. clear -V3 Q2 Q10 MCU. lia.
      - intros Hq'. apply NoDup_app_remove_l in Q7. apply (NoDup_app_in _ _ x' Q7 Hx'). apply in_or_app. right. exact Hq'. }
    split; [exact X5'|]. split; [exact X6'|]. split; [exact X7'|]. split; [exact X8'|]. intros _. reflexivity. }
  assert (HA' : AInv Ar rho3 tp md).
  { unfold AInv, AInvA. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|].

  assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ envR SB T c nf mu a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hn. destruct (Z_lt_dec a IMG_LO) as [LO|NLO]; [|destruct (Z_le_dec IMG_HI a) as [HI|NHI]].
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_introl LO)), <- (view_rm_off (rm rhoE) a Ha (or_introl LO)). exact (NZE a Hn).
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_intror HI)), <- (view_rm_off (rm rhoE) a Ha (or_intror HI)). exact (NZE a Hn).
    - apply HRMI. clear -NLO NHI. lia. }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold IMG_HI in Ha; clear -Ha; lia).
    rewrite <- (view_rm_off (rm rho3) a Ha' (or_intror (proj1 Ha))). rewrite <- (view_rm_off (rm rhoE) a Ha' (or_intror (proj1 Ha))) in Hd.
    change (v3 a <> None). change (vE a <> None) in Hd. destruct (ZND a) as [Hc|Hn]; [destruct (PRES a Hc) as [b Hb]; rewrite Hb; discriminate | rewrite (VO a Hn); exact Hd]. }
  split.
  2: { intros x0 j Hx Hj Hdef.
       assert (Bx : 0 <= x0 < 2 ^ 47).
       { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HFv Hsep CX))|].
         destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
       unfold word_byte. apply DEFM; [|exact Hdef].
       pose proof (Z.div_mod (Sh x0) 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear; lia)) as MB.
       unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear; lia) ltac:(clear -Bx; lia)) as D0.
       pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
       clear -Hj DM MB D0 D1. lia. }
  intros a Ha Hcl.

  assert (NOC : forall y, client_addrA CST A y ->
            (exists b n, In (b, n) (aa_live A) /\ b <= y < b + n)
            \/ (0 <= y < 2 ^ 47 /\ (y + 8 <= SB + 2 ^ 32 \/ SB + 2 ^ 37 + 4096 <= y) /\ (y + 8 <= T + 288 \/ T + 2688 <= y) /\ (y + 8 <= 2147450880 \/ 17594333495296 <= y))).
  { intros y Hy.
    destruct (client_addr_cases CST A y _ HFv Hy) as [S|[L|[FR|[C|FL]]]].
    - right. fold G in S. clear -S S2 G5 TG. lia.
    - left. exact L.
    - right. destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hyf. clear -Hyf M S4 G10 WF G2 G3 TG. lia.
    - right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. clear -X S1 TI. lia.
    - right. destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G. unfold fs_flags. rewrite FS_kFlagsOffset_val.
      unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M. clear -M S4 G10 WF G2 G3 TG. lia. }
  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> (y + 8 <= SB + 2 ^ 32 \/ SB + 2 ^ 37 + 4096 <= y) -> ~ envR SB T c nf mu (Sh y)).
  { intros y By Hy Hc.
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (env_sh_out SB T (topG G) c nf mu (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) GEO C1 NF0 MUB); [|clear -By DY MY; lia|clear -By DY MY; lia|clear -Hy DY MY; lia|exact Hc].
    unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
    replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
    clear. lia. }
  apply RMO; [exact Ha|].
  destruct Hcl as [[CL1 _]|[CL1 _]].
  - destruct (NOC a CL1) as [(b & n & Hbn & Hab)|(B1 & B2 & B3 & B4)].
    + apply (LIVE_OUT b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + intros Hc. apply (env_out SB T (topG G) c nf mu a (a + 8) a GEO C1 NF0 MUB ltac:(clear; lia)); [exact B2 | exact B3 | exact B4 | exact Hc].
  - destruct CL1 as [(y & Cy & ->)|(y & Gy & ->)].
    + destruct (NOC y Cy) as [(b & n & Hbn & Hyb)|(B1 & B2 & B3 & B4)].
      * apply (LIVE_OUT b n (Sh y) Hbn). right.
        assert (B8 : b mod 8 = 0).
        { destruct (is_primary n) eqn:HP.
          - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hbn HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & (RZN & _) & _). fold SB in O0, OM, OE.
            destruct (Size_facts _ D1) as (SZ' & SM'). destruct (mod8_of_slot _ _ (proj1 SZ') SM' OM) as [Mo _].
            pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.rz_facts n) as (_ & RZ16).
            set (o' := b - rz n - (SB + ClassID (needed n) * 2 ^ 32)) in *.
            assert (Eb : b = SB + ClassID (needed n) * 2 ^ 32 + o' + rz n) by (unfold o'; clear; lia).
            destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear; lia)) S3) as [qs Hqs]. destruct (proj1 (Z.mod_divide o' 8 ltac:(clear; lia)) Mo) as [qo Hqo].
            destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(clear; lia)) RZ16) as [qr Hqr].
            rewrite Eb. apply Z.mod_divide; [clear; lia|]. exists (qs * 2 ^ 13 + ClassID (needed n) * 2 ^ 29 + qo + qr * 2). clear -Hqs Hqo Hqr. lia.
          - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hbn HP) as (i & ch & Hi & Eb & _ & _ & _ & D6 & _). unfold PG in Eb, D6.
            destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(clear; lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [clear; lia|]. exists (k0 * 512 + 768). clear -Eb Hk0. lia. }
        unfold Sh. destruct (proj1 (Z.mod_divide b 8 ltac:(clear; lia)) B8) as [qb Hqb].
        pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
        pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as MN.
        rewrite Hqb. rewrite Z.div_mul by (clear; lia). clear -Hyb Hqb DY MY DN MN. lia.
      * exact (SHY y B1 B2).
    + destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y); [clear -Y1 Y2; lia | left; clear -Y2 S1; lia].
Qed.
End R.
End RebuildR.

(* [comment removed for export] *)
Module SpineMallocS5t.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S5T.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Lemma JG_pure : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JG W st A Kc rho) E rhoE tp w -> sep_geom (aa_geom A) /\ prim_room A.
Proof.
  intros A Kc rho rhoE tp w E Hw. split.
  - destruct (proj2 (proj2 Hw)) as (HA & _). exact (sep_geom3_sep _ (proj1 (AInvA_inv3 _ _ _ _ HA))).
  - destruct (proj2 (proj2 Hw)) as (_ & _ & _ & _ & HB & _). exact (budget_ok_alloc_prim _ _ HB).
Qed.

Section TAIL.
Hypothesis SKY : map skel (ss_objs (ax_S (E3p W st tmax))) = map skel ((((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
Hypothesis YX : ax_X (E3p W st tmax) = [].
Hypothesis YF : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis YP : In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis WY1 : swf (ax_S (Y1 (E3p W st tmax))) = true.
Hypothesis WY2 : swf (ax_S (Y2 (E3p W st tmax))) = true.
Hypothesis WY3 : swf (ax_S (Y3 (E3p W st tmax))) = true.
Hypothesis WY4 : swf (ax_S (Y4 (E3p W st tmax))) = true.
Hypothesis WY5 : swf (ax_S (Y5 (E3p W st tmax))) = true.
Hypothesis WY6 : swf (ax_S (Y6 (E3p W st tmax))) = true.
Hypothesis WY7 : swf (ax_S (Y7 (E3p W st tmax))) = true.
Variable s3 : wsub.
Hypothesis ENT3 : entailsA (Y7 (E3p W st tmax)) (C3 W st tmax) s3 = true.
Hypothesis SID3 : wsub_id_below s3 GW = true.

Lemma e3p_carve : forall A Kc rho tp w rhoX,
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp w ->
  SPA segs (JG W st A Kc rho) (C3 W st tmax) (rho_sub rhoX s3) tp w.
Proof.
  intros A Kc rho tp w rhoX HW HUS HKc Hw.
  apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc
           (proj1 (JG_pure A Kc rho rhoX tp w _ Hw))); [|exact Hw].
  exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP).
Qed.

Lemma e3p_cnt : forall A Kc rho tp w rhoX,
  SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp w -> 1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof. intros A Kc rho tp w rhoX Hw. exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP). Qed.

Theorem spine_s3p_tail : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) -> sep_geom (aa_geom A) -> prim_room A ->
   forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q.
Proof.
  intros ok A Kc rho tp Q HW HUS HKc HC rhoX.
  apply (triple_pre_pure segs ok _ _ (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) /\ sep_geom (aa_geom A) /\ prim_room A)).
  { intros w Hw. split; [exact (e3p_cnt A Kc rho tp w rhoX Hw) | exact (JG_pure A Kc rho rhoX tp w _ Hw)]. }
  intros (Hcnt & HSEP & HPRM).
  eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC Hcnt HSEP HPRM (rho_sub rhoX s3))].
  exact (e3p_carve A Kc rho tp w rhoX HW HUS HKc Hw).
Qed.

Theorem espine_s3p_tail : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) -> sep_geom (aa_geom A) -> prim_room A ->
   forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q.
Proof.
  intros A Kc rho tp Q HW HUS HKc HC rhoX.
  apply (etriple_pre_pure segs _ _ (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) /\ sep_geom (aa_geom A) /\ prim_room A)).
  { intros w Hw. split; [exact (e3p_cnt A Kc rho tp w rhoX Hw) | exact (JG_pure A Kc rho rhoX tp w _ Hw)]. }
  intros (Hcnt & HSEP & HPRM).
  eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC Hcnt HSEP HPRM (rho_sub rhoX s3))].
  exact (e3p_carve A Kc rho tp w rhoX HW HUS HKc Hw).
Qed.
End TAIL.

Section CERT.
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] = true.
Theorem spine_s3p_cert : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x40e58; 0x3c614] GW [C2p W st tmax] [E3p W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3p.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply (HC rhoX)].
  - left. reflexivity.
Qed.
End CERT.

Section ECERT.
Hypothesis NXC2p : (GW <= ss_next (ax_S (C2p W st tmax)))%positive.
Hypothesis ECert3p : check_ecfgA segsA 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] = true.
Theorem espine_s3p_cert : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x40e58; 0x3c614] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2p W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2p].
  - exact ECert3p.
  - intros E rhoX HinE. clear NXC2p ECert3p. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply (HC rhoX)].
  - left. reflexivity.
Qed.
End ECERT.
End S5T.
End SpineMallocS5t.

(* [comment removed for export] *)
Module SpineMallocEc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "app"; "list"; "nil"; "prod"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_next"; "ss_facts"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E2a"; "E2b"; "C1g"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "E2a'"; "E2b'"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "ulink"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EC.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2fS5eVCST;R1A2S5eS68R2A2S1F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S58VAInv;VW;Vst;VA;VKc;S16PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S5dS17SaS63Q40A1A1S67VAInv;R4R3R2R1A4S5fS61Vsegs;S1dR4A1A2S60Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_spine_s2C.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S1fVW;Vst;Vtmax;A3S2S37VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S20VW;Vst;Vtmax;A3S2S38VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6S35S2eUfa0S8S2fZ40d40SbS2fA1A3S2dS8S3S21VW;Vst;Vtmax;A3SbS3A1M0A3S8S3S1fVW;Vst;Vtmax;A3S8S3S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S39P9dS25VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S39P9dS26VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6S3aP9dS25VW;Vst;Vtmax;A3S51Z208S65S66S48S49S4aS48S4bA1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6S3aP9dS26VW;Vst;Vtmax;A3S51Z18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S12S2S37VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S12S2S38VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4dS2S1fVW;Vst;Vtmax;A3A1S2S37VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S25VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4dS2S20VW;Vst;Vtmax;A3A1S2S38VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S26VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S30S14S2S37VnW;Vst;Vtmax;A3A1A1S14S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S30S14S2S38VnW;Vst;Vtmax;A3A1A1S14S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S43S10S19S4cS18Z200A1S16S29A1A3S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S43S10S1cS19S4cS18Z200A1S16S29A1A3A1S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S42S10S22S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S42S10S22S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3dS1bS2VXa;A1A1A4S31S13G0S3dS9S13S8S13S50S9S13S57VW;A1S52A3A3S4fA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3dS1bS2VXb;A1A1A4S31S13G0S3dS9S13S8S13S50S9S13S57VW;A1S52A3A3S4fA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S42S10S9S10S9S10S9S10S56VW;Vst;A2S54S53A1A3S4eA3S22A3S15S2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S42S10S9S10S9S10S9S10S56VW;Vst;A2S54S53A1A3S4eA3S22A3S15S2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXa;A1A1A1S7A3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXa;A1A1A1S7A3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S12S2S40VXa;A1A1A1S7A3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S12S2S3bVXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S12S2S41VXa;A1A1A1S7A3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXb;A1A1A1S7A3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXb;A1A1A1S7A3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S12S2S40VXb;A1A1A1S7A3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S12S2S3bVXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S12S2S41VXb;A1A1A1S7A3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S4S3bVXa;A1S23VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S4S3cVXa;A1S24VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S4S3bVXb;A1S23VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S4S3cVXb;A1S24VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S32Vsa;S2dA2S7A3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S32Vsra;S2dA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S32Vsb;S2dA2S7A3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S32Vsrb;S2dA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S44S10S1aS14S2S23VW;Vst;Vtmax;A3A1A1A1S9S10S27S2cA3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S44S10S1aS14S2S24VW;Vst;Vtmax;A3A1A1A1S27A3S7A3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S6bS2dS14S2S21VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S6S36S2eUfa0S8S2fZ40d40SbS2fA1A3S2dS8S33S34S21VW;Vst;Vtmax;A3Z1S18Z0M0A1M1A3SbS33A1M2A3S8S33S34S1fVW;Vst;Vtmax;A3G0G1A3S8S33S34S20VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S7A3").
Theorem espine_s2c : ltac2:(tb__ "0|2|
S5dS59S17SaS63Q40M0A1A1S46OF_;S0S5cVst;S5bA3S0SaS55A1VW;SbS55A1A3F_;S6aVW;Vst;A2S5aR6A1S17S45Vsegs;S47Vsegs;S62VW;Vst;R9R8R7A5S2aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S0S2fS69R9S64G0S1eR7PcA2A2A2Z0A3S17S45Vsegs;S47Vsegs;S62VW;Vst;RbRaR9A5M1S2bVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;S17S45Vsegs;S47Vsegs;G1S21VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40d40] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2C.
End EC.
End SpineMallocEc.

(* [comment removed for export] *)
Module SegQ3D_qiq.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "cons"; "list"; "bool"; "nat"; "app"; "nil"; "true"; "false"; "option"; "None"; "andb"; "fst"; "S"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "rm"; "valuation"; "SAlu"; "SLit"; "sprop"; "ss_objs"; "ss_facts"; "eval"; "ob_dflt"; "obj_range"; "odefault"; "rl"; "rw"; "SExt"; "dflt_writable"; "ranges_disjoint"; "swf"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "opp"; "sub"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_setS"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "mkQB"; "aa_cache_inited"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "qb_addr"; "qb_items"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs"; "TQ2"; "KEPTQ"; "TQ1"; "TQ3"; "RIr"; "TQIf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "vIT"; "F_DI"; "O_it"; "vS7"; "@Stdlib.Lists.List"; "forallb"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "O_sb"; "add"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq"; "RQP"; "NRO"; "rieS"; "spec_litb"; "FTLQ"; "N_itmP"; "cptrQ"; "entS"; "hdrS"; "hideP"; "hwP"; "magS"; "slotS"; "stqS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "N_rti"; "entQ"; "O_ishQ"; "qienv"; "rieQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "HVI"; "HVS"; "addo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "with_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "O_mtx00"; "STK"; "SWD"; "cb_cells"; "vXF"; "vXK"; "vXL"; "vXS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "O_gmax"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_ab"; "it_cls"; "it_id"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "batch_mem"; "item_mem"; "QFP"; "QRD"; "batch_pure"; "push_cache"; "set_q"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep";
"set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "coverb"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "vb_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma FRM_absorb_gen : ltac2:(tb__ "0|7|
S40S17S17S17S0OF_;S0S2bR2R1A1M0S2aG0A1A2Fz;S1S28S3cQ40M1A1M2S22R4R1A2S22R5R1A2A3Fi;S1S28S5S3cQ8A1M3A1S21R5R1A2S21R6R1A2A3Fl;S0R5R1A1S2bS94RaR2A2S29S95RaR2A2S28ScG3A1M4S48S37S16R7A1R2A3S48S37S16R8A1R2A3A3A2A2F_;Fz;G2R6S3eG1R1A2M5A1S29S2fS9dS3eG1R2A2M6A2S30G6S9cA2A2S2aS28G4S16R9R3A2SdG3A1A3A1F_;F_;Fa;S0S2aR7R1A1A1S28G4S48S37S16R9A1R2A3S48S37S16RaA1R2A3A3F_;Fz;G2S2aR8G5A1A1S28G4S16RaR2A2S16RbR2A2A3F_;Fa;S83RcRbRaA3S83RdRcRaA3F_;F_;F_;F_;F_;F_;F_;F_;FP;Frho3;Frho;Frho0;FA0;").
Proof.
  intros A0 rho0 rho rho3 P PD Hrw Hrl HP HB FR FRrm ((F1 & F1') & F2 & F3 & F4).
  split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
  - intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. destruct (HP _ Hp) as [HQ|[HQ _]]; [left; exact HQ | exact HQ].
  - intros z NQ. rewrite <- (F3 z NQ). destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [HQ|[_ HE]]; [exfalso; exact (NQ HQ) | exact HE].
  - intros a HBa Hdef. destruct (PD (bv_unsigned a)) as [Hp|Np]; [exact (HB a Hp HBa) | rewrite (FRrm a Np); exact (F4 a HBa Hdef)].
Qed.

Lemma item_mem_frameP : ltac2:(tb__ "0|4|
S49S49S2S0S0A2S2fZ10S9eS12S0S0R1A3A1A2S0S29S2fS8eR3A1R1A2S30R1SfS0S0R3A3A2A2S28ScS3cQ8A1M0A1M1R5R2A1R6R2A1M2A3F_;Fz;S0S2aS28G1R6R1A1SdG0A1M3A3A1S2aS28G1G2G3A3A1F_;Fz;S93R6R4A2S93R6R5A2F_;F_;F_;F_;Fit;Fm';Fm;").
Proof.
  intros m m' it Hrz HL HP (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold it_ab in HL.
  split; [rewrite HL by lia; exact H1|]. split; [eapply present_frame; [|exact H2]; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H3]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H4]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply present_frame; [|exact H5]; intros z Hz; apply HL; lia|].
  split.
  - unfold alloc_magic_ok in *. destruct H6 as [H6|[H6a H6b]]; [left; exact H6 | right].
    split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply HL; lia.
  - intros z Hz. destruct (H7 z Hz) as [b Hb]. pose proof (HP z ltac:(rewrite Hb; discriminate)) as X.
    destruct (m' z) as [b'|]; [exists b'; reflexivity | exfalso; exact (X eq_refl)].
Qed.
Lemma batch_mem_frameP : ltac2:(tb__ "0|5|
S40S49S49S3fS96R4R1A2S0S29S2fS32S46R3A1M0Z8A2R1A2S30R1S32G0Z2000A2A2A2S28ScS3cQ8A1M1A1M2R5R2A1R6R2A1A3F_;Fz;S2S0S0A2M3S0S59G3R2S47R5A1A3S29S2fS8eR3A1R2A2S30R2SfS0S0R3A3A2A2S28G2R8R3A1R9R3A1A3F_;F_;Fz;Fit;S0S2aS28G2R7R1A1SdG1A1M4A3A1S2aS28G2R7R2A1G4A3A1F_;Fz;S92R7R5A2S92R7R6A2F_;F_;F_;F_;F_;Fb;Fm';Fm;FA;").
Proof.
  intros A m m' b (_ & HLn & _ & HPu) HB HI HP (H1 & H2 & H3 & H4 & H5). unfold kQuarantineBatchCount in HLn.
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frameP; [apply (proj1 (rz_facts (snd it))) | intros z Hz; exact (HI it z Hin Hz) | exact HP | exact I].
Qed.

Lemma head_item_fresh : forall {X Y : Type} (f : X -> Y) (p : X -> bool) (x : X) (l : list X),
  NoDup (map f (List.filter p (x :: l))) -> p x = true -> ~ In x l.
Proof.
  intros X Y f p x l ND Hp Hin. cbn [List.filter] in ND. rewrite Hp in ND. cbn [map] in ND. inversion ND as [|y0 l0 NI ND']; subst.
  apply NI. apply list_elem_of_In. apply in_map. apply filter_In. split; [exact Hin | exact Hp].
Qed.

Lemma absorb_io : ltac2:(tb__ "0|3|
S17S5S14A1S99S29S3cQ40M0A1S2aS5eR4R3R1A3A1S28ScS3cQ8A1A1M1S16S5fR5R4R3A3M2R2A2S16R5R2A2A3F_;Fa;S0S2aS29S29S2fZ0R1A2S30R1S31Z2Z40A2A2A2S5eR4R3S3dG0R1A2A3A2A1S28G1S48S37S16G2A1R2A3S48S37S16R5A1R2A3A3F_;Fz;A2Fms;FR;Frho;").
Proof.
  intros rho R ms. split; [intros a Ha; apply rm_absorb_out; exact Ha|].
  intros z Hz. apply view_agree. intros Hr. apply rm_absorb_out. intros Hin. apply Hz. split; [exact Hr | exact Hin].
Qed.
Lemma IRdec : ltac2:(tb__ "0|1|
S17S5S14A1S0S2bS29S29S2fZ0R1A2S30R1S31Z2Z40A2A2A2S5eR3R2S3dQ40R1A2A3A2M0S2aG0A1A2Fz;FR;Frho;").
Proof.
  intros rho R z. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [H|H]; [|right; intros [_ X]; exact (H X)].
  destruct (Z_le_dec 0 z) as [L|L]; [destruct (Z_lt_dec z (2 ^ 64)) as [L2|L2]|]; [left; split; [lia | exact H] | right; intros [X _]; lia | right; intros [X _]; lia].
Qed.

Lemma carve_slot_it : ltac2:(tb__ "0|5|
S53S3bS17S5S3cQ40M0A1M1A1S74S0S0S52S37R7R6R5R4R3A6S28S5S2S13S13A2M2A1S39R7A1S9G2A1A3S28S6S26S82S38R8A1S56A2A1SaA3S28G1S1dR8S57A2S3dG0R5A2M3A3S28G1S1dR9S54A2G3A3S2fS32Z643000Z80M4A2R7A2S2fR8S31Z2Z3eA2A2S4aS48S37S16RcA1A2S4bS34R9G4A2U8R8A3A2S72S14S14S25S1fReR1A2S3S0S0S34RbG4A2S34RbZ78A2A4A2Lo';S1bS38ReA1A1A3S52S37R10S3aRfS82S38RfA1S56A2A2ReRdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmm;FB;Fw;Ftp;Frho;FS0;FJ;").
Proof.
  intros J S0 rho tp w B mm H HX Hswf Ee Em HB1 HB2 Cm HD.
  pose proof (SPA_carve_list segsA J rho S0 tp w [(vS7, -128, -120, [(-128, 8%nat, vIT)])] (ss_next (ax_S S0)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. rewrite Ee, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff. replace (B + off) with (B - 128 + (off + 128)) by lia. eapply (cell_wok_rd _ _ _ _ _ Cm); cbn [Z.of_nat]; lia.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      eapply (civ_cell rho (rm rho) B (-128)); [replace (B + -128) with (B - 128) by lia; exact Cm | exact Em | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_it, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj vS7 (SLit (-128)) (SLit (-120)) cs DUnknown) = (B - 128, B - 120)).
    { intros cs. rewrite obj_range_mk by lia. rewrite Ee, u64_lit by lia. f_equal; lia. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma carve_obj_range : ltac2:(tb__ "0|4|
S17S2dS2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2OLk;R1G1G2G1OLp;R2G0S0G0OLp0;R2S13S0S29S2fS33S31Z2Z3eA2M3A1R1A2S29S2fR1R3A2S30R3G3A2A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1S28S2S0S0A2S1fR3S2eR2A1A2Sa0R3R2A2A3F_;Fk;Frho;").
Proof. intros rho [[[b lo] hi] cs] (H1 & H2 & H3). cbn [carve_obj SMGlue.spec_range]. unfold carved. rewrite obj_range_mk by lia. reflexivity. Qed.

Definition hwP : sv := ltac2:(tb__ "0|0|
S18S5dS23SaQ20S15PcbA1A3S19Z3A1A3").
Definition cptrQ (vb : bool) : sv := ltac2:(tb__ "0|0|
S18S5cS18S5aS18S5aS6S13Lvb;Vvb;S15Pd2A1S54X6x2S18S5bS15Pc8A1S19Z20A1A3A3S62A3S19Z4A1A3").
Definition rieS : carve_spec := ltac2:(tb__ "0|4|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S7dZ30M3A4Z38A4S4G2S3G1S13S3S0S7G3U8A4S15PcaA1A4S9G2A1A3A4").
Definition entS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S7aZ0M3A4Z10A4S4G2S3G1S13S3S0S7G3U4M4A4S61S15PceA1S19Z1A1A2A4S4G2S3G1S13S3S0S7Z4G4A4S15PcfA1A4S4G2S3G1S13S3S0S7Z8U8A4S15Pc9A1A4S9G2A1A3A3A3A4").
Definition slotS (vb : bool) : carve_spec := ltac2:(tb__ "0|4|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S61S7aS18S5bS15PceA1S19Z2A1A3A2Z10M3A4Z14A4S4G2S3G1S13S3S0S7G3U4A4S69Vvb;A1A4S9G2A1A3A4").
Definition hdrS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S54Z0M3A4Z8A4S4G2S3G1S13S3S0S7G3U4M4A4S6dA4S4G2S3G1S13S3S0S7Z4G4A4S15PccA1A4S9G2A1A3A3A4").
Definition stqS : carve_spec := ltac2:(tb__ "0|3|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S9bZad0A4Zc60A4S4G2S3G1S13S3S0S7Zae0U8A4S61S15Pd1A1S18S5aS19Z0A1S15Pc9A1A3A2A4S9G2A1A3A4").
Definition magS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S15Pd2A1Z0M3A4Z10A4S4G2S3G1S13S3S0S7G3U8M4A4S19G3A1A4S4G2S3G1S13S3S0S7Z8G4A4S54A4S9G2A1A3A3A4").
Definition N_itmP (vb : bool) : list carve_spec := ltac2:(tb__ "0|1|
S8S2dS4S2dS6bS4S2dS6aS4S2dS6fVvb;A1S4S2dS70S9S2dA1M0A3A3A3A3S6S5S2dA1Lvb;Vvb;S4S2dS6eG0A3G0X6x2A3").
Definition NRO : list carve_spec := ltac2:(tb__ "0|0|
S8S2dS79S4S2dS65S9S2dA1A3A3").
Definition RQP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S8S14S71S2dS14S2eS79A4S8S14S4S14S7bS4S14S2eS65A1S9S14A1A3A3S71S2dS14S2eS68Vvb;A1A4A3A3").
Lemma TQ1_objsP : ltac2:(tb__ "0|0|
S6S28S5S14A1S1bS38S4eR1A1A1A1S8S14S4dS63R1A1A3A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TQ2_eq : ltac2:(tb__ "0|1|
S6S28S3bS3aS4eR1A1M0S9aS38G0A1S4dA2A2S4cR1A1A3Fvb;"). Proof. intros vb. reflexivity. Qed.
Definition FTLQ (vb : bool) : list sprop := ltac2:(tb__ "0|0|
S73S1aS11S1aS55A2S1cS38S4fVvb;A1A1A1A3").
Lemma TQ3_facts : ltac2:(tb__ "0|2|
S6S29S28S5S1aA1M0S1cS38S4cR1A1A1A1S8S1aS55S67R1A1A3M1A3S28G0S1cS38S4fR1A1A1A1G1A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma F_DI_pre : ltac2:(tb__ "0|1|
S2cS5S1aA1M0G0S28G0S55S8S1aS76S8dA1R1A3A3LF;A2"). Proof. eexists. reflexivity. Qed.
Lemma TQ2_objs : ltac2:(tb__ "0|1|
S6S28S5S14A1S1bS38S4cR1A1A1A1S8S14S8S14S85S87S86S89S88S8aS8bA4A2S4S14S84S4S14S8cS9S14A1M0A3A3A3S8S14S75G0A3A3A3Fvb;"). Proof. intros [|]; reflexivity. Qed.
Lemma TQ2a_objs : ltac2:(tb__ "0|1|
S6S28S5S14A1S1bS38S80S4cR1A1S60A2A1A1S8S14S8S14S85S87S86S89S88S8aS8bA4A2S4S14S84S4S14S8cS9S14A1M0A3A3A3S8S14S75S4S14S60G0A3A3A3A3Fvb;"). Proof. intros [|]; reflexivity. Qed.
Lemma TQ2_X : ltac2:(tb__ "0|4|
S6S29S28S5S2S13S13A2M0A1M1S39S4cR1A1M2A1S9G0A1M3A3S28G1S39S80G2S60A2A1G3A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma NRO_chk : ltac2:(tb__ "0|0|
S28S6S58S2dS9fS64A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RQP_unk : ltac2:(tb__ "0|1|
S6S28S6S58S14S14S20S6Lx;S1eR1A1SaSbSbS1SbLl;M0G0S0S13S5S2S0S0A2A1S5S27A1SbLtmpl;Lflds;Lcnt;Lesz;X20x6Lo;S63R1A1A3SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RQP_wr : ltac2:(tb__ "0|0|
S6S28S6S58S14S14S24S1eR1A1A1Lo;S63R1A1A3SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition spec_litb (k : carve_spec) : bool := ltac2:(tb__ "0|4|
S2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2S6Lk;Vk;G1G2G1S6Lp;R2G0S0G0S6Lp0;R2S13S0SeSeS35S33S31Z2Z3eA2M3A1R1A2S35R1R3A2A2S36R3G3A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1").
Lemma NRO_lit : ltac2:(tb__ "0|0|
S28S6S58S2dS66S64A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spec_litb_sound : ltac2:(tb__ "0|4|
S2dS28S6S66R1A1SaA3S2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2OLk;R2G1G2G1OLp;R2G0S0G0OLp0;R2S13S0S29S2fS33S31Z2Z3eA2M3A1R1A2S29S2fR1R3A2S30R3G3A2A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1F_;Fk;").
Proof. intros [[[b lo] hi] cs] H. unfold spec_litb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia. Qed.
Definition hideP (P : Prop) : Prop := P.
Lemma hideP_intro : ltac2:(tb__ "0|0|
OR1S6cR2A1F_;FP;"). Proof. intros P x. exact x. Qed.

Section QIPost.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A0 : AA) (rho0 : valuation).
Variables (A : AA) (it : Z * Z).
Local Notation qT := (ag_thread (aa_geom A)).
Local Notation qSB := (ag_spacebeg (aa_geom A)).
Local Notation qc := (it_cls it).
Local Notation qk := (Z.of_nat (length (cs_cache (cls_of A (it_cls it))))).
Local Notation qu := (fst it).
Local Notation qab := (fst it - rz (snd it)).
Local Notation qLEN := ((snd it + 7) / 8 * 8 / 8).
Local Notation qE := (ag_thread (aa_geom A) + 208 + 80 * it_cls it).

Lemma qi_post : ltac2:(tb__ "0|3|
S0S0S0S7S5S2S0S0A2M0A1S5S3fA1M1G1S17S5S3cQ40A1A1S74S0S0S28G1S45VA;A1S9S3fA1M2A3S28S6S42VA;A1SaA3S0S91VA;R1A2S91VA0;R2A2F_;Fz;S78VA0;VA;A2S28G1S44VA;A1S4S3fS41R10S4G0Vit;RcA3RfA3S8S3fRbRaA3A3A3S52S37S77VK;VA0;Vrho0;VA;R11RfReS4G0Vit;RdA3RcRbAaS51Sa1Vit;A1A1RaR9R8A6S7cVA;Vit;RbR8R7A5S81RcReA2S7eRdR14R12R11Vit;A5S7fReR15R12Vit;A4S2cS17S17S29S52S37S77VK;VA0;Vrho0;S97S98VA;G2S4S3fS41R17R13R16A3S8S3fR12R11A3A3A3S8fVit;A1S90S43VA;A1Vit;A2A3R17R15S10R14A1R13R12R11AaS50R1RfReA6S29S81R1R12A2S29S7eR1R17R15R14Vit;A5S7fR1R17R14Vit;A4A2A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fnd;Fn0;Fs;Fa;").
Proof.
  intros a s n0 nd its tmp' rest rho tp w t st HTH HCI HQW HQP0 HGL H QE HVx HVi HVs. destruct w as [tr [ms md]].
  remember (vb_of it) as vb eqn:EVB.
  pose proof (SPA_axforms segsA _ _ rho _ _ tp _ (TQ1_eq vb) H) as H1.
  destruct (proj2 H1) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H1)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  pose proof (HSBD A rho tp tr md HK) as HSECB.

  pose proof QE as [_ _ _ _ QGEO QV QCV QIM _ _ _ QNF _ _ QIN QPR _]. unfold qgeo in QGEO. unfold it_ab in QGEO.
  destruct QGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  destruct HRIG as (E151 & E152 & E155 & E156).
  destruct QV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof (qe_nums A it rho t st QE) as NUMS. cbv zeta in NUMS. destruct NUMS as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  pose proof (qe_Sh A it rho t st QE) as SHF. cbv zeta in SHF. destruct SHF as (SH0 & SH1 & L0 & L1).
  pose proof (qe_E A it rho t st QE) as EVS. cbv zeta in EVS. unfold it_ab in EVS. destruct EVS as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  pose proof (qe_wins A it rho t st QE) as WINS. cbv zeta in WINS. apply hideP_intro in WINS.
  pose proof (ish_range A it rho t st QE) as RG_ish. cbv zeta in RG_ish.
  pose proof (cv_max _ _ _ _ _ QCV) as C_max. pose proof (cv_size _ _ _ _ _ QCV) as C_sz. unfold pc_entry in C_max, C_sz.
  pose proof HCB as (_ & HN0 & HN1 & _). unfold kQuarantineBatchCount in HN1. cbn [length] in HN0.
  assert (INB : In (mkQB a (it :: its) s) (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho _ BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). cbn [qb_addr] in BA1, BA2, BA3, BA4, BA5. unfold HIGH_SHADOW_END in BA4.
  pose proof HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  assert (HVB : vb = true -> rz (snd it) <> 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_true_iff in X; apply Z.eqb_neq in X; exact X).
  assert (HVBf : vb = false -> rz (snd it) = 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_false_iff in X; apply Z.eqb_eq in X; exact X).
  pose proof (carve_rti A it rho t st QE) as CRTI.
  pose proof (carve_itm A it rho t st QE) as CITM. cbv zeta in CITM. specialize (CITM vb HVB). unfold N_itm in CITM. cbn [app] in CITM. pose proof (Forall_inv CITM) as CRIE. clear CITM.
  set (R := RQP vb). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.

  assert (RG_hdr : obj_range rho (carve_obj hdrS) = (qu - 16 + 0, qu - 16 + 8)) by (unfold hdrS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite EvIT; reflexivity).
  assert (RG_ent : obj_range rho (carve_obj entS) = (qE + 0, qE + 16)) by (unfold entS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eent; reflexivity).
  assert (RG_slot : obj_range rho (carve_obj (slotS vb)) = (qE + 4 * qk + 16, qE + 4 * qk + 20)) by (unfold slotS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eslot; reflexivity).
  assert (RG_stq : obj_range rho (carve_obj stqS) = (qT + 2768, qT + 3168)) by (unfold stqS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite EvT; reflexivity).
  assert (RG_mag : obj_range rho (carve_obj magS) = (qab + 0, qab + 16)) by (unfold magS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite E210u; reflexivity).
  set (RNG := fun z : Z => (exists k0, In k0 NRO /\ fst (SMGlue.spec_range rho k0) <= z < snd (SMGlue.spec_range rho k0))
                \/ (Sh qu <= z < Sh qu + qLEN) \/ (qu - 16 <= z < qu - 8) \/ (qE <= z < qE + 16)
                \/ (qE + 4 * qk + 16 <= z < qE + 4 * qk + 20) \/ (qT + 2768 <= z < qT + 3168) \/ (vb = true /\ qab <= z < qab + 16)).
  assert (IRC : forall x, in_ranges rho R x -> RNG (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold RNG. unfold R, RQP in Ho. apply in_app_or in Ho as [Ho|Ho].
    - apply in_map_iff in Ho as (k0 & <- & Hk0). left. exists k0.
      assert (Hk0' : In k0 NRO) by (unfold NRO; apply in_or_app; left; exact Hk0). split; [exact Hk0'|].
      rewrite <- (carve_obj_range rho k0 (spec_litb_sound k0 (proj1 (forallb_forall _ _) NRO_lit k0 Hk0'))). exact Hz.
    - cbn [app In] in Ho. destruct Ho as [<-|[<-|Ho]].
      + right; left. rewrite RG_ish in Hz. cbn [fst snd] in Hz. lia.
      + left. exists rieS. assert (Hk0' : In rieS NRO) by (unfold NRO; apply in_or_app; right; left; reflexivity). split; [exact Hk0'|].
        rewrite <- (carve_obj_range rho rieS (spec_litb_sound rieS (proj1 (forallb_forall _ _) NRO_lit rieS Hk0'))). exact Hz.
      + unfold N_itmP in Ho. rewrite map_app in Ho. apply in_app_or in Ho as [Ho|Ho].
        * cbn [map In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
          -- right; right; left. rewrite RG_hdr in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; left. rewrite RG_ent in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; right; left. rewrite RG_slot in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; right; right; left. rewrite RG_stq in Hz. cbn [fst snd] in Hz. lia.
        * destruct vb; cbn [map In] in Ho; [|destruct Ho]. destruct Ho as [<-|[]].
          right; right; right; right; right; right. split; [reflexivity|]. rewrite RG_mag in Hz. cbn [fst snd] in Hz. lia. }

  assert (HNK : forall k0, In k0 NRO -> In (carve_obj k0) R /\ SMGlue.spec_small k0 /\ SMGlue.spec_covered k0
                 /\ cells_in_view rho (rd_of segsA (rm rho)) (fst (SMGlue.spec_range rho k0) - (let '(_, lo, _, _) := k0 in lo)) (let '(_, _, _, cs0) := k0 in cs0)).
  { intros k0 Hk0. assert (CK : carve_okq rho k0).
    { unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]]; [exact (proj1 (Forall_forall _ _) CRTI k0 Hk0) | exact CRIE]. }
    split; [|split; [|split]].
    - unfold R, RQP. unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]]; [apply in_or_app; left; apply in_map; exact Hk0 | apply in_or_app; right; right; left; reflexivity].
    - destruct k0 as [[[b0 lo0] hi0] cs0]. unfold carve_okq in CK. lazy beta iota zeta in CK. destruct CK as (K1 & K2 & K3 & _ & _ & K6 & _).
      unfold SMGlue.spec_small. lazy beta iota zeta. repeat split; assumption.
    - exact (SMGlue.coverb_sound k0 (proj1 (forallb_forall _ _) NRO_chk k0 Hk0)).
    - destruct k0 as [[[b0 lo0] hi0] cs0]. unfold carve_okq in CK. lazy beta iota zeta in CK. destruct CK as (_ & _ & _ & _ & _ & _ & _ & K8).
      cbn [SMGlue.spec_range fst]. lazy beta iota zeta. replace (bv_unsigned (eval rho b0) + lo0 - lo0) with (bv_unsigned (eval rho b0)) by lia. exact K8. }

  assert (INent : In (carved entQ 0 16 [(0, 4%nat, add (SVar 206) (SLit 1)); (4, 4%nat, SVar 207); (8, 8%nat, SVar 201)]) R)
    by (unfold R, RQP; apply in_or_app; right; apply in_or_app; right; unfold N_itmP; cbn [app map In]; right; left; reflexivity).
  assert (INslot : In (carved (add entQ (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 [(16, 4%nat, cptrQ vb)]) R)
    by (unfold R, RQP; apply in_or_app; right; apply in_or_app; right; unfold N_itmP; cbn [app map In]; right; right; left; reflexivity).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTQ R entQ 0 16 _ Hsm (TQ1_objsP vb) INent ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eent; lia) ltac:(rewrite Eent; lia)) as [AV1 _].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTQ R (add entQ (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 _ Hsm (TQ1_objsP vb) INslot ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eslot; lia) ltac:(rewrite Eslot; lia)) as [AV2 _].
  fold rho3 v3 in AV1, AV2. rewrite Eent in AV1. rewrite Eslot in AV2.
  assert (Ek1 : eval rho (add (SVar 206) (SLit 1)) = Z_to_bv 64 (qk + 1)) by (apply ev_add_lit; [cbn [eval]; exact E206 | lia | lia | lia]).
  assert (EBG : bv_unsigned (eval rho (if vb then SVar 210 else vIT)) = qab).
  { destruct vb; [exact E210u|]. rewrite EvIT. specialize (HVBf eq_refl). lia. }
  pose proof (HAU (it_cls it) C1) as AUc. rewrite kUserSpaceSize_val in AUc.
  assert (QD : 0 <= (qab - (qSB + qc * 2 ^ 32)) / 16 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (ECP : eval rho (cptrQ vb) = Z_to_bv 64 ((qab - (qSB + qc * 2 ^ 32)) / 16)).
  { apply bv_eq. rewrite (u64_lit ((qab - (qSB + qc * 2 ^ 32)) / 16)) by lia.
    unfold cptrQ. rewrite U_srl_lit, U_sub, U_sub, U_sll_lit, EBG. unfold vSB. cbn [eval]. rewrite E200, E155, !u64_lit by lia.
    change (32 mod 64) with 32. change (4 mod 64) with 4. unfold M64v. rewrite (Z.mod_small (qc * 2 ^ 32)) by lia.
    rewrite (Z.mod_small (qab - qc * 2 ^ 32)) by lia. rewrite Z.mod_small by lia. change (2 ^ 4) with 16. f_equal. lia. }
  assert (EID : it_id (aa_geom A) it = (qab - (qSB + qc * 2 ^ 32)) / 16)
    by (unfold it_id, it_ab, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (C_cnt3 : cell_ok v3 (mkACell qE 4 (qk + 1))) by (replace qE with (qE + 0) by lia; exact (av_cell v3 qE 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) Ek1)).
  assert (C_max3 : cell_ok v3 (mkACell (qE + 4) 4 (max_count qc))) by exact (av_cell v3 qE 4 4 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) E207).
  assert (C_sz3 : cell_ok v3 (mkACell (qE + 8) 8 (Size qc))) by exact (av_cell v3 qE 8 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E201).
  assert (C_slot3 : cell_ok v3 (mkACell (qE + 4 * qk + 16) 4 ((qab - (qSB + qc * 2 ^ 32)) / 16))) by exact (av_cell v3 (qE + 4 * qk) 16 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.

  set (CHGo := fun z : Z => (Sh qu <= z < Sh qu + qLEN) \/ (qu - 16 <= z < qu - 8) \/ (qE <= z < qE + 4)
                \/ (qE + 4 * qk + 16 <= z < qE + 4 * qk + 20) \/ (qT + 2768 <= z < qT + 3168) \/ (vb = true /\ qab <= z < qab + 16)).
  assert (VO : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho R (Z_to_bv 64 z) -> ~ CHGo z -> v3 z = v z).
  { intros z Hz Hin NC. pose proof (IRC _ Hin) as RN. rewrite u64_lit in RN by lia. unfold RNG in RN.
    destruct RN as [(k0 & Hk0 & Hr)|[X|[X|[X|[X|[X|X]]]]]]; try (exfalso; apply NC; unfold CHGo; tauto).
    - unfold v3, v. rewrite !view_in by lia.
      exact (SMGlue.absorb_specs_view rho _ tr (vms md tp ms) (vmd md) KEPTQ R NRO (rd_of segsA (rm rho)) Hsm (TQ1_objsP vb) HNK z k0 Hk0 Hr).
    - destruct (Z_lt_dec z (qE + 4)) as [L4|L4]; [exfalso; apply NC; unfold CHGo; right; right; left; lia|].
      destruct (Z_lt_dec z (qE + 8)) as [L8|L8]; [apply (cell_ok_same v v3 _ C_max C_max3); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ C_sz C_sz3); cbn [c_addr c_w]; lia]. }
  assert (PRS : forall z, v z <> None -> v3 z <> None).
  { intros z Hd. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|unfold v3, rho3; rewrite (proj2 (absorb_io rho R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj rho _ tr (vms md tp ms) (vmd md) KEPTQ R o Hsm (TQ1_objsP vb) Ho) as (X1 & _ & X3 & _). cbn zeta in X1, X3.
    assert (Do : ob_dflt o = DUnknown).
    { pose proof (proj1 (forallb_forall _ _) (RQP_unk vb) o Ho) as Y. cbv beta in Y. destruct (ob_dflt o); first [reflexivity | discriminate Y | (cbn in Y; discriminate Y)]. }
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl Do) (z - bv_unsigned (eval rho (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v3, rho3. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (z - bv_unsigned (eval rho (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  set (CHG := fun z : Z => (qab <= z < qu) \/ (Sh qu <= z < Sh qu + qLEN) \/ (qT + 208 <= z < qT + 3168)).
  assert (EQF : forall z, ~ CHG z -> v3 z = v z).
  { intros z NC. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io rho R (vms md tp ms)) z NI)].
    apply (VO z Hz Hin). intros HC. apply NC. unfold CHG, CHGo in *. clear - HC K16 C1 EU RZ.
    destruct HC as [X|[X|[X|[X|[X|[_ X]]]]]]; [right; left; exact X | left; lia | right; right; lia | right; right; lia | right; right; lia | left; lia]. }
  assert (NCHG : forall z, ~ (qT <= z < qT + 0x1000) -> (z < 0x7fff8000 \/ 0x10007fff8000 <= z) -> (z < qab \/ qu <= z) -> ~ CHG z).
  { intros z NT NBD NIT HC. unfold CHG in HC. clear - NT NBD NIT HC SH0 SH1 L0. lia. }

  assert (VRO : forall z k0, 0 <= z < 2 ^ 64 -> In k0 NRO -> fst (SMGlue.spec_range rho k0) <= z < snd (SMGlue.spec_range rho k0) -> v3 z = v z).
  { intros z k0 Hz Hk0 Hr. unfold v3, v. rewrite !view_in by lia.
    exact (SMGlue.absorb_specs_view rho _ tr (vms md tp ms) (vmd md) KEPTQ R NRO (rd_of segsA (rm rho)) Hsm (TQ1_objsP vb) HNK z k0 Hk0 Hr). }
  assert (INQW : forall z, (qab <= z < qu) \/ (Sh qu <= z < Sh qu + qLEN) -> QW A z).
  { intros z Hz. left. unfold qzone. rewrite (qall_A1 A HTH), HGL. apply Exists_cons_hd. right. cbn [qb_items]. apply Exists_cons_hd.
    split; [exact QPR|]. unfold it_ab. rewrite L1 in Hz. exact Hz. }
  assert (EQB : forall b, In b (aa_q_global A) -> forall z, qb_addr b <= z < qb_addr b + 8192 -> v3 z = v z).
  { intros b Hb z Hz. apply EQF. apply NCHG.
    - apply HSEP. unfold q_foot. rewrite HTH. cbn [app]. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
    - right. destruct (batch_addr_facts A HTH rho b BE Hb) as (_ & _ & _ & B4 & _). unfold HIGH_SHADOW_END in B4. lia.
    - assert (Hb' : In b (qall A)) by (rewrite (qall_A1 A HTH); exact Hb).
      assert (IBA : it_ab it + Size (it_cls it) <= qb_addr b \/ qb_addr b + 8192 <= it_ab it) by (eapply item_batch_apart; eassumption).
      unfold it_ab in IBA. clear - IBA Hz UN N8a. lia. }
  assert (NFRESH : ~ In it (its ++ qitems (tmp' ++ rest))).
  { pose proof (HIDS (it_cls it) C1) as ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. unfold q_ids in ND. apply NoDup_app_l in ND.
    rewrite (qall_A1 A HTH), HGL in ND. unfold qitems in ND. cbn [flat_map qb_items app] in ND.
    apply (head_item_fresh _ _ it _ ND). cbv beta. rewrite QPR, Z.eqb_refl. reflexivity. }
  assert (EQI : forall it', In it' (its ++ qitems (tmp' ++ rest)) -> forall z, it_ab it' <= z < fst it' -> v3 z = v z).
  { intros it' Hin' z Hz. assert (NE : it <> it') by (intros X; subst it'; exact (NFRESH Hin')).
    assert (Hin'' : In it' (qitems (qall A))) by (rewrite (qall_A1 A HTH), HGL; unfold qitems; cbn [flat_map qb_items app]; right; exact Hin').
    destruct (qitems_In A it' Hin'') as (b & Hb & Hib). pose proof (rz_facts (snd it')) as (RZ' & _). unfold it_ab in Hz.
    apply EQF. apply NCHG.
    - apply HSEP. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it'. split; [exact Hib|]. left. exact Hz.
    - destruct (is_primary (snd it')) eqn:EP.
      + pose proof (item_slot A HQPU HAU HG it' Hin'' EP) as IS'. cbv zeta in IS'. unfold it_ab in IS'.
        destruct IS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS' & _). unfold HIGH_SHADOW_END in HS'. right. lia.
      + destruct (HSECB it' Hin'' EP) as [X|X]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X; [left | right]; lia.
    - destruct (is_primary (snd it')) eqn:EP.
      + assert (IA : it_ab it + Size (it_cls it) <= it_ab it' \/ it_ab it' + Size (it_cls it') <= it_ab it) by (eapply items_apart; eassumption).
        pose proof (item_slot A HQPU HAU HG it' Hin'' EP) as IS'. cbv zeta in IS'. unfold it_ab in IS', IA.
        destruct IS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UN' & N1' & _). clear - IA Hz UN N8a UN' N1'. lia.
      + destruct (HKSECQ it' Hin'' EP) as [X _]. rewrite kSpaceSize_val in X. clear - X Hz R1 C1 UN N8a TOP. lia. }

  set (A' := push_cache (set_q A [] (mkQB a its s :: tmp' ++ rest)) (it_cls it) (it_id (aa_geom A) it)).
  assert (HK3 : K A' rho3 tp tr md).
  { unfold A'. apply (kq_push_item segsA K HL A rho rho3 tp tr md [] (tmp' ++ rest) a it its s s HTH HGL HCI QPR QNF); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io rho R (vms md tp ms)) z NI)].
      apply (VO z Hz Hin). intros HC. unfold CHGo in HC. destruct HC as [X|[X|[X|[X|[X|[_ X]]]]]].
      + apply NQ. apply INQW. right. exact X.
      + apply NQ. apply INQW. left. clear - X RZ. lia.
      + apply NPZ. left. unfold pc_entry. clear - X. lia.
      + apply NPZ. right. unfold pc_entry. clear - X. lia.
      + apply NQ. right. right. unfold qstat_zone. exact X.
      + apply NQ. apply INQW. left. clear - X RZ. lia.
    - intros z _ Hd. exact (PRS z Hd).
    - fold v3. unfold pc_entry. exact C_cnt3.
    - fold v3. unfold pc_entry. rewrite EID. replace (qT + 0xd0 + 80 * qc + 16 + 4 * qk) with (qE + 4 * qk + 16) by lia. exact C_slot3. }

  assert (HCB3 : CURB v3 a n0 (S nd) its).
  { pose proof (CURB_next _ _ _ _ _ _ HCB) as (Q1 & Q2 & Q3 & Q4 & Q5). unfold kQuarantineBatchCount in Q3.
    assert (EQa : forall z, a <= z < a + 8192 -> v3 z = v z) by (intros z Hz; exact (EQB _ INB z Hz)).
    split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply EQa; lia|]. split; [exact Q2|]. split; [exact Q3|].
    split; [eapply present_frame; [|exact Q4]; intros z Hz; apply EQa; unfold kQuarantineBatchSize in Hz; lia|].
    intros j it' Hj. destruct (Q5 j it' Hj) as [Cj Ij]. pose proof (nth_error_In _ _ Hj) as Hin'.
    assert (Hj' : (j < length its)%nat) by (apply (proj1 (nth_error_Some its j)); rewrite Hj; discriminate).
    split.
    - eapply cell_ok_frame1; [|exact Cj]. cbn. intros z Hz. apply EQa. lia.
    - eapply item_mem_frameP; [apply (proj1 (rz_facts (snd it'))) | intros z Hz; exact (EQI it' (in_or_app _ _ _ (or_introl Hin')) z Hz) | exact PRS | exact Ij]. }
  assert (HR3 : RMEM2 v3 (aa_geom A) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
    pose proof WINS as W2. unfold hideP in W2. destruct W2 as (WTI & _ & WTB & _ & _ & WTS & _).
    split; [|split; [|split; [|split]]].
    - clear WTI WTB WTS. apply Forall_forall. intros b Hb.
      assert (BP : batch_pure A b) by (apply (proj1 (Forall_forall _ _) (proj1 HQPU) b); rewrite (qall_A1 A HTH); exact (INQ b Hb)).
      apply (batch_mem_frameP A v v3 b BP); [| | exact PRS | exact (proj1 (Forall_forall _ _) HBM b Hb)].
      + intros z Hz. apply (EQB b (INQ b Hb)). lia.
      + intros it' z Hit' Hz. apply (EQI it'); [|exact Hz]. apply in_or_app. right. unfold qitems. apply in_flat_map. exists b. split; [exact Hb | exact Hit'].
    - clear WTI WTB WTS. apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply (EQB b (INQ b (in_or_app _ _ _ (or_introl Hb)))). lia.
    - clear WTI WTB WTS. apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply (EQB b (INQ b (in_or_app _ _ _ (or_intror Hb)))). lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (TOUT : forall z, qT + 0x50 <= z < qT + 0x70 -> v3 z = v z).
      { intros z Hz. apply EQF. unfold CHG. intros [X|[X|X]]; [clear - X Hz WTS R1 C1 UN N8a TOP; lia | clear - X Hz WTB SH0 SH1 L0; lia | clear - X Hz; lia]. }
      clear WTI WTB WTS.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z).
      { intros z Hz. apply EQF. unfold CHG. unfold QG in Hz. intros [X|[X|X]]; [clear - X Hz R1 C1 S2; lia | clear - X Hz SH0; lia | clear - X Hz WTI; lia]. }
      clear WTI WTB WTS.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }

  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_gen A0 rho0 rho rho3 (fun z => 0 <= z < 2 ^ 64 /\ in_ranges rho R (Z_to_bv 64 z)) (IRdec rho R) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity));
      [| | exact (proj2 (absorb_io rho R (vms md tp ms))) | | exact HFRM].
    - intros z [Hz Hin]. pose proof (IRC _ Hin) as RN. rewrite u64_lit in RN by lia. unfold RNG in RN.
      destruct RN as [(k0 & Hk0 & Hr)|[X|[X|[X|[X|[X|[_ X]]]]]]].
      + pose proof (VRO z k0 Hz Hk0 Hr) as EVz. unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]].
        * right. split; [|exact EVz]. right. left. rewrite <- EG. unfold N_rti in Hk0. cbn [In] in Hk0.
          repeat (destruct Hk0 as [<-|Hk0]; [cbn [SMGlue.spec_range fst snd] in Hr; rewrite ?EvC in Hr; cbn [eval] in Hr; rewrite ?u64_lit in Hr by lia; rewrite ?Z.add_0_l in Hr; unfold qrtc_zone; clear - Hr; first [tauto | (repeat right; lia)]|]).
          destruct Hk0.
        * left. right. right. left. exists (it_cls it). split; [exact C1|]. left. unfold rieS in Hr. cbn [SMGlue.spec_range fst snd] in Hr. rewrite Erie in Hr.
          unfold region_info, kRegionInfoStride. rewrite <- EG, kSpaceSize_val. clear - Hr. lia.
      + left. left. apply HQW. apply INQW. right. exact X.
      + left. left. apply HQW. apply INQW. left. clear - X RZ. lia.
      + left. right. left. rewrite <- EG. clear - X C1. lia.
      + left. right. left. rewrite <- EG. clear - X C1 K16. lia.
      + left. left. right. right. unfold qstat_zone. rewrite <- EG. exact X.
      + left. left. apply HQW. apply INQW. left. clear - X RZ. lia.
    - intros x [_ Hin] HBx. rewrite Z_to_bv_bv_unsigned in Hin.
      apply (SpineMallocS9.absorb_defined rho _ tr (vms md tp ms) (vmd md) KEPTQ R x Hsm (TQ1_objsP vb)); [| exact Hin | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HBx; unfold IMG_HI; clear - HBx; lia].
      apply Forall_forall. intros o Ho. exact (proj1 (forallb_forall _ _) (RQP_wr vb) o Ho).
    - intros x NP. apply (proj1 (absorb_io rho R (vms md tp ms))). intros Hin. apply NP. split; [apply urange|]. rewrite Z_to_bv_bv_unsigned. exact Hin. }

  assert (C_it3 : cell_ok v3 (mkACell (a + 24 + 8 * Z.of_nat nd) 8 (fst it - 16))).
  { unfold HVS in HVs. fold v in HVs. eapply cell_ok_frame1; [|exact HVs]. cbn. intros z Hz. apply (EQB _ INB). cbn [qb_addr]. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (TQ1 vb) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (TQ1 vb) KEPTQ R tp tr ms md (TQ1_objsP vb) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. rewrite TQ2_eq in HU.
  set (J' := JRI K A0 rho0 A' a n0 (S nd) its tmp' rest).
  assert (HU1 : SPA segsA J' (TQ2 vb) rho3 tp (tr, mkCfg ms md)).
  { split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HR3 | exact HF3]. }
  pose proof (SPA_facts_hold segsA _ rho3 (TQ2 vb) tp _ HU1) as HFa. rewrite (proj1 (TQ3_facts vb)) in HFa. apply Forall_app in HFa as [HFDI _].
  assert (HFpre : Forall (holds rho3) (pre_facts DEPTH_R)) by (unfold F_DI in HFDI; apply Forall_app in HFDI as [X _]; exact X).
  destruct (kq_facts segsA K HL A' rho3 tp _ _ HK3) as [_ HRIG3 HRTC3 _ _ _ _ _ _ _ _ HKTOP3 _].
  assert (HU2 : SPA segsA J' (addo (TQ2 vb) O_sb) rho3 tp (tr, mkCfg ms md)).
  { apply (carve_sb J' (TQ2 vb) rho3 tp _ (aa_geom A') HU1 (proj1 (TQ2_X vb)) (proj1 (TQ3_swf vb)) HRTC3 (proj1 (proj2 (proj2 HRIG3)))).
    rewrite TQ2_objs. exact (OBD_clear_sb A' rho3 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HKTOP3 HFpre). }
  assert (HU3 : SPA segsA J' (TQ3 vb) rho3 tp (tr, mkCfg ms md)).
  { pose proof HVi as (_ & E163 & _ & _ & _).
    apply (carve_slot_it J' (addo (TQ2 vb) O_sb) rho3 tp _ (a + 152 + 8 * Z.of_nat nd) (fst it - 16) HU2 (proj2 (TQ2_X vb)) (proj2 (TQ3_swf vb))).
    - unfold vS7. cbn [eval]. exact E163.
    - unfold vIT. cbn [eval]. exact E165.
    - lia.
    - lia.
    - replace (a + 152 + 8 * Z.of_nat nd - 128) with (a + 24 + 8 * Z.of_nat nd) by lia. exact C_it3.
    - rewrite TQ2a_objs. pose proof (OBD_fixed A' rho3 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HKTOP3 HFpre) as FX.
      change (topG (aa_geom A')) with (topG (aa_geom A)) in FX.
      eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho3 (topG (aa_geom A)) o _ _ Ho); lia. }
  assert (HU4 : SPA segsA J' (TQ4 vb) rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU3 | exact (TQ4_below vb) |]. intros HF. rewrite (proj2 (TQ3_facts vb)) in HF. exact (proj1 (proj1 (Forall_app _ _ _) HF)). }
  pose proof (JRI_stable K HL A0 rho0 A' a n0 (S nd) its tmp' rest) as HSTI.
  destruct (entM_SPA _ _ RIr MI rho3 tp _ (TQ4_ent vb) HSTI HU4) as (H7 & AG7 & V7 & RM7).
  assert (VV : forall i, In i [160; 161; 162; 163; 164; 165; 166; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho3 (infer_sub NPRE (ax_S (TQ4 vb)) (ax_S RIr))) i = rw rho i).
  { intros i Hi. rewrite (V7 i (SVar i)); [reflexivity|]. unfold MI, idm. apply in_map_iff. exists i. split; [reflexivity | exact Hi]. }
  eexists. split; [exact H7|].
  destruct HVx as (E184 & E185 & E186 & E187 & E208). destruct HVi as (E162 & E163 & E164 & E165' & E166).
  split; [unfold HVX; rewrite !VV by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !VV by (cbn; tauto); tauto|].
  unfold HVS. rewrite RM7. exact C_it3.
Qed.
End QIPost.
End SegQ3D_qiq.

(* [comment removed for export] *)
Module SpineCallocR3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "SLit"; "SVar"; "SAlu"; "rm"; "cell"; "ss_objs"; "sprop"; "ss_facts"; "SPBranch"; "eval"; "mkCell"; "obj_range"; "ss_lenient"; "ss_next"; "SExt"; "SPNot"; "ext_low"; "smatch"; "sstate"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "to_nat"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "bool"; "true"; "pair"; "prod"; "false"; "nat"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "PV4"; "PV6"; "PV7"; "keepn"; "GR"; "O_cell"; "PNX"; "O_pcm"; "O_ri"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3.POP"; "JRpop"; "phK"; "O_dstc"; "O_srcc"; "e_end"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "FAb"; "PCE"; "ph_fill"; "frozen"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "rmlink"; "entryR"; "gh_new"; "gh_nf"; "rlink"; "zoneR"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "skipn"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "view"; "acell"; "c_addr"; "c_w"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "pc_base"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_thread"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sext32_small : ltac2:(tb__ "0|2|
S0S3S1fZ0R1A2S20R1S25Z2Z1fA2A2A2S2S35Q40M0A1S1aS2aQ20S36G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low. apply bv_eq.
  assert (E : bv_unsigned (bv_extract 0 32 (Z_to_bv 64 z)) = z).
  { rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.shiftr_0_r.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia. }
  rewrite sext64_32_small by (rewrite E; lia). rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small. lia.
Qed.

Lemma view_absorb_out : ltac2:(tb__ "0|1|
S7S27S6A1S6fS0S6S68S6R1R4A3S4S3S1fS32S0S0S15R6R2A2M0A3R3A2S20R3S33S0S0G0A3A2A2A1F_;Fo;S2S2fS35Q8A1A1S74S34SdS6dR5R4R3A3A1R2A3S74S34SdR5A1R2A3A3F_;Fz;Fms;FR;Frho;").
Proof.
  intros rho R ms z Hout. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
  intros (o & Ho & Hr). apply (Hout o Ho). rewrite u64_lit in Hr by lia. exact Hr.
Qed.

Lemma rmlink_absorb : ltac2:(tb__ "0|1|
S35Q40A1S2fS35Q8A1A1F_;S7S27S6A1S6fS5eR4SdR3A1A2S6S68S6R1R4A3S5S1fS33S0S0S15R6R2A2M0A3S84A2S1fS83S32S0S0G0A3A2A2F_;Fo;S5eR6SdS6dR5R4R3A3A1A2F_;F_;Fms;FR;Frho;Ff0;").
Proof.
  intros f0 rho R ms H HR a Ha. rewrite rm_absorb_out; [exact (H a Ha)|].
  intros (o & Ho & Hr). rewrite u64_lit in Hr by (unfold IMG_LO, IMG_HI in Ha; lia). destruct (HR o Ho); lia.
Qed.

Lemma cell_ok_agree_range : ltac2:(tb__ "0|1|
S72S72S75S0S3S1fS76R2A1M0R1A2S20R1S1eG0S24S77R2A1A1A2A2A2S2S2fS35Q8A1A1R4R2A1R5R2A1A3F_;Fz;S73R4R2A2S73R4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma ph_eta : ltac2:(tb__ "0|0|
S5dS2S5dR1S57S5cR1A1S59R1A1S54R1A1S5aR1A1S58R1A1S5bR1A1A6A3Fp;").
Proof. intros p. destruct p. reflexivity. Qed.

Lemma nth_skipn_Z : ltac2:(tb__ "0|0|
S27S0A1S2eS2eS0S2S0S64S0R2S67S0R3R4A3R1A4S64S0S7fR3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. intros l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|]. destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH. Qed.

Section POP.

Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S5fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.

Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S3S2S0S5aVph;A1Z0A3S3S2S29S58Vph;A1S2dA3S2S29S5bVph;A1S2dA3A2A2").
Definition phK (i : Z) : phase := ltac2:(tb__ "0|0|
S57S5cVph;A1S59Vph;A1S54Vph;A1Vi;S2dS2dA6").
Variable faP : list Z.
Let nfP : Z := Z.of_nat (length faP).
Hypothesis HSRC : ltac2:(tb__ "0|1|
S0S72S3S1fZ0M0R2A2S1fR2Vk;A2A2S62VA;Vrb;S4aR3A1S74S34SdVrb;A1A2R2A5S0S3S1fG0R1A2S20R1VnfP;A2A2S73R5S78S1eS52VA;Vrb;A2S21Z4R2A2A2U4S64S0S23R2A1VfaP;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Hypothesis HKF : k <= nfP.
Hypothesis HNFP : 4 * nfP <= 536870912.
Hypothesis HFILLR : ltac2:(tb__ "0|4|
S20Z0M0S54Vph;A1M1A2S3S1fG0S61VA;Vrb;A2M2A2S3S2S0S1eG2S60VA;Vrb;A2M3A2VnfP;A3S1fG1G3A2A2A2F_;").
Hypothesis HIDS : ltac2:(tb__ "0|0|
S0S68S0R1VfaP;A3S3S1fZ0R2A2S20R2S25Z2Z1cA2A2A2F_;Fx;").
Hypothesis HCACHE : ltac2:(tb__ "0|0|
S2S27S0A1S87S88Vc;S8cVA;Vnv;A2A2A1S67S0S23S22VnfP;Vk;A2A1VfaP;A3A3").

Lemma zone_thread : ltac2:(tb__ "0|2|
S0S0S3S1fS1eS86S85VA;A1A1M0Z120A2R1A2S20R1S1eG0Zc60A2A2A2S63VA;Vrb;S4aR3A1R2A4S3S1fS1eS53VA;Vrb;A2Z10A2M1R3A2S20R3S1eG1S21Z4R4A2A2A2A2F_;F_;Fz;Fi;").
Proof.
  intros i z Hz HZ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
  unfold zoneR, phK in HZ. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in HZ. fold nv c in HZ.
  unfold U0, F0, FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ. fold nv c in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; try exact X; exfalso.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFILLR X2) as (F1 & F2 & F3). unfold gh_nf, gh_new in *. fold nv c in F1, F2, F3, X.
    clear -X Hz F1 F2 F3 HNFP C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Definition JRpop (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVi;A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRpop_K : ltac2:(tb__ "0|0|
S0S89VKc;S49R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRpop_stable : ltac2:(tb__ "0|0|
S0S1S2S29S7dS43R1A2S2aA3S48S34R2S49R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H4 & H6). apply Pos.leb_le in Hn. unfold PNX in Hn.
  split; [|split].
  - eapply (JR_stable A Kc rb tp0 md0 (phK i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw PV4) by (unfold PV4; lia). exact H4.
  - destruct Hag as (Hw & _). rewrite <- (Hw PV6) by (unfold PV6; lia). exact H6.
Qed.

Definition O_srcc : sobj := ltac2:(tb__ "0|0|
S42S3eS26SeS14SaZ0A1Z4SbS3fA1A3S28SeA1A3A2").
Definition O_dstc : sobj := ltac2:(tb__ "0|0|
S42S3dS26SeS14SaZ0A1Z4S18S2aQ20SbS3fA1A3A3S28SeA1A3A2").

Lemma pop_release : ltac2:(tb__ "0|6|
S1cS27S6A1M0S7S27S35Q40M1A1M2A1S27S6bA1M3S6fS6aS6aS0S3S1fZ0M4R1A2S20R1Vk;A2A2S2G0SfRaA1S30S6R9S26S6S4cS26S6S4bS28S6A1A3A3M5A3A3S1bS34R9RbS2bG3S80R7S81R6R5A2A4A4S2G2S9RaS3fA2S36G1S64S0S23S1eS22VnfP;Vk;A2R4A2A1VfaP;G4A4A2A3S49R5RbRaR9R6A5S6dRcG5R9A3S7S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eR7Z1A2A1R1RcRbR8AaS3S2G2S9R1S3dA2S9RdS3dA2A3S2G2S9R1S3eA2S9RdS3eA2A3A2A2Tr3;F_;F_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FS;").
Proof.
  intros S K r2 tp tr ms md mdJ i Hi HO Hsm H7 ((HFz & HGh & HKc' & HM & HR & HRM) & H4 & H6) r3.
  split; [|split; reflexivity].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & _ & (_ & N6) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (Hid : 0 <= idv < 2 ^ 28).
  { apply HIDS. unfold idv. apply nth_In. unfold nfP in *. lia. }
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  idtac "pr:1".
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RS : obj_range r2 O_srcc = (Si, Si + 4)).
  { unfold O_srcc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H6, u64_lit by (unfold Si in *; lia). f_equal; lia. }
  assert (RD : obj_range r2 O_dstc = (Di, Di + 4)).
  { unfold O_dstc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H4, u64_lit by (unfold Di in *; lia). f_equal; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).

  assert (M3S : forall j, (j < 4)%nat -> m3 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_srcc Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SVar PV7)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_srcc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H6, soff_lit_small, u64_lit in ASb by (unfold Si in *; lia).
    rewrite H7 in ASb. unfold m3. rewrite view_in by (unfold Si in *; lia). fold Si in ASb. replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M3D : forall j, (j < 4)%nat -> m3 (Di + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_dstc Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SExt true 32 (SVar PV7))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_dstc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H4, soff_lit_small, u64_lit in ASb by (unfold Di in *; lia).
    rewrite H7, sext32_small in ASb by lia. unfold m3. rewrite view_in by (unfold Di in *; lia). fold Di in ASb. replace (Di + 0 + Z.of_nat j) with (Di + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M2S : forall j, (j < 4)%nat -> m2 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m2 ltac:(lia) HR (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    unfold Si. exact Hc. }
  assert (AGR : forall z, ~ (Di <= z < Di + 4) -> m3 z = m2 z).
  { intros z Hz. destruct (Z_le_dec Si z) as [H1|H1]; [destruct (Z_lt_dec z (Si + 4)) as [H2|H2]|].
    - replace z with (Si + Z.of_nat (Z.to_nat (z - Si))) by lia. rewrite M3S, M2S by lia. reflexivity.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia. }
  idtac "pr:2".
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r2 [O_srcc; O_dstc] ms HRM); intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd];
           unfold IMG_LO, IMG_HI, Si, Di; rewrite ?FAr, ?PCr; unfold nfP in *; lia].
  fold m3. unfold rlink in HR |- *. fold m2 in HR.
  destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI : forall z, zoneR A rb (phK (i + 1)) z <-> (zoneR A rb (phK i) z \/ Di <= z < Di + 4)).
  { intros z. unfold zoneR, phK. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. fold nv c. unfold Di. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)); [left; right; right; right; right; right; left; lia | right; lia].
      + left; right; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; lia.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; left; lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec Di z) as [H1|H1]; [destruct (Z_lt_dec z (Di + 4)) as [H2|H2]|].
    + replace z with (Di + Z.of_nat (Z.to_nat (z - Di))) by lia. rewrite M3D by lia. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill phK] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLR ltac:(lia)) as (F1 & F2 & F3). unfold Di. rewrite PCr. rewrite FAr in Hz. change (Z.of_nat 4) with 4 in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj Hi K1 HNFP F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop phK] in Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold Di. rewrite M3D by exact Hj. do 3 f_equal. fold nv c. rewrite HCACHE, nth_skipn_Z.
      unfold idv. replace (Z.to_nat (nfP - k) + Z.to_nat i)%nat with (Z.to_nat (nfP - k + i)) by (clear -HKF Hi; lia). reflexivity.
    + eapply cell_ok_agree_range; [|exact (L4 i' ltac:(cbn [ph_pop phK]; lia))]. cbn [c_addr c_w]. intros z Hz. apply AGR. unfold Di. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
Qed.

Variable F : nat.
Variable CT0 : axst.
Variables LB LX : leafA.
Variable nob : nat.
Variable s_bk : wsub.
Let CT1 : axst := cT1 CT0.
Definition e_end : sv := ltac2:(tb__ "0|0|
ScS4eScS4eS79SaZ10A1A3ScS50S46SaZ2A1A3A3").
Definition NPOP : list carve_spec := ltac2:(tb__ "0|9|
S26S2cS2cS2cS8S0A2M0S0A2M1S27S2cS2cS0S2eA2M2S8A2M3A1M4A2M5S2bG1G4S2bG0S0S2bS8S0SbS3eA1Z0M6A4Z4M7A4S26G3S2bG2S8S2bS0S2eG6U4A4SbS3fA1A4S28G3A1M8A3A4S26G5S2bG1G4S2bG0S0S2bS8S0SbS3dA1G6A4G7A4G8A4S28G5A1A3A3").
Hypothesis SK_t : ltac2:(tb__ "0|1|
S2S27S2cS2cS8S8A2S8A2M0A1S66S6G0S7cSfS38VCT0;A1A1A4S66S6G0S7cS30S6S8bVW;A1S26S6S7aS26S6S7bS26S6S44S26S6S45S28S6A1A3A3A3A3A3A4A3").
Hypothesis XX_t : ax_X CT0 = [].
Hypothesis XF_t : ltac2:(tb__ "0|0|
S69S10S8aVW;Vst;A2S11S38VCT0;A1A1A3").
Hypothesis NX_t : ltac2:(tb__ "0|0|
S2S29S7eS17S38VCT0;A1A1S43A2S2aA3").
Hypothesis W_t1 : ltac2:(tb__ "0|0|
S2S29S1dS38VCT1;A1A1S2aA3").
Hypothesis R_t1 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z41570S26S0Z41584S28S0A1A3A3VCT1;S2aA5S31G0S26S3aVLB;S26S3aVLX;S28S3aA1A3A3A2A3").
Hypothesis LN_t1 : ltac2:(tb__ "0|0|
S2S29S16S38VCT1;A1A1S2dA3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLB;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLX;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S2S29S3bS40S39VLB;A1Vnob;A2VCT0;Vs_bk;A3S2aA3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S2S29S6eVs_bk;S41A2S2aA3").
Hypothesis S_bk4 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3dA2ScS4eSbS3dA1SaZ4A1A3A3").
Hypothesis S_bk6 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3eA2ScS4eSbS3eA1SaZ4A1A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S10S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3S11S38S39VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S10S19S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3A1S11S38S39VLX;A1A1A1A3").

Lemma pop_carve : ltac2:(tb__ "0|5|
S0S7S27S35Q40M0A1M1A1S71S3S1fZ0M2R4A2S20R4Vk;A2A2S47S34S49R5A1VCT0;R4R3R2A6S82R5S26S2cS1G1A2M3S2bS1G1S3fS36G0S64S0S23S1eS22VnfP;Vk;A2M4R6A2A1VfaP;G2A4A2A4S28G3A1A3A2S7S3S47S34S49R7A1VCT1;R1R5R4A6S2G1S9R1S3fA2S36G0S64S0S23S1eG4R7A2A1VfaP;G2A4A2A3A2Tr1;F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H r1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & (_ & MU0 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  split; [|exact E7].
  assert (AG1 : agree_below PNX r r1). { unfold r1. apply agree_below_rho_sets. intros j v [X|[]]. injection X as <- _. unfold PNX, PV7. lia. }
  assert (Erm1 : rm r1 = rm r) by (unfold r1; apply rm_rho_sets).
  assert (H1 : SPA segs (JRpop i) CT0 r1 tp w).
  { destruct H as [Hsm HJ]. split.
    - eapply smatchA_agree; [|exact Hsm]. apply Pos.eqb_eq in NX_t. rewrite NX_t. exact AG1.
    - eapply (JRpop_stable i PNX ltac:(reflexivity)); [exact AG1 | apply mat_equiv_refl | exact HJ]. }
  idtac "pc:1".
  destruct H1 as [HsmA1 HJ1]. pose proof HJ1 as ((HFz & HGh & _ & _ & HR & _) & H4 & H6). pose proof (proj1 HJ1) as HJ1'.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  pose proof (proj1 HsmA1) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CT0) [O_pcc0; O_st; O_pcm; O_ri] r1 _ HW HE HFz Hsm1 SK_t XF_t) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r1 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r1 os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r1 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r1 ori O_ri SKr) in RNr.
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  set (m1 := view segs (rm r1)) in *. unfold rlink in HR. fold m1 in HR.
  assert (ES : bv_unsigned (eval r1 (SVar PV6)) = Si) by (cbn [eval]; rewrite H6; apply u64_lit; unfold Si; lia).
  assert (ED : bv_unsigned (eval r1 (SVar PV4)) = Di) by (cbn [eval]; rewrite H4; apply u64_lit; unfold Di; lia).

  assert (MS : forall j, (j < 4)%nat -> m1 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m1 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 HJ1'))))) (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc. exact Hc. }
  assert (PD : forall z, Di <= z < Di + 4 -> exists b, m1 z = Some b).
  { intros z Hz. destruct HR as (L1 & L2 & _).
    assert (ZD : zoneR A rb (phK i) z \/ ~ zoneR A rb (phK i) z).
    { destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)) as [Y|Y]; [left; unfold zoneR, phK; cbn [ph_pop]; do 5 right; left; unfold Di in Hz; lia|].
      right. intros X. apply (zone_thread i z) in X; [lia|]. unfold Di in Hz. rewrite PCr in Hz. lia. }
    destruct ZD as [ZD|ZD].
    - specialize (L2 z ZD). destruct (m1 z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z ZD). destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
      destruct (pc_entry_facts0 segs A rb tp0 md0 nv HA Hnv Hcnt) as (_ & PE & _). cbn zeta in PE. fold c in PE. apply PE. unfold Di in Hz. rewrite PCr in Hz. lia. }
  idtac "pc:2".
  assert (SiR : ag_spacebeg (aa_geom A) <= Si /\ Si + 4 <= ag_spacebeg (aa_geom A) + 137438953472) by (unfold Si; rewrite FAr; lia).
  assert (DiR : ag_thread (aa_geom A) + 288 <= Di /\ Di + 4 <= ag_thread (aa_geom A) + 2656) by (unfold Di; rewrite PCr; lia).
  assert (HS1 : SPA segs (JRpop i) CT0 r1 tp w) by (split; [exact HsmA1 | exact HJ1]).
  apply (SPA_carve_list segs _ r1 CT0 tp w NPOP PNX1 HS1 W_t1).
  - apply Pos.eqb_eq in NX_t. rewrite NX_t. unfold PNX, PNX1. lia.
  - unfold NPOP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite ES. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
      split.
      { intros off Hoff. rewrite Erm1. specialize (MS (Z.to_nat off) ltac:(lia)). replace (Si + Z.of_nat (Z.to_nat off)) with (Si + off) in MS by lia.
        unfold m1 in MS. rewrite Erm1 in MS. rewrite view_in in MS by lia. eapply wok_rd_off_image; [|exact MS]. lia. }
      split; [|unfold xwords_clear; rewrite XX_t; intros rr y j []].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. rewrite E7. specialize (MS j Hj). unfold m1 in MS. rewrite view_in in MS by lia.
      replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) by lia. exact MS.
    + rewrite ED. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply Forall_nil|].
      split.
      { intros off Hoff. destruct (PD (Di + off) ltac:(lia)) as [b Hb]. unfold m1 in Hb. rewrite view_in in Hb by lia.
        eapply wok_rd_off_image2; [| |exact Hb]; lia. }
      split; [apply Forall_nil | unfold xwords_clear; rewrite XX_t; intros rr y j []].
  - cbn [map carve_obj NPOP]. unfold carved.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite obj_range_mk by lia; rewrite ?ES, ?ED; rewrite EO; apply Forall_app; split.
    + apply BZ. right; left. rewrite kSpaceSize_val. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; lia.
    + apply BZ. left. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; unfold Di in *; rewrite ?PCr in *; lia.
  - cbn [map carve_obj NPOP pairwise_disjoint]. unfold carved. split; [|split; [constructor | exact I]].
    apply Forall_cons; [|apply Forall_nil]. rewrite !obj_range_mk by lia. rewrite ES, ED. unfold ranges_disjoint; cbn [fst snd]. lia.
Qed.

Lemma e_end_val : ltac2:(tb__ "0|0|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S0S37Q40S13R3S4dA2A2S1eS1eS53VA;Vrb;A2Z10A2S21Z4Vk;A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  unfold e_end, vK. cbn [eval]. rewrite add_val, add_val, sll_val. rewrite EB, Q227, !u64_lit by lia. change (2 mod 64) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite (Z.mod_small (PCE A rb + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition JRrel (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eVi;Z1A2A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").

Lemma pop_iter : ltac2:(tb__ "0|1|
S0S7S27S35Q40A1A1S70S3S1fZ0R4A2S20R4Vk;A2A2S20S1eR5Z1M0A2Vk;A2S7VTR;S47S34S49S1eR7G0A2A1VCT0;R1R5A5R4A2Fr';F_;S2S0S1eR6G0A2Vk;A3S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R6A5R5A2Fr';F_;VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx.
  assert (NUM : 0 <= PCE A rb /\ PCE A rb + 16 + 4 * k + 8 < 2 ^ 62 /\ 1 <= k <= 8).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & _ & (T1 & T2 & _) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia. }
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0).
  set (r1 := rho_sets r [(PV7, Z_to_bv 64 idv)]).
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop i) CT1 r1 tp)); [intros w Hw; exact (proj1 (pop_carve i r tp w Hi Hw))|].
  apply (tr_run Kc TR KIT F [0x41570; 0x41584] CT1 [LB; LX] (JRpop i) r1 tp Q (JRpop_K i) (JRpop_stable i (ss_next (ax_S CT1)) eq_refl) R_t1 LN_t1).
  intros L r2 HL Hag.
  assert (NX1 : ss_next (ax_S CT1) = PNX1) by reflexivity. rewrite NX1 in Hag.
  assert (E72 : rw r2 PV7 = Z_to_bv 64 idv) by (destruct Hag as (Hw & _); rewrite <- (Hw PV7) by (unfold PV7, PNX1; lia); exact E7).

  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nob (ss_objs (ax_S (la_state LL))) ++ [O_srcc; O_dstc] ->
            forall w, SPA segs (JRpop i) (la_state LL) r2 tp w -> exists r3, SPA segs (JRrel i) (keepn (la_state LL) nob) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_srcc; O_dstc] (vms md tp ms)).
    apply (SPA_unobj_J (JRpop i) (JRrel i) r2 (la_state LL) _ [O_srcc; O_dstc] tp tr ms md HO Hw).
    intros Hsm HJ. pose proof HJ as (_ & H4 & H6).
    destruct (pop_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm E72 HJ) as (P1 & P2 & P3). cbn zeta in P1, P2, P3.
    split; [exact P1|]. split; [rewrite P2; exact H4 | rewrite P3; exact H6]. }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply negb_true_iff in BF. apply Z.eqb_neq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Hlt.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LB) nob) r3 tp) Q (REL LB OB_b)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRpop (i + 1)) CT0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J (JRrel i) (JRpop (i + 1)) _ CT0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & H4 & H6). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs.
    split; [|split].
    + eapply (JR_stable A Kc rb tp0 md0 (phK (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk4. cbn [eval]. rewrite H4. apply bv_eq. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
    + cbn [rho_sub rw]. rewrite S_bk6. cbn [eval]. rewrite H6. apply bv_eq.
      assert (FAR : 0 <= FAb A rb /\ FAb A rb + 536870912 + 8 < 2 ^ 62).
      { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
        destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
        unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
      rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply not_true_is_false in BF. apply negb_false_iff in BF. apply Z.eqb_eq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LX) nob) r3 tp) Q (REL LX OB_x)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phK k)) (keepn (la_state LX) nob) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J (JRrel i) (JRp (phK k)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma pop_loop : ltac2:(tb__ "0|0|
S2eS0S7S27S35Q40A1A1S70S2S0S22Vk;R4A2S24R5A1A3S3S1fZ0R5A2S20R5Vk;A2A2S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R5A5R4A2Fr';VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [lia|].
  apply (pop_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [lia | lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variable J0 : axst.
Variable LT0 : leafA.
Variable s_in : wsub.
Variable e_src : sv.
Hypothesis R_t0 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z41570S26S0Z41584S28S0A1A3A3VJ0;S2aA5S31G0S26S3aVLT0;S28S3aA1A3A2A3").
Hypothesis LN_t0 : ltac2:(tb__ "0|0|
S2S29S16S38VJ0;A1A1S2dA3").
Hypothesis NX_t0 : ltac2:(tb__ "0|0|
S2S29S7dS41S17S38VJ0;A1A1A2S2aA3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S2S29S3bS39VLT0;A1VCT0;Vs_in;A3S2aA3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S2S29S6eVs_in;S41A2S2aA3").
Hypothesis S_in4 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3dA2ScS4eS79SaZ10A1A3A3").
Hypothesis S_in6 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3eA2Ve_src;A3").
Hypothesis HSRCP : ltac2:(tb__ "0|1|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S35Q40M0A1S13R3Ve_src;A2S36G0S1eS52VA;Vrb;A2S21Z4S22VnfP;Vk;A2A2A2A2A3F_;F_;Fr;").

Lemma phK0 : phK 0 = ph.
Proof.
  destruct PH0 as (P1 & P2 & P3).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phK; rewrite P1, P2, P3; reflexivity | symmetry; apply ph_eta].
Qed.

Lemma pop_all : ltac2:(tb__ "0|0|
S7S27S35Q40A1A1S70S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R3A5R2A2Fr';VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VJ0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41570; 0x41584] J0 [LT0] ph r tp Q R_t0 LN_t0 NX_t0).
  intros L r1 [<-|[]] _.
  assert (K1 : 1 <= k).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1. lia. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop 0) CT0 (rho_sub r1 s_in) tp)); [|apply (pop_loop (Z.to_nat k) 0 _ tp Q); [lia | lia | exact HX]].
  intros w Hw. apply (SPA_entails_J (JRp ph) (JRpop 0) _ CT0 s_in r1 tp w ENT_in); [|exact Hw].
  intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
  split; [|split].
  - rewrite phK0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
  - cbn [rho_sub rw]. rewrite S_in4. cbn [eval].
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & _).
    apply bv_eq. rewrite add_val, EB, !u64_lit.
    + rewrite Z.mod_small; [lia|]. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + lia.
  - cbn [rho_sub rw]. rewrite S_in6. rewrite (HSRCP r1 HFz HGh). f_equal. lia.
Qed.
End POP.
End SpineCallocR3.

(* [comment removed for export] *)
Module SpineMallocR10.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "SAlu"; "eval"; "ss_next"; "ss_facts"; "valuation"; "sprop_below"; "ss_objs"; "swf"; "smatch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "sym_runA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "true"; "nat"; "prod"; "pair"; "Some"; "app"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "lt"; "pow"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "rMS"; "sMS"; "GR"; "nxt"; "O_pcm"; "O_ri"; "addobjs"; "idx_rot"; "nobj"; "pcof"; "relM"; "updR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "sh_e"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10"; "a2_e"; "cMr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition a2_e (eb : sv) : sv := ltac2:(tb__ "0|1|
S7S49S7S47S7S48S7S47Veb;S5Z3fff8A1A3S5Z3A1M0A3S5Z1A1A3S7S48Veb;G0A3A3").
Definition cMr (E : axst) : axst := ltac2:(tb__ "0|2|
S34S17S6A1M0VE;S32VE;A1S16S1cS1bS4A2M1S1dS1bS4UcS5Z8000A1A4S17G1A1A3S17S3A1S21G0S2cVE;A1A8").
Definition cMc (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|0|
S2fS53VE;A1S16S3S43Veb;A1S17S3A1A3S2cVE;A1A3").
Definition dMSf (C : axst) : axst := ltac2:(tb__ "0|0|
S62S51VC;S2aVC;A1S29VC;A1A3SaS11VC;A1A1A2").

Lemma idx_rot_ok : ltac2:(tb__ "0|1|
S1bS58U1M0R1A2S1bS2S56S1bR1S1fS1bS3fG0S46R3G0A2A2S16S1bU0S17S1bA1A3A3A3S59R1R3A2A2Fi;F_;Fn;").
Proof.
  intros n Hn i. rewrite in_app_iff, in_seq. cbn [In]. lia.
Qed.

Section VALS.
Variables (r : valuation) (eb : sv) (B : Z).
Hypothesis EB : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;Veb;A2A2VB;A3").
Hypothesis HB : ltac2:(tb__ "0|1|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S0S22S25VB;Z10000A2G0A3A2A2").

Lemma a2_val : ltac2:(tb__ "0|0|
S0S3bQ40A1S8Vr;S52Veb;A1A2S8Vr;S5Z8000A1A2A3").
Proof.
  destruct HB as (B0 & B1 & BM). destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) BM) as [q Hq].
  unfold a2_e. cbn [eval]. apply bv_eq. rewrite sub_val, add_val, !srl_val, add_val, EB, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (B + 262136)) by lia. rewrite Hq.
  replace ((q * 65536 + 262136) / 8) with (q * 8192 + 32767) by (apply Z.div_unique with 0; lia).
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  rewrite (Z.mod_small (q * 8192 + 32767 + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sh_val : ltac2:(tb__ "0|0|
S0S22S3cQ40S8Vr;S44Veb;A1A2A2S4dVB;A1A3").
Proof.
  destruct HB as (B0 & B1 & BM). unfold sh_e, gsv, shb. cbn [eval]. rewrite add_val, srl_val, EB, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Sh.
  pose proof (Z.div_le_upper_bound B 8 (2 ^ 59) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
Qed.
End VALS.

Section MEMSET.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S50Vst;S4fA3S0S18S4eA1VW;S17S4eA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S37VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S0S1bS6bVp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S6aVA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SbS38Vrb;R1A2S39VA;Vrb;R2A3S0S22S3cQ40S8R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S24S23S69S68VA;A1A1M0Z100000000A2VB;A2S1S24S23VB;Z40000A2S23G0Z2000000000A2A2S0S22S25VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S18S3bQ40A1A1S40S3aVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S28S65R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (G1 : axst) (LM : leafA).
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S20S18S12A1M0A1S15S35VF;S16S22Zdb004S17S22A1A3VG1;S1aA5S1eG0S16S12VLM;S17S12A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S19S10S11VG1;A1A1S21A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S19S45S2bS9S11VG1;A1A1A2S1aA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S18S1cS1cS4S4A2S4A2M0A1S3dS3G0S54SdS11VEM;A1A1A4S3dS3G0S54S1fS3S6dVW;A1S16S3S66S16S3S67S16S3S2dS16S3S2eS16S3S42Veb;A1S17S3A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S57S6S6cVW;Vst;A2SaS11VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S19SeS11VCMR;A1A1S1aA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S20S1cS18S1cS4S4A2M0A1M1S18S6A1M2A2M3A1S5fS11VEM;A1S11VCMR;A1A2S1eG3S1dG1G2S16G0S1dS4S4S52Veb;A1S5Z8000A1A4S17G0A1A3S17S6A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S19SeS11VCMC;A1A1S1aA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S20S18S3A1M0A1S64VCMC;S4aS2aVCMC;A1A3S1eG0S29VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S19S63VCMC;S4aS2aVCMC;A1S29VCMC;A1S3dS12S13S14S4bA4A5S1aA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S19S45S5eS9S11VCMC;A1A1A2S1aA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S19S45S2bS9S11VCMC;A1A1A2S1aA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S19S55S6ScS9S11VCMC;A1M0A1A1SaG0A1A3S1aA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S19S55S6ScS9S11S51VCMC;S2aVCMC;A1S29VCMC;A1A3A1A1A1SaS11VCMC;A1A1A3S1aA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S19S60S30VDM;A1A1S1aA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S18S3A1SdS11VRM;A1A1M0S1fS3S3eS3S46S31VDM;A1U2A2G0A3S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3A3A3").

Let ph2 : phase := ph_set p 2 ph.
Let ph3 : phase := ph_set p 3 ph.

Lemma piece_nums : ltac2:(tb__ "0|2|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S1S0S22S25VB;Z10000A2G0A3S1S0S22S25S4dVB;A1M1Z1000A2G0A3S1S24Z2008fff7000G1A2S24S23G1Z8000A2Z10007fff8000A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _). destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & _).
  split; [clear -HB1 G13; lia|]. split; [clear -HB2 G14 TG; lia|]. split; [exact HB3|]. split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Lemma piece_release : ltac2:(tb__ "0|1|
SbS18S3bQ40A1A1S18S41A1M0S5aS40S40SfS35R6S11VRM;A1S1dG0S5bR4S5cR3R2A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;Vph2;R7R6R5R2AaS36VA;VKc;Vrb;Vtp0;Vmd0;Vph3;S61R8S16S3S42Veb;A1S16S3S43Veb;A1S17S3A1A3A3R5A3R7R6R3AaF_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr ms md mdJ Hsm (HFz & HGh & HK' & HM & HR & HRM).
  destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  set (R := [O_piece eb; O_shp eb]). set (r3 := rho_absorb r R ms).
  pose proof (HBv r HFz HGh) as EB.
  assert (RNp : obj_range r (O_piece eb) = (B, B + 262144)).
  { unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r (O_shp eb) = (Sh B, Sh B + 32768)).
  { unfold O_shp. rewrite obj_range_mk by (clear; lia). rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))). f_equal; clear; lia. }
  assert (G2 : ph_get p ph2 = 2%nat) by (unfold ph2; apply ph_get_set).
  assert (E3 : ph3 = ph_set p 3 ph2) by (unfold ph3, ph2; rewrite ph_set_set; reflexivity).
  assert (ZR : forall z, zoneR A rb ph3 z <-> (zoneR A rb ph2 z \/ B <= z < B + 262144)) by (intros z; rewrite E3; exact (zone_release A rb p ph2 z G2)).
  assert (ZS : forall z, Sh B <= z < Sh B + 32768 -> zoneR A rb ph2 z).
  { intros z Hz. unfold ph2. apply (zone_reveal A rb p ph z PH1). right. exact Hz. }
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  assert (MO : forall z, ~ (B <= z < B + 262144) -> ~ (Sh B <= z < Sh B + 32768) -> m3 z = m z).
  { intros z H1 H2. unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; assumption. }
  assert (MIN : forall z, (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) -> m3 z <> None).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz B0 B1 Q2 Q3; lia).
    destruct Hz as [Hz|Hz].
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_piece eb) Hsm OB_r (or_introl eq_refl)) as (_ & _ & ASp & _).
      cbn [ob_base O_piece ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_piece] in ASp. rewrite !soff_lit_small in ASp by (clear; lia). rewrite EB in ASp.
      destruct (ASp (or_intror eq_refl) (z - B) ltac:(clear -Hz; lia)) as [x Hx]. replace (B + (z - B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate.
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_shp eb) Hsm OB_r (or_intror (or_introl eq_refl))) as (_ & _ & ASp & _).
      cbn [ob_base O_shp ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_shp] in ASp. rewrite !soff_lit_small in ASp by (clear; lia).
      rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))) in ASp.
      destruct (ASp (or_introl eq_refl) (z - Sh B) ltac:(clear -Hz; lia)) as [x Hx]. replace (Sh B + (z - Sh B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|].
  split; [rewrite E3; exact (mlink_release A rb tp0 md0 p ph2 tp mdJ HM G2)|].
  split.
  - apply (rlink_quiet_intro A rb ph2 ph3 _ m m3); [unfold ph3; apply ph_quiet_set; exact PQ | | exact HR | |].
    + intros z Hz. apply ZR. left. exact Hz.
    + intros z Hz. apply MO; intros X; apply Hz; apply ZR; [right; exact X | left; exact (ZS z X)].
    + intros z Hz. apply ZR in Hz.
      assert (D : (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) \/ ~ (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768)) by (clear; lia).
      destruct D as [D|D]; [exact (MIN z D)|]. rewrite MO by (clear -D; lia).
      destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | exfalso; apply D; left; exact Hz].
  - apply (rmlink_absorb _ r R ms HRM). intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; unfold IMG_LO, IMG_HI.
    + pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. destruct CF0 as (_ & _ & _ & _ & _ & (_ & G13 & _) & _).
      destruct HBn as (HB1 & _). right. clear -HB1 G13. lia.
    + right. clear -Q2. lia.
Qed.

Theorem piece_map : ltac2:(tb__ "0|1|
SbS18S3bQ40A1A1M0S5dSbG0VTR;S4cS35S36VA;VKc;Vrb;Vtp0;Vmd0;Vph3;A6S33VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S4cS35S36VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VG1;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC. destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0xdb004] G1 [LM] ph r tp Q R_m LN_g NX_g).
  intros L r1 [<-|[]] _. fold EM.

  apply (tr_cut Kc TR KIT (list word * valuation) _ (fun x => SPA segs (JRp ph2) EM (snd x) (fst x ++ tp)) Q).
  { intros w Hw. destruct (piece_reveal A Kc rb tp0 md0 W st rho HW HE p eb ph PH1 PQ HBv HBn HROOM EM SK_m XF_m r1 tp w Hw) as (tpn & r' & H').
    exists (tpn, r'). exact H'. }
  intros [tpn r2]. cbn [fst snd]. set (tp2 := tpn ++ tp).

  apply (tr_pure Kc TR KIT (Forall (fun o => ranges_disjoint (obj_range r2 o) (Sh B, Sh B + 32768)) (ss_objs (ax_S EM)))).
  { intros w Hw. assert (G2 : ph_get p ph2 = 1%nat -> False) by (unfold ph2; rewrite ph_get_set; discriminate).
    destruct Hw as [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r2 CF0 RG HGh) as (EBx & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
    unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
    pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S EM) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r2 _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
    destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
    assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
    assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
    assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
    rewrite <- (obj_range_skel r2 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r2 os O_st SKs) in RNs.
    rewrite <- (obj_range_skel r2 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r2 ori O_ri SKr) in RNr.
    assert (RNp : obj_range r2 opc = (B, B + 262144)).
    { rewrite (obj_range_skel r2 opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r2 HFz HGh). f_equal; clear; lia. }
    assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
    destruct HBn as (HB1 & HB2 & _).
    rewrite EO. apply Forall_app. split.
    - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Q2 Q3. lia.
    - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Q2 Q3 HB1 HB2 C1 T1 T2 TB G13; lia. }
  intros OBJD.

  apply (jr_restate A Kc rb tp0 md0 TR KIT EM (ax_S CMR) _ _ ph2 r2 tp2 Q W_mr D_mr ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (a2_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))). }
  change (ax_setS EM (ax_S CMR)) with CMR.

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) CMC r2 tp2)).
  { intros w Hw. pose proof (proj2 Hw) as HJ. pose proof HJ as (HFz & HGh & _ & _ & HR & _).
    pose proof (sh_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))) as ESH.
    apply (SPA_carve_unk segs (JRp ph2) r2 CMR tp2 w (sh_e eb) (SLit 0) (SLit 32768) (nxt EM) Hw W_mc ltac:(apply Pos.le_refl)); rewrite ?ESH, ?soff_lit_small by (clear; lia).
    - clear; lia.
    - clear; lia.
    - clear -Q2; lia.
    - clear -Q3; lia.
    - replace (Sh B + 0) with (Sh B) by (clear; lia). change (ss_objs (ax_S CMR)) with (ss_objs (ax_S EM) ++ []). rewrite app_nil_r. exact OBJD.
    - intros a Ha. assert (Ha64 : 0x643000 <= a < 2 ^ 64) by (clear -Ha Q2 Q3; lia).
      assert (ZN : zoneR A rb ph2 a) by (unfold ph2; apply (zone_reveal A rb p ph a PH1); right; fold B; clear -Ha; lia).
      pose proof (proj1 (proj2 HR) a ZN) as D. rewrite view_in in D by (clear -Ha64; lia).
      pose proof (wok_rd_off_image (rm r2) a) as WK.
      destruct (rd_of segs (rm r2) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
    - unfold xwords_clear. change (ax_X CMR) with (ax_X EM). rewrite XX_m. intros rr y j []. }

  apply (tr_facts Kc TR KIT). intros HFC.
  apply (tr_memset Kc TR KIT (JRp ph2) CMC (sMS CMC) (rMS CMC) r2 tp2 Q (JR_K A Kc rb tp0 md0 ph2)
           (JR_stable A Kc rb tp0 md0 ph2 _ HKc ltac:(apply Pos.leb_le; exact NX_ms)) ltac:(apply Pos.leb_le; exact NF_ms) E_ms CHK_ms).
  intros r3 tp3 Hag.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) DM r3 tp3)).
  { intros w Hw. apply SPA_refacts; [exact Hw | exact FBT_ms |]. intros _. exact (Forall_holds_agree _ r2 r3 _ Hag FBC_ms HFC). }

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) RM r3 tp3)).
  { intros w Hw. apply (SPA_select segs (JRp ph2) r3 DM (idx_rot DM) tp3 w Hw ND_r).
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi.
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi. }
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JRp ph3) (relM DM) r4 tp3) Q); [|intros r4; exact (HC r4 tp3)].
  intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_piece eb; O_shp eb] (vms md tp3 ms)).
  apply (SPA_unobj_J (JRp ph2) (JRp ph3) r3 RM _ [O_piece eb; O_shp eb] tp3 tr ms md OB_r Hw).
  intros Hsm HJ. exact (piece_release r3 tp3 tr (vms md tp3 ms) (vmd md) md Hsm HJ).
Qed.
End MEMSET.
End SpineMallocR10.

