(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From stdpp Require list.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf4 InvQ8 ja.

(* [comment removed for export] *)
Module RebuildD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "bview"; "view"; "acell"; "c_addr"; "c_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "class_state"; "aa_cls"; "cs_empty"; "AA"; "aa_geom"; "aa_cache_inited"; "cs_cache"; "ag_spacebeg"; "ag_thread"; "ageom"; "cs_allocated_user"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "nthZ"; "bandtp_inv"; "class_repr"; "live_ids"; "model_inv"; "@Corelib.Init.Datatypes"; "nat"; "option"; "bool"; "length"; "list"; "true"; "Some"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "drain_cs"; "drain_keep"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "drain_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD"; "drain_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG"; "setclsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "q_pure"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma cell_ok_agree_rangeD : ltac2:(tb__ "0|1|
SdSdSfS0S1S6S10R2A1M0R1A2S8R1S5G0S7S11R2A1A1A2A2A2S2S28S30Q8A1A1R4R2A1R5R2A1A3F_;Fz;SbR4R2A2SbR4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma nth_skipnD : ltac2:(tb__ "0|0|
S2bS0A1S27S27S0S2S0S32S0R2S33S0R3R4A3R1A4S32S0S37R3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. induction l as [|a l IH]; intros [|n] i d; cbn; try reflexivity; [destruct i; reflexivity | apply IH]. Qed.

Lemma drainA_setcls : ltac2:(tb__ "0|0|
S17S0S2S29S19R2A1S2cA3S2S17S34R3R2A2S4bR3R2S35R2S22S14S15R3A1R2S16A4A2A3A3F_;Fc;FA;").
Proof. intros A c H. unfold drainA, setclsA, nthZ. rewrite H. reflexivity. Qed.

Lemma entry_cls_pureQ : ltac2:(tb__ "0|1|
SdS17S0S1S6Z1R1A2S6R1Z1eA2A2S24R4S18R3A1R3R2S22S14S15R3A1R2S16A4A5S50R4A1S4cR4S22S14S15R5A1R4S16A4S2eS0S25S18R5A1M0R5R4A3S4eG0S4fR5A1R4A3A3A3F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c Hc P4 HQP. pose proof (fun x => live_ids_valid m A c x Hc P4) as LVV. pose proof (q_ids_valid A c) as QVV.
  set (cs := nthZ (aa_cls A) c cs_empty) in *. unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & _ & ND & _ & _ & _ & TI10 & CV10 & MC10 & FC10).
  unfold cls_pure. split; [exact N1|]. split; [exact N2|]. split; [exact N4|]. split; [exact N5|].
  split; [pose proof (Zle_0_nat (length (cs_free_array cs))); lia|]. split; [lia|].
  split.
  { intros x Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx|Hx].
    - destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
      replace (16 * x) with (x * 16) by lia. split; [exact X1|]. split; [exact X2 | exact X3].
    - apply in_app_or in Hx as [Hx|Hx]; [exact (LVV x Hx) | exact (QVV x Hc HQP Hx)]. }
  split; [exact (proj1 (NoDup_ListNoDup _) ND)|]. split; [exact TI10|].
  split; [unfold slots in CV10; rewrite CV10, length_app; f_equal; lia|].
  exact (conj MC10 FC10).
Qed.

Definition drain_mem (A : AA) (c : Z) (vE v3 : bview) : Prop := ltac2:(tb__ "0|7|
S18VA;A1S1dS1cR1A1S0S1bR2A1S0S22S14S15VA;A1Vc;S16A4S14S35Vc;R1A2S14S7S2aS0S1fR2A1A2A1S0S36Vc;R3A2S27S5S5R6Zd0A2S9Z50Vc;A2A2S0S48R6Vc;A2S0S46R7Vc;A2S0S1S0S4S3bRbVc;R8R1A4M0A1S2S28S30Q8A1M1A1M2Vv3;R2A1VvE;R2A1A3F_;Fz;S1S0G0S3G1G1S2G2Vv3;R3A1S2dG1R1A2A3Lb;A2F_;Fz;S1SbVv3;ScR3U4M3S7R4A1A3A2S1S27S3aR1SaS4dVc;A1M4A1A2SbVv3;ScS5R3S9Z4S5R7S7R2A1A2A2A2G3S32S0S37R6R2A2S1aR9A1Z0M5A4A3A2F_;Fi;S1SbVv3;ScS5R2S44A2U8M6G5A3A2S1SbVv3;ScS5R2S45A2G6S5R5G4A2A3A2S1SbVv3;ScS5R2S41A2G6S20R6A1A3A2S1SbVv3;ScS5R2S3fA2G6S1eR7A1A3A2S1SbVv3;ScS5R2S3eA2G6G5A3A2S1SbVv3;ScS5R2S43A2G6S21R7A1A3A2S1SbVv3;ScS5R2S42A2G6G5A3A2SbVv3;ScS5R2S40A2U1G5A3A2A2A2A2A2A2A2A2A2A2A2A2Tfa;Tri;Tpce;Tkeep;Tnf;TcsD;Tcs;TSB;TT;TG;").

Section RD.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Theorem drain_rebuild : ltac2:(tb__ "0|4|
S17S13S13S2bS30Q40M0A1A1M1G1S38S38S0S39R8R7R5R3A4S1S6Z1R2A2S6R2Z1eA2A2S2S29S19RaA1S2cA3S2S0S7S2aS0S1aS22S14S15RbA1R4S16A4A1A2A1S47R4A1A3S4aRcR5SeS2fS12RbA1A2SeS2fS12RaA1A2A4S0S1S6S3dR1A2S8R1S3cA2A2S2S28S30Q8A1A1S12RdS31G0R2A2M2A2S12ReG2A2A3F_;Fa;S26S2fS34ReR7A2RaR8A4S23SeS2fS12RdA1A2RbA2S1S39S34R10R9A2M3ReRcRaA4S49VCST;VXGL;R10G3S12RfA1S12ReA1A6A2F_;F_;F_;F_;F_;F_;F_;F_;Fc;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md c HA C1 Hini HFULL HDM HRMI HMD HBT.
  rewrite (drainA_setcls A c Hini) in HMD |- *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *. set (cs := nthZ (aa_cls A) c cs_empty) in *.
  set (vE := view segs (rm rhoE)) in *. set (v3 := view segs (rm rho3)) in *.
  unfold drain_mem in HDM. cbv zeta in HDM. fold G T SB cs in HDM.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (keep := drain_keep c cs) in *.
  set (pce := T + 0xd0 + 80 * c) in *. set (ri := region_info SB c) in *. set (fa := free_array SB c) in *.
  destruct HDM as (VO & PRES & HCN & HDST & R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8').
  pose proof HA as (HG & _ & _ & HRest & _). fold G vE in HRest.
  destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (PC c C1) as PCc. fold G cs in PCc.
  pose proof (entry_cls_pureQ _ A c C1 PCc HQP) as HP0. fold G cs in HP0.
  destruct (kchunks_facts c C1) as (K1 & K2 & K3).
  assert (Hn : kchunks c <= Z.of_nat (length (cs_cache cs))) by (rewrite HFULL; clear -K1 K2; lia).
  destruct (drain_pure c cs _ C1 HP0 Hn) as (HP1 & LC & LCZ & LF & ECA & EMU & EAU & EMF). cbv zeta in HP1, LC, LCZ, LF, ECA, EMU, EAU, EMF.
  set (csD := drain_cs c cs) in *. fold keep in LC, ECA.
  pose proof (fs_footb_space G) as FSP. pose proof (fs_footb_thread G) as FTH.
  assert (MSP : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> maskv (fs_footb G) vE z = vE z).
  { intros z Hz. apply maskv_out. apply FSP; [exact HG | rewrite kSpaceSize_val; fold SB; exact Hz]. }
  assert (MTH : forall z, T <= z < T + 4096 -> maskv (fs_footb G) vE z = vE z).
  { intros z Hz. apply maskv_out. apply FTH; [exact HG | fold T; clear -Hz; lia]. }
  unfold class_repr in PCc. cbv zeta in PCc. fold SB in PCc. fold ri fa in PCc. fold nf in PCc.
  destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & R9 & _ & _ & _ & _ & _ & _ & _ & CI & _).
  destruct (CI Hini) as (_ & _ & _ & K4 & K5). fold T pce in K4.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  assert (NF0 : 0 <= nf) by (unfold nf; apply Zle_0_nat).
  assert (FAr : fa = SB + c * 4294967296 + 3758096384) by (unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; clear; lia).
  assert (RIr : ri = SB + 137438953472 + c * 128) by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; clear; lia).
  assert (NK : 4 * (nf + kchunks c) <= 536870912).
  { destruct HP1 as (_ & _ & _ & _ & _ & P5 & _ & _ & _ & _ & _ & P11). destruct (cap_facts c C1) as (_ & _ & _ & _ & FC & _).
    unfold kFreeArraySize in FC. fold csD in P5, P11. rewrite LF in P5. clear -P5 P11 FC. lia. }
  assert (GRW : drain_grows c cs = true -> cs_mapped_free_array cs < 4 * (nf + kchunks c)).
  { intros X. unfold drain_grows in X. fold nf in X. apply Z.ltb_lt in X. exact X. }
  cut (AInvQ (setclsA A c csD) rho3 tp md
       /\ (quarantine_repr (maskv (fs_footb G) vE) A -> quarantine_repr (maskv (fs_footb G) v3) (setclsA A c csD))
       /\ mem_keptA CST XGL A (setclsA A c csD) (rm rhoE) (rm rho3)); [intros (X1 & _ & X3); exact (conj X1 X3)|].
  apply (class_rebuild CST XGL HCST HXGL A rhoE rho3 tp0 tp md0 md c csD (drain_zone G c cs) HA C1 Hini); fold G; fold T SB; fold cs; fold pce ri fa nf; fold vE v3.
  - exact HP1.
  - fold cs. rewrite EAU. clear; lia.
  - fold cs. rewrite EMU. clear; lia.
  - fold cs. exact (proj1 EMF).
  - rewrite LCZ, HFULL. clear -K1; lia.
  -
    intros z. unfold drain_zone. cbv zeta. fold T SB. fold pce ri fa nf. destruct (drain_grows c cs).
    + assert (D : (pce <= z < pce + 4 \/ fa + 4 * nf <= z < fa + 4 * (nf + kchunks c) \/ ri <= z < ri + 128
                    \/ (fa + cs_mapped_free_array cs <= z < fa + cs_mapped_free_array cs + kFreeArrayMapSize
                        \/ Sh (fa + cs_mapped_free_array cs) <= z < Sh (fa + cs_mapped_free_array cs) + 32768))
                   \/ ~ (pce <= z < pce + 4 \/ fa + 4 * nf <= z < fa + 4 * (nf + kchunks c) \/ ri <= z < ri + 128
                    \/ (fa + cs_mapped_free_array cs <= z < fa + cs_mapped_free_array cs + kFreeArrayMapSize
                        \/ Sh (fa + cs_mapped_free_array cs) <= z < Sh (fa + cs_mapped_free_array cs) + 32768))) by (clear; lia).
      destruct D as [D|D]; [left | right; intros X; apply D]; tauto.
    + assert (D : (pce <= z < pce + 4 \/ fa + 4 * nf <= z < fa + 4 * (nf + kchunks c) \/ ri <= z < ri + 128)
                   \/ ~ (pce <= z < pce + 4 \/ fa + 4 * nf <= z < fa + 4 * (nf + kchunks c) \/ ri <= z < ri + 128)) by (clear; lia).
      destruct D as [D|D]; [left; tauto | right; intros X; apply D].
      destruct X as [X|[X|[X|(X & _)]]]; [tauto | tauto | tauto | discriminate X].
  -
    intros z HZ. unfold drain_zone in HZ. cbv zeta in HZ. fold T SB in HZ. fold pce ri fa nf in HZ. fold cs nf. unfold envR.
    destruct HZ as [X|[X|[X|(HGr & [X|X])]]].
    + right; left. unfold pce in X. clear -X. lia.
    + right; right; right; left. rewrite FAr in X. clear -X K1 NK. lia.
    + left. rewrite RIr in X. clear -X. lia.
    + right; right; right; left. rewrite FAr in X. unfold kFreeArrayMapSize in X. pose proof (GRW HGr) as GL. clear -X N6 GL N5 K1 NK. lia.
    + right; right; right; right; right. rewrite FAr in X.
      pose proof (Geometry.Sh_mono (SB + c * 2 ^ 32 + cs_mapped_user cs) (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) ltac:(clear -N2 N3 N6 NF0; lia)) as M1.
      assert (M2 : Sh (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) + 32768 <= Sh (SB + c * 2 ^ 32 + 2 ^ 32)).
      { pose proof (GRW HGr) as GL. unfold Sh.
        pose proof (Z.div_le_mono (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) 8 ltac:(clear; lia) ltac:(clear -N6 GL K1 N5 NK; lia)) as D.
        replace (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs + 262144) with ((SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) + 32768 * 8) in D by (clear; lia).
        rewrite Z.div_add in D by (clear; lia). clear -D. lia. }
      clear -X M1 M2. lia.
  - exact VO.
  - exact PRES.
  - exact HRMI.
  - exact R1'.
  - rewrite LF. exact R2'.
  - exact R3'.
  - rewrite EAU. exact R4'.
  - exact R5'.
  - rewrite EMU. exact R6'.
  - exact R7'.
  - exact R8'.
  -
    intros i x Hi. unfold csD, drain_cs in Hi. cbn [cs_free_array] in Hi. fold keep in Hi.
    destruct (Nat.lt_ge_cases i (length (cs_free_array cs))) as [LT|GE].
    + rewrite nth_error_app1 in Hi by exact LT. pose proof (R9 i x Hi) as CE.
      eapply cell_ok_agree_rangeD; [|eapply cell_ok_agree; [|exact CE]].
      * cbn [c_addr c_w]. intros z Hz. apply VO. intros HZ. unfold drain_zone in HZ. cbv zeta in HZ. fold T SB in HZ. fold pce ri fa nf in HZ.
        change (Z.of_nat 4) with 4 in Hz. rewrite FAr, RIr in HZ. rewrite FAr in Hz. unfold pce in HZ.
        pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _). fold G T in G4, G5.
        pose proof HA as (_ & _ & _ & _ & _ & HI3 & _). destruct (proj1 HI3) as (T3 & _). rewrite kSpaceSize_val in T3. fold G T SB in T3.
        assert (Li : Z.of_nat i < nf) by (unfold nf; clear -LT; lia).
        destruct HZ as [X|[X|[X|(HGr & [X|X])]]].
        -- clear -X Hz T3 C1 Li N6. lia.
        -- clear -X Hz Li. lia.
        -- clear -X Hz C1 Li N6. lia.
        -- unfold kFreeArrayMapSize in X. clear -X Hz Li N6. lia.
        -- assert (GS : 17594333495296 <= SB).
           { pose proof (geom_old _ HG) as X0. rewrite FS_total_val, kSpaceSize_val in X0. unfold HIGH_SHADOW_END in X0. fold G SB in X0. clear -X0. tauto. }
           assert (SHU : Sh (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) + 32768 <= 17594333495296).
           { pose proof (geom_numsS _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). fold G in TG.
             assert (S2 : SB + 2 ^ 37 + 4096 <= topG G).
             { pose proof (geom_old _ HG) as X0. rewrite FS_total_val, kSpaceSize_val in X0. unfold HIGH_SHADOW_END in X0. fold G SB in X0. clear -X0. tauto. }
             unfold Sh, SHADOW_OFF. pose proof (Z.div_le_upper_bound (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) 8 (2 ^ 44 - 32768 * 2) ltac:(clear; lia) ltac:(clear -S2 TG C1 N6; lia)). clear -H. lia. }
           clear -X Hz GS SHU Li C1 N6. lia.
      * cbn [c_addr c_w]. intros k Hk. symmetry. apply MSP. pose proof (nth_error_Some_lt _ _ _ Hi) as L. rewrite FAr. clear -Hk L C1 N6. fold nf in N6. lia.
    + rewrite nth_error_app2 in Hi by exact GE. set (j := (i - length (cs_free_array cs))%nat) in *.
      pose proof (nth_error_Some_lt _ _ _ Hi) as Lj. rewrite length_skipn in Lj.
      assert (Lj' : (j < Z.to_nat (kchunks c))%nat) by (unfold keep, drain_keep in Lj; clear -Lj Hn; lia).
      pose proof (HDST j Lj') as CE.
      assert (Ex : nth (keep + j) (cs_cache cs) 0 = x) by (rewrite <- nth_skipnD; exact (nth_error_nth _ _ 0 Hi)).
      rewrite Ex in CE. replace (fa + 4 * Z.of_nat i) with (fa + 4 * (nf + Z.of_nat j)) by (unfold j, nf; clear -GE; lia). exact CE.
  -
    rewrite LC. exact HCN.
  -
    intros i x Hi. unfold csD, drain_cs in Hi. cbn [cs_cache] in Hi. fold keep in Hi.
    pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (unfold keep, drain_keep; clear; lia).
    rewrite nth_error_firstn in Hi. replace (i <? keep)%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (K4 i x Hi) as CE.
    eapply cell_ok_agree_rangeD; [|eapply cell_ok_agree; [|exact CE]].
    + cbn [c_addr c_w]. intros z Hz. apply VO. intros HZ. unfold drain_zone in HZ. cbv zeta in HZ. fold T SB in HZ. fold pce ri fa nf in HZ.
      change (Z.of_nat 4) with 4 in Hz. rewrite FAr, RIr in HZ.
      pose proof HA as (_ & _ & _ & _ & _ & HI3 & _). destruct (proj1 HI3) as (T3 & _). rewrite kSpaceSize_val in T3. fold G T SB in T3.
      pose proof (geom_bands _ HG) as (_ & TB & _). fold G T in TB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB.
      assert (Li' : Z.of_nat i < 16) by (pose proof (max_count_le16 c C1); unfold keep, drain_keep in Li; clear -Li HFULL H; lia).
      destruct HZ as [X|[X|[X|(HGr & [X|X])]]].
      * clear -X Hz. lia.
      * unfold pce in Hz. clear -X Hz T3 C1 Li' NF0 K1 NK. lia.
      * unfold pce in Hz. clear -X Hz T3 C1 Li'. lia.
      * unfold pce in Hz. unfold kFreeArrayMapSize in X. pose proof (GRW HGr) as GL. clear -X Hz T3 C1 Li' N5 N6 NK GL. lia.
      * assert (SHB : 2147450880 <= Sh (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) /\ Sh (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) + 32768 <= 17594333495296).
        { pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). fold G T in G4, TG.
          assert (S2 : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
          { pose proof (geom_old _ HG) as X0. rewrite FS_total_val, kSpaceSize_val in X0. unfold HIGH_SHADOW_END in X0. fold G SB in X0. clear -X0. tauto. }
          unfold Sh, SHADOW_OFF. pose proof (Z.div_pos (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) 8 ltac:(clear -S2 C1 N6 NF0; lia) ltac:(clear; lia)).
          pose proof (Z.div_le_upper_bound (SB + c * 4294967296 + 3758096384 + cs_mapped_free_array cs) 8 (2 ^ 44 - 32768 * 2) ltac:(clear; lia) ltac:(clear -S2 TG C1 N6; lia)). clear -H H0. lia. }
        unfold pce in Hz. clear -X Hz TB SHB C1 Li'. lia.
    + cbn [c_addr c_w]. intros k Hk. symmetry. apply MTH. pose proof (max_count_le16 c C1). unfold pce. unfold keep, drain_keep in Li. clear -Hk Li C1 H HFULL. lia.
  - fold cs. rewrite EMU. intros z Hz. exfalso. clear -Hz. lia.
  - fold cs. rewrite EMU. intros z Hz. exfalso. clear -Hz. lia.
  -
    fold cs. intros z Hz. unfold drain_zone. cbv zeta. fold T SB. fold pce ri fa nf. unfold csD, drain_cs in Hz. cbn [cs_mapped_free_array] in Hz.
    destruct (drain_grows c cs) eqn:HGr; [|exfalso; clear -Hz; lia].
    right; right; right. split; [reflexivity|]. left. clear -Hz. lia.
  - exact HMD.
  - exact HBT.
Qed.
End RD.
End RebuildD.

(* [comment removed for export] *)
Module SpineMallocQ1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "list"; "nil"; "app"; "bool"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "rw"; "SLit"; "SPUle"; "valuation"; "SPAlign"; "ss_facts"; "ss_objs"; "SVar"; "agree_below"; "holds"; "obj_range"; "ranges_disjoint"; "smatch"; "sprop_below"; "ss_next"; "sstate"; "swf"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ag_spacebeg"; "ag_thread"; "budget_bound"; "class_state"; "cs_mapped_user"; "aa_cache_inited"; "aa_geom"; "ag_ctx"; "ageom"; "cs_allocated_user"; "cs_mapped_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "r0_of"; "factsQ"; "ghostl"; "NR0"; "XFQ"; "cQ0"; "entryRq"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cR0a"; "F_r0"; "F_r1"; "GR"; "O_pcm"; "O_ri"; "vAU"; "vMC"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "BASEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Size"; "kUserMapSize"; "max_count"; "region_info"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "F_clsD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "F_sp_high"; "KcA"; "UStopLe"; "V_DEPTH"; "pre_facts"; "top_high"; "tp_ok"; "ulink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "geom_ok"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "FAb"; "JR"; "gh_chx"; "gh_new"; "gh_nf"; "ghosts"; "ph0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "needs_populate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "JRf"; "rf_depth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1.ZONE"; "armint"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZONE.
Let segs : list Segment := segsA.

Definition armint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S21S1fS27S28S2fVG;A1M0Z120A2Vlo;A2S27Vhi;S28G0Zc60A2A2A2S21S1fS27S2eVG;A1M1Vlo;A2S27Vhi;S28S28G1S5cA2Z1000A2A2A2S1fS27S5fVlo;A2S27Vhi;S5eA2A2A2A2").

Lemma base_zone : ltac2:(tb__ "0|3|
S36S11S1dS2S4S66A1S65A2S4SbA1S9S9S79R7A1S7aR8A1S1aVsegs;R8R7R6A4SbS45SbR1R7A3S45SbR2S14RaA1A3F_;Fo;S20S4S2S2ScScA2ScA2M0A1S2aSbG0S3aR7A4S2aSbG0S3aS5bA4A3S17RbS71A2S27S39RdA1S28S25Q40M1SeRcPaA2A2S26G1SeRcS74A2A2A2A2S20S24G1A1M2SeRdP97A2S23G1S2fReA1A2A3S20G2SeReP98A2S23G1S35RfA1A2A3S89R10RbRaA3S2bSbSbS19S18R11R1A2S0S9S9RdRcA4A2Lo';RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fw;FS;FrhoE;FG;").
Proof.
  intros G rhoE S w objs lo hi HG0 HS3 Hsm Hsub HSK Hhigh Htop E151 E152 HI.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21 G1 G2 G3 G4 G10 G11.
  pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, CB, TI, CI.
  destruct HS3 as (PS1 & PS2 & _). rewrite kSpaceSize_val in PS1, PS2.
  pose proof (topG_range G) as TG.
  unfold armint, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HI. rewrite kSpaceSize_val in HI.
  destruct objs as [|osw orest]; [cbn [map BASEG] in HSK; exfalso; clear -HSK; discriminate HSK|].
  cbn [map BASEG] in HSK.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HSK).
  assert (SKrest : map skel orest = map skel (A_globals ++ RTG)) by exact (f_equal (@tl _) HSK).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm (Hsub osw (or_introl eq_refl)) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  constructor.
  - clear -SW0 G14 HI G6 TG. unfold ranges_disjoint. cbn [fst snd]. lia.
  - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
        clear -HI G5 G13 TI; lia.
    + unfold RTG, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx98, O_pgb, O_insta, O_insta2, O_cfb, O_cfc, O_rms.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E151, ?E152, ?u64_lit by (first [ clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI G5 G13 TI; lia | clear -HI G5 G6 TB TI PS1 G13 TG; lia | clear -HI G8 G9 CB CI PS2 G13 G24 TG G5 G6 G19; lia ]).
Qed.
End ZONE.

Definition NR0 : list carve_spec := ltac2:(tb__ "0|b|
S1S2S2S2ScS9A2M0S9A2M1S4S2S2S9S3A2M2ScA2M3A1M4A2M5S0G1G4S0G0S9S0ScS9S4eZ4M6A4Z8A4S1G3S0G2ScS0S9S3G6U4A4S56A4S5G3A1M7A3A4S1G5S0G1G4S0G0S9S0ScS9S5aZ0M8A4Z80A4S1G3S0G2ScS0S9S3G8U8M9A4SfG8A1MaA4S1G3S0G2ScS0S9S3Z10G9A4S59A4S1G3S0G2ScS0S9S3Z18G9A4S57A4S1G3S0G2ScS0S9S3Z20G9A4S55A4S1G3S0G2ScS0S9S3Z28G9A4GaA4S1G3S0G2ScS0S9S3Z30G9A4S58A4S1G3S0G2ScS0S9S3Z38G9A4GaA4S1G3S0G2ScS0S9S3Z44U1A4GaA4G7A3A3A3A3A3A3A3A3A4S5G5A1A3A3").
Lemma NR0_objs : ltac2:(tb__ "0|0|
S20S4SbA1S2aS6cSbS6bS41A4S1SbS53S1SbS54S5SbA1A3A3A3"). Proof. reflexivity. Qed.

Definition ghostl (A : AA) (rb : valuation) : list (positive * word) := ltac2:(tb__ "0|3|
S25Q40M0SeVrb;PcA2A2S9S3bR1A1S9S3cVA;R2A2S31S2eS34VA;A1A1S9S1S2SaS24G0A1M1A2M2S0SaG1PdcS23G0S62R3A1A2A4S1G2S0SaG1PddS23G0S82VA;Vrb;A2A2A4S1G2S0SaG1PdeS23G0S38R2A1A2A4S1G2S0SaG1PdfS23G0S37R2A1A2A4S1G2S0SaG1Pe0S23G0S32R2A1A2A4S1G2S0SaG1Pe1S23G0S63R1R3A2A2A4S1G2S0SaG1Pe2S23G0S7eVA;Vrb;A2A2A4S1G2S0SaG1Pe3S23G0S85R3A1A2A4S1G2S0SaG1Pe4S23G0S81VA;Vrb;A2A2A4S1G2S0SaG1Pe5S23G0S80VA;Vrb;A2A2A4S5G2A1A3A3A3A3A3A3A3A3A3A3TSB;Tcs;Tc;Tnv;").
Definition r0_of (A : AA) (rb : valuation) : valuation := ltac2:(tb__ "0|0|
S6dVrb;S40VA;Vrb;A2A2").

Lemma ghostl_ge : ltac2:(tb__ "0|1|
S2dS11SaS24Q40A1M0S45S2SaG0A2S0SaG0R2R1A4S40R4R3A2A3S8aPdcR3A2F_;Fv;Fj;Frb;FA;").
Proof. intros A rb j v H. unfold ghostl in H. cbn [In] in H. repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H. Qed.
Lemma r0_agree : ltac2:(tb__ "0|0|
S2dS11S16PdcR1S3eR2R1A2A3Frb;FA;").
Proof. intros A rb. apply agree_below_rho_sets. apply ghostl_ge. Qed.
Lemma r0_ghosts : ltac2:(tb__ "0|0|
S2dS11S83R2R1S3eR2R1A2A3Frb;FA;").
Proof.
  intros A rb. unfold ghosts, r0_of.
  assert (ND : List.NoDup (map fst (ghostl A rb))).
  { unfold ghostl. cbn [map fst]. repeat (constructor; [cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|]). constructor. }
  repeat split; apply (rw_rho_sets_in rb (ghostl A rb) _ _ ND); unfold ghostl; cbn [In]; tauto.
Qed.

Definition entryRq (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S25Q40M0SeVrb;PcA2A2S9S3bR1A1S9S3cVA;R2A2S31S1fS1fS7bVA;Vrb;A2S1fS20S24G0A1M1SeVrb;P9eA2S23G0R2A2A3S1fS20G1SeVrb;P94A2S23G0S60R2A1A2A3S20S7S86R2R1A2S8A3S27S28S32R2A1S61A2S7dR3A1A2F_;A2A2A2S1fS7cVA;Vrb;Vtp0;Vmd0;A4S1fS77VA;Vrb;A2S1fS22S1fS27S30VA;A1S49A2S1fS1fS27Z1R3A2S27R3Zfc00A2A2S1fS76VA;Vrb;A2S1fS20S9S3dVA;R3A2Z0A3S69Vmd0;A1A2A2A2A2A2A2A2A2Tcs;Tc;Tnv;").
Definition BASEOq (W : list ulink) : list sobj := BASEG.
Definition BASEFq (W : list ulink) (st : ustop) : list sprop := pre_facts rf_depth.

Definition XFQ : list sprop := ltac2:(tb__ "0|2|
S6SdS70S1SdS10S15S4bA1SfZ10000A1A2S1SdS12S4bZ4A2S1SdS12P97ZcA2S1SdS10SfZ1000M0A1M1S6fA2S1SdS10G1S6eA2S1SdS10SfS5dA1S4aA2S1SdS10S4aSfS29S29Z7fffff800000S5cA2G0A2A1A2S5SdA1A3A3A3A3A3A3A3A3").
Definition factsQ (E3 : axst) : list sprop := ltac2:(tb__ "0|0|
S6SdS13S2cVE3;A1A1S6SdS50S6SdS51S42A3A3A3").
Definition cQ0 (E3 : axst) : axst := ltac2:(tb__ "0|0|
S6aS4fVE3;A1S3fVE3;A1A2").

Section ENTRY.
Let segs : list Segment := segsA.

Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S20S4S2S2ScScA2ScA2M0A1S2aSbG0S3aS14S2cVE3;A1A1A4S2aSbG0S3aS6SbS5bS1SbS4cS1SbS4dS5SbA1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S47SdS75S88A1S13S2cVE3;A1A1A3").
Hypothesis NX3 : ltac2:(tb__ "0|0|
S20S7S8bS1cS2cVE3;A1A1PdcA2S8A3").
Hypothesis WR0a : ltac2:(tb__ "0|0|
S20S7S1eS2cS4fVE3;A1A1A1S8A3").
Hypothesis FB0 : ltac2:(tb__ "0|0|
S20S7S46SdS1bS52A1S3fVE3;A1A3S8A3").

Lemma refill_entry : ltac2:(tb__ "0|2|
S2dS72S9S9S11S4S24Q40M0A1A1S68S27S30R7A1S49A2S20S7S33R8A1S8A3S48Vsegs;S87R9R8R7R6A4VE3;R5R4R3A6S1fS20S9R8S3bS25G0SeR6PcA2A2A1A3S1fS44RaR6R5S64S67R4A1A1M1S5S78A1S73R6A7S48Vsegs;S7fRaR9R6R5G1S84A6S43VE3;A1S3eRaR6A2R5R4A6A2A2F_;F_;F_;Fw;Ftp;FrhoE;Fnv0;Fc0;FKc;FA;").
Proof.
  intros A Kc c0 nv0 rhoE tp w HBUD Hini H.
  pose proof H as [HsmA HJ]. destruct HJ as ((HA & HK & Htp & Htop & HRQ) & (Hnv0 & Hcls0 & E12 & E158 & E148 & Hc0 & Hroom)).
  destruct HRQ as (E151 & E152 & E155 & E156).
  assert (ENV : bv_unsigned (rw rhoE 12%positive) = nv0) by (rewrite E12; apply u64_lit; lia).
  set (nv := bv_unsigned (rw rhoE 12%positive)) in *. rewrite <- ENV in Hnv0, Hcls0. subst c0.
  change (SegQ_wf2.cls_of A (cls_of nv)) with (cst_of A nv) in Hc0, Hroom.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (Hnv : nv <= 64512) by lia.
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  split; [reflexivity|].
  split.
  { unfold entryRq. cbn zeta. fold nv.
    split; [exact (conj (conj E151 (conj E152 (conj E155 E156))) (conj E158 (conj E148 Hroom)))|].
    split; [exact HA|]. split; [exact Htp|]. split; [exact I|]. split; [exact HBUD|]. split; [exact Hnv0|]. split; [exact Htop|].
    split; [unfold cnt_of; rewrite Hc0; reflexivity|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  idtac "entry:1".

  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). pose proof HG as HG0.
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  pose proof (proj1 HI3) as HS3.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.
  pose proof (topG_range (aa_geom A)) as TG.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  assert (MS : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. fold G SB in P4.
  destruct P4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  idtac "entry:2".
  set (r0 := r0_of A rhoE).
  pose proof (r0_agree A rhoE) as AG0. pose proof (r0_ghosts A rhoE) as GH0. fold r0 in AG0, GH0.
  assert (Erm0 : rm r0 = rm rhoE) by (unfold r0, r0_of; apply rm_rho_sets).

  assert (Ha : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) E3 r0 tp w).
  { split.
    - eapply smatchA_agree; [|exact HsmA]. eapply agree_below_le; [|exact AG0]. apply Pos.leb_le. exact NX3.
    - unfold JR. split; [|split; [exact GH0|split; [exact HK|split; [|split]]]].
      + destruct AG0 as (Aw & Al & _). split; [exact Aw | exact Al].
      + unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
        repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
      + rewrite Erm0. unfold rlink, zoneR, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
        split; [intros; reflexivity|]. split.
        { intros z [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; exfalso; lia. }
        split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
      + intros a _. rewrite Erm0. reflexivity. }
  idtac "entry:3".

  destruct AG0 as (A0w & A0l & A0m).
  assert (R151 : rw r0 151%positive = Z_to_bv 64 T) by (rewrite <- (A0w 151%positive) by (clear; lia); exact E151).
  assert (R152 : rw r0 152%positive = Z_to_bv 64 (ag_ctx G)) by (rewrite <- (A0w 152%positive) by (clear; lia); exact E152).
  assert (R158 : rw r0 158%positive = Z_to_bv 64 c) by (rewrite <- (A0w 158%positive) by (clear; lia); exact E158).
  assert (R10 : rw r0 10%positive = rw rhoE 10%positive) by (rewrite <- (A0w 10%positive) by (clear; lia); reflexivity).
  assert (R15 : rw r0 V_DEPTH = rw rhoE V_DEPTH) by (rewrite <- (A0w V_DEPTH) by (unfold V_DEPTH; clear; lia); reflexivity).
  destruct GH0 as (Q220 & Q221 & Q222 & Q223 & Q224 & Q225 & Q226 & Q227 & Q228 & Q229).
  unfold gh_nf, FAb, cst_of in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold nv in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227. fold c in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold cs in Q221, Q222, Q223, Q224. fold G in Q225, Q226. fold SB in Q225, Q226.
  assert (EB : bv_unsigned (eval r0 pc_base) = T + 208 + 80 * c).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite R151, R158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 TG; lia).
    rewrite (Z.mod_small (c * 80)) by (clear -C1; lia). rewrite (Z.mod_small (T + 208)) by (clear -G5 G6 TG; lia). rewrite Z.mod_small by (clear -C1 G5 G6 TG; lia). clear; lia. }
  pose proof kSpaceSize_val as KSV.
  assert (RIr : SB + kSpaceSize <= region_info SB c /\ region_info SB c + 128 <= SB + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. clear -C1. lia. }
  assert (ERI : bv_unsigned (eval r0 vRI) = region_info SB c).
  { unfold vRI. cbn [eval]. rewrite Q225. apply u64_lit. rewrite kSpaceSize_val in *. clear -RIr G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }
  pose proof (proj1 Ha) as HsmA0. pose proof (proj1 HsmA0) as Hsm0. unfold virt in Hsm0. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm0.
  pose proof (smatch_facts_hold _ _ _ _ Hsm0) as HFa0.
  assert (HFX0 : forall p, In p (pre_facts rf_depth) -> holds r0 p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa0 p (XF3 p Hp)). }

  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact SK3)) as (ob & ox & EO & SKb & SKx).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range r0 oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel r0 oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r0 os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r0 os O_st SKs). unfold O_st, vT. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite R151, u64_lit by (clear -G5 G6 TG; lia). reflexivity. }
  assert (BZ : forall lo hi, armint G lo hi -> Forall (fun o' => ranges_disjoint (obj_range r0 o') (lo, hi)) ob).
  { intros lo hi HI. apply (base_zone G r0 (ax_S E3) _ ob lo hi HG0 HS3 Hsm0); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | exact R151 | exact R152 | exact HI].
    - apply HFX0. unfold pre_facts. cbn; tauto.
    - rewrite R10, R15. exact Htop. }
  idtac "entry:4".

  assert (PRT : forall z, T <= z < T + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G5 G6 TG; lia).
    eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hz G5 G6 TG; lia | clear -Hz TI; lia]. }
  assert (PRS : forall z, SB <= z < SB + kSpaceSize + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite kSpaceSize_val in Hz. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    eapply wok_rd_off_image; [|exact Hb]. clear -Hz G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }

  assert (CVT : forall a k v (e : sv), T <= a -> a + Z.of_nat k <= T + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MT in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G5 G6 TG; lia). rewrite Erm0, Ee. exact Hc. }
  assert (CVS : forall a k v (e : sv), SB <= a -> a + Z.of_nat k <= SB + kSpaceSize + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MS in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite kSpaceSize_val in Ha2.
    rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G13 G14 TG; unfold HIGH_SHADOW_END in *; lia). rewrite Erm0, Ee. exact Hc. }
  idtac "entry:5".
  assert (Hb : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) (cR0a E3) r0 tp w).
  { apply (SPA_carve_list segs _ r0 E3 tp w NR0 GR Ha WR0a).
    - apply Pos.leb_le in NX3. clear -NX3. unfold GR. lia.
    - unfold NR0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 G5 TG; lia|]. split; [clear -C1 G5 G6 TG; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRT; [clear -Hoff C1; lia|]. destruct (PE (T + 208 + 80 * c + off) ltac:(unfold T, G, c; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MT by (clear -Hoff C1; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        apply Forall_cons; [|apply Forall_nil]. intros j Hj.
        exact (CVT (T + 208 + 80 * c + 4) 4%nat (max_count c) vMC ltac:(clear -C1; lia) ltac:(clear -C1; lia) Q220 D2 j Hj).
      + rewrite ERI. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear -RIr G13; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [clear -RIr G13 G14 TG; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRS; [clear -Hoff RIr KSV; lia|]. destruct (PRI (region_info SB c + off) ltac:(unfold kRegionInfoStride; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MS by (clear -Hoff RIr KSV; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted in *.
        repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
        * exact (CVS (region_info SB c + 0) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R1 j Hj).
        * exact (CVS (region_info SB c + 16) 8%nat _ vNF ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q221 R2 j Hj).
        * exact (CVS (region_info SB c + 24) 8%nat _ vMFA ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q222 R3 j Hj).
        * exact (CVS (region_info SB c + 32) 8%nat _ vAU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q223 R4 j Hj).
        * exact (CVS (region_info SB c + 40) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R5 j Hj).
        * exact (CVS (region_info SB c + 48) 8%nat _ vMU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q224 R6 j Hj).
        * exact (CVS (region_info SB c + 56) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R7 j Hj).
        * exact (CVS (region_info SB c + 68) 1%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R8 j Hj).
    - idtac "entry:6". cbn [map carve_obj NR0].
      assert (RNm : obj_range r0 (carved pc_base 4 8 [(4, 4%nat, vMC)]) = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite EB. reflexivity. }
      assert (RNr : obj_range r0 (carved vRI 0 128 [(0, 8%nat, SLit 0); (16, 8%nat, vNF); (24, 8%nat, vMFA); (32, 8%nat, vAU); (40, 8%nat, SLit 0); (48, 8%nat, vMU); (56, 8%nat, SLit 0); (68, 1%nat, SLit 0)])
                    = (region_info SB c + 0, region_info SB c + 128)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite ERI. reflexivity. }
      destruct HS3 as (PS1 & _). fold T SB in PS1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite EO; apply Forall_app; split.
      + rewrite RNm. apply BZ. left. fold T. clear -C1. lia.
      + rewrite RNm. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
      + rewrite RNr. apply BZ. right; left. fold SB. clear -RIr KSV. lia.
      + rewrite RNr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1 RIr KSV PS1; lia.
    - cbn [map carve_obj NR0 pairwise_disjoint]. split; [|split; [constructor | exact I]].
      apply Forall_cons; [|apply Forall_nil]. unfold carved. rewrite !obj_range_mk by (clear; lia). rewrite EB, ERI.
      destruct HS3 as (PS1 & _). fold T SB in PS1. unfold ranges_disjoint; cbn [fst snd]. clear -C1 RIr KSV PS1. lia. }
  idtac "entry:7".

  unfold cQ0. apply (SPA_refacts segs _ r0 (cR0a E3) _ tp w Hb FB0).
  intros HF0.
  assert (R155 : rw r0 155%positive = Z_to_bv 64 SB) by (rewrite <- (A0w 155%positive) by (clear; lia); exact E155).
  assert (R148 : rw r0 148%positive = Z_to_bv 64 (Size c)) by (rewrite <- (A0w 148%positive) by (clear; lia); exact E148).
  unfold factsQ. apply Forall_app. split; [exact HF0|]. rewrite app_assoc. apply Forall_app. split.
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0.
  assert (DSB : exists q, SB = q * 2 ^ 16) by (apply Z.mod_divide in G12; [destruct G12 as [q Hq]; exists q; exact Hq | clear; lia]).
  destruct DSB as [q Hq].
  { unfold F_r0, F_r1, vMC, vK, vNF, vAU, vMU. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -K1 K2. lia.
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -C4. lia.
  - split; [clear; lia|]. rewrite Q225, u64_lit by (clear -RIr KSV G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    unfold region_info, kRegionInfoStride. rewrite KSV, Hq. replace (q * 2 ^ 16 + 2 ^ 37 + c * 128) with ((q * 512 + 2 ^ 30 + c) * 2 ^ 7) by (clear; lia). apply Z_mod_mult.
  - split; [clear; lia|]. rewrite Q226.
    unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize.
    rewrite u64_lit by (clear -C1 G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia).
    rewrite Hq. replace (q * 2 ^ 16 + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) with ((q * 16 + c * 2 ^ 20 + (2 ^ 20 - 2 ^ 17)) * 2 ^ 12) by (clear; lia). apply Z_mod_mult.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q221, !u64_lit by (clear -N6 NF0; lia). clear -N6. lia.
  - rewrite Q223, Q224, !u64_lit by (clear -N2 N3; lia). clear -N2. lia.
  - split; [clear; lia|]. rewrite Q224, u64_lit by (clear -N2 N3; lia). exact N1.
  - split; [clear; lia|]. rewrite R155, u64_lit by (clear -G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia). exact G12. }

  pose proof (geom_old _ HG0) as HG''. rewrite FS_total_val, kSpaceSize_val in HG''. unfold HIGH_SHADOW_END, IMG_HI, PG in HG''.
  destruct HG'' as (_ & _ & _ & _ & _ & _ & G7 & G8 & G9 & _).
  unfold XFQ, F_clsD, vT, vCTX, vSB, V_CLS, V_SIZE, HIGH_SHADOW_END. rewrite KSV. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?R158, ?R148, ?R151, ?R152, ?R155, ?u64_lit by (first [clear -C1; lia | clear -C2; lia | clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | clear -G13 G14 TG; lia | lia]).
  - clear -C1; lia.
  - clear -C1; lia.
  - clear -C2; lia.
  - split; [clear; lia|]. change (2 ^ 4) with 16. exact C3.
  - split; [clear; lia|]. change (2 ^ 12) with 4096. exact G7.
  - clear -G5; lia.
  - clear -G8; lia.
  - clear -G13; lia.
  - clear -G14 TG; lia.
Qed.
End ENTRY.
End SpineMallocQ1.

(* [comment removed for export] *)
Module RebuildGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "bview"; "maskv"; "view"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_mapped_user"; "cs_mapped_free_array"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "AA"; "aa_cache_inited"; "aa_cls"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "ageom"; "cs_empty"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Datatypes"; "length"; "Some"; "nat"; "option"; "app"; "bool"; "list"; "true"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "quarantine_repr"; "bandtp_inv"; "live_ids"; "model_inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@Stdlib.Lists.List"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG"; "setclsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ"; "envR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma class_rebuildC : ltac2:(tb__ "0|d|
S16S1fS1fS26S40Q40M0A1A1M1G1S28S28S0S12S0OF_;S3eRaR9R7R5A4SbS2Z1R4A2S2R4Z1eA2A2ScS25S17RcA1S27A3S19RdA1S1cS1bR1A1S0S1aR2A1S0S3dS12S18R10A1R9S1dA4S12S43R11RaR9A3S16S1S1R4Zd0A2S5Z50RbA2A2S0S37R4RcA2S0S34R5RdA2S0S36R6ReA2S0SaVsegs;S1eR14A1A2S8SaVsegs;S1eR16A1A2S8S45R11R10S24S0S3bRbR18R11A3S46RbS47R18A1R11A3A3A3S2S13R9A1S13R11A1A2S2S10RaA1S10R12A1A2S2S11RbA1S11R13A1A2S2S3S20S0S14R14A1A2A1S35R15A1A2S0SfR15R1A1M2SdG2A1A2Fz;S0R16R1A1S44R11R12R19S3S20S0S15R10A1A2A1S10R10A1R2A6F_;Fz;S0SdR17R1A1A1ScS23S40Q8A1M3A1M4RbR2A1RaR2A1A3F_;Fz;S0R18R1A1SeG3G3ScG4RdR3A1S21G3R1A2A3Lb;A2F_;Fz;S0SbS2S2bR1A2S4R1S2aA2A2ScG4S1eR21S41G0R2A2M5A2S1eR22G5A2A3F_;Fa;S6RcS7S1RfS32A2U8M6Z0M7A3A2S6RdS7S1R10S33A2G6S3S20S0S15R1bA1A2A1A3A2S6ReS7S1R11S2fA2G6S11R1cA1A3A2S6RfS7S1R12S2dA2G6S13R1dA1A3A2S6R10S7S1R13S2cA2G6G7A3A2S6R11S7S1R14S31A2G6S10R1fA1M8A3A2S6R12S7S1R15S30A2G6G7A3A2S6R13S7S1R16S2eA2U1G7A3A2S22S0ScS23S0A1M9S3fS0S15R24A1R2A3S21S0R1A2MaA3S6R17S7S1R19S5Z4S3R3A1A2MbA2U4McR2A3A2F_;Fx;Fi;S6R15S7R19GcS3S20S0S14R23A1A2A1A3A2S22S0ScG9S3fS0S14R26A1R2A3GaA3S6R19S7S1S1R1dZ10A2GbA2GcR2A3A2F_;Fx;Fi;S0SbS2S1R19S10R1eA1A2R1A2S4R1S1R19S10R26A1A2A2A2R26R2A1F_;Fz;S0SbS2S29S1R1aG8A2A1R1A2S4R1S29S1R1aS10R27A1A2A1A2A2R27R2A1F_;Fz;S0SbS2S1R1cS11R20A1A2R1A2S4R1S1R1cS11R28A1A2A2A2R28R2A1F_;Fz;S3cVsegs;R1fR2cR2aA4S3aR1bR2dA2SbS3eR21R30R2eR2cA4SbS39S9S38R25A1R1bA2R32A2S39S9S38R26A1R1dA2R22A2F_;S42VCST;VXGL;R32R21S1eR31A1S1eR30A1A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Trb;Tfa;Tri;Tpce;TAr;Tcs;TSB;TT;TG;F_;F_;F_;FZN;FcsR;Fc;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md c csR ZN HA C1 Hini G T SB cs Ar pce ri fa rb v3 vE
         HPURE HAUm HMUm HMFm HKC ZND HZE VO PRES HRMI R1' R2' R3' R4' R5' R6' R7' R8' HFA HCN HCC HNU HNS HNF HMD HBT.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
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
  fold mE in Hlive, PC, Hsec, Hdep, Hia, HTH, Hmisc, R1, R2, R3, R4, R5, R6, R7, R8, PRI, R9, PR, PU, PSH, PE, CI.
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
  { unfold Ar, setclsA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlenc. reflexivity. }
  assert (ECSo : forall c', c' <> c -> 0 <= c' -> nthZ (aa_cls Ar) c' cs_empty = nthZ (aa_cls A) c' cs_empty).
  { intros c' Hc' Hc'0. unfold Ar, setclsA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_other; [reflexivity|]. clear -Hc' Hc'0 C1. lia. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  destruct Hq as (HQP & HQMIN).
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
  assert (HLB : live_block_reprC m3 Ar).
  { apply (live_block_reprC_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [unfold Ar, setclsA; cbn [aa_cls]; rewrite length_list_upd; exact PL|].
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
  assert (HQR : quarantine_repr mE A -> quarantine_repr m3 Ar).
  { intros HqE. refine (quarantine_repr_agreeR mE m3 A Ar eq_refl eq_refl eq_refl eq_refl _ _ _ _ HqE).
    - intros c'. unfold Ar, setclsA, nthZ. cbn [aa_cls]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
      + rewrite <- E. rewrite nth_list_upd_same by exact Hlenc. exact HAUm.
      + rewrite nth_list_upd_other by exact NE. clear; lia.
    - intros z Hz. apply AGm. exact (QF_OUT z Hz).
    - intros z Hz. apply AGm. apply NE_T. left. fold G T in Hz. clear -Hz. lia.
    - intros z Hz. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI in *. clear -Hz. lia. }
  assert (HQP' : q_pure Ar).
  { apply (q_pure_mono A Ar eq_refl eq_refl eq_refl); [|exact HQP].
    intros c'. unfold SegQ_wf2.cls_of, Ar, setclsA, nthZ. cbn [aa_cls]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
    - rewrite <- E. rewrite nth_list_upd_same by exact Hlenc. exact HAUm.
    - rewrite nth_list_upd_other by exact NE. clear; lia. }
  assert (HQM : cell_ok m3 (mkACell (QG + 72) 8 kQuarantineMin)).
  { eapply cell_ok_agree; [|exact HQMIN]. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
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
  assert (HA' : AInvQC Ar rho3 tp md).
  { unfold AInvQC. cbv zeta. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [split; [exact HQP' | exact HQM]|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|]. split; [exact HQR|].

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
End RebuildGC.

(* [comment removed for export] *)
Module InvQ10a.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "NoDup"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "@Corelib.Init.Datatypes"; "prod"; "list"; "app"; "nat"; "fst"; "Some"; "cons"; "bool"; "snd"; "option"; "pair"; "false"; "length"; "nil"; "true"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "sec_chunk"; "sc_map_beg"; "mkQB"; "sc_map_size"; "aa_sec"; "aa_live"; "list_upd"; "aa_geom"; "aa_q_global"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qitems"; "qall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "map_remove"; "maps_subtract"; "vm_maps"; "iv_subtract"; "page_in_ranges"; "page_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "ranges_apart"; "hwN"; "hwS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "swap_remove"; "unmap_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "is_primary"; "PG"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "IMG_HI"; "IMG_LO"; "LOW_SHADOW_BEG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "SHADOW_GAP_BEG"; "dyn_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "in_maps"; "model_inv"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "set_q"; "item_pure"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.InvQ10a"; "L8text"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws ContractFreeNull RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nth_error_list_upd_same {T} : ltac2:(tb__ "0|0|
S13VT;A1S15VT;S49R2S1eVT;R3A2A2S1S1bVT;A1S8VT;S29VT;R4R3R2A4R3A3S17VT;R2A2A3F_;Fx;Fi;Fl;").
Proof. induction l; intros [|i] x H; cbn in *; try lia; auto. apply IHl. lia. Qed.

Lemma swap_remove_spec {T} : ltac2:(tb__ "0|2|
S13VT;A1M0S15VT;S1S1bVT;A1S8VT;R3R2A3S17VT;R1A2A3S5G0G0S5VT;VT;S2S1G0R6S14VT;R2S18VT;R1S1fVT;A1A3A3A3S2S4aR5S1eVT;R2A2M1A2S1G0S3aVT;R6R5A3S19G0L_;S54R5G1A2R2S29VT;R2R5R1A4X19x2A3A2A2Llst;A2Ll0;A2F_;Fc;Fi;Fl;").
Proof.
  intros l i c Hi. assert (NE : l <> []) by (intros ->; destruct i; discriminate Hi).
  destruct (exists_last NE) as (l0 & lst & ->). exists l0, lst. split; [reflexivity|].
  split. { pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hi; discriminate)) as L. rewrite length_app in L. cbn [length] in L. lia. }
  unfold swap_remove. rewrite length_app. cbn [length]. replace (length l0 + 1 - 1)%nat with (length l0) by lia.
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error]. rewrite removelast_last. reflexivity.
Qed.

Lemma swap_remove_length {T} : ltac2:(tb__ "0|0|
S13VT;A1S15VT;S1S1bVT;A1S8VT;R3R2A3S17VT;R1A2A3S1S15S1eVT;S3aVT;R4R3A3A2S4eS1eVT;R4A2U1A2A3F_;Fc;Fi;Fl;").
Proof.
  intros l i c Hi. destruct (swap_remove_spec l i c Hi) as (l0 & lst & -> & Hle & E). rewrite E, length_app. cbn [length].
  destruct (Nat.eqb i (length l0)); [|rewrite length_list_upd]; lia.
Qed.

Lemma swap_remove_nth {T} : ltac2:(tb__ "0|4|
S13VT;A1S15VT;S15VT;S1S1bVT;A1M0S8VT;R5R4A3S17VT;R3A2M1A3S1G0S8VT;S3aVT;R6R5A3R3A3S17VT;R2A2A3S2S49R4S4eS1eVT;R7A2U1A2M2A2S4S2S3S1S15R4R6A3M3A1S1G0S8VT;R7R4A3G1A3A2S2G3S2S49R6G2A2S1G0S8VT;R7G2A3G1A3A2A2A2A2F_;F_;Fc';Fj;Fc;Fi;Fl;").
Proof.
  intros l i c j c' Hi Hj. destruct (swap_remove_spec l i c Hi) as (l0 & lst & -> & Hle & E). rewrite E in Hj. clear E.
  rewrite length_app. cbn [length]. replace (length l0 + 1 - 1)%nat with (length l0) by lia.
  assert (LT : (j < length l0)%nat).
  { pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as L. destruct (Nat.eqb i (length l0)); [|rewrite length_list_upd in L]; exact L. }
  split; [exact LT|].
  destruct (Nat.eqb_spec i (length l0)) as [Ei|Ni].
  - left. split; [lia|]. rewrite nth_error_app1 by lia. exact Hj.
  - destruct (Nat.eq_dec j i) as [->|Nji].
    + right. split; [reflexivity|]. split; [lia|]. rewrite nth_error_list_upd_same in Hj by lia. injection Hj as <-.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + left. split; [exact Nji|]. rewrite nth_error_list_upd_other in Hj by (intros X; apply Nji; symmetry; exact X).
      rewrite nth_error_app1 by lia. exact Hj.
Qed.

Lemma swap_remove_In {T} : ltac2:(tb__ "0|1|
S13VT;A1S15VT;S15VT;S1S1bVT;A1M0S8VT;R5R4A3S17VT;R3A2A3S1G0S8VT;R6R3A3S17VT;R2A2A3S3S1S15R4R6A3A1S7VT;R4S3aVT;R8R7A3A3F_;F_;F_;Fc';Fj;Fc;Fi;Fl;").
Proof.
  intros l i c j c' Hi Hj Nji. destruct (swap_remove_spec l i c Hi) as (l0 & lst & -> & Hle & E). rewrite E. clear E.
  pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Lj. rewrite length_app in Lj. cbn [length] in Lj.
  destruct (Nat.eqb_spec i (length l0)) as [Ei|Ni].
  - rewrite nth_error_app1 in Hj by lia. exact (nth_error_In _ _ Hj).
  - destruct (Nat.eq_dec j (length l0)) as [Ej|Nj].
    + subst j. rewrite nth_error_app2 in Hj by lia. rewrite Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      apply (nth_error_In _ i). apply nth_error_list_upd_same. lia.
    + rewrite nth_error_app1 in Hj by lia. apply (nth_error_In _ j). rewrite nth_error_list_upd_other by (intros X; apply Nji; symmetry; exact X). exact Hj.
Qed.

Lemma swap_remove_incl {T} : ltac2:(tb__ "0|1|
S13VT;A1S15VT;VT;S1S1bVT;A1M0S8VT;R4R3A3S17VT;R2A2A3S7VT;R2S3aVT;R5R4A3A3S5S15S15S2S3S1S15R1R6A3A1S1G0S8VT;R7R1A3S17VT;R4A2A3A2Lj;A2F_;F_;Fc';Fc;Fi;Fl;").
Proof.
  intros l i c c' Hi Hin. destruct (In_nth_error _ _ Hin) as [j Hj].
  destruct (swap_remove_nth l i c j c' Hi Hj) as (LT & [[N E]|(-> & LT2 & E)]); [exists j; split; [exact N | exact E]|].
  exists (length l - 1)%nat. split; [lia | exact E].
Qed.

Lemma uR : ltac2:(tb__ "0|2|
ScQ40M0A1S2SeZ0SbG0R1A2M1A2SfG1S11Z2Z40A2A2A2Fw;").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u64 : ltac2:(tb__ "0|1|
S0S2SeZ0R1A2SfR1S11Z2Z40A2A2A2S1S0SbQ40M0SdG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma entry_at_base : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2M2A1G1G1G2S37R4A1S7G2S1cG1G1R4R3A4R5A3S7G2R3R6A3S1S0SbG0S16G1G1R4A3A2SbG0R6A2M3A3SfZ0M4G3A2S4S1G2R6S1cG1G1R8R7A4A3S1S0SbG0S1aG1G1R6A3A2G4A3A2F_;F_;F_;F_;F_;Fe;Fn;Fa;Fl;").
Proof.
  intros l a n e RA H1 H2 E Hn. destruct (In_nth_error _ _ H1) as [i Hi]. destruct (In_nth_error _ _ H2) as [j Hj].
  destruct (Nat.eq_dec i j) as [->|N]; [left; congruence|]. right.
  pose proof (maps_disjoint_in l i j _ _ RA N Hi Hj) as AP. unfold apartW in AP. cbn [fst snd] in AP. rewrite E in AP.
  pose proof (uR (snd e)). lia.
Qed.

Lemma remove_keeps : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2M2A1G1G1G2S0S37R5A1S7G2S1cG1G1R5R4A4R6A3SfZ0SbG0R5A2A2S7G2R5R8A3S2SeSbG0S16G1G1R6A3A2M3R5A2SfR5S10G3SbG0S1aG1G1R6A3A2A2A2A2S3S2SeSbG0R9A2M4R6A2SfR6S10G4SbG0R8A2A2A2A2A1S7G2R8S30RbRaA2A3F_;F_;F_;F_;F_;F_;Fx;Fe;Fn;Fa;Fl;").
Proof.
  intros l a n e x RA H1 Hn H2 Hx NX. unfold map_remove. apply filter_In. split; [exact H2|].
  unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned (fst e)) (bv_unsigned a)) as [E|E]; [|reflexivity]. exfalso.
  destruct (entry_at_base l a n e RA H1 H2 E Hn) as [->|Z0]; cbn [fst snd] in *; lia.
Qed.
Lemma remove_keeps_base : ltac2:(tb__ "0|3|
S13S12ScQ40M0A1M1G1A2M2A1G1G2S7G2R1R3A3S3S1S0SbG0S16G1G1R2A3A2SbG0R3A2A3A1S7G2R3S30R5R4A2A3F_;F_;Fe;Fa;Fl;").
Proof.
  intros l a e H N. unfold map_remove. apply filter_In. split; [exact H|]. unfold bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned (fst e)) (bv_unsigned a)) as [E|E]; [exfalso; exact (N E) | reflexivity].
Qed.
Lemma remove_incl : ltac2:(tb__ "0|2|
S13S12ScQ40A1M0G0A2M1A1G0G1S7G1R1S30R3R2A2A3S7G1R2R4A3F_;Fe;Fa;Fl;").
Proof. intros l a e H. unfold map_remove in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma iv_subtract_in : ltac2:(tb__ "0|5|
ScQ40M0A1M1G1S0S0S12G1G1A2M2S0SfR3S11Z2Z40A2A2S7G2R3S33R7R6R5R4A4A3S2SeSbG0S16G1G1R4A3A2M3R3A2SfR3S10G3SbG0S1aG1G1R4A3A2A2A2A2S2S2SeSbG0R9A2M4R4A2SfR4S10G4SbG0R8A2A2A2A2S3S2SeR7R4A2SfR4R6A2A2A1A2F_;F_;F_;Fx;Fe;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi e x Hhi Hin Hx. pose proof (uR a) as Ra. pose proof (uR sz) as Rs. unfold iv_subtract in Hin. cbv zeta in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [L|L]; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd] in Hx.
    rewrite u64 in Hx by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [L|L]; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd] in Hx.
    rewrite !u64 in Hx by lia. lia.
Qed.
Lemma maps_subtract_in : ltac2:(tb__ "0|5|
S13S12ScQ40M0A1M1G1A2M2A1S0S0G2S0SfR3S11Z2Z40A2A2S7G2R3S31R6R5R4A3A3S2SeSbG0S16G1G1R4A3A2M3R3A2SfR3S10G3SbG0S1aG1G1R4A3A2A2A2A2S2S5G2G2S2S7G2R1R9A3S2SeSbG0S16G1G1R1A3A2M4R5A2SfR5S10G4SbG0S1aG1G1R1A3A2A2A2A2A2Le0;A2S3S2SeR7R4A2SfR4R6A2A2A1A2F_;F_;F_;Fx;Fe;Fhi;Flo;Fl;").
Proof.
  intros l lo hi e x Hhi. induction l as [|[a sz] l IH]; intros Hin Hx; [destruct Hin|]. cbn [maps_subtract] in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (iv_subtract_in a sz lo hi e x Hhi Hin Hx) as [X Y]. split; [|exact Y]. exists (a, sz). split; [left; reflexivity | exact X].
  - destruct (IH Hin Hx) as [(e0 & H0 & X) Y]. split; [|exact Y]. exists e0. split; [right; exact H0 | exact X].
Qed.
Lemma covered_spec : ltac2:(tb__ "0|4|
S13S12ScQ40M0A1M1G1A2M2A1S0S6S1S19S4bR2R1A2S20A3S5G2G2S2S7G2R1R3A3S2SeSbG0S16G1G1R1A3A2M3R2A2SfR2S10G3SbG0S1aG1G1R1A3A2A2A2A2A2Le;A2A2Fx;FC;").
Proof.
  intros C x. unfold covered. rewrite existsb_exists. split; intros (e & He & Hx); exists e; (split; [exact He|]);
    unfold in_iv, in_rng, ivB, ivS in *; [apply andb_prop in Hx as [X Y]; apply Z.leb_le in X; apply Z.ltb_lt in Y; lia | apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
Qed.
Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S13S12ScQ40A1M0G0A2A1S0S0S0SfR2S11Z2Z40A2A2S1S19S4bR5R2A2S1dA3S1S19S4bS31R6R5R4A3R3A2S1dA3F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hhi H. destruct (covered (maps_subtract l lo hi) x) eqn:E; [|reflexivity]. exfalso.
  apply covered_spec in E as (e & He & Hx). destruct (maps_subtract_in l lo hi e x Hhi He Hx) as [(e0 & H0 & X) _].
  assert (C : covered l x = true) by (apply covered_spec; exists e0; split; assumption). rewrite H in C. discriminate C.
Qed.

Lemma maps_subtract_keep : ltac2:(tb__ "0|4|
S13S12ScQ40M0A1M1G1A2M2A1S0S0G1G1S7G2S1cG1G1R2R1A4R5A3SfZ0SbG0R2A2A2S4SeS10SbG0R4A2M3SbG0R3A2A2R6A2SeR5G3A2A2S7G2S1cG1G1R5R4A4S31R8R7R6A3A3F_;F_;F_;Fs;Fb;Fhi;Flo;Fl;").
Proof.
  intros l lo hi b s Hin Hs AP. induction l as [|[a sz] l IH]; [destruct Hin|]. cbn [maps_subtract]. apply in_or_app.
  destruct Hin as [E|Hin]; [left | right; exact (IH Hin)]. injection E as -> ->. unfold iv_subtract. cbv zeta. apply in_or_app.
  destruct AP as [AP|AP].
  - left. destruct (Z.ltb_spec (bv_unsigned b) lo) as [L|L]; [|exfalso; lia]. left.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - right. destruct (Z.ltb_spec hi (bv_unsigned b + bv_unsigned s)) as [L|L]; [|exfalso; lia]. left.
    rewrite Z.max_l by lia. replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_piece : ltac2:(tb__ "0|2|
S13S12ScQ40A1M0G0A2M1A1S0S0G1G1S7G1R2R5A3S7G1R2S33S16G0G0R3A3S1aG0G0R3A3R5R4A4A3S7G1R3S31R7R6R5A3A3F_;F_;Fr';Fr;Fhi;Flo;Fl;").
Proof.
  intros l lo hi r r' Hin Hp. induction l as [|[a sz] l IH]; [destruct Hin|]. cbn [maps_subtract]. apply in_or_app.
  destruct Hin as [<-|Hin]; [left; exact Hp | right; exact (IH Hin)].
Qed.
Lemma page_in_subtract : ltac2:(tb__ "0|3|
S13S12ScQ40M0A1M1G1A2A1S0S0G1SfR2S11Z2Z40A2A2S1S19S34R2R5A2S20A3S4SeS10SbG0R3A2M2S35A2R5A2SeR4G2A2A2S1S19S34R4S31R7R6R5A3A2S20A3F_;F_;F_;Fp;Fhi;Flo;Fl;").
Proof.
  intros l lo hi p Hhi Hp AP. unfold page_in_ranges in Hp |- *. apply existsb_exists in Hp as (r & Hr & Hb). cbv zeta in Hb.
  apply andb_prop in Hb as [X Y]. apply Z.leb_le in X, Y. pose proof (uR (fst r)) as Ra. pose proof (uR (snd r)) as Rs. pose proof (uR p) as Rp.
  pose proof page_size_pos as PSP. apply existsb_exists.
  destruct AP as [AP|AP].
  - exists (fst r, Z_to_bv 64 (Z.min (bv_unsigned (snd r)) (lo - bv_unsigned (fst r)))). split.
    + apply (maps_subtract_piece l lo hi r _ Hr). unfold iv_subtract. cbv zeta. apply in_or_app. left.
      destruct (Z.ltb_spec (bv_unsigned (fst r)) lo) as [L|L]; [left; reflexivity | exfalso; lia].
    + cbv zeta. cbn [fst snd]. rewrite u64 by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia.
  - exists (Z_to_bv 64 (Z.max (bv_unsigned (fst r)) hi), Z_to_bv 64 (bv_unsigned (fst r) + bv_unsigned (snd r) - Z.max (bv_unsigned (fst r)) hi)). split.
    + apply (maps_subtract_piece l lo hi r _ Hr). unfold iv_subtract. cbv zeta. apply in_or_app. right.
      destruct (Z.ltb_spec hi (bv_unsigned (fst r) + bv_unsigned (snd r))) as [L|L]; [left; reflexivity | exfalso; lia].
    + cbv zeta. cbn [fst snd]. rewrite !u64 by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.

Lemma hwN_remove_le : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2G0SeS38S14G1R3S30R2R1A2A3A1S38S14G1R3R2A3A1A2Fa;Fl2;Fl1;").
Proof.
  intros l1 l2 a. rewrite !hwN_app. apply Z.add_le_mono_l. unfold map_remove. induction l2 as [|e l2 IH]; [cbn; lia|].
  cbn [List.filter]. pose proof (hwN_nonneg l2). destruct (negb (bv_eqb (fst e) a)); rewrite ?hwN_cons; destruct (Placement.live_at GAPF e); lia.
Qed.
Lemma hwS_remove_le : ltac2:(tb__ "0|3|
S13S12ScQ40A1M0G0A2M1A1M2G2G0SeS39S14G1R3S30R2R1A2A3A1S39S14G1R3R2A3A1A2Fa;Fl2;Fl1;").
Proof.
  intros l1 l2 a. rewrite !hwS_app. apply Z.add_le_mono_l. unfold map_remove. induction l2 as [|e l2 IH]; [cbn; lia|].
  cbn [List.filter]. pose proof (hwS_nonneg l2). pose proof (uR (snd e)). destruct (negb (bv_eqb (fst e) a)); rewrite ?hwS_cons; destruct (Placement.live_at GAPF e); lia.
Qed.
Lemma ranges_apart_filter : ltac2:(tb__ "0|2|
S12ScQ40A1M0G0A2M1S19F_;S13G1A1S37R1A1S37S9G1R3R2A3A1F_;Fl;Ff;").
Proof.
  intros f l. induction l as [|e l IH]; intros H; [exact I|]. cbn [ranges_apart] in H. destruct H as [F R]. cbn [List.filter].
  destruct (f e); [|exact (IH R)]. cbn [ranges_apart]. split; [|exact (IH R)].
  apply Forall_forall. intros e' He'. apply filter_In in He' as [He' _]. exact (proj1 (Forall_forall _ _) F e' He').
Qed.

Definition L8text (V : VmMaps) : Prop := ltac2:(tb__ "0|2|
S2ScQ40M0A1M1G1S7S12G1G1A2S1cG1G1R2R1A4S32VV;A1A3SfZ0SbG0R2A2A2F_;Fs;Fb;S2S47VV;S42S45A3S47VV;S3eS3fA3A2A2").

Section ModelUnmap.
Variables (A : AA) (tp : list word) (md : Model) (i : nat) (ch : sec_chunk) (t g : list qbatch).
Hypothesis HM : ltac2:(tb__ "0|0|
S48S52VA;Vtp;Vmd;A4").
Hypothesis HI3 : inv3 A.
Hypothesis Hi : ltac2:(tb__ "0|0|
S1S1bS23A1S8S23S27VA;A1Vi;A3S17S23Vch;A2A3").
Hypothesis HCH : ltac2:(tb__ "0|1|
S15S23S1S1bS23A1S8S23S27VA;A1R2A3S17S23R1A2A3S2SfZ0S26R2A1M0A2S46S2cS2aVA;A1A1S24R2A1G0A3A2F_;Fc;Fj;").
Local Abbreviation lo := (sc_map_beg ch).
Local Abbreviation n := (sc_map_size ch).
Local Abbreviation aw := (Z_to_bv 64 (sc_map_beg ch)).
Local Abbreviation nw := (Z_to_bv 64 (sc_map_size ch)).
Local Abbreviation md' := (munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch))).
Local Abbreviation tp' := (tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp).
Local Abbreviation A' := (unmap_sec (set_q A t g) i).
Hypothesis HPAID : ltac2:(tb__ "0|3|
SeS51S36Vmd;SdQ40M0S24Vch;A1M1A2SdG0S26Vch;A1M2A2A3S50G1S10G1G2A2Vtp;A3A2S51Vmd;Vtp;A2A2").

Lemma MU_nums : ltac2:(tb__ "0|4|
S2SeZ1000S24Vch;A1M0A2S2SfZ0S26Vch;A1M1A2S2SeS10G0G1A2M2Z7fffff800000A2S2S4SeG2S41A2SeS40G0A2A2S2S4SeG2S44A2SeS43G0A2A2S2S1S0SbQ40M3SdG3G0A2A2G0A3S1S0SbG3SdG3G1A2A2G1A3A2A2A2A2A2A2").
Proof.
  destruct (HCH i ch Hi) as (P & D1 & D2 & D3 & D4 & D5). pose proof (topG_range (aa_geom A)) as TG.
  split; [exact D1|]. split; [exact P|]. split; [lia|]. split; [exact D4|]. split; [exact D5|]. split; apply u64; lia.
Qed.
Lemma MU_entry : ltac2:(tb__ "0|2|
S7S12ScQ40M0A1M1G1A2S1cG1G1SdG0S24Vch;A1A2SdG0S26Vch;A1A2A4S32S2fVmd;A1A1A3").
Proof. destruct HM as (VG & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & N8 & _). exact (N8 ch (nth_error_In _ _ Hi)). Qed.
Lemma MU_apart : ltac2:(tb__ "0|0|
S37S32S2fVmd;A1A1A1").
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & LI). destruct LI as (_ & _ & L3 & _). unfold maps_disjoint in L3.
  apply ranges_apart_app in L3 as (_ & R & _). exact R.
Qed.
Lemma MU_keep : ltac2:(tb__ "0|6|
S12ScQ40M0A1M1G1A2M2S0S7G2R2S32S2fVmd;A1A1A3S2SeSbG0S16G1G1R3A3A2M3R2A2SfR2S10G3SbG0S1aG1G1R3A3A2A2A2A2S3S2SeS24Vch;A1M4R3A2SfR3S10G4S26Vch;A1M5A2A2A2A1S7G2R5S32S2fS36Vmd;SdG0G4A2SdG0G5A2A3A1A1A3F_;F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx NX. pose proof MU_nums as (_ & Pn & _ & _ & _ & Ua & Un).
  change (vm_maps (m_vmmaps md')) with (map_remove (vm_maps (m_vmmaps md)) aw).
  apply (remove_keeps _ aw nw e x MU_apart MU_entry ltac:(rewrite Un; exact Pn) He Hx). rewrite Ua, Un. exact NX.
Qed.
Lemma MU_in_maps : ltac2:(tb__ "0|3|
S0S0SfR2R1A2S4SeR2S24Vch;A1M0A2SeS10G0S26Vch;A1M1A2R3A2A2S47S2fVmd;A1R4R3A3S47S2fS36Vmd;SdQ40M2G0A2SdG2G1A2A3A1R5R4A3F_;F_;F_;FY;FX;").
Proof.
  intros X Y HXY AP (e & He & Hc). exists e. split; [|exact Hc]. apply (MU_keep e X He); lia.
Qed.

Lemma MU_other : ltac2:(tb__ "0|0|
S15S23S1S1bS23A1S8S23S27VA;A1R2A3S17S23R1A2A3S3S1S15R3Vi;A3A1S3S1S0S24R3A1S24Vch;A1A3A1F_;F_;Fc;Fj;").
Proof.
  intros j c Hj Nji E. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & _ & _ & _ & X5 & _).
  specialize (X5 j c Hj ltac:(intros X; apply Nji; symmetry; exact X)). destruct (HCH j c Hj) as (P & _). destruct (HCH i ch Hi) as (P' & _). lia.
Qed.

Lemma L8_unmap : ltac2:(tb__ "0|1|
S53S2fVmd;A1A1S53S2fS36Vmd;SdQ40M0S24Vch;A1A2SdG0S26Vch;A1A2A3A1A1F_;").
Proof.
  intros (P1 & P2 & P3). pose proof MU_nums as (_ & _ & _ & _ & DB & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB.
  split; [|split].
  - intros b s Hin. change (vm_maps (m_vmmaps md')) with (map_remove (vm_maps (m_vmmaps md)) aw) in Hin. exact (P1 b s (remove_incl _ _ _ Hin)).
  - apply MU_in_maps; [unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG; lia | unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG; lia | exact P2].
  - apply MU_in_maps; [unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END; lia | unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END; lia | exact P3].
Qed.

Theorem model_unmap : ltac2:(tb__ "0|3|
S48S52S3bS4cVA;Vt;Vg;A3Vi;A2S50S24Vch;A1M0S10G0S26Vch;A1M1A2Vtp;A3S36Vmd;SdQ40M2G0A2SdG2G1A2A3A4").
Proof.
  pose proof MU_nums as (Lo & Pn & Top & DI & DB & Ua & Un).
  pose proof HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & LI).
  pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & _). destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
  assert (HI64 : lo + n < 2 ^ 64) by lia.
  assert (ENA : vm_noaccess (m_vmmaps md') = maps_subtract (vm_noaccess (m_vmmaps md)) lo (lo + n)).
  { change (vm_noaccess (m_vmmaps md')) with (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw)). rewrite Ua, Un. reflexivity. }
  assert (ELZ : m_vm_lazy md' = maps_subtract (m_vm_lazy md) lo (lo + n)).
  { change (m_vm_lazy md') with (maps_subtract (m_vm_lazy md) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw)). rewrite Ua, Un. reflexivity. }
  assert (EMP : vm_maps (m_vmmaps md') = map_remove (vm_maps (m_vmmaps md)) aw) by reflexivity.
  assert (ETOP : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by reflexivity.
  unfold model_inv.
  split.
  {
    destruct VG as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). unfold vm_geom. cbv zeta.
    change (aa_geom A') with (aa_geom A). change (aa_sec A') with (swap_remove (aa_sec A) i).
    split.
    { intros e x He Hx. rewrite ENA in He. destruct (maps_subtract_in _ lo (lo + n) e x HI64 He Hx) as [(e0 & H0 & Hx0) NX].
      destruct (N1 e0 x H0 Hx0) as (e' & He' & Hx'). exists e'. split; [exact (MU_keep e' x He' Hx' NX) | exact Hx']. }
    split; [apply MU_in_maps; [rewrite kSpaceSize_val; lia | lia | exact N2]|].
    split; [apply MU_in_maps; [lia | lia | exact N3]|].
    split; [apply MU_in_maps; [lia | lia | exact N4]|].
    split; [apply MU_in_maps; [lia | lia | exact N5]|].
    split; [apply MU_in_maps; [rewrite FS_total_val; lia | lia | exact N6]|].
    split; [apply MU_in_maps; [unfold kPtrArrayReserve; lia | lia | exact N7]|].
    split.
    { intros c Hc. destruct (swap_remove_incl _ i ch c Hi Hc) as (j & Nj & Hj). rewrite EMP. apply remove_keeps_base; [exact (N8 c (nth_error_In _ _ Hj))|].
      cbn [fst]. destruct (HCH j c Hj) as (Pc & D1 & D2 & D3 & _). pose proof (topG_range (aa_geom A)) as TG.
      rewrite Ua, u64 by lia. exact (MU_other j c Hj Nj). }
    intros p Hal Hband. destruct (N9 p Hal Hband) as [Z1 Z2]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB.
    split.
    - rewrite ELZ. apply page_in_subtract; [exact HI64 | exact Z1|]. unfold page_size. unfold PG, LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in Hband. lia.
    - intros j Hj. rewrite ENA. apply covered_subtract_false; [exact HI64 | exact (Z2 j Hj)]. }
  split.
  { rewrite (PrimCredit.prim_credit_same A A' eq_refl). change (budget_boundD A') with (budget_boundD A). lia. }
  split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite ETOP; exact V7|].

  destruct LI as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10). unfold ledger_inv. cbv zeta.
  split; [exact L1|].
  split.
  { intros x Hx. destruct (L2 x Hx) as (b & s & Hbs & Hxb). exists b, s. split; [|exact Hxb]. apply (MU_keep (b, s) x Hbs Hxb).
    unfold Placement.SHADOW_BAND_LO, Placement.SHADOW_BAND_HI in Hx. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB. lia. }
  split.
  { unfold maps_disjoint in L3 |- *. apply ranges_apart_app in L3 as (R1 & R2 & R3). apply (proj2 (ranges_apart_app _ _)).
    split; [exact R1|]. split; [rewrite EMP; unfold map_remove; apply ranges_apart_filter; exact R2|].
    intros e1 e2 H1 H2. rewrite EMP in H2. exact (R3 e1 e2 H1 (remove_incl _ _ _ H2)). }
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. change (aa_V A') with (aa_V A). change (aa_depot A') with (aa_depot A).
    rewrite EMP. change (vm_reserved (m_vmmaps md')) with (vm_reserved (m_vmmaps md)). destruct L4 as [N4' S4'].
    pose proof (hwN_remove_le (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md)) aw) as HN.
    pose proof (hwS_remove_le (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md)) aw) as HS.
    split; [unfold GN in *; lia | lia]. }
  split.
  { change (aa_depot A') with (aa_depot A). destruct L5 as [DV1 DV2 DV3 DV4 DV5 DV6].
    assert (BLK : forall bn, In bn (dblocks (aa_depot A)) -> dyn_in (topG (aa_geom A)) (fst bn) (snd bn) /\ (fst bn + snd bn <= lo \/ lo + n <= fst bn)).
    { intros bn Hbn. destruct (DEP3 bn Hbn) as (D1 & _ & _ & _ & _ & _ & _ & D8). split; [exact D1|].
      pose proof (D8 ch (nth_error_In _ _ Hi)) as S. unfold sepZ in S. cbn [fst snd] in S. lia. }
    pose proof (topG_range (aa_geom A)) as TG.
    constructor.
    - intros bn Hbn. rewrite EMP. apply remove_keeps_base; [exact (DV1 bn Hbn)|]. destruct (BLK bn Hbn) as ((B1 & B2 & B3 & _) & AP).
      unfold wentry. cbn [fst]. rewrite Ua, u64 by lia. lia.
    - intros b Hb. rewrite ELZ.
      assert (Hbn : In (b, FBSZ) (dblocks (aa_depot A))) by (unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb]).
      destruct (BLK _ Hbn) as ((B1 & B2 & B3 & _) & AP). cbn [fst snd] in B1, B2, B3, AP.
      apply maps_subtract_keep; [exact (DV2 b Hb) | rewrite u64 by (unfold FBSZ; lia); unfold FBSZ; lia | rewrite !u64 by (unfold FBSZ in *; lia); lia].
    - intros b j Hb Hj. rewrite ENA. apply covered_subtract_false; [exact HI64 | exact (DV3 b j Hb Hj)].
    - intros b k Hb Hk. rewrite <- (DV4 b k Hb Hk). unfold tp_forget. rewrite filter_In.
      assert (Hbn : In (nth b (dFB (aa_depot A)) 0, FBSZ) (dblocks (aa_depot A))).
      { unfold dblocks. apply in_or_app. right. apply in_map_iff. exists (nth b (dFB (aa_depot A)) 0). split; [reflexivity | apply nth_In; exact Hb]. }
      destruct (BLK _ Hbn) as ((B1 & B2 & B3 & _) & AP). cbn [fst snd] in B1, B2, B3, AP.
      assert (OUT : page_outside_range lo (lo + n) (Z_to_bv 64 (fpage (aa_depot A) b k)) = true).
      { unfold page_outside_range, fpage. unfold FBSZ, FBPAGES, PG in *. assert (RG : 0 <= nth b (dFB (aa_depot A)) 0 + 4096 * k < 2 ^ 64) by (clear -B1 B3 TG Hk; lia). rewrite (u64 _ RG). apply negb_true_iff. apply andb_false_iff.
        destruct AP as [AP|AP]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
      split; [intros [H _]; exact H | intros H; exact (conj H OUT)].
    - intros bn Hbn. rewrite ETOP. exact (DV5 bn Hbn).
    - rewrite ETOP. exact DV6. }
  split; [exact L6|]. split; [exact L7|]. split; [first [exact L8 | exact (L8_unmap L8)]|].
  split.
  { change (aa_sec A') with (swap_remove (aa_sec A) i). change (aa_Km A') with (aa_Km A). rewrite (swap_remove_length _ i ch Hi). lia. }
  rewrite ENA. exact (ivs_pos_subtract _ lo (lo + n) L10).
Qed.
End ModelUnmap.

Section PureUnmap.
Variables (A : AA) (g1 g2 : list qbatch) (a : Z) (it : Z * Z) (i2 : list (Z * Z)) (s s' : Z) (i : nat) (ch : sec_chunk).
Hypothesis Hth : aa_q_thread A = [].
Hypothesis Hgl : ltac2:(tb__ "0|0|
S1S13S22A1S2bVA;A1S14S22Vg1;S18S22S25Va;S18S12S0S0A2Vit;Vi2;A3Vs;A3Vg2;A3A3A3").
Hypothesis HPit : ltac2:(tb__ "0|0|
S1S19S3cS1aS0S0Vit;A3A1S1dA3").
Hypothesis Hi : ltac2:(tb__ "0|0|
S1S1bS23A1S8S23S27VA;A1Vi;A3S17S23Vch;A2A3").
Hypothesis Hu : ltac2:(tb__ "0|0|
S1S0S16S0S0Vit;A3S10S10S24Vch;A1S3dA2Z800A2A3").
Hypothesis HQP : q_pure A.
Hypothesis HI3 : inv3 A.
Local Abbreviation q' := (g1 ++ mkQB a i2 s' :: g2).
Local Abbreviation A' := (unmap_sec (set_q A [] (g1 ++ mkQB a i2 s' :: g2)) i).
Local Abbreviation secf := (fun bn : Z * Z => negb (is_primary (snd bn))).

Lemma PU_qall : ltac2:(tb__ "0|0|
S1S13S22A1S2eVA;A1S14S22Vg1;S18S22S25Va;S18S12S0S0A2Vit;Vi2;A3Vs;A3Vg2;A3A3A3").
Proof. unfold qall. rewrite Hth, Hgl. reflexivity. Qed.
Lemma PU_items : ltac2:(tb__ "0|1|
S1S13S12S0S0A2M0A1S2dS2eVA;A1A1S14G0S2dVg1;A1S18G0Vit;S14G0Vi2;S2dVg2;A1A3A3A3A3").
Proof. rewrite PU_qall. unfold qitems. rewrite flat_map_app. reflexivity. Qed.
Lemma PU_items' : ltac2:(tb__ "0|1|
S1S13S12S0S0A2M0A1S2dS14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3A1S14G0S2dVg1;A1S14G0Vi2;S2dVg2;A1A3A3A3").
Proof. unfold qitems. rewrite flat_map_app. reflexivity. Qed.
Lemma PU_rest_in : ltac2:(tb__ "0|1|
S12S0S0A2M0S7G0R1S2dS14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3A1A3S7G0R2S2dS2eVA;A1A1A3F_;Fit';").
Proof. intros it' H. rewrite PU_items' in H. rewrite PU_items. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. Qed.

Lemma PU_nodup : ltac2:(tb__ "0|4|
S2SaS0S14S0S4fS12S0S0A2M0S0S16S0S0A2M1S9G0G0S21S3cS1aS0S0R1A3A1A1Lbn;M2S28VA;A1A3A4S4fG0S0G1S9G0G2S2dS14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3A1A3A4A3M3A2S3S7S0S16S0S0Vit;A3G3A3A1A2").
Proof.
  destruct HI3 as (_ & _ & _ & _ & _ & ND & _). apply (proj1 (NoDup_ListNoDup _)) in ND.
  rewrite PU_items in ND. rewrite PU_items'.
  rewrite (List.filter_app secf (qitems g1)) in ND. rewrite (List.filter_app secf (qitems g1)).
  cbn [List.filter] in ND. rewrite HPit in ND. cbn [negb] in ND.
  rewrite map_app in ND. rewrite map_app. cbn [map] in ND.
  set (L := List.map fst (List.filter secf (aa_live A))) in *. set (F1 := List.map fst (List.filter secf (qitems g1))) in *.
  set (F2 := List.map fst (List.filter secf (i2 ++ qitems g2))) in *.
  rewrite app_assoc in ND. rewrite app_assoc. exact (NoDup_remove _ _ _ ND).
Qed.

Lemma PU_live_other : ltac2:(tb__ "0|0|
S0S0S7S12S0S0A2S1cS0S0R2R1A4S28VA;A1A3S1S19S3cR2A1S1dA3S3S1S0R4S16S0S0Vit;A3A3A1F_;F_;Fn;Fb;").
Proof.
  intros b n Hin HP E. destruct PU_nodup as [_ NI]. apply NI. apply in_or_app. left. apply in_map_iff. exists (b, n). split; [exact E|].
  apply filter_In. split; [exact Hin|]. cbn. rewrite HP. reflexivity.
Qed.
Lemma PU_item_other : ltac2:(tb__ "0|1|
S12S0S0A2M0S7G0R1S2dS14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3A1A3S1S19S3cS1aS0S0R2A3A1S1dA3S3S1S0S16S0S0R3A3S16S0S0Vit;A3A3A1F_;F_;Fit';").
Proof.
  intros it' Hin HP E. destruct PU_nodup as [_ NI]. apply NI. apply in_or_app. right. apply in_map_iff. exists it'. split; [exact E|].
  apply filter_In. split; [exact Hin|]. rewrite HP. reflexivity.
Qed.

Lemma PU_chunk_stays : ltac2:(tb__ "0|0|
S23S0S7S23R2S27VA;A1A3S1S0R2S10S10S24R3A1S3dA2Z800A2A3S3S1S0R3S16S0S0Vit;A3A3A1S7S23R5S27S3bS4cVA;S1fS22A1S14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3A3Vi;A2A1A3F_;F_;F_;Fu;Fc;").
Proof.
  intros c u Hc Eu NE. change (aa_sec A') with (swap_remove (aa_sec A) i). destruct (In_nth_error _ _ Hc) as [j Hj].
  apply (swap_remove_In _ i ch j c Hi Hj). intros ->. rewrite Hi in Hj. injection Hj as <-. apply NE. rewrite Eu, Hu. reflexivity.
Qed.

Lemma PU_item_pure : ltac2:(tb__ "0|2|
S12S0S0A2M0S7G0R1S2dS14S22Vg1;S18S22S25Va;Vi2;Vs';A3Vg2;A3A3M1A1A3S4dVA;R2A2S4dS3bS4cVA;S1fS22A1G1A3Vi;A2R3A2F_;F_;Fit';").
Proof.
  intros it' Hin (I1 & I2 & I3 & I4). unfold item_pure. cbv zeta. split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  intros HP. destruct (I4 HP) as (c & Hc & Eu & Es). exists c. split; [|exact (conj Eu Es)].
  exact (PU_chunk_stays c (fst it') Hc Eu (PU_item_other it' Hin HP)).
Qed.

Lemma QP_unmap : q_pure A'.
Proof.
  destruct HQP as [QF QN]. unfold q_pure. change (qall A') with ([] ++ q'). cbn [app]. rewrite PU_qall in QF, QN. split.
  - apply Forall_forall. intros b Hb.
    assert (OLD : exists b0, In b0 (g1 ++ mkQB a (it :: i2) s :: g2) /\ qb_addr b0 = qb_addr b /\ (length (qb_items b) <= length (qb_items b0))%nat
                             /\ (forall it', In it' (qb_items b) -> In it' (qb_items b0))).
    { apply in_app_or in Hb as [Hb|[<-|Hb]].
      - exists b. split; [apply in_or_app; left; exact Hb|]. split; [reflexivity|]. split; [lia | intros it' H; exact H].
      - exists (mkQB a (it :: i2) s). split; [apply in_or_app; right; left; reflexivity|]. split; [reflexivity|]. cbn [qb_items length]. split; [lia | intros it' H; right; exact H].
      - exists b. split; [apply in_or_app; right; right; exact Hb|]. split; [reflexivity|]. split; [lia | intros it' H; exact H]. }
    destruct OLD as (b0 & Hb0 & EA & LE & SUB). pose proof (proj1 (Forall_forall _ _) QF b0 Hb0) as (B1 & B2 & B3 & B4).
    unfold batch_pure. rewrite <- EA. split; [exact B1|]. split; [lia|]. split; [exact B3|].
    apply Forall_forall. intros it' Hit'. apply PU_item_pure.
    + unfold qitems. apply in_flat_map. exists b. split; [exact Hb | exact Hit'].
    + exact (proj1 (Forall_forall _ _) B4 it' (SUB it' Hit')).
  - replace (map qb_addr q') with (map qb_addr (g1 ++ mkQB a (it :: i2) s :: g2)) by (rewrite !map_app; reflexivity). exact QN.
Qed.

Lemma PU_large : is_large it = true.
Proof.
  destruct HQP as [QF _]. assert (Hit : In it (qitems (qall A))) by (rewrite PU_items; apply in_or_app; right; left; reflexivity).
  unfold qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit). pose proof (proj1 (Forall_forall _ _) QF b Hb) as (_ & _ & _ & B4).
  pose proof (proj1 (Forall_forall _ _) B4 it Hit) as (_ & I2 & _). unfold is_large. apply Z.leb_le.
  destruct (Z_le_dec 64513 (snd it)) as [L|L]; [exact L|]. rewrite (primary_small (snd it)) in HPit by lia. discriminate HPit.
Qed.

Lemma I3_unmap : inv3 A'.
Proof.
  pose proof HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbv zeta.
  change (aa_geom A') with (aa_geom A). change (aa_live A') with (aa_live A). change (aa_sec A') with (swap_remove (aa_sec A) i).
  change (aa_cls A') with (aa_cls A). change (aa_depot A') with (aa_depot A). change (aa_cache_inited A') with (aa_cache_inited A).
  split; [exact I1|].
  split.
  { intros b n Hin. destruct (I2 b n Hin) as [P|(c & Hc & Eb & Es)]; [left; exact P|].
    destruct (is_primary n) eqn:EP; [left; reflexivity | right]. exists c. split; [|exact (conj Eb Es)].
    exact (PU_chunk_stays c b Hc Eb (PU_live_other b n Hin EP)). }
  split.
  {
    intros j c Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (LTj & ORj).
    assert (OLDj : exists j0, nth_error (aa_sec A) j0 = Some c /\ j0 <> i /\ ((j <> i /\ j0 = j) \/ (j = i /\ j0 = (length (aa_sec A) - 1)%nat))).
    { destruct ORj as [[N E]|(E1 & LT & E)]; [exists j; split; [exact E | split; [exact N | left; split; [exact N | reflexivity]]]|].
      exists (length (aa_sec A) - 1)%nat. split; [exact E | split; [lia | right; split; [exact E1 | reflexivity]]]. }
    destruct OLDj as (j0 & Hj0 & Nj0 & Cj). destruct (I3 j0 c Hj0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
    intros j2 c2 Hj2 Nj. destruct (swap_remove_nth _ i ch j2 c2 Hi Hj2) as (LTj2 & ORj2).
    destruct ORj2 as [[N2 E2]|(E21 & LT2 & E2)].
    - apply (X5 j2 c2 E2). destruct Cj as [[_ ->]|[_ ->]]; [exact Nj | lia].
    - apply (X5 _ c2 E2). destruct Cj as [[Nji ->]|[Eji _]]; [lia | exfalso; apply Nj; rewrite Eji, E21; reflexivity]. }
  split.
  { intros z Hz. apply I4. unfold q_foot in *. change (aa_q_thread A' ++ aa_q_global A') with ([] ++ q') in Hz. cbn [app] in Hz.
    fold (qall A). rewrite PU_qall. apply Exists_exists in Hz as (b & Hb & Hz). apply Exists_exists.
    apply in_app_or in Hb as [Hb|[<-|Hb]].
    - exists b. split; [apply in_or_app; left; exact Hb | exact Hz].
    - exists (mkQB a (it :: i2) s). split; [apply in_or_app; right; left; reflexivity|]. cbn [qb_addr qb_items] in Hz |- *.
      destruct Hz as [Hz|Hz]; [left; exact Hz | right]. apply Exists_cons_tl. exact Hz.
    - exists b. split; [apply in_or_app; right; right; exact Hb | exact Hz]. }
  split.
  { intros bn Hbn. destruct (I5 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
    intros c Hc. destruct (swap_remove_incl _ i ch c Hi Hc) as (j & _ & Hj). exact (D8 c (nth_error_In _ _ Hj)). }
  split.
  { change (qall A') with ([] ++ q'). cbn [app]. apply (proj2 (NoDup_ListNoDup _)). exact (proj1 PU_nodup). }
  split.
  { rewrite (swap_remove_length _ i ch Hi). rewrite (large_live_same A A' eq_refl).
    assert (EQL : qlarge A = qlarge A' + 1).
    { unfold qlarge. change (qall A') with ([] ++ q'). cbn [app]. rewrite PU_items, PU_items'. rewrite !List.filter_app. cbn [List.filter]. rewrite PU_large.
      rewrite ?List.filter_app, ?length_app. cbn [length]. rewrite ?List.filter_app, ?length_app. lia. }
    pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI. lia. }
  split; [rewrite (small_live_same A A' eq_refl); exact I8|].
  intros _. apply I9. fold (qall A). rewrite PU_qall. intros E. apply app_eq_nil in E as [_ E]. discriminate E.
Qed.
End PureUnmap.
End InvQ10a.

(* [comment removed for export] *)
Module SpineCallocS5t.


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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc ->
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
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc ->
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
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc ->
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
End SpineCallocS5t.

(* [comment removed for export] *)
Module SpineCallocE9.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "or"; "False"; "@Corelib.Init.Datatypes"; "bool"; "list"; "nil"; "cons"; "true"; "pair"; "prod"; "nat"; "Some"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "rw"; "ss_next"; "sv"; "SLit"; "SVar"; "ss_facts"; "SPUle"; "sobj"; "sprop_below"; "rm"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "JLc_ok"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "F_gen"; "MSENT"; "ube"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9"; "fin_hyps"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SfS50VCST;R1A2S50S5aR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S3cVAInv;VW;Vst;VA;VKc;S1cPcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S23S16S5S2bQ40A1A1S55VAInv;R4R3R2R1A4S51S53Vsegs;S21R4A1A2S52Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_arm.
Variable partial : bool.
Variable Frz : list sprop.
Variables (CC9 EE9m CC9m T9 CC10 F10 : axst).
Hypothesis HCC9m : ltac2:(tb__ "0|1|
S0S12VCC9m;S4fVW;Vst;Vtmax;VEE9m;S4dS7SaSbS1aA2M0S9SbS1aUaS4eA4S7G0S9SbS1aUcS1cPcA1A4S6G0A1A3A3S6S1fA1SeS6S17A1A9A3").
Hypothesis W9m : ltac2:(tb__ "0|0|
S0S4S22S11VCC9m;A1A1S8A3").
Hypothesis D9m : ltac2:(tb__ "0|4|
S0SdSaS5SaS1aS1aA2M0A1M1S5S17A1M2A2M3A1S57S11VEE9m;A1S11VCC9m;A1A2ScG3S9G1G2S6G0A1S6S17A1A4A2A3").
Hypothesis NX9m : ltac2:(tb__ "0|0|
S0S10S19S11VCC9m;A1A1S19S11VEE9m;A1A1A3").
Variables (sm sdm : wsub) (Rm : list sobj).
Hypothesis Hem : ltac2:(tb__ "0|1|
S0SdS5S1fA1M0A1S28VCC9m;S48Vsm;A3ScG0VRm;A2A3").
Hypothesis Hchkm : ltac2:(tb__ "0|0|
S0S4S27VCC9m;S48Vsm;VRm;S54S15S12S14S4aA4A5S8A3").
Hypothesis HTm : ltac2:(tb__ "0|0|
S0S12S29Vsm;S48S56S49A1VCC9m;VRm;A5VT9;A3").
Hypothesis FBCm : ltac2:(tb__ "0|1|
S0S4S43S17S20S19S11VCC9m;A1M0A1A1S1dG0A1A3S8A3").
Hypothesis FBTm : ltac2:(tb__ "0|0|
S0S4S43S17S20S19S11VT9;A1A1A1S1dS11VCC9m;A1A1A3S8A3").
Hypothesis ENT10 : ltac2:(tb__ "0|0|
S0S4S13S59VT9;S1dS11VCC9m;A1A1A2VCC10;Vsdm;A3S8A3").
Hypothesis SID10 : ltac2:(tb__ "0|0|
S0S4S58Vsdm;S2cA2S8A3").
Hypothesis NXCm : ltac2:(tb__ "0|0|
S45S2cS19S11VCC9m;A1A1A2").
Hypothesis NX9f : ltac2:(tb__ "0|0|
S45S2cS19S11S2fVFrz;VCC9;A2A1A1A2").
Hypothesis NX10 : ltac2:(tb__ "0|0|
S45S2cS19S11VCC10;A1A1A2").
Hypothesis ECert9 : ltac2:(tb__ "0|3|
S0S4S31S2dUfa0S7SfZdb004S6SfA1A3S2cS7S2eS30S2fVFrz;VCC9;A2Z1S1bZ0M0A1M1A3S6S2eA1M2A3S7S2eS30VEE9m;G0G1A3G2A3A6S8A3").
Hypothesis ECert10 : ltac2:(tb__ "0|3|
S0S4S31S2dUfa0S6SfA1S2cS7S2eS30VCC10;Z1S1bZ0M0A1M1A3S6S2eA1M2A3S7S2eS30VF10;G0G1A3G2A3A6S8A3").
Variables (swc scells hcells : list cell) (sf : wsub).
Hypothesis FH : ltac2:(tb__ "0|0|
S5bVnW;Vst;VF10;Vswc;Vscells;Vhcells;Vpartial;Vsf;A8").

Lemma es9c_arm : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fVFrz;VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cut 4000%nat [0xdb004] GW [mkVNA (ax_add_facts Frz CC9) 1 (SLit 0)] [mkVNA EE9m 0 (SLit 0)] (JGb W st A Kc rho) _ tpX _ _ HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NX9f.
  - exact ECert9.
  - intros E rhoY HinE. clear ECert9. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (ecall_gen nW st CC9m T9 CC10 sm Rm sdm Pre_mszA Posts_mszA P_msz
                eq_refl (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) Hem Hchkm HTm FBCm FBTm ENT10 SID10 NXCm eq_refl
                A Kc rho tpX rhoY _ HUS HKc).
        intros rhoZ tpZ.
        apply (ecfg_cut 4000%nat [] GW [mkVNA CC10 1 (SLit 0)] [mkVNA F10 0 (SLit 0)] (JGb W st A Kc rho) _ tpZ _ _ HST).
        - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NX10.
        - exact ECert10.
        - intros E' rhoV HinE'. clear ECert10. destruct HinE' as [<-|[]]. cbn [vna_state].
          eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
          eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
          intros w Hw. exact (calloc_finish'_P nW st CST XGL HCST HXGL HCSTM law_die F10 swc scells hcells partial sf FH A0 A Kc rho0 rho keep rhoV tp0 tpZ w Posts HPin HW HKc HDO HL HKEEP Hcnt HPRM Hpar Hw).
        - left. reflexivity. }
    rewrite HCC9m. unfold upd. lazy zeta. rewrite HCC9m in W9m, D9m, NX9m. unfold upd in W9m, D9m, NX9m.
    eapply SPA_restate; [exact W9m | exact D9m | exact NX9m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End E_arm.

Section E_spine_s9c.
Variable partial : bool.
Variable CC9 : axst.
Hypothesis NX9 : ltac2:(tb__ "0|0|
S45S2cS19S11VCC9;A1A1A2").
Hypothesis FGC : ltac2:(tb__ "0|0|
S44S17S4cS1dS11VCC9;A1A1A3").
Hypothesis ARMa : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fS7S17S1eS1bZ20A1S1cS4bA1A2S6S17A1A3VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Hypothesis ARMb : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5S2fS7S17S1eS1cS4bA1S1bZ10A1A2S6S17A1A3VCC9;A2R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").

Theorem espine_s9c_P : ltac2:(tb__ "0|5|
S23S23S38S16S16SfOF_;S5S2bQ40M0A1A1M1S5SaS12S25A2M2A1S42G2S9S12S25S37VW;Vst;A2S36VCST;VXGL;R8R6A4A4R1A3S35VW;Vst;A2S41VW;Vst;A2S39R9A1S3eRcRbA2S3fR8RaR9A3SfS2S3aVCST;RfR1A3S3bVCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S46Z1S40ReS2aG0S18RbPcM3A2A2A2A2S24RfA1S4OLpartial;Vpartial;S1S0SfS47S2aG0S18RdG3A2A2Z8A2Z0A3M4A1G4X4x2S16G1S32Vsegs;S34Vsegs;S3dVW;Vst;R13R12R10A5VCC9;R2R1A5S26Vsegs;S33R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;").
Proof.
  intros A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (etriple_pre_pure segs _ _ (rw rhoX V_RZ = Z_to_bv 64 (rz nv) /\ (16 <= rz nv <= 1024 /\ rz nv mod 16 = 0))).
  { intros w Hw. pose proof (JGb_pvals nW st A Kc rho rhoX tpX w CC9 Hw FGC Hcnt) as PV. cbn zeta in PV.
    destruct PV as (_ & _ & E150 & _ & _ & _ & _ & _ & Brz & _). split; [exact E150 | exact Brz]. }
  intros [E150 RZF].
  destruct (Z.eq_dec (rz nv) 16) as [E16|N16].
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMb A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SVar V_RZ) (SLit 16)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
  - eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | exact (ARMa A0 A Kc rho0 rho keep tp0 Posts HPin HW HUS HKc HDO HL HKEEP Hcnt HPRM Hpar rhoX tpX)].
    apply (SPA_add_facts (JGb W st A Kc rho) rhoX CC9 [SPUle (SLit 32) (SVar V_RZ)] tpX w); [| |exact Hw].
    + constructor; [|constructor]. cbn [holds eval]. rewrite E150, !u64_lit by lia. lia.
    + cbn. unfold V_RZ. rewrite !andb_true_r. apply (proj2 (Pos.ltb_lt _ _)). unfold GW in NX9. lia.
Qed.
End E_spine_s9c.
End E.
End SpineCallocE9.

