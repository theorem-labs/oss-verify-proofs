(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "div"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "length"; "prod"; "option"; "None"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "rl"; "rm"; "agree_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ.RJ"; "F0"; "U0"; "PCE"; "FAb"; "revealedp"; "gh_new"; "gh_nf"; "JR"; "committed"; "releasedp"; "shpage"; "subF"; "subU"; "frozen"; "gh_chx"; "ghosts"; "mlink"; "rlink"; "rmlink"; "zoneR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserMapSize"; "Sh"; "kFreeArrayMapSize"; "region_info"; "Size"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_allocated_user"; "cs_mapped_user"; "cs_mapped_free_array"; "cs_cache"; "aa_geom"; "ag_thread"; "budget_ok_alloc"; "cs_free_array"; "@Corelib.Lists.ListDef"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "alloc_top"; "m_vm_lazy"; "m_vmmaps"; "maps_subtract"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "ph_cnt"; "ph_f"; "ph_fill"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "GR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "rhoM_of"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record phase := mkPh { ph_u : nat; ph_f : nat; ph_fill : Z; ph_pop : Z; ph_cnt : bool; ph_ri : bool }.
Definition ph0 : phase := mkPh 0 0 0 0 false false.

Section RJ.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let SB : Z := ag_spacebeg (aa_geom A).
Let csR : class_state := refill_cs c cs.

Definition gh_nf : Z := Z.of_nat (length (cs_free_array cs)).
Definition gh_new : Z := ltac2:(tb__ "0|0|
SaS9S5S49Vcs;A1S36A2S48Vcs;A1A2S3aVc;A1A2").
Definition gh_chx : Z := ltac2:(tb__ "0|1|
S50S15S66S10S15S4bVcsR;A1M0A2U1A2G0Z0A4").
Definition PCE : Z := ltac2:(tb__ "0|0|
S5S5S4dS4cVA;A1A1Zd0A2S8Z50Vc;A2A2").
Definition U0 : Z := ltac2:(tb__ "0|0|
S5S47VSB;Vc;A2S49Vcs;A1A2").
Definition F0 : Z := ltac2:(tb__ "0|0|
S5S45VSB;Vc;A2S4aVcs;A1A2").
Definition FAb : Z := free_array SB c.

Definition ghosts (r : valuation) : Prop := ltac2:(tb__ "0|2|
S0S1S20Q40M0A1M1S17Vr;PdcA2S1fG0S46Vc;A1A2A3S0S1G1S17Vr;PddA2S1fG0S28A2A3S0S1G1S17Vr;PdeA2S1fG0S4aVcs;A1A2A3S0S1G1S17Vr;PdfA2S1fG0S48Vcs;A1A2A3S0S1G1S17Vr;Pe0A2S1fG0S49Vcs;A1A2A3S0S1G1S17Vr;Pe1A2S1fG0S39VSB;Vc;A2A2A3S0S1G1S17Vr;Pe2A2S1fG0S25A2A3S0S1G1S17Vr;Pe3A2S1fG0S64Vc;A1A2A3S0S1G1S17Vr;Pe4A2S1fG0S27A2A3S1G1S17Vr;Pe5A2S1fG0S30A2A3A2A2A2A2A2A2A2A2A2").
Definition frozen (r : valuation) : Prop := ltac2:(tb__ "0|0|
S0S16S74R1PdcA2S1S20Q40A1S17Vrb;R2A2S17Vr;R2A2A3F_;Fi;S16S1SfS20Q8A1A1S18Vrb;R1A2S18Vr;R1A2A3Fl;A2").

Definition entryR (W : list ulink) (st : ustop) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S0S1aS6aS72VA;Vrho;A2Vrb;A3S0S6fVsegs;VA;Vrb;Vtp0;Vmd0;A5S0S6dVA;Vrb;A2S0S6eVW;Vst;Vrb;A3S0S4eVA;Vnv;A2S0S0S6Z1Vnv;A2S6Vnv;Zfc00A2A2S0S6cVA;Vrb;A2S0S1S15S71VA;Vnv;A2Z0A3S67Vmd0;A1A2A2A2A2A2A2A2A2").

Definition subU (b : bool) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|1|
SdSfS11S20Q40A1M0G0A2A1Lb;Vb;S55Vl;S23S5S23S36A2A3Vl;Xdx2").
Definition subF (b : bool) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|1|
SdSfS11S20Q40A1M0G0A2A1Lb;Vb;S55Vl;S22S5S22S38A2A3Vl;Xdx2").
Definition committed (n : nat) : bool := (1 <=? n)%nat.
Definition revealedp (n : nat) : bool := (2 <=? n)%nat.
Definition releasedp (n : nat) : bool := (3 <=? n)%nat.
Definition shpage (base : Z) (p : word) : Prop := ltac2:(tb__ "0|0|
S4S15S15S0S0S6Z0R1A2S7R1Z8A2A2S1S15S21Q40Vp;A2S5S37Vbase;A1S8Z1000R1A2A2A3A2Lj;A2").
Definition mlink (ph : phase) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|d|
S54Vmd;A1S51S54Vmd0;A1S51S0S1SfS11S20Q40A1M0G0A2A1M1S57R2A1S57R1A1A3S0S1G1S59R2A1S59R1A1A3S0S1S15S56R2A1S56R1A1A3S0S1S15S52R2A1S52R1A1A3S0S1G1S58R2A1S2dS2aS5eVph;A1M2A1M3S2eS2aS62Vph;A1M4A1M5S58R1A1A2A2A3S0S1G1S53Vmd;A1S2dG3S2eG5S53Vmd0;A1A2A2A3S4SfG0A1M6G6S0S1G6Vtp;S14G0R1Vtp0;A3A3S0G0S65G0R1R2A3S0S3S65G0R2Vtp0;A3A1S2S0S1SdS26G4A1M7SeA3S2cS23R2A2A2S0S1SdS26G2A1M8SeA3S2cS22R2A2A2A2A2F_;Fp;S0S6SbS10G0R1A2A1S5SdS15L_;M9G7Z8MaZ0MbXdx2G9G8GaGbXdx2A2McA2S6S5cVmd;Vtp;A2S5S5S5S5cVmd0;Vtp0;A2G9G5S36GbXdx2A2G9G3S38GbXdx2A2S8Z1000GcA2A2A2A2A2A2Ltp1;A2A2A2A2A2A2A2TV0;TV;").

Definition zoneR (ph : phase) (z : Z) : Prop := ltac2:(tb__ "0|a|
S2S0S1SdS26S62Vph;A1M0A1SeA3S0S6S37S23A1M1Vz;A2S7Vz;S5G1Z8000M2A2A2A2A2S2S0S1SdS2bG0A1SeA3S0S6S23Vz;A2S7Vz;S5S23S36A2A2A2A2S2S0S1SdS26S5eVph;A1M3A1SeA3S0S6S37S22A1M4Vz;A2S7Vz;S5G4G2A2A2A2A2S2S0S1SdS2bG3A1SeA3S0S6S22Vz;A2S7Vz;S5S22S38A2A2A2A2S2S0S0S6S5S25S8Z4M5S9S5S28S27A2M6S5fVph;A1M7A2A2A2Vz;A2S7Vz;S5S25S8G5G6A2A2A2A2S7Z0G7A2A2S2S0S6S5S24Z10A2M8Vz;A2S7Vz;S5G8S8G5S60Vph;A1A2A2A2A2S2S0S1SdS5dVph;A1SeA3S0S6S24Vz;A2S7Vz;S5S24G5A2A2A2A2S0S1SdS61Vph;A1SeA3S0S6S39VSB;Vc;A2M9Vz;A2S7Vz;S5G9Z80A2A2A2A2A2A2A2A2A2A2A2").
Definition rlink (ph : phase) (m0 m : bview) : Prop := ltac2:(tb__ "0|a|
S0S15S3S35Vph;R1A2M0A1S1S12S20Q8A1M1A1M2Vm;R2A1M3Vm0;R2A1A3F_;Fz;S0S15G0S3S1G2G3S13G1A1A3A1F_;Fz;S0S15S0S6Z0M4R1A2M5S7R1S5fVph;A1A2A2S1cVm;S1dS5S25S8Z4M6S9S9S5S28S27A2Z1A2R2A2A2A2U4M7SaS5S48Vcs;A1S8R2S3aVc;A1A2A2Z10M8A2A3A2F_;Fj;S0S15S0G5S7R1S60Vph;A1A2A2S1cVm;S1dS5S5S24G8A2S8G6R2A2A2G7S50S15ScR2A1S4bVcsR;A1G4A4A3A2F_;Fi;S0S1SdS5dVph;A1SeA3S1cVm;S1dS24G7S64Vc;A1A3A2F_;S1SdS61Vph;A1SeA3S39VSB;Vc;A2S15S0S1cVm;S1dS5R1S43A2U8M9G4A3A2S0S1cVm;S1dS5R1S44A2G9SbS10S15S4fVcsR;A1A2A1A3A2S0S1cVm;S1dS5R1S40A2G9S4aVcsR;A1A3A2S0S1cVm;S1dS5R1S3eA2G9S48VcsR;A1A3A2S0S1cVm;S1dS5R1S3dA2G9G4A3A2S0S1cVm;S1dS5R1S42A2G9S49VcsR;A1A3A2S0S1cVm;S1dS5R1S41A2G9G4A3A2S1cVm;S1dS5R1S3fA2U1G4A3A2A2A2A2A2A2A2A2Tri;F_;A2A2A2A2A2").

Definition rmlink (f0 f : word -> option byte) : Prop := ltac2:(tb__ "0|1|
S15S0S6S3cR1A2S7R1S3bA2A2S1S12S20Q8A1A1Vf;S1fQ40R2A2M0A1Vf0;G0A1A3F_;Fa;").

Definition JR (ph : phase) : jpredA := ltac2:(tb__ "0|2|
S1bSfS20Q40A1A1SfS5bA1S5aS0S2fR4A1S0S31R4A1S0VKc;R2R1A2S0S32Vph;R3R1A3S0S33Vph;S1eVsegs;S19Vrb;A1M0A2S1eVsegs;S19R4A1M1A2A3S34G0G1A2A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JR_K : ltac2:(tb__ "0|0|
S63S70VKc;S29R1A1A2Fph;").
Proof. intros ph r t tr md (_ & _ & HK & _). exact HK. Qed.

Lemma JR_stable : ltac2:(tb__ "0|0|
S63S16S6bVKc;A1S73S69R2A2S68Vsegs;R3S29R4A1A3F_;F_;Fn;Fph;").
Proof.
  intros ph n HKc Hn r r' tp tr md md' Hag Hme (HF & HGh & HK & HM & HR & HRM).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (Hlt : forall i, (i < 240)%positive -> rw r' i = rw r i) by (intros i Hi; symmetry; apply Hw; unfold GR in Hn; lia).
  destruct Hme as ((mat' & ->) & Hpaid & _).
  split; [|split; [|split; [|split; [|split]]]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (Hlt i ltac:(lia)); exact (F1 i Hi) | intros l; rewrite <- (Hl l); exact (F2 l)].
  - unfold ghosts in *. rewrite !Hlt by lia. exact HGh.
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlink in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - rewrite Erm. exact HR.
  - rewrite Erm. exact HRM.
Qed.

End RJ.
