(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "div"; "mul"; "of_nat"; "sub"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "or"; "not"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "aa_live"; "class_state"; "cs_mapped_user"; "aa_cls"; "cs_empty"; "cs_free_array"; "topG"; "ag_ctx"; "cs_mapped_free_array"; "aa_cache_inited"; "ag_dtls"; "ag_fsb"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rzone.RZ"; "RZ"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "prod"; "true"; "length"; "app"; "cons"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "nthZ"; "AInvA"; "q_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "Sh"; "kFreeArraySize"; "rz"; "IMG_HI"; "IMG_LO"; "Size"; "kFreeArrayMapSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "needs_populate"; "kchunks"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "CZ"; "GEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ"; "envR"; "geoR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "refill_zone"; "rf_grows"; "rf_new"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rzone"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildSM RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma c24_nums : ltac2:(tb__ "0|4|
SaSdS9S31Z18M0A1Z2000M1A3SaSdS9S36G0A1Z1A3SaS0S34G0A1M2S3Z2M3Z28A2A2S0S1S5Z4S4G2G1A2A2S3G3Z12A2A2S3G3Z1dA2A2A2A2A2").
Proof. vm_compute. repeat split; intros; discriminate. Qed.

Lemma refill_zone_env : ltac2:(tb__ "0|4|
S1eS20S13S9S10R4A1S9S11R5A1S9S6S24S9S17R4A1A2A1S9S14R5A1S9S0Z0M0R3A2S0G0R2A2S0S5Z4M1R4A2S1aR8A1A2SdS20S35Z18M2R9A2S23A3SaS0S1R5S2bA2S33A2SaS0G0S42G2RaA2M3A2S0S5G1S1R6G3A2A2S2dA2A2A2F_;SdS20S41G2RaA2S23A3S0S1S1aRbA1S32A2S2dA2F_;S40RdRcG2RbRaA5SbS3eR9RaG2R8R7RbA6SaS0S1RaZ120A2RbA2S2RbS1RaZad0A2A2A2A2F_;F_;F_;F_;F_;F_;Tmu;Tnf;TSB;TT;Fz;Fcs;Finited;FG;").
Proof.
  intros G inited cs z T SB nf mu S0 Hmu Hnf HP HGr HZ. destruct c24_nums as (_ & K1 & _).
  unfold refill_zone in HZ. cbn zeta in HZ. fold T SB in HZ. rewrite K1 in HZ.
  unfold region_info, free_array, region_beg, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.
  rewrite kSpaceSize_val in HZ. fold nf mu in HZ, HP, HGr. unfold envR.
  assert (SHP : forall a, SB + 24 * 2 ^ 32 + mu <= a -> a + 262144 <= SB + 24 * 2 ^ 32 + 2 ^ 32 ->
                Sh (SB + 24 * 2 ^ 32 + mu) <= Sh a /\ Sh a + 32768 <= Sh (SB + 24 * 2 ^ 32 + 2 ^ 32)).
  { intros a A1 A2. split; [apply Geometry.Sh_mono; exact A1|]. unfold Sh.
    pose proof (Z.div_le_mono (a + 262144) (SB + 24 * 2 ^ 32 + 2 ^ 32) 8 ltac:(lia) A2) as D.
    replace (a + 262144) with (a + 32768 * 8) in D by lia. rewrite Z.div_add in D by lia. lia. }
  destruct HZ as [H|[H|[H|[(NP & H)|[(GR & H)|(_ & H)]]]]].
  - left. right; left. lia.
  - left. right; right; left. lia.
  - left. left. lia.
  - destruct (HP NP) as (P1 & P2 & P3). left. destruct H as [H|[H|H]].
    + do 4 right. left. lia.
    + do 5 right. destruct (SHP (SB + 24 * 2 ^ 32 + mu) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
    + do 3 right. left. lia.
  - pose proof GR as GR'. unfold rf_grows in GR'. apply andb_prop in GR' as [NP _]. destruct (HP NP) as (P1 & _ & _).
    specialize (HGr GR). left. destruct H as [H|H].
    + do 3 right. left. lia.
    + do 5 right. destruct (SHP (SB + 24 * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + cs_mapped_free_array cs) ltac:(lia) ltac:(lia)) as [S1 S2]. lia.
  - right. exact H.
Qed.

Section RZ.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model).
Hypothesis HA : ltac2:(tb__ "0|0|
S29S38VA;Vrho;Vtp;Vmd;A5").
#[local] Abbreviation G := (aa_geom A).
#[local] Abbreviation T := (ag_thread (aa_geom A)).
#[local] Abbreviation SB := (ag_spacebeg (aa_geom A)).
#[local] Abbreviation cs := (nthZ (aa_cls A) 24 cs_empty).
#[local] Abbreviation nf := (Z.of_nat (length (cs_free_array (nthZ (aa_cls A) 24 cs_empty)))).
#[local] Abbreviation mu := (cs_mapped_user (nthZ (aa_cls A) 24 cs_empty)).

Hypothesis HROOM : ltac2:(tb__ "0|2|
SdS20S35Z18M0S28S13S15VA;A1G0S16A4M1A2S23A3S0S1S14G1A1S2bA2S34G0A1A2F_;").
Definition RZ (z : Z) : Prop := ltac2:(tb__ "0|1|
S40SfVA;A1S1bVA;A1Z18M0S44VA;G0A2Vz;A5").

Definition GEO1 := F0A_rebuild.GEO A rho tp md 0 0 HA.
Lemma GEOR : ltac2:(tb__ "0|1|
S3fS11SfVA;A1M0A1S10G0A1S18G0A1A3").
Proof. destruct GEO1 as (T1 & T2 & SB1 & SB2 & _ & _ & ST & TB & _ & TG & _). unfold geoR. repeat split; try assumption; lia. Qed.
Lemma CNUM : ltac2:(tb__ "0|4|
SaS0Z0M0S6S24S9S17S28S13S15VA;A1Z18S16A4M1A1A2A1A2SaS0G0S14G1A1M2A2S0G2S7S3Z2M3Z20A2S3G3Z1dA2A2A2A2A2").
Proof.
  pose proof HA as (_ & _ & _ & (_ & _ & (_ & _ & _ & PC) & _) & _). pose proof (PC 24 ltac:(lia)) as P4. unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & _). unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N3.
  split; [apply Zle_0_nat | clear -N2 N3; lia].
Qed.
Lemma RZ_env : ltac2:(tb__ "0|4|
S9S1fR1A1SbS3eS11SfVA;A1M0A1S10G0A1M1Z18M2S6S24S9S17S28S13S15VA;A1G2S16A4M3A1A2A1S14G3A1R2A6SaS0S1G1Z120A2R2A2S2R2S1G1Zad0A2A2A2A2F_;Fz;").
Proof.
  intros z HZ. unfold RZ, SegQ_wf2.cls_of in HZ.
  pose proof HA as (_ & _ & _ & (_ & _ & (_ & _ & _ & PC) & _) & _). pose proof (PC 24 ltac:(lia)) as P4. unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & N4 & _ & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CV & _).
  destruct c24_nums as (S24 & K1 & M40 & MFA). destruct (cap_facts 24 ltac:(lia)) as (_ & _ & MCU & _). destruct GEO1 as (_ & _ & SB1 & _).
  rewrite S24 in N4. unfold slots in CV. rewrite S24 in CV. rewrite !Nat2Z.inj_add in CV.
  assert (NFS : 8192 * nf <= cs_allocated_user cs).
  { pose proof (Z.div_mod (cs_allocated_user cs) 8192 ltac:(lia)) as DM. rewrite N4 in DM.
    pose proof (Zle_0_nat (length (cs_cache cs))). pose proof (Zle_0_nat (length (live_ids G A 24))). pose proof (Zle_0_nat (length (q_ids G (qall A) 24))). lia. }
  assert (POP : needs_populate 24 cs = true -> mu + kUserMapSize <= kUserSpaceSize /\ 0 <= rf_new 24 cs /\ 4 * (nf + rf_new 24 cs) <= kFreeArraySize).
  { intros NP. specialize (HROOM NP). unfold rf_new. rewrite S24. unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *.
    set (au := cs_allocated_user cs) in *. set (m0 := cs_mapped_user cs) in *.
    pose proof (Z.div_mod (m0 + 2 ^ 18 - au) 8192 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (m0 + 2 ^ 18 - au) 8192 ltac:(lia)) as MB.
    pose proof (Z.div_mod (MUCAP 24) 8192 ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound (MUCAP 24) 8192 ltac:(lia)) as MB2.
    split; [clear -HROOM MCU; lia|]. split; [apply Z.div_pos; [clear -N2; lia | lia]|].
    clear -DM MB DM2 MB2 NFS HROOM MFA N2. lia. }
  apply (refill_zone_env G (aa_cache_inited A) cs z); [clear -SB1; lia | clear -N2; lia | clear -N6; lia | exact POP | | exact HZ].
  intros GR. pose proof GR as GR'. unfold rf_grows in GR'. apply andb_prop in GR' as [NP GL]. apply Z.ltb_lt in GL. destruct (POP NP) as (_ & _ & P3).
  specialize (HROOM NP). unfold rf_new in GL. rewrite S24 in GL. unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize in *.
  set (au := cs_allocated_user cs) in *. set (m0 := cs_mapped_user cs) in *.
  pose proof (Z.div_mod (m0 + 2 ^ 18 - au) 8192 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (m0 + 2 ^ 18 - au) 8192 ltac:(lia)) as MB.
  pose proof (Z.div_mod (MUCAP 24) 8192 ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound (MUCAP 24) 8192 ltac:(lia)) as MB2.
  clear -DM MB DM2 MB2 NFS HROOM MFA N2 GL. lia.
Qed.

Lemma RZ_out : ltac2:(tb__ "0|4|
S9S9S9SaS0R3R1A2S2R1R2A2A2SbS0R3S1S11SfVA;A1M0A1M1S3Z2M2Z20A2A2A2S0S1S1G1S3G2Z25A2A2Z1000A2R4A2A2SbS0R4S1S10G0A1M3Z120A2A2S0S1G3Zad0A2R5A2A2SbS0R5Z7fff8000A2S0Z10007fff8000R6A2A2ScS1fR5A1A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz O1 O2 O3 HZ. destruct CNUM as (NF0 & MUB). destruct (RZ_env z HZ) as [HE|HT]; [|clear -Hz O2 HT; lia].
  exact (env_out SB T (topG G) 24 nf mu lo hi z GEOR ltac:(lia) NF0 MUB Hz O1 ltac:(clear -O2; lia) O3 HE).
Qed.
Lemma RZ_top : ltac2:(tb__ "0|0|
S9S0S18SfVA;A1A1R1A2ScS1fR2A1A1F_;Fz;").
Proof.
  intros z Hz. destruct GEO1 as (_ & T2 & _ & SB2 & _ & _ & _ & _ & _ & TG & _).
  apply (RZ_out z (z + 1) z); [lia | right; clear -Hz SB2; lia | right; clear -Hz T2; lia | right; clear -Hz TG; lia].
Qed.
Lemma RZ_img : ltac2:(tb__ "0|0|
S9SaS0S30R1A2S2R1S2fA2A2ScS1fR2A1A1F_;Fz;").
Proof.
  intros z Hz. unfold IMG_LO, IMG_HI in Hz. destruct GEO1 as (T1 & _ & SB1 & _ & _ & _ & _ & _ & TI & _).
  destruct (Z_lt_dec z (T + 288)) as [L|L]; [|destruct (Z_le_dec (T + 2768) z) as [L'|L']; [|exfalso; clear -Hz L L' TI; lia]].
  - apply (RZ_out z (z + 1) z); [lia | left; clear -Hz SB1; lia | left; clear -L; lia | left; clear -Hz; lia].
  - apply (RZ_out z (z + 1) z); [lia | left; clear -Hz SB1; lia | right; clear -L'; lia | left; clear -Hz; lia].
Qed.
Lemma RZ_T : ltac2:(tb__ "0|1|
S9SbSaS0S10SfVA;A1A1M0R1A2S2R1S1G0Z120A2A2A2SaS0S1G0Zad0A2R1A2S2R1S1G0Z1000A2A2A2A2ScS1fR2A1A1F_;Fz;").
Proof.
  intros z Hz. destruct GEO1 as (_ & _ & _ & _ & _ & _ & ST & TB & _).
  apply (RZ_out z (z + 1) z); [lia | clear -Hz ST; lia | clear -Hz; lia | clear -Hz TB; lia].
Qed.
Lemma RZ_ctx : ltac2:(tb__ "0|1|
S9SaS0S19SfVA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS1fR2A1A1F_;Fz;").
Proof.
  intros z Hz. pose proof HA as (HG & _). destruct GEO1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TC & SC & _).
  pose proof (proj1 (proj2 (proj2 (geom_bands _ HG)))) as CB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in CB.
  apply (RZ_out z (z + 1) z); [lia | clear -Hz SC; lia | clear -Hz TC; lia | clear -Hz CB; lia].
Qed.

Lemma CZ_offT : ltac2:(tb__ "0|3|
S9S9S27S22S9S9A2M0A1M1G1SdG1S12VA;A1S25G0R2S26G0S21S9S9R4R3A4R1A3A3A3S39R5R4A2S9S3aR7R6R1A3ScSaS0S10SfVA;A1A1M2R2A2S2R2S1G2Z1000A2A2A2A1F_;Fz;F_;F_;Fl2;Fl1;Fn;Fp;").
Proof.
  intros p n l1 l2 HLV HCLS z HCZ. pose proof GEO1 as (_ & _ & _ & _ & _ & _ & _ & TB & _).
  destruct HCZ as [K|K]; [exact (proj1 (F0A_rebuild.CZA A rho tp md p n l1 l2 0 HA HLV HCLS z K))|].
  pose proof (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SHZ A rho tp md p n l1 l2 HA HLV HCLS z K)) as X. clear -X TB. lia.
Qed.
Lemma live_offT : ltac2:(tb__ "0|2|
S9S9S9S37S22S9S9A2S21S9S9R3R2A4S12VA;A1A3SbSaS0S7R4S2eR3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S2cR4A1M0R2A2S2R2S1G0S4S1R3Z7A2Z8A2A2A2A2A2ScSaS0S10SfVA;A1A1M1R3A2S2R3S1G1Z1000A2A2A2A1F_;F_;Fz;Fm;Fb;").
Proof.
  intros b m z Hin Hz. destruct (in_split _ _ Hin) as (k1 & k2 & Hsplit).
  pose proof HA as (_ & _ & _ & (Hsep & _) & _). destruct (Hsep b m Hin) as (L1 & _ & _ & _ & _ & _ & _ & L8).
  apply (CZ_offT b m k1 k2 Hsplit L8 z). unfold F0A_rebuild.CZ. pose proof (N8_facts m L1) as (NB1 & _).
  destruct Hz as [Hz|Hz]; [left; clear -Hz NB1; lia | right].
  assert (E8 : (m + 7) / 8 = N8 m / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity). rewrite <- E8. exact Hz.
Qed.
Lemma qfoot_offT : ltac2:(tb__ "0|1|
S9S2aVA;R1A2ScSaS0S10SfVA;A1A1M0R2A2S2R2S1G0Z1000A2A2A2A1F_;Fz;").
Proof.
  intros z Hz. pose proof GEO1 as (_ & _ & SB1 & SB2 & _ & _ & ST & TB & _ & TG & _).
  pose proof HA as (HG & _ & _ & (Hsep & _ & (_ & _ & _ & PC) & Hsec & HQR & _) & _ & HI3 & _).
  pose proof (quarantine_repr_pure _ A HG HQR) as (HQP & _).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }
  destruct (qfoot_cases A _ HG HI3 HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
  - destruct (Size_facts c' D1) as (SZ' & SM'). unfold czone in CZ. cbn zeta in CZ.
    destruct CZ as [K|K]; [unfold kUserSpaceSize, kRegionSize, kFreeArraySize in OE; clear -K ST D1 O0 OE SZ'; lia|].
    assert (SHB : 2147446784 <= z < 17594333495296).
    { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SH_band (SB + c' * 2 ^ 32 + o') (SB + c' * 2 ^ 32 + o' + Size c') z).
      - clear -SB1 D1 O0. lia.
      - unfold kUserSpaceSize, kRegionSize, kFreeArraySize in OE. clear -SB2 TG D1 OE. lia.
      - split; [exact (proj1 K)|]. eapply Z.lt_le_trans; [exact (proj2 K)|]. apply Sh_add_le; [clear -SB1 D1 O0; lia | clear -SZ'; lia | clear; lia]. }
    clear -SHB TB. lia.
  - destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (E1 & E2 & _). destruct D10 as (D10a & _).
    destruct Hr as [K|K]; [clear -K E2; lia|].
    assert (SHB : 2147446784 <= z < 17594333495296) by (apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SH_band (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -D10a; lia | clear -D12 TG; lia | exact K]).
    clear -SHB TB. lia.
Qed.

Lemma RZ_CZ : ltac2:(tb__ "0|2|
S9S9S27S22S9S9A2M0A1M1G1SdG1S12VA;A1S25G0R2S26G0S21S9S9R4R3A4R1A3A3A3S39R5R4A2S9S3aR7R6R1A3ScS1fR2A1A1F_;Fz;F_;F_;Fl2;Fl1;Fn;Fp;").
Proof.
  intros p n l1 l2 HLV HCLS z HCZ HZ. destruct CNUM as (NF0 & MUB). pose proof GEO1 as (_ & _ & _ & _ & _ & _ & _ & TB & _).

  assert (NT : ~ (T <= z < T + 4096)).
  { destruct HCZ as [K|K]; [exact (proj1 (F0A_rebuild.CZA A rho tp md p n l1 l2 0 HA HLV HCLS z K))|].
    pose proof (proj1 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SHZ A rho tp md p n l1 l2 HA HLV HCLS z K)) as X. clear -X TB. lia. }
  destruct (RZ_env z HZ) as [HE|HT]; [|clear -NT HT; lia].
  destruct (is_primary n) eqn:HP.
  - pose proof (F0A_rebuild.KP A rho tp md p n l1 l2 0 HA HLV HCLS HP) as KPx. cbv zeta in KPx.
    destruct KPx as (_ & E16 & O0 & _ & OE & AM & MM & _ & C1 & (SZ0 & _) & _ & _ & CZ').
    pose proof (CZ' z HCZ) as CZz. rewrite <- E16 in CZz. unfold czone in CZz. cbn zeta in CZz.
    assert (SEP : ClassID (needed n) <> 24 \/ p - rz n - (SB + ClassID (needed n) * 2 ^ 32) + Size (ClassID (needed n)) <= mu).
    { destruct (Z.eq_dec (ClassID (needed n)) 24) as [EC|NC]; [right | left; exact NC]. rewrite EC in OE, AM |- *. clear -OE AM. lia. }
    set (c := ClassID (needed n)) in *. set (o := p - rz n - (SB + c * 2 ^ 32)) in *.
    exact (slot_out SB T (topG G) 24 nf mu c o (Size c) z GEOR ltac:(clear; lia) NF0 MUB C1 O0 ltac:(clear -SZ0; lia) ltac:(clear -OE AM MM; lia) SEP CZz HE).
  - destruct (F0A_rebuild.KS A rho tp md p n l1 l2 0 HA HLV HCLS HP) as (i & ch & _ & _ & _ & _ & _ & _ & MT & ML & MBD & MSP & MTH & _ & _ & _ & _ & _ & MZ).
    pose proof GEO1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
    destruct (MZ z HCZ) as [Hz|Hz].
    + apply (env_out SB T (topG G) 24 nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEOR ltac:(clear; lia) NF0 MUB Hz); [clear -MSP; lia | clear -MTH; lia | clear -MBD; lia | exact HE].
    + apply (env_sh_out SB T (topG G) 24 nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEOR ltac:(clear; lia) NF0 MUB Hz); [clear -ML; lia | clear -MT TG; lia | clear -MSP; lia | exact HE].
Qed.

Lemma RZ_live : ltac2:(tb__ "0|1|
S9S9S9S37S22S9S9A2S21S9S9R3R2A4S12VA;A1A3SbSaS0S7R4S2eR3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S2cR4A1M0R2A2S2R2S1G0S4S1R3Z7A2Z8A2A2A2A2A2ScS1fR3A1A1F_;F_;Fz;Fm;Fb;").
Proof.
  intros b m z Hin Hz. destruct (in_split _ _ Hin) as (k1 & k2 & Hsplit).
  pose proof HA as (_ & _ & _ & (Hsep & _) & _). destruct (Hsep b m Hin) as (L1 & _ & _ & _ & _ & _ & _ & L8).
  apply (RZ_CZ b m k1 k2 Hsplit L8 z). unfold F0A_rebuild.CZ. pose proof (N8_facts m L1) as (NB1 & _).
  destruct Hz as [Hz|Hz]; [left; clear -Hz NB1; lia | right].
  assert (E8 : (m + 7) / 8 = N8 m / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity). rewrite <- E8. exact Hz.
Qed.

Lemma RZ_qfoot : ltac2:(tb__ "0|0|
S9S2aVA;R1A2ScS1fR2A1A1F_;Fz;").
Proof.
  intros z Hz HZ. destruct CNUM as (NF0 & MUB). pose proof GEO1 as (_ & _ & _ & _ & _ & _ & ST & TB & _ & TG & _).
  pose proof HA as (HG & _ & _ & (Hsep & _ & (_ & _ & _ & PC) & Hsec & HQR & _) & _ & HI3 & _).
  pose proof (quarantine_repr_pure _ A HG HQR) as (HQP & _).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }
  destruct (qfoot_cases A _ HG HI3 HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
  - destruct (q_ids_valid A c' (o' / 16) D1 HQP IDin) as (_ & _ & V3).
    destruct (Size_facts c' D1) as (SZ' & SM').
    rewrite (id16_of o' (Size c') ltac:(clear -SZ'; lia) SM' OM) in V3.
    unfold czone in CZ. cbn zeta in CZ.
    assert (NT : ~ (T <= z < T + 4096)).
    { destruct CZ as [K|K]; [unfold kUserSpaceSize, kRegionSize, kFreeArraySize in OE; clear -K ST D1 O0 OE SZ'; lia|].
      assert (SHB : 2147446784 <= z < 17594333495296).
      { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SH_band (SB + c' * 2 ^ 32 + o') (SB + c' * 2 ^ 32 + o' + Size c') z).
        - pose proof GEO1 as (_ & _ & SB1 & _). clear -SB1 D1 O0. lia.
        - pose proof GEO1 as (_ & _ & _ & SB2 & _). unfold kUserSpaceSize, kRegionSize, kFreeArraySize in OE. clear -SB2 TG D1 OE. lia.
        - split; [exact (proj1 K)|]. eapply Z.lt_le_trans; [exact (proj2 K)|]. apply Sh_add_le; [pose proof GEO1 as (_ & _ & SB1 & _); clear -SB1 D1 O0; lia | clear -SZ'; lia | clear; lia]. }
      clear -SHB TB. lia. }
    destruct (RZ_env z HZ) as [HE|HT]; [|clear -NT HT; lia].
    apply (slot_out SB T (topG G) 24 nf mu c' o' (Size c') z GEOR ltac:(clear; lia) NF0 MUB D1 O0 ltac:(clear -SZ'; lia) OE); [|exact CZ|exact HE].
    destruct (Z.eq_dec c' 24) as [EC|NC]; [right | left; exact NC].
    pose proof (PC 24 ltac:(clear; lia)) as P4. unfold class_repr in P4. destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _).
    rewrite EC in V3 |- *. unfold SegQ_wf2.cls_of in V3. clear -V3 N2. lia.
  - destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D8.
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (E1 & E2 & _). rewrite kSpaceSize_val in E1.
    destruct D10 as (D10a & D10l & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
    assert (NT : ~ (T <= z < T + 4096)).
    { destruct Hr as [K|K]; [clear -K E2; lia|].
      assert (SHB : 2147446784 <= z < 17594333495296) by (apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.SH_band (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -D10a; lia | clear -D12 TG; lia | exact K]).
      clear -SHB TB. lia. }
    destruct (RZ_env z HZ) as [HE|HT]; [|clear -NT HT; lia].
    destruct Hr as [K|K].
    + apply (env_out SB T (topG G) 24 nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEOR ltac:(clear; lia) NF0 MUB K); [clear -E1; lia | clear -E2; lia | clear -D10b; lia | exact HE].
    + apply (env_sh_out SB T (topG G) 24 nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEOR ltac:(clear; lia) NF0 MUB K); [clear -D10a; lia | clear -D12 TG; lia | clear -E1; lia | exact HE].
Qed.
End RZ.

Section KEEP.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model).
Hypothesis HA : ltac2:(tb__ "0|0|
S29S38VA;Vrho;Vtp;Vmd;A5").
Hypothesis HROOM : ltac2:(tb__ "0|2|
SdS20S35Z18M0S28S13S15VA;A1G0S16A4M1A2S23A3S0S1S14G1A1S2bA2S34G0A1A2F_;").
#[local] Abbreviation G := (aa_geom A).
#[local] Abbreviation T := (ag_thread (aa_geom A)).
#[local] Abbreviation SB := (ag_spacebeg (aa_geom A)).

Lemma client_where : ltac2:(tb__ "0|5|
S9S3cVCST;VA;R1A3SbSeS9S9SeS9S9SaS37S22S9S9A2S21S9S9R2R1A4S12VA;A1A3SaS0R2R4A2S2R4S1R2R1A2A2A2A2Ln;A2Lb;A2SaSaS0Z0R2A2S2R2S3Z2M0Z2fA2A2A2SaSbS2R2S11SfVA;A1M1A1M2A2S0S1S1G2S3G0Z25A2A2Z1000M3A2R2A2A2SaSbS2R2S10G1A1M4A2S0S1G4G3A2R2A2A2SbS2R2Z7fff7000A2S0Z10007fff8000R2A2A2A2A2A2A2F_;Fy;").
Proof.
  intros y Hy. pose proof HA as (HG & _ & HF & (Hsep & _) & _).
  pose proof (F0A_rebuild.GEO A rho tp md 0 0 HA) as (T1 & T2 & SB1 & SB2 & _ & _ & ST & TB & TI & TG & F1 & F2 & FT & FS & FB & _).
  destruct (client_addr_cases CST A y _ HF Hy) as [S|[L|[FR|[C|FL]]]].
  - right. clear -S SB2 T2 TG. lia.
  - left. exact L.
  - right. destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. clear -Hyf M F1 F2 FT FS FB TG. lia.
  - right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. clear -X SB1 TI. lia.
  - right. destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags. rewrite FS_kFlagsOffset_val.
    unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M. clear -M F1 F2 FT FS FB TG. lia.
Qed.

Theorem RZ_keep : ltac2:(tb__ "0|0|
S9SbS3cVCST;VA;R1A3S3dVCST;VXGL;VA;R1A4A2ScS43VA;R2A2A1F_;Fa;").
Proof.
  intros a Ha. pose proof HA as (HG & _ & HF & (Hsep & _) & _).
  pose proof (F0A_rebuild.GEO A rho tp md 0 0 HA) as (T1 & T2 & SB1 & SB2 & _ & _ & ST & TB & TI & TG & _).

  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> (y < SB \/ SB + 2 ^ 37 + 4096 <= y) -> ~ RZ A (Sh y)).
  { intros y By Hy HZ. destruct (CNUM A rho tp md HA) as (NF0 & MUB).
    pose proof (RebuildRZ.Sh_band y ltac:(clear -By; lia)) as SBD.
    destruct (RZ_env A rho tp md HA HROOM (Sh y) HZ) as [HE|HT]; [|clear -SBD HT TB; lia].
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (env_sh_out SB T (topG G) 24 _ _ (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) (GEOR A rho tp md HA) ltac:(clear; lia) NF0 MUB); [|clear -By DY MY; lia|clear -By DY MY; lia| |exact HE].
    - unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
      replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
      clear. lia.
    - destruct Hy as [Hy|Hy]; [left; clear -Hy DY MY SB1; lia | right; clear -Hy DY MY; lia]. }
  assert (LIVE_SH : forall b n y, In (b, n) (aa_live A) -> b <= y < b + n -> ~ RZ A (Sh y)).
  { intros b n y Hbn Hyb. apply (RZ_live A rho tp md HA HROOM b n (Sh y) Hbn). right.
    destruct (in_split _ _ Hbn) as (k1 & k2 & Hsplit). destruct (Hsep b n Hbn) as (_ & _ & _ & _ & _ & _ & _ & L8).
    pose proof (F0A_rebuild.BLK A rho tp md b n k1 k2 0 HA Hsplit L8) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B8).
    unfold Sh. destruct (proj1 (Z.mod_divide b 8 ltac:(clear; lia)) B8) as [qb Hqb].
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as MN.
    rewrite Hqb. rewrite Z.div_mul by (clear; lia). clear -Hyb Hqb DY MY DN MN. lia. }
  destruct Ha as [CL|[(y & Cy & ->)|(y & Gy & ->)]].
  - destruct (client_where a CL) as [(b & n & Hbn & Hab)|(B1 & B2 & B3 & B4)].
    + apply (RZ_live A rho tp md HA HROOM b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + apply (RZ_out A rho tp md HA HROOM a (a + 1) a ltac:(clear; lia)); [clear -B2; lia | clear -B3; lia | clear -B4; lia].
  - destruct (client_where y Cy) as [(b & n & Hbn & Hyb)|(B1 & B2 & B3 & B4)]; [exact (LIVE_SH b n y Hbn Hyb) | exact (SHY y B1 B2)].
  - destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y); [clear -Y1 Y2; lia | left; clear -Y2 SB1; lia].
Qed.
End KEEP.
