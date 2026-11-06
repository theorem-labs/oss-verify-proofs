(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "div"; "mul"; "sub"; "eq_dec"; "land"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "app"; "cons"; "nil"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sobj"; "rw"; "sprop"; "swf"; "valuation"; "sv"; "rm"; "soff"; "ss_facts"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kSpaceSize"; "region_beg"; "HIGH_SHADOW_END"; "SHADOW_OFF"; "Size"; "kRegionSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ag_spacebeg"; "ageom"; "AA"; "aa_geom"; "ag_ctx"; "ag_thread"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "UStopLeOrPc"; "unwind_factsS"; "A_globals"; "KcA"; "Kc_ok"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C3"; "BP"; "BR"; "BSH"; "BU"; "F_gen"; "LPe"; "LRe"; "LTe"; "LUe"; "M48"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "ab_e"; "ube"; "uee"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "geom_ok"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "present"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "chk_of"; "cls_of"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4.B3"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "rup8"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "pvals_ok"; "sep_geom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Sh_mono : ltac2:(tb__ "0|0|
S4S4S6R2R1A2S6S26R3A1S26R2A1A2F_;Fb;Fa;").
Proof. intros a b H. unfold Sh. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma Sh_lt_HSE : ltac2:(tb__ "0|0|
S4S8R1SaZ2Z2fA2A2S8S26R2A1S29A2F_;Fa;").
Proof. intros a H. unfold Sh, HIGH_SHADOW_END, SHADOW_OFF. pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fs_footb_space : ltac2:(tb__ "0|1|
S32S4S5fR2A1S1S6S31R3A1M0R2A2S8R2S7S7G0S27A2Z1000A2A2A2S0S13S5eR4R3A2S19A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof HG as HG0. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite kSpaceSize_val in Hz. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (Sh_lt_HSE (ag_fsb G + FS_total) ltac:(rewrite FS_total_val; lia)) as S1. unfold HIGH_SHADOW_END in S1.
  rewrite FS_total_val in S1.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset; lia.
Qed.

Lemma fs_footb_space_sh : ltac2:(tb__ "0|1|
S32S4S5fR2A1S1S6S26S31R3A1M0A1R2A2S8R2S26S7S7G0S27A2Z1000A2A1A2A2S0S13S5eR4R3A2S19A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  rewrite kSpaceSize_val in Hz. pose proof (topG_range G) as ACV.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (Sh_lt_HSE (ag_spacebeg G + 2 ^ 37 + 4096) ltac:(lia)) as S1. unfold HIGH_SHADOW_END in S1.

  pose proof (proj1 (geom_bands _ HG)) as FB. rewrite FS_total_val in FB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in FB.
  assert (S0 : 2147450880 <= Sh (ag_spacebeg G)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (ag_spacebeg G) 8); lia).
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_frames_off_val; unfold FS_kFlagsOffset;
    [clear -Hz FB S0 S1 G2 G3 ACV; lia | clear -Hz FB S0 S1 G2 G3 ACV; lia |].
  destruct G18 as [G18|G18].
  - right. pose proof (Sh_mono (ag_fsb G + 11571200) (ag_spacebeg G) G18). lia.
  - left. pose proof (Sh_mono (ag_spacebeg G + 2 ^ 37 + 4096) (ag_fsb G + 36864) ltac:(lia)). lia.
Qed.

Definition sep_geom (G : ageom) : Prop := ltac2:(tb__ "0|5|
S1S3S6S7S36VG;A1M0Z1000M1A2S31VG;A1M2A2S6S7S7G2S27A2G1A2M3G0A2A2S3S6S7S35VG;A1M4G1A2G2A2S6G3G4A2A2A2").

Lemma blk_facts : ltac2:(tb__ "0|8|
S15S47A1S33S20S15S12Q40A1A1S73S4S60R6R5R4R3R2A5S1S6Z1M0R2A2S6R2Zfc00A2A2S6G0S64R7R3A2A2S34R8A1S32S66R5A1S4S65RaR6A2S4S7S28S31R3A1R2A2ScZ10M1R1A2A2S4S63RdS22RbA1A2S62S1S1S6Z0M2R3A2S8R3SaZ2Z1cA2A2A2S1S0S4S9ScG1R3A2S2bR4A1M3A2G2A3S1S6S31R5A1M4R2A2S1S6S7R2G3A2M5S7S28G4R4A2M6S2dA2A2S1S6S7G6S2cA2S7G4S27A2A2S1S61R1R2G5A3S61R1S26R2A1M7S7G7SbG3Z8A2A2A3A2A2A2A2A2A2Tm;Tab;Tx;Tc;TG;F_;F_;F_;Fnv;Fmd;Ftp;Frho;FA;Fsegs;").
Proof.
  intros segs A rho tp md nv HA Hnv Hcnt G c x ab m. unfold ab, m, x, c, G. clear G c x ab m.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4).
  unfold chk_of, cnt_of, cst_of in *.
  set (c := cls_of nv) in *. set (m := view segs (rm rho)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM).
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & PU & PSH & PE & ND & LV & CI & CN & _ & _ & _ & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  set (x := nth (length (cs_cache cs) - 1) (cs_cache cs) 0) in *.
  assert (Hin : In x (cs_free_array cs ++ cs_cache cs)).
  { apply in_or_app. right. unfold x. apply nth_In. lia. }

  pose proof (fun z Hz => slot_not_live segs A rho tp md c x z HA C1 Hin Hz) as NLV.
  destruct (N7 _ Hin) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia.
  change (2 ^ 4) with 16 in X2, X3.
  pose proof HG as HG0. pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N2, N3 |- *. rewrite kSpaceSize_val. unfold region_beg, kRegionSize in *.
  set (SB := ag_spacebeg (aa_geom A)) in *.

  assert (AR : 0 <= x < 2 ^ 28 /\ 16 * x + Size c <= cs_allocated_user cs /\ 0 <= cs_allocated_user cs <= cs_mapped_user cs
               /\ cs_mapped_user cs <= 2 ^ 32 - 2 ^ 29 /\ 1 <= c <= 30 /\ 16 <= Size c /\ Size c mod 16 = 0
               /\ 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= 140737479966720).
  { pose proof (topG_range (aa_geom A)) as TG. clear -X1 X3 N2 N3 C1 C2 C3 G13 G14 TG. lia. }
  assert (MT : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG0 | exact Hz]. }
  assert (MTS : forall z, Sh SB <= z < Sh (SB + kSpaceSize + 4096) -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = m z).
  { intros z Hz. apply maskv_out. apply fs_footb_space_sh; [exact HG0 | exact Hz]. }
  rewrite kSpaceSize_val in MT, MTS.
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 N1 N2 N3 N4 N5 N6 X1 X3 ND LV CI CN HR HF HM Hsep Hlive HTH HG0 HA Hin N7 PE.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  split; [exact A1|]. split; [rewrite Z.mul_comm; exact X2|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros z Hz. destruct (PU z ltac:(lia) (NLV z ltac:(unfold region_beg, kRegionSize; fold SB; lia))) as [b Hb]. exists b. rewrite <- (MT z) by lia. exact Hb.
  - intros z Hz.
    assert (S1 : Sh (SB + c * 2 ^ 32) <= Sh (SB + c * 2 ^ 32 + 16 * x)) by (apply Sh_mono; lia).
    assert (S2 : Sh (SB + c * 2 ^ 32 + 16 * x) + Size c / 8 <= Sh (SB + c * 2 ^ 32 + cs_mapped_user cs)).
    { unfold Sh. pose proof (Z.div_le_mono (SB + c * 2 ^ 32 + 16 * x + Size c) (SB + c * 2 ^ 32 + cs_mapped_user cs) 8 ltac:(lia) ltac:(lia)) as D.
      replace (SB + c * 2 ^ 32 + 16 * x + Size c) with (SB + c * 2 ^ 32 + 16 * x + (Size c / 8) * 8) in D by lia.
      rewrite Z.div_add in D by lia. lia. }
    pose proof (Sh_mono SB (SB + c * 2 ^ 32) ltac:(lia)).
    pose proof (Sh_mono (SB + c * 2 ^ 32 + cs_mapped_user cs) (SB + 2 ^ 37 + 4096) ltac:(lia)).
    destruct (PSH z ltac:(lia)) as [b Hb]. exists b. rewrite <- (MTS z) by lia. exact Hb.
Qed.

Lemma SPA_entails0 : ltac2:(tb__ "0|0|
S15S47A1S39S5S2fS2fS4bS20S15S12Q40A1A1S48S0S13S30R6R5R4A3S14A3S0S13S4aR5R8A2S14A3S3aRbR9RaA3S38RcRbR9R6R5R4A6S38RdRcR9S49R7R8A2R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FT0;FL;Fg;FJ;Fsegs;").
Proof.
  intros segs J g L T0 s rho tp w He Hid HJ [Hsm Hk].
  split; [eapply smatchA_entails; eauto | eapply HJ; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk]].
Qed.

Lemma chain_pre_factsS : ltac2:(tb__ "0|1|
S15S3bA1M0S3cS1eS0S3cR2S3dA3S0G0R4S18S3bA1A3F_;S71S1eR2S42R4A1A3S71S1eR3S3eR5R4A2A3F_;F_;Fp;Fst;FW;").
Proof. intros W st p HW Hp. destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. Qed.

Lemma land_M48 : ltac2:(tb__ "0|0|
S4S1S6Z0R1A2S8R1SaZ2Z30A2A2A2S0S4SfR2S56A2SdR2S9R2Z8A2A2A3F_;Fn;").
Proof.
  intros n Hn. unfold M48.
  replace 281474976710648 with (Z.land (2 ^ 64 - 2 ^ 3) (Z.ones 48)) by reflexivity.
  rewrite Z.land_comm, <- Z.land_assoc, (Z.land_comm (Z.ones 48) n), Z.land_ones by lia.
  rewrite (Z.mod_small n (2 ^ 48)) by lia. rewrite Z.land_comm. rewrite land_high_mask by lia. reflexivity.
Qed.
Lemma land_7 : ltac2:(tb__ "0|0|
S4S6Z0R1A2S0S4SfR2Z7A2S9R2Z8A2A3F_;Fn;").
Proof. intros n Hn. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma soff_of_val : ltac2:(tb__ "0|0|
S20S21S4S0S4S10Q40S1bR3R2A2A2R1A3S1S6Z0R2A2S8R2SaZ2Z3fA2A2A2S0S4S23R5R4A2R3A3F_;F_;Fv;Fe;Frho;").
Proof. intros rho e v He Hv. rewrite soff_snorm. unfold U. rewrite He. unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); lia. Qed.

Definition pvals_ok (rho : valuation) (SB c x rzv sz n : Z) : Prop := ltac2:(tb__ "0|6|
S1S0S12Q40M0A1M1S1dVrho;PcA2S11G0Vn;A2A3S1S0G1S1dVrho;P94A2S11G0Vsz;A2A3S1S0G1S1dVrho;P96A2S11G0Vrzv;A2A3S1S0G1S1dVrho;P9bA2S11G0VSB;A2A3S1S0G1S1dVrho;P9eA2S11G0Vc;A2A3S1S0G1S1dVrho;P9fA2S11G0Vx;A2A3S1S1S6Z1Vn;A2S6Vn;Zfc00A2A2S1S1S1S6Z10M2Vsz;A2S6Vsz;Z10000A2A2S0S4S9Vsz;G2A2Z0M3A3A2S1S1S1S6G2Vrzv;A2S6Vrzv;Z400A2A2S0S4S9Vrzv;G2A2G3A3A2S1S1S6S7Vn;Vrzv;A2Vsz;A2S8Vn;Z8M4A2S6S7G4Vrzv;A2Vsz;A2F_;A2S1S1S6Z10007fff8000VSB;A2S0S4S9VSB;SaZ2M5G2A2A2G3A3A2S1S1S6G3Vc;A2S6Vc;Z1eA2A2S1S1S6G3Vx;A2S8Vx;SaG5Z1cA2A2A2S6S7S7S7VSB;ScVc;SaG5Z20A2A2A2ScG2Vx;A2A2Vsz;A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Section PieceVals.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S79Vrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S7S7VSB;ScVc;SaZ2Z20A2A2A2ScZ10Vx;A2A2").
Let ub : Z := ab + rzv.
Let r8 : Z := ltac2:(tb__ "0|1|
SdS7Vn;Z7A2M0S9G0Z8A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_ab : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5bA2A2Vab;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV.
  unfold ab_e, vSB, V_CH, V_CLS. cbn [eval]. rewrite E159, E158, E155. rewrite add_val, sll_val, add_val, sll_val, !u64_lit by lia.
  change (4 mod 64) with 4. change (32 mod 64) with 32. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (x * 16)) by lia.
  rewrite (Z.mod_small (c * 2 ^ 32 + _)) by lia. rewrite Z.mod_small by lia. unfold ab. lia.
Qed.
Lemma pv_ub : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5cA2A2Vub;A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold ube. cbn [eval]. fold ab_e. rewrite add_val, pv_ab. unfold V_RZ. rewrite E150, u64_lit by lia.
  rewrite Z.mod_small by (unfold ab; lia). reflexivity.
Qed.
Lemma pv_ue : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S5dA2A2S7Vub;Vn;A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold uee. cbn [eval]. fold ube. rewrite add_val, pv_ub, E12, u64_lit by lia.
  rewrite Z.mod_small by (unfold ub, ab; lia). reflexivity.
Qed.
Lemma Sh_small : ltac2:(tb__ "0|4|
S4S1S6Z0M0R1A2S6R1Z7fffff800000A2A2S1S1S6G0S26R2A1M1A2S8G1Z10007fff8000A2A2S1S0S4S9S7SbR2Z8A2M2S2aA2SaZ2M3Z40A2A2G1A3S1S6G0G2A2S8G2SaG3Z3dA2A2A2A2A2F_;Fa;").
Proof.
  pv.
  intros a Ha. pose proof (eq_refl 140737479966720) as ACV. unfold Sh, SHADOW_OFF.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma pv_bsh : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4fA2A2S26Vab;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BSH, gsv, shb. cbn [eval]. fold ab_e. rewrite add_val, srl_val, pv_ab, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ab ltac:(unfold ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_bu : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S50A2A2S26Vub;A1A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BU, gsv, shb. cbn [eval]. fold ube. rewrite add_val, srl_val, pv_ub, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (_ & E & _). exact E.
Qed.
Lemma pv_lu : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S55A2A2SbVn;Z8A2A3").
Proof.
  pv.
  unfold LUe, n8e. cbn [eval]. rewrite srl_val, and_val, E12, !u64_lit by (unfold M48; lia). change (3 mod 64) with 3.
  rewrite land_M48 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). nia.
Qed.
Lemma pv_lp : ltac2:(tb__ "0|4|
S0S4S10Q40S1bVrho;S52A2A2S37S0S4S9Vn;Z8A2M0Z0M1A3M2S2G2A1M3A2S4L_;SeG0G1A2G2G1L_;G3Z1L_;X37x2A3").
Proof.
  pv.
  unfold LPe. cbn [eval]. rewrite srl_val, add_val, and_val, E12, !u64_lit by lia. change (3 mod 64) with 3.
  rewrite land_7 by lia. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE]; [rewrite E; reflexivity|].
  symmetry. apply (Z.div_unique _ _ _ (n mod 8 - 1)); lia.
Qed.
Lemma r8_facts : ltac2:(tb__ "0|5|
S1S0S4S9Vr8;Z8M0A2Z0M1A3S1S1S6Vn;Vr8;A2S6Vr8;S7Vn;Z7A2A2A2S1S6G0Vr8;A2S0S4Vr8;S7ScG0SbVn;G0A2A2S37S0S4S9Vn;G0A2M2G1A3M3S2G3A1M4A2S4L_;SeG2G1A2G3G1L_;G4G0L_;X37x2A2A3A2A2A2").
Proof.
  pv.
  unfold r8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  destruct (Z.eq_dec (n mod 8) 0) as [E|NE].
  - assert ((n + 7) mod 8 = 7). { symmetry. apply Z.mod_unique with (q := n / 8); lia. } lia.
  - assert ((n + 7) mod 8 = n mod 8 - 1). { symmetry. apply Z.mod_unique with (q := n / 8 + 1); lia. } lia.
Qed.
Lemma pv_rup8 : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S76A2A2Vr8;A3").
Proof.
  pv.
  unfold rup8. cbn [eval]. rewrite and_val, add_val, E12, !u64_lit by lia.
  change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite (Z.mod_small (n + 7)) by lia. rewrite land_high_mask by lia.
  unfold r8. reflexivity.
Qed.
Lemma pv_lr : ltac2:(tb__ "0|1|
S1S0S4S10Q40S1bVrho;S53A2A2SbSdSdVsz;Vrzv;A2Vr8;A2M0Z8A2A3S6Z0G0A2A2").
Proof.
  pv.
  pose proof r8_facts as (R1 & R2 & R3 & R4).
  assert (F : 0 <= sz - rzv - r8) by (destruct (Z_lt_dec n 8); lia).
  split; [|exact F].
  unfold LRe. cbn [eval]. fold rup8. rewrite srl_val, sub_val, sub_val, pv_rup8. unfold V_SIZE, V_RZ. rewrite E148, E150, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite (Z.mod_small (sz - rzv)) by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma pv_lt : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S54A2A2SdSdVsz;Vrzv;A2Vn;A2A3").
Proof.
  pv.
  unfold LTe, V_SIZE, V_RZ. cbn [eval]. rewrite sub_val, sub_val, E148, E150, E12, !u64_lit by lia.
  rewrite (Z.mod_small (sz - rzv)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_bp : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4dA2A2S7S26Vub;A1SbVn;Z8A2A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. unfold BP. cbn [eval]. fold BU. fold LUe. rewrite add_val, pv_bu, pv_lu.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (S1 & _ & _).
  pose proof (Z.div_lt_upper_bound n 8 (2 ^ 13) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pv_br : ltac2:(tb__ "0|0|
S0S4S10Q40S1bVrho;S4eA2A2S7S26Vub;A1SbVr8;Z8A2A2A3").
Proof.
  pv.
  pose proof (eq_refl 140737479966720) as ACV. pose proof r8_facts as (R1 & R2 & R3 & R4).
  unfold BR. cbn [eval]. fold BP. fold LPe. rewrite add_val, pv_bp, pv_lp.
  destruct (Sh_small ub ltac:(unfold ub, ab; lia)) as (S1 & _ & _).
  pose proof (Z.div_lt_upper_bound n 8 (2 ^ 13) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (destruct (Z.eq_dec (n mod 8) 0); lia).
  rewrite R4. destruct (Z.eq_dec (n mod 8) 0); rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia; cbn; lia.
Qed.
End PieceVals.

Section B3.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Variable Y : axst.
Definition Y1 : axst := addobj Y O_H.
Definition Y2 : axst := addobj Y1 O_UB.
Definition Y3 : axst := addobj Y2 O_T.
Definition Y4 : axst := addobj Y3 O_L.
Definition Y5 : axst := addobj Y4 O_U.
Definition Y6 : axst := addobj Y5 O_P.
Definition Y7 : axst := addobj Y6 O_R.
Hypothesis SKY : ltac2:(tb__ "0|1|
S0S15S1aS1aS21S21A2S21A2M0A1S46S1cG0S69S25S2eVY;A1A1A4S46S1cG0S69S16S1cS16S1cS17S1cS77S16S1cS45VW;A1S3fA3A3S75A3S17S1cS57S17S1cS59S17S1cS58S17S1cS5aS18S1cA1A3A3A3A3A3A4A3").
Hypothesis YX : ax_X Y = [].
Hypothesis YF : ltac2:(tb__ "0|0|
S72S1eS16S1eS16S1eS16S1eS3eVW;Vst;A2S44S43A1A3S74A3S51A3S24S2eVY;A1A1A3").
Hypothesis WY1 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6bA1A1S14A3").
Hypothesis WY2 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6cA1A1S14A3").
Hypothesis WY3 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6dA1A1S14A3").
Hypothesis WY4 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6eA1A1S14A3").
Hypothesis WY5 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6fA1A1S14A3").
Hypothesis WY6 : ltac2:(tb__ "0|0|
S0S13S1fS2eS70A1A1S14A3").
Hypothesis WY7 : ltac2:(tb__ "0|0|
S0S13S1fS2eS6aA1A1S14A3").
Variable s3 : wsub.
Hypothesis ENT3 : ltac2:(tb__ "0|0|
S0S13S30S6aS4cVW;Vst;Vtmax;A3Vs3;A3S14A3").
Hypothesis SID3 : ltac2:(tb__ "0|0|
S0S13S4aVs3;S78A2S14A3").

Lemma b3_carve : ltac2:(tb__ "0|1|
S33S40S20S15S12Q40M0A1A1S48S20S0S3cVst;S3dA3S0S15S3bA1VW;S18S3bA1A3F_;S67VW;Vst;A2S41R7A1S7aS34R9A1A1S6Z1S64RaS10G0S1dR8PcA2A2A2A2S38Vsegs;S68VW;Vst;RbRaR9A5VY;R6R8R7A6S38Vsegs;S68VW;Vst;RcRbRaA5S4cVW;Vst;Vtmax;A3S49R7Vs3;A2R9R8A6F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc HSEP Hcnt H.
  idtac "b3:0".
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E12' : rw rhoE 12%positive = Z_to_bv 64 nv). { rewrite E12. unfold nv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E155 : rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))). { rewrite <- (Hagw 155%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (YF p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F. cbn [holds eval] in F.
    rewrite E12, u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  idtac "b3:1".
  pose proof (blk_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as BF. cbn zeta in BF.
  destruct BF as (Bx & Bal & Blo & Bhi & Breg & PB & PBS).
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (topG_range (aa_geom A)) as ACV. unfold sep_geom in HSEP. rewrite kSpaceSize_val in HSEP, Breg. destruct HSEP as [SEPT SEPC].
  unfold kUserSpaceSize in Bhi. unfold region_beg, kRegionSize, kFreeArraySize in Blo, Bhi, Breg, PB, PBS.
  set (ab := ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv) in *.
  set (sz := Size (cls_of nv)) in *.

  pose proof (rz_bound nv) as RZB.
  assert (NFIT : nv + rz nv <= sz /\ (nv < 8 -> 8 + rz nv <= sz)).
  { clear -C2 Hnv HN. unfold needed8, round_up in C2.
    pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). split; [|intros]; lia. }
  assert (RZF : 16 <= rz nv <= 1024 /\ rz nv mod 16 = 0).
  { pose proof (HFX (SPUle (SLit 16) (SVar V_RZ)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F1.
    pose proof (HFX (SPUle (SVar V_RZ) (SLit 1024)) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F2.
    pose proof (HFX (SPAlign V_RZ 4) ltac:(apply in_or_app; right; unfold F_gen; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity)) as F3.
    cbn [holds eval] in F1, F2, F3. unfold V_RZ in F1, F2, F3. rewrite E150 in F1, F2, F3. rewrite !u64_lit in F1, F2 by lia.
    destruct F3 as [_ F3]. rewrite u64_lit in F3 by lia. change (2 ^ 4) with 16 in F3. lia. }
  idtac "b3:2".

  assert (PVH : 16 <= sz <= 65536 /\ sz mod 16 = 0) by (clear -C2 C3 C4 NFIT RZB; lia).
  assert (PSB : 17594333495296 <= ag_spacebeg (aa_geom A) /\ ag_spacebeg (aa_geom A) mod 2 ^ 16 = 0) by (clear -G12 G13; lia).
  assert (PTOP : ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv + sz <= 140737479966720) by (clear -Blo Bhi Breg G14 ACV; lia).
  assert (PTOPG : ag_spacebeg (aa_geom A) + cls_of nv * 2 ^ 32 + 16 * chk_of A nv + sz <= topG (aa_geom A)) by (clear -Blo Bhi Breg G14; lia).
  assert (PV : pvals_ok rhoE (ag_spacebeg (aa_geom A)) (cls_of nv) (chk_of A nv) (rz nv) sz nv).
  { unfold pvals_ok. repeat split; try assumption; clear -C1 Hnv HN Bx PVH RZF NFIT PSB PTOP; lia. }
  pose proof (pv_ab rhoE _ _ _ _ _ _ PV) as EB. pose proof (pv_ub rhoE _ _ _ _ _ _ PV) as EUB. pose proof (pv_ue rhoE _ _ _ _ _ _ PV) as EUE.
  pose proof (pv_bsh rhoE _ _ _ _ _ _ PV) as ESH. pose proof (pv_bu rhoE _ _ _ _ _ _ PV) as EBU.
  pose proof (pv_lu rhoE _ _ _ _ _ _ PV) as ELU. pose proof (pv_lp rhoE _ _ _ _ _ _ PV) as ELP.
  pose proof (pv_lr rhoE _ _ _ _ _ _ PV) as [ELR LR0]. pose proof (pv_lt rhoE _ _ _ _ _ _ PV) as ELT.
  pose proof (pv_bp rhoE _ _ _ _ _ _ PV) as EBP. pose proof (pv_br rhoE _ _ _ _ _ _ PV) as EBR.
  pose proof (r8_facts rhoE _ _ _ _ _ _ PV) as (R81 & R82 & R83 & R84).
  cbn zeta in EB, EUB, EUE, ESH, EBU, EBP, EBR, ELR, LR0, R81, R82, R83, R84. fold ab in EB, EUB, EUE, ESH, EBU, EBP, EBR, PTOP.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *.
  set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  assert (LPV : nv / 8 + lp = r8 / 8).
  { clear -R84. unfold lp. rewrite R84. destruct (Z.eq_dec (nv mod 8) 0); rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia; cbn; lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as ND0. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 13) ltac:(lia) ltac:(lia)) as ND1.

  assert (SHB : 17594333495296 <= ag_spacebeg (aa_geom A)) by (clear -G13; lia).
  pose proof (Sh_lt_HSE (ab + sz) ltac:(lia)) as SH1. pose proof (Sh_mono ab (ab + sz) ltac:(lia)) as SH2.
  assert (SHU : Sh (ab + rz nv) = Sh ab + rz nv / 8).
  { clear -RZF Blo SHB. unfold Sh. replace (ab + rz nv) with (ab + rz nv / 16 * 2 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (SH3 : Sh ab + sz / 8 = Sh (ab + sz)).
  { clear -PVH Blo SHB. unfold Sh. replace (ab + sz) with (ab + sz / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (SH0 : 2147450880 <= Sh ab) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos ab 8) as DP8; first [ clear - DP8 Blo SHB; lia | lia ]).
  assert (SZ8 : sz / 8 = rz nv / 8 + r8 / 8 + (sz - rz nv - r8) / 8).
  { clear -PVH RZF R81 LR0.
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)).
    pose proof (Z.div_mod (rz nv) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (rz nv) 8 ltac:(lia)).
    pose proof (Z.div_mod r8 8 ltac:(lia)). pose proof (Z.mod_pos_bound r8 8 ltac:(lia)).
    pose proof (Z.div_mod (sz - rz nv - r8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz - rz nv - r8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 16 ltac:(lia)). pose proof (Z.div_mod (rz nv) 16 ltac:(lia)). lia. }
  pose proof (Z.div_pos (sz - rz nv - r8) 8 ltac:(lia) ltac:(lia)) as LRp.
  unfold HIGH_SHADOW_END in SH1, SHB.
  idtac "b3:3".

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; repeat match goal with |- _ \/ _ => first [ left; reflexivity | right ] end; try reflexivity).
  cbn [map app] in SKY.
  destruct (ss_objs (ax_S Y)) as [|osw orest] eqn:EO; [cbn [map] in SKY; exfalso; clear -SKY; discriminate SKY|].
  cbn [map] in SKY.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) SKY).
  assert (SKrest : map skel orest = map skel (((unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
  { pose proof (f_equal (@tl _) SKY) as X. cbn [tl] in X. rewrite X. rewrite !map_app. cbn [map app]. rewrite <- !app_assoc. reflexivity. }
  destruct (sw_range_gen _ rhoE _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
    pose proof (chain_pre_factsS W st p HW Hp) as Hp'.
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (ECH : soff rhoE choff = 16 + 4 * (cnt_of A nv - 1)).
  { pose proof (pc_entry_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & Hc16 & _).
    assert (E149 : rw rhoE 149%positive = Z_to_bv 64 (cnt_of A nv)). { rewrite <- (Hagw 149%positive) by (unfold GW; lia). reflexivity. }

    unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear -Hcnt Hc16 C4; lia).
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by (clear; lia); rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia); clear; lia).
    change (2 mod 64) with 2. rewrite ?u64_lit by (clear -Hcnt Hc16 C4; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 2)) by (clear -Hcnt Hc16 C4; lia). rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia).
    unfold snorm. rewrite Z.mod_small by (clear -Hcnt Hc16 C4; lia). destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)) as [LT63|GE63]; [clear; lia | clear -Hcnt Hc16 GE63; lia]. }
  idtac "b3:4".

  assert (DISJ : forall lo' hi',
            (ag_spacebeg (aa_geom A) <= lo' /\ hi' <= ag_spacebeg (aa_geom A) + 2 ^ 37 + 4096)
            \/ (2147450880 <= lo' /\ hi' <= 17594333495296) ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) (ss_objs (ax_S Y))).
  { pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, CB, TI, CI.
    intros lo' hi' HR'. rewrite EO. constructor.
    - clear -SW0 G14 G24 HR' PTOPG. unfold ranges_disjoint. cbn [fst snd]. idtac "disj:sw". lia.
    - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo', hi')) orest _ SKrest).
      apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split|]|].
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B G13 G14 G24 HR'. idtac "disj:lnk". lia.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite ?u64_lit by (clear; lia); clear -SHB HR'; idtac "disj:glob"; lia.
      + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
               O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
        unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (clear; lia); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (clear -G5 G6 G8 G9 G24; lia);
          idtac "disj:rt"; first [ clear -SHB HR'; lia | clear -SHB HR' SEPT G5 G6 G24 TB; lia | clear -SHB HR' SEPC G8 G9 G24 CB; lia ].
      + assert (EPB : bv_unsigned (eval rhoE pc_base) = ag_thread (aa_geom A) + 208 + cls_of nv * 80).
        { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 G24; lia).
          rewrite (Z.mod_small (cls_of nv * 80)) by (clear -C1; lia). rewrite (Z.mod_small (ag_thread (aa_geom A) + 208)) by (clear -G5 G6 G24; lia). rewrite Z.mod_small by (clear -C1 G5 G6 G24; lia). reflexivity. }
        unfold O_pcc, O_pcs, O_pck, O_st, vT. repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd]. rewrite EPB. clear -SHB HR' SEPT G5 C1 TB. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd]. rewrite EPB. clear -SHB HR' SEPT G5 C1 TB. lia.
        * unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite ECH, EPB. rewrite soff_lit_small by (clear -Hcnt; lia). clear -SHB HR' SEPT G5 C1 Hcnt TB. lia.
        * rewrite obj_range_mk by (clear; lia). cbn [fst snd eval]. rewrite E151, u64_lit by (clear -G5 G6 G24; lia). clear -SHB HR' SEPT G5 TB. lia. }
  idtac "b3:5".

  assert (PRB : forall a, ab <= a < ab + sz -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y).
  { intros a Ha. destruct (PB a ltac:(clear -Ha; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Ha SHB Blo PTOP ACV; lia).
    exact (wok_rd_off_image (rm rhoE) a b ltac:(clear -Ha SHB Blo PTOP ACV; lia) Hb). }
  assert (PRS : forall a, Sh ab <= a < Sh ab + sz / 8 -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y).
  { intros a Ha. destruct (PBS a ltac:(clear -Ha; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Ha SH0 SH1 SH2 SH3; lia).
    exact (wok_rd_off_image (rm rhoE) a b ltac:(clear -Ha SH0 SH1 SH2 SH3; lia) Hb). }

  assert (L0 : soff rhoE (SLit 0) = 0) by (apply soff_lit_small; lia).
  pose proof (soff_of_val rhoE (SVar V_RZ) (rz nv) ltac:(unfold V_RZ; cbn [eval]; rewrite E150; apply u64_lit; first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OH.
  pose proof (soff_of_val rhoE (SVar 12) nv ltac:(cbn [eval]; rewrite E12'; apply u64_lit; first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OUB.
  pose proof (soff_of_val rhoE LTe _ ELT ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OT.
  pose proof (soff_of_val rhoE LLe (rz nv / 8) ltac:(unfold LLe, V_RZ; cbn [eval]; rewrite srl_val, E150, u64_lit by (first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]); change (3 mod 64) with 3; rewrite Z.shiftr_div_pow2 by (first [ clear - RZF Hnv HN NFIT PVH; lia | lia ]); reflexivity) ltac:(first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OL.
  pose proof (soff_of_val rhoE LUe _ ELU ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OU.
  pose proof (soff_of_val rhoE LPe _ ELP ltac:(unfold lp; destruct (Z.eq_dec (nv mod 8) 0); first [ clear - RZF Hnv HN NFIT PVH; lia | lia ])) as OP.
  pose proof (soff_of_val rhoE LRe _ ELR ltac:(first [ clear - NFIT PVH RZF Hnv HN LR0 R81 R82 R83 R84; lia | lia ])) as OR.
  fold lp in OP.
  idtac "b3:6".

  assert (STEP : forall (Z0 : axst) (o : sobj) (b lo hi : Z),
     SPA segs (JG W st A Kc rho) Z0 rhoE tp w ->
     swf (ax_S (addobj Z0 o)) = true -> ss_next (ax_S Z0) = ss_next (ax_S Y) -> ax_X Z0 = [] ->
     ob_cells o = [] -> ob_dflt o = DUnknown ->
     bv_unsigned (eval rhoE (ob_base o)) = b -> soff rhoE (ob_lo o) = lo -> soff rhoE (ob_hi o) = hi ->
     lo <= hi -> hi - lo < 2 ^ 63 -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
     Forall (fun o' => ranges_disjoint (obj_range rhoE o') (b + lo, b + hi)) (ss_objs (ax_S Z0)) ->
     (forall a, b + lo <= a < b + hi -> wok_of segs (rm rhoE) (Z_to_bv 64 a) = true /\ exists y, rd_of segs (rm rhoE) (Z_to_bv 64 a) = Some y) ->
     SPA segs (JG W st A Kc rho) (addobj Z0 o) rhoE tp w).
  { intros Z0 o b lo hi HZ Wo NXo Xo Co Do Eb Elo Ehi I1 I2 I3 I4 Dj Pr.
    destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *. subst ocs od.
    unfold addobj.
    apply (SPA_carve_unk segs (JG W st A Kc rho) rhoE Z0 tp w ob olo ohi (ss_next (ax_S Z0)) HZ Wo (Pos.le_refl _));
      rewrite ?Eb, ?Elo, ?Ehi; try assumption.
    unfold xwords_clear. rewrite Xo. intros rr y j []. }
  assert (XA : forall Z0 o, ax_X (addobj Z0 o) = ax_X Z0) by (intros; reflexivity).
  assert (NA : forall Z0 o, ss_next (ax_S (addobj Z0 o)) = ss_next (ax_S Z0)) by (intros; reflexivity).
  assert (OA : forall Z0 o, ss_objs (ax_S (addobj Z0 o)) = ss_objs (ax_S Z0) ++ [o]) by (intros; reflexivity).

  assert (DJ : forall lo' hi' (extra : list sobj),
            ((ag_spacebeg (aa_geom A) <= lo' /\ hi' <= ag_spacebeg (aa_geom A) + 2 ^ 37 + 4096) \/ (2147450880 <= lo' /\ hi' <= 17594333495296)) ->
            Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) extra ->
            forall objs, objs = ss_objs (ax_S Y) ++ extra -> Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo', hi')) objs).
  { intros lo' hi' extra HR' Hx objs ->. apply Forall_app. split; [apply DISJ; exact HR' | exact Hx]. }
  assert (RH : obj_range rhoE O_H = (ab, ab + rz nv)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_H; cbn [ob_base ob_lo ob_hi]; rewrite EB, L0, OH; f_equal; lia).
  assert (RUB : obj_range rhoE O_UB = (ab + rz nv, ab + rz nv + nv)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_UB; cbn [ob_base ob_lo ob_hi]; rewrite EUB, L0, OUB; f_equal; lia).
  assert (RT : obj_range rhoE O_T = (ab + rz nv + nv, ab + sz)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_T; cbn [ob_base ob_lo ob_hi]; rewrite EUE, L0, OT; f_equal; lia).
  assert (RL : obj_range rhoE O_L = (Sh ab, Sh ab + rz nv / 8)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_L; cbn [ob_base ob_lo ob_hi]; rewrite ESH, L0, OL; f_equal; lia).
  assert (RU : obj_range rhoE O_U = (Sh ab + rz nv / 8, Sh ab + rz nv / 8 + nv / 8)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_U; cbn [ob_base ob_lo ob_hi]; rewrite EBU, L0, OU, SHU; f_equal; lia).
  assert (RP : obj_range rhoE O_P = (Sh ab + rz nv / 8 + nv / 8, Sh ab + rz nv / 8 + nv / 8 + lp)) by (unfold obj_range, obj_lo_of, obj_hi_of, O_P; cbn [ob_base ob_lo ob_hi]; rewrite EBP, L0, OP, SHU; f_equal; lia).
  idtac "b3:7".

  assert (H1 : SPA segs (JG W st A Kc rho) Y1 rhoE tp w).
  { apply (STEP Y O_H ab 0 (rz nv) H WY1 eq_refl YX eq_refl eq_refl EB L0 OH); try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply DISJ. left. clear -RZF Blo Bhi Breg NFIT; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H2 : SPA segs (JG W st A Kc rho) Y2 rhoE tp w).
  { apply (STEP Y1 O_UB (ab + rz nv) 0 nv H1 WY2 (NA _ _) (eq_trans (XA _ _) YX) eq_refl eq_refl EUB L0 OUB); try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H]); [left; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | apply OA].
      constructor; [|constructor]. rewrite RH. unfold ranges_disjoint; cbn [fst snd]. clear -RZF; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H3 : SPA segs (JG W st A Kc rho) Y3 rhoE tp w).
  { apply (STEP Y2 O_T (ab + rz nv + nv) 0 (sz - rz nv - nv) H2 WY3 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)) eq_refl eq_refl EUE L0 OT);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB]); [left; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRB. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:8".

  assert (H4 : SPA segs (JG W st A Kc rho) Y4 rhoE tp w).
  { apply (STEP Y3 O_L (Sh ab) 0 (rz nv / 8) H3 WY4 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX))) eq_refl eq_refl ESH L0 OL);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H5 : SPA segs (JG W st A Kc rho) Y5 rhoE tp w).
  { apply (STEP Y4 O_U (Sh ab + rz nv / 8) 0 (nv / 8) H4 WY5 (NA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)))) eq_refl eq_refl
             ltac:(cbn [ob_base O_U]; rewrite EBU, SHU; reflexivity) L0 OU);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L]); [right; unfold lp in LPV; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. unfold lp in LPV; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:9".

  assert (H6 : SPA segs (JG W st A Kc rho) Y6 rhoE tp w).
  { apply (STEP Y5 O_P (Sh ab + rz nv / 8 + nv / 8) 0 lp H5 WY6 (NA _ _)
             (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX))))) eq_refl eq_refl
             ltac:(cbn [ob_base O_P]; rewrite EBP, SHU; reflexivity) L0 OP);
      try (unfold lp in *; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L; O_U]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL, ?RU; unfold ranges_disjoint; cbn [fst snd]; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }

  assert (H7 : SPA segs (JG W st A Kc rho) Y7 rhoE tp w).
  { apply (STEP Y6 O_R (Sh ab + rz nv / 8 + r8 / 8) 0 ((sz - rz nv - r8) / 8) H6 WY7 (NA _ _)
             (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) (eq_trans (XA _ _) YX)))))) eq_refl eq_refl
             ltac:(cbn [ob_base O_R]; rewrite EBR, SHU; reflexivity) L0 OR);
      try (clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia).
    - apply (DJ _ _ [O_H; O_UB; O_T; O_L; O_U; O_P]); [right; clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia | | unfold Y6, Y5, Y4, Y3, Y2, Y1, addobj; cbn [ax_S ax_setS ss_objs]; rewrite <- ?app_assoc; reflexivity].
      repeat apply Forall_cons; try apply Forall_nil; rewrite ?RH, ?RUB, ?RT, ?RL, ?RU, ?RP; unfold ranges_disjoint; cbn [fst snd];
        unfold lp in *; destruct (Z.eq_dec (nv mod 8) 0); clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0; lia.
    - intros a Ha. apply PRS. clear -RZF Blo Bhi Breg PTOP ACV SHB NFIT PVH HN Hnv SH0 SH1 SH2 SH3 SZ8 LRp R81 R82 R83 ND0 ND1 LPV LR0 Ha; lia. }
  idtac "b3:10".

  apply (SPA_entails0 segs (JG W st A Kc rho) GW Y7 (CertMallocSP.C3 W st tmax) s3 rhoE tp w ENT3 SID3); [|exact H7].
  apply stableA_withG; [intros r1 r2 Hg Hag; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
Qed.
End B3.
