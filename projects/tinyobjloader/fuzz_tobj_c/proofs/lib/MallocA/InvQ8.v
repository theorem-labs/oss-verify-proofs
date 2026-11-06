(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "mul"; "modulo"; "@Corelib.Init.Logic"; "and"; "or"; "not"; "eq"; "ex"; "iff"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_geom"; "sc_map_beg"; "AA"; "aa_sec"; "ag_spacebeg"; "sc_map_size"; "ag_pab"; "aa_live"; "ag_ctx"; "ag_thread"; "cs_allocated_user"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "bool"; "false"; "list"; "nat"; "option"; "None"; "Some"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kPtrArrayReserve"; "PG"; "is_primary"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QRD"; "sec_held"; "same_but_qcs"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8.Client"; "sec_dyn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "QRD_IMG"; "@Stdlib.Lists.List"; "In"; "Exists"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "client_shadowA"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "SEC_INST"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3"; "QT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QRD_img (a : Z) : Prop := ltac2:(tb__ "0|0|
S9S8S1S2S3fZ40A2Va;A2S3Va;S2S3fZc0A2A2A2S9S8S1Zeddb8Va;A2S3Va;Zeddd1A2A2S9S8S1Ze9af0Va;A2S3Va;Ze9af8A2A2S9S8S1Zf0c5cVa;A2S3Va;Zf0c68A2A2S9S8S1Z624560Va;A2S3Va;Z624568A2A2S9S8S1Z645960Va;A2S3Va;Z645968A2A2S9S8S1Zf20d8Va;A2S3Va;Zf20daA2A2S9S8S1Zf20e0Va;A2S3Va;Zf20fcA2A2S9S8S1S40Va;A2S3Va;Zee070A2A2S9S8S1Z182fa0Va;A2S3Va;Z182fa8A2A2S9S8S1Z182fb8Va;A2S3Va;Z182fc0A2A2S9S8S1Z180ea0Va;A2S3Va;Z180ea8A2A2S8S1Z18302cVa;A2S3Va;Z18302dA2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition QRD_IMG : list (Z * Z) := ltac2:(tb__ "0|2|
S1cS1dS0S0A2M0S1bS0S0S2S3fZ40A2Z80A4S1cG0S1bS0S0Zeddb8Z19A4S1cG0S1bS0S0Ze9af0Z8M1A4S1cG0S1bS0S0Zf0c5cZcA4S1cG0S1bS0S0Z624560G1A4S1cG0S1bS0S0Z645960G1A4S1cG0S1bS0S0Zf20d8Z2A4S1cG0S1bS0S0Zf20e0Z1cA4S1cG0S1bS0S0S40S5Zee070S40A2A4S1cG0S1bS0S0Z182fa0G1A4S1cG0S1bS0S0Z182fb8G1A4S1cG0S1bS0S0Z180ea0G1A4S1cG0S1bS0S0Z18302cZ1A4S25G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma QRD_img_ranges : ltac2:(tb__ "0|0|
S0S35R1A1S34S36R2A2F_;Fa;").
Proof.
  intros a H. unfold QRD_img in H. unfold in_rangesZ, QRD_IMG.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - exists (QG + 64), 128. split; [cbn; tauto | lia].
  - exists 0xeddb8, 25. split; [cbn; tauto | lia].
  - exists 0xe9af0, 8. split; [cbn; tauto | lia].
  - exists 0xf0c5c, 12. split; [cbn; tauto | lia].
  - exists 0x624560, 8. split; [cbn; tauto | lia].
  - exists 0x645960, 8. split; [cbn; tauto | lia].
  - exists 0xf20d8, 2. split; [cbn; tauto | lia].
  - exists 0xf20e0, 28. split; [cbn; tauto | lia].
  - exists SEC_INST, (0xee070 - SEC_INST). split; [cbn; tauto | lia].
  - exists 0x182fa0, 8. split; [cbn; tauto | lia].
  - exists 0x182fb8, 8. split; [cbn; tauto | lia].
  - exists 0x180ea0, 8. split; [cbn; tauto | lia].
  - exists 0x18302c, 1. split; [cbn; tauto | lia].
Qed.
Lemma HCSTQ_of_apart : ltac2:(tb__ "0|0|
S20S1dS0S0A2A1S0S34R2R1A2S34S36R2A2SeF_;F_;Fa;S0S34R3R1A2SaS35R2A1A1F_;Fa;F_;FCST;").
Proof. intros CST H a Ha HQ. exact (H a Ha (QRD_img_ranges a HQ)). Qed.

Section Client.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S34VCST;R1A2SaS35R2A1A1F_;Fa;").
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S8S1Z1R1A2S1R1Z1eA2A2S8S1Z0S1aS32VA;R2A2A1M0A2S1G0S2eA2A2F_;Fc;").
Variables (mq mf : bview).
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr mq A.
Hypothesis HSR : secondary_repr mq A.
Hypothesis HF : fs_inv mf A.
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Tq := (ag_thread (aa_geom A)).
Local Abbreviation Cq := (ag_ctx (aa_geom A)).
Local Abbreviation Fq := (ag_fsb (aa_geom A)).

Local Abbreviation Pq := (ag_pab (aa_geom A)).

Definition sec_dyn (z : Z) : Prop := ltac2:(tb__ "0|5|
S9S8S1S16S10VA;A1A1M0Vz;A2S3Vz;S2G0S27A2A2A2S9S38SfSfS8S1S11R1A1M1Vz;A2M2S3Vz;S2G1Z20A2A2A2Lch;S13VA;A1M3A3S38SfSfS8S30VA;R1A2S9S8G2S3Vz;S2G1S15R1A1A2M4A2A2S8S1S26G1A1Vz;A2S3Vz;S26G4A1A2A2A2A2Lch;G3A3A2A2").
Lemma sec_dyn_QRD : ltac2:(tb__ "0|0|
S0S33R1A1S2fVA;R2A2F_;Fz;").
Proof. intros z H. left. do 3 right. right. exact H. Qed.

Lemma QRD_cases : ltac2:(tb__ "0|a|
S0S2fVA;R1A2S9S45VA;R2A2S9S8S1S2S14S10VA;A1M0A1M1S4Z2M2Z25A2A2M3R2A2S3R2S2G3Z1000A2A2A2S9ScS0S0S8S8S1Z1R1A2S1R1Z1eA2A2M4S8S1S2S2G1S6R1S4G2Z20A2M5A2A2M6S5G5S4G2Z1dA2A2A2M7R3A2S3R3S2G6G5A2M8A2A2A2Lc;A2S9ScS0S0S8G4S8S1S26G7A1R3A2S3R3S26G8A1A2A2A2Lc;A2S9S35R2A1S9S8S1S2S18G0A1M9Z98A2R2A2S3R2S2G9Za0A2A2A2S33R2A1A2A2A2A2A2A2F_;Fz;").
Proof.
  intros z [[HQ|[HQ|[(c & Hc & HQ)|HS]]]|[HQ|HQ]].
  - left. left. exact HQ.
  - left. right. clear -HQ. lia.
  - unfold region_info, free_array, region_beg, kRegionInfoStride, kFreeArraySize in HQ. rewrite kSpaceSize_val, kUserSpaceSize_val in HQ. unfold kRegionSize in HQ.
    destruct HQ as [HQ|[HQ|HQ]].
    + right; left. clear -HQ Hc. lia.
    + right; right; left. exists c. split; [exact Hc|]. clear -HQ. lia.
    + right; right; right; left. exists c. split; [exact Hc|].
      replace (SBq + c * 2 ^ 32 + 2 ^ 32) with (SBq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + 2 ^ 29) by lia. exact HQ.
  -
    destruct HS as [HS|HS]; [do 4 right; left; unfold QRD_img; do 8 right; left; exact HS | do 6 right; exact HS].
  - unfold qrtc_zone in HQ. unfold QRD_img.
    destruct HQ as [HQ|[HQ|[HQ|[HQ|[HQ|[HQ|[HQ|[HQ|[HQ|[HQ|[HQ|HQ]]]]]]]]]]];
      first [ do 5 right; left; exact HQ | do 4 right; left; unfold QG, SEC_INST in *; clear -HQ; lia ].
  - unfold qrtc2_zone in HQ. do 4 right; left. unfold QRD_img. clear -HQ. lia.
Qed.

Lemma sec_dyn_out : ltac2:(tb__ "0|2|
S0S0S0S8S1R3R1A2S3R1R2A2A2S9S1R3S16S10VA;A1A1M0A2S1S2G0S27A2R4A2A2SfS37SfR1S13VA;A1A3S9S9S1R6S11R2A1M1A2S1S2G1S15R2A1A2R7A2A2S8S1S2G1Z20A2R7A2SaS30VA;R2A2A1A2A2F_;Fch;S9S1R5Z7fff7000A2S1Z10007fff8000R6A2A2SaS33R5A1A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz OP OCH OB [HS|[HS|HS]].
  - clear -Hz OP HS. lia.
  - apply Exists_exists in HS as (ch & Hch & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & _).
    destruct (OCH ch Hch) as [O|[O _]]; unfold PG in *; clear -Hz HS O D8 D9; lia.
  - apply Exists_exists in HS as (ch & Hch & HH & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (OCH ch Hch) as [O|[_ O]]; [|exact (O HH)].
    destruct HS as [HS|HS]; [clear -Hz HS O; lia|].
    pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (_ & _ & _ & _ & _ & _ & _ & _ & TG).
    destruct D10 as (E1 & E2 & _).
    pose proof (Sh_in_band (sc_map_beg ch) ltac:(clear -E1 E2 D12 TG; lia)) as B1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(clear -E1 E2 D12 TG; lia)) as B2.
    unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -Hz OB HS B1 B2. lia.
Qed.

Lemma QRD_out : ltac2:(tb__ "0|7|
S0S0S0S8S1R3R1A2S3R1R2A2A2S9S1R3S14S10VA;A1M0A1M1A2S1S2S2G1S4Z2Z25A2A2Z1000M2A2R4A2A2S9S1R4S19G0A1M3A2S1S2G3G2A2R5A2A2S9S1R5S18G0A1M4A2S1S2G4G2A2R6A2A2S9S1R6Z7fff7000A2S1Z10007fff8000R7A2A2S9S1R7S2bA2S1S2aR8A2A2S9S1R8S16G0A1M5A2S1S2G5S27A2R9A2A2SfS37SfR1S13VA;A1A3S9S9S1RbS11R2A1M6A2S1S2G6S15R2A1A2RcA2A2S8S1S2G6Z20A2RcA2SaS30VA;R2A2A1A2A2F_;Fch;SaS2fVA;R9A2A1F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz OS OT OC OB OI OP OCH HQ. pose proof HI3 as (H3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct (QRD_cases z HQ) as [Q|[Q|[(c & Hc & Q)|[(c & Hc & Q)|[Q|[Q|Q]]]]]].
  - exact (QT_out A HG H3 HQP HAU lo hi z Hz OS OT OB OI Q).
  - clear -Hz OS Q. lia.
  - clear -Hz OS Q Hc. lia.
  - pose proof (Sh_in_band (SBq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) ltac:(clear -Hc S1 S2 TG; lia)) as B1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (SBq + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -Hc S1 S2 TG; lia)) as B2.
    unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -Hz OB Q B1 B2. lia.
  - unfold QRD_img, QG, SEC_INST, IMG_LO, IMG_HI in *. clear -Hz OI Q. lia.
  - clear -Hz OC Q. lia.
  - exact (sec_dyn_out lo hi z Hz OP OCH OB Q).
Qed.

Lemma live_user_where : ltac2:(tb__ "0|5|
S0S0S0S37S1dS0S0A2S1bS0S0R3R2A4S17VA;A1A3S8S1R4R2A2S3R2S2R4R3A2A2A2S9ScS0S0S8S8S1Z1R1A2S1R1Z1eA2A2S8S1S2S14S10VA;A1A1S6R1S4Z2M0Z20A2M1A2A2M2R4A2S3R4S2G2S5G1S4G0Z1dA2A2A2A2A2A2Lc;A2ScS21S21ScSfSfS8SbS22SfA1S39SfS13VA;A1R2A3S24SfR1A2A3S8S8S1S11R1A1M3R5A2S3R5S2G3S15R1A1A2M4A2A2S8SbS1eS29R6A1S1fA3S8SbS0R7S2S2G3S28A2Z800A2A3S1S2R7R6A2G4A2A2A2A2A2Lch;A2Li;A2A2F_;F_;Fa;Fn;Fb;").
Proof.
  intros b n a Hin Ha. pose proof HI3 as (H3 & _). destruct (is_primary n) eqn:HP.
  - left. pose proof (live_prim_czone A HG H3 mq HLS HPR b n Hin HP) as L. cbv zeta in L. destruct L as (C1 & O0 & OM & OE & _ & (RN & RZ & N1) & _).
    exists (ClassID (needed n)). split; [exact C1|]. clear -Ha O0 OE RN RZ N1. lia.
  - right. destruct (live_sec_map A mq HLS HSR HI3 b n Hin HP) as (i & ch & Hi & Eb & RZ & N1 & BN & MP & MS0 & DI).
    exists i, ch. split; [exact Hi|]. split; [unfold PG in *; clear -Ha Eb BN; lia|]. split; [reflexivity|]. split; [exact Eb|]. clear -BN. lia.
Qed.

Lemma live_sec_not_held : ltac2:(tb__ "0|0|
S0S0SfS37S1dS0S0A2S1bS0S0R3R2A4S17VA;A1A3SbS1eS29R3A1S1fA3SbS0R5S2S2S11R3A1S28A2Z800A2A3SaS30VA;R4A2A1F_;F_;F_;Fch;Fn;Fb;").
Proof.
  intros b n ch Hin HP Eb (it & Hit & HPi & Eit).
  pose proof HI3 as (_ & _ & _ & _ & _ & ND & _).
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & HD & _).
  apply (HD b).
  - apply (proj2 (list_elem_of_In _ _)). apply in_map_iff. exists (b, n). split; [reflexivity|]. apply filter_In. split; [exact Hin|]. cbn. rewrite HP. reflexivity.
  - apply (proj2 (list_elem_of_In _ _)). apply in_map_iff. exists it. split; [rewrite Eit, Eb; reflexivity|]. apply filter_In. split; [exact Hit|]. rewrite HPi. reflexivity.
Qed.

Theorem client_not_QRD : ltac2:(tb__ "0|0|
S0S3cVCST;VA;R1A3SaS2fVA;R2A2A1F_;Fa;").
Proof.
  intros a Hcl HQ. pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & (TC & SC & CB & CI) & _).
  pose proof (geom_numsS _ HG) as (_ & _ & F2 & _ & _ & _ & _ & _ & _ & _ & FC & _).
  destruct (client_addr_cases CST A a mf HF Hcl) as [S|[L|[FR|[C|FL]]]].
  -   pose proof (QRD_lt_top A HG HI3 HQP HAU mq HSR a HQ) as H. clear -S H. lia.
  -   destruct L as (b & n & Hin & Ha).
    destruct (QRD_cases a HQ) as [Q|Q].
    { revert Q. apply (live_not_QT A HG H3 HQP HAU mq HLS HPR HSR HI3 b n a Hin). left. pose proof (rz_bound n). clear -Ha H. lia. }
    destruct (live_user_where b n a Hin Ha) as [(c & Hc & W)|(i & ch & Hi & W & HP & Eb & BN)].
    + destruct Q as [Q|[(c' & Hc' & Q)|[(c' & Hc' & Q)|[Q|[Q|Q]]]]].
      * clear -W Q Hc. lia.
      * clear -W Q Hc Hc'. lia.
      * pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (SBq + c' * 2 ^ 32 + 2 ^ 32) ltac:(clear -Hc' S1 S2 TG; lia)) as B2. unfold HIGH_SHADOW_END in B2. clear -W Q Hc S1 B2. lia.
      * unfold QRD_img, QG, SEC_INST in Q. clear -W Q Hc S1. lia.
      * clear -W Q Hc SC. lia.
      *
        revert Q. apply (sec_dyn_out (SBq + c * 2 ^ 32) (SBq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) a W).
        -- pose proof H3 as (_ & _ & _ & SP & _). rewrite kSpaceSize_val in SP. clear -SP Hc. lia.
        -- intros ch Hch. left. destruct (In_nth_error _ _ Hch) as [j Hj]. destruct (SEC3 j ch Hj) as (X1 & _). rewrite kSpaceSize_val in X1. clear -X1 Hc. lia.
        -- clear -S1 Hc. lia.
    + revert HQ. pose proof HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
      destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & _ & XJ & X6 & _). rewrite kSpaceSize_val in X1.
      destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
      assert (B0 : sc_map_beg ch + 32 <= b) by (unfold PG in Eb; clear -Eb; lia).
      apply (QRD_out b (b + n) a Ha); [clear -X1 B0 BN; lia | clear -X2 B0 BN; lia | clear -X6 B0 BN; lia | clear -E5 B0 BN; lia | clear -E4 B0 BN; lia | clear -X3 B0 BN; lia |].
      intros ch' Hch'. destruct (In_nth_error _ _ Hch') as [j Hj]. destruct (Nat.eq_dec i j) as [EJ|NE].
      * subst j. rewrite Hi in Hj. injection Hj as <-. right. split; [exact B0 | exact (live_sec_not_held b n ch Hin HP Eb)].
      * left. pose proof (XJ j ch' Hj NE) as O. clear -O B0 BN. lia.
  -   destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. revert HQ.
    apply (QRD_out Fq (Fq + 11571200) a); [clear -Hx M; lia | exact FS | exact FT | clear -FC; lia | exact FB | unfold IMG_LO, IMG_HI; clear -F1; lia | |].
    + pose proof H3 as (_ & _ & _ & _ & _ & SPF & _). rewrite FS_total_val in SPF. clear -SPF. lia.
    + intros ch Hch. left. destruct (In_nth_error _ _ Hch) as [j Hj]. destruct (SEC3 j ch Hj) as (_ & _ & _ & X4 & _). rewrite FS_total_val in X4. clear -X4. lia.
  -   destruct (HCST _ C) as [X _].
    destruct (QRD_cases a HQ) as [Q|[Q|[(c' & Hc' & Q)|[(c' & Hc' & Q)|[Q|[Q|Q]]]]]].
    + destruct (Z_lt_dec a (QG + 152)) as [L|L]; [|destruct (Z_lt_dec a (QG + 192)) as [L2|L2]].
      * revert Q. apply (QT_img A HG H3 HQP HAU a X). clear -L. lia.
      * apply (HCSTQ a C). left. clear -L L2. lia.
      * revert Q. apply (QT_img A HG H3 HQP HAU a X). clear -L2. lia.
    + unfold IMG_LO, IMG_HI in X. clear -X Q S1. lia.
    + unfold IMG_LO, IMG_HI in X. clear -X Q S1 Hc'. lia.
    + pose proof (Sh_in_band (SBq + c' * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) ltac:(clear -Hc' S1 S2 TG; lia)) as B1.
      unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_LO, IMG_HI in *. clear -X Q B1. lia.
    + exact (HCSTQ a C Q).
    + unfold IMG_LO, IMG_HI in X. clear -X Q CI. lia.
    +
      revert Q. pose proof HSR as (HS1 & _ & _ & _ & PD & _).
      apply (sec_dyn_out a (a + 1) a ltac:(clear; lia)).
      * pose proof (dyn_ok_big _ _ _ PD ltac:(unfold kPtrArrayReserve; clear; lia)) as PB. clear -PB X. lia.
      * intros ch Hch. left. destruct (In_nth_error _ _ Hch) as [j Hj]. destruct (HS1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
        pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; clear -D8 D9; lia)) as PB. clear -PB X. lia.
      * unfold IMG_LO, IMG_HI in X. clear -X. lia.
  -   destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. revert HQ.
    apply (QRD_out Fq (Fq + 11571200) (fs_flags Fq c + p)); [clear -M; lia | exact FS | exact FT | clear -FC; lia | exact FB | unfold IMG_LO, IMG_HI; clear -F1; lia | |].
    + pose proof H3 as (_ & _ & _ & _ & _ & SPF & _). rewrite FS_total_val in SPF. clear -SPF. lia.
    + intros ch Hch. left. destruct (In_nth_error _ _ Hch) as [j Hj]. destruct (SEC3 j ch Hj) as (_ & _ & _ & X4 & _). rewrite FS_total_val in X4. clear -X4. lia.
Qed.

Lemma Sh_lt_aligned : ltac2:(tb__ "0|0|
S0S0SbS0S7R1Z8A2Z0A3S3R3R2A2S3S26R4A1S26R3A1A2F_;F_;Fy;Fx;").
Proof.
  intros x y Hy Hxy. unfold Sh. destruct (proj1 (Z.mod_divide y 8 ltac:(lia)) Hy) as [k Hk]. subst y. rewrite Z.div_mul by lia.
  assert (x / 8 < k) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma QRD_band : ltac2:(tb__ "0|1|
S0S2fVA;R1A2S8S1Z7fff7000R2A2S3R2Z10007fff8000A2A2S9S8S1S26S14S10VA;A1A1M0A1R3A2S3R3S26S2G0S4Z2Z25A2A2A1A2A2S33R3A1A2F_;F_;Fz;").
Proof.
  intros z HQ HB. pose proof HI3 as (H3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  pose proof (geoQ2 A HG H3) as (_ & (TC & SC & CB & CI) & _).
  destruct (QRD_cases z HQ) as [Q|[Q|[(c & Hc & Q)|[(c & Hc & Q)|[Q|[Q|Q]]]]]]; [left | left | left | left | left | left | right; exact Q].
  - pose proof (QT_num A HG H3 HQP HAU z Q) as W. unfold QG in W. destruct W as [W|[[W _]|[W|[W|W]]]]; first [exact W | clear -W HB S1 TB; lia].
  - clear -Q HB S1. lia.
  - clear -Q HB S1 Hc. lia.
  - pose proof (Geometry.Sh_mono SBq (SBq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) ltac:(clear -Hc; lia)) as M1.
    pose proof (Geometry.Sh_mono (SBq + c * 2 ^ 32 + 2 ^ 32) (SBq + 2 ^ 37) ltac:(clear -Hc; lia)) as M2. clear -Q M1 M2. lia.
  - unfold QRD_img, QG, SEC_INST in Q. clear -Q HB. lia.
  - clear -Q HB CB. lia.
Qed.

Lemma sec_dyn_sh : ltac2:(tb__ "0|1|
S0S8S1Z0R1A2S3R1S4Z2Z2fA2A2A2S33S26R2A1A1ScSfSfS8S37SfR1S13VA;A1A3S8S30VA;R1A2S8S1S11R1A1M0R4A2S3R4S2G0S15R1A1A2A2A2A2A2Lch;A2F_;F_;Fx;").
Proof.
  intros x Hx SD.
  pose proof (Sh_in_band x Hx) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  pose proof HSR as (HS1 & _ & _ & _ & (_ & PD) & _).
  destruct SD as [HS|[HS|HS]].
  - exfalso. destruct PD as (P1 & P2 & P3 & P4 & P5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P5. clear -HS B P5. lia.
  - exfalso. apply Exists_exists in HS as (ch & Hch & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _). destruct D10 as (E1 & E2 & E3 & E4 & E5).
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, PG in *. clear -HS B E5 D8 D9. lia.
  - apply Exists_exists in HS as (ch & Hch & HH & HS). exists ch. split; [exact Hch|]. split; [exact HH|].
    destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _). destruct D10 as (E1 & E2 & E3 & E4 & E5).
    destruct HS as [HS|HS].
    + exfalso. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -HS B E5. lia.
    + assert (M8 : sc_map_beg ch mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (sc_map_beg ch) PG ltac:(unfold PG; lia)) D6) as [k Hk]. rewrite Hk. unfold PG.
        replace (k * 4096) with (k * 512 * 8) by lia. apply Z_mod_mult. }
      destruct (Z_lt_dec x (sc_map_beg ch)) as [L|L]; [pose proof (Sh_lt_aligned x _ M8 L) as H; exfalso; clear -HS H; lia|].
      destruct (Z_le_dec (sc_map_beg ch + sc_map_size ch) x) as [L2|L2]; [pose proof (Geometry.Sh_mono _ _ L2) as H; exfalso; clear -HS H; lia|].
      clear -L L2. lia.
Qed.

Lemma sh_off_space : ltac2:(tb__ "0|2|
S0S8S1Z0R1A2S3R1S4Z2M0Z2fA2A2A2S9S3R2S14S10VA;A1A1M1A2S1S2G1S4G0Z25A2A2R2A2A2SaS33S26R3A1A1A1SaS2fVA;S26R4A1A2A1F_;F_;F_;Fx;").
Proof.
  intros x Hx OS NSD HQ. pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & _).
  pose proof (Sh_in_band x Hx) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  destruct (QRD_band (Sh x) HQ ltac:(clear -B; lia)) as [W|W]; [|exact (NSD W)].
  destruct OS as [O|O].
  - pose proof (Sh_lt_aligned x SBq S8 O). clear -W H. lia.
  - pose proof (Geometry.Sh_mono (SBq + 2 ^ 37) x O). clear -W H. lia.
Qed.

Theorem cshadow_not_QRD : ltac2:(tb__ "0|0|
S0S3dVCST;VXGL;VA;R1A4SaS2fVA;R2A2A1F_;Fa;").
Proof.
  intros a Hcs HQ. pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  pose proof (geoQ2 A HG H3) as ((F1 & FT & FS & FB) & _).
  pose proof (geom_numsS _ HG) as (_ & _ & F2 & _).
  assert (NSD : forall x, 0 <= x < 2 ^ 47 -> (client_addrA CST A x \/ x < IMG_HI) -> ~ sec_dyn (Sh x)).
  {
    intros x BX Hx SD. destruct (sec_dyn_sh x BX SD) as (ch & Hch & HH & Hr).
    destruct Hx as [Hx|Hx].
    - apply (client_not_QRD x Hx). apply sec_dyn_QRD. right. right. apply Exists_exists. exists ch. split; [exact Hch|]. split; [exact HH|]. left. exact Hr.
    - destruct (In_nth_error _ _ Hch) as [i Hi]. pose proof HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
      pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; clear -D8 D9; lia)) as PB. clear -PB Hx Hr. lia. }
  destruct Hcs as [(x & Hx & ->)|(x & Hx & ->)].
  2:{
      destruct (HXGL x Hx) as [X0 X1]. pose proof (NSD x ltac:(unfold IMG_HI in X1; clear -X0 X1; lia) (or_intror X1)) as NS.
      unfold IMG_HI in X1. revert HQ. apply sh_off_space; [clear -X0 X1; lia | left; clear -X1 S1; lia | exact NS]. }
  destruct (client_addr_bounds CST HCST A x mf HG HF HLS Hx) as [BX _].
  pose proof (NSD x BX (or_introl Hx)) as NS.
  destruct (client_addr_cases CST A x mf HF Hx) as [S|[L|[FR|[C|FL]]]].
  - revert HQ. apply sh_off_space; [exact BX | right; clear -S S2; lia | exact NS].
  - destruct L as (b & n & Hin & Ha).
    destruct (live_user_where b n x Hin Ha) as [(c & Hc & W)|(i & ch & Hi & W & _)].
    +
      destruct (is_primary n) eqn:HP.
      2:{ destruct (live_sec_map A mq HLS HSR HI3 b n Hin HP) as (i & ch & Hi & Eb & RZ & N1 & BN & MP & MS0 & DI).
          destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1. unfold PG in *. exfalso. clear -W Ha Eb BN X1 Hc MS0. lia. }
      pose proof (live_prim_czone A HG H3 mq HLS HPR b n Hin HP) as L. cbv zeta in L. destruct L as (C1 & O0 & OM & OE & _ & (RN & RZ & N1) & _).
      pose proof (Size_facts _ C1) as (SZ & SM). destruct (mod8_of_slot _ _ (proj1 SZ) SM OM) as [Mo Ms].
      pose proof (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.rz_facts n)) as RZ16.
      assert (B8 : b mod 8 = 0).
      { replace b with (SBq + ClassID (needed n) * 2 ^ 32 + (b - rz n - (SBq + ClassID (needed n) * 2 ^ 32)) + rz n) by lia.
        apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r; [apply Z.divide_add_r|]|].
        - apply Z.mod_divide; [lia | exact S8].
        - exists (ClassID (needed n) * 2 ^ 29). lia.
        - apply Z.mod_divide; [lia | exact Mo].
        - destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(lia)) RZ16) as [k Hk]. exists (k * 2). lia. }
      assert (SX : Sh b <= Sh x < Sh b + (n + 7) / 8).
      { split; [apply Geometry.Sh_mono; clear -Ha; lia|]. unfold Sh.
        destruct (proj1 (Z.mod_divide b 8 ltac:(lia)) B8) as [kb Hkb]. subst b. rewrite Z.div_mul by lia.
        pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
        assert (x / 8 < kb + (n + 7) / 8) by (apply Z.div_lt_upper_bound; [lia | clear -Ha DM MB; lia]). lia. }
      destruct (QRD_cases (Sh x) HQ) as [Q|Q].
      { revert Q. apply (live_not_QT A HG H3 HQP HAU mq HLS HPR HSR HI3 b n (Sh x) Hin). right. exact SX. }
      pose proof (Sh_in_band x BX) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
      destruct Q as [Q|[(c' & Hc' & Q)|[(c' & Hc' & Q)|[Q|[Q|Q]]]]]; [| | | | |exact (NS Q)].
      * clear -Q B S1. lia.
      * clear -Q B S1 Hc'. lia.
      * assert (CC : c' + 1 <= c \/ c <= c') by lia. destruct CC as [CC|CC].
        -- pose proof (Geometry.Sh_mono (SBq + c' * 2 ^ 32 + 2 ^ 32) x ltac:(clear -W CC; lia)) as M. clear -Q M. lia.
        -- assert (A8 : (SBq + c' * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) mod 8 = 0).
           { apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|]; [apply Z.mod_divide; [lia | exact S8] | exists (c' * 2 ^ 29); lia | exists (2 ^ 29 - 2 ^ 26); lia]. }
           pose proof (Sh_lt_aligned x _ A8 ltac:(clear -W CC; lia)) as M. clear -Q M. lia.
      * unfold QRD_img, QG, SEC_INST in Q. clear -Q B. lia.
      * pose proof (geoQ2 A HG H3) as (_ & (_ & _ & CB & _) & _). clear -Q B CB. lia.
    + destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1. revert HQ. apply sh_off_space; [exact BX | clear -W X1; lia | exact NS].
  - destruct FR as (c & p & Hc & Hp & _ & Hxx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. revert HQ. apply sh_off_space; [exact BX | clear -Hxx M FS; lia | exact NS].
  - destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. revert HQ. apply sh_off_space; [exact BX | left; clear -X S1; lia | exact NS].
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. revert HQ. apply sh_off_space; [exact BX | clear -M FS; lia | exact NS].
Qed.
End Client.

Section Kept.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S34VCST;R1A2SaS35R2A1A1F_;Fa;").

Lemma client_same_qcs : ltac2:(tb__ "0|0|
S12S12S31R2R1A2S8S0SdS3cVCST;R3R1A3S3cVCST;R4R1A3A2Fa;S0SdS3dVCST;VXGL;R3R1A4S3dVCST;VXGL;R4R1A4A2Fa;A2F_;FA3;FA2;").
Proof.
  intros A2 A3 E. unfold same_but_qcs in E.
  assert (C : forall a, client_addrA CST A3 a <-> client_addrA CST A2 a) by (intros a; rewrite E; unfold client_addrA, client_mut_addrA, aa_frames, frame_flag; cbn [aa_geom aa_live aa_fs_busy]; tauto).
  split; [exact C|]. intros a. unfold client_shadowA. split; intros [(x & Hx & Ea)|H]; try (right; exact H); left; exists x; (split; [apply C; exact Hx | exact Ea]).
Qed.

Theorem mem_kept_drain : ltac2:(tb__ "0|7|
S12S12S12S20S41Q40M0A1M1A1S43S3bG1S22S41Q8A1M2A1M3F_;M4G4S44R7R3R5R4A4S31R8R7A2G1SaS2fRaS42G0R1A2M5A2A1SbG3R5R2A1S3aR7R2A2A3F_;Fa;G1S8S1S2dG5A2S3G5S2cA2A2SaSbG3S3aR8R2A2S23G2A1M6A3A1SaSbG3R7R3A1G6A3A1F_;F_;Fa;S3eVCST;VXGL;RcRbR6S3aR7A1A6S3eVCST;VXGL;RdRbR7R6A6F_;F_;F_;F_;F_;Fm5;Fm0;FrE;Fmd;Ftpx;FA3;FA2;FA;").
Proof.
  intros A A2 A3 tpx md rE m0 m5 HAQ ESB KEY DEF [K1 K2].
  destruct (client_same_qcs A2 A3 ESB) as [CA CS].
  pose proof HAQ as (HG & _ & HF & HRest & _ & HI3 & _). cbn zeta in HRest, HF. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A2 c) <= kUserSpaceSize).
  { intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  split.
  - intros a Ha Hcl. rewrite <- (K1 a Ha).
    2:{ destruct Hcl as [(C1 & C3 & NE)|(S1 & S3 & D0)]; [left; exact (conj C1 (conj (proj1 (CA a) C3) NE)) | right; exact (conj S1 (conj (proj1 (CS a) S3) D0))]. }
    apply KEY. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by exact Ha.
    destruct Hcl as [(_ & C3 & _)|(_ & S3 & _)].
    + exact (client_not_QRD CST HCST HCSTQ A2 HG HI3 R5 HAU _ _ R1 R3 R4 HF a (proj1 (CA a) C3)).
    + exact (cshadow_not_QRD CST XGL HCST HXGL HCSTQ A2 HG HI3 R5 HAU _ _ R1 R3 R4 HF a (proj1 (CS a) S3)).
  - intros x j Hx Hj Hdef. apply DEF.
    + assert (Bx : 0 <= x < 2 ^ 47).
      { destruct Hx as [[_ C3]|GX]; [| destruct (HXGL x GX) as [X1 X2]; unfold IMG_HI in X2; clear -X1 X2; lia].
        exact (proj1 (client_addr_bounds CST HCST A2 x _ HG HF R1 (proj1 (CA x) C3))). }
      destruct (word_byte_range (Sh x) j ltac:(unfold Sh, SHADOW_OFF; clear -Bx; lia) Hj) as (W1 & W2 & W3). rewrite W2.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (Z.div_pos x 8 ltac:(clear -Bx; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)).
      clear -W3 Hj H H0. lia.
    + apply (K2 x j); [|exact Hj | exact Hdef]. destruct Hx as [[C1 C3]|GX]; [left; exact (conj C1 (proj1 (CA x) C3)) | right; exact GX].
Qed.
End Kept.
