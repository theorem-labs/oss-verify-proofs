(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From Stdlib Require NArith PArith.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.

(* [comment removed for export] *)
Module InvQ7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "topG"; "AA"; "ag_thread"; "cs_allocated_user"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "q_mem"; "QRD"; "cls_of"; "q_pure"; "@Corelib.Init.Datatypes"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "q_foot"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3"; "QT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma q_mem_frame : ltac2:(tb__ "0|4|
S6SbSbSfR3A1S0S12R5R1A2SaS10S13Q8A1A1M0R4R2A1R5R2A1M1A3F_;Fz;S0S9S1S3S7S4R6A1A1M2Z50A2R1A2S2R1S3G2Z70A2A2A2SaG0G1R6R2A1M3A3F_;Fz;S0S9S1S3S11Z98A2R1A2S2R1S3S11Zc0A2A2A2SaG0G3R7R2A1A3F_;Fz;ScR6R7A2ScR6R8A2F_;F_;F_;F_;F_;Fm';Fm;FA;").
Proof.
  intros A m m' [QP _] AGF AGT AGQ (QB & QL1 & QL2 & QH1 & QH2 & QMX). unfold q_mem.
  assert (EXT : forall b z, In b (qall A) -> qb_addr b <= z < qb_addr b + kQuarantineBatchSize -> m' z = m z).
  { intros b z Hb Hz. apply AGF. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb | left; exact Hz]. }
  split.
  { apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) QP b Hb) as BP. pose proof (proj1 (Forall_forall _ _) QB b Hb) as BM.
    apply (batch_mem_frame A m m' b BP); [|exact BM]. intros z Hz. apply AGF. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact Hb|].
    destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right].
    apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it. split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz. }
  split; [apply (qlinks_agree m m'); [|exact QL1]; intros b z Hb Hz; apply (EXT b z); [unfold qall; apply in_or_app; left; exact Hb | unfold kQuarantineBatchSize; lia]|].
  split; [apply (qlinks_agree m m'); [|exact QL2]; intros b z Hb Hz; apply (EXT b z); [unfold qall; apply in_or_app; right; exact Hb | unfold kQuarantineBatchSize; lia]|].
  split; [apply (qhdr_repr_agree m m'); [|exact QH1]; intros z Hz; apply AGT; lia|].
  split; [apply (qhdr_repr_agree m m'); [|exact QH2]; intros z Hz; apply AGQ; lia|].
  eapply cell_ok_agree; [|exact QMX]. cbn [c_addr c_w]. intros k Hk. apply AGQ. lia.
Qed.

Section Top.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S9S1Z1R1A2S1R1Z1eA2A2S9S1Z0S8SeVA;R2A2A1M0A2S1G0S14A2A2F_;Fc;").
Variable mq : bview.
Hypothesis HSR : secondary_repr mq A.
Local Abbreviation Gq := (aa_geom A).

Lemma QT_lt_top : ltac2:(tb__ "0|0|
S0S15VA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z HQ. pose proof HI3 as (H3 & _). pose proof (QT_num A HG H3 HQP HAU z HQ) as W.
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG). unfold QG in W.
  destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -W T2 S2 TG; lia.
Qed.

Lemma q_foot_lt_top : ltac2:(tb__ "0|0|
S0S12VA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _ & SEC3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> z < topG Gq) by (intros QZ; exact (QT_lt_top z (or_introl (or_introl QZ)))).
  destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz]; [clear -Hz RZ Eu Esz D8 R8 IP2 D12; lia|].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (fst it + snd it + 8) ltac:(clear -Eu Esz D8 R8 IP2 D12 TG D10; destruct D10 as (E1 & _); lia)) as SL. unfold HIGH_SHADOW_END in SL.
      assert (M : Sh (fst it) + (snd it + 7) / 8 <= Sh (fst it + snd it + 8)).
      { unfold Sh. pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
        pose proof (Z.div_le_mono (fst it + (snd it + 7) / 8 * 8) (fst it + snd it + 8) 8 ltac:(lia) ltac:(lia)) as X. rewrite Z.div_add in X by lia. lia. }
      clear -Hz SL M TG. lia.
Qed.

Lemma QRD_lt_top : ltac2:(tb__ "0|0|
S0SdVA;R1A2S2R2S5S4VA;A1A1A2F_;Fz;").
Proof.
  intros z HQ. pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & C1 & C2 & _).
  destruct HQ as [[HQ|[HQ|[(c & Hc & HQ)|HS]]]|[HQ|HQ]].
  - exact (QT_lt_top z (or_introl HQ)).
  - clear -HQ T2. lia.
  - unfold region_info, free_array, region_beg, kRegionInfoStride, kFreeArraySize in HQ. rewrite kSpaceSize_val, kUserSpaceSize_val in HQ. unfold kRegionSize in HQ.
    destruct HQ as [HQ|[HQ|HQ]]; [clear -HQ Hc S2; lia | clear -HQ Hc S2; lia |].
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (ag_spacebeg Gq + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + 2 ^ 29) ltac:(clear -Hc S1 S2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL. clear -HQ SL TG. lia.
  -
    destruct HSR as (HS1 & _ & _ & _ & (_ & PD) & _). destruct PD as (_ & _ & PD3 & _).
    destruct HS as [HS|[HS|[HS|HS]]].
    + unfold SEC_INST in HS. clear -HS TG. lia.
    + clear -HS PD3. lia.
    + apply Exists_exists in HS as (ch & Hch & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *. clear -HS D8 D9 D12. lia.
    + apply Exists_exists in HS as (ch & Hch & _ & HS). destruct (In_nth_error _ _ Hch) as [i Hi].
      destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      destruct HS as [HS|HS]; [clear -HS D12; lia|].
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(destruct D10 as (E1 & E2 & _); clear -E1 E2 D12 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
      clear -HS SL TG. lia.
  - unfold qrtc_zone, QG in HQ. clear -HQ C2 TG. lia.
  - unfold qrtc2_zone in HQ. clear -HQ TG. lia.
Qed.

Lemma q_mem_frame_top : ltac2:(tb__ "0|1|
SbSbS0S2R1S5S4VA;A1A1A2SaS10S13Q8A1A1R3R2A1R4R2A1A3F_;Fz;ScR3VA;A2M0G0F_;F_;Fm';Fm;").
Proof.
  intros m m' AV HQM. pose proof HI3 as (H3 & _). pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (q_mem_frame A m m' HQP); [| | | exact HQM].
  - intros z Hz. apply AV. exact (q_foot_lt_top z Hz).
  - intros z Hz. apply AV. clear -Hz T2. lia.
  - intros z Hz. apply AV. unfold QG in Hz. clear -Hz TG. lia.
Qed.
End Top.
End InvQ7.

(* [comment removed for export] *)
Module InvQC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_geom"; "ageom"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "pair"; "Some"; "option"; "prod"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "le"; "div"; "lt"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "live_block_reprC"; "K0C"; "rest_invQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "maskv"; "view"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "live_block_repr"; "AInvA"; "QG"; "alloc_magic_ok"; "bandtp_inv"; "depot_wf"; "fs_inv"; "geom_ok"; "ia_inv"; "inv3"; "live_sep"; "misc_inv"; "model_inv"; "primary_repr"; "secondary_repr"; "shadow_unpoisoned"; "thread_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "K0"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kQuarantineMin"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QNPRE"; "q_pure"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition live_block_reprC (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|7|
S0S0S1dS10S0S0A2SdS0S0R2R1A4S6VA;A1A3S2SfS9Q8M0A1M1A1M2Vm;S11R3Z10M3A2A1SeG1SaG0Z2M4A2A2M5A3S1S2G2Vm;S11R4G3A2A1G5A3S1S23Vm;S24S11R4ZcA2U4S16R3S17G4Z20A2M6A2A3A2S1S23Vm;S24S11R4ZeA2U2S14R3G6A2A3A2S1S3dVm;R4R3A3S1S31Vm;R4R3A3S3G1G1S1S2G2Vm;S11R5ZfA2A1SeG1R1A2A3S2S0S16SbG0R1A2Z4A2Z1A3A2Lt;A2A2A2A2A2A2F_;F_;Fn;Fb;").

Definition rest_invQC (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S1S38VA;A1S1S1fVm;VA;A2S1S3bVm;VA;A2S1S3cVm;VA;A2S1S1S47VA;A1S23Vm;S24S12S30Z48A2U8S44A3A2A2S1S33Vm;VA;A2S1S36Vm;VA;A2S1S3eVm;S7VA;A1A2S39Vm;A1A2A2A2A2A2A2A2A2").

Definition AInvQC (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S26S1cS1bVrho;A1A2S22S7VA;A1S8S1S35R1A1S1S28R2R1A2S1S34S27S2dR1A1M0R2A2VA;A2S1S21S25G0R2A2VA;A2S1S3aS1cVA;Vtp;Vmd;A4S1S37VA;A1S32R2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma live_block_repr_C : ltac2:(tb__ "0|0|
S22S5S2eR2R1A2S1fR3R2A2F_;FA;Fm;").
Proof. intros m A H b n Hin _. exact (H b n Hin). Qed.
Lemma live_block_reprC_back : ltac2:(tb__ "0|3|
S0SfS9Q8M0A1M1A1M2Fx;S5S0S0S1dS10S0S0A2SdS0S0R2R1A4S6R3A1A3S2G2R5S11R3Z10A2A1SeG1SaG0Z2A2A2A3F_;Fn;Fb;S1fR3R2A2S2eR4R3A2F_;F_;FA;Fm;").
Proof. intros m A H2 H b n Hin. exact (H b n Hin (H2 b n Hin)). Qed.

Theorem AInvQ_C : ltac2:(tb__ "0|0|
S5S1aScS9Q40A1A1S18S3fR4R3R2R1A4S1eR5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQC. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3). split; [exact R1|]. split; [exact (live_block_repr_C _ A R2) | exact R3].
Qed.
Theorem AInvA_QC : ltac2:(tb__ "0|0|
S5S1aScS9Q40A1A1S18S2fS1cR4R3R2R1A5S1eR5R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md H. exact (AInvQ_C A rho tp md (AInvA_Q A rho tp md H)). Qed.
Theorem AInvQC_back : ltac2:(tb__ "0|2|
S5S1aScS9Q40A1A1S18S0S0S1dS10S0S0A2SdS0S0R2R1A4S6R6A1A3S2SfS9Q8M0A1M1A1S25S2dS7R7A1A1S26S1cS1bR6A1A2S11R3Z10A2A3SeG1SaG0Z2A2A2A3F_;Fn;Fb;S1eR5R4R3R2A4S3fR6R5R4R3A4F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md H2 (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQ. cbn zeta.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
  destruct HRest as (R1 & R2 & R3). split; [exact R1|]. split; [exact (live_block_reprC_back _ A H2 R2) | exact R3].
Qed.

Lemma live_block_reprC_agree : ltac2:(tb__ "0|4|
S22S22S5S5S2ScS10S0S0A2M0A1S6R1A1S6R2A1A3S0S0S0S1dG0SdS0S0R3R2A4S6R6A1M1A3S4S1S13S11R4S45R3A1A2R2A2S15R2S12R4R3A2A2A2S1S13S43R4A1M2R2A2S15R2S12G2S14S12R3Z7A2Z8A2A2A2A2A2S2SfS9Q8A1A1R9R3A1RaR3A1A3F_;F_;Fz;Fn;Fb;S0S0S1dG0SdS0S0R2R1A4G1A3S13Z1R2A2F_;Fn;Fb;S1fR7R5A2M3G3F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EL AG HN HL b n Hin H2'. rewrite EL in Hin.
  pose proof (HN b n Hin) as Hn1. pose proof (rz_bound n) as RZ.
  assert (AGb : forall z, b - rz n <= z < b + n -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); left; exact Hz).
  assert (H2 : m (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- AGb by lia; exact H2').

  set (A1 := mkAA (aa_geom A) (aa_cls A) (aa_cache_inited A) (aa_sec A) (aa_ptr_committed A) [(b, n)]
                  (aa_q_thread A) (aa_q_global A) (aa_depot A) (aa_fs_hint A) (aa_fs_busy A) (aa_internal_inited A) (aa_V A) (aa_Km A) (aa_Kf A)).
  assert (L1 : live_block_repr m A1).
  { intros b0 n0 [E|[]]. injection E as <- <-. exact (HL b n Hin H2). }
  assert (L1' : live_block_repr m' A1).
  { apply (live_block_repr_agree m m' A1 A1 eq_refl); [| |exact L1].
    - intros b0 n0 z [E|[]] Hz. injection E as <- <-. exact (AG b n z Hin Hz).
    - intros b0 n0 [E|[]]. injection E as <- <-. exact Hn1. }
  exact (L1' b n (or_introl eq_refl)).
Qed.

Definition K0C (Kc : KcA) (A : AA) : jpredA := ltac2:(tb__ "0|0|
S1aScS9Q40A1A1ScS19A1S18S1S1eVA;R4R3R1A4S1VKc;R2R1A2S1S2cVA;R4A2S1S2bVA;R4A2S41VA;R4A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma K0_C : ltac2:(tb__ "0|0|
S29S5S1aScS9Q40A1A1ScS19A1S18S40R6R5R4R3R2R1A6S20R7R6R5R4R3R2A6F_;Fmd;Ftr;Ftp;Frho;FA;FKc;").
Proof. intros Kc A rho tp tr md (HA & HR). exact (conj (AInvQ_C A rho tp md HA) HR). Qed.

Theorem K0C_stable : ltac2:(tb__ "0|0|
S29S5S2aR2A1S42S1cS46S20R3R2A2A3F_;FA;FKc;").
Proof.
  intros Kc A HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Htop & HRG). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [|split; [|split; [|split]]].
  - destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB). unfold AInvQC. cbn zeta. rewrite Erm.
    split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [exact (model_inv_mat A tp md md' HM Hme) | exact (conj HI3 HB)].
  - destruct Hme as ((mat' & ->) & _). rewrite <- (with_vm_backing_id md) in HK. exact (Kc_ok_mat Kc tr md _ _ _ _ HKc HK).
  - unfold tp_ok in *. rewrite <- (Hw 24%positive) by (unfold QNPRE; lia). exact Htp.
  - unfold top_high in *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (unfold QNPRE, V_DEPTH; lia). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite <- (Hw 151%positive), <- (Hw 152%positive), <- (Hw 155%positive), <- (Hw 156%positive) by (unfold QNPRE; lia).
    exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End InvQC.

(* [comment removed for export] *)
Module RebuildR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_mapped_user"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "AA"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Datatypes"; "length"; "option"; "Some"; "nat"; "app"; "bool"; "list"; "true"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "Sh"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "region_info"; "@Stdlib.Lists.List"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "bandtp_inv"; "live_ids"; "model_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ"; "envR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "cls_pure"; "refillA"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP.
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
    apply (env_out SB T (topG G) c nf mu 65536 6578176 z GEO C1 NF0 MUB Hz); [clear -S1; lia | clear -TI; lia | clear; lia | exact Hc]. }
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
            pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.rz_facts n) as (_ & RZ16).
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
Module F0A_hbN_zones.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "obj_range"; "ob_base"; "ob_hi"; "ob_lo"; "ranges_disjoint"; "pairwise_disjoint"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "pair"; "false"; "prod"; "Some"; "andb"; "option"; "list"; "true"; "fst"; "orb"; "snd"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "zdisjb"; "in_zone"; "zcheck"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "le"; "pow"; "div"; "lt"; "max"; "min"; "mul"; "opp"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "same_rng"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones.ZonesW"; "in_zoneW"; "@Stdlib.Lists.List"; "Forall2"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "zd_of"; "botwinb"; "in_zoneW"; "zd_allb"; "zds_of"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_blkN"; "O_hdr"; "O_iamP"; "O_sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "unwind_objs"; "free_depth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "topG"; "ag_ctx"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "LOW_SHADOW_BEG"; "Sh"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZonesW.
Variable rho : valuation.
Variable zb zlo zhi : nat -> Z.
Variable zused : list nat.
Hypothesis Hsep : ltac2:(tb__ "0|3|
ScScS32ScR2Vzused;A3M0G0S1dS19ScR4R3A3A1S1bS24S22Vzb;R5A1M1Vzhi;R5A1A2S22Vzb;R4A1M2Vzlo;R4A1A2A2S24S22G2Vzhi;R4A1A2S22G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Definition in_zoneW (o : sobj) (d : zdesc) : Prop := ltac2:(tb__ "0|5|
SfSfScS1A2M0S1A2OLd;Vd;G0S1G0OLp;R2ScS1S1aS32ScR2Vzused;A3S1bS24S17S1S1S5Vrho;Vo;A2M1A3M2S15S1S1G1A3M3A2S1aS24S22Vzb;R2A1M4S28R1Vzlo;R2A1A2A2G3A2S24G2S22G4S29R3Vzhi;R2A1A2A2A2A2A2A2Llo;Lz;Xfx1Lhi;Lp;Xfx1").
Lemma in_zone_W : ltac2:(tb__ "0|0|
S4S1eS20Vrho;Vzb;Vzlo;Vzhi;Vzused;R2R1A7S30R3R2A2F_;Fd;Fo;").
Proof. intros o [[z lo] hi] (U & L1 & L2 & R). split; [exact U|]. destruct R as [R|[R1 R2]]; [left; exact R | right; lia]. Qed.
Lemma zdisjW_sound : ltac2:(tb__ "0|1|
S4S4S1eS1eS30R4R2A2M0G0S19SbS1fR4R3A2S14A3S9S5Vrho;R7A2S5Vrho;R6A2A2F_;F_;F_;Fd';Fd;Fo';Fo;").
Proof.
  intros o o' [[z lo] hi] [[z' lo'] hi'] (U & R) (U' & R') Hb. unfold zdisjb in Hb. unfold ranges_disjoint.
  destruct (obj_range rho o) as [a b]. destruct (obj_range rho o') as [a' b']. cbn [fst snd] in *.
  destruct R as [R|[R1 R2]]; [lia|]. destruct R' as [R'|[R1' R2']]; [lia|].
  destruct (Nat.eqb_spec z z') as [<-|NE]; cbn [negb orb] in Hb.
  - repeat (apply Bool.orb_prop in Hb as [Hb|Hb]); try (apply Z.leb_le in Hb; lia).
  - destruct (Hsep z z' U U' NE); lia.
Qed.
Theorem zonesW_pd : ltac2:(tb__ "0|0|
S13S4A1S13S1eA1S31S4S1eS30R2R1A5S19SbS21R2A1S14A3SaVrho;R4A2F_;F_;Fds;Fobjs;").
Proof.
  intros objs ds HF. induction HF as [|o d objs' ds' Ho HF IH]; intros Hc; [exact I|].
  cbn [zcheck] in Hc. apply andb_prop in Hc as [Hd Hc]. cbn [SymState.pairwise_disjoint]. split; [|exact (IH Hc)].
  clear IH Hc. induction HF as [|o' d' objs'' ds'' Ho' HF' IH']; [constructor|].
  cbn [forallb] in Hd. apply andb_prop in Hd as [H1 H2]. constructor; [exact (zdisjW_sound o o' d d' Ho Ho' H1) | exact (IH' H2)].
Qed.
Theorem zonesW_cross : ltac2:(tb__ "0|2|
S13S4A1M0S13S1eA1M1G0G1S31S4S1eS30R4R3A5S31S4S1eS30R3R2A5S19SbS34S1eS1eS34S1eS1fR1A1R4A3Ld;R5A3S14A3S3aS4S4S3aS4S4S9S5Vrho;R1A2S5Vrho;R2A2A2Lo';R6A3Lo;R7A3F_;F_;F_;Fds';Fobjs';Fds;Fobjs;").
Proof.
  intros objs ds objs' ds' HF HF' Hc. induction HF as [|o d objs1 ds1 Ho HF IH]; [constructor|].
  cbn [forallb] in Hc. apply andb_prop in Hc as [H1 H2]. constructor; [|exact (IH H2)].
  clear IH H2 HF. induction HF' as [|o' d' objs2 ds2 Ho' HF' IH']; [constructor|].
  cbn [forallb] in H1. apply andb_prop in H1 as [Ha Hb]. constructor; [|exact (IH' Hb)].
  pose proof (zdisjW_sound o o' d d' Ho Ho' Ha) as D. unfold ranges_disjoint in D |- *. lia.
Qed.
End ZonesW.

Definition botwinb (o : sobj) : bool := ltac2:(tb__ "0|9|
S3SbLx;M0S6Vo;A1S1SeLz;M1S0S0SbLi;R1S0SeLp;S0S0SbLp;R1S0S0SbLp0;R1S0SeLp1;S0S0SbLp1;R1S0SeLp2;M2G2G0S8Vo;A1G1S0S0SbLi0;R1S0S0SbLp2;R1S0S0SbLp3;R1S0S0SbLp4;R1S0SeLp5;M3G3G0S7Vo;A1S1S11S23S2bS43A1R1A2S23R1Z0A2A2Lhi;S0SeLi1;S2cS3S3SeLb;La;M4Lop;M5G5S2dG4Lop;M6G6SbS2S3SeLa;Lw;Lsgn;M7S0S3S1SeLk;M8Li1;Ll;X3x8X0x3Lp4;S0SeLp4;SeX0x3Lp3;S0SeLp3;SeX0x3Lp2;G2SeX0x3Li0;G5G5G6G6G7S0S3G8Li0;Ll;X3x8X0x3Lp1;SeX0x3Lp0;S0SeLp0;SeX0x3Lp;SeX0x3Li;G5G5G6G6G7S0S3G8Li;Ll;X3x8").
Definition zd_of (nW : nat) (o : sobj) : option zdesc := ltac2:(tb__ "0|36|
SbS12S1eA1M0L_;M1S16S16S2fVo;A1S36Vo;A1A2S33S4S2eVo;A1S42S41VnW;A1A1A3A2S10SfSfScS1A2M2S1A2M3SdG2S1SdScS1U3Z0M4A4S25Z2M5Z40A2A4A2G1S2eVo;S3eA2S10G3SdG2S1SdScS1U5M6Z17f0A4Z17f8A4A2G1S2eVo;S3dA2S10G3SdG2S1SdScS1G6Z1800A4S25G5Z3eA2A4A2G1S2eVo;S40A2S10G3SdG2S1SdScS1U4G4A4Z100000001000A4A2G1S2eVo;S3fA2S10G3SdG2S1SdScS1U0M7Zf2608M8A4S22S22G8Z40000A2Z8A2A4A2S3G0Lx;M9S6Vo;A1S1S1G0Lz;R1G9S8Vo;A1MaS1G9S7Vo;A1MbS1G1S11S11S23Ze4000R2A2S23R2R1A2McA2S23R1Z646000A2A2S10G3SdG2S1SdScS1G7R2A4R1A4A2S18S1eA1MdXbx2Lb;S0GdLi;MeS2cS3S3GdLb;MfLa0;M10Lop;M11G11S2dG10Lop;M12G12SbS2S3GdLa0;Lw;Lsgn;M13S0S3S1GdLk;M14Li;Ll;M15X3x8La;GeS2cS3GfLa;M16Lop;M17G17S2dG16Lop;M18G18SbS2S3GdLa;Lw;Lsgn;M19G15X3x8S0GdLp;M1aG1aX1x3Lz;S0S0G0Li;M1bR1S0S0G0Lp;M1cR1S0S0G0Lp0;M1dR1S0S0G0Lp1;M1eR1S0GdLp2;M1fS0S0G0Lp2;M20R1S0S0G0Lp3;M21R1S0GdLp4;M22S0S0G0Lp4;M23R1S0GdLp5;M24S0S0G0Lp5;M25R1S0GdLp6;M26G26G9GaS1G9GbS1G1S11S11S23G4R2A2GcA2S23R1Z1000M27A2A2M28S10G3SdG2S1SdScS1U1M29R2A4R1A4A2GdXbx2Lb;S0GdLi0;M2aG11G11G12G12G13S0S3G14Li0;Ll;M2bX3x8La;G2aG17G17G18G18G19G2bX3x8X0x3Lp5;GdX0x3Lp4;GdX0x3Lp3;S0GdLp3;M2cGdX0x3Lp2;GdX0x3Lp1;S0GdLp1;M2dGdX0x3Lp0;S0GdLp0;M2eGdX0x3Lp;S0G1cR1G2eS0G1dR1G2dS0G1eR1S0G20R1S0G21R1G22S0G23R1G24S0G25R1G26G26G9GaS1G9GbS1G1G28S10G3SdG2S1SdScS1U2R2A4R1A4A2GdXbx2Lb;G2aG11G11G12G12G13G2bX3x8La;G2aG17G17G18G18G19G2bX3x8X0x3Lp5;GdX0x3Lp4;GdX0x3Lp3;G2cGdX0x3Lp2;G1fGdX0x3Lp1;GdX0x3Lp0;GdX0x3Lp;GdX0x3Li;S2cS3S3S2cG0Lop;R3S3G0La0;R2S1GdLz;S0G1bR1S0G1cR1S0G1dR1S0G1eR1G1fS0G20R1S0G21R1G22S0G23R1G24S0G25R1G26G26S3G0Lb0;R9S1G9GaS1G9GbS1G1S11S11S11S11S23G4R3A2S23R3G27A2A2S23G4S22R3R2A2M2fA2A2GcA2S23S22R3R1A2M30G27A2A2S10G3SdG2S1SdScS1G29G2fA4G30A4A2GdXbx2Lb;G2aS2cS3GfLa1;M31Lop0;M32G32S2dG31Lop0;M33G33SbS2S3GdLa1;Lw;Lsgn;G2bX3x8La;G2aS2cG16Lop0;M34G34S2dG16Lop0;M35G35G19G2bX3x8Lc;G2aG34G34G35G35G19G2bX3x8X0x3Lp5;GdX0x3Lp4;GdX0x3Lp3;G2cGdX0x3Lp2;GdX0x3Lp1;G2dGdX0x3Lp0;G2eGdX0x3Lp;G1aGdX0x3Li;G34G34G35G35G19G15X3x8GdGdGdGdGdGdGdGdGdX2cxaLb0;La0;Lop;G17G18G18G19G15X3x8Xbx2Xbx2Xbx2Xbx2Xbx2").
Definition zds_of (nW : nat) (objs : list sobj) : list zdesc := ltac2:(tb__ "0|1|
S3bS4S1eS4S12S1eA1S1eLx;S35VnW;R1A2S1eR1Ld;SdSfScS1A2S1SdScS1U63Z0M0A4G0A4X12x2Lo;Vobjs;A4").
Definition zd_allb (nW : nat) (ZU : list nat) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S34S4S4S12S1eA1SbLx;S35VnW;R1A2S1eSfSfScS1A2M0S1A2SbLz0;R1G0S1G0SbLp;R2ScS1S33ScS49R2A1VZU;A3Lz2;Lz;Xfx1Lz1;Lp;Xfx1Lz0;SeX12x2Lo;Vobjs;A3").

Section Sound.
Variables (nW : nat) (A : AA) (p n : Z) (ch : sec_chunk) (rho : valuation).
Let G : ageom := aa_geom A.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Record zenv : Prop := mkZE {
  ze_151 : rw rho 151%positive = Z_to_bv 64 (ag_thread G);
  ze_152 : rw rho 152%positive = Z_to_bv 64 (ag_ctx G);
  ze_12 : rw rho 12%positive = Z_to_bv 64 p;
  ze_105 : rw rho 105%positive = Z_to_bv 64 (N8 n);
  ze_106 : rw rho 106%positive = Z_to_bv 64 (N8 n / 8);
  ze_top : top_high A rho;
  ze_dep : bv_signed (rw rho V_DEPTH) <= - free_depth;
  ze_chn : Forall (holds rho) (chain_pre (Wcan nW));
  ze_nums : 0x1000 <= ag_thread G /\ ag_thread G + 0x1000 <= topG G /\ 0x1000 <= ag_ctx G /\ ag_ctx G + 0x1000 <= topG G /\ topG G <= 2 ^ 47;
  ze_blk : p = h + 6144 /\ 0x646000 <= h /\ h mod 4096 = 0 /\ h + ms <= 2 ^ 47 /\ 8 <= N8 n /\ N8 n mod 8 = 0 /\ 6144 + N8 n <= ms
}.
Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis HZ0 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U0M0A1Z0A3S1aS19S1Vzlo;G0A1Ze4000A3S19S1Vzhi;G0A1Z646000A3A2A2").
Hypothesis HZ1 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U1M0A1S46VG;A1A3S1aS19S1Vzlo;G0A1Z0A3S19S1Vzhi;G0A1Z1000A3A2A2").
Hypothesis HZ2 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U2M0A1S45VG;A1A3S1aS19S1Vzlo;G0A1Z0A3S19S1Vzhi;G0A1Z1000A3A2A2").
Hypothesis HZ3 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U3M0A1S44VG;A1A3S1aS19S1Vzlo;G0A1Z0A3S19S1Vzhi;G0A1S25Z2Z40A2A3A2A2").
Hypothesis HZ4 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U4M0A1S47A3S1aS19S1Vzlo;G0A1Z0A3S19S1Vzhi;G0A1Z100000001000A3A2A2").
Hypothesis HZ5 : ltac2:(tb__ "0|1|
S1aS19S1Vzb;U5M0A1Vh;A3S1aS19S1Vzlo;G0A1Z0A3S19S1Vzhi;G0A1Vms;A3A2A2").
Hypothesis ZE : zenv.

Lemma stk_zone : ltac2:(tb__ "0|3|
S4S19SbS16S16S2fR1A1S36R1A1A2S33S4S2eR1A1S42S41VnW;A1A1A3A2S14A3S1bS24S17S1S1S5Vrho;R2A2M0A3M1S15S1S1G0A3M2A2S1aS24S44VG;A1G2A2S24G1S25Z2Z40A2A2A2A2F_;Fo;").
Proof.
  intros o Hok. pose proof ZE as [_ _ _ _ _ HTOP HDEP HCH _ _]. unfold top_high in HTOP. unfold free_depth in *. fold G in HTOP.
  pose proof (urange (rw rho 10%positive)) as U10.
  apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]|].
  - unfold winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk by lia. cbn [fst snd eval]. right. lia.
  - unfold botwinb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct ohi as [hi| | | | | | | ]; try discriminate. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2. unfold free_depth in *.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. unfold soff. cbn [eval]. unfold V_DEPTH in *. right. lia.
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rho o o' Hs).
    assert (LNK : Forall (fun o => bv_unsigned (rw rho 10%positive) + 16 <= bv_unsigned (eval rho (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l0 W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rho (SVar 28) (l0 :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk by lia. cbn [fst snd]. right. lia.
Qed.

Lemma rng_hdr : ltac2:(tb__ "0|0|
S19SfS1S1A2S5Vrho;S3eA2SdS1S1S22Vh;Z17f0A2S22Vh;Z17f8A2A4A3").
Proof.
  pose proof ZE as [_ _ E12 _ _ _ _ _ _ (B1 & B2 & B3 & B4 & B5 & B6 & B7)]. unfold O_hdr. rewrite obj_range_mk by lia. cbn [eval]. rewrite E12, u64_lit by lia. f_equal; lia.
Qed.
Lemma rng_blk : ltac2:(tb__ "0|1|
S19SfS1S1A2S5Vrho;S3dA2SdS1S1S22Vh;Z1800A2M0S22G0S3cVn;A1A2A4A3").
Proof.
  pose proof ZE as [_ _ E12 E105 _ _ _ _ _ (B1 & B2 & B3 & B4 & B5 & B6 & B7)]. unfold O_blkN, vN8, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite E12, E105, u64_lit by lia. rewrite signed_lit. unfold snorm.
  rewrite Z.mod_small by lia. destruct (Z.ltb_spec (N8 n) (2 ^ 63)); [|lia]. f_equal; lia.
Qed.
Lemma rng_sh : ltac2:(tb__ "0|1|
S19SfS1S1A2S5Vrho;S40A2SdS1S1S48S22Vh;Z1800A2A1M0S22G0S26S3cVn;A1Z8A2A2A4A3").
Proof.
  pose proof ZE as [_ _ E12 _ E106 _ _ _ _ (B1 & B2 & _ & B4 & B5 & B6 & B7)]. unfold O_sh, shb, vN8g, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite add_val, srl_val, E12, E106, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (N8 n) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  rewrite signed_lit. unfold snorm. rewrite (Z.mod_small (N8 n / 8)) by lia. destruct (Z.ltb_spec (N8 n / 8) (2 ^ 63)); [|lia].
  unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small by lia. rewrite B1. f_equal; lia.
Qed.
Lemma rng_iam : ltac2:(tb__ "0|1|
S1cS1S1S1aS1aS24Z0R1A2S27R1S25Z2ZfA2A2A2S19SfS1S1A2S5Vrho;S3fA2SdS1S1S22S2aZ8R1A2M0Zf2608A2S22G0Zf2610A2A4A3A2Lk;A2").
Proof.
  pose proof ZE as [_ _ E12 _ _ _ _ _ _ (B1 & B2 & B3 & B4 & B5 & B6 & B7)]. exists (p / 2 ^ 32).
  pose proof (Z.div_lt_upper_bound p (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos p (2 ^ 32) ltac:(lia) ltac:(lia)).
  split; [lia|]. unfold O_iamP. rewrite obj_range_mk by lia. unfold iam_base. cbn [eval]. rewrite sll_val, srl_val, E12, u64_lit by lia.
  change (32 mod 64) with 32. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. f_equal; lia.
Qed.

Theorem zd_sound : ltac2:(tb__ "0|0|
S4S1eS19S12S1eA1S35VnW;R2A2S10S1eR1A2A3S32ScS15ScS1S15SfScS1A2S1R2A3A3VZU;A3S37Vrho;Vzb;Vzlo;Vzhi;VZU;R4R3A7F_;F_;Fd;Fo;").
Proof.
  intros o d Hd HU. pose proof ZE as [E151 E152 E12 _ _ _ _ _ (T0 & T1 & C0 & C1 & TG) (B1 & B2 & B3 & B4 & B5 & B6 & B7)].
  destruct HZ0 as (Z0a & Z0b & Z0c). destruct HZ1 as (Z1a & Z1b & Z1c). destruct HZ2 as (Z2a & Z2b & Z2c). destruct HZ3 as (Z3a & Z3b & Z3c).
  destruct HZ4 as (Z4a & Z4b & Z4c). destruct HZ5 as (Z5a & Z5b & Z5c).
  unfold zd_of in Hd.
  destruct (winpb o || botwinb o || existsb (same_rng o) (unwind_objs (Wcan nW))) eqn:ES.
  { injection Hd as <-. cbn [fst] in HU. split; [exact HU|]. destruct (stk_zone o ES) as [R|[R1 R2]]; [left; exact R | right]. rewrite Z3a, Z3b, Z3c. lia. }
  destruct (same_rng o O_hdr) eqn:EH.
  { injection Hd as <-. cbn [fst] in HU. split; [exact HU|]. right. rewrite (same_rng_range rho o _ EH), rng_hdr, Z5a, Z5b, Z5c. cbn [fst snd]. lia. }
  destruct (same_rng o O_blkN) eqn:EB.
  { injection Hd as <-. cbn [fst] in HU. split; [exact HU|]. right. rewrite (same_rng_range rho o _ EB), rng_blk, Z5a, Z5b, Z5c. cbn [fst snd]. lia. }
  destruct (same_rng o O_sh) eqn:ESH.
  { injection Hd as <-. cbn [fst] in HU. split; [exact HU|]. right. rewrite (same_rng_range rho o _ ESH), rng_sh, Z4a, Z4b, Z4c. cbn [fst snd].
    unfold Sh, SHADOW_OFF, LOW_SHADOW_BEG in *.
    pose proof (Z.div_pos (h + 6144) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)).
    assert ((h + 6144) / 8 + N8 n / 8 <= 2 ^ 44).
    { destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(lia)) B6) as [k Ek]. rewrite Ek, Z.div_mul by lia.
      destruct (proj1 (Z.mod_divide h 4096 ltac:(lia)) B3) as [k2 Ek2]. replace (h + 6144) with ((k2 * 512 + 768) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    lia. }
  destruct (same_rng o O_iamP) eqn:EI.
  { injection Hd as <-. cbn [fst] in HU. split; [exact HU|]. right. destruct rng_iam as (k & Hk & RK). rewrite (same_rng_range rho o _ EI), RK, Z0a, Z0b, Z0c. cbn [fst snd]. lia. }
  destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hd.
  destruct ob as [c0| v | op e1 e2 | | | | | ]; try discriminate.
  - destruct c0; try discriminate. destruct olo as [a| | | | | | | ]; try discriminate. destruct ohi as [b| | | | | | | ]; try discriminate.
    destruct ((0xe4000 <=? a) && (a <=? b) && (b <=? 0x646000)) eqn:EC; [|discriminate]. injection Hd as <-. cbn [fst] in HU.
    apply andb_prop in EC as [EC H3]. apply andb_prop in EC as [H1 H2]. apply Z.leb_le in H1, H2, H3.
    split; [exact HU|]. right. rewrite obj_range_mk by lia. cbn [eval fst snd]. rewrite u64_lit by lia. rewrite Z0a, Z0b, Z0c. lia.
  - destruct olo as [a| | | | | | | ]; try (repeat (destruct v as [v|v|]; try discriminate); fail).
    destruct ohi as [b| | | | | | | ]; try (repeat (destruct v as [v|v|]; try discriminate); fail).
    assert (CASE : (v = 151%positive /\ (0 <=? a) && (a <=? b) && (b <=? 4096) = true /\ d = (1%nat, a, b))
                   \/ (v = 152%positive /\ (0 <=? a) && (a <=? b) && (b <=? 4096) = true /\ d = (2%nat, a, b))).
    { do 8 (destruct v as [v|v|]; try discriminate); destruct ((0 <=? a) && (a <=? b) && (b <=? 4096)) eqn:EC; try discriminate; injection Hd as <-; [left | right]; repeat split; reflexivity. }
    destruct CASE as [(-> & EC & ->)|(-> & EC & ->)]; cbn [fst] in HU; apply andb_prop in EC as [EC H3]; apply andb_prop in EC as [H1 H2]; apply Z.leb_le in H1, H2, H3;
      (split; [exact HU|]); right; rewrite obj_range_mk by lia; cbn [eval fst snd].
    + rewrite E151, u64_lit by lia. rewrite Z1a, Z1b, Z1c. fold G. lia.
    + rewrite E152, u64_lit by lia. rewrite Z2a, Z2b, Z2c. fold G. lia.
  - destruct op; try discriminate. destruct e1 as [| v | | | | | | ]; try discriminate. destruct e2 as [c| | | | | | | ]; try (repeat (destruct v as [v|v|]; try discriminate); fail).
    destruct olo as [a| | | | | | | ]; try (repeat (destruct v as [v|v|]; try discriminate); fail).
    destruct ohi as [b| | | | | | | ]; try (repeat (destruct v as [v|v|]; try discriminate); fail).
    assert (CASE : v = 151%positive /\ (0 <=? c) && (c <=? 4096) && (0 <=? c + a) && (a <=? b) && (c + b <=? 4096) = true /\ d = (1%nat, c + a, c + b)).
    { do 8 (destruct v as [v|v|]; try discriminate). destruct ((0 <=? c) && (c <=? 4096) && (0 <=? c + a) && (a <=? b) && (c + b <=? 4096)) eqn:EC; try discriminate. injection Hd as <-. repeat split; reflexivity. }
    destruct CASE as (-> & EC & ->). cbn [fst] in HU. apply andb_prop in EC as [EC H5]. apply andb_prop in EC as [EC H4]. apply andb_prop in EC as [EC H3]. apply andb_prop in EC as [H1 H2].
    apply Z.leb_le in H1, H2, H3, H4, H5. split; [exact HU|]. right. rewrite obj_range_mk by lia. cbn [eval fst snd].
    rewrite add_val, E151, !u64_lit by lia. rewrite Z.mod_small by lia. rewrite Z1a, Z1b, Z1c. fold G. lia.
Qed.
Corollary zds_sound : ltac2:(tb__ "0|0|
S13S4A1S19SbS38VnW;VZU;R1A3S14A3S31S4S1eS37Vrho;Vzb;Vzlo;Vzhi;VZU;A5R2S39VnW;R2A2A5F_;Fobjs;").
Proof.
  intros objs HB. unfold zds_of. induction objs as [|o objs IH]; [constructor|]. cbn [zd_allb forallb] in HB. apply andb_prop in HB as [H1 H2]. cbn [map].
  constructor; [|exact (IH H2)]. destruct (zd_of nW o) as [[[z lo] hi]|] eqn:Ed; [|discriminate].
  apply (zd_sound o _ Ed). cbn [fst]. apply existsb_exists in H1 as (z' & Hz' & E). apply Nat.eqb_eq in E. subst z'. exact Hz'.
Qed.
End Sound.
End F0A_hbN_zones.

(* [comment removed for export] *)
Module F0A_rebuildW.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "Some"; "list"; "option"; "bool"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "alloc_magic_ok"; "qhdr_repr"; "qlinks"; "QG"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "aa_q_global"; "aa_q_thread"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "q_mem"; "batch_mem"; "item_mem"; "q_pure"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "present"; "acell"; "maskv"; "mkACell"; "view"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "qrepr_B"; "AInvB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Mono.
Variables (m m' : bview).
Hypothesis HM : ltac2:(tb__ "0|2|
S0S20Q8A1M0S2S5G0A1M1Vm;R2A1S3G0R1A2A3S2G1Vm';R3A1S3G0R2A2A3F_;Fb;Fz;").
Lemma cell_ok_mono : ltac2:(tb__ "0|0|
S1cS1aVm;R1A2S1aVm';R2A2F_;Fc;").
Proof. intros c H k Hk. apply HM. exact (H k Hk). Qed.
Lemma present_mono : ltac2:(tb__ "0|0|
S0S0S1bVm;R2R1A3S1bVm';R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. destruct (H z Hz) as [b Hb]. exists b. exact (HM z b Hb). Qed.
Lemma alloc_magic_mono : ltac2:(tb__ "0|0|
S0S0S9Vm;R2R1A3S9Vm';R3R2A3F_;Fn;Fu;").
Proof. intros u n [H|[H1 H2]]; [left; exact H | right; split; apply cell_ok_mono; assumption]. Qed.
Lemma item_mem_mono : ltac2:(tb__ "0|0|
S7S0S0A2S15Vm;R1A2S15Vm';R2A2F_;Fit;").
Proof.
  intros it (X1 & X2 & X3 & X4 & X5 & X6 & X7). unfold item_mem. cbn zeta in *.
  split; [exact (HM _ _ X1)|]. split; [exact (present_mono _ _ X2)|]. split; [exact (cell_ok_mono _ X3)|]. split; [exact (cell_ok_mono _ X4)|].
  split; [exact (present_mono _ _ X5)|]. split; [exact (alloc_magic_mono _ _ X6) | exact (present_mono _ _ X7)].
Qed.
Lemma batch_mem_mono : ltac2:(tb__ "0|0|
SfS14Vm;R1A2S14Vm';R2A2F_;Fb;").
Proof.
  intros b (M1 & M2 & M3 & M4 & M5). unfold batch_mem.
  split; [exact (cell_ok_mono _ M1)|]. split; [exact (cell_ok_mono _ M2)|]. split; [exact M3|]. split; [exact (present_mono _ _ M4)|].
  intros i it Hi. destruct (M5 i it Hi) as [C IM]. split; [exact (cell_ok_mono _ C) | exact (item_mem_mono it IM)].
Qed.
Lemma qlinks_mono : ltac2:(tb__ "0|0|
S4SfA1SbVm;R1A2SbVm';R2A2F_;Fl;").
Proof. induction l as [|b r IH]; intros H; [exact I|]. cbn in H |- *. destruct H as [H1 H2]. split; [exact (cell_ok_mono _ H1) | exact (IH H2)]. Qed.
Lemma qhdr_repr_mono : ltac2:(tb__ "0|0|
S0S4SfA1SaVm;R2R1A3SaVm';R3R2A3F_;Fl;Fhdr;").
Proof.
  intros hdr l (H1 & H2 & H3 & H4). unfold qhdr_repr. split; [exact (cell_ok_mono _ H1)|].
  split; [intros Hl; destruct (H2 Hl) as [X Y]; split; apply cell_ok_mono; assumption|]. split; [exact (present_mono _ _ H3) | exact (cell_ok_mono _ H4)].
Qed.
Lemma q_mem_mono : ltac2:(tb__ "0|0|
SeS13Vm;R1A2S13Vm';R2A2F_;FA;").
Proof.
  intros A (QB & QL1 & QL2 & QH1 & QH2 & QMX). unfold q_mem.
  split; [eapply Forall_impl; [|exact QB]; intros b Hb; exact (batch_mem_mono b Hb)|].
  split; [exact (qlinks_mono _ QL1)|]. split; [exact (qlinks_mono _ QL2)|]. split; [exact (qhdr_repr_mono _ _ QH1)|].
  split; [exact (qhdr_repr_mono _ _ QH2) | exact (cell_ok_mono _ QMX)].
Qed.
End Mono.

Lemma maskv_some : ltac2:(tb__ "0|2|
S0S6F_;S19S0S20Q8A1M0S2S5G0A1M1S1dR4R3R2A3S3G0R1A2A3S2G1R4R3A1S3G0R2A2A3F_;Fb;Fz;Fm;FP;").
Proof. intros P m z b H. unfold maskv in H. destruct (P z); [discriminate | exact H]. Qed.

Lemma qrepr_B_pure : ltac2:(tb__ "0|0|
S0S19SeSdS12R1A1A1S21R4R3R2A3S1S16R3A1S1aR4S1eS18ScZ48A2U8S24A3A2A2F_;F_;FA;Fm;FB;").
Proof.
  intros B m A HG (HB & _ & _ & _ & _ & _ & HMIN & _ & _ & HND). split; [|exact HMIN]. unfold q_pure, qall. split; [|exact HND].
  eapply Forall_impl; [|exact HB]. intros b Hb. exact (batch_repr_pure m A b HG Hb).
Qed.
Lemma qrepr_B_mem : ltac2:(tb__ "0|0|
S0S19SeS21R3R2R1A3S1S13R3R2A2S1S17S8S11R2A1A1R4A2S17S8S10R2A1A1S23A2A2A2F_;FA;Fm;FB;").
Proof.
  intros B m A (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). unfold q_mem, qall. split; [|exact (conj H8 H9)].
  split; [|split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | exact H6]]]]].
  apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) H1 b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact B2|]. split; [exact B3|]. split; [exact B5|]. split; [exact B6|].
  intros i it Hi. destruct (B7 i it Hi) as [C (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11)]. split; [exact C|].
  split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|]. exact Q11.
Qed.

Theorem AInvB_Q : ltac2:(tb__ "0|0|
S0SeS27S4S20Q40A1A1S25S22R5R4R3R2R1A5S1S29R5R4R3R2A4S1S13S1fS28S26R4A1A2R5A2S1S17S8S11R5A1A1R6A2S17S8S10R5A1A1S23A2A2A2A2F_;Fmd;Ftp;Frho;FA;FB;").
Proof.
  intros B A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  destruct (qrepr_B_mem B _ A R5) as (QM & QB1 & QB2).
  split; [|split; [|exact (conj QB1 QB2)]].
  - unfold AInvQ. cbn zeta. split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [|exact (conj HM (conj HI3 HB))].
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact (qrepr_B_pure B _ A HG R5)|].
    split; [exact R6|]. split; [exact R7|]. split; [exact R8 | exact R9].
  - eapply q_mem_mono; [|exact QM]. intros z b Hz. exact (maskv_some _ _ z b Hz).
Qed.
End F0A_rebuildW.

(* [comment removed for export] *)
Module SegQ3D_qcs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "list"; "cons"; "nat"; "prod"; "nil"; "app"; "length"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "valuation"; "SAlu"; "SLit"; "SVar"; "sprop"; "sobj"; "ss_facts"; "eval"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "cs_cache"; "mkQB"; "aa_cache_inited"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ageom"; "class_fresh"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "add"; "le"; "lt"; "pow"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs"; "TC1"; "TC2"; "KEPTC"; "RCr"; "TQCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QW"; "push_cache"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "max_count"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc"; "entC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs"; "cptrC"; "FTLC"; "N_qcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "cbC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qb_id"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "JOK"; "TR"; "@Corelib.Lists.ListDef"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop"; "INVD"; "INVI"; "QC_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs.QCStep"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DQCs"; "RC"; "clsB"; "vB"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cptrC : sv := ltac2:(tb__ "0|0|
S12S35S12S33S12S33S60S12S34S5fS13Z20A1A3A3S37A3S13Z4A1A3").
Definition N_qcP : list carve_spec := ltac2:(tb__ "0|e|
S3S5S5S5SfS0A2M0S0A2M1S2S5S5S0S4A2M2SfA2M3A1M4A2M5S1G1G4S1G0S0S1SfS0S47Z0M6A4Z10M7A4S3G3S1G2SfS1S0S4G6U4M8A4S36S14PceA1M9S13Z1A1A2A4S3G3S1G2SfS1S0S4Z4G8A4S14PcfA1A4S3G3S1G2SfS1S0S4Z8U8MaA4S14Pc9A1MbA4S6G3A1McA3A3A3A4S3G5S1G1G4S1G0S0S1SfS0S36S47S12S34G9S13Z2A1A3A2G7A4Z14A4S3G3S1G2SfS1S0S4G7G8A4S48A4GcA3A4S3G5S1G1G4S1G0S0S1SfS0S4cZa10MdA4Za18A4S3G3S1G2SfS1S0S4GdGaA4S36S14Pd1A1S12S33S13G6A1GbA3A2A4GcA3A4S6G5A1A3A3A3").
Lemma TC1_objsP : ltac2:(tb__ "0|0|
SbS2S16A1S19S2eS3bA1A1S7S16S3dS51S58S16S57S4aA4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition FTLC : list sprop := ltac2:(tb__ "0|0|
S52S15S8S15S46S4bA1A2S17S2eS3cA1A1A3").
Lemma TC2_facts : ltac2:(tb__ "0|0|
SbS2S15A1S17S2eS3cA1A1S7S15S46S4bA1S49A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TC2_eq : ltac2:(tb__ "0|0|
SbS30S2fS3bS56S2eS3bA1S3dA2A2S3cA3"). Proof. reflexivity. Qed.

Lemma cptrC_val : ltac2:(tb__ "0|6|
S11S0S0S0SbS26Q40M0A1M1S10R4Pa6A2S25G0R2A2A3SbG1S10R5P9bA2S25G0R4A2A3SbS0R4S28S28R5S27Z18S2bZ2M2Z20A2M3A2A2S27Z10M4R3A2A2A3S29Z0M5R4A2S2aS27G4R5A2G3A2S29G5R8A2S2aR8S2bG2Z40A2A2SbG1S18RbS48A2S25G0R8A2A3F_;F_;F_;F_;F_;F_;F_;Fy;Fa;FSB;Frho;").
Proof.
  intros rho SB a y E166 E155 Ea Hy Hy2 HSB Ha. pose proof (clsB_val rho SB a y E166 E155 Ea Hy Hy2 HSB Ha) as EC.
  apply bv_eq. rewrite (u64_lit y) by lia. unfold cptrC. rewrite U_srl_lit, U_sub, U_sub, U_sll_lit, EC. unfold vB, vSB. cbn [eval]. rewrite E166, E155, !u64_lit by lia.
  change (32 mod 64) with 32. change (4 mod 64) with 4. unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia.
  replace (a - 24 * 2 ^ 32) with (SB + 16 * y) by lia. rewrite (Z.mod_small (SB + 16 * y)) by lia.
  replace (SB + 16 * y - SB) with (y * 2 ^ 4) by lia. rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.
Lemma qb_id_val : ltac2:(tb__ "0|0|
S23S0S2S5S0S0A2A1S0S0SbS0R4S28S28S22R5A1S27Z18S2bZ2Z20A2A2A2S27Z10R1A2A2A3SbS0S4dR6S1dR5R4R3A3A2R2A3F_;Fy;Fs;Fits;Fa;FG;").
Proof.
  intros G a its s y E. unfold qb_id, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale. cbn [qb_addr]. rewrite Z.shiftr_div_pow2 by lia.
  replace (a - (ag_spacebeg G + 24 * 2 ^ 32)) with (y * 2 ^ 4) by lia. apply Z.div_mul. lia.
Qed.

Section QCPost.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma qc_post : ltac2:(tb__ "0|7|
S1bS0S0S0S4S2S1aA1M0G0S11S2S26Q40M1A1M2A1S55S0SbG0S21RbA1S6S1aA1M3A3SbS9S1eRcA1SaA3S0S41ReR1A2S41VA0;R2A2F_;Fz;S3aVA0;ReA2SbG0S20RfA1S3S1aS1dReS6S5S0S0A2A1M4RdA3S7S1aRaR9A3A3A3S2aS2cS8S0S1cS40R10Z18M5A2A1A2A1S44G5A1M6A2S2dS31S39VK;VA0;Vrho0;R11R10ReRdG4RcRbAaS3fRaR9R8A6SbG2S10RbPa6A2S25G1R11A2A3SbG2S10RcPceA2S25G1S2cS8S0S1cS40R13G5A2A1A2A1A2A3SbG2S10RdPcfA2S25G1G6A2A3SbG2S10RePc9A2S25G1S45G5A1A2A3ScS29Z0RcA2S2aRcS2bZ2Z40A2A2A2SbG2S10R10Pd1A2S25G1RdA2A3S32R11R13A2SdS11S11ScS2dS31S38VK;VA0;Vrho0;S42S43R1aG3S7S1aR15R14A3A3G5S4dS1fR1aA1S1dR19G4R18A3A2A3R15R14A6S3eR1R12R11A6S32R1R15A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd tmp' rest rho tp w st HTH HCI HQW HQP0 HGL HNF H E166 E206 E207 E201 Hst E209 HVx. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho _ _ tp _ TC1_eq H) as H1.
  destruct (proj2 H1) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H1)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (E151 & E152 & E155 & E156). pose proof (HCLS HCI 24 ltac:(lia)) as CV.
  pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz. pose proof (cv_len _ _ _ _ _ CV) as K_le.
  unfold pc_entry in C_max, C_sz. change (max_count 24) with 2 in *. change (Size 24) with 8192 in *.
  set (T := ag_thread (aa_geom A)) in *. set (k := Z.of_nat (length (cs_cache (cls_of A 24)))) in *.
  replace (T + 208 + 80 * 24 + 4) with (T + 2128 + 4) in C_max by lia. replace (T + 208 + 80 * 24 + 8) with (T + 2128 + 8) in C_sz by lia.
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & G7 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG) as (_ & TBD & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI, TBD. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A HTH), HGL; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  pose proof (SB_facts A HG) as (_ & SBF1 & SBF2). unfold HIGH_SHADOW_END in SBF1. rewrite kSpaceSize_val in SBF2.
  assert (EC : eval rho clsB = Z_to_bv 64 24) by (apply (clsB_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  assert (ECP : eval rho cptrC = Z_to_bv 64 y) by (apply (cptrC_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  rewrite (qb_id_val (aa_geom A) a [] s y Ey).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply (eval_add_lit A); try lia; unfold vT; cbn [eval]; exact E151).
  assert (Eent : bv_unsigned (eval rho entC) = T + 2128).
  { unfold entC, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval rho (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Eslot : bv_unsigned (eval rho (add entC (SAlu ALU_SLL (SVar 206) (SLit 2)))) = T + 2128 + 4 * k).
  { unfold add at 1. rewrite U_add, U_sll_lit, Eent. cbn [eval]. rewrite E206, u64_lit by lia. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Ek1 : eval rho (add (SVar 206) (SLit 1)) = Z_to_bv 64 (k + 1)) by (apply (eval_add_lit A); try lia; cbn [eval]; exact E206).
  set (R := map carve_obj N_qcP).
  set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R entC 0 16 _ Hsm TC1_objsP ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eent; lia) ltac:(rewrite Eent; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R (add entC (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 _ Hsm TC1_objsP ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eslot; lia) ltac:(rewrite Eslot; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTC R cbC 2576 2584 _ Hsm TC1_objsP ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite EcbC, u64_lit by lia; lia) ltac:(rewrite EcbC, u64_lit by lia; lia)) as [_ PR3].
  fold rho3 v3 in AV1, PR1, AV2, PR2, PR3. rewrite Eent in AV1, PR1. rewrite Eslot in AV2, PR2. rewrite EcbC, u64_lit in PR3 by lia.
  assert (C_cnt3 : cell_ok v3 (mkACell (T + 2128) 4 (k + 1))) by (replace (T + 2128) with (T + 2128 + 0) by lia; exact (av_cell v3 (T + 2128) 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) Ek1)).
  assert (C_max3 : cell_ok v3 (mkACell (T + 2128 + 4) 4 2)) by exact (av_cell v3 (T + 2128) 4 4 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) E207).
  assert (C_sz3 : cell_ok v3 (mkACell (T + 2128 + 8) 8 8192)) by exact (av_cell v3 (T + 2128) 8 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E201).
  assert (C_slot3 : cell_ok v3 (mkACell (T + 2128 + 4 * k + 16) 4 y)) by exact (av_cell v3 (T + 2128 + 4 * k) 16 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.
  set (P := fun z : Z => (T + 2128 <= z < T + 2144) \/ (T + 2144 + 4 * k <= z < T + 2148 + 4 * k) \/ (T + 2784 <= z < T + 2792)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (PT : forall z, P z -> T + 2128 <= z < T + 2792) by (intros z Hz; unfold P in Hz; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold carve_obj, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz;
      rewrite ?Eent, ?Eslot, ?EcbC, ?u64_lit in Hz by lia; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (PPR : forall z, P z -> v3 z <> None).
  { intros z Hz. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PR1 z ltac:(lia)) as [x Hx] | destruct (PR2 z ltac:(lia)) as [x Hx] | destruct (PR3 z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }

  assert (HK3 : K (push_cache (set_q A [] (tmp' ++ rest)) 24 y) rho3 tp tr md).
  { rewrite <- (qb_id_val (aa_geom A) a [] s y Ey).
    apply (kq_push_batch segsA K HL A rho rho3 tp tr md [] (tmp' ++ rest) (mkQB a [] s) HTH HGL eq_refl HCI HNF); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. unfold push_zone, pc_entry in NPZ. fold T k in NPZ.
      destruct Hp as [Hp|[Hp|Hp]].
      + destruct (Z_lt_dec z (T + 2132)) as [|]; [exfalso; apply NPZ; left; lia|].
        destruct (Z_lt_dec z (T + 2136)) as [|]; [apply (cell_ok_same v v3 _ C_max C_max3); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ C_sz C_sz3); cbn [c_addr c_w]; lia].
      + exfalso. apply NPZ. right. lia.
      + exfalso. apply NQ. right. right. unfold qstat_zone. fold T. lia.
    - intros z _ Hd. fold v3. fold v in Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
    - fold v3. unfold pc_entry. fold T k. replace (T + 0xd0 + 80 * 24) with (T + 2128) by lia. exact C_cnt3.
    - fold v3. unfold pc_entry. fold T k. rewrite (qb_id_val (aa_geom A) a [] s y Ey). replace (T + 0xd0 + 80 * 24 + 16 + 4 * k) with (T + 2128 + 4 * k + 16) by lia. exact C_slot3. }

  assert (QF_OUT : forall z, q_foot A z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; pose proof (PT z HP); lia).
  assert (HR3 : RMEM2 v3 (aa_geom A) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (qall A)) by (intros b Hb; rewrite (qall_A1 A HTH), HGL; right; exact Hb).
    split; [|split; [|split; [|split]]].
    - apply Forall_forall. intros b Hb.
      apply (batch_mem_frame A v v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b (INQ b Hb))); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [exact (INQ b Hb)|]. unfold bfoot in Hz.
      destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
      split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; left; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; right; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr. fold T in Q1, Q2, Q3, Q4 |- *.
      assert (TOUT : forall z, T + 0x50 <= z < T + 0x70 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); unfold QG in *; lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }

  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. pose proof (PT z Hz) as PTz. split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *; lia].
    destruct HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
    destruct (Z_lt_dec z (T + 2768)) as [|]; [right; left; rewrite <- EG; fold T; lia | left; right; right; unfold qstat_zone; rewrite <- EG; fold T; lia]. }

  set (A' := push_cache (set_q A [] (tmp' ++ rest)) 24 y) in *.
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ TC1 rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).
  pose proof (SPA_unobj segsA TJ rho TC1 KEPTC R tp tr ms md TC1_objsP HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. rewrite TC2_eq in HU.
  assert (HU1 : SPA segsA (JRD K A0 rho0 A' tmp' rest) TC2 rho3 tp (tr, mkCfg ms md)).
  { split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HR3 | exact HF3]. }
  assert (HU2 : SPA segsA (JRD K A0 rho0 A' tmp' rest) TC4 rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU1 | exact TC4_below |]. intros HF. rewrite TC2_facts in HF. exact (proj1 (proj1 (Forall_app _ _ _) HF)). }
  pose proof (JRD_stable K HL A0 rho0 A' tmp' rest) as HSTD.
  destruct (entM_SPA _ _ RCr MC rho3 tp _ TC4_ent HSTD HU2) as (H7 & AG7 & V7 & RM7).
  assert (VV : forall i, In i [166; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho3 (infer_sub NPRE (ax_S TC4) (ax_S RCr))) i = rw rho i).
  { intros i Hi. rewrite (V7 i (SVar i)); [reflexivity|]. unfold MC, idm. apply in_map_iff. exists i. split; [reflexivity | exact Hi]. }
  eexists. split; [exact H7|]. destruct HVx as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !VV by (cbn; tauto). tauto.
Qed.
End QCPost.

Section QCStep.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
S1bS2S1aA1M0G0S4fVQ;VX;S38VK;VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S1bS0S0S4S2S5S0S0A2A1S2S1aA1M0G0S4fVQ;VX;S39VK;VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Variable TPI : list word -> Prop.

Definition QC_full_step : Prop := ltac2:(tb__ "0|6|
S1bS0S0S4S2S1aA1S11S2S26Q40M0A1M1A1M2VTPI;R1A1M3S5aVA0;Vrest;R8R7S6S5S0S0A2A1M4R4A6S32R4R5A2SbG1S10R5Pa6A2S25G0R9A2A3S29S44Z18M5A1S2cS8S0S1cS40RbG5A2A1A2A1A2S1bS11G2G3S59VA0;Vrest;R4RcA4S32R4RdA2S50VQ;VX;S2dS31S38VK;VA0;Vrho0;R6ReVrest;A6S5eR5R4A5A3F_;F_;F_;Ftp';Frho';FA';S50VQ;VX;S2dS31S39VK;VA0;Vrho0;RdRcRbRaG4R9Vrest;AaS5dR8R7A5A3F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fnd;Fn0;Fa;FA;").

Lemma cls24_not_fresh : ltac2:(tb__ "0|0|
S1bS1aS11S2S26Q40A1A1S2S54A1S53SbS9S1eR6A1SaA3S3aVA0;R7A2VK;R8R6R5R4R3A5S61S1aR8S4eR9A1A3SeS24VA0;Z18A2A1F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fb;FA;").
Proof.
  intros A b rho tp tr md HCI (_ & _ & EF) HK Hb HF. specialize (EF 24 HF). unfold class_fresh in HF. rewrite HF in EF.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (proj1 (Forall_forall _ _) (proj1 HQPU) b Hb) as (_ & _ & (y & _ & Y0 & _ & Y1) & _).
  unfold cls_of, nthZ in Y1. rewrite EF in Y1. unfold kQuarantineBatchSize in Y1. cbn in Y1. lia.
Qed.

Theorem QC_step_of_full : ltac2:(tb__ "0|0|
S5cS5bVK;VA0;Vrho0;VQ;VX;Vrest;VTPI;A7F_;").
Proof.
  intros HFULL A a n0 nd tmp' rho tp HTP HI HVx E166 HC.
  destruct (Z_lt_dec (Z.of_nat (length (cs_cache (cls_of A 24)))) (max_count 24)) as [HNF|HFL]; [|exact (HFULL A a n0 nd tmp' rho tp HTP HI HVx E166 ltac:(lia) HC)].
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6).
  set (k := Z.of_nat (length (cs_cache (cls_of A 24)))) in *. set (J := JRI K A0 rho0 A a n0 nd [] tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 24)).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK.
    apply (cls24_not_fresh A (mkQB a [] s) rho tp tr md I2 I4 HK). rewrite (qall_A1 A I1), I5. left. reflexivity. }
  intros NFR.
  apply (tr_glue X _ J Cqc tp (fun r => HVX r tmp' /\ rw r 166%positive = Z_to_bv 64 a /\ rw r 206%positive = Z_to_bv 64 k /\ rw r 207%positive = Z_to_bv 64 (max_count 24)
                                         /\ rw r 201%positive = Z_to_bv 64 (Size 24) /\ exists st, 0 <= st < 2 ^ 64 /\ rw r 209%positive = Z_to_bv 64 st)).
  { intros w Hw. destruct (qc_pre K HL A0 rho0 A a s n0 nd tmp' rest rho tp w I1 I2 I5 HNF Hw E166) as (st & Hst & _ & Hs). eexists. split; [exact Hs|].
    assert (OTH : forall i, i <> 206%positive -> i <> 207%positive -> i <> 201%positive -> i <> 209%positive ->
                   rw (rho_sets rho [(206%positive, Z_to_bv 64 k); (207%positive, Z_to_bv 64 (max_count 24)); (201%positive, Z_to_bv 64 (Size 24)); (209%positive, Z_to_bv 64 st)]) i = rw rho i).
    { intros i N1 N2 N3 N4. apply rho_sets_other. cbn. intros [E|[E|[E|[E|[]]]]]; congruence. }
    destruct HVx as (E184 & E185 & E186 & E187 & E208).
    split; [unfold HVX; rewrite !OTH by discriminate; tauto|]. split; [rewrite OTH by discriminate; exact E166|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists st. split; [exact Hst | reflexivity]. }
  intros rhoE (HVe & E166e & E206e & E207e & E201e & st & Hst & E209e).
  apply (qc_call X J rhoE tp (HJI _ _ _ _ _ _ _)). intros rho' Hag.
  assert (AGV : forall i, (i < ss_next (ax_S Cqc))%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  set (A' := push_cache (set_q A [] (tmp' ++ rest)) 24 (qb_id (aa_geom A) (mkQB a [] s))).
  apply (tr_glue X _ (JRD K A0 rho0 A' tmp' rest) RCr tp (fun r => HVX r tmp')).
  { intros w Hw. apply (qc_post K HL A0 rho0 A a s n0 nd tmp' rest rho' tp w st I1 I2 I3 I4 I5 HNF Hw); try (rewrite AGV by reflexivity; assumption); [exact Hst|].
    destruct HVe as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !AGV by reflexivity. tauto. }
  intros rho5 HV5. apply (seg_D_CrM X _ rho5 tp (HJD _ _ _)). intros Tx M rho6 HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' rho6 tp HTP); [|exact (HVX_keep _ rho5 rho6 tmp' HKp ltac:(cbn; tauto) HV5)].
  split; [reflexivity|]. split; [exact I2|]. split; [|split; [|split; [reflexivity|]]].
  - intros z Hz. apply I3. exact (QW_push_batch A (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
  - apply QP_push; [exact I4 | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_batch A (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
Qed.
End QCStep.
End SegQ3D_qcs.

