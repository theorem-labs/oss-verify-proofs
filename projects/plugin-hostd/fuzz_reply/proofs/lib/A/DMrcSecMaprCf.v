(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecMaprCf.v (commit 3d8ad2aeb77e, H4 cf instance set (reply-rccf); file sha256 dccf8b3a46ec) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): H4's secondary MAP-READ field DMrcSecReads.rc_sec_mapr_t at reply's
   cf cut relation YGcfInstDrainR.ARXr_cf.
   rule 24: proves function __asan::QuarantineCallback::Recycle (0x33e30; RChunk secondary cut / map reads) at reply's cf relation,
   instance of H4's own transports; checker: git grep rc_sec_cut|rc_sec_mapr|rc_reads|rchunk_ok = 0 statements.

   WHAT.  [rc_sec_mapr_of_cf]: for every B with TfibSyms B and every IOK, Hp, rc_sec_mapr_t B holds at
   ARXr_cf B IOK Hp, with no other premise.
   [rc_sec_mapr_nf_of_cf]: the same at the flag-free field DMrcSecNf.rc_sec_mapr_nf_t (rcc_pre_sec, rcc_pre_x without
   st_cache_inited X = true, for rcc_pre_x): the reads take only the pre's relation conjunct, so [rc_sec_mapr_of_cf]
   is that theorem through DMiface.rcc_pre_sec_of_x (Theorem Labs, 2026-10-30, lane B1, slice H4; rule 24: no
   function proved, the same reads at one pre conjunct less).

   HOW.  The cut relation gives ARcfR (the cut record, the ledger, the budget, amwf, the shadow facts).  For the dead
   entry r at slot i of the pointer array:
   - [sec_of_arr]: r in the array has a chunk based at (PSec r kPage) (wsc_arr_chunks); that chunk's facts
     (RL.chunk_facts_cf) put (ly_sec ly r, sec_map_size (ck_req y)) in sec_extents, and its secmap is sm with
     sm_len sm = sec_map_size (ck_req y) (wfr_chunks), so (MAP, LEN) = (ly_sec ly r, sm_len sm) is a secondary extent;
   - the index: the array is NoDup (wsc_nodup), so index_of finds slot i;
   - the world's account: the budget's asecA puts (MAP, MAP + LEN) in w_A W;
   - the vm map: the ledger's alc_sec puts wiv (MAP, LEN) in the model's maps;
   - amwf: the relation's own conjunct;
   - the madvise gate: the extent is in the application zone (amr_placed), so its shadow lies in the low or the high
     shadow band; [gate_cf] is YG0g.madvise_gate over the cf ledger (alc_reserved, alc_img, alc_band, alc_shna). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03cf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstDrainR YGcfInstDrainRL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFg8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA06 YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSecGv DMrcSecReads DMrcSecNf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.

Lemma u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The slot of r in the pointer array.                                                                              *)
Lemma index_of_nth : forall l r i, List.NoDup l -> nth_error l i = Some r -> YG00.index_of l r 0%nat = Some i.
Proof.
intros l r i ND H. destruct (index_of_spec l r 0%nat (nth_error_In _ _ H)) as (j & E & H').
rewrite Nat.add_0_l in E. rewrite E. f_equal.
apply (proj1 (NoDup_nth_error _) ND); [exact (nth_error_lt _ _ _ H') | rewrite H, H'; reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* An entry of the pointer array is a secondary extent, with its secmap's length.                                   *)
Lemma sec_of_arr : forall B ly X Hp rd r sm i, ARmcfR B ly X Hp rd ->
nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
In (ly_sec ly r, sm_len sm) (sec_extents ly X).
Proof.
intros B ly X Hp rd r sm i M Hsm Hi.
pose proof (amr_wfr _ _ _ _ _ M) as WF. pose proof (wfr_secondary _ _ _ _ _ WF) as XS.
destruct (proj1 (wsc_arr_chunks _ XS r) (nth_error_In _ _ Hi)) as (y & Hy & Eby).
pose proof (RL.chunk_facts_cf B ly X Hp _ y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite Eby in GG. destruct GG as (_ & _ & _ & _ & Gin & _).
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ WF) y Hy) as [_ CK]. rewrite Eby in CK.
destruct CK as (_ & _ & sm' & Q1 & _ & _ & Q4). rewrite Hsm in Q1. injection Q1 as <-.
rewrite Q4. exact Gin.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The madvise gate over a shadow band, from the cf ledger (YG0g.madvise_gate, over ALedger_cf).                    *)
Lemma gate_cf : forall (segs : list Segment) ly S md (b n : Z),
layout_ok ly -> ALedger_cf segs ly S md -> 0 < n ->
(kLowShadowBeg <= b /\ b + n <= kLowShadowEnd \/ kHighShadowBeg <= b /\ b + n <= kHighShadowEnd) ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 b) (Z_to_bv 64 n) = true.
Proof.
intros segs ly S md b n LO L Hn Hin. destruct (alc_shna _ _ _ _ L) as [N1 N2].
unfold YG0n.w64, YG0d.w64 in N1, N2.
assert (Rb : 0 <= b /\ b + n < 2 ^ 63) by (unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hin; lia).
assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply u64; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64; lia).
assert (HR : region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 b) (Z_to_bv 64 n) = true).
{ rewrite (alc_reserved _ _ _ _ L). apply (YG0h.region_free_reserved segs); [| | lia | lia].
  - intros sg Hsg. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img _ LO) as (J0 & J1 & J2 & J3).
    unfold kImgLo, kImgEnd in *. lia.
  - unfold kImgEnd, kLowShadowBeg, kHighShadowBeg in *. lia. }
destruct Hin as [[I1 I2]|[I1 I2]].
- apply (YA06.madvise_gate_intro _ (wiv (kLowShadowBeg, kLowShadowEnd - kLowShadowBeg))).
  + apply (alc_band _ _ _ _ L). left. reflexivity.
  + unfold wiv, YG0n.w64. cbn [fst snd]. rewrite Ub, u64 by (unfold kLowShadowBeg; lia). exact I1.
  + unfold wiv, YG0n.w64. cbn [fst snd]. rewrite Ub, Un, !u64 by (unfold kLowShadowBeg, kLowShadowEnd; lia). lia.
  + exact HR.
  + apply (YA06.region_free_sub _ _ _ _ _ N1); rewrite ?Ub, ?Un, !u64 by (unfold kLowShadowBeg, kLowShadowEnd; lia); lia.
- apply (YA06.madvise_gate_intro _ (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg))).
  + apply (alc_band _ _ _ _ L). right. right. left. reflexivity.
  + unfold wiv, YG0n.w64. cbn [fst snd]. rewrite Ub, u64 by (unfold kHighShadowBeg; lia). exact I1.
  + unfold wiv, YG0n.w64. cbn [fst snd]. rewrite Ub, Un, !u64 by (unfold kHighShadowBeg, kHighShadowEnd; lia). lia.
  + exact HR.
  + apply (YA06.region_free_sub _ _ _ _ _ N2); rewrite ?Ub, ?Un, !u64 by (unfold kHighShadowBeg, kHighShadowEnd; lia); lia.
Qed.

(* The shadow of an application extent lies in the low or the high shadow band. *)
Lemma shadow_band : forall m len PB kk, in_app m len -> 0 < kk ->
DMrcSecGv.SHAv m <= PB -> PB + kk <= DMrcSecGv.SHEv m len ->
(kLowShadowBeg <= PB /\ PB + kk <= kLowShadowEnd \/ kHighShadowBeg <= PB /\ PB + kk <= kHighShadowEnd).
Proof.
intros m len PB kk IA Hkk H1 H2. unfold DMrcSecGv.SHEv, DMrcSecGv.SHAv, DMrcSecGv.CNTv in H1, H2.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
destruct IA as [IA0 [IL|[IH1 IH2]]]; [left | right];
unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *;
Z.div_mod_to_equations; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The five reads from ARcfR.                                                                                       *)
Lemma mapr_of_ARcfR : forall (segs : list Segment) B ly X Hp (W : world segs) mem md r sm i,
ARcfR segs B ly X Hp W mem md -> nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
YG00.index_of (st_sec_arr X) r 0%nat = Some i /\
In (ly_sec ly r, ly_sec ly r + sm_len sm) (w_A W) /\
In (Z_to_bv 64 (ly_sec ly r), Z_to_bv 64 (sm_len sm)) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGv.SHAv (ly_sec ly r) <= PB -> PB + kk <= DMrcSecGv.SHEv (ly_sec ly r) (sm_len sm) ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
Proof.
intros segs B ly X Hp W mem md r sm i MR Hsm Hi.
destruct MR as (M & LED & BUD & MW & _).
pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (sec_of_arr B ly X Hp _ r sm i M Hsm Hi) as GI.
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ M)) _ GI) as (_ & IA & _). cbn [fst snd] in IA.
pose proof (wfr_secondary _ _ _ _ _ (amr_wfr _ _ _ _ _ M)) as XS.
split; [exact (index_of_nth _ _ _ (wsc_nodup _ XS) Hi)|].
split; [destruct BUD as (_ & BU2 & _); exact (proj1 (BU2 _ GI))|].
split; [exact (alc_sec _ _ _ _ LED _ GI)|].
split; [exact MW|].
intros PB kk Hkk H1 H2. apply (gate_cf segs ly X md PB kk LO LED Hkk).
exact (shadow_band _ _ PB kk IA Hkk H1 H2).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* H4's secondary map-read field at reply's cf cut relation, over rcc_pre_sec (DMrcSecNf.rc_sec_mapr_nf_t).         *)
Theorem rc_sec_mapr_nf_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  DMrcSecNf.rc_sec_mapr_nf_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_reply B IOK Hp).
Proof.
intros B TB IOK Hp. unfold DMrcSecNf.rc_sec_mapr_nf_t.
intros inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi.
destruct PRE as ((_ & HA & _) & _).
exact (mapr_of_ARcfR _ B ly X Hp W mem md r sm i HA Hsm Hi).
Qed.

(* H4's secondary map-read field at reply's cf cut relation.                                                        *)
Theorem rc_sec_mapr_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  DMrcSecReads.rc_sec_mapr_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_reply B IOK Hp).
Proof.
intros B TB IOK Hp. unfold DMrcSecReads.rc_sec_mapr_t.
intros inst ly X k cbp W regs mem md r o sm i PRE.
exact (rc_sec_mapr_nf_of_cf B TB IOK Hp inst ly X k cbp W regs mem md r o sm i (rcc_pre_sec_of_x _ _ _ _ _ _ _ _ _ _ _ PRE)).
Qed.
End d.
