(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFg7.v, with its module paths and module names changed; 381 of its 430 lines of code are new or changed and 272 lines of the source are left out. *)
(* The free half of the any-U allocator, lane cd: cache_dealloc (lib/A/AFg0.v) and recycle_chunk of a primary chunk (lib/A/AFg7.v) under ARU (FSupoisonAllocFK.v cd_preU / rcc_preU). *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The machine runs on mem, where the user-poisoned head bytes UP read 0xf7; the donor's AR holds of
   FSupoison.unpoison UP mem (mu below), where they read 0. Each walk keeps the donor text:
   - facts: the donor facts lemmas (AFfi.v, AFfr.v) applied unchanged at mu;
   - seed transfer (mu -> real): cd_hyps_real / rc_hyps_real rebuild the run's hyps record (AFgk.v / AFgs.v free_hyps)
     on mem, field by field; the values the donor reads from memory (j80 j88 jst, hb1 j1 j2) keep their mu-value;
   - run: the donor segments (AFgy.v segK1, AFgz.v segK2, AFh7.v segRC) unchanged on the real configuration;
   - post transfer (real -> mu): cd_post_mu / rc_post_mu give the donor post (AFgk.at_RETK / AFgs.at_CD) for the
     configuration whose memory is unpoison UP mem';
   - leaf: the donor leaf / bridge (AFg0.FINKH, AFg7.CDPRE) at mu, then FSupoisonAllocFK.cd_leafU_intro /
     rcc_leafU_intro with U's two invariants. upoison_ok: cache_dealloc keeps st_chunks (upoison_ok_chunks);
     recycle_chunk removes a quarantined chunk, no live block (upoison_ok_del_quar). upoisoned: cache_dealloc's write
     window is application memory, off the shadow band (FSupoisonAllocFK.upoisoned_frame with AFgk.WIN_zone);
     recycle_chunk's write window may hold shadow bytes, but only of the recycled chunk's non-live granules, so each is
     off UP (upoisoned_frame_off with rc_WIN_fixed).
   - raw frame (the leaf's last conjunct, on mem itself): the run's frame on mem (cd_post_mu / rc_post_mu) and the
     donor's window lemmas (AFg0.WIN_D with AFez.D_owned; AFg7.WIN_D with AFf3.D_owned) put every written byte in an
     owned byte or the call's stack window (FSupoisonAllocFK.raw_of_meq); recycle_chunk composes this with the raw
     frame of its cache_dealloc leaf (FSupoisonAllocFK.raw_trans, AFf3.aowned_X1).
   - region condition: cd_fixed / rc_fixed are the bytes whose value or presence is transferred plus the write window;
     cdealloc_regions_off_ush / rchunk_prim_regions_off_ush put them off U: application memory (stack, thread
     object, thread context, region info, free array, the chunk's extent, the image) and, for recycle_chunk, the
     shadow of the recycled chunk's user granules, which no live block meets. *)
(* Modified by Theorem Labs, 2026-10: tfib_cdealloc_okU and tfib_rchunk_primU prove their leaves' raw frame from the runs' frames and the donors' window lemmas: raw memory frame re-exported for the ARU lift of route 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AFgk AFgs.
(*PART2-REQUIRE*)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AFgy AFgz AFh7 AFfi AFfr AFez AFf3 AFg0 AFg7.
(*END-PART2-REQUIRE*)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac nums := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL,
  kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_stats, KSTACK, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_ALLOCATOR, kRegionInfoOff,
  kFreeArrayOffset, kFreeArrayMax, kChunkHeaderSize in *.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Shared steps: the return configuration, and U's two invariants across a call.                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma cfg_ra : forall (regs regs' : bvmap 5 word) (m : word -> option byte) md,
  mkCfg (YK11.mkst regs' (YK11.getr regs 1) m (YK11.seg_rom tfibsegs)) md = cfg_at tfibsegs (raZ regs) regs' m md.
Proof. intros regs regs' m md. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Section g.
Variable B : asyms.
(* A step that keeps st_chunks keeps every live block, so U's ranges stay in live blocks. *)
Lemma upoison_ok_chunks : forall ly S S' UP, FSP.upoison_ok B ly S UP -> st_chunks S' = st_chunks S ->
  FSP.upoison_ok B ly S' UP.
Proof.
intros ly S S' UP OK E. apply (FAR.upoison_ok_keep B ly S ly S' UP OK).
intros r p n _ Hb _ _. unfold ablocks, blocks in *. rewrite E. exact Hb.
Qed.
(* Removing a quarantined chunk loses no live block. *)
Lemma upoison_ok_del_quar : forall ly S S' UP k, FSP.upoison_ok B ly S UP ->
  In k (st_chunks S) -> ck_state k = CQuarantined -> List.NoDup (map ck_beg (st_chunks S)) ->
  st_chunks S' = del_chunk (st_chunks S) (ck_beg k) -> FSP.upoison_ok B ly S' UP.
Proof.
intros ly S S' UP k OK Hk Hst ND E. apply (FAR.upoison_ok_keep B ly S ly S' UP OK).
intros r p n _ Hb _ _.
destruct (In_split_beg _ _ Hk ND) as (l1 & l2 & EL & N1 & N2).
apply In_ablocks in Hb as (y & Hy & Hsy & Hu & Hn). apply In_ablocks.
exists y. split; [|exact (conj Hsy (conj Hu Hn))].
rewrite E, EL, (del_chunk_present l1 k l2 N1). rewrite EL in Hy.
apply in_app_iff in Hy as [Hy|[<-|Hy]]; apply in_app_iff; [left; exact Hy | rewrite Hst in Hsy; discriminate | right; exact Hy].
Qed.
(* A run that keeps the memory outside a window D, every byte of which is off U, keeps U's 0xf7 bytes. Unlike
   FSupoisonAllocFK.upoisoned_frame (a window outside the shadow band), D may hold shadow bytes: recycle_chunk's
   window holds the shadow of the recycled chunk's user granules. *)
Lemma upoisoned_frame_off : forall ly S UP W mem md mem' (D : Z -> Prop),
  FSP.ARU tfibsegs B ly S UP W mem md -> (forall a, D a -> FAR.offU UP a) ->
  (forall x : word, ~ D (bv_unsigned x) -> mem' x = mem x) -> FSP.upoisoned tfibsegs W mem' UP.
Proof.
intros ly S UP W mem md mem' D H OFF FR.
apply (FAR.upoisoned_keep UP W W mem mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem md H)).
intros s Hs. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s H Hs) as Rs.
apply FSP.aview_at. apply FR. rewrite (FSP.wz s Rs). intros HD.
pose proof (OFF s HD) as O. unfold FAR.offU in O. rewrite Z.mod_small in O by exact Rs. congruence.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. cache_dealloc (lib/A/AFg0.v): the region condition and the two transfers.                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the walk's seed regions (AFgk.REG0) and hyps record fix, and its write window AFgk.WIN: the stack, the
   thread object (cache counter, slot, junk word, drained source slots), the class's region info, the free-array
   slots a full drain writes, and the image's cells. *)
Definition cd_fixed (ly : alayout) (c cnt old a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (ly_T ly <= a < ly_T ly + kThreadObjSize) \/
  (AFgk.RGv ly c <= a < AFgk.RGv ly c + 128) \/
  (cnt = AFgk.MAXv c /\ AFgk.DSTv ly c old <= a < AFgk.DSTv ly c old + 4 * AFgk.Nv c) \/
  (TFIB_IMG_LO <= a < TFIB_IMG_END).

Lemma cdealloc_regions_off_ush : forall B ly S UP W mem md regs c off cnt old mf j80 j88 jst,
  FSP.ARU tfibsegs B ly S UP W mem md ->
  AFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  forall a, cd_fixed ly c cnt old a -> FAR.offU UP a.
Proof.
intros B ly S UP W mem md regs c off cnt old mf j80 j88 jst H FH a Ha.
pose proof FH as DR. apply AFgk.derived_ranges in DR.
pose proof FH as LB. apply AFgk.LYB in LB.
pose proof FH as KF. apply AFgk.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hfull _].
destruct Ha as [Hs|[Ht|[Hr|[[Hf Hd]|Hi]]]].
- exact (FAR.stack_offU B ly S UP W mem md a H Hs).
- destruct LB as (ZT & _). exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZT Ht).
- apply (FAR.offU_high B ly S UP W mem md a H). decompose [and] DR. ceil; unfold kHighMemBeg, ASAN_CEIL in *; lia.
- apply (FAR.offU_high B ly S UP W mem md a H). destruct (Hfull Hf) as (F1 & F2 & F3 & _). decompose [and] DR. decompose [and] KF.
  unfold AFgk.DSTv, AFgk.FAv in Hd. ceil; unfold kHighMemBeg, ASAN_CEIL, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *; lia.
- apply (FAR.offU_low B ly S UP W mem md a H). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *; lia.
Qed.

(* The write window is application memory (AFgk.v WIN_zone), outside the shadow band. *)
Lemma cd_WIN_band : forall W ly regs m c off cnt old mf j80 j88 jst,
  AFgk.free_hyps W ly regs m c off cnt old mf j80 j88 jst ->
  forall a, AFgk.WIN ly regs c cnt old a -> ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros W ly regs m c off cnt old mf j80 j88 jst FH a Ha.
eapply proj1. eapply proj2. eapply AFgk.WIN_zone; first [exact FH | exact Ha].
Qed.

(* Seed transfer: the walk's hyps record on the unpoisoned reading gives it on mem. *)
Lemma cd_hyps_real : forall W ly regs mem UP c off cnt old mf j80 j88 jst,
  AFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  (forall a, cd_fixed ly c cnt old a -> FAR.offU UP a) ->
  AFgk.free_hyps W ly regs mem c off cnt old mf j80 j88 jst.
Proof.
intros W ly regs mem UP c off cnt old mf j80 j88 jst FH OFF.
pose proof FH as DR. apply AFgk.derived_ranges in DR.
pose proof FH as KF. apply AFgk.class_facts in KF.
destruct FH as [LY IMG Htp Hra Hra4 Hsp Hal Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
assert (ST : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (RG : forall a, AFgk.RGv ly c <= a < AFgk.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (IM : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
decompose [and] DR. decompose [and] KF.
assert (RPC : 0 <= AFgk.PCv ly c < 2 ^ 64) by (nums; lia).
assert (RT : 0 <= ly_T ly < 2 ^ 64) by (nums; lia).
assert (RO : FAR.regions_offU UP (AFgk.E0 ly regs c off cnt old mf j80 j88 jst) (ss_mem AFgk.SS0)).
{ intros r a Hr Ha. unfold AFgk.SS0 in Hr. cbn [ss_mem] in Hr.
  unfold AFgk.REG0, AFgk.R_STK_HI, AFgk.R_STK_LO, AFgk.R_PC, AFgk.R_JST, fatom8, flit8, flit4 in Hr. cbn [In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
  rewrite ?AFgk.E2, ?AFgk.EqPC, ?AFgk.EqT in Ha; unfold w64 in Ha; rewrite ?(FSP.wz _ RPC), ?(FSP.wz _ RT) in Ha;
  first [apply ST; nums; lia | apply TH; nums; lia | apply IM; nums; lia]. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply ST; nums; lia | exact (Hpres a Ha)].
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply TH; nums; lia | exact (Hslot a Ha)].
- intros Hf. destruct (Hfull Hf) as (F1 & F2 & F3 & FP & V0 & V16 & V24 & V80 & V88 & FD & FS).
  assert (DS : forall a, AFgk.DSTv ly c old <= a < AFgk.DSTv ly c old + 4 * AFgk.Nv c -> FAR.offU UP a)
    by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
  refine (conj F1 (conj F2 (conj F3 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply RG; lia | exact (FP a Ha)].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact V0].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact V16].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact V24].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact V80].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact V88].
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply DS; exact Ha | exact (FD a Ha)].
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [|exact (FS a Ha)].
    apply TH. unfold AFgk.SRCv in Ha. nums. lia.
- exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ mem _ RO) SEED).
Qed.

(* Post transfer: the walk's post on mem' gives the post for unpoison UP mem', relative to the unpoisoned reading. *)
Lemma cd_post_mu : forall W ly regs mem md UP c off cnt old mf j80 j88 jst W' cfg',
  AFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  (forall a, cd_fixed ly c cnt old a -> FAR.offU UP a) ->
  AFgk.at_RETK W ly regs mem md c off cnt old mf W' cfg' ->
  exists regs' mem' mat, W' = W /\
    cfg' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    AFgk.at_RETK W ly regs (FSP.unpoison UP mem) md c off cnt old mf W
      (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    (forall x : word, ~ AFgk.WIN ly regs c cnt old (bv_unsigned x) -> mem' x = mem x).
Proof.
intros W ly regs mem md UP c off cnt old mf j80 j88 jst W' cfg' FH OFF HR.
pose proof FH as DR. apply AFgk.derived_ranges in DR.
pose proof FH as KF. apply AFgk.class_facts in KF.
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (RG : forall a, AFgk.RGv ly c <= a < AFgk.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (DS : cnt = AFgk.MAXv c -> forall a, AFgk.DSTv ly c old <= a < AFgk.DSTv ly c old + 4 * AFgk.Nv c -> FAR.offU UP a)
  by (intros Hf a Ha; apply OFF; unfold cd_fixed; tauto).
decompose [and] DR. decompose [and] KF.
destruct HR as (-> & regs' & mem' & mat & -> & CSP & CS & MEQ' & PRESW & VALS).
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact MEQ'].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat.
split; [reflexivity|]. split; [exact CSP|]. split; [exact CS|].
split. { intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ' x Hx)]. }
split. { intros a Ha. apply FAR.apresent_to_unpoison. exact (PRESW a Ha). }
cbv zeta in VALS |- *. destruct VALS as (V1 & V2 & VF).
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply TH; nums; lia | exact V1]|].
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply TH; nums; lia | exact V2]|].
intros Hf. destruct (VF Hf) as (R0 & R16 & R24 & CPY).
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply RG; lia | exact R0]|].
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply RG; lia | exact R16]|].
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply RG; lia | exact R24]|].
intros i v Hi Hv. apply FAR.val_mem_to_unpoison; [intros k Hk; apply (DS Hf); lia|].
apply (CPY i v Hi). apply (FAR.val_mem_of_unpoison _ UP); [|exact Hv].
intros k Hk. apply TH. unfold AFgk.SRCv. nums. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. recycle_chunk of a primary chunk (lib/A/AFg7.v): the region condition and the two transfers.                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the walk's seed regions (AFgs.REG0) and hyps record fix, and its write window AFgs.WIN: the stack, the
   thread object, the thread context, the class's region info, the chunk's extent (header, magic word), the shadow of
   the chunk's user granules, and the image's cells. *)
Definition rc_fixed (ly : alayout) (c base rz nn a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/
  (AFgs.RGv ly c <= a < AFgs.RGv ly c + 128) \/ (base <= a < base + AFgs.SZv c) \/
  (AFgs.SPv base rz <= a < AFgs.SPv base rz + AFgs.CNT8v nn) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END).

Lemma rchunk_prim_regions_off_ush : forall B ly X UP W mem md k regs c base rz nn hb1 cbp muc j1 j2,
  FSP.ARU tfibsegs B ly X UP W mem md -> In k (st_chunks X) -> ck_state k = CQuarantined ->
  ck_base B ly k = base -> ck_extent k = AFgs.SZv c ->
  AFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a.
Proof.
intros B ly X UP W mem md k regs c base rz nn hb1 cbp muc j1 j2 H Hk Hst Eb Ee FH a Ha.
pose proof FH as DR. apply AFgs.derived_ranges in DR.
pose proof FH as LB. apply AFgs.LYB in LB.
pose proof FH as KF. apply AFgs.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ _ _ _ _ _ _ Hrz _ _ _ _ _ _ _ _].
destruct Ha as [Hs|[Ht|[Hcc|[Hr|[Hx|[Hsh|Hi]]]]]].
- exact (FAR.stack_offU B ly X UP W mem md a H Hs).
- destruct LB as (ZT & _). exact (FK.offU_zone3 B ly X UP W mem md H _ _ a ZT Ht).
- destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZC & _). exact (FK.offU_zone3 B ly X UP W mem md H _ _ a ZC Hcc).
- apply (FAR.offU_high B ly X UP W mem md a H). decompose [and] DR. nums; lia.
- apply (FAR.offU_high B ly X UP W mem md a H). decompose [and] DR. decompose [and] KF. nums; lia.
- (* The shadow of the recycled chunk's user granules: the chunk is quarantined, and chunks are disjoint, so no live
     block meets those granules. *)
  decompose [and] DR. decompose [and] KF.
  assert (Ea : shadow_addr (8 * (a - SHADOW_OFF)) = a).
  { unfold shadow_addr. replace (8 * (a - SHADOW_OFF)) with ((a - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hin : base <= 8 * (a - SHADOW_OFF) < base + AFgs.SZv c).
  { (* lia does not see Z.div / Z.modulo here (FSupoisonIntrinR sets the euclidean-division flag of zify to false),
       so the granule arithmetic is made linear first. *)
    assert (EU : AFgs.Uv base rz = base + rz) by assumption.
    assert (UM : AFgs.Uv base rz mod 16 = 0) by assumption.
    assert (BM : base mod 16 = 0) by assumption.
    assert (EN : AFgs.N8v nn = 8 * AFgs.CNT8v nn) by assumption.
    assert (NB : nn <= AFgs.N8v nn < nn + 8) by (split; assumption).
    assert (UNB : AFgs.Uv base rz + nn <= base + AFgs.SZv c) by assumption.
    assert (SM : AFgs.SZv c mod 32 = 0) by assumption.
    apply Z.mod_divide in UM as [qu Hqu]; [|lia]. apply Z.mod_divide in BM as [qb Hqb]; [|lia].
    apply Z.mod_divide in SM as [qs Hqs]; [|lia].
    unfold AFgs.SPv in Hsh. rewrite Hqu in Hsh.
    replace (qu * 16 / 8) with (qu * 2) in Hsh by (replace (qu * 16) with (qu * 2 * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    destruct Hrz as (R1 & _ & R3). lia. }
  rewrite <- Ea. apply (FAR.offU_shadow_nonlive B ly X UP W mem md _ H); [nums; lia|].
  intros p n Hb' Hpn. apply In_ablocks in Hb' as (y & Hy & Hsy & Hu & Hn). subst p n.
  pose proof (FSP.ARU_ARm tfibsegs B ly X UP W mem md H) as M.
  pose proof (chunk_facts B ly X _ y M Hy) as (_ & _ & _ & G4 & _). rewrite G4 in Hpn.
  pose proof (user_in_extent B ly X _ y _ M Hy Hpn) as UE.
  assert (Hne : ck_beg y <> ck_beg k).
  { intros Eq. destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ (am_wf B ly X _ M))) as (l1 & l2 & E & N1 & N2).
    rewrite E in Hy. apply in_app_iff in Hy as [Y0|[<-|Y0]]; [apply N1 | rewrite Hst in Hsy; discriminate | apply N2];
    rewrite <- Eq; apply in_map; exact Y0. }
  pose proof (chunks_disjoint B ly X _ y k M Hy Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
  rewrite Eb, Ee in DJ. lia.
- apply (FAR.offU_low B ly X UP W mem md a H). nums; lia.
Qed.

Lemma rc_WIN_fixed : forall W ly regs m c base rz nn hb1 cbp muc j1 j2,
  AFgs.free_hyps W ly regs m c base rz nn hb1 cbp muc j1 j2 ->
  forall a, AFgs.WIN ly regs base rz nn a -> rc_fixed ly c base rz nn a.
Proof.
intros W ly regs m c base rz nn hb1 cbp muc j1 j2 FH a Hw.
pose proof FH as DR. apply AFgs.derived_ranges in DR.
pose proof FH as KF. apply AFgs.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ Hsp _ _ _ _ _ Hrz _ _ _ _ _ _ _ _].
unfold AFgs.WIN, AFgs.WINF, AFgs.WINS in Hw. unfold rc_fixed.
decompose [and] DR. decompose [and] KF. nums.
destruct Hw as [Hw|[[Hw|[[_ Hw]|Hw]]|Hw]].
- left. lia.
- right; right; right; right; left. lia.
- right; right; right; right; left. lia.
- right; left. lia.
- right; right; right; right; right; left. exact Hw.
Qed.

(* Seed transfer for recycle_chunk. *)
Lemma rc_hyps_real : forall W ly regs mem UP c base rz nn hb1 cbp muc j1 j2,
  AFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  (forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a) ->
  AFgs.free_hyps W ly regs mem c base rz nn hb1 cbp muc j1 j2.
Proof.
intros W ly regs mem UP c base rz nn hb1 cbp muc j1 j2 FH OFF.
pose proof FH as DR. apply AFgs.derived_ranges in DR.
pose proof FH as KF. apply AFgs.class_facts in KF.
destruct FH as [LY IMG Htp Hra Hra4 Hsp Hal Hpres Hcb Hc Hbase Hrz Hnn Hhb1 Hhdr Hmag Hshp Hrg Hjunk SEED].
assert (ST : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (CC : forall a, ly_C ly <= a < ly_C ly + 256 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (RG : forall a, AFgs.RGv ly c <= a < AFgs.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (CK : forall a, base <= a < base + AFgs.SZv c -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (SH : forall a, AFgs.SPv base rz <= a < AFgs.SPv base rz + AFgs.CNT8v nn -> FAR.offU UP a)
  by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (IM : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
decompose [and] DR. decompose [and] KF.
destruct Hcb as (C1 & C2 & C3 & C4 & C5).
assert (RCB : 0 <= cbp < 2 ^ 64) by (nums; lia).
assert (RM : 0 <= AFgs.Mv base rz < 2 ^ 64) by (nums; lia).
assert (RRG : 0 <= AFgs.RGv ly c < 2 ^ 64) by (nums; lia).
assert (RC : 0 <= ly_C ly < 2 ^ 64) by (nums; lia).
assert (RT : 0 <= ly_T ly < 2 ^ 64) by (nums; lia).
assert (RO : FAR.regions_offU UP (AFgs.E0 ly regs c base rz nn hb1 cbp muc j1 j2) (ss_mem AFgs.SS0)).
{ intros r a Hr Ha. unfold AFgs.SS0 in Hr. cbn [ss_mem] in Hr.
  unfold AFgs.REG0, AFgs.R_STK, AFgs.R_CB, AFgs.R_HDR, AFgs.R_RGMU, AFgs.R_CTX, AFgs.R_JST, flit1, flit4, flit8, flits8, fatom8 in Hr.
  cbn [In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
  rewrite ?AFgs.E2, ?AFgs.EqCBP, ?AFgs.EqM, ?AFgs.EqRG, ?AFgs.EqC, ?AFgs.EqT in Ha; unfold w64 in Ha;
  rewrite ?(FSP.wz _ RCB), ?(FSP.wz _ RM), ?(FSP.wz _ RRG), ?(FSP.wz _ RC), ?(FSP.wz _ RT) in Ha;
  first [apply ST; nums; lia | apply TH; nums; lia | apply CC; nums; lia | apply RG; nums; lia | apply CK; unfold AFgs.Mv in *; nums; lia
        | apply IM; nums; lia]. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply ST; nums; lia | exact (Hpres a Ha)].
- refine (conj C1 (conj C2 (conj C3 (conj _ _)))).
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply ST; nums; lia | exact (C4 a Ha)].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply ST; nums; lia | exact C5].
- destruct Hhdr as (HD1 & HD2 & HD3). split; [|split].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply CK; nums; lia | exact HD1].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply CK; nums; lia | exact HD2].
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply CK; exact Ha | exact (HD3 a Ha)].
- intros Hne. apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply CK; nums; lia | exact (Hmag Hne)].
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply SH; exact Ha | exact (Hshp a Ha)].
- destruct Hrg as [RG1 RG2]. split.
  + intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply RG; lia | exact (RG1 a Ha)].
  + apply (FAR.val_mem_of_unpoison _ UP); [intros k Hk; apply RG; lia | exact RG2].
- exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ mem _ RO) SEED).
Qed.

(* Post transfer for recycle_chunk (the configuration at the cache_dealloc call). *)
Lemma rc_post_mu : forall W ly regs mem md UP c base rz nn hb1 cbp muc j1 j2 W' cfg',
  AFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  (forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a) ->
  AFgs.at_CD W ly regs mem md c base rz nn hb1 W' cfg' ->
  exists regs' mem' mat, W' = W /\
    cfg' = cfg_at tfibsegs A_CDealloc regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
    AFgs.at_CD W ly regs (FSP.unpoison UP mem) md c base rz nn hb1 W
      (cfg_at tfibsegs A_CDealloc regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)) /\
    (forall x : word, ~ AFgs.WIN ly regs base rz nn (bv_unsigned x) -> mem' x = mem x).
Proof.
intros W ly regs mem md UP c base rz nn hb1 cbp muc j1 j2 W' cfg' FH OFF HCD.
pose proof FH as DR. apply AFgs.derived_ranges in DR.
pose proof FH as KF. apply AFgs.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ _ _ _ _ _ _ Hrz _ _ _ _ _ _ _ _].
assert (CK : forall a, base <= a < base + AFgs.SZv c -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (SH : forall a, AFgs.SPv base rz <= a < AFgs.SPv base rz + AFgs.CNT8v nn -> FAR.offU UP a)
  by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
decompose [and] DR. decompose [and] KF.
destruct HCD as (-> & regs' & mem' & mat & -> & CSP & CRA & CS & C10 & C11 & C12 & C13 & MEQ' & PRESW & VALS).
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact MEQ'].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
split; [exact CSP|]. split; [exact CRA|]. split; [exact CS|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|].
split; [exact C13|].
split. { intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQ' x Hx)]. }
split. { intros a Ha. apply FAR.apresent_to_unpoison. exact (PRESW a Ha). }
cbv zeta in VALS |- *. destruct VALS as (V1 & V2 & VS).
split; [apply FAR.val_mem_to_unpoison; [intros k Hk; apply CK; nums; lia | exact V1]|].
split; [intros Hne; apply FAR.val_mem_to_unpoison; [intros k Hk; apply CK; nums; lia | exact (V2 Hne)]|].
intros i Hi. unfold w64 in *. rewrite (FAR.unpoison_offU UP mem' (AFgs.SPv base rz + i)); [exact (VS i Hi) | apply SH; lia].
Qed.
(*PART2*)

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The two walks (the donor arms lib/A/AFg0.v:290 and lib/A/AFg7.v:294, with the U steps above).                  *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem tfib_cdealloc_okU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly X c off UP W regs mem md,
  FK.cd_preU B ly X c off UP W regs mem md -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (FK.cd_leafU B ly X UP W regs mem md).
Proof.
intros B LAWS TB ly X c off UP W regs mem md PREU HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (FAR.ARU_intro B ly X UP W mem md (proj1 PRE) OKU POU) as HU.
pose proof PRE as (_ & Hci & Hcc & Hx & Hxm & _ & HROOM & _).
rewrite (AFez.cache_dealloc_S' B ly X (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) (proj1 (proj1 PRE)) c off Hci Hcc Hx Hxm HROOM).
cbn [amreal].
destruct (AFfi.junk_vals B ly X c off W regs (FSP.unpoison UP mem) md PRE) as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (AFfi.FH_ok B TB ly X c off W regs (FSP.unpoison UP mem) md PRE j80 j88 jst HJ80 HJ88 HJST) as FHu.
pose proof (AFfi.reg_facts B ly X c off W regs (FSP.unpoison UP mem) md PRE) as RFx.
pose proof (cdealloc_regions_off_ush B ly X UP W mem md regs c off _ _ _ j80 j88 jst HU FHu) as OFF.
pose proof (cd_hyps_real W ly regs mem UP c off _ _ _ j80 j88 jst FHu OFF) as FH.
assert (ECH : st_chunks (AFez.S' X c off) = st_chunks X) by (unfold AFez.S', AFez.X1; destruct (AFez.full X c); reflexivity).
assert (FINKHU : forall W' c', AFgk.at_RETK W ly regs mem md c off (AFfi.kcnt X c) (AFfi.kold X c) (AFfi.kmf X c) W' c' ->
  FK.cd_leafU B ly X UP W regs mem md (tt, AFez.S' X c off) W' c').
{ intros W' c' HR.
  destruct (cd_post_mu W ly regs mem md UP c off _ _ _ j80 j88 jst W' c' FHu OFF HR) as (regs' & mem' & mat & -> & -> & HRu & MEQ').
  pose proof (AFg0.FINKH B TB ly X c off W regs (FSP.unpoison UP mem) md PRE HTSD W _ HRu) as LF.
  rewrite cfg_ra in LF |- *.
  apply (FK.cd_leafU_intro B ly X UP W regs mem md _ W regs' mem' _ LF).
  - exact (upoison_ok_chunks B ly X _ UP OKU ECH).
  - exact (FK.upoisoned_frame B ly X UP W mem md HU mem' (AFgk.WIN ly regs c (AFfi.kcnt X c) (AFfi.kold X c))
      (cd_WIN_band _ _ _ _ _ _ _ _ _ _ _ _ FHu) MEQ').
  - (* The run keeps mem off AFgk.WIN (MEQ'); each byte of AFgk.WIN is in the donor's window AFez.D (AFg0.WIN_D),
       so it is owned by X or in the call's stack window (AFez.D_owned). *)
    pose proof (AFfi.HSP B ly X c off W regs (FSP.unpoison UP mem) md PRE) as HSP0. cbv zeta in HSP0.
    apply (FK.raw_of_meq B ly X _ KSTACK regs (fun _ => False) _ mem mem' MEQ').
    intros a Ha Hw.
    destruct (AFez.D_owned B ly X _ (proj1 (proj1 PRE)) c off Hci Hcc Hx Hxm HROOM _ HSP0
      (AFfi.IMG B ly X c off W regs (FSP.unpoison UP mem) md PRE) a (proj1 Ha) (AFg0.WIN_D ly X c regs a Hw)) as [O|O];
      [left; exact O | right; left; exact O]. }
unfold cfg_at, A_CDealloc. rewrite <- (AFg0.wvb_self md) at 1.
eapply SRr_mono; [| intros W' c' _ HR; exact (FINKHU W' c' HR)].
destruct (Z_lt_le_dec (AFfi.kcnt X c) (AFgk.MAXv c)) as [LT|GE].
- exact (AFgy.segK1 W ly regs mem md c off _ _ _ j80 j88 jst (m_vm_materialized md) FH LT).
- apply (AFgz.segK2 W ly regs mem md c off _ _ _ j80 j88 jst (m_vm_materialized md) FH). clear - RFx GE. unfold AFgk.MAXv in *. lia.
Qed.

Theorem tfib_rchunk_primU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly X k cbp UP W regs mem md off,
  FK.rcc_preU B ly X k cbp UP W regs mem md -> ck_beg k = PPrim off -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (FK.rcc_leafU B ly X k UP W regs mem md).
Proof.
intros B LAWS TB ly X k cbp UP W regs mem md off PREU Hb HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (FAR.ARU_intro B ly X UP W mem md (proj1 PRE) OKU POU) as HU.
pose proof PRE as (_ & _ & Hk & Hst & _).
pose proof (AFfr.geom B ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb) as GE.
assert (EXT : ck_extent k = AFgs.SZv (AFfr.rcl off)) by (decompose [and] GE; assumption).
pose proof (AFfr.FH_ok B TB ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb HTSD) as FHu.
pose proof (rchunk_prim_regions_off_ush B ly X UP W mem md k regs (AFfr.rcl off) (AFfr.rbase B ly k) (AFfr.rrz k) (AFfr.rnn k)
  (AFfr.hb1 B ly k W (FSP.unpoison UP mem)) cbp (AFfr.rmuc X off) (AFfr.j1 ly W (FSP.unpoison UP mem)) (AFfr.j2 ly W (FSP.unpoison UP mem))
  HU Hk Hst eq_refl EXT FHu) as OFF.
pose proof (rc_hyps_real W ly regs mem UP _ _ _ _ _ _ _ _ _ FHu OFF) as FH.
rewrite (AFg7.recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (AFg0.wvb_self md) at 1.
eapply (amreal_SRr_pre tfibsegs _ _ _ _
  (AFgs.at_CD W ly regs mem md (AFfr.rcl off) (AFfr.rbase B ly k) (AFfr.rrz k) (AFfr.rnn k) (AFfr.hb1 B ly k W (FSP.unpoison UP mem)))).
{ exact (AFh7.segRC W ly regs mem md _ _ _ _ _ cbp _ _ _ (m_vm_materialized md) FH). }
intros W' c' _ HCD.
destruct (rc_post_mu W ly regs mem md UP _ _ _ _ _ cbp _ _ _ W' c' FHu OFF HCD) as (regs1 & mem1 & mat & -> & -> & HCDu & MEQ1).
destruct (AFg7.CDPRE B TB ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb HTSD W _ HCDu)
  as (regs' & mem' & mat' & _ & Ec & PRE' & R2 & R1 & RS & FR & PUF).
apply FK.cfg_at_inj in Ec as (Er & Em & Ed). subst regs' mem'. rewrite <- Ed in PRE'.
assert (OKX1 : FSP.upoison_ok B ly (AFf3.X1 X k) UP).
{ exact (upoison_ok_del_quar B ly X (AFf3.X1 X k) UP k OKU Hk Hst (wf_chunks_nodup _ _ _ _ _ (am_wf B ly X _ (proj1 (proj1 PRE)))) eq_refl). }
assert (PO1 : FSP.upoisoned tfibsegs W mem1 UP).
{ exact (upoisoned_frame_off B ly X UP W mem md mem1 (AFgs.WIN ly regs (AFfr.rbase B ly k) (AFfr.rrz k) (AFfr.rnn k)) HU
    (fun a Ha => OFF a (rc_WIN_fixed _ _ _ _ _ _ _ _ _ _ _ _ _ FHu a Ha)) MEQ1). }
eapply amreal_mono; [| exact (tfib_cdealloc_okU B LAWS TB ly (AFf3.X1 X k) (AFfr.rcl off) off UP W regs1 mem1 _ (conj PRE' (conj OKX1 PO1)) HTSD)].
cbv beta. intros [[] S''] W'' c'' HL. destruct HL as (regs'' & mem'' & md'' & -> & (AP & OK'' & PO'') & UF & CI & RAWc).
(* The raw frame: mem -> mem1 by the run's frame MEQ1, each byte of AFgs.WIN being in the donor's window AFf3.D
   (AFg7.WIN_D), so owned by X or in the call's stack window (AFf3.D_owned); mem1 -> mem'' by cache_dealloc's raw frame
   at regs1, whose sp is regs' (R2), from AFf3.X1 X k, which owns what X owns (AFf3.aowned_X1). *)
assert (RAWr : forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly S'' (bv_unsigned x) ->
  ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem'' x = mem x).
{ pose proof PRE as PRE2. destruct PRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in Hlo, Hcb1.
  assert (HSP0 : ly_stk_lo ly + KSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly) by (clear - Hlo Hcb1 Hcb2; lia).
  assert (OWN1 : forall a, aowned B ly (AFf3.X1 X k) a -> aowned B ly X a).
  { intros a O1. exact (proj1 (AFf3.aowned_X1 B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb (bv_unsigned (YK11.getr regs 2)) HSP0 a) O1). }
  assert (RAW1 : forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (AFf3.X1 X k) (bv_unsigned x) ->
    ~ ascratch B KSTACK regs (bv_unsigned x) -> mem1 x = mem x).
  { intros x N0 N1 NS.
    apply (FK.raw_of_meq B ly X (AFf3.X1 X k) KSTACK regs (fun _ => False) _ mem mem1 MEQ1); [| exact N0 | exact N1 | exact NS | intros F; exact F].
    intros a Ha Hw.
    destruct (AFf3.D_owned B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb _ HSP0 a (proj1 Ha)
      (AFg7.WIN_D B ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb a Hw)) as [O|O]; [left; exact O | right; left; exact O]. }
  intros x N0 N2 NS _.
  apply (FK.raw_trans B ly X (AFf3.X1 X k) S'' (ascratch B KSTACK regs) (ascratch B KSTACK regs) mem mem1 mem'' OWN1 (fun a Ha => Ha) RAW1);
    [| exact N0 | exact N2 | exact NS].
  intros y N1 N2' NS'. apply (RAWc y N1 N2'); [| intros F; exact F]. unfold ascratch, spZ in NS' |- *. rewrite R2. exact NS'. }
assert (Ec2 : cfg_at tfibsegs (raZ regs1) regs'' mem'' md'' = cfg_at tfibsegs (raZ regs) regs'' mem'' md'') by (unfold cfg_at, raZ; rewrite R1; reflexivity).
rewrite Ec2.
apply (FK.rcc_leafU_intro B ly X k UP W regs mem md (tt, S'') W'' regs'' mem'' md''); [| exact OK'' | exact PO'' | exact RAWr].
exists regs'', (FSP.unpoison UP mem''), md''. split; [reflexivity|].
split.
2:{ split; [|exact CI]. intros a Ha PU NK. rewrite (UF a Ha) by exact PU. exact (PUF a Ha PU NK). }
destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS). unfold acall_post. unfold spZ in *. rewrite R2 in PRS.
split; [exact AR''|]. split; [exact LLE|]. split; [exact WLE|]. split.
{ intros r Hr. rewrite (RP r Hr). unfold acallee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct R as [->|R]; [exact R2|]. apply RS. clear - R. unfold AFgs.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split. { pose proof (AFg0.same_io_wvb md mat) as IO1. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
split.
{ pose proof PRE as PRE2. destruct PRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in Hlo, Hcb1.
assert (HSP0 : ly_stk_lo ly + KSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly) by (clear - Hlo Hcb1 Hcb2; lia).
intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [apply FR; [exact Ha | exact NO | exact NS] | | exact NO' | unfold ascratch, spZ in *; rewrite R2; exact NS | exact NE].
intros O1. apply NO. exact (proj1 (AFf3.aowned_X1 B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb (bv_unsigned (YK11.getr regs 2)) HSP0 a) O1). }
exact PRS.
Qed.
(*END-PART2*)
End t.
