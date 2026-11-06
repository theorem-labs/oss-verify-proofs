(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFg7.v, with its module paths and module names changed; 385 of its 432 lines of code are new or changed and 274 lines of the source are left out. *)
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
   - region condition: cd_fixed / rc_fixed are the bytes whose value or presence is transferred plus the write window;
     cdealloc_regions_off_ush / rchunk_prim_regions_off_ush put them off U: application memory (stack, thread
     object, thread context, region info, free array, the chunk's extent, the image) and, for recycle_chunk, the
     shadow of the recycled chunk's user granules, which no live block meets. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFcd.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFew YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFgk YFgs.
(*PART2-REQUIRE*)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFgy YFgz YFh7 YFfi YFfr YFez YFf3 YFg0 YFg7.
(*END-PART2-REQUIRE*)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK.
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
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.
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
(* 2. cache_dealloc (lib/B/YFg0.v): the region condition and the two transfers.                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the walk's seed regions (YFgk.REG0) and hyps record fix, and its write window YFgk.WIN: the stack, the
   thread object (cache counter, slot, junk word, drained source slots), the class's region info, the free-array
   slots a full drain writes, and the image's cells. *)
Definition cd_fixed (ly : alayout) (c cnt old a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (ly_T ly <= a < ly_T ly + kThreadObjSize) \/
  (YFgk.RGv ly c <= a < YFgk.RGv ly c + 128) \/
  (cnt = YFgk.MAXv c /\ YFgk.DSTv ly c old <= a < YFgk.DSTv ly c old + 4 * YFgk.Nv c) \/
  (TFIB_IMG_LO <= a < TFIB_IMG_END).

Lemma cdealloc_regions_off_ush : forall B ly S UP W mem md regs c off cnt old mf j80 j88 jst,
  FSP.ARU tfibsegs B ly S UP W mem md ->
  YFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  forall a, cd_fixed ly c cnt old a -> FAR.offU UP a.
Proof.
intros B ly S UP W mem md regs c off cnt old mf j80 j88 jst H FH a Ha.
pose proof FH as DR. apply YFgk.derived_ranges in DR.
pose proof FH as LB. apply YFgk.LYB in LB.
pose proof FH as KF. apply YFgk.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ _ _ _ _ _ _ _ _ Hfull _].
destruct Ha as [Hs|[Ht|[Hr|[[Hf Hd]|Hi]]]].
- exact (FAR.stack_offU B ly S UP W mem md a H Hs).
- destruct LB as (ZT & _). exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZT Ht).
- apply (FAR.offU_high B ly S UP W mem md a H). decompose [and] DR. ceil; unfold kHighMemBeg, ASAN_CEIL in *; lia.
- apply (FAR.offU_high B ly S UP W mem md a H). destruct (Hfull Hf) as (F1 & F2 & F3 & _). decompose [and] DR. decompose [and] KF.
  unfold YFgk.DSTv, YFgk.FAv in Hd. ceil; unfold kHighMemBeg, ASAN_CEIL, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *; lia.
- apply (FAR.offU_low B ly S UP W mem md a H). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *; lia.
Qed.

(* The write window is application memory (YFgk.v WIN_zone), outside the shadow band. *)
Lemma cd_WIN_band : forall W ly regs m c off cnt old mf j80 j88 jst,
  YFgk.free_hyps W ly regs m c off cnt old mf j80 j88 jst ->
  forall a, YFgk.WIN ly regs c cnt old a -> ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros W ly regs m c off cnt old mf j80 j88 jst FH a Ha.
eapply proj1. eapply proj2. eapply YFgk.WIN_zone; first [exact FH | exact Ha].
Qed.

(* Seed transfer: the walk's hyps record on the unpoisoned reading gives it on mem. *)
Lemma cd_hyps_real : forall W ly regs mem UP c off cnt old mf j80 j88 jst,
  YFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  (forall a, cd_fixed ly c cnt old a -> FAR.offU UP a) ->
  YFgk.free_hyps W ly regs mem c off cnt old mf j80 j88 jst.
Proof.
intros W ly regs mem UP c off cnt old mf j80 j88 jst FH OFF.
pose proof FH as DR. apply YFgk.derived_ranges in DR.
pose proof FH as KF. apply YFgk.class_facts in KF.
destruct FH as [LY IMG Htp Hra Hra4 Hsp Hal Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
assert (ST : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (RG : forall a, YFgk.RGv ly c <= a < YFgk.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (IM : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
decompose [and] DR. decompose [and] KF.
assert (RPC : 0 <= YFgk.PCv ly c < 2 ^ 64) by (nums; lia).
assert (RT : 0 <= ly_T ly < 2 ^ 64) by (nums; lia).
assert (RO : FAR.regions_offU UP (YFgk.E0 ly regs c off cnt old mf j80 j88 jst) (ss_mem YFgk.SS0)).
{ intros r a Hr Ha. unfold YFgk.SS0 in Hr. cbn [ss_mem] in Hr.
  unfold YFgk.REG0, YFgk.R_STK_HI, YFgk.R_STK_LO, YFgk.R_PC, YFgk.R_JST, fatom8, flit8, flit4 in Hr. cbn [In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
  rewrite ?YFgk.E2, ?YFgk.EqPC, ?YFgk.EqT in Ha; unfold w64 in Ha; rewrite ?(FSP.wz _ RPC), ?(FSP.wz _ RT) in Ha;
  first [apply ST; nums; lia | apply TH; nums; lia | apply IM; nums; lia]. }
constructor; try assumption.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply ST; nums; lia | exact (Hpres a Ha)].
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [apply TH; nums; lia | exact (Hslot a Ha)].
- intros Hf. destruct (Hfull Hf) as (F1 & F2 & F3 & FP & V0 & V16 & V24 & V80 & V88 & FD & FS).
  assert (DS : forall a, YFgk.DSTv ly c old <= a < YFgk.DSTv ly c old + 4 * YFgk.Nv c -> FAR.offU UP a)
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
    apply TH. unfold YFgk.SRCv in Ha. nums. lia.
- exact (proj1 (FAR.st_ok_unpoison_iff UP _ _ _ _ _ mem _ RO) SEED).
Qed.

(* Post transfer: the walk's post on mem' gives the post for unpoison UP mem', relative to the unpoisoned reading. *)
Lemma cd_post_mu : forall W ly regs mem md UP c off cnt old mf j80 j88 jst W' cfg',
  YFgk.free_hyps W ly regs (FSP.unpoison UP mem) c off cnt old mf j80 j88 jst ->
  (forall a, cd_fixed ly c cnt old a -> FAR.offU UP a) ->
  YFgk.at_RETK W ly regs mem md c off cnt old mf W' cfg' ->
  exists regs' mem' mat, W' = W /\
    cfg' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    YFgk.at_RETK W ly regs (FSP.unpoison UP mem) md c off cnt old mf W
      (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    (forall x : word, ~ YFgk.WIN ly regs c cnt old (bv_unsigned x) -> mem' x = mem x).
Proof.
intros W ly regs mem md UP c off cnt old mf j80 j88 jst W' cfg' FH OFF HR.
pose proof FH as DR. apply YFgk.derived_ranges in DR.
pose proof FH as KF. apply YFgk.class_facts in KF.
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (RG : forall a, YFgk.RGv ly c <= a < YFgk.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold cd_fixed; tauto).
assert (DS : cnt = YFgk.MAXv c -> forall a, YFgk.DSTv ly c old <= a < YFgk.DSTv ly c old + 4 * YFgk.Nv c -> FAR.offU UP a)
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
intros k Hk. apply TH. unfold YFgk.SRCv. nums. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. recycle_chunk of a primary chunk (lib/B/YFg7.v): the region condition and the two transfers.                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the walk's seed regions (YFgs.REG0) and hyps record fix, and its write window YFgs.WIN: the stack, the
   thread object, the thread context, the class's region info, the chunk's extent (header, magic word), the shadow of
   the chunk's user granules, and the image's cells. *)
Definition rc_fixed (ly : alayout) (c base rz nn a : Z) : Prop :=
  (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/
  (YFgs.RGv ly c <= a < YFgs.RGv ly c + 128) \/ (base <= a < base + YFgs.SZv c) \/
  (YFgs.SPv base rz <= a < YFgs.SPv base rz + YFgs.CNT8v nn) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END).

Lemma rchunk_prim_regions_off_ush : forall B ly X UP W mem md k regs c base rz nn hb1 cbp muc j1 j2,
  FSP.ARU tfibsegs B ly X UP W mem md -> In k (st_chunks X) -> ck_state k = CQuarantined ->
  ck_base B ly k = base -> ck_extent k = YFgs.SZv c ->
  YFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a.
Proof.
intros B ly X UP W mem md k regs c base rz nn hb1 cbp muc j1 j2 H Hk Hst Eb Ee FH a Ha.
pose proof FH as DR. apply YFgs.derived_ranges in DR.
pose proof FH as LB. apply YFgs.LYB in LB.
pose proof FH as KF. apply YFgs.class_facts in KF.
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
  assert (Hin : base <= 8 * (a - SHADOW_OFF) < base + YFgs.SZv c).
  { (* lia does not see Z.div / Z.modulo here (FSupoisonIntrinR sets the euclidean-division flag of zify to false),
       so the granule arithmetic is made linear first. *)
    assert (EU : YFgs.Uv base rz = base + rz) by assumption.
    assert (UM : YFgs.Uv base rz mod 16 = 0) by assumption.
    assert (BM : base mod 16 = 0) by assumption.
    assert (EN : YFgs.N8v nn = 8 * YFgs.CNT8v nn) by assumption.
    assert (NB : nn <= YFgs.N8v nn < nn + 8) by (split; assumption).
    assert (UNB : YFgs.Uv base rz + nn <= base + YFgs.SZv c) by assumption.
    assert (SM : YFgs.SZv c mod 32 = 0) by assumption.
    apply Z.mod_divide in UM as [qu Hqu]; [|lia]. apply Z.mod_divide in BM as [qb Hqb]; [|lia].
    apply Z.mod_divide in SM as [qs Hqs]; [|lia].
    unfold YFgs.SPv in Hsh. rewrite Hqu in Hsh.
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
  YFgs.free_hyps W ly regs m c base rz nn hb1 cbp muc j1 j2 ->
  forall a, YFgs.WIN ly regs base rz nn a -> rc_fixed ly c base rz nn a.
Proof.
intros W ly regs m c base rz nn hb1 cbp muc j1 j2 FH a Hw.
pose proof FH as DR. apply YFgs.derived_ranges in DR.
pose proof FH as KF. apply YFgs.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ Hsp _ _ _ _ _ Hrz _ _ _ _ _ _ _ _].
unfold YFgs.WIN, YFgs.WINF, YFgs.WINS in Hw. unfold rc_fixed.
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
  YFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  (forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a) ->
  YFgs.free_hyps W ly regs mem c base rz nn hb1 cbp muc j1 j2.
Proof.
intros W ly regs mem UP c base rz nn hb1 cbp muc j1 j2 FH OFF.
pose proof FH as DR. apply YFgs.derived_ranges in DR.
pose proof FH as KF. apply YFgs.class_facts in KF.
destruct FH as [LY IMG Htp Hra Hra4 Hsp Hal Hpres Hcb Hc Hbase Hrz Hnn Hhb1 Hhdr Hmag Hshp Hrg Hjunk SEED].
assert (ST : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (TH : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (CC : forall a, ly_C ly <= a < ly_C ly + 256 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (RG : forall a, YFgs.RGv ly c <= a < YFgs.RGv ly c + 128 -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (CK : forall a, base <= a < base + YFgs.SZv c -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (SH : forall a, YFgs.SPv base rz <= a < YFgs.SPv base rz + YFgs.CNT8v nn -> FAR.offU UP a)
  by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (IM : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
decompose [and] DR. decompose [and] KF.
destruct Hcb as (C1 & C2 & C3 & C4 & C5).
assert (RCB : 0 <= cbp < 2 ^ 64) by (nums; lia).
assert (RM : 0 <= YFgs.Mv base rz < 2 ^ 64) by (nums; lia).
assert (RRG : 0 <= YFgs.RGv ly c < 2 ^ 64) by (nums; lia).
assert (RC : 0 <= ly_C ly < 2 ^ 64) by (nums; lia).
assert (RT : 0 <= ly_T ly < 2 ^ 64) by (nums; lia).
assert (RO : FAR.regions_offU UP (YFgs.E0 ly regs c base rz nn hb1 cbp muc j1 j2) (ss_mem YFgs.SS0)).
{ intros r a Hr Ha. unfold YFgs.SS0 in Hr. cbn [ss_mem] in Hr.
  unfold YFgs.REG0, YFgs.R_STK, YFgs.R_CB, YFgs.R_HDR, YFgs.R_RGMU, YFgs.R_CTX, YFgs.R_JST, flit1, flit4, flit8, flits8, fatom8 in Hr.
  cbn [In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
  rewrite ?YFgs.E2, ?YFgs.EqCBP, ?YFgs.EqM, ?YFgs.EqRG, ?YFgs.EqC, ?YFgs.EqT in Ha; unfold w64 in Ha;
  rewrite ?(FSP.wz _ RCB), ?(FSP.wz _ RM), ?(FSP.wz _ RRG), ?(FSP.wz _ RC), ?(FSP.wz _ RT) in Ha;
  first [apply ST; nums; lia | apply TH; nums; lia | apply CC; nums; lia | apply RG; nums; lia | apply CK; unfold YFgs.Mv in *; nums; lia
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
  YFgs.free_hyps W ly regs (FSP.unpoison UP mem) c base rz nn hb1 cbp muc j1 j2 ->
  (forall a, rc_fixed ly c base rz nn a -> FAR.offU UP a) ->
  YFgs.at_CD W ly regs mem md c base rz nn hb1 W' cfg' ->
  exists regs' mem' mat, W' = W /\
    cfg' = cfg_at tfibsegs A_CDealloc regs' mem' (with_vm_backing (m_vm_lazy md) mat md) /\
    YFgs.at_CD W ly regs (FSP.unpoison UP mem) md c base rz nn hb1 W
      (cfg_at tfibsegs A_CDealloc regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)) /\
    (forall x : word, ~ YFgs.WIN ly regs base rz nn (bv_unsigned x) -> mem' x = mem x).
Proof.
intros W ly regs mem md UP c base rz nn hb1 cbp muc j1 j2 W' cfg' FH OFF HCD.
pose proof FH as DR. apply YFgs.derived_ranges in DR.
pose proof FH as KF. apply YFgs.class_facts in KF.
pose proof FH as FH'. destruct FH' as [_ _ _ _ _ _ _ _ _ _ _ Hrz _ _ _ _ _ _ _ _].
assert (CK : forall a, base <= a < base + YFgs.SZv c -> FAR.offU UP a) by (intros a Ha; apply OFF; unfold rc_fixed; tauto).
assert (SH : forall a, YFgs.SPv base rz <= a < YFgs.SPv base rz + YFgs.CNT8v nn -> FAR.offU UP a)
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
intros i Hi. unfold w64 in *. rewrite (FAR.unpoison_offU UP mem' (YFgs.SPv base rz + i)); [exact (VS i Hi) | apply SH; lia].
Qed.
(*PART2*)

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The two walks (the donor arms lib/B/YFg0.v:288 and lib/B/YFg7.v:292, with the U steps above).                  *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem tfib_cdealloc_okU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly X c off UP W regs mem md,
  FK.cd_preU B ly X c off UP W regs mem md -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (FK.cd_leafU B ly X UP W regs mem md).
Proof.
intros B LAWS TB ly X c off UP W regs mem md PREU HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (FAR.ARU_intro B ly X UP W mem md (proj1 PRE) OKU POU) as HU.
pose proof PRE as (_ & Hci & Hcc & Hx & Hxm & _ & HROOM & _).
rewrite (YFez.cache_dealloc_S' B ly X (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) (proj1 (proj1 PRE)) c off Hci Hcc Hx Hxm HROOM).
cbn [amreal].
destruct (YFfi.junk_vals B ly X c off W regs (FSP.unpoison UP mem) md PRE) as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (YFfi.FH_ok B TB ly X c off W regs (FSP.unpoison UP mem) md PRE j80 j88 jst HJ80 HJ88 HJST) as FHu.
pose proof (YFfi.reg_facts B ly X c off W regs (FSP.unpoison UP mem) md PRE) as RFx.
pose proof (cdealloc_regions_off_ush B ly X UP W mem md regs c off _ _ _ j80 j88 jst HU FHu) as OFF.
pose proof (cd_hyps_real W ly regs mem UP c off _ _ _ j80 j88 jst FHu OFF) as FH.
assert (ECH : st_chunks (YFez.S' X c off) = st_chunks X) by (unfold YFez.S', YFez.X1; destruct (YFez.full X c); reflexivity).
assert (FINKHU : forall W' c', YFgk.at_RETK W ly regs mem md c off (YFfi.kcnt X c) (YFfi.kold X c) (YFfi.kmf X c) W' c' ->
  FK.cd_leafU B ly X UP W regs mem md (tt, YFez.S' X c off) W' c').
{ intros W' c' HR.
  destruct (cd_post_mu W ly regs mem md UP c off _ _ _ j80 j88 jst W' c' FHu OFF HR) as (regs' & mem' & mat & -> & -> & HRu & MEQ').
  pose proof (YFg0.FINKH B TB ly X c off W regs (FSP.unpoison UP mem) md PRE HTSD W _ HRu) as LF.
  rewrite cfg_ra in LF |- *.
  apply (FK.cd_leafU_intro B ly X UP W regs mem md _ W regs' mem' _ LF).
  - exact (upoison_ok_chunks B ly X _ UP OKU ECH).
  - exact (FK.upoisoned_frame B ly X UP W mem md HU mem' (YFgk.WIN ly regs c (YFfi.kcnt X c) (YFfi.kold X c))
      (cd_WIN_band _ _ _ _ _ _ _ _ _ _ _ _ FHu) MEQ').
  - (* the raw frame: cache_dealloc's window (YFgk.WIN) is in YFez.D (YFg0.WIN_D), owned by X or in the stack scratch
       (YFez.D_owned) *)
    apply (FK.raw_of_meq (YFgk.WIN ly regs c (YFfi.kcnt X c) (YFfi.kold X c)) (aowned B ly X)
      (aowned B ly (snd (tt, YFez.S' X c off))) (ascratch B KSTACK regs) (fun _ => False) mem mem' MEQ').
    intros a Ha Hw.
    assert (HD : YFez.D ly X c (bv_unsigned (YK11.getr regs 2)) a)
      by (eapply YFg0.WIN_D; first [exact Hw | exact PRE | exact HTSD | exact TB]).
    destruct (YFez.D_owned B ly X _ (proj1 (proj1 PRE)) c off Hci Hcc Hx Hxm HROOM _
      (YFfi.HSP B ly X c off W regs (FSP.unpoison UP mem) md PRE) (YFfi.IMG B ly X c off W regs (FSP.unpoison UP mem) md PRE)
      a (proj1 Ha) HD) as [O|O].
    + left. exact O.
    + right; right; left. unfold ascratch, spZ. left. exact O. }
unfold cfg_at, A_CDealloc. rewrite <- (YFg0.wvb_self md) at 1.
eapply SRr_mono; [| intros W' c' _ HR; exact (FINKHU W' c' HR)].
destruct (Z_lt_le_dec (YFfi.kcnt X c) (YFgk.MAXv c)) as [LT|GE].
- exact (YFgy.segK1 W ly regs mem md c off _ _ _ j80 j88 jst (m_vm_materialized md) FH LT).
- apply (YFgz.segK2 W ly regs mem md c off _ _ _ j80 j88 jst (m_vm_materialized md) FH). clear - RFx GE. unfold YFgk.MAXv in *. lia.
Qed.

Theorem tfib_rchunk_primU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly X k cbp UP W regs mem md off,
  FK.rcc_preU B ly X k cbp UP W regs mem md -> ck_beg k = PPrim off -> ly_tsd ly = TFIB_TSD ->
  amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (FK.rcc_leafU B ly X k UP W regs mem md).
Proof.
intros B LAWS TB ly X k cbp UP W regs mem md off PREU Hb HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (FAR.ARU_intro B ly X UP W mem md (proj1 PRE) OKU POU) as HU.
pose proof PRE as (_ & _ & Hk & Hst & _).
pose proof (YFfr.geom B ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb) as GE.
assert (EXT : ck_extent k = YFgs.SZv (YFfr.rcl off)) by (decompose [and] GE; assumption).
pose proof (YFfr.FH_ok B TB ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb HTSD) as FHu.
pose proof (rchunk_prim_regions_off_ush B ly X UP W mem md k regs (YFfr.rcl off) (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k)
  (YFfr.hb1 B ly k W (FSP.unpoison UP mem)) cbp (YFfr.rmuc X off) (YFfr.j1 ly W (FSP.unpoison UP mem)) (YFfr.j2 ly W (FSP.unpoison UP mem))
  HU Hk Hst eq_refl EXT FHu) as OFF.
pose proof (rc_hyps_real W ly regs mem UP _ _ _ _ _ _ _ _ _ FHu OFF) as FH.
rewrite (YFg7.recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (YFg0.wvb_self md) at 1.
eapply (amreal_SRr_pre tfibsegs _ _ _ _
  (YFgs.at_CD W ly regs mem md (YFfr.rcl off) (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k) (YFfr.hb1 B ly k W (FSP.unpoison UP mem)))).
{ exact (YFh7.segRC W ly regs mem md _ _ _ _ _ cbp _ _ _ (m_vm_materialized md) FH). }
intros W' c' _ HCD.
destruct (rc_post_mu W ly regs mem md UP _ _ _ _ _ cbp _ _ _ W' c' FHu OFF HCD) as (regs1 & mem1 & mat & -> & -> & HCDu & MEQ1).
destruct (YFg7.CDPRE B TB ly X k cbp W regs (FSP.unpoison UP mem) md off PRE Hb HTSD W _ HCDu)
  as (regs' & mem' & mat' & _ & Ec & PRE' & R2 & R1 & RS & FR & PUF).
apply FK.cfg_at_inj in Ec as (Er & Em & Ed). subst regs' mem'. rewrite <- Ed in PRE'.
assert (OKX1 : FSP.upoison_ok B ly (YFf3.X1 X k) UP).
{ exact (upoison_ok_del_quar B ly X (YFf3.X1 X k) UP k OKU Hk Hst (wf_chunks_nodup _ _ _ _ _ (am_wf B ly X _ (proj1 (proj1 PRE)))) eq_refl). }
assert (PO1 : FSP.upoisoned tfibsegs W mem1 UP).
{ exact (upoisoned_frame_off B ly X UP W mem md mem1 (YFgs.WIN ly regs (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k)) HU
    (fun a Ha => OFF a (rc_WIN_fixed _ _ _ _ _ _ _ _ _ _ _ _ _ FHu a Ha)) MEQ1). }
eapply amreal_mono; [| exact (tfib_cdealloc_okU B LAWS TB ly (YFf3.X1 X k) (YFfr.rcl off) off UP W regs1 mem1 _ (conj PRE' (conj OKX1 PO1)) HTSD)].
cbv beta. intros [[] S''] W'' c'' HL. destruct HL as (regs'' & mem'' & md'' & -> & (AP & OK'' & PO'') & UF & CI & RAWc).
assert (Ec2 : cfg_at tfibsegs (raZ regs1) regs'' mem'' md'' = cfg_at tfibsegs (raZ regs) regs'' mem'' md'') by (unfold cfg_at, raZ; rewrite R1; reflexivity).
rewrite Ec2.
assert (HSP0 : ly_stk_lo ly + KSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly).
{ pose proof PRE as PRE2. destruct PRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in Hlo, Hcb1.
  clear - Hlo Hcb1 Hcb2; lia. }
(* the raw frame: cache_dealloc's (RAWc, from X1 at regs1; X1 owns what X owns, YFf3.aowned_X1; regs1 has regs' sp) after
   segRC's (MEQ1; its window YFgs.WIN is in YFf3.D, YFg7.WIN_D, owned by X or in the stack scratch, YFf3.D_owned) *)
assert (RAW : forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd (tt, S'')) (bv_unsigned x) ->
  ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem'' x = mem x).
{ intros x NO NO' NS NF.
  rewrite (RAWc x); [| | exact NO' | unfold ascratch, spZ in NS |- *; rewrite R2; exact NS | exact NF].
  - apply (FK.raw_of_meq (YFgs.WIN ly regs (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k)) (aowned B ly X) (fun _ => False)
      (ascratch B KSTACK regs) (fun _ => False) mem mem1 MEQ1); [| exact NO | intros [] | exact NS | intros []].
    intros a Ha Hw.
    assert (HD : YFf3.D B ly k (bv_unsigned (YK11.getr regs 2)) a)
      by (eapply YFg7.WIN_D; first [exact Hw | exact PRE | exact Hb | exact HTSD | exact TB]).
    destruct (YFf3.D_owned B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb _ HSP0 a (proj1 Ha) HD) as [O|O].
    + left. exact O.
    + right; right; left. unfold ascratch, spZ. left. exact O.
  - intros O1. apply NO. exact (proj1 (YFf3.aowned_X1 B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb (bv_unsigned (YK11.getr regs 2)) HSP0 _) O1). }
apply (FK.rcc_leafU_intro B ly X k UP W regs mem md (tt, S'') W'' regs'' mem'' md''); [| exact OK'' | exact PO'' | exact RAW].
exists regs'', (FSP.unpoison UP mem''), md''. split; [reflexivity|].
split.
2:{ split; [|exact CI]. intros a Ha PU NK. rewrite (UF a Ha) by exact PU. exact (PUF a Ha PU NK). }
destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS). unfold acall_post. unfold spZ in *. rewrite R2 in PRS.
split; [exact AR''|]. split; [exact LLE|]. split; [exact WLE|]. split.
{ intros r Hr. rewrite (RP r Hr). unfold acallee_saved in Hr.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct R as [->|R]; [exact R2|]. apply RS. clear - R. unfold YFgs.SREGS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split. { pose proof (YFg0.same_io_wvb md mat) as IO1. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
split.
{ intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [apply FR; [exact Ha | exact NO | exact NS] | | exact NO' | unfold ascratch, spZ in *; rewrite R2; exact NS | exact NE].
intros O1. apply NO. exact (proj1 (YFf3.aowned_X1 B ly X _ (proj1 (proj1 PRE)) k off Hk Hst Hb (bv_unsigned (YK11.getr regs 2)) HSP0 a) O1). }
exact PRS.
Qed.
(*END-PART2*)
End t.
