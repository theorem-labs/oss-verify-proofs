(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1.v (a working branch ced28ed2383, file sha256 f69f0bfd935f) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 25 image addresses moved by code-verified function pairs (50 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocation fixes on image B: the instance word at TFIB_INST + 0x328 is the constant 0x100000 (1 MiB, not a data address), as in the source; the Tfib_owned_static row's start in its length is B's 0xa7c90 (YF0m.v:1146), not cgif's 0xa5ad0; the inst_v comment names B's YFgi.TAILG cells 0xa50f0 / 0xa5100; ARm_gap's zero-shadow step destructs B's 12 Tfib_zero_shadow rows (YF0m.v:1144; cgif has 5), as B/YFf3.v:648. *)
(* Modified by Theorem Labs, 2026-10: omx-clap-core fuzz_state image B (fs.asan-ubsan): fs C5 - the instance's trace premise is tr_admit (as_universe B) S tr instead of In tr (as_universe B) (as YFex.v / YFfl.v): post_n_cgif, lpost_d_cgif, post_c_cgif, di_depot_cgif and diface_cgif's U; post_c_cgif and enq_bridge_cgif pass it to YFex / YFfl's sd_wf / free_fin_ARm / free_mid_ARm / WS', whose HU has that type. Image A's text (a Theorem Labs lane's DgC5-s1a.patch), mirrored. *)
(* Modified by Theorem Labs, 2026-10: moved from 86aa4177b94 to a working branch 59def5d6b9d (cgif file sha256 23d8cde3e213; a Theorem Labs lane's fs internal bounds at kFreeArrayOffset): dgo_bgeom bounds rg_mapped_user (reg S kBatchClass) by 2 ^ 32 - 2 ^ 29 (= kFreeArrayOffset) instead of 2 ^ 31, false at the kit's EV_MAX = 11776; dgo_bvc and dgo_own_ext_nonuser unfold kFreeArrayOffset in the chunk_facts bound Gal. By 3-way merge (base = agreloc of 86aa4177b94, theirs = agreloc of 59def5d6b9d, ours = this file's image-B rows); no numeral changed. *)
(* Modified by Theorem Labs, 2026-10: moved from ced28ed2383 to a working branch 86aa4177b94 (cgif file sha256 6c3f687b3e39; FS-INSTANCE 1.1 W and 3 A): imports EVroom; qv_geom_cgif bounds the class-24 region by EVroom.ev_user_room in place of unfolding EV_MAX; rview_cgif drops the removed DMiface.di_rview_t 2 ^ 31 conjunct. By 3-way merge (base = agreloc of ced28ed2383, theirs = agreloc of 86aa4177b94, ours = this file's image-B rows); no numeral changed. *)
(* Modified by Theorem Labs, 2026-10: fs's B/YFf0.batch_geom and B/YFex.batch_geom bound rg_mapped_user (reg S kBatchClass) by kFreeArrayOffset where cgif's state 2 ^ 31 (the kit's EV_MAX = 11776); batch_range_v and ARm_gap's BATCH step unfold kFreeArrayOffset where lia needs its value (L edit, as B/YFhl.v:261). *)
(* The cgif_file instance of the generic Deallocate interface DGif0.DIface: ARX = ARXr = ARX_cgif, AOX = aowned,
   rpre = rpre_dealloc_cgif, fpre = fpre_cgif (True), ft = free, lpost = qtight, dpost = CLdepot.dpost_x tfibsegs B,
   dbody = YFeu.drain_body, QB = qloose and DRq = DRq_cgif (YG03.RIx).  The class-24 batch bound L24 is a variable;
   only di_enqueue reads it, through 16385 <= L24 (CLenqcgif.EPc's batch conjunct; YG0m.batches_len_fuel).

   Ported from cgif_file's released AR facts of the free walk (YFfu / YFg1 / YFf0 / YFfl / YFex / YFey / YFeu /
   YFhl / YFhf / YFg1.ENQ_PRE / YG0q / YG0s) as cgif's instance of DIface.  Pattern: AGif1.v, the same job for
   Allocate.  di_depot comes from CLdepotcgif.di_depot_cgif at the released depot contract tfib_depot_spec, and
   di_enqueue from CLenqcgif.di_enqueue_ok with the walk-side bridge enq_bridge_cgif.  The six drain-side fields
   (Drain, the transfer / recycle cuts, Recycle, CacheDealloc) are Section hypotheses named like the fields; they
   come from cgif's released drain walk (a Theorem Labs lane's DGif1d). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The cgif image instances first, so that the released tfibsegs lemmas imported below shadow ImgBase's generalised copies. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import EVroom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFew YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif0cgif AGif1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DeallocGcgif DGbase DGgi DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG06 YG07 YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq YFf0 YFfl YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFhd YFhf YFhl YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0o YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB13 YFex YFfy AGix.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require CLdepotcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require CLenqcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* A file of CLenqcgif's closure leaves lia's div / mod handling off; the proofs below need it on. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* The cgif image instances, normalised: the projections of AImg_cgif / DImg_cgif to their cgif values, and the
   ImgBaseDG copies to their released originals (convertible, DGif0cgif.v's checks), so that lia / rewrite see the
   same atoms as the released lemmas. *)
Ltac dgn := cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif];
  repeat match goal with
  | H : context [@ImgBaseDG.dg_czone] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBaseDG.dg_inst_ok] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBaseDG.dg_dzone] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBaseDG.dg_izone] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBaseDG.dg_ial_post] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBaseDG.dg_zone3] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_segs] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_img_cover] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_const] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_tp] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_tsd] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_oom] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  | H : context [@ImgBase.im_errno] |- _ => progress cbn [ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post
  ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc
  DImg_cgif ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
  ImgBase.im_syms ImgBase.im_const AImg_cgif] in H
  end.
Ltac img_norm :=
  cbn [ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover
       ImgBase.im_syms ImgBase.im_const ImgBaseDG.dg_czone ImgBaseDG.dg_inst_ok ImgBaseDG.dg_dzone
       ImgBaseDG.dg_izone ImgBaseDG.dg_ial_post ImgBaseDG.dg_zone3 ImgBaseDG.dg_depot ImgBaseDG.dg_enqueue
       ImgBaseDG.dg_drain ImgBaseDG.dg_rchunk ImgBaseDG.dg_cdealloc AImg_cgif DImg_cgif] in *;
  try change @DGbaseC.DFSTACK with @DGbase.DFSTACK in *;
  try change @YFewC.QSTACK with @YFew.QSTACK in *;
  try change @YFl0C.DEP_STK with @YFl0.DEP_STK in *;
  try change @YFl0C.depot_after with @YFl0.depot_after in *;
  try change @YFeuC.DSTACK with @YFeu.DSTACK in *;
  try change @YFeuC.transfer_g with @YFeu.transfer_g in *;
  try change @YFeuC.recycle_body with @YFeu.recycle_body in *;
  try change @YFeuC.drain_body with @YFeu.drain_body in *;
  try change @YFeuC.plist_cells with @YFeu.plist_cells in *;
  try change @YFeuC.puser with @YFeu.puser in *;
  try change @DGgiC.SPv with @DGgi.SPv in *;
  try change @DGgiC.N8v with @DGgi.N8v in *;
  try change @DGgiC.CNT8v with @DGgi.CNT8v in *;
  try change @DGgiC.Bv with @DGgi.Bv in *;
  try change @DGgiC.BBv with @DGgi.BBv in *;
  try change @DGgiC.BCv with @DGgi.BCv in *;
  try change @DGgiC.SLOTv with @DGgi.SLOTv in *;
  try change @DGgiC.QSv with @DGgi.QSv in *;
  try change @DGgiC.QFv with @DGgi.QFv in *;
  try change @DGgiC.QBv with @DGgi.QBv in *;
  try change @DGgiC.PSTATIC with @DGgi.PSTATIC in *;
  try change @DGgiC.PBDISJ with @DGgi.PBDISJ in *;
  try change @DGgiC.WINT with @DGgi.WINT in *;
  try change @DGgiC.WINB with @DGgi.WINB in *;
  try change @DGgmC.WINT with @DGgm.WINT in *;
  try change @DGgmC.WINB with @DGgm.WINB in *;
  idtac.
(* Tactics of the view part (DGif1V) and of the owned / quarantine part (DGif1O). *)
Ltac dgo_splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac dsplits := repeat match goal with |- _ /\ _ => split end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* The instance's recycle invariant: the chunks [its] and the batch objects [zs] still to recycle. *)
Definition DRq_cgif (B : asyms) (S : astate) (its : list chunk) (zs : list Z) : Prop :=
YG03.RIx (as_universe B) 0 0 0 S its [] zs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (view) di_view_n and di_view (a Theorem Labs lane, from its DGif1V.v; ported from YFfu / YFg1 / YFf0 / YFfl over ARm). *)
Section vw.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

Section c.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation q := (st_qthread S).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Facts of ARm alone (YFfu.v:139-158, 263, 294).                                                                   *)
Lemma cell_state_v : ARm B ly S rd0 -> forall c e (w : nat) e', In c (acells B ly S) -> c = ACell e w (AV e') ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros M c e w e' Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem e w e').
exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M) _ Hin).
Qed.
Lemma cell_stateZ_v : ARm B ly S rd0 -> forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) ->
val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros M c e w x Hin E. exact (cell_state_v M c e w (ANum x) Hin E). Qed.
Lemma vis_range_v : ARm B ly S rd0 -> forall e len i, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) \/ In (e, len) (aclient S) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros M e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_client B ly S rd0 M) _ Hin i Hi).
Qed.
Lemma quar_In_v : forall c, In c (quar_cells S) -> In c (acells B ly S).
Proof. intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right. left. exact Hc. Qed.
Lemma Hsp_v : ARm B ly S rd0 -> ly_stk_lo ly + ASTACK <= ly_stk_hi ly <= ly_stk_hi ly.
Proof. intros M. pose proof (lo_top ly (am_layout B ly S rd0 M)) as (T1 & T2 & _). unfold ly_bot, kStackSpan, ASTACK in *. lia. Qed.
Lemma HB17 : 0 <= 17 < 256 /\ Z.land 17 127 = 17.
Proof. split; [lia | reflexivity]. Qed.

(* dn_unw (YFfu.v:263) *)
Lemma unw_v : ARm B ly S rd0 -> val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof.
intros M. replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply (cell_stateZ_v M); [|reflexivity]. unfold acells. rewrite !in_app_iff. do 8 right. left. reflexivity.
Qed.

(* dn_ial (YFfu.v:294, ial_vals, at st_internal_inited S = true) *)
Lemma ial_vals_v : ARm B ly S rd0 ->
val_mem tfibsegs m0 TFIB_IAL_FLAG 1 (if st_internal_inited S then 1 else 0) /\ val_mem tfibsegs m0 (TFIB_IAL_FLAG + 1) 1 0 /\
(if st_internal_inited S then val_mem tfibsegs m0 TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m0 TFIB_IAL_W 8 0 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 0) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
intros M.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells B ly S)) by (intros c Hc; unfold acells; rewrite !in_app_iff; do 7 right; left; exact Hc).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TS), (ts_ial_lo _ TS), (ts_ial_w _ TS) in IN.
dsplits.
- replace TFIB_IAL_FLAG with (aeval B ly (ANum TFIB_IAL_FLAG)) at 1 by reflexivity. eapply (cell_stateZ_v M); [apply IN; left; reflexivity | destruct (st_internal_inited S); reflexivity].
- replace (TFIB_IAL_FLAG + 1) with (aeval B ly (ANum (TFIB_IAL_FLAG + 1))) by reflexivity. eapply (cell_stateZ_v M); [apply IN; right; left; reflexivity | reflexivity].
- assert (E1 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO)) = TFIB_IAL_W) by (cbn; rewrite (ts_ial_lo _ TS); lia).
assert (E2 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 8)) = TFIB_IAL_W + 8) by (cbn; rewrite (ts_ial_lo _ TS); lia).
assert (E3 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) = TFIB_IAL_W + 16) by (cbn; rewrite (ts_ial_lo _ TS); lia).
destruct (st_internal_inited S); split.
+ rewrite <- E1. eapply (cell_stateZ_v M); [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2, <- E3. eapply (cell_state_v M); [apply IN; do 3 right; left; reflexivity | reflexivity].
+ rewrite <- E1. eapply (cell_stateZ_v M); [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2. eapply (cell_state_v M _ _ 8 (ANum 0)); [apply IN; do 3 right; left; reflexivity | reflexivity].
- intros a Ha. pose proof (am_zero B ly S rd0 M) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TS), (ts_ial_w _ TS), (ts_ial_hi _ TS) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : rd0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFIB_IAL_LO)) by (cbn; rewrite (ts_ial_lo _ TS); lia). apply Z1. cbn [snd]. lia.
- replace a with (aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) + (a - (TFIB_IAL_W + 16))) by (cbn; rewrite (ts_ial_lo _ TS); lia). apply Z2. cbn [snd]. lia. }
exact (aview_byte _ _ _ _ R).
Qed.
Lemma ial_post_v : ARm B ly S rd0 -> st_internal_inited S = true -> DGgi.IAL_POST W mem.
Proof.
intros M HI. pose proof (ial_vals_v M) as (A1 & A2 & A3 & A4). rewrite HI in A1, A3. cbv iota in A1, A3. destruct A3 as [A3 A5].
dgn; unfold DGgi.IAL_POST. cbv zeta. exact (conj A1 (conj A2 (conj A3 (conj A5 A4)))).
Qed.

(* dn_inst: the instance's quarantine fields are constant cells of the image (YF0x.v:206, tfib_const_lookup, as
   YFfu.REG0_ok reads YFgi.TAILG's flit8 0xa50f0 / 0xa5100). *)
Lemma inst_v : ARm B ly S rd0 ->
val_mem tfibsegs m0 (TFIB_INST + 0x318) 8 0x10000000 /\ val_mem tfibsegs m0 (TFIB_INST + 0x328) 8 0x100000.
Proof.
intros M. split.
- exact (tfib_const_lookup B TS ly S (w_H W) mem (TFIB_INST + 0x318) 8 0x10000000 M ltac:(vm_compute; reflexivity)).
- exact (tfib_const_lookup B TS ly S (w_H W) mem (TFIB_INST + 0x328) 8 0x100000 M ltac:(vm_compute; reflexivity)).
Qed.

(* dv_junk: the thread's stats words are thread junk (YFfu.v:157-167). *)
Lemma junk_pres_v : ARm B ly S rd0 -> img_cover ly -> forall a, T + t_stats + 24 <= a < T + t_stats + 40 -> apresent (w_H W) mem a.
Proof.
intros M IMG a Ha.
pose proof (YFf0.HIGH B ly S rd0 M IMG) as (_ & _ & _ & _ & ZT & _).
apply YFfu.vis_apresent_off.
- apply (zone3_off_img _ _ a ZT). unfold t_stats, kThreadObjSize in *. lia.
- replace a with (aeval B ly (AT t_stats) + (a - (T + t_stats))) by (cbn; lia).
apply (vis_range_v M (AT t_stats) (t_unwinding - t_stats)); [|unfold t_stats, t_unwinding in *; lia].
left. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. unfold thread_junk. cbn. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The quarantine (YFfu.v:334-351, YFg1.v:256): Wf's byte sums and qmeter's qtight part.                           *)
Lemma items_n_pos_v : ARm B ly S rd0 -> forall b x, In b (all_batches S) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros M b x Hb Hx. pose proof (am_wf B ly S rd0 M) as WF.
pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x ltac:(unfold q_items; apply in_flat_map; exists b; auto)) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(lia)). lia.
Qed.
Lemma b_bytes_ge_v : ARm B ly S rd0 -> forall b, In b (all_batches S) -> kBatchBytes <= b_bytes b.
Proof.
intros M b Hb. unfold b_bytes.
assert (G : forall l, incl l (b_items b) -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 l).
{ induction l as [|x t IH]; intros Hl; cbn; [lia|]. pose proof (items_n_pos_v M b x Hb (Hl x (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). lia. }
pose proof (G (b_items b) ltac:(intros y Hy; exact Hy)). lia.
Qed.
Lemma sum_bytes_ge_v : ARm B ly S rd0 -> forall l, incl l (all_batches S) -> 0 <= sum_bytes l.
Proof.
intros M. induction l as [|b t IH]; intros Hl; cbn; [unfold sum_bytes; cbn; lia|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge_v M b (Hl b (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). unfold kBatchBytes in *. lia.
Qed.
Lemma sum_len_v : ARm B ly S rd0 -> forall l, incl l (all_batches S) -> 8192 * Z.of_nat (length l) <= sum_bytes l.
Proof.
intros M. induction l as [|b t IH]; intros Hl; [cbn; unfold sum_bytes; cbn; lia|].
pose proof (b_bytes_ge_v M b (Hl b (or_introl eq_refl))) as Hb. pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)) as Ht.
unfold sum_bytes in *. cbn [fold_right length]. unfold kBatchBytes in Hb. lia.
Qed.
(* dv_qb *)
Lemma qb_v : ARm B ly S rd0 -> qmeter S -> 0 <= qc_bytes q <= kQuarantineCacheMax.
Proof.
intros M HQ. pose proof (am_wf B ly S rd0 M) as WF.
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE.
pose proof (sum_bytes_ge_v M (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S1.
pose proof (proj1 (qmeter_tight _ HQ)) as QT. lia.
Qed.

(* The geometry of a batch (YFf0.v:124 batch_geom, YG0s.v:196 region_in_prim; as YFfu.v:369 / :686-692). *)
Lemma batch_range_v : ARm B ly S rd0 -> forall b, In b (all_batches S) ->
ly_space ly <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize /\
(ly_space ly + b_self b) mod 8192 = 0 /\ kHighMemBeg <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ASAN_CEIL.
Proof.
intros M b Hb. pose proof (am_layout B ly S rd0 M) as LO.
destruct (YFf0.batch_geom B ly S rd0 M (ly_stk_hi ly) (Hsp_v M) b Hb) as (x & Ex & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32).
{ unfold region_base. rewrite region_off_eq by (unfold kBatchClass; lia). unfold kBatchClass. lia. }
rewrite RB in Ex, R3, R4, R5.
dsplits.
- lia.
- unfold kBatchBytes, kSpaceSize, kFreeArrayOffset in *. lia.
- rewrite Ex. apply Z.mod_divide in R3 as [c Hc]; [|lia]. apply Z.mod_divide in Ax as [c' Hc']; [|unfold kBatchBytes; lia].
rewrite Hc, Hc'. unfold kBatchBytes. apply Z.mod_divide; [lia|]. exists (c * 8 + c'). lia.
- lia.
- unfold kBatchBytes, kFreeArrayOffset in *. lia.
Qed.
Lemma qf_range_v : ARm B ly S rd0 -> 0 <= DGgi.QFv ly q < 2 ^ 64.
Proof.
intros M. unfold DGgiC.QFv, DGgi.QFv. cbv zeta. destruct (qc_list q) as [|b0 t] eqn:E; [lia|].
assert (Hb0 : In b0 (all_batches S)) by (unfold all_batches; rewrite E; left; reflexivity).
pose proof (batch_range_v M b0 Hb0) as (_ & _ & _ & H4 & H5). ceil. unfold kHighMemBeg, kBatchBytes, ASAN_CEIL in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The block [p] of size [n] and its chunk [k] (YFg1.v:57-200, 266, 273; YFfu.v:377, 384, 675-683).               *)
Variables (p : sptr) (n : Z) (k : chunk).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Definition KV : Prop :=
ARm B ly S rd0 /\ img_cover ly /\ In k (st_chunks S) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Lemma Epa_v : KV -> pa = ck_base B ly k + ck_rz k.
Proof. intros (M & _ & Hk & _ & Hu & _). pose proof (chunk_facts B ly S rd0 k M Hk) as (_ & _ & _ & G4 & _). rewrite <- Hu. exact G4. Qed.
Lemma Enn_v : KV -> nn = ck_n k.
Proof. intros (_ & _ & _ & _ & _ & Hr). unfold ck_n. rewrite Hr. reflexivity. Qed.
Lemma hdr_In_v : KV -> forall c, In c (chunk_cells k) -> In c (acells B ly S).
Proof. intros (_ & _ & Hk & _) c Hc. unfold acells. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk | exact Hc]. Qed.
(* dv_nonnull: a chunk's user pointer is a primary or secondary pointer (YG0s.v:239 chunk_facts). *)
Lemma nonnull_v : KV -> p <> PNull.
Proof.
intros (M & _ & Hk & _ & Hu & _) E. pose proof (chunk_facts B ly S rd0 k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite <- Hu in E. unfold ck_user, padd in E. destruct (ck_beg k); try discriminate E. destruct GG.
Qed.
Definition hb1v : Z := match rd0 (pa - 15) with Some b => b | None => 0 end.
Lemma hb1_facts_v : KV -> rd0 (pa - 15) = Some hb1v /\ 0 <= hb1v < 256 /\ Z.land hb1v 127 = 17.
Proof.
intros HK. pose proof HK as (M & _ & Hk & Hst & _).
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M)). apply (hdr_In_v HK). unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite (YFf0.EA2 B ly S rd0 M k _ _ Hk) in C. unfold kChunkHeaderSize in C.
replace (ck_base B ly k + (ck_rz k - 16) + 1) with (pa - 15) in C by (rewrite (Epa_v HK); lia).
destruct C as (b & Hb & Hm). unfold hb1v. rewrite Hb. destruct (YFfu.aview_vis_byte (w_H W) mem (pa - 15) ltac:(rewrite Hb; discriminate)) as (b' & E' & R' & _).
rewrite Hb in E'. injection E' as <-. auto.
Qed.
Lemma hw_val_v : KV -> val_mem tfibsegs m0 (pa - 16) 4 (2 + 256 * hb1v) /\ val_mem tfibsegs m0 (pa - 12) 4 nn.
Proof.
intros HK. pose proof HK as (M & _ & Hk & Hst & _). pose proof (hb1_facts_v HK) as (HB & HR & _).
pose proof (Epa_v HK) as EP. pose proof (Enn_v HK) as EN.
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = pa - 16).
{ rewrite (YFf0.EA B ly S rd0 M k _ Hk). rewrite EP. unfold kChunkHeaderSize. lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = pa - 16 + d).
{ intros d. rewrite (YFf0.EA2 B ly S rd0 M k _ _ Hk). rewrite EP. unfold kChunkHeaderSize. lia. }
assert (V0 : val_mem tfibsegs m0 (pa - 16) 1 2).
{ rewrite <- EH. eapply (cell_stateZ_v M); [apply (hdr_In_v HK); unfold chunk_cells; apply in_app_iff; left; left; reflexivity|]. unfold z1, c1, hdr_state. rewrite Hst. reflexivity. }
assert (V2 : val_mem tfibsegs m0 (pa - 14) 2 0).
{ replace (pa - 14) with (pa - 16 + 2) by lia. rewrite <- (EH2 2). eapply (cell_stateZ_v M); [apply (hdr_In_v HK); unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity|]. reflexivity. }
assert (V4 : val_mem tfibsegs m0 (pa - 12) 4 (ck_n k)).
{ replace (pa - 12) with (pa - 16 + 4) by lia. rewrite <- (EH2 4). eapply (cell_stateZ_v M); [apply (hdr_In_v HK); unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity|]. reflexivity. }
split; [|rewrite EN; exact V4].
intros i Hi.
assert (LB : forall v (w j : nat), YO0f.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
destruct i as [|[|[|[|i]]]]; [| | | |lia].
- rewrite (V0 0%nat ltac:(lia)). do 2 f_equal. rewrite !LB. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- change (Z.of_nat 1) with 1. replace (pa - 16 + 1) with (pa - 15) by lia. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 2) with (pa - 14 + Z.of_nat 0) by lia. rewrite (V2 0%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 3) with (pa - 14 + Z.of_nat 1) by lia. rewrite (V2 1%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia.
Qed.
(* dv_hdr *)
Lemma hdr_v : KV -> exists hb1, 0 <= hb1 < 256 /\ Z.land hb1 127 = 17 /\
val_mem tfibsegs m0 (pa - 16) 4 (2 + 256 * hb1) /\ val_mem tfibsegs m0 (pa - 12) 4 nn.
Proof.
intros HK. pose proof (hb1_facts_v HK) as (_ & HR & HM). pose proof (hw_val_v HK) as [W1 W2].
exists hb1v. exact (conj HR (conj HM (conj W1 W2))).
Qed.
Lemma user_vis_v : KV -> forall a, pa <= a < pa + 8 -> rd0 a <> None.
Proof.
intros HK a Ha. pose proof HK as (M & _ & Hk & Hst & Hu & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
destruct (Z_lt_le_dec a (pa + nn)) as [L|L].
- replace a with (aeval B ly (sptr_exp (ck_user k)) + (a - pa)) by (rewrite Hu; unfold sptr_addr; lia).
apply (vis_range_v M _ (ck_n k)); [|rewrite <- EN; lia]. do 2 right. unfold aclient. apply in_app_iff. left. apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_user. rewrite Hst. left. reflexivity.
- replace a with (aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k)) + (a - pa - nn)) by (rewrite (YFf0.EA B ly S rd0 M k _ Hk), EP, EN; lia).
apply (vis_range_v M _ (ck_extent k - ck_rz k - ck_n k)); [|rewrite <- EN; lia].
left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. rewrite !in_app_iff. do 3 right. left. reflexivity.
Qed.
Lemma meta_vis_v : KV -> forall a, pa - 16 <= a < pa -> rd0 a <> None.
Proof.
intros HK a Ha. pose proof HK as (M & _ & Hk & _). pose proof (hw_val_v HK) as [V1 V2]. pose proof (Epa_v HK) as EP.
destruct (Z_lt_le_dec a (pa - 12)) as [L1|L1]. { replace a with (pa - 16 + (a - (pa - 16))) by lia. exact (YFfu.val_mem_vis _ _ _ _ _ (a - (pa - 16)) V1 ltac:(lia)). }
destruct (Z_lt_le_dec a (pa - 8)) as [L2|L2]. { replace a with (pa - 12 + (a - (pa - 12))) by lia. exact (YFfu.val_mem_vis _ _ _ _ _ (a - (pa - 12)) V2 ltac:(lia)). }
replace a with (aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - 8)) + (a - (pa - 8))) by (rewrite (YFf0.EA B ly S rd0 M k _ Hk), EP; lia).
apply (vis_range_v M _ 8); [|lia]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. rewrite !in_app_iff. right. left. left. reflexivity.
Qed.
Lemma shadow_vis_v : KV -> forall i, 0 <= i < DGgi.CNT8v nn -> exists v, rd0 (DGgi.SPv pa + i) = Some v.
Proof.
intros HK i Hi. pose proof HK as (M & _ & Hk & _ & Hu & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (am_wf B ly S rd0 M) as WF.
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (YFfl.u_al8 B ly S rd0 M k Hk) as (U8 & B8 & R8). pose proof (chunk_facts B ly S rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
unfold DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v in Hi. rewrite Z_div_mult in Hi by lia. rewrite <- EN in ER, NN1, NN2, NN3.
set (g := pa + 8 * i).
assert (FC : find_chunk_at B ly (st_chunks S) g = Some k).
{ apply (find_chunk_at_hit B ly S rd0 (st_chunks S) k g M ltac:(intros x Hx; exact Hx) (wf_chunks_nodup _ _ _ _ _ WF) Hk). subst g.
clear - EP Hi ER NN2 G5. rewrite EP. lia. }
assert (SH : ashadow B ly S g = Some (chunk_granule k ((g - ck_base B ly k) / 8))) by (unfold ashadow; rewrite FC; reflexivity).
assert (PC : exists c, pa = c * 8). { apply Z.mod_divide in U8 as [c Hc]; [|lia]. exists c. rewrite <- Hu. exact Hc. }
destruct PC as [c Hc].
pose proof (am_shadow B ly S rd0 M g _ ltac:(subst g; rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult) SH) as R.
exists (chunk_granule k ((g - ck_base B ly k) / 8)). rewrite <- R. f_equal. unfold shadow_addr, DGgiC.SPv, DGgi.SPv. subst g.
rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia.
Qed.
Lemma p_zone_v : KV -> zone3 (pa - 16) (DGgi.N8v nn + 16).
Proof.
intros HK. pose proof HK as (M & IMG & Hk & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (chunk_facts B ly S rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (YFfl.HIGH B ly S rd0 M k Hk IMG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZK & _).
clear - G1 G4 G5 ER NN1 NN2 NN3 EP ZK.
unfold DGgiC.N8v, DGgi.N8v. rewrite EP. ceil. unfold zone3, zone3cases, in_app in *. lia.
Qed.
Lemma p_al_v : KV -> pa mod 16 = 0.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Epa_v HK) as EP.
pose proof (chunk_facts B ly S rd0 k M Hk) as (_ & _ & G3 & _ & _ & G6 & _).
rewrite EP. apply Z.mod_divide in G3 as [c Hc]; [|lia]. apply Z.mod_divide in G6 as [c' Hc']; [|lia]. rewrite Hc, Hc'.
apply Z.mod_divide; [lia|]. exists (c + c'). lia.
Qed.
Lemma nn_range_v : KV -> 1 <= nn < 2 ^ 28.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _ & _ & Hr).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly S rd0 M)) k Hk) as [N _].
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3). rewrite Hr in Q1, Q2, Q3, N. unfold MALLOC_MAX in N. lia.
Qed.
Lemma pstatic_v : KV -> DGgi.PSTATIC ly pa nn.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (chunk_facts B ly S rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (YFf0.anyX B ly S rd0 M k 8 _ Hk eq_refl ltac:(lia)) as D7. pose proof (YFf0.anyX B ly S rd0 M k 2 _ Hk eq_refl ltac:(lia)) as D2.
pose proof (YFf0.anyX B ly S rd0 M k 6 _ Hk eq_refl ltac:(lia)) as D6. pose proof (YFf0.anyX B ly S rd0 M k 4 _ Hk eq_refl ltac:(lia)) as D4.
pose proof (YFf0.anyX B ly S rd0 M k 5 _ Hk eq_refl ltac:(lia)) as D5. pose proof (YFf0.anyX B ly S rd0 M k 7 _ Hk eq_refl ltac:(lia)) as DD.
unfold zdisjoint in D7, D2, D6, D4, D5, DD. cbn [fst snd] in D7, D2, D6, D4, D5, DD.
unfold DGgiC.PSTATIC, DGgi.PSTATIC. cbv zeta. intros a Ha.
clear - Ha D7 D2 D6 D4 D5 DD EP ER G5. unfold DGgiC.N8v, DGgi.N8v in *. dsplits; lia.
Qed.
(* dv_pres (YFfu.v:680-681) *)
Lemma pres_v : KV -> forall a, pa - 16 <= a < pa + 8 -> apresent (w_H W) mem a.
Proof.
intros HK a Ha. pose proof (p_zone_v HK) as PZ. pose proof (Enn_v HK) as EN. pose proof HK as (M & _ & Hk & _).
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
apply YFfu.vis_apresent_off; [exact (zone3_off_img _ _ a PZ ltac:(unfold DGgiC.N8v, DGgi.N8v; lia))|].
destruct (Z_lt_le_dec a pa); [apply (meta_vis_v HK); lia | apply (user_vis_v HK); lia].
Qed.
(* The block's shadow is in the shadow region (YFfu.v:384 p_facts). *)
Lemma sh_range_v : KV -> SHADOW_OFF + 514 <= DGgi.SPv pa /\ DGgi.SPv pa + DGgi.CNT8v nn <= kHighMemBeg.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (chunk_facts B ly S rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
assert (LO16 : 4096 <= ck_base B ly k) by (clear - G1; unfold in_app in G1; lia).
unfold DGgiC.SPv, DGgi.SPv, DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v. rewrite Z_div_mult by lia.
pose proof (Z.div_le_mono 4112 pa 8 ltac:(lia) ltac:(lia)) as S1. change (4112 / 8) with 514 in S1.
pose proof (YFfl.hs_bounds (pa + (nn + 7) / 8 * 8 - 8) ltac:(lia) ltac:(ceil; unfold kHighMemEnd, ASAN_CEIL in *; lia)) as [_ S2].
unfold shadow_addr in S2. replace (pa + (nn + 7) / 8 * 8 - 8) with (pa + ((nn + 7) / 8 - 1) * 8) in S2 by lia. rewrite Z.div_add in S2 by lia.
split; lia.
Qed.
(* dv_shpres (YFfu.v:682-683) *)
Lemma shpres_v : KV -> forall a, dshadow pa nn a -> apresent (w_H W) mem a.
Proof.
intros HK a Ha. unfold dshadow in Ha. change (DGgi.SPv pa <= a < DGgi.SPv pa + DGgi.CNT8v nn) in Ha. pose proof (sh_range_v HK) as [S1 S2].
destruct (shadow_vis_v HK (a - DGgi.SPv pa) ltac:(lia)) as [v Hv]. replace (DGgi.SPv pa + (a - DGgi.SPv pa)) with a in Hv by lia.
apply YFfu.vis_apresent; [unfold SHADOW_OFF, kHighMemBeg, TFIB_IMG_END in *; lia | rewrite Hv; discriminate].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The last batch of the thread's quarantine cache (YFfu.v:210-246, 351, 369, 686-700).                            *)
Variables (lastb : batch) (initr : list batch).
Definition BV : Prop := ARm B ly S rd0 /\ rev (qc_list q) = lastb :: initr.
Lemma qlist0_v : BV -> qc_list q = rev initr ++ [lastb].
Proof. intros (_ & Hrev). rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity. Qed.
Lemma lastb_in_v : BV -> In lastb (all_batches S).
Proof. intros HB. unfold all_batches. rewrite (qlist0_v HB), !in_app_iff. left. right. left. reflexivity. Qed.
(* db_qc (YFfu.v:216) *)
Lemma qc_vals_v : BV -> val_mem tfibsegs m0 (T + t_qc) 8 (DGgi.QSv q) /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 (DGgi.QFv ly q) /\
val_mem tfibsegs m0 (T + t_qc + 16) 8 (DGgi.Bv ly lastb) /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 (DGgi.QBv q).
Proof.
intros (M & Hrev).
assert (IN : forall c, In c (qc_cells (AT t_qc) q) -> In c (acells B ly S)).
{ intros c Hc. apply quar_In_v. unfold quar_cells. right. right. apply in_app_iff. left. exact Hc. }
unfold qc_cells in IN. dsplits.
- replace (T + t_qc) with (aeval B ly (AT t_qc)) by reflexivity. eapply (cell_stateZ_v M); [apply IN; left; reflexivity | reflexivity].
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
replace (DGgi.QFv ly q) with (aeval B ly (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end)) by (unfold DGgiC.QFv, DGgi.QFv; destruct (qc_list q); reflexivity).
eapply (cell_state_v M); [apply IN; right; left; reflexivity | reflexivity].
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
replace (DGgi.Bv ly lastb) with (aeval B ly (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end)) by (rewrite Hrev; reflexivity).
eapply (cell_state_v M); [apply IN; do 2 right; left; reflexivity | reflexivity].
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia). eapply (cell_stateZ_v M); [apply IN; do 3 right; left; reflexivity | reflexivity].
Qed.
(* db_b (YFfu.v:231) *)
Lemma batch_vals_v : BV -> val_mem tfibsegs m0 (DGgi.Bv ly lastb + 8) 8 (DGgi.BBv lastb) /\ val_mem tfibsegs m0 (DGgi.Bv ly lastb + 16) 8 (DGgi.BCv lastb).
Proof.
intros HB. pose proof HB as (M & _). pose proof (qlist0_v HB) as QL.
destruct (batch_cells_snoc (rev initr) lastb lastb eq_refl) as (P & EP & _ & _).
assert (IN : forall c, In c (batch_cells [lastb]) -> In c (acells B ly S)).
{ intros c Hc. apply quar_In_v. unfold quar_cells. right. right. apply in_app_iff. left. unfold qc_cells. do 4 right. rewrite QL, EP. apply in_app_iff. right. exact Hc. }
cbn [batch_cells app] in IN. split.
- replace (DGgi.Bv ly lastb + 8) with (aeval B ly (aoff (batch_exp lastb) 8)) by (unfold DGgiC.Bv, DGgi.Bv; cbv zeta; cbn; lia). eapply (cell_stateZ_v M); [apply IN; right; left; reflexivity | reflexivity].
- replace (DGgi.Bv ly lastb + 16) with (aeval B ly (aoff (batch_exp lastb) 16)) by (unfold DGgiC.Bv, DGgi.Bv; cbv zeta; cbn; lia). eapply (cell_stateZ_v M); [apply IN; do 2 right; left; reflexivity | reflexivity].
Qed.
(* db_pres, the byte count and item count words (YFfu.v:695-700) *)
Lemma bcell_pres_v : BV -> forall a, DGgi.Bv ly lastb + 8 <= a < DGgi.Bv ly lastb + 24 -> apresent (w_H W) mem a.
Proof.
intros HB a Ha. pose proof HB as (M & _). pose proof (lastb_in_v HB) as LB.
pose proof (batch_range_v M lastb LB) as (_ & _ & _ & H4 & H5). pose proof (batch_vals_v HB) as [V5 V6].
apply YFfu.vis_apresent; [ceil; unfold DGgiC.Bv, DGgi.Bv, kHighMemBeg, ASAN_CEIL, TFIB_IMG_END, kBatchBytes in *; cbv zeta in *; lia|].
destruct (Z_lt_le_dec a (DGgi.Bv ly lastb + 16)).
+ replace a with (DGgi.Bv ly lastb + 8 + (a - (DGgi.Bv ly lastb + 8))) by lia. eapply YFfu.val_mem_vis; [exact V5 | lia].
+ replace a with (DGgi.Bv ly lastb + 16 + (a - (DGgi.Bv ly lastb + 16))) by lia. eapply YFfu.val_mem_vis; [exact V6 | lia].
Qed.
(* db_pres, the slot word: batch_junk of a last batch with room (YFfu.v:240 slot_vis).  The room is needed: for a
   full batch the slot word is the first word after the batch. *)
Lemma slot_pres_v : BV -> DGgi.BCv lastb < kBatchSlots -> forall a, DGgi.SLOTv ly lastb <= a < DGgi.SLOTv ly lastb + 8 -> apresent (w_H W) mem a.
Proof.
intros HB ROOM a Ha. pose proof HB as (M & _). pose proof (lastb_in_v HB) as LB.
pose proof (batch_range_v M lastb LB) as (_ & _ & _ & H4 & H5).
unfold DGgiC.SLOTv, DGgi.SLOTv, DGgiC.Bv, DGgi.Bv, DGgiC.BCv, DGgi.BCv, kBatchSlots in *. cbv zeta in *.
apply YFfu.vis_apresent; [ceil; unfold kHighMemBeg, ASAN_CEIL, TFIB_IMG_END, kBatchBytes in *; lia|].
replace a with (aeval B ly (aoff (batch_exp lastb) (24 + 8 * Z.of_nat (length (b_items lastb))))
  + (a - (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb))))) by (cbn; lia).
apply (vis_range_v M _ (kBatchBytes - 24 - 8 * Z.of_nat (length (b_items lastb)))); [|unfold kBatchBytes; lia].
left. unfold ajunk. right. right. rewrite !in_app_iff. do 4 right. left. unfold quar_junk. apply in_flat_map. exists lastb. split; [exact LB | left; reflexivity].
Qed.
(* db_range (YFfu.v:686-692) *)
Lemma brange_v : BV -> ly_space ly <= DGgi.Bv ly lastb /\ DGgi.Bv ly lastb + kBatchBytes <= ly_space ly + kSpaceSize /\
0 <= DGgi.QFv ly q < 2 ^ 64 /\ DGgi.Bv ly lastb mod 8192 = 0.
Proof.
intros HB. pose proof HB as (M & _). pose proof (lastb_in_v HB) as LB.
pose proof (batch_range_v M lastb LB) as (H1 & H2 & H3 & _). pose proof (qf_range_v M) as QF.
unfold DGgiC.Bv, DGgi.Bv. cbv zeta. dsplits; first [assumption | lia].
Qed.
(* db_bounds: the byte sums of Wf and qtight (YFfu.v:351 QB_facts, with qtight in place of the arm's room). *)
Lemma bb_v : BV -> qmeter S -> 0 <= DGgi.BBv lastb /\ DGgi.BBv lastb <= kQuarantineCacheMax /\ 8192 * DGgi.QSv q <= kQuarantineCacheMax.
Proof.
intros HB HQ. pose proof HB as (M & _). pose proof (qlist0_v HB) as QL. pose proof (lastb_in_v HB) as LB.
pose proof (am_wf B ly S rd0 M) as WF. pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE.
pose proof (proj1 (qmeter_tight _ HQ)) as QT.
assert (SUM : qc_bytes q = sum_bytes (rev initr) + b_bytes lastb).
{ rewrite QE, QL, sum_bytes_app. unfold sum_bytes at 2. cbn [fold_right]. lia. }
pose proof (sum_bytes_ge_v M (rev initr) ltac:(intros y Hy; unfold all_batches; rewrite QL, !in_app_iff; tauto)) as S1.
pose proof (b_bytes_ge_v M lastb LB) as S2.
pose proof (sum_len_v M (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S3.
unfold DGgiC.BBv, DGgi.BBv, DGgiC.QSv, DGgi.QSv. cbv zeta. unfold kBatchBytes in S2. lia.
Qed.
(* db_slots: Wf's quarantine part (YG01.v:294 wq_batches). *)
Lemma slots_v : BV -> DGgi.BCv lastb <= kBatchSlots.
Proof.
intros HB. pose proof HB as (M & _). pose proof (lastb_in_v HB) as LB. pose proof (am_wf B ly S rd0 M) as WF.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) lastb LB) as [_ H2].
unfold DGgiC.BCv, DGgi.BCv. apply Nat2Z.inj_le in H2. rewrite Z2Nat.id in H2 by (unfold kBatchSlots; lia). exact H2.
Qed.
(* db_disj: batches and chunks are disjoint (YFfl.v:223 batch_vs_chunk; YFfu.v:693-694). *)
Lemma pbdisj_v : KV -> rev (qc_list q) = lastb :: initr -> DGgi.PBDISJ ly pa nn lastb.
Proof.
intros HK Hrev. pose proof HK as (M & _ & Hk & _). pose proof (Enn_v HK) as EN. pose proof (Epa_v HK) as EP.
pose proof (lastb_in_v (conj M Hrev)) as LB.
pose proof (chunk_facts B ly S rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
pose proof (YFfl.ext_rounded B ly S rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (YFfl.batch_vs_chunk B ly S rd0 M 17 HB17 (ly_stk_hi ly) (Hsp_v M) lastb k LB Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - D EP ER G5. unfold DGgiC.PBDISJ, DGgi.PBDISJ, DGgiC.N8v, DGgi.N8v, DGgiC.Bv, DGgi.Bv, kBatchBytes in *. cbv zeta in *. lia.
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The fields.                                                                                                      *)
Lemma view_n_cgif : forall inst ly S W mem md n,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> dview_n B W ly inst mem.
Proof.
intros inst ly S W mem md n [Ei HAR] (_ & _ & HI). subst inst.
img_norm.
pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
constructor.
- exact LY.
- exact IMG.
- rewrite (am_tsd _ _ _ _ M). exact (ts_tsd B TS).
- exact (am_const B ly S _ M).
- exact (inst_v _ _ _ _ M).
- exact (ial_post_v _ _ _ _ M HI).
- exact (unw_v _ _ _ _ M).
Qed.

(* The last batch's view, for a last batch with room. *)
Lemma dbview_room_cgif : forall inst ly S W mem md n p lastb initr,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> In (p, n) (blocks S) ->
rev (qc_list (st_qthread S)) = lastb :: initr ->
dbview W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n).
Proof.
intros inst ly S W mem md n p lastb initr [_ HAR] (_ & HQ & _) HBLK Hrev.
img_norm.
pose proof (proj1 HAR) as M. pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (find_user_block _ 0 0 0 S p n (am_wf _ _ _ _ M) HBLK) as (k & _ & Hk & Hst & Hu & Hr).
assert (HK : KV ly S W mem p n k) by exact (conj M (conj IMG (conj Hk (conj Hst (conj Hu Hr))))).
assert (HB : BV ly S W mem lastb initr) by exact (conj M Hrev).
pose proof (nn_range_v _ _ _ _ _ _ _ HK) as NR.
pose proof (bb_v _ _ _ _ _ _ HB HQ) as (BB1 & BB2 & BB3).
constructor.
- exact (qc_vals_v _ _ _ _ _ _ HB).
- exact (batch_vals_v _ _ _ _ _ _ HB).
- intros a [Ha|[ROOM Ha]]; [exact (bcell_pres_v _ _ _ _ _ _ HB a Ha) | exact (slot_pres_v _ _ _ _ _ _ HB ROOM a Ha)].
- exact (brange_v _ _ _ _ _ _ HB).
- exact (pbdisj_v _ _ _ _ _ _ _ _ _ HK Hrev).
- change (0 <= DGgi.BBv lastb /\ DGgi.BBv lastb + req_size n < 2 ^ 48 /\ DGgi.QSv (st_qthread S) < 2 ^ 48).
  unfold kQuarantineCacheMax in *. dsplits; lia.
- exact (slots_v _ _ _ _ _ _ HB).
Qed.

(* di_view from the view of the last batch (every last batch). *)
Lemma view_cgif_of : forall inst ly S W mem md p n,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem p n -> In (p, n) (blocks S) ->
(forall lastb initr, rev (qc_list (st_qthread S)) = lastb :: initr ->
  dbview W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n)) ->
dview B W ly inst mem S p n.
Proof.
intros inst ly S W mem md p n HX HR _ HBLK DB.
img_norm.
pose proof (view_n_cgif inst ly S W mem md n HX HR) as VN.
destruct HX as [Ei HAR]. destruct HR as (_ & HQ & _). subst inst.
pose proof (proj1 HAR) as M. pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (find_user_block _ 0 0 0 S p n (am_wf _ _ _ _ M) HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
assert (HK : KV ly S W mem p n k) by exact (conj M (conj IMG (conj Hk (conj Hst (conj Hu Hr))))).
constructor.
- exact VN.
- exact (nonnull_v _ _ _ _ _ _ _ HK).
- exists k. exact (conj Hf (conj Hst (conj Hu Hr))).
- exact (hdr_v _ _ _ _ _ _ _ HK).
- exact (pres_v _ _ _ _ _ _ _ HK).
- exact (shpres_v _ _ _ _ _ _ _ HK).
- exact (junk_pres_v _ _ _ _ M IMG).
- exact (conj (p_zone_v _ _ _ _ _ _ _ HK) (conj (pstatic_v _ _ _ _ _ _ _ HK) (conj (p_al_v _ _ _ _ _ _ _ HK) (nn_range_v _ _ _ _ _ _ _ HK)))).
- exact (qb_v _ _ _ _ M HQ).
- exact DB.
Qed.

(* di_view: every last batch's view (DGif0's dbview with the SLOT half guarded by the room). *)
Lemma view_cgif : forall inst ly S W mem md p n,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem p n -> In (p, n) (blocks S) ->
dview B W ly inst mem S p n.
Proof.
intros inst ly S W mem md p n H R F Hin. apply (view_cgif_of inst ly S W mem md p n H R F Hin).
intros lastb initr ER. exact (dbview_room_cgif inst ly S W mem md n p lastb initr H R Hin ER).
Qed.
End vw.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (owned, quarantine view) a Theorem Labs lane, from its DGif1O.v: ARm-only restatements of YFex / YFfl section facts.  *)
(* A visible byte outside the image is present (YF0x.mbyte_off_apresent). *)
Lemma dgo_vis_off_apresent : forall (H : word -> bool) mem a, off_img a -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. unfold aview in Hv.
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exact (mbyte_off_apresent H mem a b Ha E).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Facts over ARm alone.                                                                                            *)
Section h.
Variable B : asyms.

(* YFex.batch_geom (YFex.v:228) over ARm alone. *)
Lemma dgo_bgeom : forall ly S rd b2, ARm B ly S rd -> In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\ rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= 2 ^ 32 - 2 ^ 29 /\
In x (batch_offs S kBatchClass).
Proof.
intros ly S rd b2 M Hb2. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists x. dgo_splits; try assumption; try lia. unfold region_base. subst x. lia.
Qed.

(* YFex.batches_nodup (YFex.v:244) over ARm alone. *)
Lemma dgo_bnodup : forall ly S rd, ARm B ly S rd -> List.NoDup (map b_self (all_batches S)).
Proof.
intros ly S rd M. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND.
apply YG04.NoDup_app_iff in ND as (_ & ND & _). apply YG04.NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches S) as [|x t IH]; cbn in *; [constructor|].
inversion ND as [|y l N1 N2]; subst. constructor; [|exact (IH N2)].
intros Hin. apply N1. apply in_map_iff in Hin as (x' & E & Hx'). apply in_map_iff. exists x'. split; [lia | exact Hx'].
Qed.

(* YFex.batch_vs_chunk (YFex.v:261) over ARm alone. *)
Lemma dgo_bvc : forall ly S rd b2 x, ARm B ly S rd -> In b2 (all_batches S) -> In x (st_chunks S) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof.
intros ly S rd b2 x M Hb2 Hx. pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_layout _ _ _ _ M) as LO.
destruct (dgo_bgeom ly S rd b2 M Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND.
apply YG04.NoDup_app_iff in ND as (_ & ND & _). apply YG04.NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal). unfold kFreeArrayOffset in Gal.
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs S x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. lia.
Qed.

(* YFex.ext_rounded (YFex.v:155) over ARm alone. *)
Lemma dgo_ext_round : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
ck_rz k + (req_size (ck_req k) + 7) / 8 * 8 <= ck_extent k /\ 1 <= req_size (ck_req k) /\ 0 <= (req_size (ck_req k) + 7) / 8 /\
req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8.
Proof.
intros ly S rd k M Hk. pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(lia)).
apply Z.mod_divide in R2 as [q Hq]; [|lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
- pose proof (primary_geometry (ck_req k) ltac:(lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. lia.
- pose proof (secondary_geometry (ck_req k) ltac:(lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
pose proof (rz_size_bounds (ck_req k)). lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). lia.
Qed.

(* A byte of a chunk's extent outside its user range is owned (YFfl.own_ext_quar, YFfl.v:1004, for any state of
   the chunk). *)
Lemma dgo_own_ext_nonuser : forall ly S rd x a, ARm B ly S rd -> In x (st_chunks S) ->
ck_base B ly x <= a < ck_base B ly x + ck_extent x ->
~ (ck_base B ly x + ck_rz x <= a < ck_base B ly x + ck_rz x + req_size (ck_req x)) -> aowned B ly S a.
Proof.
intros ly S rd x a M Hx Ha Hnu. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (NB : forall y, In y (st_chunks S) -> ck_state y = CAllocated ->
~ (ck_base B ly y + ck_rz y <= a < ck_base B ly y + ck_rz y + req_size (ck_req y))).
{ intros y Hy Hsy Hr. destruct (sptr_eqb (ck_beg y) (ck_beg x)) eqn:Eq.
- apply sptr_eqb_spec in Eq. destruct (In_split_beg _ _ Hx (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
assert (y = x).
{ rewrite E in Hy. apply in_app_iff in Hy as [X|[<-|X]]; [exfalso; apply N1 | reflexivity | exfalso; apply N2]; rewrite <- Eq; apply in_map_iff; exists y; auto. }
subst y. exact (Hnu Hr).
- assert (Hne : ck_beg y <> ck_beg x) by (intros E'; apply sptr_eqb_spec in E'; congruence).
pose proof (user_in_extent B ly S rd y a M Hy Hr) as HE.
pose proof (chunks_disjoint B ly S rd y x M Hy Hx Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia. }
pose proof (am_layout _ _ _ _ M) as LO0.
destruct (ck_beg x) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO0 ltac:(lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
eapply own_ext; [exact M | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x)); split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in DJ. lia.
Qed.

(* The word just past a batch object (a full batch's slot) is owned: it is in the class-24 region, and no live
   chunk's user bytes reach it (batch objects and chunk extents are disjoint, a user range starts 16 bytes or more
   into its extent). *)
Lemma dgo_own_past_batch : forall ly S rd b a, ARm B ly S rd -> In b (all_batches S) ->
ly_space ly + b_self b + kBatchBytes <= a < ly_space ly + b_self b + kBatchBytes + 8 -> aowned B ly S a.
Proof.
intros ly S rd b a M Hb Ha. pose proof (am_layout _ _ _ _ M) as LO.
destruct (dgo_bgeom ly S rd b M Hb) as (x & Eb & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M | unfold kBatchBytes in *; lia |].
intros y Hy Hsy Hr. pose proof (user_in_extent B ly S rd y a M Hy Hr) as HE.
pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & G5 & _).
pose proof (dgo_bvc ly S rd b y M Hb Hy) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kBatchBytes in *. lia.
Qed.

(* The owned set reads the state through its chunks and its fake-stack frames only. *)
Lemma dgo_aowned_same : forall ly X Y a, st_chunks X = st_chunks Y -> st_fs X = st_fs Y -> aowned B ly X a -> aowned B ly Y a.
Proof. intros ly X Y a E1 E2. unfold aowned, aclient_byte, sec_extents, frames. rewrite E1, E2. intros H. exact H. Qed.
End h.

(* DGif0.qx and YFfl's quarantined state have the same chunks and frames (they differ in the internal-allocator
   flag only). *)
Lemma dgo_qx_chunks : forall S k z tr, st_chunks (qx S k z tr) = st_chunks (YFfl.S' S k z tr).
Proof. intros S k z tr. unfold qx, dtick, qk, YFfl.S', YFl0C.depot_after, depot_after. cbv zeta. destruct (z =? 0); reflexivity. Qed.
Lemma dgo_qx_fs : forall S k z tr, st_fs (qx S k z tr) = st_fs (YFfl.S' S k z tr).
Proof. intros S k z tr. unfold qx, dtick, qk, YFfl.S', YFl0C.depot_after, depot_after. cbv zeta. destruct (z =? 0); reflexivity. Qed.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* (post) a Theorem Labs lane, from its DGif1P.v: the depot-zone gap transfer ARm_gap and its helpers.                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* Helpers.                                                                                                         *)

Lemma val_mem_aview_p : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* With the internal allocator already initialized, free's entry step is the tick. *)
Lemma tick_inited : forall S, st_internal_inited S = true -> set_internal_inited true (set_nev (st_nev S + 1) S) = dtick S.
Proof. intros S0 E0. unfold dtick. destruct S0; cbn in E0 |- *. subst. reflexivity. Qed.

(* A stack window of the released walks' size (ASTACK) that covers Deallocate's (DFSTACK) and stays in the stack. *)
Lemma sp_pick : forall ly sp0, layout_ok ly -> ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
exists sp, ly_stk_lo ly + ASTACK <= sp <= ly_stk_hi ly /\ sp - ASTACK <= sp0 - DFSTACK /\ sp0 <= sp.
Proof.
intros ly sp0 LY H1 H2. pose proof (lo_top _ LY) as (T1 & T2 & _).
exists (Z.min (ly_stk_hi ly) (sp0 + (ASTACK - DFSTACK))). unfold ly_bot, kStackSpan, ASTACK, DGbaseC.DFSTACK, DFSTACK in *. lia.
Qed.

(* Where the thread object, the context page and the D page are (layout_ok's extents). *)
Lemma geo_TCD : forall ly, layout_ok ly -> img_cover ly ->
zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\
zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_T ly, kThreadObjSize) (ly_C ly, 256) /\ zdisjoint (ly_T ly, kThreadObjSize) (ly_D ly, 4096) /\
kHighMemBeg <= ly_stk_lo ly.
Proof.
intros ly LY IMG. pose proof (lo_app _ LY) as HA. pose proof (lo_disj _ LY) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> nth_error (static_extents ly) i = Some (x, sz) ->
nth_error (static_extents ly) (i + S (8 - i)) = Some (ly_img ly) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hs Hi Hsz. exact (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He) (pairwise_ij_f _ _ i (8 - i) _ _ HD Hs Hi)). }
split; [exact (Z3 2%nat _ _ eq_refl eq_refl eq_refl ltac:(unfold kThreadObjSize; lia))|].
split; [exact (Z3 6%nat _ _ eq_refl eq_refl eq_refl ltac:(lia))|].
split; [exact (Z3 7%nat _ _ eq_refl eq_refl eq_refl ltac:(lia))|].
split; [exact (pairwise_ij_f _ _ 2 5 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 6 1 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 7 0 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 2 3 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 2 4 _ _ HD eq_refl eq_refl)|].
pose proof (lo_top _ LY) as (_ & _ & _ & _ & _ & _ & T7). exact T7.
Qed.

(* Where the constant cells are (YFfy.Tfib_const_loc): the low image outside the internal allocator's zone, the
   image's shadow, the thread object's first 80 bytes, the context page, the D page. *)
Definition cloc (ly : alayout) (a : Z) : Prop :=
(TFIB_IMG_LO <= a < TFIB_IAL_LO \/ TFIB_IAL_HI <= a < TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= a < TFIB_IMG_END \/
 SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8) \/
(ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 256) \/ (ly_D ly <= a < ly_D ly + 4096).
Lemma const_loc : forall B ly, TfibSyms B -> ly_tsd ly = TFIB_TSD ->
Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> cloc ly (aeval B ly (c_at c) + i)) (as_const B ly).
Proof.
intros B ly TS HTSD. rewrite (ts_const _ TS). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YFfy.Tfib_const_loc ly) c Hc) as K. unfold YFfy.const_loc_ok in K.
unfold cloc. destruct (c_at c); try discriminate K; cbn [aeval]; rewrite ?HTSD, ?(ts_inst _ TS), ?(ts_tp _ TS);
unfold YFfy.low_ok in K; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *;
first [ left; lia | right; left; lia | right; right; left; lia | right; right; right; lia ].
Qed.

(* A cell whose every byte reads as in one of two readers where it holds, holds. *)
Lemma cell_holds_mix : forall B ly (rd1 rd2 rd' : reader) c, cell_holds B ly rd1 c -> cell_holds B ly rd2 c ->
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
 rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd' c.
Proof.
intros B ly rd1 rd2 rd' c H1 H2 Hm. unfold cell_holds in *. cbv zeta in *. destruct (c_val c) as [e|m v].
- intros k Hk. destruct (Hm (Z.of_nat k) ltac:(lia)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct (Hm 0 ltac:(lia)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; assumption.
Qed.

Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]); fail.
Ltac fcons' := apply Forall_cons; [cbn; lia|].

Lemma le_byte_hb1 : forall hb1, 0 <= hb1 < 256 -> YG0f.le_byte (2 + 256 * hb1) 4 1 = hb1.
Proof.
intros hb1 H. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small (2 + 256 * hb1) 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (2 + 256 * hb1) with (2 + hb1 * 256) by ring. rewrite Z.div_add by lia. change (2 / 256) with 0. rewrite Z.add_0_l.
apply Z.mod_small. lia.
Qed.

(* A chunk of the list that holds [g] makes find_chunk_at answer. *)
Lemma find_chunk_some : forall B ly l g k, In k l -> ck_base B ly k <= g < ck_base B ly k + ck_extent k ->
exists x, find_chunk_at B ly l g = Some x.
Proof.
intros B ly l g k. induction l as [|k' t IH]; intros Hk Hg; [destruct Hk|]. cbn [find_chunk_at].
destruct ((ck_base B ly k' <=? g) && (g <? ck_base B ly k' + ck_extent k')) eqn:E; [eexists; reflexivity|].
destruct Hk as [<-|Hk].
- exfalso. apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
- exact (IH Hk Hg).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The gap: the depot zone DGgi.DZONE minus the depot footprint.  The depot callee's contract (DGif0.di_depot) fixes *)
(* memory outside the whole DZONE only, and dpost_cgif fixes only the depot's own cells and the constant cells      *)
(* there, so the memory at Deallocate's return is unknown on the gap.  ARm_gap: no ARm conjunct reads the gap but   *)
(* the constant cells (am_const), which the caller supplies at the new memory.                                     *)

Lemma gap_low : forall B ly a, DGgi.DZONE ly a -> ~ depot_footprint B ly a -> 0x17a308 <= a < 0x5caa90.
Proof.
intros B ly a Hd Hf. dgn; unfold DGgi.DZONE in Hd. unfold depot_footprint in Hf.
destruct Hd as [X|[X|X]]; [exact X | exfalso; apply Hf; tauto | exfalso; apply Hf; tauto].
Qed.

(* An address outside the gap (and in the address space). *)
Definition ngp (B : asyms) (ly : alayout) (a : Z) : Prop :=
0 <= a < 2 ^ 64 /\ (a < 0x17a308 \/ 0x5caa90 <= a \/ depot_footprint B ly a).

Lemma gap_agree : forall B ly (Hw : word -> bool) (mem memP : word -> option byte),
(forall x : word, ~ (DGgi.DZONE ly (bv_unsigned x) /\ ~ depot_footprint B ly (bv_unsigned x)) -> memP x = mem x) ->
forall a, ngp B ly a -> aview tfibsegs Hw memP a = aview tfibsegs Hw mem a.
Proof.
intros B ly Hw mem memP HAG a (Ha & Hn). apply aview_same. apply HAG. rewrite unsigned_lit_small by exact Ha.
intros [Hd Hf]. pose proof (gap_low B ly a Hd Hf). destruct Hn as [X|[X|X]]; [lia | lia | exact (Hf X)].
Qed.

(* The gap is in the image, where the reader never answers None. *)
Lemma gap_vis : forall B ly (Hw : word -> bool) (mem memP : word -> option byte),
(forall x : word, ~ (DGgi.DZONE ly (bv_unsigned x) /\ ~ depot_footprint B ly (bv_unsigned x)) -> memP x = mem x) ->
forall a, aview tfibsegs Hw mem a <> None -> aview tfibsegs Hw memP a <> None.
Proof.
intros B ly Hw mem memP HAG a. unfold aview, mbyte, mrestrict. set (x := Z_to_bv 64 a).
destruct (Hw x) eqn:Hx; intros Hv; [exact Hv|].
assert (Ux : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
destruct (Z_lt_le_dec (bv_unsigned x) 0x17a308) as [L|L].
{ rewrite (HAG x); [exact Hv|]. intros [Hd Hf]. pose proof (gap_low B ly _ Hd Hf). lia. }
destruct (Z_lt_le_dec (bv_unsigned x) 0x5caa90) as [L2|L2].
2:{ rewrite (HAG x); [exact Hv|]. intros [Hd Hf]. pose proof (gap_low B ly _ Hd Hf). lia. }
assert (ROM : seg_rom tfibsegs x <> None).
{ pose proof (YB13.tfib_rom_all (bv_unsigned x) ltac:(lia)) as R. rewrite Z_to_bv_bv_unsigned in R. exact R. }
destruct (memP x); [discriminate|]. destruct (seg_rom tfibsegs x) eqn:E; [discriminate|]. exfalso. apply ROM. first [exact E | reflexivity].
Qed.

(* The gap as a boolean, to patch a memory on it. *)
Definition zin (lo hi a : Z) : bool := (lo <=? a) && (a <? hi).
Definition gapb (B : asyms) (ly : alayout) (a : Z) : bool :=
zin 0x17a308 0x5caa90 a && negb (zin (as_depot B) (as_depot B + d_map1 + 8 * 32768) a || zin (ly_NB ly) (ly_NB ly + kNodesBlockSize) a ||
zin (ly_SB ly) (ly_SB ly + kStoreBlockSize) a || zin (as_store B) (as_store B + 64) a).
Lemma gapb_true : forall B ly a, gapb B ly a = true -> DGgi.DZONE ly a /\ ~ depot_footprint B ly a.
Proof. intros B ly a H. unfold gapb, zin in H. dgn; unfold DGgi.DZONE, depot_footprint. lia. Qed.
Lemma gapb_false : forall B ly a, gapb B ly a = false -> ~ (DGgi.DZONE ly a /\ ~ depot_footprint B ly a).
Proof. intros B ly a H. unfold gapb, zin in H. dgn; unfold DGgi.DZONE, depot_footprint. lia. Qed.

(* A cell is read outside the gap. *)
Definition cng (B : asyms) (ly : alayout) (c : acell) : Prop :=
forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ngp B ly (aeval B ly (c_at c) + j).

(* The transfer.  Every conjunct of ARm that reads memory, and why the gap does not change it:
   - am_const: the constant cells; premise HC (dpost_cgif's third conjunct gives them on the DZONE);
   - am_cells: no cell of acells is in the gap: regions (rinfo page, high), caches / thread / qc_cells (thread
     object, zone3), chunk metadata (chunk extent, zone3), secondary cells (instance object, below the gap; the
     pointer array, zone3; the secondary pages, zone3), batch cells (batch class region, high), fake stack (zone3),
     depot cells (depot footprint), internal allocator cells (below the gap);
   - am_fa: the free arrays (primary region, high); am_flags: the fake stack flags (zone3);
   - am_depot: the depot table and nodes (depot footprint; YFfy.depot_mem_ok_agree);
   - am_shadow, am_zshadow: shadow bytes (at SHADOW_OFF and above, above the gap);
   - am_junk, am_areas, am_client: visibility only, which holds on the whole image (YB13.tfib_rom_all);
   - am_zero: the internal allocator's zero ranges (below the gap). *)
Lemma ARm_gap : forall B ly S (Hw : word -> bool) (mem memP : word -> option byte), TfibSyms B -> img_cover ly ->
ARm B ly S (aview tfibsegs Hw mem) ->
(forall x : word, ~ (DGgi.DZONE ly (bv_unsigned x) /\ ~ depot_footprint B ly (bv_unsigned x)) -> memP x = mem x) ->
Forall (cell_holds B ly (aview tfibsegs Hw memP)) (as_const B ly) ->
ARm B ly S (aview tfibsegs Hw memP).
Proof.
intros B ly S Hw mem memP TS IMG M HAG HC.
set (rd := aview tfibsegs Hw mem) in *. set (rdP := aview tfibsegs Hw memP) in *.
pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_wf _ _ _ _ M) as WF.
assert (AGR : forall a, ngp B ly a -> rdP a = rd a) by exact (gap_agree B ly Hw mem memP HAG).
assert (VISR : forall a, rd a <> None -> rdP a <> None) by exact (gap_vis B ly Hw mem memP HAG).
pose proof (YFf0.HIGH B ly S rd M IMG) as (HP1 & HP2 & ZQ & Q2 & ZT & T2 & ZF & F2 & ZNB & NB2 & ZSB & SB2 & ZC & C2 & HS1 & HS2 & PS1 & PS2 & STK).
assert (NZ : forall x sz, zone3 x sz -> forall a, x <= a < x + sz -> ngp B ly a).
{ intros x sz Z a Ha. unfold zone3, zone3cases in Z. ceil. unfold ngp.
unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
split; [lia|]. destruct (Z_lt_le_dec a 0x17a308) as [L|L]; [left; exact L | right; left; lia]. }
assert (NH : forall a, kHighMemBeg <= a < ASAN_CEIL -> ngp B ly a).
{ intros a Ha. ceil. unfold ngp, kHighMemBeg, ASAN_CEIL in *. split; [lia | right; left; lia]. }
assert (NL : forall a, 0 <= a < 0x17a308 -> ngp B ly a) by (intros a Ha; unfold ngp; split; [lia | left; lia]).
assert (NF : forall a, 0 <= a < 2 ^ 64 -> depot_footprint B ly a -> ngp B ly a) by (intros a Ha Hf; split; [exact Ha | right; right; exact Hf]).
assert (CR : forall c lo len, (forall a, lo <= a < lo + len -> ngp B ly a) -> lo <= aeval B ly (c_at c) ->
aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cng B ly c).
{ intros c lo len R H1 H2 j Hj. apply R. lia. }
assert (FCR : forall l lo len, (forall a, lo <= a < lo + len -> ngp B ly a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l -> Forall (cng B ly) l).
{ intros l lo len R H. eapply Forall_impl; [|exact H]. intros c [H1 H2]. exact (CR c lo len R H1 H2). }
assert (NI : forall a, as_inst B <= a < as_inst B + 3632 -> ngp B ly a) by (intros a Ha; apply NL; rewrite (ts_inst _ TS) in Ha; unfold TFIB_INST in Ha; lia).
assert (NT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ngp B ly a) by exact (NZ _ _ ZT).
(* the batches are in the batch class's region *)
assert (BATCH : forall b, In b (all_batches S) -> forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ngp B ly a).
{ intros b Hb a Ha.
assert (Hsp : ly_stk_lo ly + ASTACK <= ly_stk_hi ly <= ly_stk_hi ly) by (pose proof (lo_top _ LO) as (T1 & T2' & _); unfold ly_bot, kStackSpan, ASTACK in *; lia).
destruct (YFex.batch_geom B ly S rd M b 17 ltac:(split; [lia | reflexivity]) (ly_stk_hi ly) Hsp b Hb) as (x & Ex & Px & _ & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
apply NH. unfold kBatchBytes, kFreeArrayOffset in *. lia. }
assert (BC : forall l, incl l (all_batches S) -> Forall (cng B ly) (batch_cells l)).
{ induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
pose proof (BATCH b (Hincl b (or_introl eq_refl))) as OR. unfold kBatchBytes in OR.
apply Forall_cons; [eapply CR; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix.
eapply CR; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx. }
assert (CNG : Forall (cng B ly) (acells B ly S)).
{ unfold acells. rewrite !Forall_app. splits.
- (* region info *) apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
apply (FCR _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; apply NH; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia|].
unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
- (* caches *) apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
apply (FCR _ (ly_T ly) kThreadObjSize NT).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
+ destruct WC as [PM PL]. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
+ repeat fcons'. apply Forall_nil.
- (* chunk metadata *) apply Forall_flat_map'. intros k Hk. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q2' & _).
apply (FCR _ (ck_base B ly k) (ck_rz k)); [intros a Ha; apply (NZ _ _ (YFex.ZCH B ly S rd M IMG k Hk)); lia|].
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- (* secondary *) pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells.
apply Forall_cons; [eapply CR; [exact NI | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply CR; [exact NI | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply CR; [exact NI | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
+ apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply CR; [exact (NZ _ _ ZQ) | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
+ apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q2' & _).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & GA & _). cbn [fst snd] in GA.
pose proof (YFex.SECX B ly S rd M _ 9 (ly_img ly) Gin eq_refl) as GD.
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req k)) IMG ltac:(unfold kPage in *; lia) GA GD) as ZS.
assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + 32 -> ngp B ly a) by (intros a Ha; apply (NZ _ _ ZS); unfold kPage in *; lia).
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply CR; [exact OR | cbn; lia | cbn; lia]).
- (* quarantine *) unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply CR; [exact NI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact NI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
+ do 4 (apply Forall_cons; [eapply CR; [exact NT | cbn; lia | cbn; unfold kThreadObjSize; lia]|]).
apply BC. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
+ do 4 (apply Forall_cons; [eapply CR; [exact NI | cbn; lia | cbn; lia]|]).
apply BC. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
- (* fake stack *) assert (OR : forall a, ly_F ly <= a < ly_F ly + kFakeFramesOff -> ngp B ly a) by (intros a Ha; apply (NZ _ _ ZF); unfold kFakeFramesOff, kFakeStackSize in *; lia).
unfold kFakeFramesOff in OR. unfold fs_cells.
apply Forall_cons; [eapply CR; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply CR; [exact OR | cbn; lia | cbn; lia].
- (* depot *) assert (OD : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> ngp B ly a).
{ intros a Ha. apply NF; [rewrite (ts_depot _ TS) in Ha; unfold TFIB_DEPOT in Ha; lia | left; unfold d_map1; lia]. }
assert (OS : forall a, as_store B <= a < as_store B + 32 -> ngp B ly a).
{ intros a Ha. apply NF; [rewrite (ts_store _ TS) in Ha; unfold TFIB_STORE in Ha; lia | right; right; right; lia]. }
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply CR; [exact OD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply CR; [exact OS | cbn; lia | cbn; lia]|]. apply Forall_nil.
- (* internal allocator *) unfold ialloc_cells. cbv zeta.
repeat (apply Forall_cons; [eapply (CR _ 0 0x17a308); [intros a Ha; apply NL; lia
| cbn; rewrite ?(ts_ial_flag _ TS), ?(ts_ial_lo _ TS), ?(ts_ial_w _ TS); unfold TFIB_IAL_FLAG, TFIB_IAL_LO, TFIB_IAL_W; lia
| cbn; rewrite ?(ts_ial_flag _ TS), ?(ts_ial_lo _ TS), ?(ts_ial_w _ TS); unfold TFIB_IAL_FLAG, TFIB_IAL_LO, TFIB_IAL_W; lia]|]).
apply Forall_nil.
- (* thread *) unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
eapply CR; [exact NT | cbn; unfold t_unwinding; lia | cbn; unfold t_unwinding, kThreadObjSize; lia]. }
constructor.
- exact (am_wf _ _ _ _ M).
- exact (am_universe _ _ _ _ M).
- exact (am_syms _ _ _ _ M).
- exact LO.
- exact (am_placed _ _ _ _ M).
- exact HC.
- exact (am_const_owned _ _ _ _ M).
- apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) c Hc)|].
intros j Hj. apply AGR. exact (proj1 (Forall_forall _ _) CNG c Hc j Hj).
- (* free arrays *) intros c i v Hc Hi Hv kk Hkk. rewrite AGR; [exact (am_fa _ _ _ _ M c i v Hc Hi Hv kk Hkk)|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5).
apply NH. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
- (* fake stack flags *) intros cid pos Hc Hp. rewrite AGR; [exact (am_flags _ _ _ _ M cid pos Hc Hp)|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. apply (NZ _ _ ZF). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- (* depot table *) assert (DM : depot_mem_ok B ly S rd).
{ split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat apply Forall_cons; try apply Forall_nil;
first [ apply J; unfold ajunk; do 2 right; repeat (apply in_or_app; first [ left; inlist | right ]); inlist
| apply A; unfold aareas; repeat (apply in_or_app; first [ left; inlist | right ]); inlist ]. }
assert (FPAG : forall a, depot_footprint B ly a -> rdP a = rd a).
{ intros a Hf. apply AGR. apply NF; [|exact Hf]. unfold depot_footprint in Hf. rewrite (ts_depot _ TS), (ts_store _ TS) in Hf.
unfold zone3 in ZNB, ZSB. ceil. unfold TFIB_DEPOT, TFIB_STORE, d_map1, kNodesBlockSize, kStoreBlockSize, ASAN_CEIL in *. lia. }
exact (proj1 (proj2 (YFfy.depot_mem_ok_agree B ly S S rd rdP WF (am_universe _ _ _ _ M) eq_refl FPAG DM))).
- (* shadow *) intros g v Hg8 HS. rewrite AGR; [exact (am_shadow _ _ _ _ M g v Hg8 HS)|].
assert (GB : 4096 <= g < ASAN_CEIL).
{ unfold ashadow in HS. destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
- apply find_chunk_at_In in F as [Hx Hgx]. pose proof (YFex.ZCH B ly S rd M IMG x Hx) as ZX. unfold zone3 in ZX. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
destruct (in_rangesb_true _ _ R) as (lo & len & Hin & Hg).
exact (YFex.fa_poison_high B ly S rd M (mkBatch 0 []) lo len g Hin Hg). }
ceil. unfold ngp, shadow_addr, SHADOW_OFF, ASAN_CEIL in *. split; [lia | right; left; lia].
- (* zero shadow *) pose proof (am_zshadow _ _ _ _ M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *.
rewrite AGR; [exact Z0|].
assert (RB : 0 <= fst r /\ fst r + snd r <= kHighMemEnd).
{ unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd].
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _ & _ & T7). unfold kHighMemBeg in T7. lia.
- rewrite (ts_zsh _ TS) in Hr. unfold Tfib_zero_shadow in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [fst snd]; unfold kHighMemEnd; lia. }
unfold ngp, SHADOW_OFF, kHighMemEnd in *. split; [lia | right; left; lia].
- exact (Forall_range_vis_keep B ly rd rdP _ VISR (am_junk _ _ _ _ M)).
- exact (Forall_range_vis_keep B ly rd rdP _ VISR (am_areas _ _ _ _ M)).
- exact (Forall_range_vis_keep B ly rd rdP _ VISR (am_client _ _ _ _ M)).
- (* the internal allocator's zero ranges *) pose proof (am_zero _ _ _ _ M) as Z0. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) Z0 r Hr i Hi) as Z1.
rewrite AGR; [exact Z1|]. unfold ialloc_zero in Hr. cbv zeta in Hr.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; apply NL;
rewrite ?(ts_ial_lo _ TS), ?(ts_ial_hi _ TS), ?(ts_ial_w _ TS) in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia.
- exact (am_tsd _ _ _ _ M).
- exact (am_static_img _ _ _ _ M).
Qed.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable L24 : Z.

(* (post) a Theorem Labs lane: di_post_n, di_lpost_d, di_post_c. *)

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_post_n: the NULL arm (YFg3.FINH's AR part over YFf0.free_finn_ARm).                                           *)

Lemma post_n_cgif : forall inst ly S W mem0 md0 n tr sp0 mem' mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem0 PNull n -> tr_admit (as_universe B) S tr ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
dmem_n W ly sp0 mem0 mem' ->
(exists trc, apath (free PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
ARX_cgif B inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (dtick S).
Proof.
intros inst ly S W mem0 md0 n tr sp0 mem' mat [Ei HAR] [Hev [HQ Hii]] _ HU Hlo Hhi Hbot Hal (MEQ & IALP & UNW & PRES) _.
img_norm.
pose proof HAR as (M & LED & BUD & MW & HSH).
pose proof (am_layout _ _ _ _ M) as LY. pose proof (img_cover_of_ledger ly S md0 LED) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ M); exact (ts_tsd B TS)).
destruct (sp_pick ly sp0 LY Hlo Hhi) as (sp & HSP & SP1 & SP2).
pose proof (geo_TCD ly LY IMG) as (ZT & ZC & ZD & DTS & DCS & DDS & DTC & DTD & HMB).
pose proof (lo_top _ LY) as (T1 & T2 & _ & T4 & _).
set (rd := aview tfibsegs (w_H W) mem0) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFf0.D B ly sp a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ (Z_to_bv 64 a)); rewrite unsigned_lit_small by exact Ha.
- intros X. apply ND. right; left. unfold YFf0.DS. unfold ASTACK, DGbaseC.DFSTACK, DFSTACK in *. lia.
- intros X. apply ND. left. exact X.
- intros X. apply ND. right; right. dgn; unfold DGgi.IZONE in X. unfold YFf0.DI. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS). exact X. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem0 x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (0x10000 <= a' < 0x5fd000)).
{ intros X. apply (YB13.tfib_rom_all a' X). rewrite Ex. exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (sp0 - DFSTACK) sp0 a') as [C1|C1]. { exact (PRX mem' (PRES a' C1) E'). }
destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
{ pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a' in U by lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C4|C4]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C4; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C5|C5]; [apply NIMG; unfold TFIB_IAL_FLAG in C5; lia|].
rewrite (MEQ x) in E'; [congruence | exact C1 | exact C2 | dgn; unfold DGgi.IZONE; tauto]. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
assert (C1 : ~ (sp0 - DFSTACK <= a < sp0)) by (intros C1; exact (PRX mem' (PRES a C1))).
assert (C2 : ~ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1)).
{ intros C2. pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a in U by lia.
rewrite (seg_rom_none_high a ltac:(clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd in *; lia)) in U. fold x in U. rewrite Hx in U. discriminate. }
apply (MEQ x); rewrite Ux.
- exact C1.
- exact C2.
- dgn; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia. }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview_p _ _ _ _ _ 0 UNW ltac:(lia)). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (YFf0.S' S)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ dgn; unfold DGgi.IAL_POST in IALP. cbv zeta in IALP. destruct IALP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. change (st_internal_inited (YFf0.S' S)) with true. rewrite (ts_ial_flag _ TS), (ts_ial_lo _ TS), (ts_ial_w _ TS), (ts_ial_hi _ TS).
subst rd'. split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I1). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I2). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I3 Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) mem' a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TS); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc)|].
intros i Hi. pose proof (proj1 (Forall_forall _ _) (const_loc B ly TS HTSD) c Hc i Hi) as CL.
assert (R : 0 <= aeval B ly (c_at c) + i < 2 ^ 64 /\ ~ YFf0.D B ly sp (aeval B ly (c_at c) + i)).
{ unfold cloc in CL. unfold YFf0.D, YFf0.DT, YFf0.DS, YFf0.DI. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS).
set (a := aeval B ly (c_at c) + i) in *. clear - CL ZT ZC ZD DTS DCS DDS DTC DTD HMB HSP T4.
unfold zone3, zone3cases, zdisjoint in *. cbn [fst snd] in *. ceil.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd,
ASAN_CEIL, kThreadObjSize, t_unwinding, ASTACK in *. lia. }
exact (AG _ (proj1 R) (proj2 R)). }
pose proof (YFf0.free_finn_ARm B TS ly S rd rd' M Hev sp HSP IMG AG VIS NEW_unw IAL CONST') as MF.
rewrite <- (tick_inited S Hii).
split.
- split; [exact Ei|].
split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (YFf0.ALedger_S' ly S tfibsegs md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact PIN].
eapply Z.le_trans; [exact BUD | exact (YFf0.abudget_le S)].
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly S _ (w_H W) mem0 mem' (al_img_env tfibsegs ly S md0 (am_layout B ly S _ M) LED) M HSH VIS HSK).
* eapply (aclient_band_same_frames B ly S); [exact MF | reflexivity].
* reflexivity.
* intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize in ZT. unfold kHighMemBeg in ZT, HMB.
unfold YFf0.D, YFf0.DT, YFf0.DS, YFf0.DI. intros [X|[X|X]].
-- clear - X SBg ZT. unfold t_unwinding in *. lia.
-- clear - X SBg HMB HSP. unfold ASTACK in *. lia.
-- rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS) in X. clear - X SBg. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in X. lia.
- apply (qtight_ext S); [reflexivity | reflexivity | reflexivity | exact (qmeter_tight _ HQ)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_lpost_d: qtight at the end of a granted path of drain_body (YFeu.drain_body_apost), with the extra premise   *)
(* ARX of the enqueued state X' (the premise di_enqueue's acall_post_x hands the walk).                             *)

Lemma lpost_d_cgif : forall inst ly S W mem md p n tr k z nb X' W' mem' md' trc r,
ARX_cgif B inst ly S W mem md -> ARX_cgif B inst ly X' W' mem' md' ->
rpre_dealloc_cgif S n -> In (p, n) (blocks S) -> tr_admit (as_universe B) S tr ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
kQuarantineCacheMax < qc_bytes (st_qthread X') ->
apath (drain_body X' X') trc r -> gflag trc = true -> qtight (snd r).
Proof.
intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r [_ HAR] [_ HARX] [Hev [HQ Hii]] HBLK HU Hf Hst HQ' Hnb HCK' HQG' HDR HP _.
img_norm.
pose proof (proj1 HAR) as M. pose proof (am_wf _ _ _ _ M) as WF.
destruct (find_user_block _ 0 0 0 S p n WF HBLK) as (k0 & Hf0 & Hk & _ & _ & _). rewrite Hf in Hf0. injection Hf0 as <-.
assert (EX : qx S k z tr = YFfl.S' S k z tr) by (unfold qx, YFfl.S', qk; rewrite <- (tick_inited S Hii); reflexivity).
rewrite EX in HQ', Hnb, HCK', HQG'.
pose proof (YFfl.quar_S' B ly S _ M k Hk Hst z tr) as [QX1 QX2].
pose proof (unq_push (YFfl.S' S k z tr) X' (qk k) nb HCK' HQ' HQG' ltac:(intros ->; exact Hnb)) as UQ. unfold unq in UQ.
pose proof (qmeter_tight _ HQ) as (T1 & T2 & T3).
assert (WFX' : Wf (as_universe B) X') by exact (am_wf _ _ _ _ (proj1 HARX)).
assert (QT : st_qthread (YFfl.S' S k z tr) = st_qthread S) by exact (YFfl.S'_qthread S k z tr).
assert (QG : st_qglobal (YFfl.S' S k z tr) = st_qglobal S) by exact (YFfl.S'_qglobal S k z tr).
assert (NK : ck_n (qk k) = ck_n k) by reflexivity. rewrite NK in UQ.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKn _].
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & _ & R3).
assert (QLX' : qloose X').
{ unfold qloose. rewrite HQG', QG. split; [|split].
- rewrite HQ', QT. destruct nb; cbn [qc_push qc_bytes]; rewrite NK; unfold ck_n, MALLOC_MAX, kQuarantineCacheMax, kBatchBytes in *; lia.
- unfold kQuarantineMax in T2. lia.
- lia. }
pose proof (drain_body_apost (as_universe B) 0 0 0 X' WFX' QLX' HDR trc r HP) as (_ & _ & QT6 & QG6 & UQ6).
unfold qtight. split; [exact QT6|]. split.
- eapply Z.le_trans; [exact QG6|]. rewrite HQG', QG. unfold kQuarantineMax in *. lia.
- unfold unq in UQ6. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_post_c: the arm whose last batch has room (YFfy.FINH's AR part over YFex.free_fin_ARm).  The released lemma   *)
(* wants the return memory equal to the entry memory outside its write set, which dmem_c does not give on the gap; *)
(* so YFex runs from the entry memory patched on the gap (memP), whose ARm is ARm_gap's.                          *)

Lemma post_c_cgif : forall inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem0 p n -> In (p, n) (blocks S) -> tr_admit (as_universe B) S tr ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_c W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb (AGif1.dpost_cgif B inst ly S W tr z) mem' ->
(exists trc, apath (free p tr S) trc (tt, qfin_c S k z tr) /\ gflag trc = true) ->
ARX_cgif B inst ly (qfin_c S k z tr) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (qfin_c S k z tr).
Proof.
intros inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat [Ei HAR] [Hev [HQ Hii]] _ HBLK HU Hf Hst Hrev Hroom Hcache
Hlo Hhi Hbot Hal Hhb HV0 DM _.
img_norm.
destruct DM as ((memD & (AOKD & DEPD & CSTD) & PRD & EQD) & MEQ & IALP & SHV & PRS & PRW & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
pose proof HAR as (M0 & LED & BUD & MW & HSH).
pose proof (am_layout _ _ _ _ M0) as LY. pose proof (img_cover_of_ledger ly S md0 LED) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ M0); exact (ts_tsd B TS)).
pose proof (am_wf _ _ _ _ M0) as WF.
destruct (find_user_block _ 0 0 0 S p n WF HBLK) as (k0 & Hf0 & Hk & _ & Hu & Hr). rewrite Hf in Hf0. injection Hf0 as <-.
subst p n.
(* the chunk header's second byte (the chunk cell AVmask 127 17 at the entry memory) *)
assert (HB1M : Z.land hb1 127 = 17).
{ pose proof (chunk_facts B ly S _ k M0 Hk) as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & GG').
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG']; cbn; lia. }
assert (C : cell_holds B ly (aview tfibsegs (w_H W) mem0) (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M0)). unfold acells. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite EA2 in C. destruct C as (b & Hb & Hm).
replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (sptr_addr B ly (ck_user k) - 16 + Z.of_nat 1) in Hb
by (rewrite G4'; unfold kChunkHeaderSize; lia).
rewrite (val_mem_aview_p _ _ _ _ _ 1 HV0 ltac:(lia)) in Hb. injection Hb as <-. rewrite le_byte_hb1 in Hm by exact Hhb. exact Hm. }
(* the stack window, the geometry *)
destruct (sp_pick ly sp0 LY Hlo Hhi) as (sp & HSP & SP1 & SP2).
pose proof (geo_TCD ly LY IMG) as (_ & _ & ZD & DTS & DCS & DDS & DTC & DTD & HMB).
pose proof (YFex.HIGH B ly S _ M0 k lastb initr hb1 Hk Hrev (conj Hhb HB1M) sp HSP IMG)
as (HP1 & HP2 & ZQ & Q2 & ZT & T2 & ZF & F2 & ZNB & NB2 & ZSB & SB2 & ZC & C2 & HS1 & HS2 & PS1 & PS2 & ZK & K2 & RZ16 & BV1 & BV2 & STK & BV3 & BV4).
pose proof (YFex.ext_rounded B ly S _ M0 k lastb Hk) as (ER & NN1 & NN2 & NN3).
pose proof (YFex.Hu B ly S _ M0 k Hk) as G4.
pose proof (YFex.u_al8 B ly S _ M0 k lastb Hk) as (U8 & B8 & R8).
pose proof (chunk_facts B ly S _ k M0 Hk) as (G1 & G2 & G3 & _ & G5 & G6 & G7 & G8 & _).
pose proof (YFex.anyX B ly S _ M0 lastb k 2 _ Hk eq_refl ltac:(discriminate)) as KT.
pose proof (YFex.anyX B ly S _ M0 lastb k 6 _ Hk eq_refl ltac:(discriminate)) as KC.
pose proof (YFex.anyX B ly S _ M0 lastb k 7 _ Hk eq_refl ltac:(discriminate)) as KD.
pose proof (YFex.SX B ly S _ M0 lastb 0 2 _ _ eq_refl eq_refl ltac:(discriminate)) as PT.
pose proof (YFex.SX B ly S _ M0 lastb 0 6 _ _ eq_refl eq_refl ltac:(discriminate)) as PC.
pose proof (YFex.SX B ly S _ M0 lastb 0 7 _ _ eq_refl eq_refl ltac:(discriminate)) as PD.
assert (AOK : aok (set_internal_inited true (set_nev (st_nev S + 1) S)) (KDepot tr) z) by exact AOKD.
assert (HU1 : ck_base B ly k <= sptr_addr B ly (ck_user k)) by (clear - G4 RZ16; lia).
assert (HU2 : sptr_addr B ly (ck_user k) + ck_n k <= ck_base B ly k + ck_extent k) by (clear - G4 ER NN3; lia).
assert (HU3 : 0 <= ck_n k) by (clear - NN1; lia).
(* the entry memory, patched on the gap with the return memory *)
pose (memP := fun x : word => if gapb B ly (bv_unsigned x) then mem' x else mem0 x).
assert (MP1 : forall x : word, DGgi.DZONE ly (bv_unsigned x) -> ~ depot_footprint B ly (bv_unsigned x) -> memP x = mem' x).
{ intros x H1 H2. unfold memP. cbv beta. destruct (gapb B ly (bv_unsigned x)) eqn:G; [reflexivity|]. exfalso. exact (gapb_false _ _ _ G (conj H1 H2)). }
assert (MP2 : forall x : word, ~ (DGgi.DZONE ly (bv_unsigned x) /\ ~ depot_footprint B ly (bv_unsigned x)) -> memP x = mem0 x).
{ intros x H1. unfold memP. cbv beta. destruct (gapb B ly (bv_unsigned x)) eqn:G; [exfalso; exact (H1 (gapb_true _ _ _ G)) | reflexivity]. }
assert (CLR : forall a, cloc ly a -> 0 <= a < 2 ^ 64).
{ intros a CL. clear - CL ZT ZC ZD. unfold cloc in CL. unfold zone3 in ZT, ZC, ZD. ceil.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, ASAN_CEIL, kThreadObjSize in *. lia. }
(* the constant cells at memP: from dpost_cgif on the gap, from the entry memory elsewhere *)
assert (CP : Forall (cell_holds B ly (aview tfibsegs (w_H W) memP)) (as_const B ly)).
{ apply Forall_forall. intros c Hc.
apply (cell_holds_mix B ly (aview tfibsegs (w_H W) memD) (aview tfibsegs (w_H W) mem0) _ c (proj1 (Forall_forall _ _) CSTD c Hc)
(proj1 (Forall_forall _ _) (am_const _ _ _ _ M0) c Hc)).
intros j Hj. pose proof (CLR _ (proj1 (Forall_forall _ _) (const_loc B ly TS HTSD) c Hc j Hj)) as A64.
destruct (gapb B ly (aeval B ly (c_at c) + j)) eqn:G.
- left. apply aview_same. destruct (gapb_true _ _ _ G) as [H1 H2].
rewrite (MP1 (Z_to_bv 64 (aeval B ly (c_at c) + j))) by (rewrite unsigned_lit_small by exact A64; assumption).
apply EQD. rewrite unsigned_lit_small by exact A64. exact H1.
- right. apply aview_same. apply MP2. rewrite unsigned_lit_small by exact A64. exact (gapb_false _ _ _ G). }
pose proof (ARm_gap B ly S (w_H W) mem0 memP TS IMG M0 MP2 CP) as MP.
set (rd0 := aview tfibsegs (w_H W) mem0) in *. set (rdP := aview tfibsegs (w_H W) memP) in *.
set (rd' := aview tfibsegs (w_H W) mem') in *. set (rdD := aview tfibsegs (w_H W) memD) in *.
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
(* YFex's frame premise: outside its write set D the return memory reads as memP *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFex.D B ly k lastb sp a -> rd' a = rdP a).
{ intros a Ha ND. unfold rd', rdP. apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
destruct (gapb B ly a) eqn:G.
- destruct (gapb_true _ _ _ G) as [H1 H2]. symmetry. apply MP1; rewrite Ux; assumption.
- assert (NG : ~ (DGgi.DZONE ly (bv_unsigned (Z_to_bv 64 a)) /\ ~ depot_footprint B ly (bv_unsigned (Z_to_bv 64 a))))
by (rewrite Ux; exact (gapb_false _ _ _ G)).
rewrite (MP2 _ NG).
unfold YFex.D, YFex.DT, YFex.DK, YFex.DB, YFex.DS, YFex.DI, YFex.DH in ND.
apply MEQ; rewrite Ux.
+ intros X. apply ND. unfold dwin_c, DGgiC.WINT, DGgi.WINT, DGgiC.WINB, DGgi.WINB, DGgiC.SLOTv, DGgi.SLOTv, DGgiC.Bv, DGgi.Bv, DGgiC.BCv, DGgi.BCv in X. cbv zeta in X.
destruct X as [X|[X|X]].
* do 3 right; left. unfold ASTACK, DGbaseC.DFSTACK, DFSTACK in *. lia.
* left. lia.
* right. destruct X as [X|[X|[X|X]]]; [left; left; lia | left; right; lia | right; left; left; lia | right; left; right; lia].
+ intros X. apply (gapb_false _ _ _ G). split; [exact X|]. intros F. apply ND. do 5 right; left; exact F.
+ intros X. apply ND. do 4 right; left. dgn; unfold DGgi.IZONE in X. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS). exact X.
+ intros X. apply ND. do 6 right. unfold dshadow, DGgiC.SPv, DGgi.SPv, DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v in X. rewrite Z_div_mult in X by lia. unfold shadow_addr. exact X. }
(* visibility: what memP shows, the return memory shows *)
assert (VIS : forall a, rdP a <> None -> rd' a <> None).
{ intros a Hv HN. unfold rdP, rd', aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
revert Hv HN. destruct (w_H W x) eqn:Hx; intros Hv HN; [exact (Hv HN)|].
revert Hv HN. destruct (seg_rom tfibsegs x) eqn:ROM; intros Hv HN; [destruct (mem' x); discriminate|].
revert HN. destruct (mem' x) as [|] eqn:E'; intros HN; [discriminate|]. clear HN.
revert Hv. destruct (memP x) as [b0|] eqn:E0; intros Hv; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (0x10000 <= a' < 0x5fd000)) by (intros X; apply (YB13.tfib_rom_all a' X); rewrite Ex; exact ROM).
assert (NG : ~ (DGgi.DZONE ly a' /\ ~ depot_footprint B ly a')) by (intros [Hd Hn]; pose proof (gap_low B ly a' Hd Hn); lia).
rewrite (MP2 x NG) in E0.
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False) by (intros m [_ [bb Hb]] Hm; rewrite Ex in Hb; congruence).
destruct (EM (DGgi.SPv (sptr_addr B ly (ck_user k))) (DGgi.SPv (sptr_addr B ly (ck_user k)) + DGgi.CNT8v (req_size (ck_req k))) a') as [Y1|Y1].
{ rewrite (SHV x Y1) in E'. discriminate. }
destruct (EM (sp0 - DFSTACK) sp0 a') as [Y2|Y2]. { exact (PRX mem' (PRS a' Y2) E'). }
assert (WD : (DGgi.WINT ly a' \/ DGgi.WINB ly (sptr_addr B ly (ck_user k)) lastb a') \/ ~ (DGgi.WINT ly a' \/ DGgi.WINB ly (sptr_addr B ly (ck_user k)) lastb a'))
by (unfold DGgiC.WINT, DGgi.WINT, DGgiC.WINB, DGgi.WINB; cbv zeta; lia).
destruct WD as [Y3|Y3]. { exact (PRX mem' (PRW a' Y3) E'). }
assert (Y5 : ~ DGgi.DZONE ly a' \/ DGgi.DZONE ly a') by (dgn; unfold DGgi.DZONE; lia).
destruct Y5 as [Y5|Y5].
2:{ assert (P0 : apresent (w_H W) mem0 a') by (split; [rewrite Ex; exact Hx | exists b0; rewrite Ex; exact E0]).
destruct (PRD a' Y5 P0) as [_ [bd Hbd]]. rewrite Ex in Hbd. rewrite (EQD x Y5) in E'. congruence. }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [Y6|Y6]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in Y6; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [Y7|Y7]; [apply NIMG; unfold TFIB_IAL_FLAG in Y7; lia|].
rewrite (MEQ x) in E'; [congruence | | exact Y5 | fold a'; dgn; unfold DGgi.IZONE; tauto | exact Y1].
unfold dwin_c. intros [X|X]; [exact (Y2 X) | exact (Y3 X)]. }
(* the values the walk wrote *)
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V1 Hi)).
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V2 Hi)).
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V3 Hi)).
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V4 Hi)).
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (ly_space ly + b_self lastb) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V5 Hi)).
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes (st_qthread S) + ck_n k) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V6 Hi)).
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview_p _ _ _ _ _ 0 V7 ltac:(lia)). }
assert (NEW_bb : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 8 + Z.of_nat i) = Some (YG0f.le_byte (b_bytes lastb + ck_n k) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V8 Hi)).
assert (NEW_bc : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 16 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (b_items lastb)) + 1) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V9 Hi)).
assert (NEW_slot : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb)) + Z.of_nat i) =
Some (YG0f.le_byte (sptr_addr B ly (ck_user k) - 16) 8 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V10 Hi)).
assert (NEW_sh : forall a, YFex.DH B ly k a -> rdP a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. unfold YFex.DH, shadow_addr in Hd.
assert (Ha : 0 <= a < 2 ^ 64 /\ TFIB_IMG_END <= a).
{ clear - Hd G1 G2 G4 ER NN1 NN2 NN3 RZ16. unfold in_app in G1. ceil. unfold SHADOW_OFF, ASAN_CEIL, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold rdP, rd', aview, mbyte, mrestrict in Hv |- *.
assert (ROM : seg_rom tfibsegs (Z_to_bv 64 a) = None) by (apply seg_rom_none_high; lia).
revert Hv. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; intros Hv.
- rewrite ROM in Hv. exfalso. exact (Hv eq_refl).
- rewrite (SHV (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. unfold dshadow, DGgiC.SPv, DGgi.SPv, DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v.
rewrite Z_div_mult by lia. exact Hd. }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (YFex.S' S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ dgn; unfold DGgi.IAL_POST in IALP. cbv zeta in IALP. destruct IALP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. rewrite (YFex.S'_inited S k z tr), (ts_ial_flag _ TS), (ts_ial_lo _ TS), (ts_ial_w _ TS), (ts_ial_hi _ TS).
subst rd'. split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I1). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I2). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I3 Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) mem' a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TS); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
(* the depot's memory facts after the put, from dpost_cgif's second conjunct (the footprint is in the DZONE) *)
assert (DEP : depot_mem_ok B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rd').
{ assert (DEPs : depot_mem_ok B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rdD).
{ apply (AGix.depot_mem_ok_ext B ly TS LY IMG HTSD (depot_after z tr S)); [unfold YFl0C.depot_after, depot_after; destruct (z =? 0); reflexivity | exact DEPD]. }
eapply (YFfy.depot_mem_ok_agree B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))
(depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rdD rd'); [| exact (am_universe _ _ _ _ M0) | reflexivity | | exact DEPs].
- apply (WfP_weaken _ 1 1 1); try lia. exact (YFex.sd_wf B ly S _ M0 lastb z tr Hev AOK HU).
- intros a Ha. assert (A64 : (0 <= a < 2 ^ 64) /\ DGgi.DZONE ly a).
{ unfold depot_footprint in Ha. rewrite (ts_depot _ TS), (ts_store _ TS) in Ha. dgn; unfold DGgi.DZONE.
clear - Ha ZNB ZSB. unfold zone3 in ZNB, ZSB. ceil. unfold TFIB_DEPOT, TFIB_STORE, d_map1, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *. lia. }
unfold rd', rdD. apply aview_same. apply EQD. rewrite unsigned_lit_small by exact (proj1 A64). exact (proj2 A64). }
(* the constant cells avoid YFex's write set outside the DZONE *)
assert (CD : forall a, cloc ly a -> ~ DGgi.DZONE ly a -> ~ YFex.D B ly k lastb sp a).
{ intros a CL NDZ.
unfold YFex.D, YFex.DT, YFex.DK, YFex.DB, YFex.DS, YFex.DI, YFex.DH. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS).
intros [X|[X|[X|[X|[X|[X|X]]]]]].
- assert (XT : ly_T ly + 80 <= a < ly_T ly + 4096) by (clear - X; unfold t_qc, t_unwinding, t_stats in X; lia).
clear - XT CL ZT DTC DTD. unfold cloc, zone3, zone3cases, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- assert (XK : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by (clear - X G4 RZ16 ER NN1 NN3; lia).
clear - XK CL ZK KT KC KD. unfold cloc, zone3, zone3cases, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- assert (XB : ly_space ly + b_self lastb <= a < ly_space ly + b_self lastb + 8192) by (clear - X Hroom; unfold kBatchSlots in Hroom; lia).
clear - XB CL BV1 BV3 BV4 PS2 PT PC PD. unfold cloc, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kHighMemBeg, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes in *. lia.
- assert (XS : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - X HSP; unfold ASTACK in *; lia).
clear - XS CL HS1 DTS DCS DDS. unfold cloc, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kHighMemBeg, kThreadObjSize in *. lia.
- clear - X CL ZT ZC ZD. unfold cloc, zone3, zone3cases in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- apply NDZ. dgn; unfold DGgi.DZONE. unfold depot_footprint in X. rewrite (ts_depot _ TS), (ts_store _ TS) in X. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X.
destruct X as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; exact X | left; lia].
- assert (XH : (a < SHADOW_OFF + 8192 \/ SHADOW_OFF + 784896 <= a) /\ SHADOW_OFF <= a < kHighMemBeg).
{ unfold shadow_addr in X. clear - X ZK G4 ER NN1 NN2 NN3 RZ16. unfold zone3, zone3cases in ZK. ceil.
unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear - XH CL ZT ZC ZD. unfold cloc, zone3, zone3cases in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc.
apply (cell_holds_mix B ly rdD rdP rd' c (proj1 (Forall_forall _ _) CSTD c Hc) (proj1 (Forall_forall _ _) (am_const _ _ _ _ MP) c Hc)).
intros j Hj. pose proof (proj1 (Forall_forall _ _) (const_loc B ly TS HTSD) c Hc j Hj) as CL.
pose proof (CLR _ CL) as A64.
assert (DZD : DGgi.DZONE ly (aeval B ly (c_at c) + j) \/ ~ DGgi.DZONE ly (aeval B ly (c_at c) + j)) by (dgn; unfold DGgi.DZONE; lia).
destruct DZD as [DZ|NDZ].
- left. unfold rd', rdD. apply aview_same. apply EQD. rewrite unsigned_lit_small by exact A64. exact DZ.
- right. exact (AG _ A64 (CD _ CL NDZ)). }
pose proof (YFex.free_fin_ARm B TS ly S rdP rd' MP k lastb initr hb1 Hk Hst Hrev Hroom (conj Hhb HB1M) z tr Hev AOK HU sp HSP IMG AG VIS
NEW_hdr NEW_n NEW_qs NEW_qf NEW_ql NEW_qb NEW_unw NEW_bb NEW_bc NEW_slot NEW_sh IAL DEP CONST') as M'.
(* the shadow band, for the AR's shadow part *)
assert (SHP : forall a, DGgi.SPv (sptr_addr B ly (ck_user k)) <= a < DGgi.SPv (sptr_addr B ly (ck_user k)) + DGgi.CNT8v (req_size (ck_req k)) ->
w_H W (Z_to_bv 64 a) = false).
{ intros a Ha. unfold DGgiC.SPv, DGgi.SPv, DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v in Ha. rewrite Z_div_mult in Ha by lia.
change (req_size (ck_req k)) with (ck_n k) in Ha.
pose proof U8 as U8'. apply Z.mod_divide in U8' as [q Hq]; [|lia].
assert (Hq8 : sptr_addr B ly (ck_user k) / 8 = q) by (rewrite Hq; apply Z.div_mul; lia).
rewrite Hq8 in Ha.
assert (Eg : shadow_addr (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) = a).
{ unfold shadow_addr. rewrite Hq. replace (q * 8 + 8 * (a - (SHADOW_OFF + q))) with ((a - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (G8' : (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) mod 8 = 0).
{ rewrite Hq. replace (q * 8 + 8 * (a - (SHADOW_OFF + q))) with ((q + (a - (SHADOW_OFF + q))) * 8) by lia. apply Z_mod_mult. }
assert (Gb : ck_base B ly k <= sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q)) < ck_base B ly k + ck_extent k)
by (clear - Ha G4 RZ16 ER NN2; lia).
destruct (find_chunk_some B ly (st_chunks S) _ k Hk Gb) as (x & Fx).
assert (AS : exists v, ashadow B ly S (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) = Some v)
by (unfold ashadow; rewrite Fx; eexists; reflexivity).
destruct AS as [v Hv].
pose proof (am_shadow _ _ _ _ M0 _ v G8' Hv) as R. rewrite Eg in R.
assert (Ha' : 0 <= a < 2 ^ 64 /\ TFIB_IMG_END <= a).
{ clear - Ha Hq G1 G2 G4 ER NN2 RZ16. unfold in_app in G1. ceil. unfold SHADOW_OFF, ASAN_CEIL, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold rd0, aview, mbyte, mrestrict in R. revert R. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; intros R; [|reflexivity].
rewrite seg_rom_none_high in R by lia. discriminate. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; rewrite Hx in Hh; discriminate).
apply MEQ; rewrite Ux.
- unfold dwin_c. intros [X|[X|X]]; [exact (PRX mem' (PRS a X)) | exact (PRX mem' (PRW a (or_introl X))) | exact (PRX mem' (PRW a (or_intror X)))].
- intros X. dgn; unfold DGgi.DZONE in X. clear - X Ha ZNB ZSB. unfold zone3, zone3cases in ZNB, ZSB.
unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg, TFIB_IMG_LO, TFIB_IMG_END, kNodesBlockSize, kStoreBlockSize in *. lia.
- dgn; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia.
- intros X. pose proof (SHP a X) as F. rewrite Hx in F. discriminate. }
assert (VIS0 : forall a, rd0 a <> None -> rd' a <> None) by (intros a Hv; apply VIS; exact (gap_vis B ly (w_H W) mem0 memP MP2 a Hv)).
assert (NDG : forall g, in_app g 8 -> g mod 8 = 0 -> hfree ly S g -> ~ YFex.D B ly k lastb sp (shadow_addr g)).
{ intros g Hga Hg HF. pose proof (shadow_addr_band_rw g Hga) as SBg.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
unfold YFex.D, YFex.DT, YFex.DK, YFex.DB, YFex.DS, YFex.DI, YFex.DH.
intros [X|[X|[X|[X|[X|[X|X]]]]]].
- clear - X SBg ZT. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, t_qc, t_unwinding, t_stats in *. lia.
- clear - X SBg ZK G4 RZ16 ER NN1 NN3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
- clear - X SBg BV1 Hroom. unfold kHighMemBeg, kBatchSlots in *. lia.
- clear - X SBg HS1 HSP. unfold ASTACK, kHighMemBeg in *. lia.
- rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS) in X. clear - X SBg. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in X. lia.
- unfold depot_footprint in X. rewrite (ts_depot _ TS), (ts_store _ TS) in X. clear - X SBg ZNB ZSB.
unfold zone3, zone3cases, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. lia.
- exact (hfree_shadow_off_range B ly S rd0 k (sptr_addr B ly (ck_user k)) (ck_n k) g M0 Hk HU1 HU2 U8 HU3 Hg HF X). }
(* the final state *)
assert (EQF : qfin_c S k z tr = YFex.S' S k z tr).
{ unfold qfin_c, qx, YFex.S', qk. rewrite <- (tick_inited S Hii). unfold YFl0C.depot_after, depot_after. destruct (z =? 0); reflexivity. }
rewrite EQF.
split.
2:{ apply (YFex.qtight_S' B ly S _ M0 k lastb initr Hk Hst Hrev z tr); [exact Hcache | exact (qmeter_tight _ HQ)]. }
split; [exact Ei|].
split; [exact M' | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (YFex.ALedger_S' B ly S _ M0 k Hk z tr tfibsegs md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact (YFex.asecA_S' B ly S _ M0 k Hk z tr _ PIN)].
eapply Z.le_trans; [exact BUD | exact (YFex.abudget_le B ly S _ M0 k lastb Hk z tr)].
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly S _ (w_H W) mem0 mem' (al_img_env tfibsegs ly S md0 (am_layout B ly S _ M0) LED) M0 HSH VIS0 HSK).
* eapply (aclient_band_same_frames B ly S); [exact M' | unfold frames, YFex.S', depot_after; destruct (z =? 0); reflexivity].
* exact (YFex.sec_extents' B ly S _ M0 k Hk z tr).
* intros g Hg Hga HF Hh.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64 /\ kLowShadowBeg <= shadow_addr g < kHighShadowEnd).
{ pose proof (shadow_addr_band_rw g Hga) as SBg. clear - SBg. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
transitivity (rdP (shadow_addr g)).
-- apply AG; [exact (proj1 Rg) | exact (NDG g Hga Hg HF)].
-- apply (gap_agree B ly (w_H W) mem0 memP MP2). split; [exact (proj1 Rg)|]. right; left. unfold kLowShadowBeg in Rg. lia.
Qed.


(* (di_owned) The walk's writes outside its stack windows: the thread's cells (own_core), the chunk header (own_meta),
   the block's first word (its user bytes, or its extent past them), the depot zone (own_static / own_core) and the
   block's shadow (own_shadow_prim / own_shadow_sec): the cases of YFex.D_owned / YFfl.D_owned at the entry state. *)
Lemma owned_cgif : forall inst ly S W mem md p n k a,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros inst ly S W mem md p n k a [_ HAR] _ Hblk _ Ra Hw.
img_norm.
pose proof (proj1 HAR) as M.
apply In_blocks in Hblk as (k0 & Hk0 & Hst0 & Hu0 & Hr0).
pose proof (chunk_facts B ly S _ k0 M Hk0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (dgo_ext_round B ly S _ k0 M Hk0) as (ER & NN1 & NN2 & NN3).
rewrite <- Hu0, <- Hr0 in Hw |- *. rewrite G4 in Hw |- *.
unfold dwrites in Hw. destruct Hw as [X|[X|[X|[X|X]]]].
- left. cbv beta zeta delta [DGgiC.WINT DGgi.WINT] in X.
eapply (own_core B ly S _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
cbn [fst snd]. unfold t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- left. apply (own_meta B ly S _ k0 a M Hk0).
assert (0 <= match ck_beg k0 with PSec _ _ => kPage | _ => 0 end) by (destruct (ck_beg k0); unfold kPage; lia). lia.
- destruct (Z_lt_le_dec a (ck_base B ly k0 + ck_rz k0 + req_size (ck_req k0))) as [L|L]; [right; lia | left].
apply (dgo_own_ext_nonuser B ly S _ k0 a M Hk0); lia.
- left. cbv beta zeta delta [DGgi.DZONE] in X. destruct X as [X|[X|X]].
+ apply (own_static B ly S _ a M). rewrite (ts_owned _ TS).
apply Exists_exists. exists (0xa7c90, 0x5caa90 - 0xa7c90). split; [unfold Tfib_owned_static; cbn; tauto|].
unfold in_zr. cbn [fst snd]. lia.
+ eapply (own_core B ly S _ (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact X].
+ eapply (own_core B ly S _ (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact X].
- left. unfold dshadow, DGgiC.SPv, DGgi.SPv, DGgiC.CNT8v, DGgi.CNT8v, DGgiC.N8v, DGgi.N8v in X.
assert (U8 : exists a0, ck_base B ly k0 + ck_rz k0 = a0 * 8).
{ apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. exists (2 * q + 2 * q'). lia. }
destruct U8 as [a0 Hua]. rewrite Hua in X. rewrite !Z_div_mult in X by lia.
replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
destruct (extent_zone B ly S _ k0 M Hk0) as [[Z1 Z2]|(m & len & Zin & Z1 & Z2)].
+ eapply own_shadow_prim; [exact M|]. lia.
+ eapply own_shadow_sec; [exact M | exact Zin |]. unfold kPage in *. lia.
Qed.

(* (di_owned_b) The last batch's byte count, item count and slot are owned (own_batch, YG0q.v:222), or, for a full
   last batch, the word just past the batch object (dgo_own_past_batch). *)
Lemma owned_b_cgif : forall inst ly S W mem md lastb initr a,
ARX_cgif B inst ly S W mem md -> rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a ->
aowned B ly S a.
Proof.
intros inst ly S W mem md lastb initr a [_ HAR] Hrev Ra Hw.
img_norm.
pose proof (proj1 HAR) as M.
assert (Hin : In lastb (all_batches S)).
{ assert (E : qc_list (st_qthread S) = rev (lastb :: initr)) by (rewrite <- Hrev; rewrite rev_involutive; reflexivity).
unfold all_batches. apply in_app_iff. left. rewrite E. cbn [rev]. apply in_app_iff. right. apply in_eq. }
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf _ _ _ _ M))) lastb Hin) as [L1 L2].
unfold bwrites in Hw. cbv beta zeta delta [DGgiC.SLOTv DGgi.SLOTv DGgiC.Bv DGgi.Bv DGgiC.BCv DGgi.BCv] in Hw.
destruct (Z_lt_le_dec a (ly_space ly + b_self lastb + kBatchBytes)) as [Lt|Ge].
- apply (own_batch B ly S _ lastb a M Hin). unfold kBatchSlots, kBatchBytes in *. lia.
- apply (dgo_own_past_batch B ly S _ lastb a M Hin). unfold kBatchSlots, kBatchBytes in *. lia.
Qed.

(* (di_owned_i) The internal allocator's zone is in the owned static range (YFex.D_owned's DI case). *)
Lemma owned_i_cgif : forall inst ly S W mem md a, ARX_cgif B inst ly S W mem md -> DGgi.IZONE a -> aowned B ly S a.
Proof.
intros inst ly S W mem md a [_ HAR] HI. apply (own_static B ly S _ a (proj1 HAR)). rewrite (ts_owned _ TS).
img_norm.
apply Exists_exists. exists (0xa7c90, 0x5caa90 - 0xa7c90). split; [unfold Tfib_owned_static; cbn; tauto|].
dgn; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in HI. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* (di_owned_x) The quarantined state owns no more than the entry state and the block (YFfl.owned_S', YFfl.v:988). *)
Lemma owned_x_cgif : forall inst ly S W mem md p n k z tr a,
ARX_cgif B inst ly S W mem md -> rpre_dealloc_cgif S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
aowned B ly (qx S k z tr) a -> aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros inst ly S W mem md p n k z tr a [_ HAR] _ Hblk Hf Ho.
img_norm.
pose proof (proj1 HAR) as M.
destruct (find_user_block _ _ _ _ S p n (am_wf _ _ _ _ M) Hblk) as (k0 & Hf0 & Hk0 & _ & Hu0 & Hr0).
rewrite Hf in Hf0. injection Hf0 as E. subst k0.
pose proof (dgo_aowned_same B ly (qx S k z tr) (YFfl.S' S k z tr) a (dgo_qx_chunks S k z tr) (dgo_qx_fs S k z tr) Ho) as Ho'.
destruct (YFfl.owned_S' B ly S _ M k Hk0 z tr a Ho') as [H|H]; [left; exact H | right].
rewrite <- Hu0, <- Hr0. unfold ck_n in H. exact H.
Qed.

(* (di_qowned) The quarantine's header words are in the owned static range (the instance) and the thread object
   (own_core); the batch objects are owned (own_batch). *)
Lemma qowned_cgif : di_qowned_t (ARX_cgif B) (aowned B) L24 qloose.
Proof.
intros inst ly X W mem md a [Ei HAR] _ Ra Hq. subst inst. pose proof (proj1 HAR) as M.
img_norm.
destruct Hq as [Hq|(b & Hb & Hob)].
- unfold qhdr in Hq. destruct Hq as [Hq|[Hq|Hq]].
1,2: apply (own_static B ly X _ a M); rewrite (ts_owned _ TS); apply Exists_exists;
  exists (0xa4dd8, 0xa7c88 - 0xa4dd8); split; [unfold Tfib_owned_static; cbn; tauto|];
  unfold in_zr, TFIB_INST, o_quar in *; cbn [fst snd]; lia.
eapply (own_core B ly X _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
cbn [fst snd]. unfold t_qc, kThreadObjSize in *. lia.
- unfold bobj in Hob. exact (own_batch B ly X _ b a M Hb Hob).
Qed.

(* (di_qview) The parts of DMiface.qview. *)
Lemma qv_cells_cgif : forall ly X (W : world tfibsegs) (mem : word -> option byte), ARm B ly X (aview tfibsegs (w_H W) mem) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (quar_cells X).
Proof.
intros ly X W mem M. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M)).
unfold acells. rewrite !in_app_iff. do 4 right; left. exact Hc.
Qed.

(* The Quarantine object's max_size_ / min_size_ and the two bytes after the mutexes are image constants
   (YFev.const_vals / mutex_vals' C3, by YF0x.tfib_const_lookup). *)
Lemma qv_const_cgif : forall ly X (W : world tfibsegs) (mem : word -> option byte), ARm B ly X (aview tfibsegs (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_q_max) 8 kQuarantineMax /\
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_q_min) 8 kQuarantineMin /\
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_q_cmutex + 2) 2 0.
Proof.
intros ly X W mem M. split; [|split].
- exact (tfib_const_lookup B TS ly X (w_H W) mem (TFIB_INST + o_q_max) 8 kQuarantineMax M ltac:(clear; vm_compute; reflexivity)).
- exact (tfib_const_lookup B TS ly X (w_H W) mem (TFIB_INST + o_q_min) 8 kQuarantineMin M ltac:(clear; vm_compute; reflexivity)).
- exact (tfib_const_lookup B TS ly X (w_H W) mem (TFIB_INST + o_q_cmutex + 2) 2 0 M ltac:(clear; vm_compute; reflexivity)).
Qed.

(* The thread object is visible (aareas' (AT 0, kThreadObjSize)) and outside the image, so its bytes are present
   (YFfu.vis_apresent's route, through YF0x.mbyte_off_apresent). *)
Lemma qv_tpres_cgif : forall ly X (W : world tfibsegs) (mem : word -> option byte) a, ARm B ly X (aview tfibsegs (w_H W) mem) -> img_cover ly ->
ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> apresent (w_H W) mem a.
Proof.
intros ly X W mem a M IMG Ha. pose proof (am_layout _ _ _ _ M) as LO.
assert (IN : In (AT 0, kThreadObjSize) (aareas X)).
{ unfold aareas. rewrite !in_app_iff. do 6 right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ M) _ IN (a - ly_T ly) ltac:(cbn [snd]; unfold t_qc, kThreadObjSize in *; lia)) as V.
cbn [fst] in V. replace (aeval B ly (AT 0) + (a - ly_T ly)) with a in V by (cbn [aeval]; lia).
pose proof (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split;
  [unfold owned_extents; cbn; tauto | unfold in_zr, t_qc, kThreadObjSize in *; cbn [fst snd]; lia])) as (APP & _ & NIMG).
pose proof (app_addr_below_ceil a APP) as CE. pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
apply dgo_vis_off_apresent; [|exact V].
destruct IMG as [IC1 IC2]. unfold off_img, in_zr in *. cbn [fst snd] in NIMG.
unfold TFIB_IMG_LO, TFIB_IMG_END, ASAN_CEIL in *. lia.
Qed.

(* A batch object is in the class-24 region's mapped part (aareas), and above the image. *)
Lemma qv_bpres_cgif : forall ly X (W : world tfibsegs) (mem : word -> option byte) b a, ARm B ly X (aview tfibsegs (w_H W) mem) -> In b (all_batches X) ->
bobj ly b a -> apresent (w_H W) mem a.
Proof.
intros ly X W mem b a M Hb Ha. pose proof (am_layout _ _ _ _ M) as LO. unfold bobj in Ha.
destruct (dgo_bgeom B ly X _ b M Hb) as (x & Eb & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (IN : In (ASp (region_off kBatchClass), rg_mapped_user (reg X kBatchClass)) (aareas X)).
{ unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass.
  split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity]. }
pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ M) _ IN (x + (a - (ly_space ly + b_self b)))
  ltac:(cbn [snd]; unfold kBatchBytes in *; lia)) as V.
cbn [fst] in V. replace (aeval B ly (ASp (region_off kBatchClass)) + (x + (a - (ly_space ly + b_self b)))) with a in V
  by (cbn [aeval]; unfold region_base in Eb; lia).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
apply dgo_vis_off_apresent; [|exact V].
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kBatchBytes, region_base in *. lia.
Qed.

(* Every batch object is a class-24 object of the region's allocated part (dgo_bgeom). *)
Lemma qv_geom_cgif : forall ly X rd, ARm B ly X rd ->
rg_alloc_user (reg X kBatchClass) <= kFreeArrayOffset /\
forall b, In b (all_batches X) ->
0 <= b_self b - region_off kBatchClass /\ b_self b - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
(b_self b - region_off kBatchClass) mod kBatchBytes = 0.
Proof.
intros ly X rd M. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
split; [pose proof ev_user_room; unfold kUserMapSize, kFreeArrayOffset in *; lia|].
intros b Hb. destruct (dgo_bgeom B ly X rd b M Hb) as (x & Eb & Px & Ax & Ux & _).
assert (Ex : b_self b - region_off kBatchClass = x) by (unfold region_base in Eb; lia).
rewrite Ex. dgo_splits; assumption.
Qed.

(* The quarantine's well-formedness (Wf's wf_quar), with the chunk sizes of its items. *)
Lemma qv_wf_cgif : forall ly X rd, ARm B ly X rd ->
qc_bytes (st_qthread X) = sum_bytes (qc_list (st_qthread X)) /\
qc_bytes (st_qglobal X) = sum_bytes (qc_list (st_qglobal X)) /\
Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches X) /\
Forall (fun k => 0 <= ck_n k) (q_items X).
Proof.
intros ly X rd M. pose proof (am_wf _ _ _ _ M) as WF. pose proof (wf_quarantine _ _ _ _ _ WF) as WQ.
dgo_splits; [exact (wq_bytes_t _ WQ) | exact (wq_bytes_g _ WQ) | exact (wq_batches _ WQ) |].
apply Forall_forall. intros k Hk.
pose proof (proj1 (Forall_forall _ _) (wq_items _ WQ) k Hk) as [Hin _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hin) as [Hn _].
unfold ck_n. pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
Qed.

(* A non-empty quarantine means the thread cache is initialized (Wf's wf_qinited). *)
Lemma qv_inited_cgif : forall ly X rd, ARm B ly X rd -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
st_cache_inited X = true.
Proof.
intros ly X rd M HTB. pose proof (am_wf _ _ _ _ M) as WF.
apply (wf_qinited _ _ _ _ _ WF). intros E. unfold all_batches in E. apply app_eq_nil in E as [E _].
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QB. rewrite E in QB. cbn in QB.
unfold kQuarantineCacheMax in HTB. lia.
Qed.

(* (di_qview) The record's 14 conjuncts, with qv_hpres narrowed to the thread cache's header (a Theorem Labs lane, 03:05Z:
   DMdrain stores to the instance's header by the image's writability, not by apresent; the instance half of qhdr
   has no source from AR, since aview is Some on the whole rw window from seg_rom alone).  With that narrowing in
   DMiface.qview this is the record, field by field. *)
Lemma qview_cgif_narrow : forall inst ly X W mem md, ARX_cgif B inst ly X W mem md -> dprem L24 qloose X ->
inst = as_inst B /\ layout_ok ly /\ img_cover ly /\ ly_tsd ly = TFIB_TSD /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (quar_cells X) /\
(val_mem tfibsegs (mrestrict (w_H W) mem) (inst + o_q_max) 8 kQuarantineMax /\
 val_mem tfibsegs (mrestrict (w_H W) mem) (inst + o_q_min) 8 kQuarantineMin /\
 val_mem tfibsegs (mrestrict (w_H W) mem) (inst + o_q_cmutex + 2) 2 0) /\
(forall a, ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> apresent (w_H W) mem a) /\
(forall b a, In b (all_batches X) -> bobj ly b a -> apresent (w_H W) mem a) /\
(rg_alloc_user (reg X kBatchClass) <= kFreeArrayOffset /\
 forall b, In b (all_batches X) ->
 0 <= b_self b - region_off kBatchClass /\ b_self b - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
 (b_self b - region_off kBatchClass) mod kBatchBytes = 0) /\
NoDup (map b_self (all_batches X)) /\
(qc_bytes (st_qthread X) = sum_bytes (qc_list (st_qthread X)) /\
 qc_bytes (st_qglobal X) = sum_bytes (qc_list (st_qglobal X)) /\
 Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches X) /\
 Forall (fun k => 0 <= ck_n k) (q_items X)) /\
qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31 /\
st_cache_inited X = true.
Proof.
intros inst ly X W mem md [Ei HAR] (HTB & HQL & _). subst inst.
img_norm.
pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (img_cover_of_ledger ly X md (proj1 (proj2 HAR))) as IMG.
destruct HQL as (Q1 & Q2 & _).
dgo_splits.
- symmetry. exact (ts_inst _ TS).
- exact LO.
- exact IMG.
- rewrite (am_tsd _ _ _ _ M). exact (ts_tsd B TS).
- exact (qv_cells_cgif ly X W mem M).
- exact (proj1 (qv_const_cgif ly X W mem M)).
- exact (proj1 (proj2 (qv_const_cgif ly X W mem M))).
- exact (proj2 (proj2 (qv_const_cgif ly X W mem M))).
- intros a Ha. exact (qv_tpres_cgif ly X W mem a M IMG Ha).
- intros b a Hb Ha. exact (qv_bpres_cgif ly X W mem b a M Hb Ha).
- exact (proj1 (qv_geom_cgif ly X _ M)).
- exact (proj2 (qv_geom_cgif ly X _ M)).
- apply NoDup_ListNoDup. exact (dgo_bnodup B ly X _ M).
- exact (proj1 (qv_wf_cgif ly X _ M)).
- exact (proj1 (proj2 (qv_wf_cgif ly X _ M))).
- exact (proj1 (proj2 (proj2 (qv_wf_cgif ly X _ M)))).
- exact (proj2 (proj2 (proj2 (qv_wf_cgif ly X _ M)))).
- unfold qloose in *. lia.
- exact (qv_inited_cgif ly X _ M HTB).
Qed.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* (enqueue bridge) a Theorem Labs lane, from its DGif1E.v (helpers shared with the post part). *)
(* The batch bound.  CLenqcgif.EPc's last conjunct (CLenqcgif.v:396) asks
   Z.of_nat (length (all_batches (qx S k z tr))) + 1 <= L24, and no premise of CLenqcgif.enq_bridge mentions L24, so
   enq_bridge L24 is false for a small L24 (L24 = 0: the left side is at least 1).  The released bound is
   YG0m.batches_len_fuel (YG0m.v:92): Wf + qloose give Z.of_nat (length (all_batches s)) <= 16384, so the bridge holds
   for every L24 >= 16385; the premise 16385 <= L24 is that bound, used only for that conjunct. *)
Lemma enq_bridge_cgif : forall L24, 16385 <= L24 -> CLenqcgif.enq_bridge B L24.
Proof.
intros L24x HL24x. unfold CLenqcgif.enq_bridge.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat [Ei HAR] [Hev [HQ Hii]] _ HBLK HU Hf Hst
  Hlo Hhi Hbot Hal Hhb HV0 DM HRA HRA4 HSP0 HGP HTP HA0 HA1 HA3 HA4.
destruct DM as ((memD & (AOKD & DEPD & CSTD) & PRD & EQD) & MEQ & IALP & SHV & PRS & PRW & V1 & V2 & V3).
pose proof HAR as (M0 & LED & BUD & MW & HSH).
pose proof (am_layout _ _ _ _ M0) as LY. pose proof (img_cover_of_ledger ly S md0 LED) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ M0); exact (ts_tsd B TS)).
pose proof (am_wf _ _ _ _ M0) as WF.
destruct (find_user_block _ 0 0 0 S p n WF HBLK) as (k0 & Hf0 & Hk & _ & Hu & Hr). rewrite Hf in Hf0. injection Hf0 as <-.
subst p n.
(* the chunk header's second byte (the chunk cell AVmask 127 17 at the entry memory) *)
assert (HB1M : Z.land hb1 127 = 17).
{ pose proof (chunk_facts B ly S _ k M0 Hk) as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & GG').
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG']; cbn; lia. }
assert (C : cell_holds B ly (aview tfibsegs (w_H W) mem0) (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M0)). unfold acells. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite EA2 in C. destruct C as (b & Hb & Hm).
replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (sptr_addr B ly (ck_user k) - 16 + Z.of_nat 1) in Hb
by (rewrite G4'; unfold kChunkHeaderSize; lia).
rewrite (val_mem_aview_p _ _ _ _ _ 1 HV0 ltac:(lia)) in Hb. injection Hb as <-. rewrite le_byte_hb1 in Hm by exact Hhb. exact Hm. }
(* the stack window, the geometry *)
destruct (sp_pick ly sp0 LY Hlo Hhi) as (sp & HSP & SP1 & SP2).
pose proof (geo_TCD ly LY IMG) as (_ & _ & ZD & DTS & DCS & DDS & DTC & DTD & HMB).
pose proof (YFfl.HIGH B ly S _ M0 k Hk IMG)
as (HP1 & HP2 & ZQ & HQ2 & ZT & HT2 & ZF & HF2 & ZNB & HNB2 & ZSB & HSB2 & ZC & HC2 & HS1 & HS2 & PS1 & PS2 & ZK & HK2 & RZ16 & STK).
pose proof (YFfl.ext_rounded B ly S _ M0 k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (YFfl.Hu B ly S _ M0 k Hk) as G4.
pose proof (YFfl.u_al8 B ly S _ M0 k Hk) as (U8 & B8 & R8).
pose proof (chunk_facts B ly S _ k M0 Hk) as (G1 & G2 & G3 & _ & G5 & G6 & G7 & G8 & _).
pose proof (YFfl.anyX B ly S _ M0 k 2 _ Hk eq_refl ltac:(discriminate)) as KT.
pose proof (YFfl.anyX B ly S _ M0 k 6 _ Hk eq_refl ltac:(discriminate)) as KC.
pose proof (YFfl.anyX B ly S _ M0 k 7 _ Hk eq_refl ltac:(discriminate)) as KD.
assert (AOK : aok (set_internal_inited true (set_nev (st_nev S + 1) S)) (KDepot tr) z) by exact AOKD.
assert (HU1 : ck_base B ly k <= sptr_addr B ly (ck_user k)) by (clear - G4 RZ16; lia).
assert (HU2 : sptr_addr B ly (ck_user k) + ck_n k <= ck_base B ly k + ck_extent k) by (clear - G4 ER NN3; lia).
assert (HU3 : 0 <= ck_n k) by (clear - NN1; lia).
(* the entry memory, patched on the gap with the memory at the call *)
pose (memP := fun x : word => if gapb B ly (bv_unsigned x) then mem x else mem0 x).
assert (MP1 : forall x : word, DGgi.DZONE ly (bv_unsigned x) -> ~ depot_footprint B ly (bv_unsigned x) -> memP x = mem x).
{ intros x H1 H2. unfold memP. cbv beta. destruct (gapb B ly (bv_unsigned x)) eqn:G; [reflexivity|]. exfalso. exact (gapb_false _ _ _ G (conj H1 H2)). }
assert (MP2 : forall x : word, ~ (DGgi.DZONE ly (bv_unsigned x) /\ ~ depot_footprint B ly (bv_unsigned x)) -> memP x = mem0 x).
{ intros x H1. unfold memP. cbv beta. destruct (gapb B ly (bv_unsigned x)) eqn:G; [exfalso; exact (H1 (gapb_true _ _ _ G)) | reflexivity]. }
assert (EQD' : forall x : word, DGgi.DZONE ly (bv_unsigned x) -> mem x = memD x) by exact EQD.
assert (CLR : forall a, cloc ly a -> 0 <= a < 2 ^ 64).
{ intros a CL. clear - CL ZT ZC ZD. unfold cloc in CL. unfold zone3 in ZT, ZC, ZD. ceil.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, ASAN_CEIL, kThreadObjSize in *. lia. }
(* the constant cells at memP: from dpost_x on the gap, from the entry memory elsewhere *)
assert (CP : Forall (cell_holds B ly (aview tfibsegs (w_H W) memP)) (as_const B ly)).
{ apply Forall_forall. intros c Hc.
apply (cell_holds_mix B ly (aview tfibsegs (w_H W) memD) (aview tfibsegs (w_H W) mem0) _ c (proj1 (Forall_forall _ _) CSTD c Hc)
(proj1 (Forall_forall _ _) (am_const _ _ _ _ M0) c Hc)).
intros j Hj. pose proof (CLR _ (proj1 (Forall_forall _ _) (const_loc B ly TS HTSD) c Hc j Hj)) as A64.
destruct (gapb B ly (aeval B ly (c_at c) + j)) eqn:G.
- left. apply aview_same. destruct (gapb_true _ _ _ G) as [H1 H2].
rewrite (MP1 (Z_to_bv 64 (aeval B ly (c_at c) + j))) by (rewrite unsigned_lit_small by exact A64; assumption).
apply EQD'. rewrite unsigned_lit_small by exact A64. exact H1.
- right. apply aview_same. apply MP2. rewrite unsigned_lit_small by exact A64. exact (gapb_false _ _ _ G). }
pose proof (ARm_gap B ly S (w_H W) mem0 memP TS IMG M0 MP2 CP) as MP.
set (rd0 := aview tfibsegs (w_H W) mem0) in *. set (rdP := aview tfibsegs (w_H W) memP) in *.
set (rd' := aview tfibsegs (w_H W) mem) in *. set (rdD := aview tfibsegs (w_H W) memD) in *.
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
(* YFfl's frame premise: outside its write set D the memory at the call reads as memP *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFfl.D B ly k sp a -> rd' a = rdP a).
{ intros a Ha ND. unfold rd', rdP. apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
destruct (gapb B ly a) eqn:G.
- destruct (gapb_true _ _ _ G) as [H1 H2]. symmetry. apply MP1; rewrite Ux; assumption.
- assert (NG : ~ (DGgi.DZONE ly (bv_unsigned (Z_to_bv 64 a)) /\ ~ depot_footprint B ly (bv_unsigned (Z_to_bv 64 a))))
by (rewrite Ux; exact (gapb_false _ _ _ G)).
rewrite (MP2 _ NG).
unfold YFfl.D, YFfl.DT, YFfl.DK, YFfl.DS, YFfl.DI, YFfl.DH in ND.
apply MEQ; rewrite Ux.
+ intros X. apply ND. unfold dwin_m, DGgmC.WINT, DGgmC.WINB in X. cbv zeta in X.
destruct X as [X|[X|X]].
* do 2 right; left. unfold ASTACK, DFSTACK, DGbaseC.DFSTACK in *. lia.
* left. lia.
* right; left. exact X.
+ intros X. change (DGgi.DZONE ly a) in X. apply (gapb_false _ _ _ G). split; [exact X|]. intros F. apply ND. do 4 right; left; exact F.
+ intros X. change (DGgi.IZONE a) in X. apply ND. do 3 right; left. unfold DGgi.IZONE in X. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS). exact X.
+ intros X. apply ND. do 5 right. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X. rewrite Z_div_mult in X by lia. unfold shadow_addr. exact X. }
(* visibility: what memP shows, the memory at the call shows *)
assert (VIS : forall a, rdP a <> None -> rd' a <> None).
{ intros a Hv HN. unfold rdP, rd', aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
revert Hv HN. destruct (w_H W x) eqn:Hx; intros Hv HN; [exact (Hv HN)|].
revert Hv HN. destruct (seg_rom tfibsegs x) eqn:ROM; intros Hv HN; [destruct (mem x); discriminate|].
revert HN. destruct (mem x) as [|] eqn:E'; intros HN; [discriminate|]. clear HN.
revert Hv. destruct (memP x) as [b0|] eqn:E0; intros Hv; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (0x10000 <= a' < 0x5fd000)) by (intros X; apply (YB13.tfib_rom_all a' X); rewrite Ex; exact ROM).
assert (NG : ~ (DGgi.DZONE ly a' /\ ~ depot_footprint B ly a')) by (intros [Hd Hn]; pose proof (gap_low B ly a' Hd Hn); lia).
rewrite (MP2 x NG) in E0.
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False) by (intros m [_ [bb Hb]] Hm; rewrite Ex in Hb; congruence).
destruct (EM (DGgiC.SPv (sptr_addr B ly (ck_user k))) (DGgiC.SPv (sptr_addr B ly (ck_user k)) + DGgiC.CNT8v (req_size (ck_req k))) a') as [C1|C1].
{ rewrite (SHV x C1) in E'. discriminate. }
destruct (EM (sp0 - DGbaseC.DFSTACK) sp0 a') as [C2|C2]. { exact (PRX mem (PRS a' C2) E'). }
assert (WD : (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a') \/ ~ (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a'))
by (unfold DGgmC.WINT, DGgmC.WINB; cbv zeta; lia).
destruct WD as [C3|C3]. { exact (PRX mem (PRW a' C3) E'). }
assert (C5 : ~ DGgi.DZONE ly a' \/ DGgi.DZONE ly a') by (unfold DGgi.DZONE; lia).
destruct C5 as [C5|C5].
2:{ assert (P0 : apresent (w_H W) mem0 a') by (split; [rewrite Ex; exact Hx | exists b0; rewrite Ex; exact E0]).
destruct (PRD a' C5 P0) as [_ [bd Hbd]]. rewrite Ex in Hbd. rewrite (EQD' x C5) in E'. congruence. }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C6|C6]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C6; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C7|C7]; [apply NIMG; unfold TFIB_IAL_FLAG in C7; lia|].
rewrite (MEQ x) in E'; [congruence | | exact C5 | change (~ DGgi.IZONE a'); unfold DGgi.IZONE; tauto | exact C1].
unfold dwin_m. intros [X|X]; [exact (C2 X) | exact (C3 X)]. }
(* the values the walk wrote *)
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V1 Hi)).
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i))
by (intros i Hi; exact (val_mem_aview_p _ _ _ _ _ i V2 Hi)).
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview_p _ _ _ _ _ 0 V3 ltac:(lia)). }
assert (NEW_sh : forall a, YFfl.DH B ly k a -> rdP a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. unfold YFfl.DH, shadow_addr in Hd.
assert (Ha : 0 <= a < 2 ^ 64 /\ TFIB_IMG_END <= a).
{ clear - Hd G1 G2 G4 ER NN1 NN2 NN3 RZ16. unfold in_app in G1. ceil. unfold SHADOW_OFF, ASAN_CEIL, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold rdP, rd', aview, mbyte, mrestrict in Hv |- *.
assert (ROM : seg_rom tfibsegs (Z_to_bv 64 a) = None) by (apply seg_rom_none_high; lia).
revert Hv. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; intros Hv.
- rewrite ROM in Hv. exfalso. exact (Hv eq_refl).
- rewrite (SHV (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v.
rewrite Z_div_mult by lia. exact Hd. }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (YFfl.S' S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ change (DGgi.IAL_POST W mem) in IALP. unfold DGgi.IAL_POST in IALP. cbv zeta in IALP. destruct IALP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. rewrite (YFfl.S'_inited S k z tr), (ts_ial_flag _ TS), (ts_ial_lo _ TS), (ts_ial_w _ TS), (ts_ial_hi _ TS).
subst rd'. split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I1). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_p _ _ _ _ _ 0 I2). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I3 Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TS). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. exact (val_mem_aview_p _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) mem a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TS); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
(* the depot's memory facts after the put, from dpost_x's second conjunct (the footprint is in the DZONE) *)
assert (DEP : depot_mem_ok B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rd').
{ assert (DEPs : depot_mem_ok B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rdD).
{ apply (AGix.depot_mem_ok_ext B ly TS LY IMG HTSD (CLdepot.depot_after z tr S)); [unfold CLdepot.depot_after, depot_after; destruct (z =? 0); reflexivity | exact DEPD]. }
eapply (YFfy.depot_mem_ok_agree B ly (depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S)))
(depot_after z tr (set_internal_inited true (set_nev (st_nev S + 1) S))) rdD rd'); [| exact (am_universe _ _ _ _ M0) | reflexivity | | exact DEPs].
- apply (WfP_weaken _ 1 1 1); try lia. exact (YFfl.sd_wf B ly S _ M0 z tr Hev AOK HU).
- intros a Ha. assert (A64 : (0 <= a < 2 ^ 64) /\ DGgi.DZONE ly a).
{ unfold depot_footprint in Ha. rewrite (ts_depot _ TS), (ts_store _ TS) in Ha. unfold DGgi.DZONE.
clear - Ha ZNB ZSB. unfold zone3 in ZNB, ZSB. ceil. unfold TFIB_DEPOT, TFIB_STORE, d_map1, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *. lia. }
unfold rd', rdD. apply aview_same. apply EQD'. rewrite unsigned_lit_small by exact (proj1 A64). exact (proj2 A64). }
(* the constant cells avoid YFfl's write set outside the DZONE *)
assert (CD : forall a, cloc ly a -> ~ DGgi.DZONE ly a -> ~ YFfl.D B ly k sp a).
{ intros a CL NDZ.
unfold YFfl.D, YFfl.DT, YFfl.DK, YFfl.DS, YFfl.DI, YFfl.DH. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS).
intros [X|[X|[X|[X|[X|X]]]]].
- assert (XT : ly_T ly + 80 <= a < ly_T ly + 4096) by (clear - X; unfold t_unwinding, t_stats in X; lia).
clear - XT CL ZT DTC DTD. unfold cloc, zone3, zone3cases, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- assert (XK : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by (clear - X G4 RZ16 ER NN1 NN3; lia).
clear - XK CL ZK KT KC KD. unfold cloc, zone3, zone3cases, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- assert (XS : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - X HSP; unfold ASTACK in *; lia).
clear - XS CL HS1 DTS DCS DDS. unfold cloc, zdisjoint in *. cbn [fst snd] in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kHighMemBeg, kThreadObjSize in *. lia.
- clear - X CL ZT ZC ZD. unfold cloc, zone3, zone3cases in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
- apply NDZ. unfold DGgi.DZONE. unfold depot_footprint in X. rewrite (ts_depot _ TS), (ts_store _ TS) in X. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X.
destruct X as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; exact X | left; lia].
- assert (XH : (a < SHADOW_OFF + 8192 \/ SHADOW_OFF + 784896 <= a) /\ SHADOW_OFF <= a < kHighMemBeg).
{ unfold shadow_addr in X. clear - X ZK G4 ER NN1 NN2 NN3 RZ16. unfold zone3, zone3cases in ZK. ceil.
unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear - XH CL ZT ZC ZD. unfold cloc, zone3, zone3cases in *.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc.
apply (cell_holds_mix B ly rdD rdP rd' c (proj1 (Forall_forall _ _) CSTD c Hc) (proj1 (Forall_forall _ _) (am_const _ _ _ _ MP) c Hc)).
intros j Hj. pose proof (proj1 (Forall_forall _ _) (const_loc B ly TS HTSD) c Hc j Hj) as CL.
pose proof (CLR _ CL) as A64.
assert (DZD : DGgi.DZONE ly (aeval B ly (c_at c) + j) \/ ~ DGgi.DZONE ly (aeval B ly (c_at c) + j)) by (unfold DGgi.DZONE; lia).
destruct DZD as [DZ|NDZ].
- left. unfold rd', rdD. apply aview_same. apply EQD'. rewrite unsigned_lit_small by exact A64. exact DZ.
- right. exact (AG _ A64 (CD _ CL NDZ)). }
pose proof (YFfl.free_mid_ARm B TS ly S rdP rd' MP k hb1 Hk Hst (conj Hhb HB1M) z tr Hev AOK HU sp HSP IMG AG VIS
NEW_hdr NEW_n NEW_unw NEW_sh IAL DEP CONST') as M'.
(* the shadow band, for the AR's shadow part *)
assert (SHP : forall a, DGgiC.SPv (sptr_addr B ly (ck_user k)) <= a < DGgiC.SPv (sptr_addr B ly (ck_user k)) + DGgiC.CNT8v (req_size (ck_req k)) ->
w_H W (Z_to_bv 64 a) = false).
{ intros a Ha. unfold DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in Ha. rewrite Z_div_mult in Ha by lia.
change (req_size (ck_req k)) with (ck_n k) in Ha.
pose proof U8 as U8'. apply Z.mod_divide in U8' as [q Hq]; [|lia].
assert (Hq8 : sptr_addr B ly (ck_user k) / 8 = q) by (rewrite Hq; apply Z.div_mul; lia).
rewrite Hq8 in Ha.
assert (Eg : shadow_addr (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) = a).
{ unfold shadow_addr. rewrite Hq. replace (q * 8 + 8 * (a - (SHADOW_OFF + q))) with ((a - SHADOW_OFF) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (G8' : (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) mod 8 = 0).
{ rewrite Hq. replace (q * 8 + 8 * (a - (SHADOW_OFF + q))) with ((q + (a - (SHADOW_OFF + q))) * 8) by lia. apply Z_mod_mult. }
assert (Gb : ck_base B ly k <= sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q)) < ck_base B ly k + ck_extent k)
by (clear - Ha G4 RZ16 ER NN2; lia).
destruct (find_chunk_some B ly (st_chunks S) _ k Hk Gb) as (x & Fx).
assert (AS : exists v, ashadow B ly S (sptr_addr B ly (ck_user k) + 8 * (a - (SHADOW_OFF + q))) = Some v)
by (unfold ashadow; rewrite Fx; eexists; reflexivity).
destruct AS as [v Hv].
pose proof (am_shadow _ _ _ _ M0 _ v G8' Hv) as R. rewrite Eg in R.
assert (Ha' : 0 <= a < 2 ^ 64 /\ TFIB_IMG_END <= a).
{ clear - Ha Hq G1 G2 G4 ER NN2 RZ16. unfold in_app in G1. ceil. unfold SHADOW_OFF, ASAN_CEIL, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold rd0, aview, mbyte, mrestrict in R. revert R. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; intros R; [|reflexivity].
rewrite seg_rom_none_high in R by lia. discriminate. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem (w64 a) = mem0 (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; rewrite Hx in Hh; discriminate).
apply MEQ; rewrite Ux.
- unfold dwin_m. intros [X|X]; [exact (PRX mem (PRS a X)) | exact (PRX mem (PRW a X))].
- intros X. change (DGgi.DZONE ly a) in X. unfold DGgi.DZONE in X. clear - X Ha ZNB ZSB. unfold zone3, zone3cases in ZNB, ZSB.
unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg, TFIB_IMG_LO, TFIB_IMG_END, kNodesBlockSize, kStoreBlockSize in *. lia.
- change (~ DGgi.IZONE a). unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia.
- intros X. pose proof (SHP a X) as F. rewrite Hx in F. discriminate. }
assert (VIS0 : forall a, rd0 a <> None -> rd' a <> None) by (intros a Hv; apply VIS; exact (gap_vis B ly (w_H W) mem0 memP MP2 a Hv)).
assert (NDG : forall g, in_app g 8 -> g mod 8 = 0 -> hfree ly S g -> ~ YFfl.D B ly k sp (shadow_addr g)).
{ intros g Hga Hg HF. pose proof (shadow_addr_band_rw g Hga) as SBg.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
unfold YFfl.D, YFfl.DT, YFfl.DK, YFfl.DS, YFfl.DI, YFfl.DH.
intros [X|[X|[X|[X|[X|X]]]]].
- clear - X SBg ZT. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, t_unwinding, t_stats in *. lia.
- clear - X SBg ZK G4 RZ16 ER NN1 NN3. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
- clear - X SBg HS1 HSP. unfold ASTACK, kHighMemBeg in *. lia.
- rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS), (ts_ial_flag _ TS) in X. clear - X SBg. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in X. lia.
- unfold depot_footprint in X. rewrite (ts_depot _ TS), (ts_store _ TS) in X. clear - X SBg ZNB ZSB.
unfold zone3, zone3cases, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. lia.
- exact (hfree_shadow_off_range B ly S rd0 k (sptr_addr B ly (ck_user k)) (ck_n k) g M0 Hk HU1 HU2 U8 HU3 Hg HF X). }
(* the quarantined state *)
assert (EX : qx S k z tr = YFfl.S' S k z tr).
{ unfold qx, YFfl.S', qk. rewrite <- (tick_inited S Hii). reflexivity. }
rewrite EX.
pose proof (qmeter_tight _ HQ) as (QT1 & QT2 & QT3).
pose proof (YFfl.qloose_S' B ly S _ M0 k Hk Hst z tr (qmeter_tight _ HQ)) as QLX.
pose proof (YFfl.WS' B ly S _ M0 k Hk Hst z tr Hev AOK HU) as WFX.
pose proof (YFfl.quar_S' B ly S _ M0 k Hk Hst z tr) as [QX1 QX2].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKn _].
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & _ & R3).
split.
- (* the enqueue pre (YFew.enq_pre over ARX_cgif): the released ENQ_PRE's last part, YFg1.v:851-892 *)
unfold CLenq.enq_pre_x. splits.
+ split; [exact Ei|].
split; [exact M' | split; [|split; [|split]]].
* eapply ALedger_same; [exact (YFfl.ALedger_S' B ly S _ M0 k Hk z tr tfibsegs md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
* destruct BUD as [BUD PIN]. split; [| exact (YFfl.asecA_S' B ly S _ M0 k Hk z tr _ PIN)].
eapply Z.le_trans; [exact BUD | exact (YFfl.abudget_le B ly S _ M0 k Hk z tr)].
* eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
* eapply (ahs_transfer tfibsegs B ly S _ (w_H W) mem0 mem (al_img_env tfibsegs ly S md0 (am_layout B ly S _ M0) LED) M0 HSH VIS0 HSK).
-- eapply (aclient_band_same_frames B ly S); [exact M' | exact (YFfl.frames' S k z tr)].
-- exact (YFfl.sec_extents' B ly S _ M0 k Hk z tr).
-- intros g Hg Hga HF Hh.
assert (Rg : 0 <= shadow_addr g < 2 ^ 64 /\ kLowShadowBeg <= shadow_addr g < kHighShadowEnd).
{ pose proof (shadow_addr_band_rw g Hga) as SBg. clear - SBg. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
transitivity (rdP (shadow_addr g)).
++ apply AG; [exact (proj1 Rg) | exact (NDG g Hga Hg HF)].
++ apply (gap_agree B ly (w_H W) mem0 memP MP2). split; [exact (proj1 Rg)|]. right; left. unfold kLowShadowBeg in Rg. lia.
+ rewrite (YFfl.abudget_step B ly S _ M0 k Hk z tr). destruct BUD as [BUD _]. lia.
+ rewrite (YFfl.all_batches_S' S k z tr), (YFfl.S'_nev S k z tr). pose proof (wf_batches_ev _ _ _ _ _ WF). lia.
+ exact (YFfl.refill_reg_S' B ly S _ M0 k Hk z tr Hev kBatchClass ltac:(unfold kBatchClass; lia)).
+ exact (YFfl.k'_in B ly S _ M0 k Hk z tr).
+ reflexivity.
+ exact (YFfl.k'_fresh_items B ly S _ M0 k Hk Hst z tr).
+ exact HRA.
+ exact HRA4.
+ rewrite HSP0. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
+ rewrite HSP0. clear - Hlo. unfold CLenq.QSTACK_G, DFSTACK in *. lia.
+ rewrite HSP0. clear - Hhi. lia.
+ intros a Ha. rewrite HSP0 in Ha. apply PRS. clear - Ha. unfold CLenq.QSTACK_G, DGbaseC.DFSTACK in *. lia.
+ exact HGP.
+ exact HTP.
+ exact HA0.
+ exact HA1.
+ exact HA3.
+ exact HA4.
+ split; [exact QLX | exact (YFfl.rroom_S' B ly S _ M0 k Hk Hst z tr (qmeter_room _ HQ))].
- (* the caller's facts CLenqcgif.EPc *)
unfold CLenqcgif.EPc. split; [|split; [|split]].
+ rewrite (YFfl.S'_qglobal S k z tr). exact QT2.
+ rewrite QX1, QX2. change (ck_n (qk k)) with (ck_n k). lia.
+ rewrite (YFfl.S'_qthread S k z tr). change (ck_n (qk k)) with (ck_n k). unfold ck_n, MALLOC_MAX, kQuarantineCacheMax, kBatchBytes in *. lia.
+ pose proof (YG0m.batches_len_fuel _ _ _ _ _ WFX QLX) as BL. lia.
Qed.


(* (inst) The instance object is the image's, as AGif1's if_inst.                                                   *)
Lemma inst_cgif : forall inst ly S W mem md, ARX_cgif B inst ly S W mem md -> inst_ok inst.
Proof. intros inst ly S W mem md [-> _]. dgn; unfold inst_ok, TFIB_INST. lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (shape) The free tree after its entry step.  [rpre_dealloc_cgif] carries [st_internal_inited S = true], so the   *)
(* entry's internal-allocator step is a no-op and the state after the tick is [dtick S].                            *)
Lemma shape_n_cgif : forall n tr S, rpre_dealloc_cgif S n -> free PNull tr S = ret tt (dtick S).
Proof.
intros n tr S (_ & _ & Hii). unfold free, dtick.
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl). cbv beta.
unfold bind at 1. unfold get. cbn [ibind].
assert (E : st_internal_inited (set_nev (st_nev S + 1) S) = true) by exact Hii.
rewrite E. unfold ret at 1. cbn [ibind]. reflexivity.
Qed.

(* The live-block arm.  [p <> PNull] is the premise DGif0.di_shape still lacks (reported to a Theorem Labs lane at
   03:12Z): the free tree matches on p before it looks at the chunk list, and no other premise of the field
   excludes a chunk whose [ck_beg] is PNull.  Every consumer has it: the machine tested the pointer against 0. *)
Lemma shape_cgif : forall p n tr S k, rpre_dealloc_cgif S n -> p <> PNull -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
free p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd drain_body) (dtick S).
Proof.
intros p n tr S k (_ & _ & Hii) Hp Hin Hfu Hst. unfold free, dtick.
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl). cbv beta.
unfold bind at 1. unfold get. cbn [ibind].
assert (Eii : st_internal_inited (set_nev (st_nev S + 1) S) = true) by exact Hii.
rewrite Eii. unfold ret at 1. cbn [ibind].
destruct p as [|o|r o|c q]; [exfalso; exact (Hp eq_refl)| | | ];
(do 2 (match goal with |- bind ?m ?f ?s = _ => rewrite (bind_ret_l m f s _ _ eq_refl); cbv beta end);
 change (st_chunks (set_nev (st_nev S + 1) S)) with (st_chunks S); rewrite Hfu, Hst; cbv iota;
 match goal with |- bind ?m ?f ?s = _ => rewrite (bind_ret_l m f s _ _ eq_refl); cbv beta end;
 unfold qk; reflexivity).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (laws) The released frame and stack laws of AR.  ARXr is ARX_cgif, so di_frame_r is di_frame.                    *)
Lemma frame_cgif : di_frame_t (ARX_cgif B) (aowned B).
Proof.
intros inst ly S W mem md mem' md' [Ei HAR] AGR VIS Hvm Hlz He HK. split; [exact Ei|].
exact (AR_frame_law_ok tfibsegs B ly S W mem md mem' md' HAR AGR VIS Hvm Hlz He HK).
Qed.

Lemma stack_cgif : di_stack_t (ARX_cgif B) (aowned B).
Proof.
intros inst ly S W mem md a [_ HAR] Ha.
exact (AR_stack_law_ok tfibsegs B ly S W mem md a HAR Ha).
Qed.

(* (depot) The depot answer of the depot post is a granted one (CLdepot.dpost_x, first conjunct). *)
Lemma dpost_aok_cgif : forall inst ly S W tr z m, CLdepot.dpost_x tfibsegs B inst ly S W tr z m -> aok S (KDepot tr) z.
Proof. intros inst ly S W tr z m H. exact (proj1 H). Qed.

(* (quarantine view) DMiface.qview, field by field, from qview_cgif_narrow (c5 3c93da64d30 narrowed qv_hpres to the
   thread header, a Theorem Labs lane's text). *)
Lemma qview_cgif : di_qview_t B (ARX_cgif B) L24 qloose.
Proof.
intros inst ly X W mem md H P.
destruct (qview_cgif_narrow inst ly X W mem md H P) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
constructor; assumption.
Qed.

(* a Theorem Labs lane, from its DGif1R.v. *)
(* (di_rview) What DoRecycle reads at every cut. *)
Lemma rview_cgif : di_rview_t B (ARX_cgif B) (DRq_cgif B).
Proof.
intros inst ly X W mem md its zs [Ei HAR] RX. subst inst. pose proof (proj1 HAR) as M.
img_norm.
split; [|split].
- replace (TFIB_INST + o_space) with (YFl1.A_ALLOCATOR + 32) by reflexivity.
  exact (YFhl.sb_cell B TS ly X W mem M).
- intros k Hk.
  destruct RX as (_ & IT & _).
  assert (Hks : In k (st_chunks X)).
  { apply (proj1 (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk))). }
  pose proof (YFhl.item_facts B ly X _ k M Hks) as (I0 & I1 & I2 & I3 & _).
  unfold YFhd.hdra in I0, I1, I2, I3. rewrite I0 in I1, I2, I3. rewrite I0.
  split; [reflexivity|]. split; [exact I1|]. split; [exact I2|exact I3].
- intros z Hz.
  assert (SZ : YFhf.slot_ok X z).
  { apply (YFhf.RIx_slots (as_universe B) 0 0 0 X its [] zs z RX). cbn [map]. rewrite app_nil_r. exact Hz. }
  pose proof (YFhf.slot_carved B ly X _ z M SZ) as (C1 & C2 & C3 & C4).
  pose proof SZ as (_ & Z2 & _). rewrite YFhf.class_size_24 in Z2.
  split; [exact C1|]. split; [exact C2|]. split; [unfold kBatchBytes; exact Z2|].
  intros k a Hk Ha.
  destruct RX as (_ & IT & _).
  assert (Hks : In k (st_chunks X)).
  { apply (proj1 (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk))). }
  exact (YFhf.slot_vs_chunk B ly X _ z k M SZ Hks a ltac:(unfold YFhf.bslot; exact Ha)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The fields of the other hands, as Section hypotheses named like the fields.                                      *)
(* The released depot contract (YFl0.tfib_depot_spec), the same premise AGif1.iface_cgif takes. *)
Hypothesis HD1 : tfib_depot_spec B.
(* di_depot: a Theorem Labs lane's CLdepotcgif.di_depot_cgif at the released depot contract. *)
Lemma di_depot_cgif : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX_cgif B inst ly S W mem0 md0 -> tr_admit (as_universe B) S tr ->
(forall x : word, DGgi.DZONE ly (bv_unsigned x) \/ (CZONE ly (bv_unsigned x) /\ ~ DGgi.IZONE (bv_unsigned x)) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ DGgi.DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  CLdepot.dpost_x tfibsegs B inst ly S W tr z mem').
Proof. exact (CLdepotcgif.di_depot_cgif B TS HD1). Qed.

(* The batch bound enq_bridge needs (CLenqcgif.EPc; YG0m.batches_len_fuel caps the batches at 16384). *)
Hypothesis HL24 : 16385 <= L24.

Hypothesis di_drain_cgif : tfib_drain_spec_cf B (ARX_cgif B) (aowned B) drain_body L24 qloose.
Hypothesis di_requar_x_cgif : di_requar_x_t B (ARX_cgif B) (aowned B) L24 qloose.
Hypothesis di_requar_r_cgif : di_requar_r_t B (ARX_cgif B) (ARX_cgif B) (aowned B) L24 qloose (DRq_cgif B).
Hypothesis di_requar_e_cgif : di_requar_e_t (ARX_cgif B) (ARX_cgif B) (DRq_cgif B).
Hypothesis di_rchunk_cgif : di_rchunk_t B (ARX_cgif B) (aowned B) (DRq_cgif B).
Hypothesis di_cdealloc_cgif : di_cdealloc_t B (ARX_cgif B) (aowned B) (DRq_cgif B).


(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem diface_cgif :
DIface B (fun tr (S : astate) => tr_admit (as_universe B) S tr) free (ARX_cgif B) (ARX_cgif B) (aowned B) rpre_dealloc_cgif qtight
fpre_cgif (CLdepot.dpost_x tfibsegs B) drain_body L24 qloose (DRq_cgif B).
Proof.
constructor.
- exact inst_cgif.
- exact (view_n_cgif B TS).
- exact (view_cgif B TS).
- exact shape_n_cgif.
- (* the frozen di_shape puts p <> PNull first *)
  intros p n tr S k Hp Hr. exact (shape_cgif p n tr S k Hr Hp).
- exact di_depot_cgif.
- exact dpost_aok_cgif.
- (* di_enqueue: a Theorem Labs lane's CLenqcgif.di_enqueue_ok with the walk-side bridge enq_bridge_cgif.  CLenq's call post
     still carries the raw frame conjunct that c5 30300848492 dropped from DMspec.acall_post_x, so it is weakened here. *)
  intros until mat. intros.
  eapply amreal_mono; [| eapply (CLenqcgif.di_enqueue_ok B TS L24 (enq_bridge_cgif L24 HL24)); eassumption].
  intros r W' c' (regs' & mem' & md' & nb & Ec & (P1 & P2 & P3 & P4 & P5 & P6 & _ & P8) & R).
  exists regs', mem', md', nb. split; [exact Ec|]. split; [exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P8))))))|]. exact R.
- exact di_drain_cgif.
- (* the frozen di_lpost_d puts ARX of X' after the st_qglobal premise *)
  intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  exact (lpost_d_cgif inst ly S W mem md p n tr k z nb X' W' mem' md' trc r H1 H11 H2 H3 H4 H5 H6 H7 H8 H9 H10 H12 H13 H14).
- exact qview_cgif.
- exact qowned_cgif.
- exact di_requar_x_cgif.
- exact di_requar_r_cgif.
- exact di_requar_e_cgif.
- exact di_rchunk_cgif.
- exact di_cdealloc_cgif.
- exact frame_cgif.
- exact rview_cgif.
- exact post_c_cgif.
- exact post_n_cgif.
- exact frame_cgif.
- exact stack_cgif.
- exact owned_cgif.
- exact owned_b_cgif.
- exact owned_i_cgif.
- exact owned_x_cgif.
Qed.
End b.
End a.
