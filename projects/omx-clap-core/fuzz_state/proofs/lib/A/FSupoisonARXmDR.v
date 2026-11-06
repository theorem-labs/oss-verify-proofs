(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1dr.v (a working branch 84ee52cd012, file sha256 b93fc55c9771) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: cgif_file's instance of DGif0.DIface's di_rchunk and di_cdealloc (DMiface.v types),
   restated from the released QuarantineCallback::Recycle and LocalCache::Deallocate walks (YFfs, YFg7, YFg8, YFg9, YFg0)
   at DMspec.acall_post_x's raw frame clause and the stack window DMiface.KSTACK_CF. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/DGif1dr.v, with its module paths and module names changed; 430 of its 511 lines of code are new or changed and 338 lines of the source are left out. *)
(* fuzz_state image A: DIfaceR (lib/Reusable/DIfaceR.v) at the any-user-poison instance ARX_ARU, the premise H_difR_U
   of lib/A/FSReallocAG.v (a Theorem Labs lane, brief L17-AruLift, 2026-10-29).

   rule 24: no function proved (kind: instance lift - the four DIfaceR fields at ARU from the U-raw callee specs below,
   by the AR bridges of lib/A/DIfaceRcgif.v with ARU in place of AR; no walk).

   WHAT THIS FILE IS.  [fs_difR_U] is DIfaceR at the parameters lib/A/DIfaceRcgif.v:42-46 (diface_r_cgif) uses, except
   ARX := ARXr := ARX_ARU tfibsegs B TFIB_INST Up and fpre := fpreU tfibsegs B Up, for every Up:
     U := tr_admit (as_universe B), rpre := rpre_dealloc_cgif, lpost := qtight, dpost := CLenqcgifRaw.dpost_enq_cgif B,
     dbody := drain_body, QB := qloose, DRq := DGif1dr.DRq_cgif B, 16385 <= L24.
   It is built with Build_DIfaceR from four field lemmas, each the ARU twin of its AR source:
     dr_enqueue  [dr_enqueue_U]  twin of CLenqcgifRaw.dr_enqueue_cgif (CLenqcgifRaw.v:54) over CLenqcgif.di_enqueue_cgif
                                 (CLenqcgif.v:474) and DGif1.enq_bridge_cgif (DGif1.v:1884);
     dr_drain    [dr_drain_U]    twin of DGif1d.dr_drain_cgif (DGif1d.v:56) = DGif1df.tfib_drain_ok_cf (DGif1df.v:358);
     dr_rchunk   [dr_rchunk_U]   twin of DGif1dr.dgif1_rchunk_cgif / dgif1_rchunk_walk (DGif1dr.v:420 / :370);
     dr_cdealloc [dr_cdealloc_U] twin of DGif1dr.dgif1_cdealloc_cgif / dgif1_cdealloc_walk (DGif1dr.v:486 / :431).

   THE GAP: FOUR U-RAW CALLEE SPECS (premises of fs_difR_U).  Every DIfaceR field carries the raw frame acall_raw_x
   (DIfaceR.v:51-56: mem' x = mem x on the RAW memory).  a Theorem Labs lane's U twins (lib/A/FSupoisonAllocFK.v:40-120) end in
   FSupoisonU.acall_postU (FSupoisonU.v:171-176), YG0d's acall_post at FSupoison.unpoison U mem: a frame on the view
   only.  The AR sources do not bridge from the released (view-only) specs either: they re-run each walk with the
   segments' raw MEQ kept.  So each U leaf below is the FK leaf with ONE more conjunct, the last one inside its
   existential: DIfaceR.acall_raw_x at the leaf's stack constant, on the raw memory, character for character the text
   of route 1's raw-frame text RAW-TEXT.md (kept by a Theorem Labs lane; a Theorem Labs lane 19:11Z, items 1, 3, 4, 5; `~ False ->` kept
   per its 19:14Z decision).  Each spec has the shape of its FK spec, so once a Theorem Labs lane adds the conjunct to the FK
   leaf, the FK spec is this spec by conversion.
     [drain_leafRU]   FK.drain_leafU (FK.v:43-47) + raw at DSTACK.   AR source: DIfaceR.drain_leaf_raw_cf (DIfaceR.v:85,
                      over :73-79), proved by DGif1df.drain_arm_x (DGif1df.v:351); the walk's MEQs: AFgj.at_RETD (FIN_x,
                      DGif1df.v:107), AFer.ATDR + DoRecycle's raw (EPI_x, DGif1df.v:260); U: FSupoisonAllocFdn.v:328-330.
     [cd_leafRU]      FK.cd_leafU (FK.v:70-77) + raw at KSTACK.      AR source: DGif1dr.cd_leafR (DGif1dr.v:117-122),
                      proved by cdealloc_okR (:132), from AFgk.MEQ (:146); U: FSupoisonAllocFcd.v:184-192 (cd_post_mu).
     [rcc_leafRU]     FK.rcc_leafU (FK.v:86-93) + raw at KSTACK.     AR source: DGif1dr.rcc_leafR (DGif1dr.v:123-128),
                      proved by rchunkR (:322) over rchunk_primR (:161, AFgs.MEQ :176) and rchunk_secR (:300, AFg8.LINKD /
                      AFgv.MEQP); U: FSupoisonAllocFcd.v:353-361 (rc_post_mu), FSupoisonAllocFrs.v.
     [enq_leafRU]     FK.enq_leafU (FK.v:107-115) + raw at QSTACK.   AR source: CLenq.enq_leaf_x's raw clause
                      (CLenq.v:61-62), proved per arm by CLenqcgif.enq_room_xs / enq_hit_xs / enq_miss_xs (CLenqcgif.v:80,
                      :143, :217) from AFgp / AFgq / AFgr MEQ; U: FSupoisonAllocFeqR.v:149, :267, :468.
   (FK.dr_leafU's raw text, RAW-TEXT.md item 2, is what a Theorem Labs lane needs to prove [tfib_drain_specRU]; no DIfaceR field
   reads DoRecycle directly, so it is not a premise here.)

   ONE DIFFERENCE FROM THE AR SOURCES.  AR's cd / rcc raw frame (DGif1dr.v:121-122, :127-128) excludes the stack window
   only; the U texts exclude ascratch (the window and the errno cells).  DIfaceR's dr_rchunk / dr_cdealloc exclude
   ascratch KSTACK_CF, so the fields still follow; DGif1dr.pres_lift reads the stack-only form, so [pres_lift_s] re-proves
   it for the ascratch form (the errno cells lie in the image, below the stack).

   HOW EACH BRIDGE MOVES ACROSS THE UNPOISONING (FSupoisonARXm's kit, FSupoisonARXmD's off-Up facts).  Pre: the ARU pre
   gives AR at unpoison Up mem, and every byte the pre reads raw (stack presence, the cbp word) is off Up.  Post: the U
   leaf's AR at unpoison Up mem' plus its upoison_ok / upoisoned IS ARU at the post; the view frame moves to the raw
   memories because a byte of Up is owned ([view_U]) and a puser byte is off Up ([puser_off]); the raw frame is the new
   conjunct.  The enqueue's pre at the quarantined state ([enq_bridge_U]) is DGif1.enq_bridge_cgif at the unpoisoned
   memories ([dmem_m_U], a cut of FSupoisonARXmD.dmem_c_U at DImg_cgif's zones), then ARU is rebuilt as FSupoisonARXmD's
   di_post_c does: the freed block holds no range of Up (fpreU), and the bytes of Up lie outside every window of dmem_m.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0j YG0k YG08 YG0g YG0l YG0m YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj YFfk YFfn YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLdepot CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGgi DGif1dr DGif1 CLenqcgif CLenqcgifRaw.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocFK.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm FSupoisonARXmD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The U-raw callee specs: the FK leaves with the raw frame as their last conjunct (RAW-TEXT.md items 1, 3-5).      *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section spec.
Variable B : asyms.

(* Drain: FK.drain_leafU (FSupoisonAllocFK.v:43-47) + raw at DSTACK (DIfaceR.drain_leaf_raw_cf, DIfaceR.v:85). *)
Definition drain_leafRU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B DSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B DSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_drain_specRU : Prop :=
  forall ly X U W regs mem md,
    FK.drain_preU B ly X U W regs mem md ->
    amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (drain_leafRU ly X U W regs mem md).

(* CacheDealloc: FK.cd_leafU (FSupoisonAllocFK.v:70-77) + raw at KSTACK (DGif1dr.cd_leafR, DGif1dr.v:117-122). *)
Definition cd_leafRU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B KSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall a, 0 <= a < 2 ^ 64 -> puser ly X a ->
       aview tfibsegs (w_H W') (FSP.unpoison U mem') a = aview tfibsegs (w_H W) (FSP.unpoison U mem) a) /\
    st_cache_inited (snd r) = true /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_cdealloc_specRU : Prop :=
  forall ly X c off U W regs mem md,
    FK.cd_preU B ly X c off U W regs mem md ->
    amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leafRU ly X U W regs mem md).

(* Recycle: FK.rcc_leafU (FSupoisonAllocFK.v:86-93) + raw at KSTACK (DGif1dr.rcc_leafR, DGif1dr.v:123-128). *)
Definition rcc_leafRU (ly : alayout) (X : astate) (k : chunk) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B KSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
       aview tfibsegs (w_H W') (FSP.unpoison U mem') a = aview tfibsegs (w_H W) (FSP.unpoison U mem) a) /\
    st_cache_inited (snd r) = true /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_rchunk_specRU : Prop :=
  forall ly X k cbp U W regs mem md,
    FK.rcc_preU B ly X k cbp U W regs mem md ->
    amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafRU ly X k U W regs mem md).

(* Enqueue: FK.enq_leafU (FSupoisonAllocFK.v:107-115) + raw at QSTACK (CLenq.enq_leaf_x's raw clause, CLenq.v:61-62). *)
Definition enq_leafRU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : chunk) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md' nb,
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B QSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    st_qthread (snd r) = qc_push (st_qthread X) k nb /\
    match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
    st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
    st_fs (snd r) = st_fs X /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B QSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_enqueue_spec_nbRU (nbq : bool) : Prop :=
  forall ly X U W regs mem md k,
    need_new_batch (st_qthread X) = nbq ->
    FK.enq_preU B ly X U W regs mem md k ->
    amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leafRU ly X U W regs mem md k).
End spec.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Kit: the view across the unpoisoning, the zones off Up, the memory at Put's Enqueue call.                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* A view equality on the unpoisoned memories gives it on the raw ones at a byte the pre-state does not own (a byte
   of Up is owned, FSupoison.ush_facts). *)
Lemma view_U : forall segs B ly S Up (W : world segs) mem md (W' : world segs) mem' a,
  FSP.ARU segs B ly S Up W mem md -> 0 <= a < 2 ^ 64 -> ~ aowned B ly S a ->
  aview segs (w_H W') (FSP.unpoison Up mem') a = aview segs (w_H W) (FSP.unpoison Up mem) a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
intros segs B ly S Up W mem md W' mem' a H Ha NO EQ.
destruct (FSP.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
- exfalso. rewrite (wz64 a Ha) in Ei. exact (NO (proj1 (FSP.ush_facts segs B ly S Up W mem md a H Ei))).
- rewrite (FSP.aview_unpoison_out segs (w_H W') Up mem' a Ei), (FSP.aview_unpoison_out segs (w_H W) Up mem a Ei) in EQ.
  exact EQ.
Qed.

(* The same at a byte off Up. *)
Lemma view_off_U : forall segs (W W' : world segs) Up mem mem' a, off_ush Up a ->
  aview segs (w_H W') (FSP.unpoison Up mem') a = aview segs (w_H W) (FSP.unpoison Up mem) a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
intros segs W W' Up mem mem' a O EQ.
rewrite (aview_unpoison_off segs (w_H W') Up mem' a O), (aview_unpoison_off segs (w_H W) Up mem a O) in EQ. exact EQ.
Qed.

(* A user byte of the primary space is above kHighMemBeg, so off Up. *)
Lemma puser_off : forall B ly X Up (W : world tfibsegs) mem md a, FSP.ARU tfibsegs B ly X Up W mem md ->
  0 <= a < 2 ^ 64 -> puser ly X a -> off_ush Up a.
Proof.
intros B ly X Up W mem md a H Ha (c & Hc & Hr).
pose proof (am_layout B ly X _ (FSP.ARU_ARm tfibsegs B ly X Up W mem md H)) as LO.
pose proof (lo_high ly LO) as [HP1 _]. pose proof (lo_space_in ly LO) as [S1 _].
apply (high_off_ush tfibsegs B ly X Up W mem md a H).
unfold region_base, region_off in Hr. rewrite Z.shiftl_mul_pow2 in Hr by lia.
assert (C0 : 0 <= c * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.

(* DImg_cgif's depot zone (DGgi.DZONE: image data, the nodes block, the store block) and internal-allocator zone
   (DGgi.IZONE, below SHADOW_OFF) are off Up. *)
Lemma dzone_off : forall B ly S Up (W : world tfibsegs) mem md a, FSP.ARU tfibsegs B ly S Up W mem md ->
  DGgi.DZONE ly a -> off_ush Up a.
Proof.
intros B ly S Up W mem md a H [Ha|[Ha|Ha]].
- apply (low_off_ush tfibsegs B ly S Up W mem md a H). unfold SHADOW_OFF. lia.
- exact (owned_ext_off_ush tfibsegs B ly S Up W mem md (ly_NB ly, kNodesBlockSize) a H
    ltac:(unfold owned_extents; cbn [In]; tauto) Ha).
- exact (owned_ext_off_ush tfibsegs B ly S Up W mem md (ly_SB ly, kStoreBlockSize) a H
    ltac:(unfold owned_extents; cbn [In]; tauto) Ha).
Qed.

Lemma izone_off : forall B ly S Up (W : world tfibsegs) mem md a, FSP.ARU tfibsegs B ly S Up W mem md ->
  DGgi.IZONE a -> off_ush Up a.
Proof.
intros B ly S Up W mem md a H Ha. apply (low_off_ush tfibsegs B ly S Up W mem md a H).
unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha. unfold SHADOW_OFF. lia.
Qed.

(* DImg_cgif's "internal allocator initialized" (DGgi.IAL_POST) reads only cells below SHADOW_OFF. *)
Lemma ial_post_unpoison : forall B ly S Up (W : world tfibsegs) mem0 md m, FSP.ARU tfibsegs B ly S Up W mem0 md ->
  DGgi.IAL_POST W m -> DGgi.IAL_POST W (FSP.unpoison Up m).
Proof.
intros B ly S Up W mem0 md m H (I1 & I2 & I3 & I4 & I5).
assert (LO : forall a, 0 <= a < SHADOW_OFF -> off_ush Up a)
  by (intros a Ha; exact (low_off_ush tfibsegs B ly S Up W mem0 md a H Ha)).
assert (VU : forall a w v, (forall k, 0 <= k < Z.of_nat w -> 0 <= a + k < SHADOW_OFF) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison Up m)) a w v).
{ intros a w v HO HV. refine (proj2 (val_mem_unpoison tfibsegs (w_H W) Up m a w v _) HV).
  intros k Hk. apply LO. exact (HO k Hk). }
unfold DGgi.IAL_POST. cbv zeta.
refine (conj _ (conj _ (conj _ (conj _ _)))).
- apply VU; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I1].
- apply VU; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I2].
- apply VU; [intros k Hk; unfold TFIB_IAL_W, SHADOW_OFF; lia | exact I3].
- apply VU; [intros k Hk; unfold TFIB_IAL_W, SHADOW_OFF; lia | exact I4].
- intros a Ha. rewrite (mbyte_unpoison_off tfibsegs (w_H W) Up m a); [exact (I5 a Ha)|].
  apply LO. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_HI, SHADOW_OFF in *. lia.
Qed.

(* The memory at Put's call of QuarantineCache::Enqueue (DGif0.dmem_m), moved to the unpoisoned memories
   (FSupoisonARXmD.dmem_c_U's argument, at DImg_cgif's zones). *)
Lemma dmem_m_U : forall B ly S Up W mem0 md sp0 pa nn hb1 DP mem',
  FSP.ARU tfibsegs B ly S Up W mem0 md ->
  (forall a, pa - 16 <= a < pa + 8 -> off_ush Up a) ->
  (forall a, dshadow pa nn a -> off_ush Up a) ->
  dmem_m W ly sp0 mem0 pa nn hb1 DP mem' ->
  dmem_m W ly sp0 (FSP.unpoison Up mem0) pa nn hb1 DP (FSP.unpoison Up mem').
Proof.
intros B ly S Up W mem0 md sp0 pa nn hb1 DP mem' H HDR SHD (C1 & C2 & C3 & C4 & C5 & C6 & V1 & V2 & V3).
assert (OZ : forall a, dg_dzone ly a -> off_ush Up a)
  by (intros a Ha; exact (dzone_off B ly S Up W mem0 md a H Ha)).
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush tfibsegs B ly S Up W mem0 md a H Ha)).
assert (VU : forall a w v, (forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison Up mem')) a w v).
{ intros a w v HO HV. exact (proj2 (val_mem_unpoison tfibsegs (w_H W) Up mem' a w v HO) HV). }
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
- destruct C1 as (memD & D1 & D2 & D3). exists memD. split; [exact D1|]. split.
  + intros a Ha HP. exact (D2 a Ha (apresent_unpoison_bwd (w_H W) Up mem0 a (OZ a Ha) HP)).
  + intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OZ _ Hx))). exact (D3 x Hx).
- intros x H1 H2 H3 H4. apply unpoison_eq. exact (C2 x H1 H2 H3 H4).
- exact (ial_post_unpoison B ly S Up W mem0 md mem' H C3).
- intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (SHD _ Hx))). exact (C4 x Hx).
- intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem' a (C5 a Ha)).
- intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem' a (C6 a Ha)).
- apply VU; [intros k Hk; apply HDR; lia | exact V1].
- apply VU; [intros k Hk; apply HDR; lia | exact V2].
- apply VU; [intros k Hk; apply OT; unfold t_unwinding, kThreadObjSize; lia | exact V3].
Qed.

(* The quarantined state's chunks (FSupoisonARXmD.qfin_chunks for qx). *)
Lemma qx_chunks : forall S k z tr, st_chunks (qx S k z tr) = upd_chunk (st_chunks S) (qk k).
Proof. intros S k z tr. unfold qx, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The four fields.                                                                                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable Up : list (Z * Z).
Local Notation ARXU := (ARX_ARU tfibsegs B TFIB_INST Up).

(* The call post at ARX_ARU from the U leaf's post (same layout), at a window inside the stack. *)
Lemma post_x_U : forall inst stk ly S W regs mem md E S' W' regs' mem' md',
  ARXU inst ly S W mem md ->
  ly_stk_lo ly + stk <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  FSU.acall_postU tfibsegs B stk ly S Up W regs mem md E ly S' W' regs' mem' md' ->
  acall_post_x B ARXU (aowned B) inst stk ly S W regs mem md E ly S' W' regs' mem' md'.
Proof.
intros inst stk ly S W regs mem md E S' W' regs' mem' md' [Hinst HARU] Hlo Hhi
  ((AR' & LLE & WLE & ARP & SIO & AGV & PRS) & OK' & PO').
split; [exact (conj Hinst (conj AR' (conj OK' PO')))|].
split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
split.
- intros a Ha NO NO' NS NE. exact (view_U tfibsegs B ly S Up W mem md W' mem' a HARU Ha NO (AGV a Ha NO NO' NS NE)).
- intros a Ha. apply (apresent_unpoison_bwd (w_H W') Up mem' a); [|exact (PRS a Ha)].
  apply (stack_off_ush tfibsegs B ly S Up W mem md a HARU). lia.
Qed.

(* DGif1dr.pres_lift (DGif1dr.v:344) with the raw frame in the U texts' form: ascratch excluded, so the errno cells
   too; they lie in the image (ts_errno), below the stack (FSupoison.stk_kHighMemBeg). *)
Lemma pres_lift_s : forall ly S S' (W W' : world tfibsegs) mem mem' md md' (regs : bvmap 5 word),
  AR tfibsegs B ly S W mem md -> AR tfibsegs B ly S' W' mem' md' -> wle W W' ->
  (forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly S' (bv_unsigned x) ->
     ~ ascratch B KSTACK regs (bv_unsigned x) -> mem' x = mem x) ->
  ly_stk_lo ly + KSTACK_CF <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W) mem a) ->
  (forall a, spZ regs - KSTACK <= a < spZ regs -> apresent (w_H W') mem' a) ->
  forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W') mem' a.
Proof.
intros ly S S' W W' mem mem' md md' regs HAR HAR' WLE RAW Hlo Hhi P0 P1 a Ha.
destruct (Z_lt_le_dec a (spZ regs - KSTACK)) as [Hl|Hh]; [|apply P1; lia].
pose proof (FSP.stk_kHighMemBeg B ly S _ (proj1 HAR)) as [K1 K2].
pose proof (u64_range (getr regs 2)) as SPR.
assert (Ua : 0 <= a < 2 ^ 64) by (unfold spZ, KSTACK_CF, kHighMemBeg in *; lia).
destruct (P0 a Ha) as [Hn [b Hb]].
assert (E : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ apply RAW; rewrite unsigned_lit_small by exact Ua.
  - apply (AR_stack_law_ok tfibsegs B ly S W mem md a HAR). unfold KSTACK, KSTACK_CF in *. lia.
  - apply (AR_stack_law_ok tfibsegs B ly S' W' mem' md' a HAR'). unfold KSTACK, KSTACK_CF in *. lia.
  - unfold ascratch. rewrite (ts_errno B TB). unfold TFIB_ERRNO, KSTACK, KSTACK_CF, kHighMemBeg in *. lia. }
split; [|exists b; rewrite E; exact Hb].
destruct (w_H W' (Z_to_bv 64 a)) eqn:E'; [|reflexivity]. rewrite (WLE _ E') in Hn. discriminate.
Qed.

(* ---- dr_cdealloc: the twin of DGif1dr.dgif1_cdealloc_walk (DGif1dr.v:431-485) ---- *)
Lemma dr_cdealloc_U : tfib_cdealloc_specRU B -> dr_cdealloc_t B ARXU (aowned B) (DGif1dr.DRq_cgif B).
Proof.
intros CDR inst ly X its z zs W regs mem md PREX RX.
destruct PREX as ([Hinst HARU] & Hci & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (FSP.ARU_AR tfibsegs B ly X Up W mem md HARU) as HAR.
pose proof (DGif1dr.RIx_cd_pre_its _ _ _ _ _ _ _ _ _ RX) as (WF & Z1 & Z2 & Z3 & ROOM).
assert (ROOM0 : 4 * (Z.of_nat (length (class_elems X kBatchClass)) + 1 + (0 + bslack kBatchClass 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X kBatchClass)).
{ change (bslack kBatchClass 0) with 0. exact ROOM. }
assert (STK : forall a, spZ regs - KSTACK_CF <= a < spZ regs -> off_ush Up a).
{ intros a Ha. apply (stack_off_ush tfibsegs B ly X Up W mem md a HARU). unfold KSTACK_CF in *. lia. }
assert (PRE : FK.cd_preU B ly X kBatchClass z Up W regs mem md).
{ split; [|exact (conj (FSP.ARU_ok tfibsegs B ly X Up W mem md HARU) (FSP.ARU_poisoned tfibsegs B ly X Up W mem md HARU))].
  refine (conj HAR (conj Hci (conj _ (conj Z1 (conj Z2 (conj Z3 (conj ROOM0 (conj Hra (conj Hra4 (conj Hal
    (conj _ (conj Hhi (conj _ (conj Hgp (conj Htp (conj Ha0 (conj _ (conj Ha2 Ha3)))))))))))))))))).
  - unfold kBatchClass. lia.
  - unfold KSTACK, KSTACK_CF in *. lia.
  - intros a Ha. apply apresent_unpoison_fwd. apply HPRES. unfold KSTACK, KSTACK_CF in *. lia.
  - rewrite Ha1, Hinst. reflexivity. }
pose proof (CDR ly X kBatchClass z Up W regs mem md PRE) as RR.
assert (APOST : apost (cache_dealloc kBatchClass z X)
  (fun r => exists ns, cache_dealloc_post (as_universe B) 0 0 0 X kBatchClass (z - region_off kBatchClass) ns r)).
{ intros tr r0 Hp. exact (atok_apath _ true _ tr r0
    (cache_dealloc_ok (as_universe B) 0 0 0 X kBatchClass z true WF ltac:(unfold kBatchClass; lia) Z1 Z2 Z3 ROOM0) Hp). }
pose proof (amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] S'] W' c' [(ns & CP) (regs' & mem' & md' & Hc & (POST & OK' & PO') & PUF & CI & RAW)].
cbn [snd] in POST, OK', PO', PUF, CI, RAW |- *.
exists regs', mem', md'. split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [exact (conj Hinst (conj AR' (conj OK' PO')))|].
  split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split.
  { intros a Ha NO NO' NS NE. apply (view_U tfibsegs B ly X Up W mem md W' mem' a HARU Ha NO).
    apply AGV; try assumption. intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
  intros a Ha. apply (apresent_unpoison_bwd (w_H W') Up mem' a (STK a Ha)).
  refine (pres_lift_s ly X S' W W' (FSP.unpoison Up mem) (FSP.unpoison Up mem') md md' regs HAR AR' WLE _ Hlo Hhi _ PRS a Ha).
  - intros x N1 N2 N3. apply unpoison_eq. exact (RAW x N1 N2 N3 (fun F => F)).
  - intros a0 Ha0'. exact (apresent_unpoison_fwd (w_H W) Up mem a0 (HPRES a0 Ha0')). }
split.
{ intros x NO NO' NS NE. apply RAW; [exact NO | exact NO' | | exact NE].
  intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
split.
{ intros a Ha Hp. exact (view_off_U tfibsegs W W' Up mem mem' a (puser_off B ly X Up W mem md a HARU Ha Hp) (PUF a Ha Hp)). }
split.
{ intros a (c0 & Hc0 & Hr). exists c0. split; [exact Hc0|].
  pose proof CP as CP'. destruct CP' as (_ & _ & AU & _). cbn [snd] in AU.
  rewrite (AU c0 ltac:(lia)). exact Hr. }
split; [exact (DGif1dr.RIx_cd_step_its _ _ _ _ _ _ _ _ _ _ _ RX CP)|]. split; [exact CI|].
intros a O. exact (proj1 (aowned_cd_same B ly _ _ _ _ X kBatchClass _ ns S' CP a) O).
Qed.

(* ---- dr_rchunk: the twin of DGif1dr.dgif1_rchunk_walk (DGif1dr.v:370-419) ---- *)
Lemma dr_rchunk_U : tfib_rchunk_specRU B -> dr_rchunk_t B ARXU (aowned B) (DGif1dr.DRq_cgif B).
Proof.
intros RCR inst ly X k ks zs cbp W regs mem md PREX RX.
destruct PREX as ([Hinst HARU] & Hci & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
pose proof (FSP.ARU_AR tfibsegs B ly X Up W mem md HARU) as HAR.
pose proof (RIx_head _ _ _ _ _ _ _ _ _ RX) as (WF & Hk & Hst & Hni).
assert (STK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> off_ush Up a)
  by (intros a Ha; exact (stack_off_ush tfibsegs B ly X Up W mem md a HARU Ha)).
assert (PRE : FK.rcc_preU B ly X k cbp Up W regs mem md).
{ split; [|exact (conj (FSP.ARU_ok tfibsegs B ly X Up W mem md HARU) (FSP.ARU_poisoned tfibsegs B ly X Up W mem md HARU))].
  refine (conj HAR (conj Hci (conj Hk (conj Hst (conj Hni (conj Hra (conj Hra4 (conj Hal (conj _ (conj Hcb1 (conj Hcb2 (conj Hcb3
    (conj _ (conj _ (conj _ (conj Hgp (conj Htp (conj Ha0 Ha1)))))))))))))))))).
  - unfold KSTACK, KSTACK_CF in *. lia.
  - intros a Ha. apply apresent_unpoison_fwd. apply HPRES. unfold KSTACK, KSTACK_CF in *. lia.
  - intros a Ha. apply apresent_unpoison_fwd. exact (HPRC a Ha).
  - refine (proj2 (val_mem_unpoison tfibsegs (w_H W) Up mem cbp 8 _ _) HVC).
    intros j Hj. apply STK. unfold KSTACK_CF in *. lia. }
pose proof (RCR ly X k cbp Up W regs mem md PRE) as RR.
assert (APOST : apost (recycle_chunk k X) (fun r => exists ns, recycle_postx (as_universe B) 0 0 0 X k ns r)).
{ intros tr r0 Hp. exact (atok_apath _ true _ tr r0 (recycle_chunk_okx (as_universe B) 0 0 0 X k true WF Hk Hst Hni) Hp). }
pose proof (amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] S'] W' c' [(ns & RPX & _) (regs' & mem' & md' & Hc & (POST & OK' & PO') & PUF & CI & RAW)].
cbn [snd] in POST, OK', PO', PUF, CI, RAW |- *.
pose proof (RIx_rc_step _ _ _ _ _ _ _ _ _ _ _ RX RPX) as (RX' & _).
exists regs', mem', md'. split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [exact (conj Hinst (conj AR' (conj OK' PO')))|].
  split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split.
  { intros a Ha NO NO' NS NE. apply (view_U tfibsegs B ly X Up W mem md W' mem' a HARU Ha NO).
    apply AGV; try assumption. intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
  intros a Ha. apply (apresent_unpoison_bwd (w_H W') Up mem' a); [apply STK; unfold KSTACK_CF in *; lia|].
  refine (pres_lift_s ly X S' W W' (FSP.unpoison Up mem) (FSP.unpoison Up mem') md md' regs HAR AR' WLE _ Hlo
    ltac:(lia) _ PRS a Ha).
  - intros x N1 N2 N3. apply unpoison_eq. exact (RAW x N1 N2 N3 (fun F => F)).
  - intros a0 Ha0'. exact (apresent_unpoison_fwd (w_H W) Up mem a0 (HPRES a0 Ha0')). }
split.
{ intros x NO NO' NS NE. apply RAW; [exact NO | exact NO' | | exact NE].
  intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
split.
{ intros a Ha Hp Hn.
  exact (view_off_U tfibsegs W W' Up mem mem' a (puser_off B ly X Up W mem md a HARU Ha Hp) (PUF a Ha Hp Hn)). }
split.
{ intros a (c0 & Hc0 & Hr). exists c0. split; [exact Hc0|].
  pose proof RPX as RPX'. unfold recycle_post in RPX'. cbn [snd] in RPX'. destruct RPX' as (_ & _ & _ & _ & _ & _ & _ & _ & AU & _).
  rewrite (AU c0 ltac:(lia)). exact Hr. }
split; [exact RX'|]. split; [exact CI|].
intros a O. exact (aowned_rc_back B ly _ _ _ _ X k ns S' Hst RPX a O).
Qed.

(* ---- dr_drain: the twin of DGif1d.dr_drain_cgif / DGif1df.tfib_drain_ok_cf (DGif1df.v:358-366) ---- *)
Lemma dr_drain_U : tfib_drain_specRU B -> forall L24, drain_spec_raw_cf B ARXU (aowned B) drain_body L24 qloose.
Proof.
intros DRR L24 inst ly X W regs mem md PREcf.
destruct PREcf as ([Hinst HARU] & HTB & HQL & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
pose proof (FSP.ARU_AR tfibsegs B ly X Up W mem md HARU) as HAR.
assert (PRE : FK.drain_preU B ly X Up W regs mem md).
{ split; [|exact (conj (FSP.ARU_ok tfibsegs B ly X Up W mem md HARU) (FSP.ARU_poisoned tfibsegs B ly X Up W mem md HARU))].
  rewrite Hinst in Ha0.
  refine (conj HAR (conj HTB (conj HQL (conj Hra (conj Hra4 (conj Hal (conj Hlo (conj Hhi (conj _ (conj Hgp (conj Htp
    (conj Ha0 (conj Ha1 Ha2))))))))))))).
  intros a Ha. apply apresent_unpoison_fwd. exact (HPRES a Ha). }
eapply amreal_mono; [|exact (DRR ly X Up W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & POSTU & RAW).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (post_x_U inst DSTACK ly X W regs mem md _ _ W' regs' mem' md' (conj Hinst HARU) Hlo Hhi POSTU)|].
exact RAW.
Qed.

(* ---- dr_enqueue: the twin of CLenqcgifRaw.dr_enqueue_cgif (CLenqcgifRaw.v:54-70) ---- *)

(* The pre at the quarantined state: DGif1.enq_bridge_cgif (DGif1.v:1884) at the unpoisoned memories, then ARU
   rebuilt there (FSupoisonARXmD's di_post_c argument, FSupoisonARXmD.v:764-802, for qx in place of qfin_c). *)
Lemma enq_bridge_U : forall L24, 16385 <= L24 ->
  forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
  ARXU inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpreU tfibsegs B Up ly S W mem0 p n -> In (p, n) (blocks S) ->
  tr_admit (as_universe B) S tr ->
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (CLdepot.dpost_x tfibsegs B inst ly S W tr z) mem ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
  getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
  CLenq.enq_pre_x tfibsegs B ARXU inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) /\
  CLenqcgif.EPc L24 (qx S k z tr) (qk k).
Proof.
intros L24 HL24 inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat HX Hrp Hf Hb Htr Hk Hst Hlo Hhi Hbot Hal Hhb Hhv HM
  Hra Hra4 Hsp Hgp Htp Ha0 Ha1 Ha3 Ha4.
pose proof HX as [E HARU].
pose proof (FSP.ARU_ARm tfibsegs B ly S Up W mem0 md0 HARU) as M.
destruct (blk_geo tfibsegs B ly S Up W mem0 md0 p n HARU Hb) as (P16 & P8 & N1 & P4 & PC & HDR).
destruct (find_user_block _ 0 0 0 S p n (am_wf _ _ _ _ M) Hb) as (k0 & Hf0 & _ & _ & _ & Hn').
rewrite Hk in Hf0. injection Hf0 as <-.
assert (SHD : forall a, dshadow (sptr_addr B ly p) (req_size n) a -> off_ush Up a).
{ intros a Ha. exact (dshadow_off tfibsegs B ly S Up W mem0 md0 (sptr_addr B ly p) (req_size n) a HARU P8
    ltac:(lia) ltac:(lia) PC Hf Ha). }
assert (HM' : dmem_m W ly sp0 (FSP.unpoison Up mem0) (sptr_addr B ly p) (req_size n) hb1
  (CLdepot.dpost_x tfibsegs B inst ly S W tr z) (FSP.unpoison Up mem))
  by exact (dmem_m_U B ly S Up W mem0 md0 sp0 _ _ hb1 _ mem HARU HDR SHD HM).
assert (Hhv' : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison Up mem0)) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1)).
{ refine (proj2 (val_mem_unpoison tfibsegs (w_H W) Up mem0 _ _ _ _) Hhv). intros j Hj; apply HDR; lia. }
destruct (DGif1.enq_bridge_cgif B TB L24 HL24 inst ly S W (FSP.unpoison Up mem0) md0 p n tr k z hb1 sp0 regs
  (FSP.unpoison Up mem) mat (ARX_ARU_AR tfibsegs B TFIB_INST Up inst ly S W mem0 md0 HX) Hrp I Hb Htr Hk Hst
  Hlo Hhi Hbot Hal Hhb Hhv' HM' Hra Hra4 Hsp Hgp Htp Ha0 Ha1 Ha3 Ha4) as [PREX HEP].
split; [|exact HEP].
destruct PREX as ([E' HAR'] & Hbud & Hbev & Hrf & Hk' & Hst' & Hnq & Hra' & Hra4' & Hal' & Hlo' & Hhi' & HPRES & Hgp' & Htp'
  & Ha0' & Ha1' & Ha3' & Ha4' & HQL).
assert (HARU' : FSP.ARU tfibsegs B ly (qx S k z tr) Up W mem (with_vm_backing (m_vm_lazy md0) mat md0)).
{ apply (ARU_rebuild_raw tfibsegs B ly S Up W mem0 md0 ly (qx S k z tr) mem _ HARU HAR').
  + (* every block that holds a range of Up survives: the freed block holds none (fpreU) *)
    intros r p' n' Hr' Hb' Hp1 Hp2.
    unfold ablocks in Hb' |- *. apply in_map_iff in Hb' as ([q m] & Eq & Hq). cbn [fst snd] in Eq.
    injection Eq as Eq1 Eq2. subst p' n'.
    destruct (blocks_chunk S q m Hq) as (k0 & Hk0 & Hu0 & Hm0 & Hs0).
    apply in_map_iff. exists (q, m). split; [reflexivity|].
    unfold blocks. apply in_map_iff. exists k0. split; [rewrite Hu0, Hm0; reflexivity|].
    apply filter_In. split; [| unfold is_alloc; rewrite Hs0; reflexivity].
    rewrite qx_chunks.
    destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:Eb.
    * apply sptr_eqb_spec in Eb. exfalso.
      destruct (find_user_spec _ _ _ Hk) as [Hkin Hku].
      pose proof (nodup_beg_inj (st_chunks S) k0 k (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M)) Hk0 Hkin Eb) as Ek.
      subst k0. rewrite Hku in Hu0. subst q. rewrite Hn' in Hm0. subst m.
      destruct (FSP.upoison_ok_In B ly S Up r (FSP.ARU_ok tfibsegs B ly S Up W mem0 md0 HARU) Hr') as (_ & L8 & _).
      pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
      destruct (Hf r Hr') as [D|D]; lia.
    * apply upd_chunk_keeps; [exact Hk0|]. intros Eb'. cbn [qk ck_beg] in Eb'.
      rewrite Eb', sptr_eqb_refl in Eb. discriminate Eb.
  + (* Up's bytes are outside every window of dmem_m *)
    intros s Hs. destruct HM as (_ & FRM & _).
    pose proof (ush_band tfibsegs B ly S Up W mem0 md0 s HARU Hs) as (SB1 & SB2 & SB3).
    assert (NO : forall a, off_ush Up a -> a <> s).
    { intros a Ha ->. exact (ush_not_off tfibsegs B ly S Up W mem0 md0 s HARU Hs Ha). }
    apply FRM; rewrite (in_ush_w64 tfibsegs B ly S Up W mem0 md0 s HARU Hs); intros HW.
    * destruct HW as [HW|[HW|HW]].
      -- apply (NO s); [|reflexivity]. apply (stack_off_ush tfibsegs B ly S Up W mem0 md0 s HARU).
         unfold DGbaseC.DFSTACK in *. lia.
      -- apply (NO s); [|reflexivity]. apply (thread_off_ush tfibsegs B ly S Up W mem0 md0 s HARU).
         unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
      -- apply (NO s); [|reflexivity]. unfold DGgmC.WINB in HW. destruct HW as [HW|HW]; apply HDR; lia.
    * exact (NO s (dzone_off B ly S Up W mem0 md0 s HARU HW) eq_refl).
    * exact (NO s (izone_off B ly S Up W mem0 md0 s HARU HW) eq_refl).
    * exact (NO s (SHD s HW) eq_refl). }
refine (conj (conj E' HARU') (conj Hbud (conj Hbev (conj Hrf (conj Hk' (conj Hst' (conj Hnq (conj Hra' (conj Hra4'
  (conj Hal' (conj Hlo' (conj Hhi' (conj _ (conj Hgp' (conj Htp' (conj Ha0' (conj Ha1' (conj Ha3' (conj Ha4' HQL))))))))))))))))))).
intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (HPRES a Ha)].
apply (stack_off_ush tfibsegs B ly S Up W mem0 md0 a HARU). unfold CLenq.QSTACK_G in *. lia.
Qed.

(* CLenq's enqueue pre at ARX_ARU gives FK's U pre (CLenqcgif.enq_pre_of_x, CLenqcgif.v:58, across the unpoisoning). *)
Lemma enq_preU_of_x : forall inst ly X W regs mem md k,
  CLenq.enq_pre_x tfibsegs B ARXU inst ly X W regs mem md k -> FK.enq_preU B ly X Up W regs mem md k.
Proof.
intros inst ly X W regs mem md k ([Hinst HARU] & Hbud & Hbev & Hrf & Hk & Hst & Hnq & Hra & Hra4 & Hal & Hlo & Hhi & HPRES
  & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL).
split; [|exact (conj (FSP.ARU_ok tfibsegs B ly X Up W mem md HARU) (FSP.ARU_poisoned tfibsegs B ly X Up W mem md HARU))].
refine (conj (FSP.ARU_AR tfibsegs B ly X Up W mem md HARU) (conj Hbud (conj Hbev (conj Hrf (conj Hk (conj Hst (conj Hnq
  (conj Hra (conj Hra4 (conj Hal (conj Hlo (conj Hhi (conj _ (conj Hgp (conj Htp (conj Ha0 (conj Ha1 (conj Ha3 (conj Ha4 HQL))))))))))))))))))).
intros a Ha. apply apresent_unpoison_fwd. exact (HPRES a Ha).
Qed.

(* The U-raw enqueue leaf gives CLenq's leaf at ARX_ARU. *)
Lemma enq_leaf_x_of_RU : forall inst ly X W regs mem md k r W' c',
  CLenq.enq_pre_x tfibsegs B ARXU inst ly X W regs mem md k ->
  enq_leafRU B ly X Up W regs mem md k r W' c' ->
  CLenq.enq_leaf_x tfibsegs B ARXU (aowned B) inst ly X W regs mem md k r W' c'.
Proof.
intros inst ly X W regs mem md k r W' c' ([Hinst HARU] & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _)
  (regs' & mem' & md' & nb & Hc & POSTU & Hqt & Hnb & Hch & Hqg & Hfs & RAW).
exists regs', mem', md', nb. split; [exact Hc|].
split; [|exact (conj Hqt (conj Hnb (conj Hch (conj Hqg Hfs))))].
destruct (post_x_U inst QSTACK ly X W regs mem md _ _ W' regs' mem' md' (conj Hinst HARU) Hlo Hhi POSTU)
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj RAW P7))))))).
Qed.

(* CLenq's sub-interface at ARX_ARU (CLenqcgif.EnqSub_cgif, CLenqcgif.v:441, across the unpoisoning). *)
Lemma EnqSub_U : forall L24, CLenq.EnqSub tfibsegs ARXU (aowned B) qtight qloose L24 (CLenqcgif.EPc L24).
Proof.
intros L24. constructor.
- intros inst inst' ly ly' X X' W W' mem mem' md md' [E1 _] [E2 _]. congruence.
- intros inst ly X W mem md HX. pose proof HX as [_ HARU].
  refine (proj1 (val_mem_unpoison tfibsegs (w_H W) Up mem _ 8 _ _)
    (CLenqcgif.es_qbytes_cgif B inst ly X W _ md (ARX_ARU_AR tfibsegs B TFIB_INST Up inst ly X W mem md HX))).
  intros j Hj. apply (thread_off_ush tfibsegs B ly X Up W mem md _ HARU). unfold t_qc, kThreadObjSize in *. lia.
- exact (CLenqcgif.es_owned_cgif B).
- intros inst ly X W mem md k nb X' HX.
  exact (CLenqcgif.es_lpost_cgif B L24 inst ly X W _ md k nb X' (ARX_ARU_AR tfibsegs B TFIB_INST Up inst ly X W mem md HX)).
- intros inst ly X W mem md k nb X' HX.
  exact (CLenqcgif.es_qb_cgif B L24 inst ly X W _ md k nb X' (ARX_ARU_AR tfibsegs B TFIB_INST Up inst ly X W mem md HX)).
Qed.

Lemma dr_enqueue_U : (forall nbq, tfib_enqueue_spec_nbRU B nbq) -> forall L24, 16385 <= L24 ->
  enq_spec_g B (fun tr S => tr_admit (as_universe B) S tr) ARXU (aowned B) rpre_dealloc_cgif qtight (fpreU tfibsegs B Up)
    (CLenqcgifRaw.dpost_enq_cgif B) L24 qloose (acall_raw_x B (aowned B)).
Proof.
intros ENQ L24 HL24 inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14
  H15 H16 H17 H18 H19 H20 H21 H22 H23.
destruct (enq_bridge_U L24 HL24 inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11
  H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23) as [PREX HEP].
eapply amreal_mono;
[| exact (ENQ (need_new_batch (st_qthread (qx S k z tr))) ly (qx S k z tr) Up W regs mem
     (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) eq_refl (enq_preU_of_x _ _ _ _ _ _ _ _ PREX))].
cbv beta. intros r W' c' LEAF.
destruct (CLenq.di_enq_post_of_leaf tfibsegs B ARXU (aowned B) qtight qloose L24 (CLenqcgif.EPc L24) (EnqSub_U L24)
  inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) r W' c' HEP PREX
  (enq_leaf_x_of_RU _ _ _ _ _ _ _ _ _ _ _ PREX LEAF)) as (regs' & mem' & md' & nb & Hc & HP & R).
destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
exists regs', mem', md', nb. split; [exact Hc|].
split; [exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P8))))))|].
split; [exact P7|].
exact R.
Qed.

(* The record. *)
Theorem difR_U : forall L24, 16385 <= L24 ->
  (forall nbq, tfib_enqueue_spec_nbRU B nbq) -> tfib_drain_specRU B -> tfib_rchunk_specRU B -> tfib_cdealloc_specRU B ->
  DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) ARXU ARXU (aowned B) rpre_dealloc_cgif qtight (fpreU tfibsegs B Up)
    (CLenqcgifRaw.dpost_enq_cgif B) drain_body L24 qloose (DGif1dr.DRq_cgif B).
Proof.
intros L24 HL24 ENQ DRN RCH CDL. constructor.
- exact (dr_enqueue_U ENQ L24 HL24).
- exact (dr_drain_U DRN L24).
- exact (dr_rchunk_U RCH).
- exact (dr_cdealloc_U CDL).
Qed.
End b.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The deliverable: H_difR_U of lib/A/FSReallocAG.v:290-292 at DIfaceRcgif's parameters, for every Up, from the   *)
(*    four U-raw callee specs (section 1).                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem fs_difR_U : forall B, TfibSyms B -> forall L24, 16385 <= L24 ->
  (forall nbq, tfib_enqueue_spec_nbRU B nbq) -> tfib_drain_specRU B -> tfib_rchunk_specRU B -> tfib_cdealloc_specRU B ->
  forall Up,
  DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) (ARX_ARU tfibsegs B TFIB_INST Up) (ARX_ARU tfibsegs B TFIB_INST Up)
    (aowned B) rpre_dealloc_cgif qtight (fpreU tfibsegs B Up) (CLenqcgifRaw.dpost_enq_cgif B) drain_body L24 qloose
    (DGif1dr.DRq_cgif B).
Proof.
intros B TB L24 HL24 ENQ DRN RCH CDL Up. exact (difR_U B TB Up L24 HL24 ENQ DRN RCH CDL).
Qed.
End a.

About fs_difR_U.
Print Assumptions fs_difR_U.
