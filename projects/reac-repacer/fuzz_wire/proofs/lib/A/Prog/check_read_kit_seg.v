(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, at commit d2e4b664b21d), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and proofs/libreac/fuzz_grant/lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the donors are proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (sm_effect_journal, sm_call) and .../LLVMFuzzerTestOneInput_seg_exit_tail.v (t_flag_store_pi) at origin/ossv/recipes 88154566652a: module paths, listing symbol type and this image's own numbers changed, the fake-frame class is 1 (128 bytes) instead of 0, the hypotheses model_laws and api_env are dropped and the two frame-list facts they gave are computed from lib/Reusable/YG00.v's own stack_malloc and stack_free_state, and the four-byte shadow-check lemma, the region helpers and the stack-shadow helpers are new. *)
(* check_read_kit_seg: proofs of the two statements of check_read_kit_segs.v.
   1. crd_sm_path: the frame list and the untouched fields of the allocator state after `stack_malloc`, by computation
      on lib/Reusable/YG00.v's own definition; crd_sf_frames: the frame list after `stack_free_state`.
   2. crd_stack_malloc_at_ok: a class-cid fake-stack call composed into the caller's journal, from the contract
      `astack_malloc_realizes` and the progress law alone (lib/Reusable/YCbq.v ajournal_sub, acall_kept_of_journal).
   3. crd_flag_free_ok: a memory change that writes only bytes the journal allows plus the flag byte of the journal's
      first owned frame, and leaves that byte 0, releases the frame (lib/Reusable/YG0d.v astack_free_law, then
      lib/Reusable/YCbq.v ajournal_after_write). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require WirePImg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import check_read_kit_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.

(* ------------------------------------------------------------------ *)
(* 1. The allocator state after a stack malloc and a stack free        *)
(* ------------------------------------------------------------------ *)

(* `stack_malloc cid s` asks the kernel nothing (lib/Reusable/YG00.v: it is get / put / ret only), so an apath with
   no answers computes its result. A PFake result means fs_probe found a free position, and the state it leaves is
   the entry state with the frame list extended. *)
Lemma crd_sm_path : forall cid s pos s',
  apath (stack_malloc cid s) [] (PFake cid pos, s') ->
  frames s' = (cid, pos) :: frames s /\
  st_chunks s' = st_chunks s /\ st_secs s' = st_secs s /\ st_nev s' = st_nev s /\
  st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
  (exists f, s' = set_fs f s).
Proof.
  intros cid s pos s' H.
  unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
  destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs s)) cid (znth 0 cid (fs_hint (st_fs s))))
    as [[pos0 h0]|] eqn:E; cbn [ibind apath] in H.
  - inversion H. subst.
    repeat split; try reflexivity.
    exists (mkFS (zupd cid h0 (fs_hint (st_fs s))) ((cid, pos) :: fs_live (st_fs s))). reflexivity.
  - inversion H.
Qed.

(* `del_pos` drops the first (cid, pos) of the list, so a frame list that starts with it loses exactly it. *)
Lemma crd_sf_frames : forall cid pos s rest,
  frames s = (cid, pos) :: rest -> frames (stack_free_state cid pos s) = rest.
Proof.
  intros cid pos s rest Hf.
  assert (E : frames (stack_free_state cid pos s) = del_pos (frames s) cid pos) by reflexivity.
  rewrite E, Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The class-cid fake-stack call in the caller's journal            *)
(* ------------------------------------------------------------------ *)

Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation ajournal := (ajournal segs B).

(* lib/Reusable/YCbq.v call_effect_journal, for a call whose memory clause is the stack malloc's: it may change only
   owned bytes and its own stack window, never a heap block, and names no errno byte, so api_env is not needed. *)
Lemma crd_sm_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1,
  AR segs B ly2 S2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (spZ regs - stk <= a < spZ regs) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
  AR segs B lyc Sc W memc mdc ->
  astk_ok stk lyc (spZ regs) ->
  frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
  (length (st_secs Sc) <= length (st_secs S2))%nat ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2)) ->
  qtight S2 ->
  ajournal stk (spZ regs) [] lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs Hkeep HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H6. exact (Hfr a H6 H1 H2 H3). }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|].
split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{ intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (al_owned_low _ _ LAWS _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia. }
split.
{ intros a Hi Hns He _. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- zlia. }
split.
{ intros cid pos a Hin Hr Hnf.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- destruct Hr as [Hr|Hr].
  + clear -Hr Hf0 Hfc C1. lia.
  + destruct Hsb2 as [_ Hsb2b]. destruct Hsb1 as [Hsb1a _].
    assert (Hlt : shadow_addr (frame_addr lyc cid pos + fs_frame_bytes cid) < kHighMemBeg) by (apply Hsb2b; rewrite C4; lia).
    rewrite C3 in Hlt. unfold SHADOW_OFF in Hsb1a. clear -Hr Hse Hlt Hsb1a. lia. }
split; [intros p n i H1 H2 Hi; exfalso; exact (H2 (Hkeep p n H1))|].
split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
{ intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (AR_extra_law_ok segs B lyc Sc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (AR_extra_law_ok segs B ly2 S2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.
End sm.

(* lib/Reusable/YCbq.v aj_stack_malloc_at with crd_sm_effect_journal for its journal step and crd_sm_path for the
   frame list, so neither model_laws nor api_env is used; the segments are image A's, with wire_segs_low. *)
Lemma crd_stack_malloc_at_ok : crd_stack_malloc_at_stmt.
Proof.
unfold crd_stack_malloc_at_stmt.
intros fx rc SK B LAWS stack_malloc_progress cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof WirePImg.wire_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
destruct (crd_sm_path cid Sc pos S2 Hpath) as (Hfrs2 & Hchk2 & Hsecs2 & Hnev2 & Hqt2 & Hqg2 & Hset2).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks, blocks; rewrite Hchk2; reflexivity).
assert (HJ1 : ajournal tfibsegs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ apply (crd_sm_effect_journal tfibsegs B LAWS segs_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | exact Hfr | exact Hpres2
  | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros p n Hp; rewrite Eab2; exact Hp |].
  apply (qtight_ext Sc); [exact Hchk2 | exact Hqt2 | exact Hqg2 | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub tfibsegs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hnev2|].
split; [exact Hset2|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal tfibsegs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The frame-flag store: the frame is released in the journal      *)
(* ------------------------------------------------------------------ *)

(* The middle of UciCcKit.v ucc_flag_store_pi, with the memory and model after the store given instead of computed by a
   run: astack_free_law gives the allocator invariant of the state without the frame, and ajournal_after_write
   carries the journal over the written bytes (the journal's own, plus the frame's flag byte, which the frame owns). *)
Lemma crd_flag_free_ok : crd_flag_free_stmt.
Proof.
unfold crd_flag_free_stmt.
intros rc SK B LAWS ASF FFL STK sp0 FP ly S W0 mem md own' lyc Sc W memc mdc k cid pos memc' mdc' Wr
HJ Hcid Hfr' Hgr' Hhid Hsame' Hwr Hflag0.
pose proof WirePImg.wire_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc Sc W memc mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
  aview tfibsegs (w_H W) memc' a = aview tfibsegs (w_H W) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame') as Emd.
assert (HAR' : AR tfibsegs B lyc (stack_free_state cid pos Sc) W memc' mdc').
{ eapply (ASF lyc Sc W memc mdc memc' mdc' cid pos HAR Hin).
  - exact Hflag0.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. exact (Hhid _ Hh). }
eapply (ajournal_after_write tfibsegs B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memc
  mdc k memc' mdc' Wr (stack_free_state cid pos Sc) own' HJ Heqw
  ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
- intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
- exact HAR'.
- unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
- reflexivity.
- cbn. zlia.
- exact (crd_sf_frames cid pos Sc (own' ++ frames S) Hfrs).
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
  apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.

Check (crd_stack_malloc_at_ok : crd_stack_malloc_at_stmt).
Check (crd_flag_free_ok : crd_flag_free_stmt).
