(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 1087 of its 1309 lines of code are new or changed and 302 lines of the source are left out. *)
(* check_read_cgW: Theorem wire_check_read_holds : forall fx rc B MT, wire_check_read_holds_stmt
   (lib/B/Prog/check_read_cg.v), the walk of check_read in image B (fuzz_wire.asan-ubsan 0x805f4, frame 0xc0
   realigned to 32 bytes, the class-1 fake frame of __asan_stack_malloc_1).
   1. The class-1 fake frame in the caller's journal: crw_sm_path .. crw_stack_malloc_at, the port of
      reac-repacer/fuzz_uci's lib/B/Prog/UciCcKit.v ucc_sm_path .. ucc_stack_malloc_at (from the contract
      astack_malloc_realizes alone: no model_laws, no api_env).
   2. Footprint runs carried into SRr (crw_run, the form of fuzz_uci's lib/A/Prog/check_value_cgW.v cv_run), the
      journal across a run's writes (crw_aj_step, lib/B/YCbq.v ajournal_exec), and the release of the frame
      (crw_release: YG0d.v astack_free_law, then YCbq.v ajournal_after_write with the flag byte as the one owned byte
      written).
   3. The walk, backwards from the return: crw_at_ret1 (segment C, the release, the post by YCbq.v ajournal_sub and
      acall_kept_of_journal, the meter bound by mo_le_set_fs_r), crw_leaf_call (rp_slot_read by the statement's leaf
      premise through lib/B/Prog/WireCcLeafb.v wcc_leafb_journal; its premises from the journal, the caller's block of
      c and the frame's shadow segment B wrote), crw_at_ret0 (segment B), crw_entry (segment A and the stack malloc).
   The footprint runs are lib/B/Prog/check_read_walk_kit.v's. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0p YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.

(* ------------------------------------------------------------------ *)
(* 1. The allocator state after a stack malloc and a stack free        *)
(* ------------------------------------------------------------------ *)

(* `stack_malloc cid s` asks the kernel nothing (lib/Reusable/YG00.v: it is get / put / ret only), so an apath with
   no answers computes its result. A PFake result means fs_probe found a free position, and the state it leaves is
   the entry state with the frame list extended. *)
Lemma crw_sm_path : forall cid s pos s',
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
Lemma crw_sf_frames : forall cid pos s rest,
  frames s = (cid, pos) :: rest -> frames (stack_free_state cid pos s) = rest.
Proof.
  intros cid pos s rest Hf.
  assert (E : frames (stack_free_state cid pos s) = del_pos (frames s) cid pos) by reflexivity.
  rewrite E, Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma crw_sf_chunks : forall cid pos s,
  st_chunks (stack_free_state cid pos s) = st_chunks s /\
  st_secs (stack_free_state cid pos s) = st_secs s /\
  st_nev (stack_free_state cid pos s) = st_nev s /\
  st_qthread (stack_free_state cid pos s) = st_qthread s /\
  st_qglobal (stack_free_state cid pos s) = st_qglobal s.
Proof. intros cid pos s. repeat split; reflexivity. Qed.

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

(* lib/B/YCbq.v call_effect_journal, for a call whose memory clause is the stack malloc's: it may change only
   owned bytes and its own stack window, never a heap block, and names no errno byte, so api_env is not needed. *)
Lemma crw_sm_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1,
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
    rewrite C3 in Hlt. unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia. }
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

Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation code := (as_code B).

(* lib/B/YCbq.v aj_stack_malloc_at with crw_sm_effect_journal for its journal step and crw_sm_path for the
   frame list, so neither model_laws nor api_env is used. *)
Lemma crw_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
st_nev S2 = st_nev Sc /\ (exists f, S2 = set_fs f Sc) /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
destruct (crw_sm_path cid Sc pos S2 Hpath) as (Hfrs2 & Hchk2 & Hsecs2 & Hnev2 & Hqt2 & Hqg2 & Hset2).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks, blocks; rewrite Hchk2; reflexivity).
assert (HJ1 : ajournal ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ apply (crw_sm_effect_journal ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | exact Hfr | exact Hpres2
  | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros p n Hp; rewrite Eab2; exact Hp |].
  apply (qtight_ext Sc); [exact Hchk2 | exact Hqt2 | exact Hqg2 | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hnev2|].
split; [exact Hset2|].
split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End sm.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import check_read_walk_kit.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0p YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import check_read_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_slot_read_cg rp_slot_read_F_c rp_slot_width_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require reac_frame_clean_len_c rp_frame_channels_c.
Import ListNotations.
Open Scope Z_scope.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module LSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_cg.
Module RSRF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_F_c.
Module RSWF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_width_F_c.
Module RCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_clean_len_c.
Module RFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_c.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Small facts                                                              *)
(* ======================================================================== *)

Lemma crw_entry_eq : wire_sigma WS_check_read = CRW_ENTRY.
Proof. reflexivity. Qed.
Lemma crw_sm1_eq : wire_sigma WS___asan_stack_malloc_1 = CRW_SM1.
Proof. reflexivity. Qed.

Lemma crw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma crw_signed_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. change (bv_signed (Z_to_bv 64 z)) with (bv_swrap 64 (bv_unsigned (Z_to_bv 64 z))).
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
  change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Lemma crw_rom_img : forall a, in_rom tfibsegs a -> in_img tfibsegs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

Lemma crw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (fuzz_uci's lib/A/Prog/check_value_cgW.v cv_run). *)
Lemma crw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (crw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma crw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma crw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma crw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 13) = x13 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (crw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

(* A byte present before and after with the same view is the same raw byte. *)
Lemma crw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma crw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

Lemma crw_bytes_at_ext : forall (m m' : word -> option byte) (A : Z) (bs : list byte),
  bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & Hb) He. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  unfold mrd. rewrite (He (A + Z.of_nat i)) by lia. exact (Hb i Hi).
Qed.

(* Cells and bytes kept by a step that keeps their view and their presence. *)
Lemma crw_rw_cells_kept : forall (H : word -> bool) (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     apresent H m a /\ apresent H m' a /\ aview tfibsegs H m' a = aview tfibsegs H m a) ->
  rw_cells rsegs m' A cs.
Proof.
  intros H m m' A cs HC HK. apply (crw_rw_cells_ext m m' A cs HC). intros a Ha.
  destruct (HK a Ha) as (P1 & P2 & E). unfold wa. exact (crw_byte_eq H H m m' a P1 P2 E).
Qed.

Lemma crw_bytes_at_kept : forall (H : word -> bool) (m m' : word -> option byte) (A : Z) (bs : list byte),
  bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) ->
     apresent H m a /\ apresent H m' a /\ aview tfibsegs H m' a = aview tfibsegs H m a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros H m m' A bs HB HK. apply (crw_bytes_at_ext m m' A bs HB). intros a Ha.
  destruct (HK a Ha) as (P1 & P2 & E). unfold wa. exact (crw_byte_eq H H m m' a P1 P2 E).
Qed.

(* Present bytes are a junk cell. *)
Lemma crw_present_rw : forall (W : world tfibsegs) m A (n : nat),
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat n -> apresent (w_H W) m a) ->
  exists J, rw_cells rsegs m A [CB n J].
Proof.
  intros W m A n H0 H1 HP.
  pose proof (wcc_leafb_stk W m A (A + Z.of_nat n) H0 H1 HP) as ST.
  destruct (stk_carve rsegs m A (A + Z.of_nat n) n ST ltac:(lia)) as [_ [J HJ]].
  replace (A + Z.of_nat n - Z.of_nat n) with A in HJ by lia. exists J. exact HJ.
Qed.

(* A byte the view shows, outside the loaded image, is present. *)
Lemma crw_present_of_aview : forall (W : world tfibsegs) m a v,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  aview tfibsegs (w_H W) m a = Some v -> apresent (w_H W) m a.
Proof.
  intros W m a v Ha Hn H. pose proof (wcc_leafb_aview_vis W m a v H) as Hv. split; [exact Hv|].
  unfold aview, YP09.mbyte, mrestrict in H. rewrite Hv in H.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
  rewrite (seg_rom_none tfibsegs a Ha Hn) in H. discriminate.
Qed.

Lemma crw_aview_wrap : forall H m a, aview tfibsegs H m a = aview tfibsegs H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros H m a. unfold aview, YP09.mbyte, mrestrict. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma crw_apresent_wrap : forall H m a, apresent H m a <-> apresent H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros H m a. unfold apresent. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* The 8 bytes of an image constant, as the image holds them (decided by vm_compute). *)
Definition crw_rom_chk (a K : Z) : bool :=
  forallb (fun i => match YK11.seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error (le8 (Z_to_bv 64 K)) i with
                    | Some b, Some c => (bv_unsigned b =? bv_unsigned c)
                    | _, _ => false
                    end) (seq 0 8).

Lemma crw_rom_chk_M : crw_rom_chk RCL.A_M RCL.KM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crw_rom_chk_T : crw_rom_chk RCL.A_T RCL.KT = true.
Proof. vm_compute. reflexivity. Qed.

(* A constant the view shows as the image's bytes is bytes_at of the raw memory. *)
Lemma crw_rom_bytes : forall (W1 : world tfibsegs) m1 a K,
  crw_rom_chk a K = true -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> aview tfibsegs (w_H W1) m1 (a + i) =
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (a + i)))) ->
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 K)).
Proof.
  intros W1 m1 a K HC H0 H8 HV.
  split; [exact H0|]. rewrite length_le8. split; [lia|].
  intros i Hi.
  unfold crw_rom_chk in HC. rewrite forallb_forall in HC.
  specialize (HC i ltac:(apply in_seq; lia)).
  specialize (HV (Z.of_nat i) ltac:(lia)).
  destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:Eb; [|discriminate HC].
  destruct (nth_error (le8 (Z_to_bv 64 K)) i) as [c|] eqn:Ec; [|discriminate HC].
  apply Z.eqb_eq in HC. cbn [option_map] in HV.
  destruct (wcc_leafb_mrd_aview W1 m1 _ _ HV) as (b' & Hb' & Hu).
  assert (Hb2 : mrd rsegs m1 (wa (a + Z.of_nat i)) = Some b') by exact Hb'.
  rewrite Hb2. f_equal. apply bv_eq. lia.
Qed.

(* ======================================================================== *)
(* A footprint run's writes in the caller-journal form                      *)
(* ======================================================================== *)

Lemma crw_outside_dec : forall (Wl : list (Z * Z)) x, outside Wl x \/ ~ outside Wl x.
Proof.
  induction Wl as [|[lo hi] Wl IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_lt_le_dec x lo) as [L|L]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [L'|L']; [right; intros [H' _]; lia | left; split; [lia | exact H]].
Qed.

(* A byte outside the loaded image that the write view shows is a raw byte. *)
Lemma crw_wview_raw : forall (m : word -> option byte) (x : word),
  ~ in_img tfibsegs (bv_unsigned x) -> wview rsegs m x <> None -> m x <> None.
Proof.
  intros m x Hn Hw. change (wview tfibsegs m x <> None) in Hw. unfold wview in Hw.
  destruct (m x) as [b|]; [discriminate|].
  rewrite (find_segment_none tfibsegs (bv_unsigned x) Hn) in Hw. exact Hw.
Qed.

Section J. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* The journal follows a run that writes only bytes it allows, all outside the image. *)
Lemma crw_aj_step : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wl : list (Z * Z)),
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  munch Wl memc memc' -> wmono rsegs memc memc' ->
  (forall a, ~ outside Wl a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a /\
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wl HJ MU WM HW Hs.
  assert (HP : forall x : word, ~ outside Wl (bv_unsigned x) -> apresent (w_H Wc) memc (bv_unsigned x)).
  { intros x Ha. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R. destruct (HW _ Ha R) as (_ & Hw).
    exact (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw)). }
  eapply (ajournal_exec segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k
            memc' mdc' (fun a => ~ outside Wl a /\ 0 <= a < 2 ^ 64) HJ).
  - intros x Hx. unfold mrestrict. destruct (crw_outside_dec Wl (bv_unsigned x)) as [Ho|Ho];
      [rewrite (MU x Ho); reflexivity|].
    exfalso. apply Hx. split; [exact Ho|]. pose proof (bv_unsigned_in_range 64 x) as R. exact R.
  - intros x Hx. unfold mrestrict in *. destruct (w_H Wc x) eqn:Eh; [exact Hx|].
    destruct (crw_outside_dec Wl (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
    pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
    destruct (HW _ Ho R) as (Hni & _).
    apply (crw_wview_raw memc' x Hni). apply WM. unfold wview.
    destruct (memc x); [discriminate | exfalso; exact (Hx eq_refl)].
  - intros x Hh. destruct (crw_outside_dec Wl (bv_unsigned x)) as [Ho|Ho]; [exact (MU x Ho)|].
    destruct (HP _ Ho) as [Hv _]. rewrite Z_to_bv_bv_unsigned in Hv. congruence.
  - exact Hs.
  - intros a (Ha & Hr). exact (proj2 (HW a Ha Hr)).
Qed.

Lemma crw_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  apply (crw_aj_step STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc' [] HJ
           (munch_refl [] memc) (wmono_refl rsegs memc)); [|exact Hs].
  intros a Ha. exfalso. exact (Ha I).
Qed.

(* The release: a run that writes allowed bytes and the flag byte of the one owned class-1 frame, leaving that
   byte 0, gives the frame back (YG0d.v astack_free_law), and the journal owns no frame again. *)
Lemma crw_release : astack_free_law segs B -> frame_flag_lawP segs B ->
  forall STK sp0 FP ly S W mem md lyc Sc Wc memc mdc k pos memc' mdc' (Wl : list (Z * Z)),
  ajournalA STK sp0 FP ly S W mem md [(1, pos)] lyc Sc Wc memc mdc k ->
  munch (Wl ++ [(flag_addr lyc 1 pos, flag_addr lyc 1 pos + 1)]) memc memc' -> wmono rsegs memc memc' ->
  (forall a, ~ outside Wl a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a /\
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(1, pos)] a) ->
  bytes_at rsegs memc' (flag_addr lyc 1 pos) [Z_to_bv 8 0] ->
  same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md [] lyc (stack_free_state 1 pos Sc) Wc memc' mdc' k.
Proof.
  intros ASF FFL STK sp0 FP ly S W mem md lyc Sc Wc memc mdc k pos memc' mdc' Wl HJ MU WM HW HFL Hs.
  set (FL := flag_addr lyc 1 pos) in *.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
  assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (FFL lyc Sc Wc memc mdc 1 pos HAR Hin) as (Hfp & Hfo & (Hfapp & Hfimg) & (Hf4 & _ & Hfc)).
  fold FL in Hfp, Hfo, Hfapp, Hfimg, Hf4, Hfc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HFL64 : 0 <= FL < 2 ^ 64) by lia.
  set (Wa := Wl ++ [(FL, FL + 1)]) in *.
  assert (Hout : forall a, outside Wa a <-> outside Wl a /\ ~ (FL <= a < FL + 1)).
  { intros a. unfold Wa. clear. induction Wl as [|[lo hi] Wl IH]; cbn [app outside]; [tauto|]. rewrite IH. tauto. }
  assert (Hin2 : forall a, ~ outside Wa a -> ~ outside Wl a \/ a = FL).
  { intros a Ha. destruct (crw_outside_dec Wl a) as [Ho|Ho]; [|left; exact Ho]. right.
    destruct (Z_lt_le_dec a FL); [exfalso; apply Ha; apply Hout; split; [exact Ho | lia]|].
    destruct (Z_lt_le_dec a (FL + 1)); [lia | exfalso; apply Ha; apply Hout; split; [exact Ho | lia]]. }
  assert (HP : forall a, ~ outside Wl a -> 0 <= a < 2 ^ 64 -> apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a).
  { intros a Ha Hr. destruct (HW a Ha Hr) as (_ & Hw).
    exact (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw). }
  assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> outside Wa a ->
    aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
  { intros a Ha Ho. apply aview_eq_of. unfold mrestrict. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite crw_u64 by lia. exact Ho. }
  (* the flag byte reads 0 after the run *)
  assert (HF0 : aview segs (w_H Wc) memc' FL = Some 0).
  { destruct HFL as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
    rewrite Z.add_0_r in HB. unfold mrd, wa in HB.
    destruct Hfp as [Hv _]. unfold aview, YP09.mbyte, mrestrict. rewrite Hv.
    destruct (memc' (Z_to_bv 64 FL)) as [b|] eqn:E.
    - injection HB as ->. reflexivity.
    - pose proof (seg_rom_none segs FL HFL64 Hfimg) as HR.
      change (PropExec.seg_rom rsegs (Z_to_bv 64 FL) = None) in HR. rewrite HR in HB. discriminate. }
  (* a written byte is present after the run *)
  assert (HPw : forall a, ~ outside Wa a -> 0 <= a < 2 ^ 64 -> apresent (w_H Wc) memc' a).
  { intros a Ha Hr. destruct (Hin2 a Ha) as [Ha' | ->].
    - destruct (HW a Ha' Hr) as (Hni & _). destruct (HP a Ha' Hr) as ([Hv [b Hb]] & _).
      split; [exact Hv|].
      assert (Hw : wview rsegs memc' (Z_to_bv 64 a) <> None) by (apply WM; unfold wview; rewrite Hb; discriminate).
      assert (Hni' : ~ in_img segs (bv_unsigned (Z_to_bv 64 a))) by (rewrite crw_u64 by lia; exact Hni).
      pose proof (crw_wview_raw memc' _ Hni' Hw) as Hr'.
      destruct (memc' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (Hr' eq_refl)].
    - exact (crw_present_of_aview Wc memc' FL 0 HFL64 Hfimg HF0). }
  pose proof (same_but_materialized_wvb mdc mdc' Hs) as Emd.
  assert (HAR' : AR segs B lyc (stack_free_state 1 pos Sc) Wc memc' mdc').
  { eapply (ASF lyc Sc Wc memc mdc memc' mdc' 1 pos HAR Hin HF0).
    - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. apply Hout. split.
      + destruct (crw_outside_dec Wl a) as [H'|H']; [exact H'|]. exfalso. exact (proj2 (HP a H' Ha) Ho).
      + intros Hr. apply Hne. fold FL. lia.
    - intros a Hv. rewrite crw_aview_wrap in Hv |- *.
      set (a' := bv_unsigned (Z_to_bv 64 a)) in *.
      assert (Ha' : 0 <= a' < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; exact R).
      destruct (crw_outside_dec Wa a') as [Ho|Ho]; [rewrite (Heqw a' Ha' Ho); exact Hv|].
      destruct (HPw a' Ho Ha') as [Hv' [b Hb]]. unfold aview, YP09.mbyte, mrestrict. rewrite Hv', Hb. discriminate.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - intros a _ Hh. destruct (crw_outside_dec Wa (bv_unsigned (w64 a))) as [Ho|Ho]; [exact (MU _ Ho)|].
      pose proof (bv_unsigned_in_range 64 (w64 a)) as R.
      destruct (HPw _ Ho R) as [Hv _]. rewrite Z_to_bv_bv_unsigned in Hv. congruence. }
  eapply (ajournal_after_write segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W mem md [(1, pos)] lyc Sc Wc memc
            mdc k memc' mdc' (fun a => ~ outside Wa a /\ 0 <= a < 2 ^ 64) (stack_free_state 1 pos Sc) [] HJ).
  - intros a Ha HWa. apply Heqw; [exact Ha|].
    destruct (crw_outside_dec Wa a) as [Ho|Ho]; [exact Ho | exfalso; exact (HWa (conj Ho Ha))].
  - intros a Hp. apply crw_apresent_wrap in Hp. apply crw_apresent_wrap.
    set (a' := bv_unsigned (Z_to_bv 64 a)) in *.
    assert (Ha' : 0 <= a' < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as R; exact R).
    destruct (crw_outside_dec Wa a') as [Ho|Ho]; [|exact (HPw a' Ho Ha')].
    destruct Hp as [Hv [b Hb]]. split; [exact Hv|]. exists b. rewrite (MU (Z_to_bv 64 a')); [exact Hb|].
    rewrite crw_u64 by lia. exact Ho.
  - exact Hs.
  - intros a (Ha & Hr). destruct (Hin2 a Ha) as [Ho | ->].
    + left. exact (proj2 (HW a Ho Hr)).
    + right. split; [exact Hfo | split; [exact Hfapp | exact Hfimg]].
  - exact HAR'.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. lia.
  - exact (crw_sf_frames 1 pos Sc (frames S) Hfrs).
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.
End J.

(* ======================================================================== *)
(* The walk in the caller-journal form                                      *)
(* ======================================================================== *)

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HPCS : pc_stack_malloc (as_code B) CRD_CID = wire_sigma WS___asan_stack_malloc_1.
Hypothesis HCELLS : wire_cells B.
Hypothesis HOWN : wire_ro_rd_unowned B.
Hypothesis HERR : wire_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.
Hypothesis ASM : @astack_malloc_realizes fx rc segs B CRD_CID.
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_wr_at rc B (@LSR.wire_rp_slot_read_cg) fx'.
Hypothesis SEGB : crw_segB_stmt.
Hypothesis SEGC : crw_segC_stmt.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (pin len slot : Z) (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 pin.
Hypothesis H11 : YK11.getr regs 11 = w64 len.
Hypothesis H12 : YK11.getr regs 12 = w64 slot.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CRD_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hlen : 0 <= len <= W_RECV_MAX.
Hypothesis Hbs : Z.of_nat (length bs) = len.
Hypothesis Hslot : INT_MIN <= slot <= INT_MAX.
Hypothesis Hblk : 0 < len -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= pin /\ pin + len <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) pin (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hcnt : count_cid CRD_CID (frames Sc) < fs_frames CRD_CID.
Hypothesis Hrom : wire_rom_view_rd W memc.

Local Abbreviation SP0 := (spZ regs).
Local Abbreviation SP1 := (crw_sp1 (spZ regs)).
Local Abbreviation POST := (wire_crd_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
Local Abbreviation JI own' S' m md := (ajournalA CRD_STK (spZ regs) [] lyc Sc W memc mdc own' lyc S' W m md 0).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).
(* The thirteen words the prologue saves below the entry sp (s11 at sp - 104 .. ra at sp - 8). *)
Definition crw_saves (m : word -> option byte) : Prop :=
  rw_cells rsegs m (spZ regs - 104)
    [C8 (GR regs 27); C8 (GR regs 26); C8 (GR regs 25); C8 (GR regs 24); C8 (GR regs 23); C8 (GR regs 22);
     C8 (GR regs 21); C8 (GR regs 20); C8 (GR regs 19); C8 (GR regs 18); C8 (GR regs 9); C8 (GR regs 8);
     C8 (GR regs 1)].

Lemma crw_JI0 : JI [] Sc memc mdc.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CRD_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
  - lia.
Qed.

Lemma crw_sp_rng : YM05.alloc_ceiling + CRD_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof crw_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma crw_win : forall own' S' m md, JI own' S' m md ->
  forall a, spZ regs - CRD_STK <= a < spZ regs -> apresent (w_H W) m a.
Proof.
  intros own' S' m md J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma crw_sp1_rng : spZ regs - 208 <= SP1 <= spZ regs - 192 /\ SP1 mod 32 = 0.
Proof.
  pose proof crw_sp_rng as [S1 S2]. pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  apply crw_sp1_facts; [unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in S1; lia | exact Hal].
Qed.

(* The class-1 fake frame the stack malloc handed back, at any state of the inner journal that owns it. *)
Lemma crw_frame_facts : forall S2 pos m md, JI [(1, pos)] S2 m md -> frames S2 = (1, pos) :: frames Sc ->
  4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos mod 64 = 0 /\
  frame_addr lyc 1 pos + 128 <= YM05.alloc_ceiling /\ in_app (frame_addr lyc 1 pos) 128 /\
  (forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
     apresent (w_H W) m a /\ ~ aowned B lyc S2 a /\ ~ in_img segs a) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W) m (crw_sh (frame_addr lyc 1 pos) + i) /\
     ~ aowned B lyc S2 (crw_sh (frame_addr lyc 1 pos) + i) /\ ~ in_img segs (crw_sh (frame_addr lyc 1 pos) + i)) /\
  (frame_addr lyc 1 pos + 128 <= crw_sh (frame_addr lyc 1 pos) \/
   crw_sh (frame_addr lyc 1 pos) + 16 <= frame_addr lyc 1 pos) /\
  kLowMemEnd <= crw_sh (frame_addr lyc 1 pos) /\ crw_sh (frame_addr lyc 1 pos) + 16 <= 2 ^ 45.
Proof.
  intros S2 pos m md J Hfrs.
  pose proof (proj1 J) as HAR.
  assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hin) as (HFal & HFapp & HFb & HFsh).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF0 & HFc & _).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFsh.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (E64 : frame_addr lyc 1 pos mod 64 = 0).
  { destruct HAR as [M _].
    destruct (frame_facts B lyc S2 _ 1 pos M Hin) as (_ & _ & _ & _ & PA & _ & _ & FO & _).
    unfold page_aligned in PA. unfold frame_addr. clear - PA FO. Z.div_mod_to_equations. lia. }
  assert (ESH : forall i, crw_sh (frame_addr lyc 1 pos) + i = shadow_addr (frame_addr lyc 1 pos) + i)
    by (intros i; unfold crw_sh, shadow_addr, SHADOW_OFF, ASAN_K; lia).
  set (FR := frame_addr lyc 1 pos) in *.
  assert (HD8 : 0 <= FR / 8 <= 2 ^ 47 / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
  unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  split; [lia|]. split; [exact E64|]. split; [lia|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; lia|].
  split.
  { intros a Ha. destruct (HFb a Ha) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    exact (frm_img segs B LAWS _ _ _ _ _ 1 pos a HAR Hin Ha). }
  split.
  { intros i Hi. rewrite ESH. destruct (HFsh i Hi) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    intros Him. pose proof (WirePImg.wire_segs_low _ Him). unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia. }
  unfold crw_sh, ASAN_K, kLowMemEnd. lia.
Qed.

(* The frame c, on a path that reads it: the caller's block holds it, at any state of the inner journal. *)
Lemma crw_block_facts : forall own' S2 m md, JI own' S2 m md -> ablocks B lyc S2 = ablocks B lyc Sc -> 0 < len ->
  exists bA nA, In (bA, nA) (ablocks B lyc S2) /\ bA <= pin /\ pin + len <= bA + req_size nA /\
  4096 <= bA /\ bA + req_size nA <= YM05.alloc_ceiling /\ in_app bA (req_size nA) /\
  bytes_at rsegs m pin bs /\ AsanCells.addressable m pin len /\
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) pin len /\
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (AsanCells.shadow_addr pin)
    (AsanCells.shadow_addr (pin + len - 1) - AsanCells.shadow_addr pin + 1).
Proof.
  intros own' S2 m md J Eab Hl.
  destruct (Hblk Hl) as (bA & nA & Hb & H1 & H2).
  pose proof (proj1 J) as HAR. pose proof crw_JI0 as J0. pose proof (proj1 J0) as HAR0.
  assert (Hb2 : In (bA, nA) (ablocks B lyc S2)) by (rewrite Eab; exact Hb).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR Hb2) as (_ & H4096 & Hc & Happ & Hpres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR0 Hb) as (_ & _ & _ & _ & Hpres0 & _).
  assert (HnA : 0 <= nA) by lia.
  destruct (req_size_pos nA HnA) as [R1 R2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  exists bA, nA. split; [exact Hb2|]. split; [exact H1|]. split; [lia|]. split; [exact H4096|]. split; [exact Hc|].
  split; [exact Happ|].
  split.
  { pose proof (wcc_leafb_bytes_garr8 W memc pin bs Hgarr ltac:(lia) ltac:(lia)) as B0.
    apply (crw_bytes_at_kept (w_H W) memc m pin bs B0). intros a Ha. rewrite Hbs in Ha.
    split; [exact (proj1 (Hpres0 a ltac:(lia)))|]. split; [exact (proj1 (Hpres a ltac:(lia)))|].
    pose proof J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    replace a with (bA + (a - bA)) by lia. apply (F2 bA nA (a - bA) Hb Hb2); [lia | intros (r & Hr & _); destruct Hr]. }
  split; [apply (wcc_leafb_addressable_block B LAWS lyc S2 W m md bA nA pin len HAR Hb2); lia|].
  split; [apply (wcc_leafb_rng_block B LAWS lyc S2 W m md bA nA pin len HAR Hb2); lia|].
  apply (wcc_leafb_rng_shadow_block B LAWS lyc S2 W m md bA nA pin len HAR Hb2); lia.
Qed.

(* The read-only constants keep their image bytes through the inner journal (its image clause), and the contract's
   wire_rom_view_rd says what they are at the entry. *)
Lemma crw_rom_at : forall own' S2 m md, JI own' S2 m md -> forall a, wire_in_ro_rd a ->
  aview segs (w_H W) m a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)).
Proof.
  intros own' S2 m md J1 a Hin.
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  destruct (wire_ro_rd_scoped B HOWN HERR a Hin) as [N1 N2].
  destruct (wire_ro_rd_rom_clean a Hin) as [HR _].
  rewrite (F3 a (crw_rom_img a HR) N1 N2 (fun Ho => False_ind _ (sink_closed_nil Ho))).
  exact (Hrom a Hin).
Qed.

(* After rp_slot_read: segment C, the release of the fake frame, and the post. *)
Lemma crw_at_ret1 : forall S2 pos f2 regs4 m4 md4,
  frames S2 = (1, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc -> st_nev S2 = st_nev Sc ->
  S2 = set_fs f2 Sc ->
  JI [(1, pos)] S2 m4 md4 ->
  GR regs4 2 = Z_to_bv 64 SP1 -> GR regs4 3 = GR regs 3 -> GR regs4 4 = GR regs 4 -> GR regs4 8 = GR regs 2 ->
  GR regs4 9 = Z_to_bv 64 SP1 -> GR regs4 10 = Z_to_bv 64 (crw_want len bs slot) -> GR regs4 21 = Z_to_bv 64 slot ->
  GR regs4 23 = Z_to_bv 64 ASAN_K -> GR regs4 26 = Z_to_bv 64 (crw_W len) ->
  GR regs4 27 = Z_to_bv 64 (crw_want len bs slot) ->
  crw_saves m4 ->
  (exists J0 J1 J2 J3, rw_cells rsegs m4 SP1 (crw_slots (frame_addr lyc 1 pos) pin J0 J1 J2 J3)) ->
  (exists Jh, rw_cells rsegs m4 (frame_addr lyc 1 pos) [CB 8 Jh]) ->
  bytes_at rsegs m4 (frame_addr lyc 1 pos + 32) (crw_v len bs slot) ->
  bytes_at rsegs m4 (frame_addr lyc 1 pos + 120) (le8 (Z_to_bv 64 (flag_addr lyc 1 pos))) ->
  SRr segs W (@cfg_at fx segs CRW_RET1 regs4 m4 md4) POST.
Proof.
  intros S2 pos f2 regs4 m4 md4 Hfrs Eab Hnev Hset J4 R2 R3 R4 R8 R9 R10 R21 R23 R26 R27 SV
    (J0 & J1 & J2 & J3 & SL) (Jh & FRh) HV HFLb.
  pose proof crw_sp_rng as [Hsp1 Hsp2]. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hsp1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof crw_sp1_rng as [G1 G2].
  pose proof (crw_win _ _ _ _ J4) as Hpres4.
  pose proof (proj1 J4) as HAR4.
  pose proof (proj1 crw_JI0) as HAR0.
  assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (crw_frame_facts S2 pos m4 md4 J4 Hfrs) as (HF0 & HF64 & HFc & HFapp & HFb & HFsh & HFd & HSl & HSh).
  destruct (FFL lyc S2 W m4 md4 1 pos HAR4 Hin) as (Hfp & Hfo & (Hfapp' & Hfimg) & (Hf4 & _ & Hfc)).
  set (FR := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
  pose proof Hlen as Hlen'. unfold W_RECV_MAX in Hlen'.
  pose proof Hslot as Hslot'. unfold INT_MIN, INT_MAX in Hslot'.
  assert (HFLF : FL + 1 <= FR \/ FR + 128 <= FL).
  { destruct (Z_lt_le_dec FL FR) as [L|L]; [left; lia|].
    destruct (Z_lt_le_dec FL (FR + 128)) as [L'|L']; [|right; lia].
    exfalso. exact (proj1 (proj2 (HFb FL ltac:(lia))) Hfo). }
  assert (HFLS : FL + 1 <= crw_sh FR \/ crw_sh FR + 16 <= FL).
  { destruct (Z_lt_le_dec FL (crw_sh FR)) as [L|L]; [left; lia|].
    destruct (Z_lt_le_dec FL (crw_sh FR + 16)) as [L'|L']; [|right; lia].
    exfalso. replace FL with (crw_sh FR + (FL - crw_sh FR)) in Hfo by lia.
    exact (proj1 (proj2 (HFsh (FL - crw_sh FR) ltac:(lia))) Hfo). }
  destruct (crw_present_rw W m4 (crw_sh FR) 16 ltac:(unfold crw_sh, ASAN_K in *; lia) ltac:(lia)) as (Js & CH).
  { intros a Ha. replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj1 (HFsh (a - crw_sh FR) ltac:(lia))). }
  destruct (crw_present_rw W m4 FL 1 ltac:(lia) ltac:(lia)) as (Jf & CFL).
  { intros a Ha. assert (a = FL) by lia. subst a. exact Hfp. }
  assert (E2 : GR regs 2 = Z_to_bv 64 (spZ regs)) by (unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  eapply (@crw_run fx W regs4 m4 md4 CRW_RET1).
  { unfold LCK.ms_of_regs. rewrite R2, R8, E2, R9, R10, R21, R23, R26, R27.
    eapply (SEGC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 bs (spZ regs) FR FL pin len slot
              J0 J1 J2 J3 Jh Js Jf).
    - exact Hal.
    - lia.
    - exact HF0.
    - exact HF64.
    - lia.
    - lia.
    - exact HFd.
    - lia.
    - lia.
    - exact HFLF.
    - exact HFLS.
    - lia.
    - lia.
    - exact SV.
    - exact SL.
    - exact FRh.
    - exact HV.
    - exact HFLb.
    - exact CH.
    - exact CFL.
    - apply (wcc_leafb_rng_vis W m4); [lia | lia |]. intros a Ha. apply Hpres4.
      unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - apply (wcc_leafb_rng_vis W m4); [lia | lia |]. intros a Ha. apply Hpres4.
      unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - apply (wcc_leafb_rng_vis W m4); [lia | lia |]. intros a Ha. exact (proj1 (HFb a ltac:(lia))).
    - apply (wcc_leafb_rng_vis W m4); [unfold crw_sh, ASAN_K in *; lia | lia |]. intros a Ha.
      replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj1 (HFsh (a - crw_sh FR) ltac:(lia))).
    - apply (wcc_leafb_rng_vis W m4); [lia | lia |]. intros a Ha. assert (a = FL) by lia. subst a. exact Hfp.
    - intros HW1.
      assert (H50 : 50 <= len).
      { unfold crw_want, PSR.rp_slot_read_model, PSW.rp_slot_width_model in HW1.
        destruct (len <? 50) eqn:E; [cbn in HW1; discriminate|]. apply Z.ltb_ge in E. lia. }
      destruct (crw_block_facts _ _ _ _ J4 Eab ltac:(lia)) as (bA & nA & _ & B1 & B2 & B3 & B4 & _ & BB & BA & BR & BRS).
      split; [exact Hbs|]. split; [exact BB|]. split; [exact BA|]. split; [lia|]. split; [lia|].
      split; [exact BR | exact BRS]. }
  intros ms' md' (ms0 & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 &
    -> & MU & WM & HFL0) & EQV) SBM.
  destruct (crw_regs_of EQV) as (G1' & G2' & G3' & G4' & G8' & G9' & _ & _ & _ & _ & G18' & G19' & G20' & G21' & G22' &
    G23' & G24' & G25' & G26' & G27').
  assert (HW5 : forall a, ~ outside [(SP1, SP1 + 88); (FR, FR + 8); (crw_sh FR, crw_sh FR + 16)] a ->
            0 <= a < 2 ^ 64 -> ~ in_img segs a /\
            awr_byte CRD_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(1, pos)] a).
  { intros a Ha Hr. cbn [outside] in Ha.
    assert (Hc : (SP1 <= a < SP1 + 88) \/ (FR <= a < FR + 8) \/ (crw_sh FR <= a < crw_sh FR + 16)) by
      (destruct (Z_lt_le_dec a SP1); destruct (Z_lt_le_dec a (SP1 + 88)); destruct (Z_lt_le_dec a FR);
       destruct (Z_lt_le_dec a (FR + 8)); destruct (Z_lt_le_dec a (crw_sh FR));
       destruct (Z_lt_le_dec a (crw_sh FR + 16)); first [ left; lia | right; left; lia | right; right; lia
             | exfalso; apply Ha; split; [lia|]; split; [lia|]; split; [lia | exact I] ]).
    destruct Hc as [Hc | [Hc | Hc]].
    - split.
      + intros Him. pose proof (WirePImg.wire_segs_low a Him). unfold kLowMemEnd in *. lia.
      + left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - split; [exact (proj2 (proj2 (HFb a ltac:(lia))))|].
      right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. fold FR. lia.
    - split.
      + replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj2 (proj2 (HFsh (a - crw_sh FR) ltac:(lia)))).
      + right; right; right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. fold FR. unfold crw_sh, shadow_addr, SHADOW_OFF, ASAN_K in *. lia. }
  pose proof (crw_release B LAWS ASF FFL CRD_STK (spZ regs) [] lyc Sc W memc mdc lyc S2 W m4 md4 0 pos m5 md'
                [(SP1, SP1 + 88); (FR, FR + 8); (crw_sh FR, crw_sh FR + 16)] J4 MU WM HW5 HFL0 SBM) as J5.
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV.
  rewrite (crw_ms_shape _ _ _ _ EQV).
  apply SRr_ret. unfold wire_crd_post.
  exists lyc, (stack_free_state 1 pos S2), (ms_regs ms'), m5, md'.
  split; [reflexivity|].
  split.
  { change own with ([] ++ own). change (k + CRD_EV) with (k + 0).
    exact (ajournal_sub segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             CRD_STK (spZ regs) [] [] lyc (stack_free_state 1 pos S2) W m5 md' 0 HJ J5 Hwlo Hwhi
             ltac:(intros a (r0 & Hr0 & _); destruct Hr0)). }
  split.
  { intros i Hi. unfold LCK.acallee_saved, acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2'|]. exact (eq_sym E2).
    - etransitivity; [exact G3'|]. exact R3.
    - etransitivity; [exact G4'|]. exact R4.
    - exact G8'.
    - exact G9'.
    - exact G18'.
    - exact G19'.
    - exact G20'.
    - exact G21'.
    - exact G22'.
    - exact G23'.
    - exact G24'.
    - exact G25'.
    - exact G26'.
    - exact G27'. }
  split; [exact (crw_sf_frames 1 pos S2 (frames Sc) Hfrs)|].
  split.
  { unfold ablocks at 1. rewrite blocks_stack_free_state. fold (ablocks B lyc S2). rewrite Eab. apply Permutation_refl. }
  split.
  { apply (acall_kept_of_journal segs B WirePImg.wire_segs_low CRD_STK (spZ regs) [] [] lyc Sc W memc mdc lyc
             (stack_free_state 1 pos S2) W m5 md' 0 (fun _ => False) J5 HAR0).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B lyc S2). rewrite Eab. exact Hb.
    - exact sink_closed_nil. }
  assert (Hmo : mo_le MT Sc S2 0) by (rewrite Hset; apply (mo_le_set_fs_r MT MTF); exact (mo_le_refl MT MTL Sc)).
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact Hmo.
Qed.

(* At the call of rp_slot_read (+0x1c8): the leaf by the statement's premise, then segment C. *)
Lemma crw_leaf_call : forall S2 pos f2 regs3 m3 md3,
  frames S2 = (1, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc -> st_nev S2 = st_nev Sc ->
  S2 = set_fs f2 Sc ->
  JI [(1, pos)] S2 m3 md3 ->
  GR regs3 1 = Z_to_bv 64 CRW_RET1 -> GR regs3 2 = Z_to_bv 64 SP1 -> GR regs3 3 = GR regs 3 ->
  GR regs3 4 = GR regs 4 -> GR regs3 8 = GR regs 2 -> GR regs3 9 = Z_to_bv 64 SP1 ->
  GR regs3 10 = Z_to_bv 64 pin -> GR regs3 11 = Z_to_bv 64 len -> GR regs3 12 = Z_to_bv 64 slot ->
  GR regs3 13 = Z_to_bv 64 (frame_addr lyc 1 pos + 32) -> GR regs3 21 = Z_to_bv 64 slot ->
  GR regs3 23 = Z_to_bv 64 ASAN_K -> GR regs3 26 = Z_to_bv 64 (crw_W len) ->
  GR regs3 27 = Z_to_bv 64 (crw_want len bs slot) ->
  crw_saves m3 ->
  (exists J0 J1 J2 J3, rw_cells rsegs m3 SP1 (crw_slots (frame_addr lyc 1 pos) pin J0 J1 J2 J3)) ->
  (exists Jx, rw_cells rsegs m3 (frame_addr lyc 1 pos)
     [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 CRW_DESC); C8 (Z_to_bv 64 CRW_ENTRY); CB 8 Jx; CB 48 crw_fill]) ->
  rw_cells rsegs m3 (crw_sh (frame_addr lyc 1 pos)) [CB 16 crw_shadow_bytes] ->
  bytes_at rsegs m3 (frame_addr lyc 1 pos + 120) (le8 (Z_to_bv 64 (flag_addr lyc 1 pos))) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 CRW_RSR) m3 (YK11.seg_rom segs)) md3) POST.
Proof.
  intros S2 pos f2 regs3 m3 md3 Hfrs Eab Hnev Hset J3 R1 R2 R3 R4 R8 R9 R10 R11 R12 R13 R21 R23 R26 R27 SV
    (J0 & J1 & J2 & J3' & SL) (Jx & FRC) SHC HFLb.
  pose proof crw_sp_rng as [Hsp1 Hsp2]. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hsp1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof crw_sp1_rng as [G1 G2].
  pose proof (crw_win _ _ _ _ J3) as Hpres3.
  pose proof (proj1 J3) as HAR3.
  assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (crw_frame_facts S2 pos m3 md3 J3 Hfrs) as (HF0 & HF64 & HFc & HFapp & HFb & HFsh & HFd & HSl & HSh).
  set (FR := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
  pose proof Hlen as Hlen'. unfold W_RECV_MAX in Hlen'.
  pose proof Hslot as Hslot'. unfold INT_MIN, INT_MAX in Hslot'.
  assert (U11 : bv_unsigned (GR regs3 11) = len) by (rewrite R11; apply crw_u64; lia).
  assert (U12 : bv_signed (GR regs3 12) = slot) by (rewrite R12; apply crw_signed_small; lia).
  assert (U13 : bv_unsigned (GR regs3 13) = FR + 32) by (rewrite R13; apply crw_u64; lia).
  assert (USP : spZ regs3 = SP1) by (change (spZ regs3) with (bv_unsigned (GR regs3 2)); rewrite R2; apply crw_u64; lia).
  set (wd := PSW.rp_slot_width_model len bs slot).
  assert (HWR : forall x, LCK.in_wr (LSR.wire_rsr_wr (0 <=? wd) (FR + 32)) x -> FR + 32 <= x < FR + 80).
  { intros x Hx. unfold LSR.wire_rsr_wr, LCK.in_wr in Hx. destruct (0 <=? wd).
    - apply Exists_cons in Hx. destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx; unfold RSRF.RP_SLOT_READ_VLEN in Hx; lia|].
      apply Exists_nil in Hx. destruct Hx.
    - apply Exists_nil in Hx. destruct Hx. }
  eapply SRr_bind.
  { apply (wcc_leafb_journal B LAWS W regs3 m3 CRD_STK (spZ regs) [] lyc Sc W memc mdc [(1, pos)] lyc S2 md3 0
             (SP1 - spZ regs) RSRF.RP_SLOT_READ
             (Some (PSR.rp_slot_read_model (bv_unsigned (GR regs3 11)) bs (bv_signed (GR regs3 12))))
             (LSR.wire_rsr_wr (0 <=? PSW.rp_slot_width_model (bv_unsigned (GR regs3 11)) bs (bv_signed (GR regs3 12)))
                (bv_unsigned (GR regs3 13)))
             (fun m2 => 0 <= PSW.rp_slot_width_model (bv_unsigned (GR regs3 11)) bs (bv_signed (GR regs3 12)) ->
                bytes_at rsegs m2 (bv_unsigned (GR regs3 13))
                  (PSR.rp_slot_bytes bs (PSW.rp_slot_width_model (bv_unsigned (GR regs3 11)) bs (bv_signed (GR regs3 12)))
                     (bv_signed (GR regs3 12)))) J3).
    - rewrite USP. lia.
    - clear - G2 Hal. Z.div_mod_to_equations. lia.
    - lia.
    - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - change (YK0s.ret_ok (GR regs3 1)). rewrite R1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - etransitivity; [exact R3 | exact Hgp].
    - etransitivity; [exact R4 | exact Htp].
    - rewrite U11, U12, U13. fold wd. intros a Ha. apply HWR in Ha.
      right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. fold FR. lia.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_wr_at, LSR.wire_rp_slot_read_cg in LF.
      specialize (LF lyc S2 W regs3 m3 md3 bs (spZ regs - CRD_STK) HPRE). cbv zeta in LF.
      assert (ESP : bv_unsigned (YK11.getr regs3 (Z_to_bv 5 2)) = SP1) by exact USP.
      pose proof HAR3 as [HM _].
      assert (HKc : Forall (cell_holds B lyc (aview segs (w_H W) m3)) (as_const B lyc)) by (eapply am_const; exact HM).
      assert (VIS : forall a0 n, wire_seg_covers a0 n = true -> a0 + n <= 2 ^ 64 ->
                forall a, a0 <= a < a0 + n -> w_H W (Z_to_bv 64 a) = false).
      { intros a0 n Hc Ht a Ha. replace a with (a0 + (a - a0)) by lia.
        apply (wcc_leafb_covers_visible (w_H W) a0 n (a - a0) (w_Hoff W) Hc); lia. }
      assert (HSHB : forall i, 0 <= i < 48 ->
                exists b, mrd rsegs m3 (wa (AsanCells.shadow_addr (FR + 32 + i))) = Some b /\ bv_signed b = 0).
      { intros i Hi. destruct SHC as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
        destruct HB as (_ & _ & HB).
        assert (Ej : AsanCells.shadow_addr (FR + 32 + i) = crw_sh FR + Z.of_nat (Z.to_nat (4 + i / 8))).
        { rewrite Z2Nat.id by (pose proof (Z.div_pos i 8); lia). unfold AsanCells.shadow_addr, crw_sh.
          assert (FR mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
          clear - H Hi. Z.div_mod_to_equations. lia. }
        rewrite Ej. assert (Hk : (Z.to_nat (4 + i / 8) < length crw_shadow_bytes)%nat)
          by (unfold crw_shadow_bytes; cbn [length map]; assert (0 <= i / 8 <= 5) by (Z.div_mod_to_equations; lia); lia).
        rewrite (HB _ Hk).
        assert (E8 : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3 \/ i / 8 = 4 \/ i / 8 = 5)
          by (Z.div_mod_to_equations; lia).
        destruct E8 as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; eexists; split; reflexivity. }
      apply LF; clear LF.
      + apply (crw_rom_bytes W m3 RCL.A_M RCL.KM crw_rom_chk_M); [unfold RCL.A_M; lia | unfold RCL.A_M; lia |].
        intros i Hi. apply (crw_rom_at _ _ m3 md3 J3).
        unfold wire_in_ro_rd, WIRE_RO_RD. apply Exists_cons_hd. unfold in_zr, RCL.A_M. cbn [fst snd]. lia.
      + apply (crw_rom_bytes W m3 RCL.A_T RCL.KT crw_rom_chk_T); [unfold RCL.A_T; lia | unfold RCL.A_T; lia |].
        intros i Hi. apply (crw_rom_at _ _ m3 md3 J3).
        unfold wire_in_ro_rd, WIRE_RO_RD. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr, RCL.A_T.
        cbn [fst snd]. lia.
      + change RFC.A_K36 with WIRE_RO_FCH. change (Z_to_bv 64 RFC.K36) with (wa WIRE_RO_FCH_VAL).
        apply (wcc_leafb_z8 B lyc (w_H W) m3 WIRE_RO_FCH WIRE_RO_FCH_VAL (w_Hoff W) HKc);
          [wcc_leafb_row HCELLS lyc | vm_compute; reflexivity | unfold WIRE_RO_FCH; lia].
      + rewrite ESP. eapply (wcc_leafb_stk_journal B); [exact J3 | lia | lia].
      + rewrite ESP. unfold RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK,
          RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME, CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
      + rewrite ESP. apply wcc_leafb_app_stack. unfold RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME,
          RSWF.RP_SLOT_WIDTH_STK, RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME. lia.
      + rewrite ESP. apply wcc_leafb_app_stack. lia.
      + exact (wcc_leafb_asan_cells B HCELLS lyc S2 W m3 md3 HAR3).
      + unfold AKA.off_stk, RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK,
          RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME. rewrite ESP. left.
        unfold MIDEND, GOT_CELL_K. lia.
      + rewrite U11. intros H50. unfold RSRF.RP_AUDIO_OFF in H50.
        destruct (crw_block_facts _ _ _ _ J3 Eab ltac:(lia)) as (bA & nA & Hb & B1 & B2 & B3 & B4 & B5 & BB & BA & _).
        rewrite R10, crw_u64 by lia. rewrite Hbs.
        split; [lia|]. split; [exact BB|].
        split; [unfold AKA.off_stk, RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK,
                  RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME; rewrite ESP; left; lia|].
        split; [exact BA | lia].
      + rewrite U11, U12, U13. fold wd. intros Hw.
        assert (H50 : 50 <= len).
        { unfold wd, PSW.rp_slot_width_model in Hw. destruct (len <? 50) eqn:E; [cbn in Hw; lia|]. apply Z.ltb_ge in E. lia. }
        destruct (crw_block_facts _ _ _ _ J3 Eab ltac:(lia)) as (bA & nA & Hb & B1 & B2 & B3 & B4 & B5 & BB & BA & _).
        pose proof (sep_block_frame segs B LAWS lyc S2 W m3 md3 bA nA 1 pos HAR3 Hb Hin) as HDJ.
        change (fs_frame_bytes 1) with 128 in HDJ. fold FR in HDJ. unfold zdisjoint in HDJ. cbn [fst snd] in HDJ.
        rewrite R10, crw_u64 by lia. rewrite Hbs. unfold RSRF.RP_SLOT_READ_VLEN.
        split; [apply (wcc_leafb_wr_at W m3); [lia | lia | intros i Hi; exact (proj1 (HFb (FR + 32 + i) ltac:(lia)))]|].
        split; [unfold AKA.off_stk, RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK,
                  RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME; rewrite ESP; left; lia|].
        split; [lia|].
        split; [lia|]. split; [lia|]. split; [unfold AsanCells.APPMEM_END; lia|].
        intros i Hi. split.
        * replace (FR + 32 + i) with (FR + (32 + i)) by lia. apply (wcc_leafb_app_of_in_app FR 128); [exact HFapp | lia].
        * destruct (HSHB i Hi) as (b & Hb' & Hs). exists b. split; [exact Hb'|]. left. exact Hs.
      + rewrite U11, U12, U13. fold wd. intros Hw.
        assert (H50 : 50 <= len).
        { unfold wd, PSW.rp_slot_width_model in Hw. destruct (len <? 50) eqn:E; [cbn in Hw; lia|]. apply Z.ltb_ge in E. lia. }
        destruct (crw_block_facts _ _ _ _ J3 Eab ltac:(lia)) as (bA & nA & Hb & B1 & B2 & B3 & B4 & B5 & _).
        rewrite R10, crw_u64 by lia. unfold RSRF.RP_AUDIO_OFF.
        split; [lia|]. split; [lia|]. clear - HF64. Z.div_mod_to_equations. lia.
      + rewrite ESP. eapply (wcc_leafb_rng_journal B); [exact J3 | unfold RSRF.RP_SLOT_READ_STK,
          RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK, RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME,
          CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia | lia].
      + exact (proj1 (wcc_leafb_rng_cells W)).
      + exact (proj2 (wcc_leafb_rng_cells W)).
      + unfold RSWF.WIRE_RFC_CONSTS. repeat apply Forall_cons; try apply Forall_nil;
          unfold AKA.off_stk, RSRF.RP_SLOT_READ_STK, RSRF.RP_SLOT_READ_FRAME, RSWF.RP_SLOT_WIDTH_STK,
          RSWF.RP_SLOT_WIDTH_FRAME, RFC.RP_FRAME_CHANNELS_FRAME; cbn [fst snd]; rewrite ESP; left;
          unfold RCL.A_M, RCL.A_T, RFC.A_K36; lia.
      + unfold RSWF.WIRE_RFC_CONSTS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        * apply (wcc_leafb_rng W); [unfold RCL.A_M; lia | unfold RCL.A_M; lia |].
          apply (VIS RCL.A_M 8); [vm_compute; reflexivity | unfold RCL.A_M; lia].
        * apply (wcc_leafb_rng W); [unfold RFC.A_K36; lia | unfold RFC.A_K36; lia |].
          apply (VIS RFC.A_K36 8); [vm_compute; reflexivity | unfold RFC.A_K36; lia].
        * apply (wcc_leafb_rng W); [unfold RCL.A_T; lia | unfold RCL.A_T; lia |].
          apply (VIS RCL.A_T 8); [vm_compute; reflexivity | unfold RCL.A_T; lia].
      + rewrite U11. intros H50. unfold RSRF.RP_AUDIO_OFF in H50.
        destruct (crw_block_facts _ _ _ _ J3 Eab ltac:(lia)) as (bA & nA & _ & B1 & B2 & B3 & B4 & _ & _ & _ & BR & BRS).
        rewrite R10, crw_u64 by lia. rewrite Hbs. split; [exact BR | exact BRS].
      + rewrite U11, U12, U13. fold wd. intros _. unfold RSRF.RP_SLOT_READ_VLEN.
        split.
        * apply (wcc_leafb_rng_vis W m3); [lia | lia |]. intros a Ha. exact (proj1 (HFb a ltac:(lia))).
        * assert (Es : forall i, 0 <= i < 48 -> AsanCells.shadow_addr (FR + 32 + i) = crw_sh FR + 4 + i / 8).
          { intros i Hi. unfold AsanCells.shadow_addr, crw_sh.
            assert (FR mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
            clear - H Hi. Z.div_mod_to_equations. lia. }
          pose proof (Es 0 ltac:(lia)) as Es0. pose proof (Es 47 ltac:(lia)) as Es47.
          rewrite Z.add_0_r in Es0. replace (FR + 32 + 48 - 1) with (FR + 32 + 47) by lia.
          rewrite Es0, Es47. change (47 / 8) with 5. change (0 / 8) with 0.
          apply (wcc_leafb_rng_vis W m3); [unfold crw_sh, ASAN_K in *; lia | lia |]. intros a Ha.
          replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj1 (HFsh (a - crw_sh FR) ltac:(lia))).
      + rewrite U11, U12, U13. fold wd. intros x Hx. apply HWR in Hx.
        destruct (HFb x ltac:(lia)) as (_ & HO & HI). split; [exact HO | exact HI]. }
  cbv beta. intros W' c' _ (-> & regs4 & m4 & md4 & -> & J4 & HP & HRES & HEFF & HGR & HX).
  rewrite U11, U12, U13 in *. fold wd in HX, HEFF.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
    replace pc with (w64 CRW_RET1) by exact (eq_sym R1) end.
  change (mkCfg (@YK11.mkst fx regs4 (w64 CRW_RET1) m4 (YK11.seg_rom segs)) md4)
    with (@cfg_at fx segs CRW_RET1 regs4 m4 md4).
  assert (KP : forall i, LCK.acallee_saved i -> GR regs4 i = GR regs3 i) by (intros i Hi; exact (HP i Hi)).
  (* a region of the state at the call that the leaf neither writes nor uses as stack is kept *)
  assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (SP1 - 4096 <= a < SP1) -> ~ (FR + 32 <= a < FR + 80) ->
            apresent (w_H W) m3 a -> apresent (w_H W) m4 a /\ aview segs (w_H W) m4 a = aview segs (w_H W) m3 a).
  { intros a Ha Hs Hv Hp. split; [exact (HGR a Hp)|]. apply HEFF; [exact Ha | rewrite USP; exact Hs |].
    intros Hx. apply HWR in Hx. lia. }
  apply (crw_at_ret1 S2 pos f2 regs4 m4 md4 Hfrs Eab Hnev Hset J4).
  - rewrite (KP 2 ltac:(unfold LCK.acallee_saved; lia)). exact R2.
  - rewrite (KP 3 ltac:(unfold LCK.acallee_saved; lia)). exact R3.
  - rewrite (KP 4 ltac:(unfold LCK.acallee_saved; lia)). exact R4.
  - rewrite (KP 8 ltac:(unfold LCK.acallee_saved; lia)). exact R8.
  - rewrite (KP 9 ltac:(unfold LCK.acallee_saved; lia)). exact R9.
  - exact (HRES _ eq_refl).
  - rewrite (KP 21 ltac:(unfold LCK.acallee_saved; lia)). exact R21.
  - rewrite (KP 23 ltac:(unfold LCK.acallee_saved; lia)). exact R23.
  - rewrite (KP 26 ltac:(unfold LCK.acallee_saved; lia)). exact R26.
  - rewrite (KP 27 ltac:(unfold LCK.acallee_saved; lia)). exact R27.
  - unfold crw_saves in *. apply (crw_rw_cells_kept (w_H W) m3 m4 _ _ SV).
    intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha.
    assert (P : apresent (w_H W) m3 a) by (apply Hpres3; unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia).
    destruct (KEPT a ltac:(lia) ltac:(lia) ltac:(lia) P) as [P' E]. exact (conj P (conj P' E)).
  - exists J0, J1, J2, J3'. apply (crw_rw_cells_kept (w_H W) m3 m4 _ _ SL).
    intros a Ha. unfold crw_slots in Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha.
    assert (P : apresent (w_H W) m3 a) by (apply Hpres3; unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia).
    destruct (KEPT a ltac:(lia) ltac:(lia) ltac:(lia) P) as [P' E]. exact (conj P (conj P' E)).
  - apply (proj1 (crw_rw_cells_app _ _ [_] _)) in FRC. destruct FRC as [FRC _].
    destruct (rw_cells_forget rsegs m3 FR _ FRC) as (Jh & FRh). cbn [cells_size csize] in FRh.
    exists Jh. apply (crw_rw_cells_kept (w_H W) m3 m4 _ _ FRh).
    intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha.
    assert (P : apresent (w_H W) m3 a) by exact (proj1 (HFb a ltac:(lia))).
    destruct (KEPT a ltac:(lia) ltac:(lia) ltac:(lia) P) as [P' E]. exact (conj P (conj P' E)).
  - unfold crw_v. destruct (Z.leb_spec 0 wd) as [Hw|Hw].
    + assert (HW1 : crw_want len bs slot = 1)
        by (unfold crw_want, PSR.rp_slot_read_model; fold wd; rewrite (proj2 (Z.ltb_ge _ _) Hw); reflexivity).
      rewrite HW1. cbn [Z.eqb Pos.eqb].
      destruct (PCR.width_facts len bs slot ltac:(lia) Hw) as (_ & _ & _ & _ & EW).
      unfold crw_W. fold wd. rewrite <- EW. exact (HX Hw).
    + assert (HW0 : crw_want len bs slot = 0)
        by (unfold crw_want, PSR.rp_slot_read_model; fold wd; rewrite (proj2 (Z.ltb_lt _ _) Hw); reflexivity).
      rewrite HW0. cbn [Z.eqb].
      apply (proj1 (crw_rw_cells_app _ _ [_; _; _; _] _)) in FRC. destruct FRC as [_ FRv].
      cbn [cells_size csize Nat.add Z.of_nat] in FRv.
      destruct FRv as [[_ FRv] _]. cbn [cells_bytes cbytes app] in FRv. rewrite app_nil_r in FRv.
      apply (crw_bytes_at_kept (w_H W) m3 m4 _ _ FRv).
      intros a Ha. unfold crw_fill in Ha. rewrite repeat_length in Ha. cbn [Z.of_nat Pos.of_succ_nat] in Ha.
      assert (P : apresent (w_H W) m3 a) by exact (proj1 (HFb a ltac:(lia))).
      split; [exact P|].
      split; [exact (HGR a P)|].
      apply HEFF; [lia | rewrite USP; try unfold LCK.ESTACK; try unfold YG0d.ESTACK; lia |].
      intros Hx. unfold LSR.wire_rsr_wr, LCK.in_wr in Hx. apply Exists_nil in Hx. exact Hx.
  - apply (crw_bytes_at_kept (w_H W) m3 m4 _ _ HFLb).
    intros a Ha. rewrite length_le8 in Ha. cbn [Z.of_nat Pos.of_succ_nat] in Ha.
    assert (P : apresent (w_H W) m3 a) by exact (proj1 (HFb a ltac:(lia))).
    destruct (KEPT a ltac:(lia) ltac:(lia) ltac:(lia) P) as [P' E]. exact (conj P (conj P' E)).
Qed.

(* A word of the view, as the raw bytes of its value. *)
Lemma crw_bytes_of_rdword : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) m) a = Some v -> bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H0 H1 Hv Hr.
  pose proof (val_mem_of_rdword segs (w_H W) m a v Hr) as HV.
  pose proof (wcc_leafb_bytes_le W m a 8 v v HV eq_refl H0 H1) as HB.
  unfold le8, word_to_le_bytes. rewrite crw_u64 by lia. exact HB.
Qed.

(* After the stack malloc: segment B, its writes in the journal, and the leaf call. *)
Lemma crw_at_ret0 : forall S2 pos f2 regs2 m2 md2,
  frames S2 = (1, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc -> st_nev S2 = st_nev Sc ->
  S2 = set_fs f2 Sc ->
  JI [(1, pos)] S2 m2 md2 ->
  GR regs2 2 = Z_to_bv 64 SP1 -> GR regs2 3 = GR regs 3 -> GR regs2 4 = GR regs 4 ->
  GR regs2 8 = GR regs 2 -> GR regs2 9 = Z_to_bv 64 SP1 -> GR regs2 10 = Z_to_bv 64 (frame_addr lyc 1 pos) ->
  GR regs2 18 = GR regs 11 -> GR regs2 19 = GR regs 10 -> GR regs2 21 = GR regs 12 ->
  GR regs2 23 = Z_to_bv 64 ASAN_K ->
  crw_saves m2 ->
  rdword (aview segs (w_H W) m2) (frame_addr lyc 1 pos + 120) = Some (flag_addr lyc 1 pos) ->
  SRr segs W (@cfg_at fx segs CRW_RET0 regs2 m2 md2) POST.
Proof.
  intros S2 pos f2 regs2 m2 md2 Hfrs Eab Hnev Hset J2 R2 R3 R4 R8 R9 R10 R18 R19 R21 R23 SV HFLr.
  pose proof crw_sp_rng as [Hsp1 Hsp2]. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hsp1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof crw_sp1_rng as [G1 G2].
  pose proof (crw_win _ _ _ _ J2) as Hpres2.
  pose proof (proj1 J2) as HAR2.
  assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (crw_frame_facts S2 pos m2 md2 J2 Hfrs) as (HF0 & HF64 & HFc & HFapp & HFb & HFsh & HFd & HSl & HSh).
  destruct (FFL lyc S2 W m2 md2 1 pos HAR2 Hin) as (_ & _ & _ & (HFL4 & _ & HFLc)).
  set (FR := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
  pose proof Hlen as Hlen'. unfold W_RECV_MAX in Hlen'.
  pose proof Hslot as Hslot'. unfold INT_MIN, INT_MAX in Hslot'.
  (* the regions segment B writes, as junk cells of the state it starts from *)
  destruct (crw_present_rw W m2 SP1 88 ltac:(lia) ltac:(lia)) as (Js & CS).
  { intros a Ha. apply Hpres2. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia. }
  destruct (crw_present_rw W m2 FR 80 ltac:(lia) ltac:(lia)) as (Jf & CF).
  { intros a Ha. exact (proj1 (HFb a ltac:(lia))). }
  destruct (crw_present_rw W m2 (crw_sh FR) 16 ltac:(unfold crw_sh, ASAN_K in *; lia) ltac:(lia)) as (Jh & CH).
  { intros a Ha. replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj1 (HFsh (a - crw_sh FR) ltac:(lia))). }
  assert (H10' : GR regs 10 = Z_to_bv 64 pin) by exact H10.
  assert (H11' : GR regs 11 = Z_to_bv 64 len) by exact H11.
  assert (H12' : GR regs 12 = Z_to_bv 64 slot) by exact H12.
  eapply (@crw_run fx W regs2 m2 md2 CRW_RET0).
  { unfold LCK.ms_of_regs. rewrite R2, R9, R10, R18, R19, R21, R23, H10', H11', H12'.
    eapply (SEGB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 bs SP1 FR pin len slot Js Jf Jh).
    - lia.
    - lia.
    - exact G2.
    - exact HF0.
    - exact HF64.
    - lia.
    - lia.
    - exact HFd.
    - lia.
    - lia.
    - exact CS.
    - exact CF.
    - exact CH.
    - apply (wcc_leafb_rng_vis W m2); [lia | lia |]. intros a Ha. apply Hpres2.
      unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - apply (wcc_leafb_rng_vis W m2); [lia | lia |]. intros a Ha. exact (proj1 (HFb a ltac:(lia))).
    - apply (wcc_leafb_rng_vis W m2); [unfold crw_sh, ASAN_K in *; lia | lia |]. intros a Ha.
      replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj1 (HFsh (a - crw_sh FR) ltac:(lia))).
    - intros H50.
      destruct (crw_block_facts _ _ _ _ J2 Eab ltac:(lia)) as (bA & nA & Hb & B1 & B2 & B3 & B4 & B5 & BB & BA & BR & BRS).
      pose proof (sep_block_frame segs B LAWS lyc S2 W m2 md2 bA nA 1 pos HAR2 Hb Hin) as HDJ.
      change (fs_frame_bytes 1) with 128 in HDJ. fold FR in HDJ. unfold zdisjoint in HDJ. cbn [fst snd] in HDJ.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in B5, HFapp.
      assert (HP8 : 0 <= pin / 8 /\ (pin + len - 1) / 8 <= 2 ^ 47 / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
      assert (HPm : pin / 8 <= (pin + len - 1) / 8) by (apply Z.div_le_mono; lia).
      assert (HFR8 : FR mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
      split; [exact Hbs|]. split; [exact BB|]. split; [exact BA|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold crw_sh, ASAN_K in *; lia|].
      split; [unfold AsanCells.shadow_addr, ASAN_K; lia|].
      split; [unfold AsanCells.shadow_addr, ASAN_K; lia|].
      split.
      { unfold AsanCells.shadow_addr, crw_sh, ASAN_K.
        destruct HDJ as [HDJ|HDJ]; [left | right].
        - assert ((pin + len - 1) / 8 < FR / 8); [|lia].
          apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod FR 8 ltac:(lia)). lia.
        - assert (FR / 8 + 16 <= pin / 8); [|lia].
          apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod FR 8 ltac:(lia)). lia. }
      split; [exact BR | exact BRS]. }
  intros ms' md' (ms0 & (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & J0 & J1 & J2' & J3 &
    Jx & -> & MU & WM & SL & FRC & SHC) & EQV) SBM.
  destruct (crw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E13 & _ & _ & _ & E21 & _ & E23 &
    _ & _ & E26 & E27).
  rewrite (crw_ms_shape _ _ _ _ EQV).
  assert (HW3 : forall a, ~ outside [(SP1, SP1 + 88); (FR, FR + 80); (crw_sh FR, crw_sh FR + 16)] a ->
            0 <= a < 2 ^ 64 -> ~ in_img segs a /\
            awr_byte CRD_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B lyc S2) lyc [(1, pos)] a).
  { intros a Ha Hr. cbn [outside] in Ha.
    assert (Hc : (SP1 <= a < SP1 + 88) \/ (FR <= a < FR + 80) \/ (crw_sh FR <= a < crw_sh FR + 16)) by
      (destruct (Z_lt_le_dec a SP1); destruct (Z_lt_le_dec a (SP1 + 88)); destruct (Z_lt_le_dec a FR);
       destruct (Z_lt_le_dec a (FR + 80)); destruct (Z_lt_le_dec a (crw_sh FR));
       destruct (Z_lt_le_dec a (crw_sh FR + 16)); first [ left; lia | right; left; lia | right; right; lia
             | exfalso; apply Ha; split; [lia|]; split; [lia|]; split; [lia | exact I] ]).
    destruct Hc as [Hc | [Hc | Hc]].
    - split.
      + intros Him. pose proof (WirePImg.wire_segs_low a Him). unfold kLowMemEnd in *. lia.
      + left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - split; [exact (proj2 (proj2 (HFb a ltac:(lia))))|].
      right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. fold FR. lia.
    - split.
      + replace a with (crw_sh FR + (a - crw_sh FR)) by lia. exact (proj2 (proj2 (HFsh (a - crw_sh FR) ltac:(lia)))).
      + right; right; right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. fold FR. unfold crw_sh, shadow_addr, SHADOW_OFF, ASAN_K in *. lia. }
  pose proof (crw_aj_step B LAWS CRD_STK (spZ regs) [] lyc Sc W memc mdc [(1, pos)] lyc S2 W m2 md2 0 m3 md' _
                J2 MU WM HW3 SBM) as JJ3.
  apply (crw_leaf_call S2 pos f2 (ms_regs ms') m3 md' Hfrs Eab Hnev Hset JJ3).
  - exact E1.
  - exact E2.
  - etransitivity; [exact E3 | exact R3].
  - etransitivity; [exact E4 | exact R4].
  - etransitivity; [exact E8 | exact R8].
  - exact E9.
  - exact E10.
  - exact E11.
  - exact E12.
  - exact E13.
  - exact E21.
  - exact E23.
  - exact E26.
  - exact E27.
  - unfold crw_saves in *. apply (rw_cells_transport rsegs _ _ _ _ _ SV MU WM).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold crw_sh, ASAN_K in *. repeat split; lia.
  - exists J0, J1, J2', J3. exact SL.
  - exists Jx. exact FRC.
  - exact SHC.
  - apply (bytes_at_transport rsegs _ _ _ _ _ (crw_bytes_of_rdword m2 (FR + 120) FL ltac:(lia) ltac:(lia) ltac:(lia) HFLr) MU).
    rewrite length_le8. cbn [disjoint_from]. unfold crw_sh, ASAN_K in *. repeat split; lia.
Qed.

(* At the entry: segment A, the stack malloc, then crw_at_ret0. *)
Lemma crw_entry : SRr segs W (@cfg_at fx segs CRW_ENTRY regs memc mdc) POST.
Proof.
  pose proof crw_sp_rng as [Hsp1 Hsp2]. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in Hsp1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof crw_JI0 as JI0.
  pose proof (crw_win _ _ _ _ JI0) as Hpres0.
  pose proof crw_sp1_rng as [G1 G2].
  pose proof (proj1 JI0) as HAR0.
  pose proof (wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc HAR0) as HAC.
  destruct HAC as (CK & GCK & _ & _ & _ & UAR1 & GUAR & _).
  assert (RCELL : forall a n, In (a, n) wire_asan_cell_ranges -> a + n <= 2 ^ 64 ->
            ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) a n).
  { intros a n Hin Hlim. pose proof (wcc_leafb_seg_of a n Hin) as Hc.
    pose proof (wcc_leafb_covers_lo a n Hc) as H0.
    apply (wcc_leafb_rng W); [exact H0 | exact Hlim |]. intros x Hx. replace x with (a + (x - a)) by lia.
    apply (wcc_leafb_covers_visible (w_H W) a n (x - a) (w_Hoff W)); [exact Hc | lia | exact Hlim]. }
  eapply (@crw_run fx W regs memc mdc CRW_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply (crw_segA_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - CRD_STK)).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (wcc_leafb_stk W); [unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *; lia | lia | exact Hpres0].
    - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - exact Hal.
    - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *. lia.
    - exact GUAR.
    - exact UAR1.
    - exact GCK.
    - exact CK.
    - apply (wcc_leafb_rng_vis W memc); [unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *; lia | lia |].
      intros a Ha. apply Hpres0.
      unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - apply RCELL; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) | unfold WCells.GOT_UAR; lia].
    - apply RCELL; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) | unfold WCells.UAR; lia].
    - apply RCELL; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) | unfold WCells.GOT_CELL_K; lia].
    - apply RCELL; [unfold wire_asan_cell_ranges; cbn [In]; repeat (first [left; reflexivity | right]) | unfold WCells.CELL_K; lia]. }
  intros ms' md' (ms0 & (m1 & -> & MU & WM & SV) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, SV.
  destruct (crw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & _ & E18 & E19 & _ & E21 & _ & E23 & _).
  change (bv_unsigned (GR regs 2)) with (spZ regs) in E2, E9.
  rewrite (crw_ms_shape _ _ _ _ EQV).
  (* the inner journal after the thirteen saves *)
  assert (HJ1 : JI [] Sc m1 md').
  { apply (crw_aj_step B LAWS CRD_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
             [(spZ regs - 192, spZ regs)] JI0 MU WM); [|exact SBM].
    intros a Ha Hr. assert (Ha' : spZ regs - 192 <= a < spZ regs).
    { cbn [outside] in Ha. destruct (Z_lt_le_dec a (spZ regs - 192)); [exfalso; apply Ha; split; [lia | exact I]|].
      destruct (Z_lt_le_dec a (spZ regs)); [lia | exfalso; apply Ha; split; [lia | exact I]]. }
    split.
    - intros Him. pose proof (WirePImg.wire_segs_low a Him). unfold kLowMemEnd in *.
      unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *. lia.
    - left. unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia. }
  (* +0x74: the class-1 fake stack, at the pc the statement's premise names *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (wire_sigma WS___asan_stack_malloc_1)) mm rom) mdx) Q) end.
  rewrite <- HPCS.
  eapply SRr_bind.
  { eapply (crw_stack_malloc_at segs B LAWS WirePImg.wire_segs_low SMP CRD_CID ASM ltac:(unfold CRD_CID; lia)
      W (ms_regs ms') m1 CRD_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc (@nil (Z * Z)) lyc Sc md' 0
      (SP1 - spZ regs) (Z_to_bv 64 CRW_RET0) HJ1).
    - change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)). rewrite E2, crw_u64 by lia. lia.
    - clear - G2 Hal. Z.div_mod_to_equations. lia.
    - lia.
    - unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK. lia.
    - etransitivity; [exact E3 | exact Hgp].
    - etransitivity; [exact E4 | exact Htp].
    - exact E1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - exact Hcnt. }
  cbv beta.
  intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2 & (f2 & Hset2)
    & Hz & Hflag & Hfpres & HK1).
  change (fs_frame_bytes CRD_CID) with 128 in Hz, Hflag, Hfpres.
  change CRD_CID with 1 in *.
  assert (KP : forall i, LCK.acallee_saved i -> GR regs2 i = GR (ms_regs ms') i)
    by (intros i Hi; exact (HP2 i Hi)).
  change (Z_to_bv 64 CRW_RET0) with (w64 CRW_RET0).
  change (mkCfg (@YK11.mkst fx regs2 (w64 CRW_RET0) mem2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs CRW_RET0 regs2 mem2 md2).
  apply (crw_at_ret0 S2 pos f2 regs2 mem2 md2 Hfrs2 Eab2 Hnev2 Hset2 HJ2).
  - rewrite (KP 2 ltac:(unfold LCK.acallee_saved; lia)). exact E2.
  - rewrite (KP 3 ltac:(unfold LCK.acallee_saved; lia)). exact E3.
  - rewrite (KP 4 ltac:(unfold LCK.acallee_saved; lia)). exact E4.
  - rewrite (KP 8 ltac:(unfold LCK.acallee_saved; lia)). exact E8.
  - rewrite (KP 9 ltac:(unfold LCK.acallee_saved; lia)). exact E9.
  - exact Ha0.
  - rewrite (KP 18 ltac:(unfold LCK.acallee_saved; lia)). exact E18.
  - rewrite (KP 19 ltac:(unfold LCK.acallee_saved; lia)). exact E19.
  - rewrite (KP 21 ltac:(unfold LCK.acallee_saved; lia)). exact E21.
  - rewrite (KP 23 ltac:(unfold LCK.acallee_saved; lia)). exact E23.
  - unfold crw_saves. apply (crw_rw_cells_kept (w_H W) m1 mem2 _ _ SV).
    intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha.
    unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK in *.
    split; [apply (crw_win _ _ _ _ HJ1); unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia|].
    split; [apply (crw_win _ _ _ _ HJ2); unfold CRD_STK, CRD_FRAME, CRD_ALIGN, ESTACK; lia|].
    apply (proj1 HK1); [lia | lia].
  - replace (frame_addr lyc 1 pos + 120) with (frame_addr lyc 1 pos + 128 - 8) by lia. exact Hflag.
Qed.

End Entry.
End Walk.

(* The frozen statement. *)
Theorem wire_check_read_holds : forall fx rc B MT, @wire_check_read_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HPCS HCELLS HOWN HERR LAWS MTL MTF SMP ASF FFL ASM0 LEAF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pin len slot bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 Hal Hwlo Hwhi Hlen Hbs Hslot Hblk Hgarr Hcnt Hrom Hev.
  rewrite crw_entry_eq.
  eapply (crw_entry B MT HPCS HCELLS HOWN HERR LAWS MTL MTF SMP ASF FFL (ASM0 fx) LEAF crw_segB_F crw_segC_F);
    eassumption.
Qed.
