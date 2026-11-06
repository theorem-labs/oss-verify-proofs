(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* CanKit: four pieces the side-stack-frame walks of this unit use (diginet_body_check's among them).
   1. can_sm_path / can_sf_frames: the frame list and the untouched fields of the allocator state after
      `stack_malloc` and `stack_free_state`, by computation on lib/Reusable/YG00.v's own definitions.
   2. can_stack_malloc_at: a class-cid fake-stack call composed into the caller's journal, from the contract
      `astack_malloc_realizes` alone (no model_laws, no api_env).
   3. can_flag_store_pi: a run of the plain position-abstract engine that writes only bytes the journal allows plus
      the flag byte of its first owned frame, and leaves that byte 0, releases the frame.
   4. can_check4 and the small arithmetic the walk needs (the realigning `andi sp,sp,-0x20`, and the four-byte
      shadow check the program runs before each `lw`). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.

(* ------------------------------------------------------------------ *)
(* 1. The allocator state after a stack malloc and a stack free        *)
(* ------------------------------------------------------------------ *)

(* `stack_malloc cid s` asks the kernel nothing (lib/Reusable/YG00.v: it is get / put / ret only), so an apath with
   no answers computes its result. A PFake result means fs_probe found a free position, and the state it leaves is
   the entry state with the frame list extended. *)
Lemma can_sm_path : forall cid s pos s',
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
Lemma can_sf_frames : forall cid pos s rest,
  frames s = (cid, pos) :: rest -> frames (stack_free_state cid pos s) = rest.
Proof.
  intros cid pos s rest Hf.
  assert (E : frames (stack_free_state cid pos s) = del_pos (frames s) cid pos) by reflexivity.
  rewrite E, Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma can_sf_chunks : forall cid pos s,
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

(* lib/Reusable/YCbq.v call_effect_journal, for a call whose memory clause is the stack malloc's: it may change only
   owned bytes and its own stack window, never a heap block, and names no errno byte, so api_env is not needed. *)
Lemma can_sm_effect_journal : forall stk lyc Sc W regs memc mdc ly2 S2 W2 mem2 md2 nf k1,
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

Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation code := (as_code B).

(* lib/Reusable/YCbq.v aj_stack_malloc_at with can_sm_effect_journal for its journal step and can_sm_path for the
   frame list, so neither model_laws nor api_env is used. *)
Lemma can_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
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
destruct (can_sm_path cid Sc pos S2 Hpath) as (Hfrs2 & Hchk2 & Hsecs2 & Hnev2 & Hqt2 & Hqg2 & Hset2).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks, blocks; rewrite Hchk2; reflexivity).
assert (HJ1 : ajournal ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ apply (can_sm_effect_journal ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 [(cid, pos)] 0);
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

(* ------------------------------------------------------------------ *)
(* 3. The frame-flag store on the position-abstract engine             *)
(* ------------------------------------------------------------------ *)

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation SEGS := (@pa_segs _ transport_listing PI_transport).
#[local] Notation VAL := (@pa_val _ transport_listing PI_transport).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Definition can_plain_stop (st : prun_status tsym) : Prop :=
  match st with PRS_running | PRS_stopped _ => True | _ => False end.

Lemma can_flag_store_pi : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_runN_pi transport_tpi n ss = (ss', st) -> can_plain_stop st ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ms' mat',
     st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
unfold sym_runN_pi in Hrun.
destruct (sym_run_pi_sound tsym SEGS (clookup (@pa_tbl _ transport_listing PI_transport)) VAL
  (@pa_sigma _ transport_listing PI_transport) transport_listing (pa_fetch_ok (PI := PI_transport))
  (@pa_cert _ transport_listing PI_transport) (@pa_B_ok _ transport_listing PI_transport) A_LIM A_LIM_text
  (@pl_lim transport_listing PL_transport)
  _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HS'0 & _ & Hfr0).
assert (HS' : st_ok_pi SEGS VAL E ss' msr') by (destruct st; cbn [prun_post] in HS'0; first [exact HS'0 | destruct Hst]).
clear HS'0.
assert (Hfr : frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr'))
  by (first [exact Hfr0 | destruct ss; exact Hfr0]).
clear Hfr0.
pose proof (@pa_wx _ transport_listing PI_transport) as Hwx. pose proof (@pa_segs_low _ transport_listing PI_transport) as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc Sc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
apply (SRr_msteps SEGS Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows SEGS _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview SEGS (w_H W) memc' a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
assert (HAR' : AR SEGS B lyc (stack_free_state cid pos Sc) W memc'
  (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASF lyc Sc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
  - unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 msr' HS'). reflexivity.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_after_write SEGS B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms)
    mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) own' HJ Heqw
    ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + exact (can_sf_frames cid pos Sc (own' ++ frames S) Hfrs).
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
End fp.

(* ------------------------------------------------------------------ *)
(* 4. Arithmetic the walk needs                                        *)
(* ------------------------------------------------------------------ *)

(* `andi sp, sp, -0x20` on a symbolic sp (the donor's GrantACja.v land_m32 / denot_and_m32 / sp1_facts at 32). *)
Lemma can_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma can_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite can_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.

Lemma can_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv.
assert (Hq : 0 <= 32 * ((v + c) / 32) < 2 ^ 64).
{ split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite can_land_m32 by lia.
rewrite (zcanon_id (32 * ((v + c) / 32))) by (unfold M64; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma can_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

(* `srli s6, s7, 3` then `add s6, s6, s8`: the shadow address of the frame. *)
Lemma can_denot_shadow : forall E n m F SHB,
  ew E n = Z_to_bv 64 F -> ew E m = Z_to_bv 64 SHB ->
  0 <= F < 2 ^ 64 -> 0 <= SHB -> SHB + F / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + F / 8).
Proof.
intros E n m F SHB Hn Hm HF HS1 HS2.
assert (HD : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Un : U E (SOff n 0) = F)
  by (rewrite U_SOff, Hn, (unsigned_lit_small F HF), Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (Um : U E (SOff m 0) = SHB)
  by (rewrite U_SOff, Hm, (unsigned_lit_small SHB ltac:(lia)), Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (F / 8)) by (unfold M64; lia).
rewrite (Z.add_comm (F / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

(* A one-byte region cell, read through the view. *)
Lemma can_aview_of_val1 : forall segs H m a v,
  val_mem segs (mrestrict H m) a 1 v -> aview segs H m a = Some (le_byte v 1 0).
Proof.
intros segs H m a v HV. pose proof (HV 0%nat ltac:(lia)) as H0.
rewrite Nat2Z.inj_0, Z.add_0_r in H0. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* The four-byte shadow check the program runs before each `lw`: `k = 0` (the fast path) or `(a mod 8) + 3 < k`
   (the slow path's `blt`). From the byte-wise addressability of [a, a + 4), reading the byte of [a, a+4) with the
   largest offset that still lies in a's own granule: at (a mod 8) <= 4 that byte is a + 3 and gives the second
   case; at (a mod 8) >= 5 its offset in the granule is 7, which saddr_ok can satisfy only with k = 0. *)
Lemma can_check4 : forall (rd : reader) a k,
  0 <= a ->
  range_addressable rd SHADOW_OFF a 4 ->
  rd (shadow_of_addr SHADOW_OFF a) = Some k ->
  k = 0 \/ (a mod 8 + 3 < k /\ k < 8).
Proof.
  intros rd a k Ha HRA Hk.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hm.
  set (j := if a mod 8 <=? 4 then 3 else 7 - a mod 8).
  assert (Hj : 0 <= j <= 3 /\ a mod 8 + j <= 7).
  { unfold j. destruct (Z.leb_spec (a mod 8) 4); lia. }
  destruct Hj as (Hj1 & Hj2).
  assert (Hdiv : (a + j) / 8 = a / 8).
  { pose proof (Z.div_mod a 8 ltac:(lia)) as D.
    symmetry. apply (Z.div_unique (a + j) 8 (a / 8) (a mod 8 + j)); lia. }
  destruct (HRA (a + j) ltac:(lia)) as (s & Hs & Hok).
  unfold shadow_of_addr in Hs, Hk. rewrite Hdiv in Hs. rewrite Hs in Hk. injection Hk as <-.
  assert (Hmj : (a + j) mod 8 = a mod 8 + j).
  { pose proof (Z.div_mod (a + j) 8 ltac:(lia)) as D1. pose proof (Z.div_mod a 8 ltac:(lia)) as D2.
    rewrite Hdiv in D1. lia. }
  unfold saddr_ok in Hok. rewrite Hmj in Hok.
  destruct Hok as [-> | [H1 H2]]; [left; reflexivity|].
  unfold j in *. destruct (Z.leb_spec (a mod 8) 4); [right; lia | left; lia].
Qed.

(* The register atoms of an image environment built over a register map (the donor's YC1g.v ew_Eimg_Ereg_nat). *)
Section env. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma can_ew_Eimg_Ereg_nat : forall (regs : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (PI := PI_transport) (Ereg regs extra)) n = YK11.getr regs r.
Proof.
  intros regs extra n r Hn. rewrite Eimg_low.
  - apply ew_Ereg_nat. exact Hn.
  - pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold A_TEXT. lia.
Qed.

(* A four-byte value of the view is a four-byte value of the restricted memory (the donor's seg_entry
   val_mem_of_rd32). *)
Lemma can_val_mem_of_rd32 : forall segs H mem a v,
  rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
  intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
  destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
  change (bv_modulus 8) with 256. exact Hrange.
Qed.
End env.

(* ------------------------------------------------------------------ *)
(* 5. Reading a region back, and the shadow of the real stack          *)
(* ------------------------------------------------------------------ *)

Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
Lemma can_region_nth : forall E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma can_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma can_aview_kept_frame : forall E rs H (m m' : word -> option byte) lo,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= lo ->
  (forall a, lo <= a < 2 ^ 64 -> ~ in_wrange E rs a) ->
  forall a, lo <= a < 2 ^ 64 -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' lo HF Hlo Hno a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
apply Hno. exact Ha.
Qed.
Lemma can_writable_kept : forall H (m m2 : word -> option byte) a,
  (apresent H m a -> apresent H m2 a) -> writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma can_aview_vis : forall H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma can_mbyte_of_aview : forall H (m m' : word -> option byte) a,
  aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H m m' a Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H m') a) as [b'|] eqn:E'; destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E;
cbn in Hv; try discriminate; [|reflexivity].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
End rg.

(* The shadow of the whole machine stack is 0 at every AR state (lib/Reusable/YG0n.v zero_shadow_ranges puts
   [ly_stk_lo, ly_stk_hi) first), so any stack range is addressable and its shadow bytes are visible. *)
Section stk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma can_stack_zshadow : forall ly S (W : world segs) mem md,
  AR segs B ly S W mem md ->
  ly_stk_lo ly mod 4096 = 0 /\ ly_stk_hi ly mod 4096 = 0 /\
  zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly).
Proof.
intros ly S W mem md HAR. destruct HAR as (M & _).
pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_top _ LO) as (_ & _ & _ & _ & Hlo4 & Hhi4 & _).
pose proof (am_zshadow _ _ _ _ M) as Z. unfold zshadow_ok in Z. rewrite Forall_forall in Z.
unfold page_aligned in Hlo4, Hhi4.
split; [exact Hlo4|]. split; [exact Hhi4|].
exact (Z (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(left; reflexivity)).
Qed.

(* A page-aligned bound divided by 8 is a multiple of 8, so the shadow of [ly_stk_lo, ly_stk_hi) starts and ends
   on an eight-byte shadow word. *)
Lemma can_page_div8 : forall x, x mod 4096 = 0 -> x / 8 mod 8 = 0 /\ x mod 8 = 0 /\ x / 8 = 512 * (x / 4096).
Proof.
intros x Hx. pose proof (Z.div_mod x 4096 ltac:(lia)) as D.
set (q := x / 4096) in *.
assert (E8 : x / 8 = q * 512) by (replace x with (q * 512 * 8) by lia; apply Z.div_mul; lia).
split; [rewrite E8; replace (q * 512) with (q * 64 * 8) by lia; apply Z_mod_mult|].
split; [replace x with (q * 512 * 8) by lia; apply Z_mod_mult|].
rewrite E8. lia.
Qed.

Lemma can_stack_addressable : forall ly S (W : world segs) mem md x n,
  AR segs B ly S W mem md -> ly_stk_lo ly <= x -> 0 <= n -> x + n <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hn Hhi.
destruct (can_stack_zshadow ly S W mem md HAR) as (A1 & A2 & A3).
destruct (can_page_div8 _ A1) as (_ & E1 & _). destruct (can_page_div8 _ A2) as (_ & E2 & _).
assert (A2' : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0)
  by (rewrite Zminus_mod, E1, E2; reflexivity).
eapply range_addressable_sub; [exact (zero_shadow_range _ _ _ _ E1 A2' A3) | lia | lia].
Qed.

Lemma can_stack_hull : forall ly S (W : world segs) mem md x n,
  AR segs B ly S W mem md -> ly_stk_lo ly <= x -> 0 < n -> x + n <= ly_stk_hi ly ->
  shadow_hull_vis (aview segs (w_H W) mem) x n.
Proof.
intros ly S W mem md x n HAR Hlo Hn Hhi.
destruct (can_stack_zshadow ly S W mem md HAR) as (A1 & A2 & A3).
destruct (can_page_div8 _ A1) as (Q1 & E1 & _). destruct (can_page_div8 _ A2) as (Q2 & E2 & _).
set (L := ly_stk_lo ly) in *. set (Hi := ly_stk_hi ly) in *.
assert (HLx : L / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (Hxh : (x + n - 1) / 8 <= (Hi - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Hhi8 : (Hi - 1) / 8 = Hi / 8 - 1).
{ pose proof (Z.div_mod Hi 8 ltac:(lia)) as D. pose proof (Z.div_mod (Hi - 1) 8 ltac:(lia)) as D'.
  pose proof (Z.mod_pos_bound (Hi - 1) 8 ltac:(lia)). lia. }
assert (Hsub : (Hi - L) / 8 = Hi / 8 - L / 8).
{ pose proof (Z.div_mod Hi 8 ltac:(lia)) as D1'. pose proof (Z.div_mod L 8 ltac:(lia)) as D2'.
  pose proof (Z.div_mod (Hi - L) 8 ltac:(lia)) as D3'. pose proof (Z.mod_pos_bound (Hi - L) 8 ltac:(lia)). lia. }
intros s Hs. unfold shadow_addr in Hs.
assert (HSL : SHADOW_OFF + L / 8 <= (SHADOW_OFF + x / 8) / 8 * 8).
{ assert (HA : (SHADOW_OFF + L / 8) mod 8 = 0) by (unfold SHADOW_OFF; rewrite Zplus_mod, Q1; reflexivity).
  pose proof (Z.div_le_mono (SHADOW_OFF + L / 8) (SHADOW_OFF + x / 8) 8 ltac:(lia) ltac:(lia)) as HD.
  pose proof (Z.div_mod (SHADOW_OFF + L / 8) 8 ltac:(lia)). lia. }
assert (HSU : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 + 8 <= SHADOW_OFF + Hi / 8).
{ assert (HA : (SHADOW_OFF + Hi / 8) mod 8 = 0) by (unfold SHADOW_OFF; rewrite Zplus_mod, Q2; reflexivity).
  pose proof (Z.div_le_mono (SHADOW_OFF + (x + n - 1) / 8) (SHADOW_OFF + Hi / 8) 8 ltac:(lia) ltac:(lia)) as HD.
  pose proof (Z.div_mod (SHADOW_OFF + Hi / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)).
  assert (HQ : (SHADOW_OFF + (x + n - 1) / 8) / 8 < (SHADOW_OFF + Hi / 8) / 8) by lia.
  lia. }
specialize (A3 (s - (SHADOW_OFF + L / 8)) ltac:(rewrite Hsub; lia)).
unfold shadow_of_addr in A3.
replace (SHADOW_OFF + L / 8 + (s - (SHADOW_OFF + L / 8))) with s in A3 by lia.
rewrite A3. discriminate.
Qed.
End stk.
