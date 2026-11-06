(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryLeave), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v, proofs/cgif/cgif_file_fuzzer/lib/YCbo.v, proofs/cgif/cgif_file_fuzzer/lib/YCbq.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryLeave.v, with its module paths and module names changed; 169 of its 299 lines of code are new or changed and 505 lines of the source are left out. *)
(* diginet_session_poll_seg_rt: the two runtime entries of lib/A/Prog/TransportRtCg.v called from a G-form
   caller-journal walk (lib/A/W_journalG.v ajournal_gx with XO = 0, OUT = []) that owns a side-stack frame, in the form
   of lib/A/Prog/TransportGFrame.v gx_stack_malloc_at. Nothing here names a program function.
   - gx_set_shadow_at: __asan_set_shadow_v (TransportRtCg.v aset_shadow_realizes) on n shadow bytes of an owned live
     frame: the journal at the same state, the n bytes v, every other byte outside the entry's ESTACK window kept.
   - gx_stack_free_at: the release entry of an owned live frame (TransportRtCg.v astack_free_cls_realizes): the
     journal with the frame released (stack_free_state, the frame off the owned list), every byte outside the
     frame's shadow, its flag byte and the entry's ESTACK window kept.
   The release entry states presence only for its own scratch, so the journal step it needs is
   rt_ajournal_after_write_stk below: lib/Reusable/YCbq.v ajournal_after_write with the presence premise asked only
   on the journal's stack window, the one place that proof uses it. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg CanKit TransportGFrame TransportRtCg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* lib/Reusable/YCbq.v ajournal_after_write with its presence premise asked only on the journal's stack window,
   the one place its proof uses it. A runtime entry whose contract keeps the view of every byte it does not write but
   states no presence for the rest (the release entry) gives presence there and nowhere else. The proof is the
   original's, with that one step changed. *)
Lemma rt_ajournal_after_write_stk : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hstkp Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
(* the two bounds without their side condition: the kit's lia drops an implication *)
assert (HS1 : SHADOW_OFF <= shadow_addr (frame_addr lyc cid pos))
  by (destruct Hsb1 as (H1 & _); exact H1).
assert (HS2 : shadow_addr (frame_addr lyc cid pos + fs_frame_bytes cid) < kHighMemBeg)
  by (destruct Hsb2 as (_ & H2); apply H2; clear - Hf0 Hfc C1 C4; lia).
clear Hsb1 Hsb2.
apply Heqw.
{ destruct Hr as [Hr0 | Hr0].
  - clear - Hr0 Efa Hf0 Hfc C1. lia.
  - clear - Hr0 HS1 HS2 Hse C3. unfold SHADOW_OFF in HS1. lia. }
intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr].
  + pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hr Hrb Hd Efa. lia.
  + clear - Hr HS1 HS2 Hse Hlow. unfold SHADOW_OFF in HS1.
    unfold kLowShadowBeg, kHighMemBeg in *. lia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos segs B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr].
  * clear - Hr Hr' Hd Efa. lia.
  * clear - Hr HS1 HS2 Hse Hlo'. unfold SHADOW_OFF in HS1.
    unfold kLowShadowBeg, kHighMemBeg in *. lia.
+ destruct Hr as [Hr | Hr].
  * clear - Hr Hfh Efa Hlo1' Hhi'.
    unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd in *. lia.
  * destruct Hd as [Hd | Hd]; pose proof (shadow_mono _ _ Hd) as Hm;
      clear - Hr Hr' Hse Hse' Hm; lia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [exact Hstkp|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo). }
Qed.

(* __asan_set_shadow_v on [q, q + n), inside the shadow of the owned live frame (cid, pos). *)
Lemma gx_set_shadow_at : forall (pc v : Z), aset_shadow_realizes segs B pc v ->
  forall G (W : world segs) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw cid pos q n,
  gx_ok segs B G ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q ->
  q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using All.
intros pc v ASR G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw cid pos q n
  HG HJ Hown Hin Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hq Hn Hn0 Hlo Hhi.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 memS md own lyc Sc W memT mdc k regsT o HJi Hsp Hal Hneg Hbud);
  [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono; [exact (ASR lyc Sc W regsT memT mdc cid pos q n HPRE Hin Hq Hn Hn0 Hlo Hhi)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hval & Hfr & _ & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k memS HSTK); [|exact Hag].
  apply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 memS md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJi).
  - intros a Ha Hna. exact (Hfr a Ha Hna).
  - exact Hgr.
  - exact Hsame.
  - intros a Ha. left. unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos. split; [exact Hown|].
    right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hval|].
split; [intros a Ha Hqa _; exact (Hfr a Ha Hqa) | exact Hgr].
Qed.

(* The release entry of the owned live frame (cid, pos), the head of the owned list. *)
Lemma gx_stack_free_at : forall (pc cid : Z), astack_free_cls_realizes segs B pc cid -> frame_flag_lawP segs B ->
  0 <= cid ->
  forall G (W : world segs) regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k (o : Z) raw pos n,
  gx_ok segs B G ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k ->
  In (cid, pos) (frames Sc) ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n ->
  rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (shadow_addr (frame_addr lyc cid pos) <= a <
             shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
          a <> flag_addr lyc cid pos -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof using All.
intros pc cid AFR FFL Hcid G W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k o raw pos n
  HG HJ Hin Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Hrd.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k HJ)
  as (memS & HJi & Hag & HSTK).
pose proof HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 memS md ((cid, pos) :: own') lyc Sc W memT mdc k regsT o HJi
    Hsp Hal Hneg Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
(* the flag byte: an owned byte of the image's client area, below the ceiling *)
destruct (FFL lyc Sc W memT mdc cid pos HAR Hin) as (_ & Hfo & Hfr_rng & (Hf4096 & _ & Hfce)).
(* the frame's shadow: below the ceiling, hence below every stack byte *)
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (HF4096 & HFce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as (_ & Hsb).
eapply SRr_mono; [exact (AFR lyc Sc W regsT memT mdc pos n HPRE Hin Ha0 Ha1 Hrd)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & _ & Hfr & Hstk2).
rewrite Hsp in Hfr, Hstk2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* presence on the journal's stack window: the entry's scratch is present by its contract; every other byte there
   keeps its view, and is outside the image, so it stays present *)
assert (Hstkp : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a).
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp0 + o - ESTACK)) as [H1 | H1];
    [| destruct (Z_lt_le_dec a (sp0 + o)) as [H2 | H2]; [exact (Hstk2 a (conj H1 H2))|]];
  (assert (Ha64 : 0 <= a < 2 ^ 64) by lia;
   apply (apresent_of_aview segs (w_H W) mem2 a Ha64);
   [ intros Hi; pose proof (segs_low a Hi); unfold kLowMemEnd in *; lia
   | rewrite (Hfr a Ha64);
     [ destruct (Hpres a Ha) as (Hh & b & Hb); unfold aview, mbyte, mrestrict; rewrite Hh, Hb; cbn; discriminate
     | lia | lia | lia ] ]). }
split.
{ apply (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k memS HSTK);
    [|exact Hag].
  apply (rt_ajournal_after_write_stk STK sp0 FP ly S W0 memS md ((cid, pos) :: own') lyc Sc W memT mdc k mem2 md2
    (fun a => (shadow_addr (frame_addr lyc cid pos) <= a <
               shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) \/
              a = flag_addr lyc cid pos \/ (sp0 + o - ESTACK <= a < sp0 + o))
    (stack_free_state cid pos Sc) own' HJi).
  - intros a Ha Hna. apply (Hfr a Ha).
    + intros Hs. apply Hna. left. exact Hs.
    + intros Hf. apply Hna. right. left. exact Hf.
    + intros He. apply Hna. right. right. exact He.
  - exact Hstkp.
  - exact Hsame.
  - intros a [Hs | [Hf | He]].
    + left. unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos. split; [left; reflexivity|].
      right. unfold in_zr. cbn [fst snd]. lia.
    + right. subst a. split; [exact Hfo | exact Hfr_rng].
    + left. unfold awr_byte. left. lia.
  - exact HAR2.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - pose proof (can_sf_chunks cid pos Sc) as (_ & _ & Hnv & _ & _). rewrite Hnv. lia.
  - exact (can_sf_frames cid pos Sc (own' ++ frames S) Hfrs).
  - apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [exact HP|].
intros a Ha Hs Hf He. exact (Hfr a Ha Hs Hf He).
Qed.

End a.
