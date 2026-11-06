(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: call lemmas for the ASan walk of check_round_trip: ajournal_after_write_win (the core's ajournal_after_write, lib/Reusable/YCbq.v, with its presence premise narrowed to the journal's stack window), aj_set_shadow_atS (a shadow-fill entry __asan_set_shadow_XX on the shadow of the caller's own side-stack frame) and aj_stack_free_cls_atS (the release entry of a side-stack class that fills the whole frame's shadow). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip_k.v, with its module paths and module names changed; 187 of its 335 lines of code are new or changed and 152 lines of the source are left out. *)
(* TransportGRt: two runtime entries of image A as steps of the caller's G journal (lib/A/W_journalG.v ajournal_gx with
   XO = 0 and OUT = []), from their callee texts in lib/A/Prog/TransportRtCg.v. Nothing here names a program function:
   every G-form walk that calls these entries (with a side-stack frame of its own) uses the same two lemmas.
   - gx_set_shadow_at: a call of __asan_set_shadow_v (TransportRtCg.v aset_shadow_realizes pc v) that fills the n
     shadow bytes [q, q + n) inside the shadow of a frame the journal owns. The journal comes back at the same state
     with the same own list; the n bytes hold v; every other byte is kept (the text keeps the ESTACK bytes below sp
     too); presence grows; the callee-saved registers are kept. The write right of the n bytes is the journal's own
     (YCbq.v awr_byte's in_frames case: the frame is in the own list).
   - gx_stack_free_cls_at: a call of the release entry __asan_stack_free_cid (TransportRtCg.v astack_free_cls_realizes
     pc cid) of the journal's top own frame (cid, pos). The journal comes back at stack_free_state cid pos with that
     frame gone from the own list; the frame's shadow bytes hold 0xf5; every byte but those, the frame's flag byte and
     the ESTACK bytes below sp is kept; every byte outside the image but the flag byte that was present stays
     present. The write rights: the shadow bytes are the own frame's (in_frames), the flag byte is an owned static
     (YCbq.v frame_flag_lawP), the ESTACK bytes are in the journal's stack window. The text states no value of the
     flag byte after the call, so neither does this lemma.
   - aj_after_write_w: YCbq.v ajournal_after_write with presence asked only of the journal's stack window (the stack
     free's text promises presence below sp only, so an image byte's presence is not known after it). Its proof is
     ajournal_after_write's, but for that one premise.
   - dk_kept_free_gw: TransportGFrame.v dk_kept_nf_gw for the stack free's step (the own frame of class cid, its shadow
     bytes, its flag byte and a range [lo, hi) inside the call's stack window may change; presence is known outside
     the image only), so the caller's acall_kept_g goes on past the call. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg CanKit TransportGFrame.
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

(* ------------------------------------------------------------------ *)
(* 1. A write that may shrink the own list, presence asked below sp0  *)
(* ------------------------------------------------------------------ *)

(* YCbq.v ajournal_after_write, whose presence premise (every present byte stays present) is used only for the
   journal's stack window [sp0 - STK, sp0): here that window's presence is the premise. *)
Lemma aj_after_write_w : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
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
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hwin Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
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
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx];
  [left; exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
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
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
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
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [exact Hwin|].
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

(* ------------------------------------------------------------------ *)
(* 2. __asan_set_shadow_v in the G journal                             *)
(* ------------------------------------------------------------------ *)

Lemma gx_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q ->
q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc v ASR G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
  HJ Hown Ha0 Ha1 Hn Hq0 Hq1 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
pose proof HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 memS md own lyc Sc W memT mdc k regsT o HJi Hsp Hal Hneg Hbud);
  [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono; [exact (ASR lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq0 Hq1)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hval & Hkeep & _ & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k memS HSTK); [|exact Hag].
  apply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 memS md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJi Hkeep Hgr Hsame).
  - intros a Ha. left. unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos.
    split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hval|]. split; [exact Hkeep | exact Hgr].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. __asan_stack_free_cid in the G journal                           *)
(* ------------------------------------------------------------------ *)

Lemma gx_stack_free_cls_at : forall pc cid, astack_free_cls_realizes segs B pc cid -> frame_flag_lawP segs B ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pos n (o : Z) raw,
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc Sc W memT mdc k ->
getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n ->
rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < fs_frame_bytes cid / 8 ->
    aview segs (w_H W) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some 0xf5) /\
 (forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
    a <> flag_addr lyc cid pos -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
    aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> a <> flag_addr lyc cid pos ->
    apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc cid ASF FFL G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pos n o raw
  HJ Ha0 Ha1 Hfw Hsp Hal Hneg Hbud Hgp Htp Hra Hraw.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc Sc W memT mdc k HJ)
  as (memS & HJi & Hag & HSTK).
pose proof HJi as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 memS md ((cid, pos) :: own) lyc Sc W memT mdc k regsT o HJi Hsp Hal
    Hneg Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc Sc W memT mdc cid pos HAR Hin) as (_ & HFLo & (HFLapp & HFLimg) & (_ & _ & HFLc)).
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (HF4096 & HFc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
eapply SRr_mono; [exact (ASF lyc Sc W regsT memT mdc pos n HPRE Hin Ha0 Ha1 Hfw)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hval & Hkeep & Hwin).
rewrite Hsp in Hkeep, Hwin.
remember (frame_addr lyc cid pos) as F eqn:EF. remember (flag_addr lyc cid pos) as FL eqn:EFL.
assert (HSH : kLowMemEnd <= shadow_addr F /\ shadow_addr F + fs_frame_bytes cid / 8 <= kHighShadowEnd).
{ pose proof (YCbq.shadow_addr_bounds F ltac:(zlia)) as B1.
  pose proof (YCbq.shadow_addr_bounds (F + fs_frame_bytes cid) ltac:(zlia)) as B2.
  pose proof (shadow_range_end F (fs_frame_bytes cid) Hfs) as B3. zlia. }
(* presence outside the image, but at the flag byte *)
assert (Hgr : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> a <> FL ->
  apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hne Hp.
  destruct (Z_le_gt_dec (shadow_addr F) a) as [h1|h1];
    [destruct (Z_lt_ge_dec a (shadow_addr F + fs_frame_bytes cid / 8)) as [h2|h2]|].
  - apply (apresent_of_aview segs); [exact Ha | exact Hni|].
    replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
    rewrite (Hval (a - shadow_addr F) ltac:(lia)). discriminate.
  - destruct (Z_le_gt_dec (sp0 + o - ESTACK) a) as [h3|h3]; [destruct (Z_lt_ge_dec a (sp0 + o)) as [h4|h4]|].
    + exact (Hwin a ltac:(lia)).
    + apply (apresent_transfer segs (w_H W) (w_H W) memT mem2 a Ha Hni); [|exact Hp].
      apply Hkeep; [exact Ha | lia | exact Hne | lia].
    + apply (apresent_transfer segs (w_H W) (w_H W) memT mem2 a Ha Hni); [|exact Hp].
      apply Hkeep; [exact Ha | lia | exact Hne | lia].
  - destruct (Z_le_gt_dec (sp0 + o - ESTACK) a) as [h3|h3]; [destruct (Z_lt_ge_dec a (sp0 + o)) as [h4|h4]|].
    + exact (Hwin a ltac:(lia)).
    + apply (apresent_transfer segs (w_H W) (w_H W) memT mem2 a Ha Hni); [|exact Hp].
      apply Hkeep; [exact Ha | lia | exact Hne | lia].
    + apply (apresent_transfer segs (w_H W) (w_H W) memT mem2 a Ha Hni); [|exact Hp].
      apply Hkeep; [exact Ha | lia | exact Hne | lia]. }
assert (HJ2 : ajournal segs B STK sp0 FP ly S W0 memS md own lyc (stack_free_state cid pos Sc) W mem2 md2 k).
{ apply (aj_after_write_w STK sp0 FP ly S W0 memS md ((cid, pos) :: own) lyc Sc W memT mdc k mem2 md2
    (fun a => (shadow_addr F <= a < shadow_addr F + fs_frame_bytes cid / 8) \/ a = FL \/
              (sp0 + o - ESTACK <= a < sp0 + o))
    (stack_free_state cid pos Sc) own HJi).
  - intros a Ha Hn. apply Hkeep; [exact Ha | intros h; apply Hn; left; exact h
      | intros h; apply Hn; right; left; exact h | intros h; apply Hn; right; right; exact h].
  - intros a Ha. destruct (Z_le_gt_dec (sp0 + o - ESTACK) a) as [h3|h3].
    + destruct (Z_lt_ge_dec a (sp0 + o)) as [h4|h4]; [exact (Hwin a ltac:(lia))|].
      apply Hgr; [zlia | intros Hi; pose proof (segs_low a Hi); zlia | zlia | exact (Hpres a Ha)].
    + apply Hgr; [zlia | intros Hi; pose proof (segs_low a Hi); zlia | zlia | exact (Hpres a Ha)].
  - exact Hsame.
  - intros a [Hs | [Hf | Hw]].
    + left. unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos.
      split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite <- EF. lia.
    + right. rewrite Hf. split; [exact HFLo | split; [exact HFLapp | exact HFLimg]].
    + left. unfold awr_byte. left. lia.
  - exact HAR2.
  - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. lia.
  - exact (can_sf_frames cid pos Sc (own ++ frames S) Hfrs).
  - apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact (gx_pack0 segs B G STK sp0 FP ly S W0 mem md own lyc (stack_free_state cid pos Sc) W mem2 md2 k memS
  HSTK HJ2 Hag)|].
split; [exact HP|]. split; [exact Hval|]. split; [exact Hkeep | exact Hgr].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. acall_kept_g past the stack free                                 *)
(* ------------------------------------------------------------------ *)

(* TransportGFrame.v dk_kept_nf_gw for a step that changes the own frame of class cid (its bytes, its shadow bytes, its
   flag byte) and a range [lo, hi) inside the call's stack window [slo, shi), and keeps presence outside the image
   but at the flag byte: the stack free's step (gx_stack_free_cls_at), at a current state (ly2, S2) whose frames are
   the call's with that frame on top, whose blocks contain the call's and whose layout puts the frames where the
   call's does. *)
Lemma dk_kept_free_gw : forall G lyc Sc W memc mdc ly2 S2 (W2 : world segs) mem2 md2 memY slo shi lo hi cid fpos F FL
    (Eo : Z -> Prop),
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP segs B ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 -> slo <= lo -> hi <= shi ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf cid F FL a -> ~ (lo <= a < hi) ->
     aview segs (w_H W2) memY a = aview segs (w_H W2) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> a <> FL ->
     apresent (w_H W2) mem2 a -> apresent (w_H W2) memY a) ->
  acall_kept_g segs B G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros G lyc Sc W memc mdc ly2 S2 W2 mem2 md2 memY slo shi lo hi cid fpos F FL Eo HAR HAR2 Hfrs Hbl ELF EF EFL FFL
  Hce Hshi Hlo Hhi (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr.
destruct (dkg_nf_sep_gw segs B LAWS segs_low lyc Sc ly2 S2 W2 mem2 md2 cid fpos F FL HAR2 Hfrs Hbl ELF EF EFL FFL)
  as (N1 & N2 & N3 & N4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFL : FL < alloc_ceiling) by (apply N4; unfold dkg_nf; right; right; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros Hn; pose proof (N4 a Hn); lia | lia].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HN; exact (N1 b m i Hb Hi HN) | lia].
- intros a Hi HnG Hno He. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; assumption | lia | intros HN; exact (N2 a HN Hi) | lia].
- intros c p a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HAR Hin) as (G4096 & Gce & _).
  pose proof (fs_frame_bytes_nonneg c) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc c p) (fs_frame_bytes c) Hfs) as Hse.
    assert (Hd : (frame_addr lyc c p + fs_frame_bytes c) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 c p a Hin Hr Hn) | lia | intros HN; exact (N3 c p a Hin Hr HN) | lia].
- intros a Ha Hw Hp. apply Hgr; [lia | intros Hi; pose proof (segs_low a Hi); unfold kLowMemEnd in *; lia | lia |].
  exact (K5 a Ha Hw Hp).
- intros a Ha. apply Hgr; [lia | intros Hi; pose proof (segs_low a Hi); unfold kLowMemEnd in *; lia | lia |].
  exact (K6 a Ha).
Qed.

End a.

Print Assumptions gx_set_shadow_at.
Print Assumptions gx_stack_free_cls_at.
Print Assumptions dk_kept_free_gw.
