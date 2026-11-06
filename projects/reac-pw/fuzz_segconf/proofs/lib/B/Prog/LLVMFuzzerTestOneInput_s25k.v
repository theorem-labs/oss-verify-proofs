(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s6.v, with its module paths and module names changed; 112 of its 340 lines of code are new or changed and 534 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of
   the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S21 (K85ec8 0x85ec8 ..
   0x85fc4) and the return (0x85fc8); the segment lemmas are in LLVMFuzzerTestOneInput_s25.v.

   The image-B twin of image A's lib/A/Prog/LLVMFuzzerTestOneInput_s25k.v (image A's S21 / ret commit 187a26673c08):
   the same lemmas, with image B's modules (the 44 B-kit modules from lib.B, lib.B.Prog, lib.B.Rt, SegInstB) and
   image B's frame (352 bytes, so S1 = (SP0 - 352) & ~31 is 352 or 368 below SP0).

   (1) The journal step of the shadow-fill entry meta_fill_f5 (the runtime's __asan_set_shadow_f5, image B 0x58b70):
   the two lemmas ajournal_after_write_stk and aj_set_shadow_atS, copied verbatim from plugin-hostd/fuzz_command's
   lib/A/Prog/chain_words_s6.v:204-401 (origin/ossv/recipes 501c0d516c69; its B twin lib/B/Prog/chain_words_s6.v:
   211-408 at 3abc3740de97 has the same text), whose release segconf's harness repeats (METHOD.md section 5.7);
   segconf's kit has no PaRt.v, so chain_words' local copy is taken.
   (2) The image facts lt_img across the release: lt_img reads only image bytes (its sa_img ranges, in_roP's
   segments, the read-only window RLO_A .. RHI_A and SegInstB's gotwA 0xa3e98 / guardA 0x5ff838 / longlA 0x5dee40),
   all in [kImgLo, kImgEnd) = [0x10000, 0x602000), and a literal's tail is a ROM fact (sa_romtail); the release
   writes the frame's first word, the frame's shadow and the flag byte, none of them an image byte.
   (3) The payload's bytes along the journal from the entry (fuzz_command's _s01.v lt_payload_kept with segconf's
   footprint ltoi_PG longlA). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- (1) the journal step of the shadow-fill entry: copied verbatim from fuzz_command's
   lib/A/Prog/chain_words_s6.v:204-401 (its own source: an earlier version of lib/A/Prog/PaRt.v:52-244) ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma ajournal_after_write_stk : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof using LAWS segs_low.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))) \/
(inFP FP a /\ in_img segs a) \/
(inFP FP a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc) \/
(inFP FP a /\ exists cid pos, In (cid, pos) (frames Sc) /\
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx];
[left; exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs Hnf. rewrite <- (F1 a Ha Hs Hnf). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | [(cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (_ & Hx)];
[exact (Hs Hs') | zlia | zlia | zlia | exact (Hnf Hf') | exact (Hnf Hf') | exact (Hnf Hf') | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)].
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
- exact (Hnf Hf').
- exact (Hnf Hf').
- exact (Hnf Hf').
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
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
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | [(c' & p' & Hown & Hr') | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)].
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
- exact (Hnf Hf').
- exact (Hnf Hf').
- exact (Hnf Hf').
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [exact Hgr|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]]) | [(_ & Hi') | [(_ & Hst) | (_ & c2 & p2 & Hin2 & Hr2)]]]]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xi Hi').
- exact (Xs Hst).
- destruct Hr2 as [Hr2 | Hr2]; unfold in_zr, frame_rng in Hr2; cbn [fst snd] in Hr2;
[exact (proj1 (Xf c2 p2 Hin2) Hr2) | exact (proj2 (Xf c2 p2 Hin2) Hr2)].
- exact (Xo Hxo). }
Qed.

(* __asan_set_shadow_XX(q, n): fills [q, q + n) with v. The range lies in the shadow of a frame (cid, pos) the
   walk holds (In (cid, pos) own), which the journal lets it write. *)
Lemma aj_set_shadow_atS : forall pc v, RtShadow.aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros pc v AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Hq Hn Hn0 Hlo Hhi Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR HinC) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
eapply SRr_mono; [exact (AS lyc Sc W regsT memT mdc cid pos q n HPRE HinC Hq Hn Hn0 Hlo Hhi)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hfill & Hkeep & Hwin).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_stk STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- exact Hkeep.
- intros a Ha. eapply (apresent_transfer segs);
[zlia | intros Him; pose proof (segs_low a Him); zlia | apply Hkeep; zlia | apply Hpres; exact Ha].
- exact Hsame.
- intros a Ha. cbv beta in Ha. left. unfold awr_byte. right; right; right; left. unfold in_frames. exists cid, pos.
split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hfill|]. split; [exact Hkeep|].
split; [intros a Ha; apply Hwin; rewrite Hsp'; exact Ha | exact Hsame].
Qed.
End e.
End c.

(* ---- the environment of the S21 / ret walk's own lemmas ---- *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaStep PaShadow SegSyms SegList SegPa PaJournal SegPaLib PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_file_c.
Import ListNotations.
Open Scope Z_scope.

(* the realigned base register s1 = (SP0 - 352) & ~31 from a 16-aligned SP0 (addi sp,sp,-352 at 0x84dc0, andi
   sp,sp,-32 at 0x84e00, mv s1,sp at 0x84e04): 352 or 368 below *)
Lemma s25_s1_cases : forall z, z mod 16 = 0 ->
  (z - 352) - (z - 352) mod 32 = z - 352 \/ (z - 352) - (z - 352) mod 32 = z - 368.
Proof.
intros z Hz. pose proof (Z.mod_pos_bound (z - 352) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (z - 352) 32 ltac:(lia)) as Hd. pose proof (Z.div_mod z 16 ltac:(lia)) as Hd2.
rewrite Hz in Hd2. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- (2) the image facts across a write outside the image ---- *)
(* a literal: its bytes and NUL are image bytes (its sa_img), its tail a ROM fact (sa_romtail) *)
Lemma s25_lit_kept : forall H (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros H mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H mem' _ Hrom)].
split; [|exact Hn0].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi.
refine (proj1 (Himg (a + Z.of_nat i) _)). lia.
Qed.

(* lt_img holds at a memory that agrees with the point's on every image address *)
Lemma s25_img_kept : forall cx H (mem mem' : word -> option byte),
  (forall x, kImgLo <= x < kImgEnd -> aview SEGS H mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H mem').
Proof.
intros cx H mem mem' K0 HI.
assert (K : forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x).
{ intros x Hx. apply K0. pose proof (pa_img_range x Hx) as Hr. unfold kImgLo. lia. }
unfold lt_img in *. destruct HI as (HRO & HIM & HGI).
destruct HIM as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
split; [|split].
- intros a Hro Ho He. rewrite K0; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + pose proof (pa_img_range a (ex_intro _ s (conj Hs Hr))) as Ha. unfold kImgLo. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgLo, kImgEnd. lia.
- unfold seg_himg.
  split.
  { intros kk Hkk. rewrite K; [exact (H1 kk Hkk)|]. refine (proj1 (H2 _ _)). lia. }
  split; [exact H2|].
  split.
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (s25_lit_kept H mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (s25_lit_kept H mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (pin_spec.row_addr catA i)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (s25_lit_kept H mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hw i Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (wordsA + 8 * Z.of_nat i)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (s25_lit_kept H mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn kk Hkk. rewrite K; [exact (Hv i Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros i Hi. rewrite K; [exact (HGI i Hi)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* ---- (3) the payload's bytes are kept along the journal from the entry while its block is live: the block is off
   the image (SegPaLib.v blk_off_imgP), the footprint ltoi_PG longlA inside it (fuzz_command's _s01.v:336-352) ---- *)
Lemma s25_payload_kept : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  (0 < x_n cx -> In (x_p cx, x_n cx) (ablocks B ly S)) ->
  forall i, 0 <= i < x_n cx -> rdW W mem (x_p cx + i) = rdW (x_W cx) (x_mem cx) (x_p cx + i).
Proof.
intros cx ly S W mem md own k HB HJ Hin i Hi.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [lia|].
pose proof (Hin ltac:(lia)) as Hin1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
apply (F2 (x_p cx) (x_n cx) i Hin0 Hin1); [lia|].
pose proof (blk_off_imgP B _ _ _ _ _ _ _ (proj1 HPRE) Hin0) as Hoff.
intros (r & Hr & Hlo & Hhi). unfold ltoi_PG, longlA, A_LONGL, LONGL_N in Hr. unfold off_img in Hoff.
cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.

(* one saved register's word in the frame: the slot SP0 - 8 (j + 1) holds register LT_SAVED[j] of the entry *)
Lemma s25_chunk_ok : forall E H (mem : word -> option byte) cx (j : nat) (r : bv 5) off,
  lt_saved cx (aview SEGS H mem) -> nth_error LT_SAVED j = Some r ->
  sv_denot E (SOff (32 + j) 0) = getr (x_regs cx) r -> off = - 8 * Z.of_nat (Datatypes.S j) ->
  YP09.chunk_ok SEGS E (mrestrict H mem) (x_sp0 cx) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))).
Proof.
intros E H mem cx j r off HSV Hj Hd ->.
apply (chunk_ok_val SEGS E _ (x_sp0 cx) _ 8 (SOff (32 + j) 0) (bv_unsigned (getr (x_regs cx) r))).
- rewrite Hd. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (getr (x_regs cx) r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
- apply val_mem_of_rdword. replace (x_sp0 cx + - 8 * Z.of_nat (Datatypes.S j)) with (x_sp0 cx - 8 * Z.of_nat (Datatypes.S j))
    by lia. exact (HSV j r Hj).
Qed.

End e.
End c.
End b.
