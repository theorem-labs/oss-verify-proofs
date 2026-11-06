(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0b YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Local Notation ajournal := (ajournal segs B).
Local Notation acall_kept := (acall_kept segs B).
Local Notation awr_byte_cases := (YCcz.awr_byte_cases segs B LAWS).
Local Notation sep_blocks := (YCcz.sep_blocks segs B LAWS).
Local Notation sep_block_frame := (YCcz.sep_block_frame segs B LAWS).
Local Notation blk_img := (YCcz.blk_img segs B LAWS).
Local Notation frm_img := (YCcz.frm_img segs B LAWS).
Local Notation frames_bounds := (YCcz.frames_bounds segs B LAWS).
Local Notation sep_frames_pos := (YCcz.sep_frames_pos segs B LAWS).
Lemma ajournal_after_write_win : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> bud_le Sc S' 0 0 0 0   -> frames S' = own2 ++ frames S ->
qtightB S' ->
ajournal STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
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
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply same_io_trans; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [exact (jbud_step0 _ _ _ _ Hk Hnev Hnev')|]. split; [exact Hk|]. rewrite !Eab'. split.
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
pose proof (sep_blocks lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He. rewrite <- (F3 a Hi Hns He). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
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
split; [intros a Ha; apply (Hgr a Ha); apply Hpres, Ha|].
split; [exact Hstatic | exact HQT'].
Qed.
Lemma aj_stack_malloc_sz_at : forall pc cid, astack_malloc_sz_realizes segs B pc cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw n,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
vev S2 = vev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) n /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros pc cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw n
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Hn Hn8 Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
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
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 n HPRE Ha0 Hn Hn8 Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity). assert (Hch2 : st_chunks S2 = st_chunks Sc) by (rewrite ES2; reflexivity).
assert (Hvev2 : vev S2 = vev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | exact (jbud_same _ _ _ 0 (Z.le_refl 0) (jbud_refl Sc) Hnev2 Hch2 Hsecs2) | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p m i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtightB_same Sc); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub segs B LAWS segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hvev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal segs B segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | ].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
Lemma aj_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (Hoff : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hp. destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
- specialize (Heff (a - q) ltac:(zlia)). replace (q + (a - q)) with a in Heff by zlia.
destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
rewrite (seg_rom_none segs a Ha Hni) in Heff. discriminate.
- eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | zlia] | exact Hp].
- eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | zlia] | exact Hp]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha Hna).
- intros a Ha Hp. apply Hoff; [zlia | intros Hi; pose proof (segs_low a Hi); zlia | exact Hp].
- exact Hsame.
- intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - apply bud_le_refl. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hoff].
Qed.
Hypothesis frame_flag_law : frame_flag_lawP segs B.
Lemma aj_stack_free_at : forall pc cid, astack_free_realizes segs B pc cid -> 0 <= cid ->
forall W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k ->
getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n / 8 -> aview segs (w_H W) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + n / 8) ->
a <> flag_addr lyc cid pos -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a)).
Proof.
intros pc cid ASFR Hcid W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k pos n o raw
HJ Ha0 Ha1 Hn Hn8 Htrail Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frame_flag_law lyc Sc W memT mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
destruct (frames_bounds lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (Hn8le : n / 8 <= fs_frame_bytes cid / 8) by (apply Z.div_le_mono; zlia).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
pose proof (sep_frames_pos lyc Sc W memT mdc (cid, pos) (cid, pos) [] l1' l2 HAR
ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
eapply SRr_mono.
{ exact (ASFR lyc Sc W regsT memT mdc pos n HPRE Hin Ha0 Ha1 Hn Hn8 Htrail). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_win STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k mem2 md2
(fun a => (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + n / 8)
\/ a = flag_addr lyc cid pos \/ (sp0 + o - ESTACK <= a < sp0 + o))
(stack_free_state cid pos Sc) own' HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right; left | right; right]; exact H'.
- intros a Ha Hp. destruct (Z_lt_ge_dec a (sp0 + o - ESTACK)) as [Hlo|Hlo]; [|destruct (Z_lt_ge_dec a (sp0 + o)) as [Hhi|Hhi]].
+ eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | | exact Hp].
apply Hfr; [zlia | zlia | | zlia]. intros ->. destruct Hfr_rng as [Happ _]. zlia.
+ apply Hpres2. zlia.
+ eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | | exact Hp].
apply Hfr; [zlia | zlia | | zlia]. intros ->. destruct Hfr_rng as [Happ _]. zlia.
- exact Hsame.
- intros a [Ha | [-> | Ha]].
+ left. right. right. right. exists cid, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. zlia.
+ right. split; [exact Hfo | exact Hfr_rng].
+ left. left. zlia.
- exact HAR2.
- unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
- reflexivity.
- apply bud_le_same; reflexivity.
- etransitivity; [exact E2 | symmetry; exact E1].
- apply (qtightB_same Sc); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
End d.
End c.
