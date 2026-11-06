(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v (ajournal_after_write) and lib/A/Prog/PaCall.v (aj_intrin_atS): the strtol call of number's walk, whose writes are its scratch window, the end pointer's word in number's own side-stack frame and the errno cell. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation awr_byte := (awr_byte segs B).
(* ajournal_after_write (YCbq.v) with one more write kind: a byte of the errno cell, which lies in the image (the
   journal's image and extra-range clauses leave the errno cell out, and it is in no block and no frame) *)
Lemma ajournal_after_write_errno : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a) \/ (as_errno B <= a < as_errno B + 4 /\ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
((~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))) \/
(inFP FP a /\ in_img segs a) \/
(inFP FP a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc) \/
(inFP FP a /\ exists cid pos, In (cid, pos) (frames Sc) /\
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) \/
(as_errno B <= a < as_errno B + 4 /\ in_img segs a /\ 0 <= a < kLowMemEnd)).
{ intros a Ha. destruct (HW a Ha) as [Hw | [Hx | (Her & Hei)]].
- left; left. exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw).
- left; right. exact Hx.
- right. split; [exact Her|]. split; [exact Hei | exact (segs_low a Hei)]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs Hnf. rewrite <- (F1 a Ha Hs Hnf). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [[(_ & [[_ Hs'] | [[[_ Hlow] _] | [(cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (_ & Hx)] | (_ & _ & Hlow)];
[exact (Hs Hs') | zlia | zlia | zlia | exact (Hnf Hf') | exact (Hnf Hf') | exact (Hnf Hf') | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [[(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)] | (_ & Hei & _)].
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
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo).
- exact (blk_img segs B LAWS lyc Sc Wc memc mdc p n (p + i) HAR H2 ltac:(zlia) Hei). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [[(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx & Hxi)] | (Her & _)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
- exact (Hxi Hi).
- exact (He Her). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (fs_frame_bytes_nonneg cid) as Hnn0.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [[(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | [(c' & p' & Hown & Hr') | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)] | (_ & Hei & Hlow)].
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
exact (proj2 Hfsh Hxo).
- destruct Hr as [Hr | Hr]; [rewrite <- ?Efa in Hr; exact (frm_img segs B LAWS lyc Sc Wc memc mdc cid pos a HAR HinC Hr Hei) | zlia]. }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [[(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]]) | [(_ & Hi') | [(_ & Hst) | (_ & c2 & p2 & Hin2 & Hr2)]]]]]) | (Hxo & Hx)] | (Her & _)].
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
- exact (Xo Hxo).
- exact (He Her). }
Qed.
End e.
Section f.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Local Notation awr_byte := (awr_byte segs B).
(* the strtol call of number: its writes are the scratch window, the end pointer's word [e, e + 8) and the errno
   cell. Model: PaCall.v aj_intrin_atS. *)
Lemma aj_strtol_atS : forall pc gotw guard, RtNumber.astrtol_realizes segs B pc gotw guard ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x e (str : list byte) ev (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 e -> getr regsT 12 = w64 10 -> 0 < x -> 0 < e ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 3 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
aguard_ok segs W memT gotw guard ->
astr_at segs W memT x str -> x + astr_len str + 1 < 2 ^ 64 ->
aread_ok segs (3 * ESTACK) W regsT memT x (astr_len str + 1) ->
(* 8 bytes of band room past the string and past the end pointer's word (the strtol contract, RtNumber.v:86-91) *)
amem_range x (astr_len str + 8) ->
atail_vis segs W memT (x + astr_len str) ->
(forall a, e <= a < e + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\ alloc_ceiling > a) ->
(forall a, e <= a < e + 8 -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
writable_at segs (mrestrict (w_H W) memT) a) ->
0 <= e -> e + 8 <= 2 ^ 63 -> amem_range e 16 ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF e 8 -> shadow_hull_vis (aview segs (w_H W) memT) e 8 ->
(e + 8 <= x \/ x + astr_len str + 1 <= e) -> (e + 8 <= as_errno B \/ as_errno B + 4 <= e) ->
(* the strtol contract's separation premises (RtNumber.v:98, :102, :104): the end pointer's word is 8-aligned and
   off the image's span, and the string is apart from the errno cell *)
e mod 8 = 0 -> (forall a, e <= a < e + 8 -> ~ in_zr a (ly_img lyc)) ->
(as_errno B + 4 <= x \/ x + astr_len str + 1 <= as_errno B) ->
rd32 (aview segs (w_H W) memT) (as_errno B) ev ->
rt_rom_view segs B W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
getr regs2 10 = w64 (__intscan_c.s10_val str) /\
rdword (aview segs (w_H W) mem2) e = Some (x + __intscan_c.s10_end str) /\
rd32 (aview segs (w_H W) mem2) (as_errno B) (bv_unsigned (__intscan_c.s10_errno str (Z_to_bv 64 ev))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 8) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (sp0 + o - 3 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc gotw guard AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x e str ev o raw
HJ Ha0 Ha1 Ha2 Hx He Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hgd Hstr Hxl Hrd Hamx Htl Hdest HPC He0 He8 Hame Hra_e Hhull Hsep Hsepe Hem8 Heoff Hxer Hev Hrom.
assert (Hamr : amem_range e 8) by (unfold amem_range in *; lia).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre_stk segs B (3 * ESTACK) lyc Sc W regsT memT mdc).
{ split; [exact (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg
ltac:(zlia) ltac:(rewrite Hra; exact Hraw) Hgp Htp)|].
split; [rewrite Eslo, Hsp'; zlia|].
intros a Ha. unfold ascratch_stk in Ha. rewrite Hsp' in Ha. apply Hpres. zlia. }
assert (HWR : awrite_ok segs B (3 * ESTACK) lyc Sc W regsT memT e 8).
{ split; [exact He0|]. split; [exact He8|]. split; [zlia|].
split.
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hac].
destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw (HPC a Ha)) as [Hp Hno].
split; [exact Hp|]. split; [exact Hno|]. unfold ascratch_stk. rewrite Hsp'. zlia. }
split; [exact Hamr|]. split; [exact Hra_e|]. intros _. exact Hhull. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x e str ev Hgd HPRE Ha0 Ha1 Ha2 Hx He Hstr Hxl Hrd Hamx Htl HWR Hame Hsep Hsepe Hem8 Heoff Hxer Hev Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & (Hres & Hend & Herr) & Hfr & Hpres2 & _).
unfold ascratch_stk, aerrno_cell in Hfr. rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_errno segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (sp0 + o - 3 * ESTACK <= a < sp0 + o) \/ (e <= a < e + 8) \/ (as_errno B <= a < as_errno B + 4)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | [Ha | Ha]].
+ left. left. zlia.
+ left. exact (proj1 (Hdest a Ha)).
+ right; right. split; [exact Ha | exact (proj1 (proj2 errno_low) a Ha)].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hend|]. split; [exact Herr|].
split; [intros a Ha H1 H2 H3; apply (Hfr a Ha); [exact H3 | intros [H' | H']; [exact (H1 H') | exact (H2 H')]]|].
split; [exact Hpres2 | exact Hsame].
Qed.
End f.
End c.
