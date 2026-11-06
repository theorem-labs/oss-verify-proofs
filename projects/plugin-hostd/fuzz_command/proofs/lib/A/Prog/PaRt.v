(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Reusable/YCbq.v, with its numbers changed; 205 of its 373 lines of code are new or changed and 3177 lines of the source are left out. *)
(* The runtime entries of lib/A/Rt whose step through a program walk's journal PaArt.v's aj_art_at does not give.

   Each contract of lib/A/Rt speaks of one call in isolation: an ecall_pre or ecall_pre_stk at the entry and, at the
   return, the same model state, the registers kept, and the bytes the call changed. A program walk holds an
   ajournal (lib/Reusable/YCbq.v:386) across the whole body of the function. The entries whose contract is
   RtDefs' art_post (lib/A/Rt/RtDefs.v:89) and which write nothing outside their stack window except the errno cell
   (the atoi and the string wrappers) go through PaArt.v's aj_art_at, one step for all of them. The lemmas below are
   the steps for the two entries that do not fit it, in the shape of aj_intrin_atS and aj_stack_malloc_atS
   (lib/A/Prog/PaCall.v): the journal at the call, the stack offset o of the call site (spZ regsT = sp0 + o,
   o mod 16 = 0, o <= 0, the entry's window - o <= STK), the register premises, and the contract's own premises as
   they are; the conclusion is the journal again with the same k (neither entry is an allocator event), the
   registers kept, the contract's result, and the bytes that did not change.

     aj_set_shadow_atS  aset_shadow_realizes (RtShadow.v:27)   window ESTACK      writes [q, q + n), inside the
                                                                                  shadow of a frame the walk holds
     cwc_aj_snprintf_atSF asnprintf_realizes (RtFormat.v)      window 2 * ESTACK  writes [d, d + n), a range the
                                                                                  walk may write

   The shadow-fill contract states its own post, not art_post. The snprintf contract is the shared one of
   RtPFCmd.v (statement pass 4): its post returns at some FP state (PaFx.v's fxrel against the caller's) and
   writes the destination's filled bytes, and aj_art_at allows only the errno cell. So the snprintf step
   builds the contract's dest_ok from the journal and rebuilds the journal with ajournal_after_write
   (YCbq.v:577), as aj_intrin_atS does for its destination; its ecall_pre_stk comes from PaArt.v's
   ecall_pre_stk_at.

   ajournal_after_write_stk is YCbq.v's ajournal_after_write with its presence premise narrowed to the journal's
   own stack window: the shadow-fill contract states that the bytes outside [q, q + n) read the same, but not that
   every present byte stays present, and the journal asks presence only of its window. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArt PaFx.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
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

(* ajournal_after_write (YCbq.v:577) with the presence premise on the journal's stack window only. *)
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
Lemma aj_set_shadow_atS : forall pc v, aset_shadow_realizes segs B pc v ->
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

(* bv_unsigned of a byte list's element, for bytes below 256 *)
Lemma pfb_unsigned_nth : forall (l : list Z) i, Forall (fun c => 0 <= c < 256) l ->
bv_unsigned (nth i (PF.pf_bytes l) (Z_to_bv 8 0)) = nth i l 0.
Proof.
intros l i Hl. unfold PF.pf_bytes. rewrite (map_nth (Z_to_bv 8) l 0 i). rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small.
destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
- rewrite Forall_forall in Hl. exact (Hl _ (nth_In l 0 Hi)).
- rewrite nth_overflow by exact Hi. lia.
Qed.

(* The snprintf wrapper (snprintf(d, n, f, ...)) under the shared contract: since statement pass 4 RtFormat.v's
   asnprintf_realizes is RtPFCmd.v's asnprintf_sh (window CMD_SNP_K = 2 * ESTACK, the return at some FP state).
   The step is the one for a destination [d, d + n) the walk may write (awr_byte, writable where the journal does
   not say it is present, outside the caller's 3 * ESTACK window); the call returns at some fx1 with fxrel fx fx1
   (PaFx.v), writes the sn_len (n - 1) T bytes it fills and its window, and keeps every present byte. Beyond the
   old contract's premises: the image lies below the destination and the window (so the format, the guard words
   and the read-only ranges CMD_SNP_CR the contract reads lie apart from what it writes, and dest_off_globals
   holds), the format's and the text's bytes are below 256, the argument words in the shared form (no stack
   arguments), every %.*s precision is at least 1, the unowned read-only bytes read as the image has them
   (rt_rom_view: the contract's text since RtPFCmd's FF_fm shape), the format a nonempty literal below the GOT word
   with no string argument (RtPFCmd.fr_lit_ok, the boolean the call site computes), and rounding mode 0. *)
Lemma cwc_aj_snprintf_atSF : forall pc gotw guard, asnprintf_realizes segs B pc gotw guard ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt ps args T (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
1 <= n < 2 ^ 31 -> 0 < d -> 0 < f -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 3 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
~ (sp0 + o - 3 * ESTACK <= a < sp0 + o)) ->
(forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/ sp0 <= a < ly_top lyc ->
writable_at segs (mrestrict (w_H W) memT) a) ->
(* the destination's band with the 8-byte slack word past it (the shared contract's amem_range d (sn_len (n - 1) T
   + 8), RtPFShared.v; GXA's range check reads 8 bytes past each written byte) *)
amem_range d (n + 8) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
shadow_hull_vis (aview segs (w_H W) memT) d n ->
RtPFCmd.CMD_IMG_HI <= d -> RtPFCmd.CMD_IMG_HI <= sp0 + o - 3 * ESTACK ->
aguard_ok segs W memT gotw guard ->
0 <= gotw -> gotw + 8 <= RtPFCmd.CMD_IMG_HI -> 0 <= guard -> guard + 8 <= RtPFCmd.CMD_IMG_HI ->
astr_at segs W memT f (PF.pf_bytes fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
f + Z.of_nat (length fmt) + 1 <= RtPFCmd.CMD_IMG_HI ->
PF.pf_parse fmt = Some ps -> PF.pf_text ps args = Some T ->
RtPFShared.pf_prec_pos (map RtPFCmd.piece_of ps) (map RtPFCmd.arg_of args) ->
Forall (fun c => 0 <= c < 256) T -> Z.of_nat (length T) < 2 ^ 31 - 1 ->
aread_ok segs (3 * ESTACK) W regsT memT f (Z.of_nat (length fmt) + 1) ->
RtPFShared.pf_args_asan (aview segs (w_H W) memT)
  (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T))
  (map (argZ regsT) [3; 4; 5; 6; 7]) (map RtPFCmd.arg_of args) ->
rt_rom_view segs B W memT ->
RtPFCmd.fr_lit_ok f fmt (map RtPFCmd.arg_of args) = true ->
frm0 fx ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
getr regs2 10 = w64 (Z.of_nat (length T)) /\
abytes_at segs W mem2 d (PF.pf_bytes (firstn (Z.to_nat (n - 1)) T ++ [0])) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - 3 * ESTACK <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros pc gotw guard AP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt ps args T o raw
HJ Ha0 Ha1 Ha2 Hn Hd Hf Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull Hdi Hwi
Hguard Hgc0 Hgc1 Hgv0 Hgv1 Hstr Hfb Hfi Hparse Htext Hprec HTb HT Hrd Hargs Hcv Hlit Hfrm.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo0 & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 2 * ESTACK) by reflexivity.
assert (HPRE : ecall_pre_stk segs B (2 * ESTACK) lyc Sc W regsT memT mdc).
{ eapply ecall_pre_stk_at; try eassumption; first [lia | rewrite Hra; exact Hraw]. }
destruct HPRE as (HEP & Hslo & Hscr).
destruct Hguard as (Hgw & cval & Hcw).
set (len := RtPFShared.sn_len (n - 1) T).
assert (Hlen : 1 <= len <= n).
{ unfold len, RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
(* what the call writes lies below the caller's window or above its stack pointer *)
assert (HDW : d + len <= sp0 + o - 3 * ESTACK \/ sp0 + o <= d).
{ destruct (Z_le_gt_dec (sp0 + o) d) as [Hge|Hlt]; [right; exact Hge|left].
  destruct (Z_le_gt_dec (d + len) (sp0 + o - 3 * ESTACK)) as [Hle|Hgt]; [exact Hle|exfalso].
  destruct (Z_le_gt_dec (sp0 + o - 3 * ESTACK) d) as [Hd1|Hd1].
  - exact (proj2 (Hdest d ltac:(lia)) ltac:(lia)).
  - exact (proj2 (Hdest (sp0 + o - 3 * ESTACK) ltac:(lia)) ltac:(lia)). }
(* the read-only ranges the contract reads lie in the image *)
assert (HCR : forall r, In r RtPFCmd.CMD_SNP_CR ->
  RtPFCmd.CMD_IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= RtPFCmd.CMD_IMG_HI).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as Hb.
  unfold RtPFCmd.in_cmd_img in Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H3. lia. }
assert (HIMG : RtPFCmd.CMD_IMG_LO = 0x10000 /\ RtPFCmd.CMD_IMG_HI = 0x606000) by (split; reflexivity).
assert (HOUT : forall x w, 0 <= w -> x + w <= RtPFCmd.CMD_IMG_HI ->
  Forall (zdisjoint (x, w)) (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) d len)).
{ intros x w Hw Hx. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
(* the format *)
assert (HFMT : RtPFShared.fmt_at (aview segs (w_H W) memT)
  (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) d len) f fmt).
{ destruct Hrd as (Hr0 & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6).
  destruct Hstr as (Hby & _).
  split; [exact Hf|]. split.
  - intros i Hi.
    assert (EQ : PF.pf_bytes fmt ++ [Z_to_bv 8 0] = PF.pf_bytes (fmt ++ [0]))
    by (unfold PF.pf_bytes; rewrite map_app; reflexivity).
    rewrite EQ in Hby.
    assert (Hlt : (Z.to_nat i < length (PF.pf_bytes (fmt ++ [0%Z])))%nat)
    by (unfold PF.pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
    pose proof (Hby (Z.to_nat i) Hlt) as Hb. rewrite Z2Nat.id in Hb by lia. rewrite Hb.
    f_equal. apply pfb_unsigned_nth. apply Forall_app. split; [exact Hfb | repeat constructor; lia].
  - split; [apply HOUT; lia|]. split; [exact Hr4|]. split; [exact Hr5 | apply Hr6; lia]. }
(* the destination *)
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d len).
{ intros a Ha. destruct (Hdest a ltac:(lia)) as [Hw Hns].
  destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw (HPC a ltac:(lia))) as [Hp Hno].
  split; [exact Hp|]. split; [exact Hno|]. rewrite Hsp'. lia. }
assert (HAMRl : amem_range d (len + 8)) by (unfold amem_range in *; lia).
assert (HRADl : range_addressable (aview segs (w_H W) memT) SHADOW_OFF d len) by (intros x Hx; apply Hrad; lia).
assert (HHULLl : shadow_hull_vis (aview segs (w_H W) memT) d len).
{ intros s Hs. apply Hhull. split; [lia|].
  assert (E1 : (d + len - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr in *.
  assert (E2 : (SHADOW_OFF + (d + len - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia. }
eapply SRr_mono.
{ apply (AP lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7]) T cval HEP).
  all: try fold len.
  - exact Hslo.
  - exact Hscr.
  - exact Ha0. - exact Ha1. - exact Ha2. - exact Hcv.
  - apply Forall_forall. intros r Hr. destruct (HCR r Hr) as (H1 & H2 & H3). lia.
  - apply Forall_forall. intros [x w] Hr. destruct (HCR (x, w) Hr) as (H1 & H2 & H3). cbn [fst snd] in *.
    apply HOUT; lia.
  - exact Hgw. - exact Hcw. - exact Hgc0. - lia. - exact Hgv0. - lia.
  - apply HOUT; lia. - apply HOUT; lia.
  - split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - cbn [length]. rewrite Hsp'. lia.
  - cbn [length]. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
  - exact (RtPFCmd.FR_cmd_intro _ _ f _ T fmt ps args HFMT Hparse Hargs Htext Hprec Hlit).
  - exact Hn. - exact HT. - exact Hd. - lia.
  - unfold RtPFShared.snp_out. rewrite HK, Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
  - exact HDEST. - exact HAMRl. - exact HRADl. - exact HHULLl.
  - unfold zdisjoint. cbn [fst snd]. lia.
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & H10 & Hby & Hfr & Hgr).
fold len in Hby, Hfr.
assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - 3 * ESTACK <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a H0 H1 H2. apply (Hfr a H0); [lia | rewrite HK, Hsp'; lia]. }
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact (fxrel_of_frm0 fx fx1 Hf1 Hf2)|].
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - 3 * ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hkeep a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hgr.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact H10|].
split.
{ intros i Hi. unfold PF.pf_bytes in Hi. rewrite length_map in Hi.
  assert (Hi' : 0 <= Z.of_nat i < len) by (unfold len, RtPFShared.sn_len, RtPFShared.sn_bytes; lia).
  rewrite (Hby (Z.of_nat i) Hi'), Nat2Z.id. f_equal. symmetry. apply pfb_unsigned_nth.
  apply Forall_app. split; [|repeat constructor; lia].
  apply Forall_forall. intros c Hc. rewrite Forall_forall in HTb. apply HTb.
  rewrite <- (firstn_skipn (Z.to_nat (n - 1)) T). apply in_or_app. left. exact Hc. }
split; [exact Hkeep|]. split; [exact Hgr | exact Hsame].
Qed.
End e.
End c.
