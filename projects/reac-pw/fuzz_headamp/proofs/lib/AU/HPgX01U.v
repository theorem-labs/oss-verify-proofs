(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v:120-122
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 6ebe35ba632; its three generic lemmas L_set_shadow_at, L_fresh and L_chain are kept as rx_set_shadow_at, rx_fresh and rx_chain (rx_set_shadow_at takes the kit's ajournal_after_write, which the strong shadow-fill text allows, in place of L_after_write_win), module paths changed to reac_pw.fuzz_role; the segment walk of reac-pw/fuzz_role's image A below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at c83d21158e9 for reac-pw/fuzz_headamp's
   image A: module paths changed to reac_pw.fuzz_headamp and the prefix rx_ renamed to hx_; kept: rx_chain,
   rx_rdword_of_val, rx_st_region, rx_chunk_zero, rx_reg_atom, rx_reg_ext, rx_reg_lit, rx_ew_reg, rx_flag0_of,
   rx_entry0, rx_jF, the tactics rx_atom, rx_lit, rx_ext, z5, z5g, rx_mach and the flag-store tactic rx_run_flag
   (the corrected local copy of the kit's aj_run_flag); rx_ffacts restated for the class-4 frame (1024 bytes, 128
   shadow bytes, flag pointer at F+0x3f8); rx_fresh, rx_regs, rx_regs_pres, rx_regs_run and rx_aview_same dropped;
   rx_set_shadow_at replaced by fuzz_identity's L_set_shadow_at and L_after_write_win
   (proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 2d2ff01bb6f, renamed
   hx_set_shadow_at and hx_after_write_win), whose journal step needs only the shadow-fill text of
   libreac/fuzz_boxreg's released lib/A/Rt/SetShadowDef.v; the step-keep lemma and the 8-byte read follow
   proofs/libreac/fuzz_disco/lib/A/Prog/ReacRateSnap.v (origin/ossv/recipes 2d2ff01bb6f) rs_step_keep and rs_rdn8;
   the walks of headamp's X01 (lib/A/HPgSegM.v hq_S_X01f_stmt and hq_S_X01r_stmt) are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgX01.v at e1724d81989 for reac-pw/fuzz_headamp's
   image B: the prefixes hx_ / HX_ / hq_ / HQ_ renamed to hxu_ / HXU_ / hqu_ / HQU_ (image B's lib/AU/HPgSegM.v), the
   record projections h_* to hu_*, the image modules to lib/AU (Img0U, HPgImgB, HPgMem, HPgSteps, HPgSeg,
   HPgSegM); the image-free lemmas are unchanged; every address, register, real-frame cell and shadow offset of the
   two walks is image B's own (measured below): the real frame is 0x220 bytes (image A 0x1e0), first / out sit in
   s7 / s6 and the pod and pp pointers are read from R+0x158 / R+0x148 (image A: s2 / s8 / s9 and R+0xf0), F sits in
   s5 and s7 (image A s10 and s6), res's granules are 84 and 85 of 116 (image A 48 and 49 of 80), and the epilogue
   restores four float registers (image A three). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the two pieces X01 of the walk of LLVMFuzzerTestOneInput (0x80c40), from C9 0x83950 (check_plain's
   return) to the return. Proves lib/AU/HPgSegM.v hqu_S_X01f_stmt and hqu_S_X01r_stmt at lib/AU/Img0U.v rsegs
   (kind: segment lemma). No numeral here is relocated from another image (alreloc maps 0 cells): every address
   is read from this image's own listing (capstone over the unstripped twin's .text, symbols from its .symtab).

   THE CODE (46 words 0x83950 .. 0x83a04, all 4-byte encodings):
     X01f (C9 0x83950 -> J 0x83980)
       0x83950 mv a0,s7;  0x83954 jal 0x530dc   free(first), ra 0x83958 (0x530dc = __wrap_free, the
                                                 4-byte trampoline of __interceptor_free 0x530e4)
       0x83958 mv a0,s6;  0x8395c jal 0x530dc   free(out), ra 0x83960
       0x83960 ld a0,0x158(s1); 0x83964 jal 0x530dc   free(pod) (the pod from the real-frame cell R+0x158), ra 0x83968
       0x83968 ld a0,0x148(s1); 0x8396c jal 0x530dc   free(pp) (pp from the real-frame cell R+0x148), ra 0x83970
       0x83970 addi a0,zero,-8; 0x83974 sb a0,0x54(s3); 0x83978 sb a0,0x55(s3)   res's two granules back to 0xf8
       0x8397c ld s7,0x18(s1)                    s7 = F (the cell R+0x18)
     X01r (J 0x83980 -> the return)
       0x83980 lui/addiw a0 = 0x45e0360e; 0x83988 sd a0,0(s5)   F[0] := the retirement word
       0x8398c beqz s7,0x839a8                   NOT taken: s7 = F >= 4096 (an atom fact), so the s7 = 0 arm with
                                                 the __asan_set_shadow_00 call at 0x839b0 is dead
       0x83990 addi a1,zero,0x80; 0x83994 mv a0,s3; 0x83998 jal 0x54d54   __asan_set_shadow_f5(shadow F, 128)
       0x8399c ld a0,0x3f8(s7); 0x839a0 sb zero,0(a0)   the flag byte of the class-4 frame := 0 (the release)
       0x839a4 j 0x839b4; 0x839b4 mv a0,zero; 0x839b8 addi sp,s0,-0x220; 13 restores 0x839bc .. 0x839ec
               (ra, s0, s1, s2 .. s11 from S-8 .. S-0x68); 0x839f0 .. 0x839fc fld fs0, fs1, fs2, fs3 from S-0x70,
               S-0x78, S-0x80, S-0x88; 0x83a00 addi sp,sp,0x220; 0x83a04 ret.
   The four frees go through the kit's aj_free_at (YCbq.v) with the allocator's afree_realizes, one generic site
   lemma (hxu_free_site) for the four; the shadow fill through hxu_set_shadow_at with libreac/fuzz_boxreg's
   shadow-fill text (ASHF5, at image B's entry 0x54d54); the flag store through hxu_run_flag (YCbq.v aj_flag_store,
   with astack_free_law_ok and the frame flag law), which drops the frame from the journal's own list; the symbolic
   engine stops at the first float load (it has no float instructions), the four loads are machine steps (YK0o.v
   fp_step_fld) and the engine resumes at the new float state for the last two words; the return through
   SRr_ret_at.
   Registers and real-frame cells used (image B's, from lib/AU/HPgImgB.v hi_L9 and lib/AU/HPgSegM.v hqu_cut_J):
   s0 = S, s1 = R, s3 = shadow F, s5 = F, s6 = out, s7 = first (then F), R+0x18 = F, R+0x148 = pp, R+0x158 = pod. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q YG0t YE00 YE01 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0s YO0f YK0o YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================ the image ============================================ *)
Definition HXU_NW : nat := 46.
Definition hxu_tbl : ctable := build_table rsegs HQU_C9 HXU_NW TEmpty.
Lemma hxu_tbl_ok : table_ok rsegs hxu_tbl.
Proof. apply build_table_ok0. unfold HQU_C9. lia. Qed.
Definition HXU_FREE : Z := 0x530dc.      (* the free wrapper's entry (the four `jal`s at 0x83954 .. 0x8396c) *)
Definition HXU_SSF5 : Z := 0x54d54.      (* __asan_set_shadow_f5 *)
Definition HXU_RA1 : Z := 0x83958.       (* free(first)'s return *)
Definition HXU_RA2 : Z := 0x83960.       (* free(out)'s return *)
Definition HXU_RA3 : Z := 0x83968.       (* free(pod)'s return *)
Definition HXU_RA4 : Z := 0x83970.       (* free(pp)'s return *)
Definition HXU_RA5 : Z := 0x8399c.       (* __asan_set_shadow_f5's return *)
Definition HXU_FLD : Z := 0x839f0.       (* the first of the four float loads *)

(* ======================================= generic lemmas ======================================= *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* ---- a journal step for a callee that writes some of its caller's own bytes and keeps only the stack
   window present (the set_shadow entries' contract states presence of its own window only). The proof is
   YCbq.v ajournal_after_write's, with the presence premise narrowed to the journal's window: that is the
   only place the original uses it. *)
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation ajournal := (ajournal segs B).
Local Notation sep_blocks := (YCbq.sep_blocks segs B LAWS).
Local Notation sep_block_frame := (YCbq.sep_block_frame segs B LAWS).
Local Notation blk_img := (YCbq.blk_img segs B LAWS).
Local Notation frm_img := (YCbq.frm_img segs B LAWS).
Local Notation frames_bounds := (YCbq.frames_bounds segs B LAWS).
Local Notation sep_frames_pos := (YCbq.sep_frames_pos segs B LAWS).
Local Notation awr_byte_cases := (YCbq.awr_byte_cases segs B LAWS).
Local Notation shadow_addr_bounds := YCbq.shadow_addr_bounds.
Local Notation shadow_range_end := YCbq.shadow_range_end.
Local Notation shadow_mono := YCbq.shadow_mono.
Lemma hxu_after_write_win : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
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
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
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
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
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
pose proof (fs_frame_bytes_nonneg cid) as Hfbn.
assert (Hfa1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
assert (Hfa2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfa1) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hfa2) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfbn) as Hse.
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
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (YG0p.AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
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

(* __asan_set_shadow_XX over a range of one of the caller's own side-stack frames' shadow, in journal form
   (cgif_rgb_fuzzer lib/YC05.v:206 aj_set_shadow_at, over this unit's journal). Its premise is libreac/fuzz_boxreg's
   released lib/A/Rt/SetShadowDef.v aset_shadow_realizes segs B pc v, written out (this unit holds no copy of that
   file yet). *)
Lemma hxu_set_shadow_at : forall pc v,
(forall ly S W regs mem md cid pos q n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a))) ->
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
aregs_preserved regsT regs2 /\ AR segs B lyc Sc W mem2 md2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfbn.
assert (Hfa1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
assert (Hfa2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfa1) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hfa2) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (hxu_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha Hna).
- intros a Ha Hp. eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | apply Hfr; zlia | exact Hp].
- exact Hsame.
- intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HAR2|]. split; [exact Heff | exact Hfr].
Qed.
End w.

(* The call chain at a call the entry makes from its own frame (identity's L_chain). *)
Lemma hxu_chain : forall ly (rd rdE : reader) (regsT : bvmap 5 word) sp0 mf ra s0e lyE,
spZ regsT = mf -> s0Z regsT = sp0 -> 4096 <= raZ regsT ->
alloc_ceiling <= mf -> mf + 16 <= sp0 -> sp0 mod 16 = 0 ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some s0e -> 4096 <= ra ->
achain lyE rdE sp0 s0e [] -> ly_top lyE = ly_top ly -> ly_top ly <= 2 ^ 47 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rdE a) ->
exists ch, chain_pre ly rd regsT ch /\ (ch = [] \/ exists fp v, ch = [(fp, ra, v)]).
Proof.
intros ly rd rdE regsT sp0 mf ra s0e lyE Hsp Hs0 Hra4 Hce Hmf Hal Hrd1 Hrd2 Hra Hach Etop Htop47 Hab.
unfold chain_pre.
destruct (frame0_ok ly regsT) eqn:Ef0.
2: { exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
destruct (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) eqn:Ebn.
{ exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
exists [(sp0, ra, s0e)]. split; [| right; exists sp0, s0e; reflexivity].
split; [exact Hra4|]. rewrite Hsp, Hs0. split; [lia|].
cbn [fpchain]. split; [reflexivity|].
split; [pose proof (Z.div_mod sp0 16 ltac:(lia)) as D; rewrite Hal, Z.add_0_r in D; rewrite D;
replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by lia; apply Z_mod_mult|].
split; [exact Hrd1|]. split; [exact Hrd2|]. split; [exact Hra|].
destruct (bad_next sp0 (ly_top ly) s0e) eqn:Ebn2; [reflexivity|].
unfold bad_next in Ebn2. apply Bool.orb_false_iff in Ebn2 as [Ebn2 E3]. apply Bool.orb_false_iff in Ebn2 as [E1 E2].
apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply Bool.negb_false_iff in E3. apply Z.eqb_eq in E3.
unfold achain in Hach. destruct Hach as [(Hbad & _) | (Hlo & Hhi & Hal8 & Hfp & _)].
- exfalso. rewrite Etop in Hbad. lia.
- cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hrr). exists r. split; [|exact Hrr].
rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hab. rewrite Etop in Hhi. clear - Hlo Hhi Hkk Htop47. lia.
Qed.

(* the 8 bytes of a cell, read back as a word *)
Lemma hxu_rdword_of_val : forall segs H mem a v, 0 <= v < 2 ^ 64 ->
val_mem segs (mrestrict H mem) a 8 v -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hm.
assert (A : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YO0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hm k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
pose proof (A 0%nat ltac:(lia)) as A0. pose proof (A 1%nat ltac:(lia)) as A1. pose proof (A 2%nat ltac:(lia)) as A2.
pose proof (A 3%nat ltac:(lia)) as A3. pose proof (A 4%nat ltac:(lia)) as A4. pose proof (A 5%nat ltac:(lia)) as A5.
pose proof (A 6%nat ltac:(lia)) as A6. pose proof (A 7%nat ltac:(lia)) as A7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in A0, A1, A2, A3, A4, A5, A6, A7. rewrite Z.add_0_r in A0.
rewrite A0, A1, A2, A3, A4, A5, A6, A7. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.
(* the 8 bytes of a cell, as the list a float load reads (fuzz_disco's rs_bytes / rs_rdn8) *)
Definition hxu_bytes (v : Z) : list byte := map (fun k => Z_to_bv 8 (YO0f.le_byte v 8 k)) (seq 0 8).
Lemma hxu_rdn8 : forall segs m a v, val_mem segs m a 8 v -> rdn segs m (Z_to_bv 64 a) 8 = Some (hxu_bytes v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (hxu_bytes v)).
intros j Hj. cbn [length hxu_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error hxu_bytes map seq]; apply H; lia.
Qed.
(* a region of the symbolic state is ok for the machine's memory *)
Lemma hxu_st_region : forall segs E ss ms r, st_ok segs E ss ms -> In r (ss_mem ss) -> region_ok segs E (ms_mem ms) r.
Proof.
intros segs E ss ms r (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _) Hin.
exact (proj1 (Forall_forall _ _) Hok r Hin).
Qed.
(* the byte a chunk holding the literal 0 shows *)
Lemma hxu_chunk_zero : forall segs E m base off n,
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal n (SLit 0))) -> (1 <= n)%N ->
mbyte segs m (base + off) = Some (Z_to_bv 8 0).
Proof.
intros segs E m base off n Hc Hn. destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hm, Hb. rewrite !Z.add_0_r in Hm. rewrite Hm. injection Hb as <-.
first [reflexivity | f_equal; vm_compute; reflexivity].
Qed.
(* the byte a one-byte chunk holding -8 (the store `sb a0` with a0 = -8) shows: 0xf8 *)
Lemma hxu_chunk_f8 : forall segs E m base off,
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 (SLit 18446744073709551608))) ->
mbyte segs m (base + off) = Some (Z_to_bv 8 248).
Proof.
intros segs E m base off Hc. destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hm, Hb. rewrite !Z.add_0_r in Hm. rewrite Hm. injection Hb as <-.
first [reflexivity | f_equal; vm_compute; reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity].
Qed.
(* a register the run did not touch, or a literal, or an extra atom *)
Lemma hxu_reg_atom : forall segs E ss ms H regs extra (r r' : bv 5) (n : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros segs E ss ms H regs extra r r' n HS -> Hg Hn. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
(* the registers of a list the run did not touch *)
Lemma hxu_regs_keepL : forall segs ss ms H regs extra (l : list Z),
st_ok segs (Ereg regs extra) ss (restrict H ms) ->
forallb (fun k : Z => (0 <=? k) && (k <? 32) && sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 k)) (SOff (Z.to_nat k) 0)) l = true ->
forall r, In r l -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros segs ss ms H regs extra l HS Hck r Hin.
pose proof (proj1 (forallb_forall _ _) Hck r Hin) as Hq. cbn beta in Hq.
apply andb_prop in Hq as [Hq Hq3]. apply andb_prop in Hq as [Hq1 Hq2].
apply Z.leb_le in Hq1. apply Z.ltb_lt in Hq2. apply sv_eqb_eq in Hq3.
apply (hxu_reg_atom segs _ ss ms H regs extra _ _ (Z.to_nat r) HS eq_refl Hq3).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma hxu_regs_keep : forall segs ss ms H regs extra,
st_ok segs (Ereg regs extra) ss (restrict H ms) ->
forallb (fun k : Z => (0 <=? k) && (k <? 32) && sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 k)) (SOff (Z.to_nat k) 0))
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
forall r, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros segs ss ms H regs extra HS Hck r Hr.
apply (hxu_regs_keepL segs ss ms H regs extra _ HS Hck r).
unfold acallee_saved in Hr. cbv [In]. lia.
Qed.
Lemma hxu_reg_ext : forall segs E ss ms H regs extra (r : bv 5) (j : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros segs E ss ms H regs extra r j HS -> Hg. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs extra j).
Qed.
Lemma hxu_reg_lit : forall segs E ss ms H (r : bv 5) z,
st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros segs E ss ms H r z HS Hg. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg. reflexivity. Qed.
Lemma hxu_ew_reg : forall regs extra (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
bv_unsigned (ew (Ereg regs extra) n) = bv_unsigned (getr regs r).
Proof. intros regs extra n r Hn. rewrite (ew_Ereg_nat regs extra n r Hn). reflexivity. Qed.
(* the fresh symbolic state of a cut or a call return with no region *)
Lemma hxu_entry0 : forall pc (W : world rsegs) regs mem,
st_ok rsegs (Ereg regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
(* the flag byte after `sb zero,0(a0)` *)
Lemma hxu_flag0_of : forall segs E ss ms n,
st_ok segs E ss ms -> In (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) (ss_mem ss) ->
mbyte segs (ms_mem ms) (bv_unsigned (ew E n)) = Some (Z_to_bv 8 0).
Proof.
intros segs E ss ms n HS Hin. pose proof (hxu_st_region segs E ss ms _ HS Hin) as (_ & _ & _ & Hc).
cbn [YP09.r_chunks YP09.r_base base_val] in Hc. inversion Hc as [|c l Hc0 _]; subst.
rewrite <- (Z.add_0_r (bv_unsigned (ew E n))). exact (hxu_chunk_zero segs E _ _ 0 1 Hc0 ltac:(lia)).
Qed.
End a.

(* one machine step that keeps the memory, under the journal (fuzz_disco's rs_step_keep): the float loads *)
Lemma hxu_step_keep : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} segs B (Hwx : wx_segs_nowrap segs) (LAWS : AR_laws segs B)
  (Hsl : forall a, in_img segs a -> 0 <= a < kLowMemEnd)
  (W : world segs) (f f' : YK11.FPState) R R' pc pc' mem md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k,
  RiscvSemantics.step segs (@mkst f R pc (mrestrict (w_H W) mem) (seg_rom segs)) =
    MachineOk (@mkst f' R' pc' (mrestrict (w_H W) mem) (seg_rom segs)) ->
  ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md k ->
  (forall md', ajournal segs B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W mem md' k ->
     SRr segs W (mkCfg (@mkst f' R' pc' mem (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (@mkst f R pc mem (seg_rom segs)) md) Q.
Proof.
intros rc SK segs B Hwx LAWS Hsl W f f' R R' pc pc' mem md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ Hk.
eapply (SRr_step segs Hwx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply Hk. apply (ajournal_materialize segs B LAWS Hsl). exact HJ.
Qed.
(* the symbolic state with no region at another float state, from a state ok at the old one (the registers and
   the memory are the same): the engine resumes after the float loads *)
Lemma hxu_switch : forall segs (f f' : YK11.FPState) E ss ms (H : word -> bool) pc',
  @st_ok segs f E ss (restrict H ms) ->
  @st_ok segs f' E (mkSS pc' (ss_regs ss) [] None (mkFacts [] [] []))
    (restrict H (@mkst f' (ms_regs ms) (Z_to_bv 64 pc') (ms_mem ms) (seg_rom segs))).
Proof.
intros segs f f' E ss ms H pc' HS.
destruct HS as (_ & _ & _ & _ & _ & _ & Hr & _ & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|].
split; [split; [reflexivity | split; [apply Forall_nil | cbn; exact I]]|].
split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
Lemma hxu_pc4 : forall p, 0 <= p < 2 ^ 60 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros p Hp. unfold v_addi. rewrite unsigned_lit_small by lia. reflexivity. Qed.

(* the value of a register after a run, from the symbolic state *)
Ltac hxu_atom HS r r' H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (hxu_reg_atom segs (Ereg rg ex) ss ms Hh rg ex r r' n HS eq_refl); vm_compute; reflexivity) end end.
Ltac hxu_lit HS r H :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SLit ?z =>
assert (H : getr (ms_regs ms) r = Z_to_bv 64 z)
  by (apply (hxu_reg_lit segs E ss ms Hh r z HS); vm_compute; reflexivity) end end.
(* a register index as the numeral the kit's texts write (getr regs 2, ...) *)
Ltac z5 H := repeat match type of H with context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) in H by (apply bv_eq; reflexivity) end.
Ltac z5g := repeat match goal with |- context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) by (apply bv_eq; reflexivity) end.
Ltac hxu_mach HS m := lazymatch type of HS with st_ok _ _ _ (restrict _ ?x) => rename x into m end.
Ltac hxu_ext HS r H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
let j := eval vm_compute in (n - 32)%nat in
assert (H : getr (ms_regs ms) r = nth j ex (Z_to_bv 64 0))
  by (apply (hxu_reg_ext segs (Ereg rg ex) ss ms Hh rg ex r j HS eq_refl); vm_compute; reflexivity) end end.
(* the flag-store run (YCbq.v aj_flag_store), applied with its sixteen journal arguments *)
Ltac hxu_run_flag HS HJ HL Hsegs ML Hwx HASF FFL :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN segs hxu_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs hxu_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (aj_flag_store segs _ HL Hsegs ML hxu_tbl hxu_tbl_ok Hwx HASF FFL W FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ] end end.
(* the release's symbolic state: the 13 saves at S-8 .. S-0x68 (atom 33 + j = the entry's j-th saved register,
   atom 32 = the flag address) *)
Definition hxu_sv_chunks : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + Nat.succ j) 0))) (seq 0 13).
Definition hxu_X7 (fl : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs r) hqu_saved_regs.

(* ======================================= the frame's shadow at J =======================================
   res's two granules are 84 and 85 (res at F+0x2a0); headamp_B_shB differs from the prologue's pattern there only *)
Lemma hxu_shA_len : length headamp_B_shA = 116%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma hxu_shA_f8 : nth 84 headamp_B_shA 0 = 248 /\ nth 85 headamp_B_shA 0 = 248.
Proof. split; vm_compute; reflexivity. Qed.
Lemma hxu_shA_shB : forall i, (i < 116)%nat -> i <> 84%nat -> i <> 85%nat -> nth i headamp_B_shA 0 = nth i headamp_B_shB 0.
Proof.
intros i Hi H84 H85.
do 116 (destruct i as [|i]; [first [vm_compute; reflexivity | exfalso; lia] |]). lia.
Qed.

(* ======================================= the segment ======================================= *)
Section m. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the allocator's laws and its free operation (at every float state: the harness reaches X01 at the float state
   M04b returns at), the side stack's flag law, the shadow fill at 0x54d54 (libreac/fuzz_boxreg's released
   lib/A/Rt/SetShadowDef.v aset_shadow_realizes rsegs B 0x54d54 0xf5, written out, at every float state), the
   image's free entry and the call traces of the four free sites, the harness's stack and event budgets *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc rsegs B.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASHF5 : forall fx : YK11.FPState,
forall ly S W regs mem md cid pos q n,
ecall_pre rsegs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr rsegs W (@cfg_at fx rsegs 0x54d54 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = @cfg_at fx rsegs (raZ regs) regs' mem' md' /\
AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem' (q + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Hypothesis HFREE : pc_wrap_free (as_code B) = HXU_FREE.
Hypothesis HTRACE : forall c, In c [[HXU_RA1]; [HXU_RA1; RA_LLVMF]; [HXU_RA2]; [HXU_RA2; RA_LLVMF];
  [HXU_RA3]; [HXU_RA3; RA_LLVMF]; [HXU_RA4]; [HXU_RA4; RA_LLVMF]] ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
(as_universe B).
Hypothesis HSTK : ASTACK + 0x230 <= LLVMF_STK.
Hypothesis HEV : HQU_EV <= EV_LIB.

(* every journal from the entry keeps ly_F, so a frame's and its flag's addresses are the entry layout's *)
Lemma hxu_jF : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
frame_addr ly' c q = frame_addr ly c q /\ flag_addr ly' c q = flag_addr ly c q.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* the frame for locals (class 4, 1024 bytes, 128 shadow bytes) and its flag at a state of the journal *)
Lemma hxu_ffacts : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> In (4, pos) (frames S') ->
frame_addr ly 4 pos mod 32 = 0 /\ in_app (frame_addr ly 4 pos) 1024 /\
4096 <= frame_addr ly 4 pos /\ frame_addr ly 4 pos + 1024 <= alloc_ceiling /\
(forall a, frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024 -> apresent (w_H W') mem' a /\ ~ aowned B ly' S' a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W') mem' (shadow_addr (frame_addr ly 4 pos) + i)) /\
apresent (w_H W') mem' (flag_addr ly 4 pos) /\ aowned B ly' S' (flag_addr ly 4 pos) /\
4096 <= flag_addr ly 4 pos < alloc_ceiling.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos HJ Hin.
pose proof (AR_laws_ok rsegs B) as HL. pose proof (proj1 HJ) as HAR.
destruct (hxu_jF STK sp0 FP ly S W mem md own ly' S' W' mem' md' k 4 pos HJ) as [EFA EFL].
destruct (al_frames _ _ HL _ _ _ _ _ 4 pos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B HL _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 4 pos HAR Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLceil)).
rewrite EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. rewrite EFL in HFLp, HFLo, HFL4096, HFLceil.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
split; [exact HFal|]. split; [exact HFapp|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFpres|]. split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
split; [exact HFLp|]. split; [exact HFLo|]. lia.
Qed.

(* the shadow of the frame lies between the low application memory and the high one, below the side stack *)
Lemma hxu_shF_bounds : forall F, 4096 <= F -> F + 1024 <= alloc_ceiling ->
0x7fff8000 + 512 <= shadow_addr F /\ shadow_addr F + 128 < 0x10007fff8000 /\ shadow_addr F + 128 < alloc_ceiling.
Proof.
intros F H1 H2. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold shadow_addr, SHADOW_OFF. set (q := F / 8) in *. set (r := F mod 8) in *. lia.
Qed.
Lemma hxu_sh_apart : forall F i lo len, 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= i < 128 ->
in_app lo len -> ~ (lo <= shadow_addr F + i < lo + len).
Proof.
intros F i lo len H1 H2 H3 Happ. destruct (hxu_shF_bounds F H1 H2) as (B1 & B2 & B3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
Qed.

(* The geometry at a harness cut: S, R and F with their bounds, the frame in the journal's frames. *)
Lemma hxu_geo : forall (hx : hqu_hcx rsegs) pos e ly S W mem md k,
hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
hqu_geo rsegs hx pos e ->
hqu_j rsegs B LLVMF_STK hx [(HQU_CID, pos)] ly S W mem md k ->
e_S e mod 16 = 0 /\ alloc_ceiling + ASTACK + 0x230 <= e_S e <= 2 ^ 47 /\
e_R e mod 16 = 0 /\ e_S e - 0x230 <= e_R e <= e_S e - 0x220 /\
e_F e mod 32 = 0 /\ in_app (e_F e) 1024 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\
In (4, pos) (frames S).
Proof.
intros hx pos e ly S W mem md k HB HG HJ.
destruct hx as [lyE SE WE regsE memE mdE p n pl].
unfold hqu_base in HB. unfold hqu_j in HJ. unfold hqu_geo in HG.
cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl] in HB, HJ, HG.
destruct HG as (ES & ER & EF).
destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & Hfr0 & _ & _ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold HQU_CID, HQU_RSZ in *.
assert (Hfin : In (4, pos) (frames S)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs, Hfr0. left. reflexivity. }
destruct (hxu_ffacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ Hfin) as (HFal & HFapp & HF4096 & HFceil & _).
rewrite <- EF in HFal, HFapp, HF4096, HFceil.
rewrite <- ES in Hal16, Hslo, Hshi.
assert (HR : e_R e mod 16 = 0 /\ e_S e - 0x230 <= e_R e <= e_S e - 0x220).
{ rewrite ER.
  pose proof (Z.div_mod (e_S e - 544) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (e_S e - 544) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (e_S e) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  set (q := (e_S e - 544) / 32) in *. set (r := (e_S e - 544) mod 32) in *. set (u := e_S e / 16) in *.
  split; [replace (32 * q) with ((2 * q) * 16) by lia; apply Z_mod_mult | lia]. }
destruct HR as (HR16 & HRb).
split; [exact Hal16|]. split; [lia|]. split; [exact HR16|]. split; [exact HRb|].
split; [exact HFal|]. split; [exact HFapp|]. split; [exact HF4096|]. split; [exact HFceil|]. exact Hfin.
Qed.

(* the carried cells (the thirteen saves, the four float saves, the flag-pointer word) survive any memory change
   that keeps [S - 0x88, S) and [F + 0x3f8, F + 0x400) *)
Lemma hxu_kept_mono : forall (hx : hqu_hcx rsegs) pos e W mem regs W' mem' regs',
(forall a, e_S e - 0x88 <= a < e_S e -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
(forall a, e_F e + 0x3f8 <= a < e_F e + 0x400 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
hqu_kept rsegs hx pos e W mem regs -> hqu_kept rsegs hx pos e W' mem' regs'.
Proof.
intros hx pos e W mem regs W' mem' regs' KS KF (HKF & HFS).
unfold hqu_kept, hqu_cells in *. apply Forall_app in HKF as [HKS HKL]. split.
- apply Forall_app. split.
  + unfold hqu_saves_L in HKS |- *. rewrite Forall_map in HKS |- *. rewrite Forall_forall in HKS |- *.
    intros j Hj. pose proof (HKS j Hj) as X. apply in_seq in Hj. cbn [fst snd hd_at hd_xv] in X |- *.
    apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact X].
    intros q Hq. apply KS. change (Z.of_nat 8) with 8 in Hq. lia.
  + apply Forall_cons_iff in HKL as [X _]. apply Forall_cons; [|apply Forall_nil].
    cbn [fst snd hd_at hd_xv] in X |- *.
    apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact X].
    intros q Hq. apply KF. unfold HQU_FLAG. change (Z.of_nat 8) with 8 in Hq. lia.
- destruct HFS as (v0 & v1 & v2 & v3 & A0 & A1 & A2 & A3). exists v0, v1, v2, v3.
  cbn [hd_at hd_xv] in A0, A1, A2, A3 |- *.
  split; [|split; [|split]].
  + apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact A0].
    intros q Hq. apply KS. change (Z.of_nat 8) with 8 in Hq. lia.
  + apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact A1].
    intros q Hq. apply KS. change (Z.of_nat 8) with 8 in Hq. lia.
  + apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact A2].
    intros q Hq. apply KS. change (Z.of_nat 8) with 8 in Hq. lia.
  + apply (val_mem_kept rsegs (w_H W) (w_H W') mem mem'); [|exact A3].
    intros q Hq. apply KS. change (Z.of_nat 8) with 8 in Hq. lia.
Qed.

(* C9's values survive a call that keeps the callee-saved registers and the real-frame cells [R, R + 0x160) *)
Lemma hxu_L9_kept : forall e (W : world rsegs) mem regs (W' : world rsegs) mem' regs',
(forall r, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall a, e_R e <= a < e_R e + 0x160 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
hd_cut rsegs (w_H W) mem regs e (hi_L9 headamp_himg_B) -> hd_cut rsegs (w_H W') mem' regs' e (hi_L9 headamp_himg_B).
Proof.
intros e W mem regs W' mem' regs' HR HM HC.
apply (hm_cut_kept rsegs _ _ _ _ _ _ _ _ HC).
intros f Hf. cbn [hi_L9 headamp_himg_B In] in Hf.
destruct Hf as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst hm_keeps hd_xv];
first [apply HR; unfold acallee_saved; lia | intros i Hi; apply HM; lia].
Qed.

(* ---- one free site: from a cut with the blocks bl0 ++ [(pa, nb)] live, at the free wrapper's entry with a0 = pa,
   to the return address with the blocks bl0 and one more event ---- *)
Lemma hxu_free_site : forall (hx : hqu_hcx rsegs) (fx2 : YK11.FPState) pos e k bl0 pa nb
  ly1 S1 W1 regs1 mem1 md1 regsT ret,
hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
hqu_at_cut rsegs B LLVMF_STK hx pos e k (bl0 ++ [(pa, nb)]) (hi_L9 headamp_himg_B) (hi_shB headamp_himg_B)
  ly1 S1 W1 regs1 mem1 md1 ->
0 <= nb -> k < HQU_EV ->
getr regsT 10 = w64 pa -> getr regsT 1 = w64 ret -> 4096 <= ret < 2 ^ 47 -> ret mod 2 = 0 ->
(forall r, acallee_saved r -> getr regsT (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) [ret]))
  (as_universe B) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r])
  [ret; RA_LLVMF])) (as_universe B) ->
SRr rsegs W1 (mkCfg (@mkst fx2 regsT (Z_to_bv 64 HXU_FREE) mem1 (seg_rom rsegs)) md1)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = @cfg_at fx2 rsegs ret regs2 mem2 md2 /\
    hqu_at_cut rsegs B LLVMF_STK hx pos e (k + 1) bl0 (hi_L9 headamp_himg_B) (hi_shB headamp_himg_B)
      ly2 S2 W2 regs2 mem2 md2).
Proof.
intros hx fx2 pos e k bl0 pa nb ly1 S1 W1 regs1 mem1 md1 regsT ret HB HA Hnb HkE Ha0 Hra1 Hret Hret2 HT HTR1 HTR2.
pose proof (AR_laws_ok rsegs B) as HL. pose proof img_segs_low as Hsegs.
pose proof HA as (HJ0 & _ & _ & _ & _ & _ & HG0 & _).
destruct (hxu_geo hx pos e _ _ _ _ _ _ HB HG0 HJ0) as (HS16 & HSb & HR16 & HRb & HFal & HFapp & HF4096 & HFceil & Hfin).
clear HJ0 HG0.
destruct hx as [lyE SE WE regsE memE mdE p n pl].
unfold hqu_base in HB. unfold hqu_at_cut, hqu_j, hqu_geo in HA.
cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl] in HB, HA |- *.
destruct HB as (HPRE & Hra & _ & _ & _ & _ & _ & Hfr0 & Hev0 & _ & _).
destruct HA as (HJ & HPerm & Hfresh & R2 & R3 & R4 & (ES & ER & EF) & HCUT & Hfsh & HKEPT).
pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
unfold HQU_CID, HQU_RSZ, HQU_EV in *.
set (S0 := spZ regsE) in *.
rewrite ES in HS16, HSb, HRb.
set (F := e_F e) in *. set (R := e_R e) in *.
assert (Ho16 : (R - S0) mod 16 = 0) by (rewrite Zminus_mod, HR16, HS16; reflexivity).
(* ---- the block and the frame ---- *)
assert (Hin1 : In (pa, nb) (ablocks B ly1 S1)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
apply Forall_app in Hfresh as [Hfresh0 Hfresh1]. apply Forall_cons_iff in Hfresh1 as [[Hnpa _] _].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ HL ly1 S1 W1 mem1 md1 pa nb HAR1 Hin1) as (Hpa16 & Hpa4096 & Hpaceil & Hpapp & Hpab & _).
pose proof (req_size_pos nb Hnb) as Hrq.
destruct (hxu_jF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ) as [EFA _]. rewrite <- EF in EFA.
pose proof (sep_block_frame rsegs B HL ly1 S1 W1 mem1 md1 pa nb 4 pos HAR1 Hin1 Hfin) as Hdpa.
rewrite EFA in Hdpa. unfold zdisjoint in Hdpa. cbn [fst snd] in Hdpa. change (fs_frame_bytes 4) with 1024 in Hdpa.
(* ---- the registers at the call ---- *)
pose proof HCUT as HC'. unfold hd_cut in HC'. cbn [hi_L9 headamp_himg_B] in HC'. rewrite !Forall_cons_iff in HC'.
destruct HC' as (C8 & _). cbn [fst snd hd_at hd_xv] in C8. rewrite ES in C8.
pose proof (HT 2 ltac:(unfold acallee_saved; lia)) as T2. z5 T2.
pose proof (HT 3 ltac:(unfold acallee_saved; lia)) as T3. z5 T3.
pose proof (HT 4 ltac:(unfold acallee_saved; lia)) as T4. z5 T4.
pose proof (HT 8 ltac:(unfold acallee_saved; lia)) as T8. z5 T8. z5 C8.
assert (EspT : spZ regsT = R) by (unfold spZ; rewrite T2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Es0T : s0Z regsT = S0) by (unfold s0Z; rewrite T8, C8; unfold w64; apply unsigned_lit_small; lia).
assert (EraT : raZ regsT = ret) by (unfold raZ; rewrite Hra1; unfold w64; apply unsigned_lit_small; lia).
(* ---- the saves read back as words (the chain) ---- *)
pose proof HKEPT as (HKF & _). unfold hqu_cells in HKF. apply Forall_app in HKF as [HKS _].
assert (HSV : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W1) mem1) (S0 + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr regsE (nth j hqu_saved_regs 0%bv)))).
{ intros j Hj. unfold hqu_saves_L in HKS. rewrite Forall_map in HKS.
  pose proof (proj1 (Forall_forall _ _) HKS j ltac:(apply in_seq; lia)) as X. cbn [fst snd hd_at hd_xv] in X.
  rewrite ES in X. rewrite Z.mod_small in X; [exact X|]. pose proof (bv_unsigned_in_range 64 (getr regsE (nth j hqu_saved_regs 0%bv))) as Y.
  change (bv_modulus 64) with (2 ^ 64) in Y. exact Y. }
pose proof (bv_unsigned_in_range 64 (getr regsE 1)) as Hra64. change (bv_modulus 64) with (2 ^ 64) in Hra64.
pose proof (bv_unsigned_in_range 64 (getr regsE 8)) as Hs064. change (bv_modulus 64) with (2 ^ 64) in Hs064.
assert (HRD1 : rdword (aview rsegs (w_H W1) mem1) (S0 - 8) = Some (raZ regsE)).
{ apply hxu_rdword_of_val; [unfold raZ; lia|].
  pose proof (HSV 0%nat ltac:(lia)) as X. replace (S0 + (-8 - 8 * Z.of_nat 0)) with (S0 - 8) in X by lia. exact X. }
assert (HRD2 : rdword (aview rsegs (w_H W1) mem1) (S0 - 16) = Some (s0Z regsE)).
{ apply hxu_rdword_of_val; [unfold s0Z; lia|].
  pose proof (HSV 1%nat ltac:(lia)) as X. replace (S0 + (-8 - 8 * Z.of_nat 1)) with (S0 - 16) in X by lia. exact X. }
pose proof HJ as (_ & Hly1 & _). destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _).
destruct (hxu_chain ly1 (aview rsegs (w_H W1) mem1) (aview rsegs (w_H WE) memE) regsT S0 R (raZ regsE) (s0Z regsE) lyE
  EspT Es0T ltac:(rewrite EraT; lia) ltac:(lia) ltac:(lia) HS16 HRD1 HRD2 Hra4 Hch0
  ltac:(symmetry; exact Etop1) ltac:(rewrite Etop1; lia)) as (ch & Hch & Hchs).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & _). apply J1; lia. }
(* ---- free(pa) ---- *)
eapply SRr_mono.
{ replace (Z_to_bv 64 HXU_FREE) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HFREE; reflexivity).
  eapply (aj_free_at (fx := fx2) rsegs B HL Hsegs HAPI ML (AFREE fx2) W1 regsT mem1 LLVMF_STK S0 [] lyE SE WE memE mdE
    [(4, pos)] ly1 S1 md1 k pa nb (R - S0) (w64 ret) ch HJ).
  - exact Hin1.
  - exact Ha0.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - rewrite T3. exact R3.
  - rewrite T4. exact R4.
  - exact Hra1.
  - apply ret_ok_even. unfold w64. rewrite unsigned_lit_small by lia. exact Hret2.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
  - exact Hch.
  - rewrite call_trace_of_spine, EraT. destruct Hchs as [-> | (fp & v & ->)]; [exact HTR1 | rewrite Hra; exact HTR2].
  - intros Hin. exfalso. exact (Hnpa Hin). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfrs2 & HK2).
destruct HK2 as (K1 & _ & _ & K4 & _ & _).
exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at; reflexivity|].
unfold hqu_at_cut, hqu_j, hqu_geo. cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md].
split; [exact HJ2|].
split.
{ rewrite E2. rewrite E1 in HPerm.
  replace (ablocks B lyE SE ++ bl0 ++ [(pa, nb)]) with ((ablocks B lyE SE ++ bl0) ++ (pa, nb) :: []) in HPerm
    by (rewrite <- app_assoc; reflexivity).
  rewrite <- (app_nil_r (ablocks B lyE SE ++ bl0)). exact (Permutation_app_inv l1 l2 _ [] (pa, nb) HPerm). }
split; [exact Hfresh0|].
pose proof (HP2 2 ltac:(unfold acallee_saved; lia)) as P2. z5 P2.
pose proof (HP2 3 ltac:(unfold acallee_saved; lia)) as P3. z5 P3.
pose proof (HP2 4 ltac:(unfold acallee_saved; lia)) as P4. z5 P4.
split; [rewrite P2, T2; exact R2|].
split; [rewrite P3, T3; exact R3|].
split; [rewrite P4, T4; exact R4|].
split; [split; [exact ES | split; [exact ER | exact EF]]|].
split.
{ apply (hxu_L9_kept e W1 mem1 regs1 W2 mem2 regs2); [| |exact HCUT].
  - intros r Hr. rewrite (HP2 r Hr). exact (HT r Hr).
  - intros a Ha. apply K1; lia. }
split.
{ apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
  change (hi_shB headamp_himg_B) with headamp_B_shB in Hi. rewrite hqu_shB_len in Hi.
  apply (K4 4 pos); [exact Hfin | right; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4 / 8) with 128; lia |].
  cbv beta. intros Hx. exact (hxu_sh_apart F i pa (req_size nb) HF4096 HFceil ltac:(lia) Hpapp Hx). }
apply (hxu_kept_mono _ pos e W1 mem1 regs1 W2 mem2 regs2); [| |exact HKEPT].
- intros a Ha. rewrite ES in Ha. apply K1; lia.
- intros a Ha. apply (K4 4 pos); [exact Hfin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4) with 1024; lia |].
  cbv beta. lia.
Qed.

(* ====================================== X01f: C9 -> J ====================================== *)
Theorem hxu_S_X01f : hqu_S_X01f_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold hqu_S_X01f_stmt.
intros hx fx2 pos e ly S W regs mem md HB HC.
destruct HC as (HA & Hfrm & Hcap & Hlen).
pose proof (AR_laws_ok rsegs B) as HL. pose proof img_segs_low as Hsegs. pose proof img_wx as Hwx.
assert (Has : ASTACK = 16384) by reflexivity.
(* ---- site 1: 0x83950 mv a0,s7; 0x83954 jal free(first) ---- *)
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & HC9 & _).
unfold hd_cut in HC9. cbn [hi_L9 headamp_himg_B] in HC9. rewrite !Forall_cons_iff in HC9.
destruct HC9 as (_ & _ & _ & _ & _ & C23 & _). cbn [fst snd hd_at hd_xv] in C23.
unfold cfg_at. change (w64 HQU_C9) with (Z_to_bv 64 HQU_C9).
pose proof (hxu_entry0 (fx := fx2) HQU_C9 W regs mem) as HS.
pose proof (proj1 HA) as HJ. unfold hqu_j in HJ.
aj_run hxu_tbl_ok HS HJ.
{ apply awr_ok_nil. }
hxu_mach HS msA.
assert (EmA : ms_mem msA = mem) by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); cbn in Hr; destruct Hr).
clear HF HFr HG.
hxu_atom HS (10%bv : bv 5) (Z_to_bv 5 23) Ra0. rewrite C23 in Ra0.
hxu_lit HS (1%bv : bv 5) Rra.
pose proof (hxu_regs_keep rsegs _ msA (w_H W) regs [] HS ltac:(vm_compute; reflexivity)) as RKA.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msA HS eq_refl). cbn [ss_pc]. rewrite EmA. rewrite EmA in HJ.
change (Z_to_bv 64 340188) with (Z_to_bv 64 HXU_FREE).
eapply SRr_bind.
{ eapply (hxu_free_site hx fx2 pos e 4 (hqu_blocks5 e) (e_first e) (hd_xv e XRc3NZ) ly S W regs mem _ (ms_regs msA) HXU_RA1 HB).
  - exact (conj HJ (proj2 HA)).
  - cbn [hd_xv]. destruct (3 * Z.max (e_rc e) 0 =? 0); lia.
  - unfold HQU_EV. lia.
  - exact Ra0.
  - exact Rra.
  - unfold HXU_RA1. lia.
  - reflexivity.
  - exact RKA.
  - apply HTRACE. cbn [In]. left. reflexivity.
  - apply HTRACE. cbn [In]. right. left. reflexivity. }
cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HA1).
clear HS HJ RKA Ra0 Rra EmA msA.
(* ---- site 2: 0x83958 mv a0,s6; 0x8395c jal free(out) ---- *)
pose proof HA1 as (_ & _ & _ & _ & _ & _ & _ & HC1 & _).
unfold hd_cut in HC1. cbn [hi_L9 headamp_himg_B] in HC1. rewrite !Forall_cons_iff in HC1.
destruct HC1 as (_ & _ & _ & _ & C22 & _). cbn [fst snd hd_at hd_xv] in C22.
unfold cfg_at. change (w64 HXU_RA1) with (Z_to_bv 64 HXU_RA1).
pose proof (hxu_entry0 (fx := fx2) HXU_RA1 W1 regs1 mem1) as HS.
pose proof (proj1 HA1) as HJ. unfold hqu_j in HJ.
aj_run hxu_tbl_ok HS HJ.
{ apply awr_ok_nil. }
hxu_mach HS msB.
assert (EmB : ms_mem msB = mem1) by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); cbn in Hr; destruct Hr).
clear HF HFr HG.
hxu_atom HS (10%bv : bv 5) (Z_to_bv 5 22) Rb0. rewrite C22 in Rb0.
hxu_lit HS (1%bv : bv 5) Rrb.
pose proof (hxu_regs_keep rsegs _ msB (w_H W1) regs1 [] HS ltac:(vm_compute; reflexivity)) as RKB.
rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ msB HS eq_refl). cbn [ss_pc]. rewrite EmB. rewrite EmB in HJ.
change (Z_to_bv 64 340188) with (Z_to_bv 64 HXU_FREE).
eapply SRr_bind.
{ eapply (hxu_free_site hx fx2 pos e (4 + 1) [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)] (e_out e) (3 * (e_cap e + 1))
    ly1 S1 W1 regs1 mem1 _ (ms_regs msB) HXU_RA2 HB).
  - exact (conj HJ (proj2 HA1)).
  - lia.
  - unfold HQU_EV. lia.
  - exact Rb0.
  - exact Rrb.
  - unfold HXU_RA2. lia.
  - reflexivity.
  - exact RKB.
  - apply HTRACE. cbn [In]. right. right. left. reflexivity.
  - apply HTRACE. cbn [In]. right. right. right. left. reflexivity. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HA2).
clear HS HJ RKB Rb0 Rrb EmB msB.
(* ---- site 3: 0x83960 ld a0,0x158(s1); 0x83964 jal free(pod) ---- *)
pose proof HA2 as (HJ2 & HPerm2 & _ & _ & _ & _ & _ & HC2 & _).
unfold hqu_j in HJ2.
unfold hd_cut in HC2. cbn [hi_L9 headamp_himg_B] in HC2. rewrite !Forall_cons_iff in HC2.
destruct HC2 as (_ & C9c & _ & _ & _ & _ & _ & _ & C158c & _). cbn [fst snd hd_at hd_xv] in C9c, C158c.
assert (Hpod2 : In (e_pod e, e_len e) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. apply in_or_app. right. right. left. reflexivity. }
destruct (al_blocks _ _ HL ly2 S2 W2 mem2 md2 _ _ (proj1 HJ2) Hpod2) as (_ & Hpod4096 & Hpodceil & _).
pose proof asan_consts as (CA1 & _).
assert (Hpod64 : 0 <= e_pod e < 2 ^ 64) by (pose proof (req_size_pos (e_len e) ltac:(lia)); lia).
rewrite Z.mod_small in C158c by exact Hpod64.
pose proof HA2 as (_ & _ & _ & _ & _ & _ & HG2 & _).
destruct (hxu_geo hx pos e _ _ _ _ _ _ HB HG2 HJ2) as (_ & HSb2 & _ & HRb2 & _).
assert (B9c : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 (e_pod e)]) 9) = e_R e)
  by (rewrite (hxu_ew_reg regs2 _ 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), C9c; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs2 [Z_to_bv 64 (e_pod e)])
  (mkSS HXU_RA2 sr_atoms [ YP09.mkRegion (Some 9%nat) 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))] ]
     None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 HXU_RA2) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9c. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (e_R e) 0x158 8 (SOff 32 0) (e_pod e)).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs2 [Z_to_bv 64 (e_pod e)] 0).
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + change (N.to_nat 8) with 8%nat. exact C158c.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 HXU_RA2) with (Z_to_bv 64 HXU_RA2).
pose proof HJ2 as HJ.
aj_run hxu_tbl_ok HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
hxu_mach HS msC.
assert (EmC : ms_mem msC = mem2).
{ apply functional_extensionality; intros x; apply HF. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
clear HF HFr HG.
hxu_ext HS (10%bv : bv 5) Rc0. cbn [nth] in Rc0.
hxu_lit HS (1%bv : bv 5) Rrc.
pose proof (hxu_regs_keep rsegs _ msC (w_H W2) regs2 [Z_to_bv 64 (e_pod e)] HS ltac:(vm_compute; reflexivity)) as RKC.
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ msC HS eq_refl). cbn [ss_pc]. rewrite EmC. rewrite EmC in HJ.
change (Z_to_bv 64 340188) with (Z_to_bv 64 HXU_FREE).
eapply SRr_bind.
{ eapply (hxu_free_site hx fx2 pos e (4 + 1 + 1) [(e_pp e, Layout.PP_SIZE)] (e_pod e) (e_len e)
    ly2 S2 W2 regs2 mem2 _ (ms_regs msC) HXU_RA3 HB).
  - exact (conj HJ (proj2 HA2)).
  - lia.
  - unfold HQU_EV. lia.
  - exact Rc0.
  - exact Rrc.
  - unfold HXU_RA3. lia.
  - reflexivity.
  - exact RKC.
  - apply HTRACE. cbn [In]. right. right. right. right. left. reflexivity.
  - apply HTRACE. cbn [In]. right. right. right. right. right. left. reflexivity. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HA3).
clear HS HJ RKC Rc0 Rrc EmC msC B9c HJ2 HPerm2 C9c C158c Hpod2 Hpod4096 Hpodceil Hpod64 HG2 HSb2 HRb2 CA1.
(* ---- site 4: 0x83968 ld a0,0x148(s1); 0x8396c jal free(pp) ---- *)
pose proof HA3 as (HJ3 & HPerm3 & _ & _ & _ & _ & _ & HC3 & _).
unfold hqu_j in HJ3.
unfold hd_cut in HC3. cbn [hi_L9 headamp_himg_B] in HC3. rewrite !Forall_cons_iff in HC3.
destruct HC3 as (_ & C9d & _ & _ & _ & _ & _ & Cf0d & _). cbn [fst snd hd_at hd_xv] in C9d, Cf0d.
assert (Hpp3 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ HL ly3 S3 W3 mem3 md3 _ _ (proj1 HJ3) Hpp3) as (_ & Hpp4096 & Hppceil & _).
pose proof asan_consts as (CA1 & _).
assert (Hpp64 : 0 <= e_pp e < 2 ^ 64) by (pose proof (req_size_pos Layout.PP_SIZE ltac:(unfold Layout.PP_SIZE; lia)); lia).
rewrite Z.add_0_r, Z.mod_small in Cf0d by exact Hpp64.
pose proof HA3 as (_ & _ & _ & _ & _ & _ & HG3 & _).
destruct (hxu_geo hx pos e _ _ _ _ _ _ HB HG3 HJ3) as (_ & HSb3 & _ & HRb3 & _).
assert (B9 : bv_unsigned (ew (Ereg regs3 [Z_to_bv 64 (e_pp e)]) 9) = e_R e)
  by (rewrite (hxu_ew_reg regs3 _ 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), C9d; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs3 [Z_to_bv 64 (e_pp e)])
  (mkSS HXU_RA3 sr_atoms [ YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0 [YP09.mkChunk 0x148 (CVal 8 (SOff 32 0))] ]
     None (mkFacts [] [] []))
  (restrict (w_H W3) (@mkst fx2 regs3 (Z_to_bv 64 HXU_RA3) mem3 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (e_R e) 0x148 8 (SOff 32 0) (e_pp e)).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs3 [Z_to_bv 64 (e_pp e)] 0).
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + change (N.to_nat 8) with 8%nat. exact Cf0d.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 HXU_RA3) with (Z_to_bv 64 HXU_RA3).
pose proof HJ3 as HJ.
aj_run hxu_tbl_ok HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
hxu_mach HS msD.
assert (EmD : ms_mem msD = mem3).
{ apply functional_extensionality; intros x; apply HF. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
clear HF HFr HG.
hxu_ext HS (10%bv : bv 5) Rd0. cbn [nth] in Rd0.
hxu_lit HS (1%bv : bv 5) Rrd.
pose proof (hxu_regs_keep rsegs _ msD (w_H W3) regs3 [Z_to_bv 64 (e_pp e)] HS ltac:(vm_compute; reflexivity)) as RKD.
rewrite (st_ok_restrict_mkst rsegs (w_H W3) _ _ msD HS eq_refl). cbn [ss_pc]. rewrite EmD. rewrite EmD in HJ.
change (Z_to_bv 64 340188) with (Z_to_bv 64 HXU_FREE).
eapply SRr_bind.
{ eapply (hxu_free_site hx fx2 pos e (4 + 1 + 1 + 1) [] (e_pp e) Layout.PP_SIZE
    ly3 S3 W3 regs3 mem3 _ (ms_regs msD) HXU_RA4 HB).
  - exact (conj HJ (proj2 HA3)).
  - unfold Layout.PP_SIZE. lia.
  - unfold HQU_EV. lia.
  - exact Rd0.
  - exact Rrd.
  - unfold HXU_RA4. lia.
  - reflexivity.
  - exact RKD.
  - apply HTRACE. cbn [In]. right. right. right. right. right. right. left. reflexivity.
  - apply HTRACE. cbn [In]. right. right. right. right. right. right. right. left. reflexivity. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HA4).
clear HS HJ RKD Rd0 Rrd EmD msD B9 HJ3 HPerm3 C9d Cf0d Hpp3 Hpp4096 Hppceil Hpp64 HG3 HSb3 HRb3.
(* ---- 0x83970 .. J: res's two granules := 0xf8, s7 := F from R+0x18 ---- *)
pose proof HA4 as (HJ4 & HPerm4 & _ & R2d & R3d & R4d & HG4 & HC4 & Hfsh4 & HK4).
unfold hqu_j in HJ4.
destruct (hxu_geo hx pos e _ _ _ _ _ _ HB HG4 HJ4) as (HS16 & HSb & HR16 & HRb & HFal & HFapp & HF4096 & HFceil & Hfin4).
pose proof HG4 as (ES & ER & EF). unfold HQU_CID in EF.
destruct (hxu_ffacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ4 Hfin4) as (_ & _ & _ & _ & HFpres4 & HFSpres4 & _ & _ & _).
rewrite <- EF in HFpres4, HFSpres4.
destruct (hxu_jF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ4) as [EFA4 _]. rewrite <- EF in EFA4.
pose proof HC4 as HC4'. unfold hd_cut in HC4'. cbn [hi_L9 headamp_himg_B] in HC4'. rewrite !Forall_cons_iff in HC4'.
destruct HC4' as (C8e & C9e & C19e & C21e & _ & _ & C18e & _ & _ & _).
cbn [fst snd hd_at hd_xv] in C8e, C9e, C19e, C21e, C18e.
rewrite Z.add_0_r in C21e, C18e. rewrite Z.mod_small in C18e by lia.
destruct (hxu_shF_bounds (e_F e) HF4096 HFceil) as (Hsh1 & Hsh2 & Hsh3).
set (shF := shadow_addr (e_F e)) in *.
assert (B19 : bv_unsigned (ew (Ereg regs4 []) 19) = shF)
  by (rewrite (hxu_ew_reg regs4 [] 19 (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), C19e; unfold w64; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew (Ereg regs4 []) 9) = e_R e)
  by (rewrite (hxu_ew_reg regs4 [] 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), C9e; unfold w64; apply unsigned_lit_small; lia).
assert (E21 : sv_denot (Ereg regs4 []) (SOff 21 0) = Z_to_bv 64 (e_F e)).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_nat regs4 [] 21 (Z_to_bv 5 21) ltac:(vm_compute; reflexivity)).
  exact C21e. }
assert (HS : st_ok rsegs (Ereg regs4 [])
  (mkSS HXU_RA4 sr_atoms
     [ YP09.mkRegion (Some 19%nat) 0x54 0x56 0x54 0x56 [];
       YP09.mkRegion (Some 9%nat) 0x18 0x20 0 0 [YP09.mkChunk 0x18 (CVal 8 (SOff 21 0))] ]
     None (mkFacts [] [] []))
  (restrict (w_H W4) (@mkst fx2 regs4 (Z_to_bv 64 HXU_RA4) mem4 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HFSpres4. lia.
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ (e_R e) 0x18 8 (SOff 21 0) (e_F e)).
      * exact E21.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C18e.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B19, B9.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 HXU_RA4) with (Z_to_bv 64 HXU_RA4).
aj_run_to hxu_tbl_ok HS HJ4 HQU_J.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat shF); [reflexivity | exact B19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA4. change (fs_frame_bytes 4 / 8) with 128. fold shF. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
hxu_mach HS msJ.
assert (KJ : forall a, 0 <= a < 2 ^ 64 -> ~ (shF + 0x54 <= a < shF + 0x56) ->
  aview rsegs (w_H W4) (ms_mem msJ) a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  rewrite ?B19, ?B9 in Hw; lia. }
assert (Hf8 : forall j, j = 84 \/ j = 85 -> aview rsegs (w_H W4) (ms_mem msJ) (shF + j) = Some 248).
{ intros j Hj. pose proof (hxu_st_region rsegs _ _ _ _ HS (or_introl eq_refl)) as (_ & _ & _ & Hc).
  cbn [YP09.r_chunks YP09.r_base base_val] in Hc. rewrite B19 in Hc.
  apply Forall_cons_iff in Hc as [Hc85 Hc]. apply Forall_cons_iff in Hc as [Hc84 _].
  change (ms_mem (restrict (w_H W4) msJ)) with (mrestrict (w_H W4) (ms_mem msJ)) in Hc84, Hc85.
  unfold aview. destruct Hj as [-> | ->].
  - rewrite (hxu_chunk_f8 rsegs _ _ _ _ Hc84). first [reflexivity | vm_compute; reflexivity].
  - rewrite (hxu_chunk_f8 rsegs _ _ _ _ Hc85). first [reflexivity | vm_compute; reflexivity]. }
clear HF HFr HG.
hxu_atom HS (Z_to_bv 5 23) (Z_to_bv 5 21) R23. rewrite C21e in R23.
pose proof (hxu_regs_keepL rsegs _ msJ (w_H W4) regs4 [] [2; 3; 4; 8; 19; 21] HS ltac:(vm_compute; reflexivity)) as RKJ.
assert (HfshJ : hd_fsh rsegs (w_H W4) (ms_mem msJ) (e_F e) (hi_shA headamp_himg_B)).
{ intros i Hi. change (hi_shA headamp_himg_B) with headamp_B_shA in *. rewrite hxu_shA_len in Hi. fold shF.
  destruct (Z.eq_dec i 84) as [->|N84].
  { change (Z.to_nat 84) with 84%nat. rewrite (proj1 hxu_shA_f8). apply Hf8. left. reflexivity. }
  destruct (Z.eq_dec i 85) as [->|N85].
  { change (Z.to_nat 85) with 85%nat. rewrite (proj2 hxu_shA_f8). apply Hf8. right. reflexivity. }
  rewrite (hxu_shA_shB (Z.to_nat i)) by lia. rewrite KJ by lia.
  exact (Hfsh4 i ltac:(change (hi_shB headamp_himg_B) with headamp_B_shB; rewrite hqu_shB_len; lia)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
  apply SRr_ret; exists ly4, S4, (ms_regs msJ), (ms_mem msJ), mdx, (4 + 1 + 1 + 1 + 1) end.
split.
{ unfold cfg_at. rewrite (st_ok_restrict_mkst rsegs (w_H W4) _ _ msJ HS eq_refl) at 1. reflexivity. }
unfold hqu_cut_J, hqu_j.
split; [exact HJ4|].
split; [unfold HQU_EV; lia|].
split; [rewrite app_nil_r in HPerm4; exact HPerm4|].
pose proof (RKJ 2 ltac:(cbv [In]; lia)) as K2. z5 K2.
pose proof (RKJ 3 ltac:(cbv [In]; lia)) as K3. z5 K3.
pose proof (RKJ 4 ltac:(cbv [In]; lia)) as K4. z5 K4.
split; [rewrite K2; exact R2d|].
split; [rewrite K3; exact R3d|].
split; [rewrite K4; exact R4d|].
split; [exact HG4|].
split; [exact Hfrm|].
split.
{ unfold hd_cut. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at hd_xv].
  - rewrite (RKJ 8 ltac:(cbv [In]; lia)). exact C8e.
  - rewrite (RKJ 19 ltac:(cbv [In]; lia)). exact C19e.
  - rewrite (RKJ 21 ltac:(cbv [In]; lia)), Z.add_0_r. exact C21e.
  - rewrite Z.add_0_r. exact R23. }
split; [exact HfshJ|].
apply (hxu_kept_mono hx pos e W4 mem4 regs4 W4 (ms_mem msJ) (ms_regs msJ)); [| |exact HK4].
- intros a Ha. apply KJ; lia.
- intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. apply KJ; lia.
Qed.

(* ====================================== X01r: J -> the return ====================================== *)
Theorem hxu_S_X01r : hqu_S_X01r_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold hqu_S_X01r_stmt.
intros hx fx2 pos e k ly SJ W regsJ mem md HB HC.
destruct HC as (HJ & Hk & HPerm & R2 & R3 & R4 & HG & Hfrm & HCUT & Hfsh & HK).
pose proof (AR_laws_ok rsegs B) as HL. pose proof img_segs_low as Hsegs. pose proof img_wx as Hwx.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof (astack_free_law_ok rsegs B) as HASF.
destruct (hxu_geo hx pos e _ _ _ _ _ _ HB HG HJ) as (HS16 & HSb & HR16 & HRb & HFal & HFapp & HF4096 & HFceil & Hfin).
pose proof HG as (ES & ER & EF). unfold HQU_CID in EF.
unfold hqu_j in HJ.
destruct (hxu_ffacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ Hfin) as (_ & _ & _ & _ & HFpres & _ & _ & HFLo & HFLr).
rewrite <- EF in HFpres.
destruct (hxu_jF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ) as [EFA EFL]. rewrite <- EF in EFA.
destruct (hxu_shF_bounds (e_F e) HF4096 HFceil) as (Hsh1 & Hsh2 & Hsh3).
pose proof HB as (HPRE & Hra & _). pose proof asan_consts as (CA1 & _).
pose proof HPRE as (_ & Hraok & _ & Hgp0 & Htp0 & _).
(* the cut's values *)
unfold hd_cut in HCUT. rewrite !Forall_cons_iff in HCUT.
destruct HCUT as (C8 & C19 & C21 & C23 & _). cbn [fst snd hd_at hd_xv] in C8, C19, C21, C23.
rewrite Z.add_0_r in C21, C23.
set (F := e_F e) in *. set (shF := shadow_addr F) in *. set (FL := flag_addr (hu_ly rsegs hx) 4 pos) in *.
set (S0 := spZ (hu_regs rsegs hx)) in *. rewrite ES in HS16, HSb, HRb, C8. set (R := e_R e) in *.
assert (Ho16 : (R - S0) mod 16 = 0) by (rewrite Zminus_mod, HR16, HS16; reflexivity).
assert (HdFFL : FL + 1 <= F \/ F + 1024 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 1024)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLo). }
(* ---- run 1: J .. the jal of __asan_set_shadow_f5 (F[0] := 0x45e0360e through s5; s7 = F >= 4096 decides the
   beqz) ---- *)
assert (B21 : bv_unsigned (ew (Ereg regsJ []) 21) = F)
  by (rewrite (hxu_ew_reg regsJ [] 21 (Z_to_bv 5 21) ltac:(vm_compute; reflexivity)), C21; unfold w64; apply unsigned_lit_small; lia).
assert (B23 : bv_unsigned (ew (Ereg regsJ []) 23) = F)
  by (rewrite (hxu_ew_reg regsJ [] 23 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)), C23; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regsJ [])
  (mkSS HQU_J sr_atoms [ YP09.mkRegion (Some 21%nat) 0 8 0 8 [] ] None (mkFacts [(23%nat, mkAF 4096 (2 ^ 47) 5)] [] []))
  (restrict (w_H W) (@mkst fx2 regsJ (Z_to_bv 64 HQU_J) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B21. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFpres (F + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B23. change (2 ^ 5) with 32. lia. }
unfold cfg_at. change (w64 HQU_J) with (Z_to_bv 64 HQU_J).
aj_run hxu_tbl_ok HS HJ.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat F); [reflexivity | exact B21 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024. lia. }
  apply awr_ok_nil. }
hxu_mach HS msA.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> aview rsegs (w_H W) (ms_mem msA) a = aview rsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite B21 in Hw. lia. }
clear HF HFr HG.
hxu_atom HS (10%bv : bv 5) (Z_to_bv 5 19) Ra0. rewrite C19 in Ra0.
hxu_lit HS (11%bv : bv 5) Ra1.
hxu_lit HS (1%bv : bv 5) Rra.
pose proof (hxu_regs_keep rsegs _ msA (w_H W) regsJ [] HS ltac:(vm_compute; reflexivity)) as RKA.
pose proof (RKA 2 ltac:(unfold acallee_saved; lia)) as A2. z5 A2.
pose proof (RKA 3 ltac:(unfold acallee_saved; lia)) as A3. z5 A3.
pose proof (RKA 4 ltac:(unfold acallee_saved; lia)) as A4. z5 A4.
(* ---- __asan_set_shadow_f5(shadow F, 128) at 0x54d54, ra 0x8399c ---- *)
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msA HS eq_refl) at 1. cbn [ss_pc].
  change (Z_to_bv 64 347476) with (Z_to_bv 64 0x54d54).
  eapply (hxu_set_shadow_at (fx := fx2) rsegs B HL Hsegs 0x54d54 0xf5 (ASHF5 fx2) W (ms_regs msA) (ms_mem msA)
    LLVMF_STK S0 [] (hu_ly rsegs hx) (hu_S rsegs hx) (hu_W rsegs hx) (hu_mem rsegs hx) (hu_md rsegs hx) [(4, pos)] ly SJ _ k 4 pos shF 128 (R - S0)
    (Z_to_bv 64 HXU_RA5) HJ).
  - left. reflexivity.
  - exact Ra0.
  - exact Ra1.
  - lia.
  - rewrite EFA. fold shF. lia.
  - rewrite EFA. fold shF. change (fs_frame_bytes 4 / 8) with 128. lia.
  - unfold spZ. rewrite A2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite A3. exact R3.
  - rewrite A4. exact R4.
  - exact Rra.
  - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HAR2 & Hf5 & Hk2).
clear HS.
assert (RK2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsJ (Z_to_bv 5 r))
  by (intros r Hr; rewrite (HP2 r Hr); exact (RKA r Hr)).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (shF <= a < shF + 128) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem a) by (intros a Ha H1 H2; rewrite (Hk2 a Ha H2); exact (KA a Ha H1)).
assert (HK2 : hqu_kept rsegs hx pos e W mem2 regs2).
{ apply (hxu_kept_mono hx pos e W mem regsJ W mem2 regs2); [| |exact HK].
  - intros a Ha. rewrite ES in Ha. apply K2; lia.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. apply K2; lia. }
pose proof HK2 as (HKF2 & HFS2). unfold hqu_cells in HKF2. apply Forall_app in HKF2 as [HKS2 HKL2].
assert (HSV2 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) mem2) (S0 + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr (hu_regs rsegs hx) (nth j hqu_saved_regs 0%bv)))).
{ intros j Hj. unfold hqu_saves_L in HKS2. rewrite Forall_map in HKS2.
  pose proof (proj1 (Forall_forall _ _) HKS2 j ltac:(apply in_seq; lia)) as X. cbn [fst snd hd_at hd_xv] in X.
  rewrite ES in X. rewrite Z.mod_small in X; [exact X|].
  pose proof (bv_unsigned_in_range 64 (getr (hu_regs rsegs hx) (nth j hqu_saved_regs 0%bv))) as Y.
  change (bv_modulus 64) with (2 ^ 64) in Y. exact Y. }
assert (HFW2 : val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x3f8) 8 FL).
{ apply Forall_cons_iff in HKL2 as [X _]. cbn [fst snd hd_at hd_xv] in X. unfold HQU_FLAG, HQU_CID in X.
  rewrite Z.add_0_r in X. fold F FL in X. rewrite Z.mod_small in X by lia. exact X. }
destruct (hxu_ffacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ2 Hfin) as (_ & _ & _ & _ & _ & _ & HFLp2 & _ & _).
fold FL in HFLp2.
(* ---- run 2: 0x8399c .. the first float load: the flag byte, a0 = 0, sp = S - 0x220, the 13 restores ---- *)
pose proof (RK2 23 ltac:(unfold acallee_saved; lia)) as Q23. rewrite C23 in Q23.
pose proof (RK2 8 ltac:(unfold acallee_saved; lia)) as Q8. rewrite C8 in Q8.
assert (B23' : bv_unsigned (ew (Ereg regs2 (hxu_X7 FL (hu_regs rsegs hx))) 23) = F)
  by (rewrite (hxu_ew_reg regs2 _ 23 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)), Q23; unfold w64; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew (Ereg regs2 (hxu_X7 FL (hu_regs rsegs hx))) 8) = S0)
  by (rewrite (hxu_ew_reg regs2 _ 8 (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)), Q8; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs2 (hxu_X7 FL (hu_regs rsegs hx))) 32 = Z_to_bv 64 FL) by exact (ew_Ereg_extra regs2 (hxu_X7 FL (hu_regs rsegs hx)) 0).
assert (B32 : bv_unsigned (ew (Ereg regs2 (hxu_X7 FL (hu_regs rsegs hx))) 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs2 (hxu_X7 FL (hu_regs rsegs hx)))
  (mkSS HXU_RA5 sr_atoms
     [ YP09.mkRegion (Some 23%nat) 0x3f8 0x400 0 0 [YP09.mkChunk 0x3f8 (CVal 8 (SOff 32 0))];
       YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
       YP09.mkRegion (Some 8%nat) (-104) 0 0 0 hxu_sv_chunks ]
     None (mkFacts [] [] []))
  (restrict (w_H W) (@mkst fx2 regs2 (Z_to_bv 64 HXU_RA5) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B23'. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ F 0x3f8 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact HFW2.
    + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable rsegs). exact HFLp2.
    + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold hxu_sv_chunks. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      apply (chunk_ok_val rsegs _ _ S0 (-8 - 8 * Z.of_nat j) 8 (SOff (32 + Nat.succ j) 0)
        (bv_unsigned (getr (hu_regs rsegs hx) (nth j hqu_saved_regs 0%bv)))).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_extra regs2 (hxu_X7 FL (hu_regs rsegs hx)) (Nat.succ j)).
        unfold hxu_X7. cbn [nth]. rewrite Z_to_bv_bv_unsigned. destruct Hj as [_ Hj]. unfold hqu_saved_regs.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      * pose proof (bv_unsigned_in_range 64 (getr (hu_regs rsegs hx) (nth j hqu_saved_regs 0%bv))) as Y.
        change (bv_modulus 64) with (2 ^ 64) in Y. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. apply HSV2. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B23', B32, B8.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
hxu_run_flag HS HJ2 HL Hsegs ML Hwx HASF FFL.
- lia.
- intros a (r & Hin & Ha). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?B23', ?B32, ?B8 in Ha; [exfalso; lia | right; rewrite EFL; fold FL; lia | exfalso; lia].
- intros msr HSr. rewrite EFL. fold FL. rewrite <- B32. apply (hxu_flag0_of rsegs _ _ msr 32 HSr).
  cbn [ss_mem In]. right. left. reflexivity.
- hxu_mach HS msD.
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> a <> FL -> aview rsegs (w_H W) (ms_mem msD) a = aview rsegs (w_H W) mem2 a).
  { intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
    cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?B23', ?B32, ?B8 in Hw; lia. }
  clear HF HFr HG.
  destruct HFS2 as (v0 & v1 & v2 & v3 & V0 & V1 & V2 & V3). cbn [hd_at hd_xv] in V0, V1, V2, V3.
  rewrite ES in V0, V1, V2, V3.
  assert (VD : forall o v, val_mem rsegs (mrestrict (w_H W) mem2) (S0 + o) 8 v -> -0x88 <= o -> o + 8 <= -0x68 ->
    val_mem rsegs (mrestrict (w_H W) (ms_mem msD)) (S0 + o) 8 v).
  { intros o v Hv H1 H2. apply (val_mem_kept rsegs (w_H W) (w_H W) mem2 (ms_mem msD)); [|exact Hv].
    intros q Hq. change (Z.of_nat 8) with 8 in Hq. apply KD; lia. }
  pose proof (VD _ _ V0 ltac:(lia) ltac:(lia)) as VD0.
  pose proof (VD _ _ V1 ltac:(lia) ltac:(lia)) as VD1.
  pose proof (VD _ _ V2 ltac:(lia) ltac:(lia)) as VD2.
  pose proof (VD _ _ V3 ltac:(lia) ltac:(lia)) as VD3.
  assert (SPD : getr (ms_regs msD) (Z_to_bv 5 2) = Z_to_bv 64 (S0 - 544)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ msD (Z_to_bv 5 2) HS).
    lazymatch goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end.
    cbn [sv_denot]. rewrite B8. f_equal; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msD HS eq_refl). cbn [ss_pc].
  (* the float states the four loads leave (FPState is a class: they are named, never left to instance search) *)
  pose (f1 := mkFP (bvmap_set (Z_to_bv 5 8) (bv_extract 0 64 (le_bytes_to_word (hxu_bytes (v0 mod 2 ^ 64))))
    (@fp_regs fx2)) (@fp_csr fx2)).
  pose (f2 := mkFP (bvmap_set (Z_to_bv 5 9) (bv_extract 0 64 (le_bytes_to_word (hxu_bytes (v1 mod 2 ^ 64))))
    (@fp_regs f1)) (@fp_csr f1)).
  pose (f3 := mkFP (bvmap_set (Z_to_bv 5 18) (bv_extract 0 64 (le_bytes_to_word (hxu_bytes (v2 mod 2 ^ 64))))
    (@fp_regs f2)) (@fp_csr f2)).
  pose (f4 := mkFP (bvmap_set (Z_to_bv 5 19) (bv_extract 0 64 (le_bytes_to_word (hxu_bytes (v3 mod 2 ^ 64))))
    (@fp_regs f3)) (@fp_csr f3)).
  (* ---- 0x839f0 fld fs0,0x1b0(sp) ---- *)
  eapply (hxu_step_keep rsegs B Hwx HL Hsegs W fx2 f1); [ | exact HJ2 | clear HJ2; intros md3 HJ2 ].
  { rewrite (YK0o.fp_step_fld fx2 rsegs (ms_regs msD) (Z_to_bv 64 539120) (mrestrict (w_H W) (ms_mem msD)) (seg_rom rsegs)
      (Z_to_bv 32 0x1b013407) (Z_to_bv 5 8) (Z_to_bv 5 2) (Z_to_bv 12 0x1b0) (Z_to_bv 64 (S0 + -0x70)) (hxu_bytes (v0 mod 2 ^ 64))).
    - rewrite (hxu_pc4 539120) by lia. reflexivity.
    - apply hxu_tbl_ok. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - rewrite SPD. unfold v_addi. rewrite unsigned_lit_small by lia.
      replace (bv_signed (Z_to_bv 12 0x1b0)) with 0x1b0 by (vm_compute; reflexivity). f_equal; lia.
    - apply hxu_rdn8. exact VD0. }
  (* ---- 0x839f4 fld fs1,0x1a8(sp) ---- *)
  eapply (hxu_step_keep rsegs B Hwx HL Hsegs W f1 f2); [ | exact HJ2 | clear HJ2; intros md4 HJ2 ].
  { rewrite (YK0o.fp_step_fld f1 rsegs (ms_regs msD) (Z_to_bv 64 (539120 + 4)) (mrestrict (w_H W) (ms_mem msD)) (seg_rom rsegs)
      (Z_to_bv 32 0x1a813487) (Z_to_bv 5 9) (Z_to_bv 5 2) (Z_to_bv 12 0x1a8) (Z_to_bv 64 (S0 + -0x78)) (hxu_bytes (v1 mod 2 ^ 64))).
    - rewrite (hxu_pc4 (539120 + 4)) by lia. reflexivity.
    - apply hxu_tbl_ok. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - rewrite SPD. unfold v_addi. rewrite unsigned_lit_small by lia.
      replace (bv_signed (Z_to_bv 12 0x1a8)) with 0x1a8 by (vm_compute; reflexivity). f_equal; lia.
    - apply hxu_rdn8. exact VD1. }
  (* ---- 0x839f8 fld fs2,0x1a0(sp) ---- *)
  eapply (hxu_step_keep rsegs B Hwx HL Hsegs W f2 f3); [ | exact HJ2 | clear HJ2; intros md5 HJ2 ].
  { rewrite (YK0o.fp_step_fld f2 rsegs (ms_regs msD) (Z_to_bv 64 (539120 + 4 + 4)) (mrestrict (w_H W) (ms_mem msD)) (seg_rom rsegs)
      (Z_to_bv 32 0x1a013907) (Z_to_bv 5 18) (Z_to_bv 5 2) (Z_to_bv 12 0x1a0) (Z_to_bv 64 (S0 + -0x80)) (hxu_bytes (v2 mod 2 ^ 64))).
    - rewrite (hxu_pc4 (539120 + 4 + 4)) by lia. reflexivity.
    - apply hxu_tbl_ok. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - rewrite SPD. unfold v_addi. rewrite unsigned_lit_small by lia.
      replace (bv_signed (Z_to_bv 12 0x1a0)) with 0x1a0 by (vm_compute; reflexivity). f_equal; lia.
    - apply hxu_rdn8. exact VD2. }
  (* ---- 0x839fc fld fs3,0x198(sp) ---- *)
  eapply (hxu_step_keep rsegs B Hwx HL Hsegs W f3 f4); [ | exact HJ2 | clear HJ2; intros md6 HJ2 ].
  { rewrite (YK0o.fp_step_fld f3 rsegs (ms_regs msD) (Z_to_bv 64 (539120 + 4 + 4 + 4)) (mrestrict (w_H W) (ms_mem msD)) (seg_rom rsegs)
      (Z_to_bv 32 0x19813987) (Z_to_bv 5 19) (Z_to_bv 5 2) (Z_to_bv 12 0x198) (Z_to_bv 64 (S0 + -0x88)) (hxu_bytes (v3 mod 2 ^ 64))).
    - rewrite (hxu_pc4 (539120 + 4 + 4 + 4)) by lia. reflexivity.
    - apply hxu_tbl_ok. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - rewrite SPD. unfold v_addi. rewrite unsigned_lit_small by lia.
      replace (bv_signed (Z_to_bv 12 0x198)) with 0x198 by (vm_compute; reflexivity). f_equal; lia.
    - apply hxu_rdn8. exact VD3. }
  (* ---- 0x83a00 addi sp,sp,0x220; 0x83a04 ret, at the float state the loads left ---- *)
  pose proof (hxu_switch rsegs fx2 f4 _ _ msD (w_H W) (539120 + 4 + 4 + 4 + 4) HS) as HS3.
  aj_run hxu_tbl_ok HS3 HJ2.
  { apply awr_ok_nil. }
  hxu_mach HS3 msE.
  clear HF HFr HG.
  eapply (SRr_ret_at rsegs hxu_tbl hxu_tbl_ok Hwx W _ _ msE _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold hqu_ret. cbv beta.
  hxu_ext HS3 (1%bv : bv 5) Rf1. unfold hxu_X7 in Rf1. cbn [nth map hqu_saved_regs] in Rf1.
  hxu_lit HS3 (10%bv : bv 5) Rf10.
  lazymatch goal with |- exists _ _ _ _ _ _ _, {| cfg_ms := @mkst ?fq ?rg _ ?mm _; cfg_model := ?mdx |} = _ /\ _ =>
    exists fq, ly, (stack_free_state 4 pos SJ), rg, mm, mdx, k end.
  split.
  { unfold cfg_at. rewrite Rf1. unfold YK0s.ret_ok in Hraok. rewrite Hraok.
    unfold w64. rewrite <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hfrm|].
  split; [unfold hqu_j; apply (ajournal_materialize rsegs B HL Hsegs); exact HJ2|].
  split; [unfold HQU_EV in *; lia|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    pose proof (RK2 3 ltac:(unfold acallee_saved; lia)) as Q3. z5 Q3. rewrite R3 in Q3.
    pose proof (RK2 4 ltac:(unfold acallee_saved; lia)) as Q4. z5 Q4. rewrite R4 in Q4.
    z5 Q8.
    destruct Hr' as [->|[->|[->|Hr']]].
    - z5g. hxu_atom HS3 (2%bv : bv 5) (8%bv : bv 5) Hx. rewrite Hx, Q8.
      change S0 with (spZ (hu_regs rsegs hx)). unfold spZ, w64. apply Z_to_bv_bv_unsigned.
    - z5g. hxu_atom HS3 (3%bv : bv 5) (3%bv : bv 5) Hx. rewrite Hx, Q3. symmetry. exact Hgp0.
    - z5g. hxu_atom HS3 (4%bv : bv 5) (4%bv : bv 5) Hx. rewrite Hx, Q4. symmetry. exact Htp0.
    - destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; z5g;
      lazymatch goal with |- getr _ ?rr = _ => hxu_ext HS3 rr Hx end;
      rewrite Hx; unfold hxu_X7; reflexivity. }
  split; [rewrite Rf10; reflexivity|].
  unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly SJ). exact HPerm.
Qed.
End m.

Print Assumptions hxu_S_X01f.
Print Assumptions hxu_S_X01r.
