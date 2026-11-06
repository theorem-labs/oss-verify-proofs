(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: call lemmas for the ASan walk of check_round_trip: ajournal_after_write_win (the core's ajournal_after_write, lib/Reusable/YCbq.v, with its presence premise narrowed to the journal's stack window), aj_set_shadow_atS (a shadow-fill entry __asan_set_shadow_XX on the shadow of the caller's own side-stack frame) and aj_stack_free_cls_atS (the release entry of a side-stack class that fills the whole frame's shadow). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip_k.v, with its module paths changed; 4 of its 106 lines of code are new or changed and 198 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the journal lemma that the walk of segment A4 of
   reac_segconf_parse_file needs for the CALL that releases its class-5 side-stack frame
   (`jal __asan_stack_free_5` at 0x88c10, a1 = 0x480), carried here verbatim from the released donor walk
   plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip_k.v at origin/ossv/recipes 501c0d516c69 (its lines
   236-313), with only the module paths changed. It is NOT in the Pa kit: check_round_trip is the one released
   walk whose frame is released by a call, and it keeps it local (the walk group's Pa walk map, section
   3(c.2)).
     aj_stack_free_cls_atS     the release entry of a side-stack class that fills the whole frame's shadow
                               (lib/A/Rt/RtStack.v astack_free_cls_realizes), called on the caller's newest frame
   Its proof uses the same donor file's ajournal_after_write_win (its lines 34-173), which pf_a2_k.v carries.
   Written 2026-10-30. No instruction of the image is walked here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtStack.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a2_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ML : model_laws (as_universe B).
(* The release entry of a side-stack class that fills the whole frame's shadow (contract lib/A/Rt/RtStack.v
   astack_free_cls_realizes), called on the caller's newest frame (the head of its own frames). The bookkeeping is
   YCbq.v aj_flag_store's, with the contract's post in place of the symbolic run: the model's stack_free removes the
   head frame, the shadow bytes are the caller's own frame shadow, the flag byte is an owned application byte outside
   the image, and the contract gives AR at stack_free_state directly. *)
Lemma aj_stack_free_cls_atS : forall pc cid, astack_free_cls_realizes segs B pc cid -> 0 <= cid ->
forall W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k (o : Z) raw pos n,
ajournal segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (frame_addr lyc cid pos) -> getr regsT 11 = w64 n ->
rdword (aview segs (w_H W) memT) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal segs B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall a, 0 <= a < 2 ^ 64 ->
   ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
   a <> flag_addr lyc cid pos -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
   aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc cid AF Hcid W regsT memT STK sp0 FP ly S W0 mem md own' lyc Sc mdc k o raw pos n
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Hflag.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg Hbud);
[rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
destruct (al_flag _ _ LAWS lyc Sc W memT mdc cid pos HAR Hin) as (_ & Hfo & Hfapp & Hflt).
assert (Hfimg : ~ in_img segs (flag_addr lyc cid pos)).
{ refine (proj2 (al_client_img _ _ LAWS lyc Sc W memT mdc (flag_addr lyc cid pos) HAR _)).
right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hse.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (_ & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
pose proof (sep_frames_pos segs B LAWS lyc Sc W memT mdc (cid, pos) (cid, pos) [] l1' l2 HAR
ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
eapply SRr_mono.
{ exact (AF lyc Sc W regsT memT mdc pos n HPRE Hin Ha0 Ha1 Hflag). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & _ & Hfr & Hpres2).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (pf_a2_k.ajournal_after_write_win segs B LAWS segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W memT mdc k mem2 md2
(fun a => (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) \/
a = flag_addr lyc cid pos \/ (sp0 + o - ESTACK <= a < sp0 + o)) (stack_free_state cid pos Sc) own' HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right; left | right; right]; exact H'.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 + o - ESTACK)) as [Hw | Hw];
[| destruct (Z_lt_le_dec a (sp0 + o)) as [Hw' | Hw']; [apply Hpres2; zlia |]];
apply (apresent_transfer segs (w_H W) (w_H W) memT mem2 a); try (zlia || exact (Hpres a Ha));
try (intros Him; pose proof (segs_low a Him); zlia); apply (Hfr a); zlia.
- exact Hsame.
- intros a [Ha | [-> | Ha]].
+ left. unfold awr_byte. right; right; right; left. exists cid, pos. split; [left; reflexivity|].
right. unfold in_zr; cbn [fst snd]. zlia.
+ right. split; [exact Hfo|]. split; [zlia | exact Hfimg].
+ left. unfold awr_byte. left. zlia.
- exact HAR2.
- unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
- reflexivity.
- cbn. zlia.
- etransitivity; [exact E2 | symmetry; exact E1].
- apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [exact HP|]. exact Hfr.
Qed.
End h.
End c.
