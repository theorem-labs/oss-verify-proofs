(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 121 of its 178 lines of code are new or changed and 354 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: one malloc call inside an own allocating function's walk (link_amem.v aleaf_alloc
   shape), on the caller's journal ajournal_gx; for the walks of text_buf and text_of.

   - amalloc04_sub_d: lib/A/Prog/YC85G.v amalloc04_sub over lib/A/Rt/LinkMallocDepot.v amalloc04_rule_d (the frame's
     malloc rule with the depot step of the call's trace), its proof body with the depot clause carried: the call on
     the donor journal, with the callee's own (nested, sink-closed) journal.
   - aj_gx_malloc_d: its lift onto ajournal_gx (LinkWalkSide.v aj_gx_unpack, W_journalG.v ajournal_gx_pack; the
     pattern of the slot walk's LLVMFuzzerTestOneInputFree.v aj_gx_calloc_w), with the model's descriptors and file
     system kept (PaJournalFs.v ajournal_closed_fs on the nested journal) and the depot step as the wild-count bound
     of a FIXED trace (`alc_depot_fixed`: the step adds no wild trace) or of any trace (`alc_depot_any`: at most one).
   - akept_drop_block: the fresh block is no byte of any clause of the call's kept clause (link_amem.v akept): it is
     below the allocator's ceiling, apart from every block and frame of the call's state and from their shadow, and
     no image byte (AR at the state after the call), so a kept clause that excepts it is the kept clause without it.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G PaJournalFs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the depot step of a FIXED trace adds no wild trace; of any trace, at most one *)
Lemma alc_depot_fixed : forall U tr d d', depot_step tr d d' -> In tr (u_fix U) ->
  (length (wild_part U d') <= length (wild_part U d))%nat.
Proof.
  intros U tr d d' H Hf. pose proof (wild_part_step U tr d d' H) as W.
  unfold wild_cost in W. apply mem_trace_In in Hf. rewrite Hf in W. cbn [orb] in W. lia.
Qed.

Lemma alc_depot_any : forall U tr d d', depot_step tr d d' ->
  (length (wild_part U d') <= length (wild_part U d) + 1)%nat.
Proof.
  intros U tr d d' H. pose proof (wild_part_step U tr d d' H) as W.
  unfold wild_cost in W. destruct (mem_trace tr (u_fix U) || mem_trace tr d); lia.
Qed.

(* at a call whose frame record is well formed the trace is call_trace0's *)
Lemma alc_call_trace_ok : forall ly pc0 (regs : bvmap 5 word) ch, spZ regs + 16 < ly_top ly ->
  call_trace ly pc0 regs ch = call_trace0 pc0 regs ch.
Proof.
  intros ly pc0 regs ch H. unfold call_trace, frame0_ok.
  replace (spZ regs + 16 <? ly_top ly) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation code := (as_code B).

(* YC85G.v amalloc04_sub with the depot clause *)
Lemma amalloc04_sub_d : amalloc04_rule_d (SK := SK) segs B MT ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n) /\
depot_step (call_trace lyc (pc_malloc_ra0 code) regsT ch) (st_depot Sc) (st_depot S2) /\
ajournal segs B ASTACK (sp0 + o) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
Proof using SK LAWS segs_low.
intros AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ASTACK (sp0 + o) [] o
HJ eq_refl Ho16 Ho ltac:(lia) Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AM W regsT memT ASTACK (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 n 0 raw ch HJ1 Ha0 Hn Hlive);
first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact HU | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & MLE & HD).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ2 | lia | lia |].
intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - ASTACK) with (sp0 + o - ASTACK) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact MLE|]. split; [exact HD|].
replace (0 + 1) with 1 in HJ2 by reflexivity. exact HJ2.
Qed.

(* MALLOC ON THE JOURNAL: the call's window [sp - ASTACK, sp) inside the journal's, sp 16 below the journal's sp0
   (the frame record is well formed); the descriptors and file system kept; the depot step of the call's trace *)
Lemma aj_gx_malloc_d : amalloc04_rule_d (SK := SK) segs B MT ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n raw ch,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ASTACK -> spZ regsT <= sp0 -> spZ regsT + 16 < sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S + k + 1 <= EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_malloc MT n) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
       4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
       acall_kept segs B lyc Sc W memT W2 mem2 (spZ regsT - ASTACK) (spZ regsT)
         (fun a => res <= a < res + req_size n) /\
       mo_le MT Sc S2 (mo_malloc MT n) /\
       depot_step (call_trace0 (pc_malloc_ra0 code) regsT ch) (st_depot Sc) (st_depot S2) /\
       m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof using SK LAWS segs_low.
  intros AM G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n raw ch
    HJX Ha0 Hn Hlive H16 Hlo Hhi Hfr0 Hgp Htp Hra Hraw Hev Hch Htr Hmo.
  assert (Has : ASTACK = 16384) by reflexivity.
  destruct (aj_gx_unpack SK segs B LAWS segs_low G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT ASTACK
    HJX ltac:(lia) H16 Hlo Hhi) as (memS & HJ & Hag & Hout & HSTK & HXO & Esp & Ho16 & Ho & Hb & Hceil & H47).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  assert (Htop : spZ regsT + 16 < ly_top lyc).
  { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    destruct Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop0 & _). rewrite Etop. lia. }
  eapply SRr_mono.
  { exact (amalloc04_sub_d AM W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k n
      (spZ regsT - (sp0 + XO)) raw ch HJ Ha0 Hn Hlive Esp Ho16 Ho Hb Hgp Htp Hra Hraw ltac:(lia) Hch Htr Hmo). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & H4096 & Hbl & HK & MLE
    & HD & HJ1).
  replace (sp0 + XO + (spZ regsT - (sp0 + XO))) with (spZ regsT) in HK, HJ1 by lia.
  assert (Hcl : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
  { eapply ajournal_closed_fs; [ .. | exact HJ1];
      first [exact LAWS | exact segs_low | intros (r & Hr & _); destruct Hr]. }
  destruct Hcl as [Efd Efs].
  exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
  split.
  { apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) memS HSTK HXO HJ2 Hag).
    intros a Ha Hno. destruct HK as (K1 & _). rewrite K1 by lia. exact (Hout a Ha Hno). }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact H4096|]. split; [exact Hbl|].
  split; [exact HK|]. split; [exact MLE|].
  split; [rewrite (alc_call_trace_ok lyc _ regsT ch Htop) in HD; exact HD|].
  split; [exact Efd | exact Efs].
Qed.

(* the fresh block is none of the bytes the call's kept clause speaks of *)
Lemma akept_drop_block : forall lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop) ly1 S1 W1 mem1 md1 p n,
  AR segs B ly1 S1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B lyc Sc ++ [(p, n)] -> frames S1 = frames Sc ->
  (forall c q, frame_addr ly1 c q = frame_addr lyc c q) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi (fun a => E a \/ p <= a < p + req_size n) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof using SK LAWS segs_low.
intros lyc Sc W memc W2 mem2 slo shi E ly1 S1 W1 mem1 md1 p n HAR1 Ebl Efr Efa (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HinP : In (p, n) (ablocks B ly1 S1)) by (rewrite Ebl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR1 HinP) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
pose proof (req_size_pos n) as Hrq.
split.
{ intros a Ha Hw HnE. apply K1; [exact Ha | exact Hw |]. intros [HE'|Hs]; [exact (HnE HE') | lia]. }
split.
{ intros b m i Hb Hi HnE. apply (K2 b m i Hb Hi). intros [HE'|Hs]; [exact (HnE HE')|].
  apply in_split in Hb as (l1 & l2 & El).
  pose proof (sep_blocks_pos segs B LAWS ly1 S1 W1 mem1 md1 (b, m) (p, n) l1 l2 [] HAR1
    ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
split.
{ intros a Hi Hns He HnE. apply K3; [exact Hi | exact Hns | exact He |].
  intros [HE'|Hs]; [exact (HnE HE')|].
  exact (blk_img segs B LAWS ly1 S1 W1 mem1 md1 p n a HAR1 HinP Hs Hi). }
split.
{ intros c q a Hin Hr HnE. apply (K4 c q a Hin Hr). intros [HE'|Hs]; [exact (HnE HE')|].
  assert (Hin1 : In (c, q) (frames S1)) by (rewrite Efr; exact Hin).
  pose proof (sep_block_frame segs B LAWS ly1 S1 W1 mem1 md1 p n c q HAR1 HinP Hin1) as Hd.
  rewrite Efa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (frames_bounds segs B LAWS ly1 S1 W1 mem1 md1 c q HAR1 Hin1) as (Hf4 & Hfc & _).
  rewrite Efa in Hf4, Hfc.
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc c q) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc c q + fs_frame_bytes c) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc c q) (fs_frame_bytes c) Hnn) as Hse.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct Hr as [Hr | Hr].
  - lia.
  - pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap. lia. }
split; [exact K5 | exact K6].
Qed.
End a.
