(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 68 of its 121 lines of code are new or changed and 358 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: one malloc call whose trace may be WILD inside an own allocating function's walk, on the
   caller's journal ajournal_gx: LinkWalkAlloc.v amalloc04_sub_d / aj_gx_malloc_d over lib/A/Rt/LinkMallocDepotW.v
   amalloc04_rule_dw (trace premise `admits (as_universe B) (call_trace0 ...) Sc` instead of a fixed row), their proof
   bodies unchanged. For text_of's call at 0x87fec (the trace runs through a word of the caller's frame); the depot
   bound after it is LinkWalkAlloc.v alc_depot_any.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot LinkMallocDepotW.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkAlloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation code := (as_code B).

(* LinkWalkAlloc.v amalloc04_sub_d with the admits trace premise (its proof body) *)
Lemma amalloc04_sub_dw : amalloc04_rule_dw (SK := SK) segs B MT ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
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

(* MALLOC ON THE JOURNAL (LinkWalkAlloc.v aj_gx_malloc_d with the admits trace premise): the call's window [sp - ASTACK, sp) inside the journal's, sp 16 below the journal's sp0
   (the frame record is well formed); the descriptors and file system kept; the depot step of the call's trace *)
Lemma aj_gx_malloc_dw : amalloc04_rule_dw (SK := SK) segs B MT ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n raw ch,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ASTACK -> spZ regsT <= sp0 -> spZ regsT + 16 < sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S + k + 1 <= EV_MAX ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
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
  { exact (amalloc04_sub_dw AM W regsT memT (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc mdc k n
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

End a.
