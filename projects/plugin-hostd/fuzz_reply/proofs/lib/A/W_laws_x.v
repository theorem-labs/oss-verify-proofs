(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the AR instance of the generic laws, built from cgif's AR_laws ALONE, at any segs and B.
   YCbqG.v:1677 AR_laws_x_of_AR takes three facts beyond AR_laws (ly_stk_lo / ly_stk_hi 8-aligned; a live block's
   tail granule viewable; the const cells holding). All three are theorems of cgif's AR itself, so no lane proves them
   at any image:
   - AR_stk8: layout_ok's lo_top makes both stack bounds page-aligned (Reusable/YG0f.v:325-327), and AR carries
     layout_ok as ARm's am_layout (Reusable/YG0n.v:209);
   - AR_tail: W7's W_alloc_tail.alloc_tail (lib/A/W_alloc_tail.v), over the same range written two ways;
   - AR_const: ARm's am_const (Reusable/YG0n.v:211), as W_journal.v:386 reads it.
   So LX / LX0, the laws a re-derived AR theorem takes in place of LAWS, are AR_laws_x_ARi_of / AR_laws_x_ARi0_of
   applied to LAWS. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_alloc_tail W_journal_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Lemma AR_stk8 : forall ly S W mem md, AR segs B ly S W mem md -> ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0.
Proof.
intros ly S W mem md (HM & _).
pose proof (lo_top _ (am_layout _ _ _ _ HM)) as (_ & _ & _ & _ & H1 & H2 & _).
unfold page_aligned in H1, H2. try unfold page_size in H1, H2.
assert (D : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->].
  replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
split; apply D; assumption.
Qed.
Lemma AR_tail : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < (p + req_size n + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
apply (alloc_tail segs B ly S W mem md p n a HAR Hin).
assert (E : (p + req_size n + 7) / 8 * 8 = p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8).
{ replace (p + req_size n + 7) with (p + req_size n - 1 + 1 * 8) by lia.
  rewrite Z.div_add by lia. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma AR_const : forall ly S W mem md, AR segs B ly S W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Proof. intros ly S W mem md (HM & _). exact (am_const _ _ _ _ HM). Qed.
(* THE LAWS AT THE AR INSTANCES, from AR_laws alone *)
Lemma AR_laws_x_ARi_of : AR_laws segs B -> AR_laws_x segs B (ARi segs B) 0.
Proof. intros L. exact (AR_laws_x_of_AR segs B L AR_stk8 AR_tail AR_const). Qed.
Lemma AR_laws_x_ARi0_of : AR_laws segs B -> AR_laws_x segs B (ARi0 segs B) 0.
Proof. intros L. exact (AR_laws_x_ARi0 segs B (AR_laws_x_ARi_of L)). Qed.
End l.
