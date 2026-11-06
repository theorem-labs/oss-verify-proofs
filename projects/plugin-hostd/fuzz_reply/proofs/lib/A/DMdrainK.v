(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainK.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 b10e949093fc) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the cell bridge from the quarantine's cells as DMiface.qview states
   them (cgif's cell vocabulary: YG0n.batch_cells / qc_cells over the view, DMiface.v:81 qv_cells) to the linked
   list form the MergeBatches slice and the dequeue loop read (DMwalkIF.lcn / bcell, with the slot word of an item
   [k] taken as the address of its chunk header).  So the drain's composition can hand MergeBatches its mb_cells
   and the dequeue loop its dq_CLK / dq_CEX from qview, without the allocator relation.
   rule 24: no function proved (kind: cell-shape lemmas over the released YFhf.batch_head_cells; the lane's
   reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle
   Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [iwB]: the slot word of an item;
   - [lcn_of_cells]: a list's batch cells give DMwalkIF.lcn with last next word 0;
   - [lcn_app_link]: two linked lists joined by the first's last next word are one linked list (the transfer of
     the thread cache onto the global cache: DMdeq's no-merge arm).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFeu AFey AFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMwalkIF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Variable ly : alayout.

(* The slot word of an item: the address of its chunk header (YG0n.batch_cells :83). *)
Definition iwB (k : chunk) : Z := aeval B ly (sptr_exp (ck_hdr k)).

Lemma fa_firstaddr_hf : forall t, fa ly t 0 = AFhf.firstaddr ly t.
Proof. intros [|b t]; reflexivity. Qed.

(* A list's batch cells, read through the view, give the linked list with last next word 0. *)
Lemma lcn_of_cells : forall (H : word -> bool) (mem : word -> option byte) (l : list batch),
Forall (cell_holds B ly (aview tfibsegs H mem)) (batch_cells l) ->
lcn ly iwB (mrestrict H mem) l 0.
Proof.
intros H mem l. induction l as [|b t IH]; intros HC; [exact I|].
cbn [lcn]. split.
- pose proof (AFhf.batch_head_cells B ly H mem b t HC) as (V0 & V8 & V16 & VS). cbv zeta in V0, V8, V16, VS.
  unfold bcell, addrb, zl. rewrite fa_firstaddr_hf. split; [exact V0|]. split; [exact V8|]. split; [exact V16|].
  intros j k Hj. exact (VS j k Hj).
- apply IH. exact (AFhf.batch_cells_tail B ly _ b t HC).
Qed.

Lemma fa_app_k : forall l1 l2 z, fa ly (l1 ++ l2) z = fa ly l1 (fa ly l2 z).
Proof. intros [|b l1] l2 z; reflexivity. Qed.

(* Two linked lists joined: the first's cells with last next word [fa l2 z] and the second's with [z]. *)
Lemma lcn_app_link : forall iw m l1 l2 z, lcn ly iw m l1 (fa ly l2 z) -> lcn ly iw m l2 z -> lcn ly iw m (l1 ++ l2) z.
Proof.
intros iw m l1. induction l1 as [|b t IH]; intros l2 z H1 H2; [exact H2|].
cbn [app lcn] in *. destruct H1 as [Hb Ht]. split.
- rewrite fa_app_k. exact Hb.
- exact (IH l2 z Ht H2).
Qed.
End d.
End c.
