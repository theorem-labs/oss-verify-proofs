(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainL.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 83fc676b2e5d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the dequeue loop's premise DMdeq.deq_pre (DMdeq.v:675-702) at the
   loop head 0x33a8c on the MERGE arm: from the registers and the lock bytes the 0x33a38 segment leaves
   (DMseg_rjL.at_RJL), its frame (only the lock word may differ from the merge's return memory), and the cells
   MergeBatches' return leaves (DMwalkIF.mb_post at 3e29c198d40: the global list's header, the temp list's
   header, the kept and the extracted lists linked).  The batch facts (placement, NoDup, the byte bound) come in
   already in deq_pre's form (DMdrainQ / DMdrainR derive them from the merge's model facts).
   rule 24: no function proved (kind: the premise of a loop already walked, DMdeq.tfib_deq_ok; the lane's reuse
   search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [keep_q]: a value outside the lock word survives the 0x33a38 segment's frame;
   - [deq_pre_merge]: DMdeq.deq_pre W ly regs1 mem1 ex Lk.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMwalkIF DMdrainQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMdeq AFer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the lock word of the quarantine: the only bytes the 0x33a38 segment may change on the loop path *)
Definition QW (a : Z) : Prop := A_QUAR + 152 <= a < A_QUAR + 156.

Lemma keep_q : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall x : word, ~ QW (bv_unsigned x) -> m' x = m x) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, 0 <= i < Z.of_nat n -> ~ QW (a + i)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HM A1 A2 HN HV. apply (val_mem_frame H m m' a n v); [|exact HV].
intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HN. lia.
Qed.

Section ml.
Variables (W : world tfibsegs) (ly : alayout) (regs1 : bvmap 5 word) (mem0 mem1 : word -> option byte).
Variables (ex Lk : list batch) (iw : chunk -> Z).
Let m0 := mrestrict (w_H W) mem0.
Let m1 := mrestrict (w_H W) mem1.
Let sp1 : Z := bv_unsigned (getr regs1 2).
(* the batch facts, in deq_pre's form *)
Hypothesis HLY : layout_ok ly.
Hypothesis HBF : forall b, In b (ex ++ Lk) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addrb ly b mod 8192 = 0 /\ kBatchBytes <= b_bytes b.
Hypothesis HND : List.NoDup (map b_self (ex ++ Lk)).
Hypothesis HSUM : sum_bytes (ex ++ Lk) <= 2 ^ 31.
(* where the primary space and Recycle's frame sit (layout_ok, DMdeq.LYB / Usp1) *)
Hypothesis HPR : kHighMemBeg <= ly_prim ly /\ ly_space ly + kSpaceSize <= ASAN_CEIL.
Hypothesis HspR : kHighMemBeg + DRSTACK <= sp1 /\ sp1 + LFRAME <= kHighMemEnd.
(* Recycle's frame (drain_pre_cf's stack window, Drain's sp - 80) *)
Hypothesis Hsp : ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly.
Hypothesis HAL : sp1 mod 16 = 0.
Hypothesis HPRS : forall a, sp1 - DRSTACK <= a < sp1 + LFRAME -> apresent (w_H W) mem1 a.
Hypothesis Htp : getr regs1 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs1 1).
(* DMseg_rjL.at_RJL's registers *)
Hypothesis R10 : getr regs1 10 = w64 A_QUAR.
Hypothesis R11 : getr regs1 11 = w64 kQuarantineMin.
Hypothesis R14 : getr regs1 14 = w64 (Z.of_nat (length ex)).
Hypothesis R15 : getr regs1 15 = w64 (la ly ex).
Hypothesis R16 : getr regs1 16 = w64 (Z.of_nat (length Lk)).
Hypothesis R5 : getr regs1 5 = w64 (fa ly Lk 0).
(* DMseg_rjL.at_RJL's lock bytes and its frame relative to the merge's return memory [mem0] *)
Hypothesis L152 : val_mem tfibsegs m1 (A_QUAR + 152) 1 1.
Hypothesis L153 : val_mem tfibsegs m1 (A_QUAR + 153) 1 1.
Hypothesis L154 : forall a, A_QUAR + 154 <= a < A_QUAR + 156 -> mbyte tfibsegs m1 a = Some (Z_to_bv 8 0).
Hypothesis HMEQ : forall x : word, ~ QW (bv_unsigned x) -> mem1 x = mem0 x.
(* DMwalkIF.mb_post's cells at [mem0] *)
Hypothesis CQS : val_mem tfibsegs m0 (A_QUAR + 160) 8 (Z.of_nat (length Lk)).
Hypothesis CQF : val_mem tfibsegs m0 (A_QUAR + 168) 8 (fa ly Lk 0).
Hypothesis CQL : val_mem tfibsegs m0 (A_QUAR + 176) 8 (la ly Lk).
Hypothesis CQB : val_mem tfibsegs m0 (A_QUAR + 184) 8 (sum_bytes Lk).
Hypothesis CT8 : val_mem tfibsegs m0 (sp1 + 8) 8 (fa ly ex 0).
Hypothesis CT24 : val_mem tfibsegs m0 (sp1 + 24) 8 (sum_bytes ex).
Hypothesis CLK : lcn ly iw m0 Lk 0.
Hypothesis CEX : lcn ly iw m0 ex 0.

Lemma Usp : 0 <= sp1 < 2 ^ 64.
Proof. unfold sp1. apply u64_range. Qed.

Local Ltac qconst := unfold QW, A_QUAR, A_ALLOCATOR, o_quar in *.
Local Ltac hconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, LFRAME, kBatchBytes, kSpaceSize in *.

(* a header word above the lock word survives *)
Lemma keep_hdr : forall off v, 160 <= off <= 184 -> val_mem tfibsegs m0 (A_QUAR + off) 8 v -> val_mem tfibsegs m1 (A_QUAR + off) 8 v.
Proof.
intros off v Ho HV. apply (keep_q (w_H W) mem0 mem1 _ 8 v HMEQ); [qconst; lia | qconst; cbn; lia | | exact HV].
intros i Hi. qconst. cbn in Hi. lia.
Qed.

(* a word of Recycle's frame survives *)
Lemma keep_stk : forall off v, 0 <= off <= 72 -> val_mem tfibsegs m0 (sp1 + off) 8 v -> val_mem tfibsegs m1 (sp1 + off) 8 v.
Proof.
intros off v Ho HV. pose proof Usp as U. pose proof HspR as [S1 S2].
apply (keep_q (w_H W) mem0 mem1 _ 8 v HMEQ); [lia | hconst; cbn; lia | | exact HV].
intros i Hi. qconst. hconst. cbn in Hi. lia.
Qed.

(* a word of a batch object survives *)
Lemma keep_batch : forall b off v, In b (ex ++ Lk) -> 0 <= off <= 8 ->
val_mem tfibsegs m0 (addrb ly b + off) 8 v -> val_mem tfibsegs m1 (addrb ly b + off) 8 v.
Proof.
intros b off v Hb Ho HV. destruct (HBF b Hb) as (B1 & B2 & B3 & B4). pose proof HPR as [P1 P2].
apply (keep_q (w_H W) mem0 mem1 _ 8 v HMEQ); [hconst; lia | hconst; cbn; lia | | exact HV].
intros i Hi. qconst. hconst. cbn in Hi. lia.
Qed.

Theorem deq_pre_merge : DMdeq.deq_pre W ly regs1 mem1 ex Lk.
Proof.
constructor.
- exact HLY.
- intros b Hb. exact (HBF b Hb).
- exact HND.
- exact HSUM.
- exact Hsp.
- exact HAL.
- exact HPRS.
- exact Htp.
- exact Hra.
- exact R10.
- exact R11.
- exact R14.
- rewrite <- la_lastaddr. exact R15.
- exact R16.
- rewrite <- fa_firstaddr. exact R5.
- (* the lock word: bytes 1, 1, 0, 0 *)
  apply (proj2 (val_mem4_bytes _ _ _)).
  change (YO0f.le_byte 257 4 0) with 1. change (YO0f.le_byte 257 4 1) with 1.
  change (YO0f.le_byte 257 4 2) with 0. change (YO0f.le_byte 257 4 3) with 0.
  pose proof (proj1 (val_mem1_byte _ _ _) L152) as B0. pose proof (proj1 (val_mem1_byte _ _ _) L153) as B1.
  change (YO0f.le_byte 1 1 0) with 1 in B0, B1.
  splits.
  + exact B0.
  + replace (A_QUAR + 152 + 1) with (A_QUAR + 153) by lia. exact B1.
  + replace (A_QUAR + 152 + 2) with (A_QUAR + 154) by lia. apply L154. lia.
  + replace (A_QUAR + 152 + 3) with (A_QUAR + 155) by lia. apply L154. lia.
- apply (keep_hdr 160); [lia | exact CQS].
- rewrite <- fa_firstaddr. apply (keep_hdr 168); [lia | exact CQF].
- rewrite <- la_lastaddr. apply (keep_hdr 176); [lia | exact CQL].
- apply (keep_hdr 184); [lia | exact CQB].
- intros i b Hi. pose proof (lcn_next ly iw m0 ex i b CEX Hi) as V.
  assert (Hb : In b (ex ++ Lk)) by (apply in_app_iff; left; exact (nth_error_In _ _ Hi)).
  rewrite <- (Z.add_0_r (addrb ly b)) in V. pose proof (keep_batch b 0 _ Hb ltac:(lia) V) as V'.
  rewrite Z.add_0_r in V'. exact V'.
- intros i b Hi.
  assert (Hb : In b (ex ++ Lk)) by (apply in_app_iff; right; exact (nth_error_In _ _ Hi)).
  pose proof (lcn_next ly iw m0 Lk i b CLK Hi) as V. pose proof (lcn_size ly iw m0 Lk 0 i b CLK Hi) as V8.
  rewrite <- (Z.add_0_r (addrb ly b)) in V. pose proof (keep_batch b 0 _ Hb ltac:(lia) V) as V'.
  rewrite Z.add_0_r in V'. split; [exact V' | exact (keep_batch b 8 _ Hb ltac:(lia) V8)].
- rewrite <- fa_firstaddr. exact (keep_stk 8 _ ltac:(lia) CT8).
- exact (keep_stk 24 _ ltac:(lia) CT24).
Qed.
End ml.
End c.
