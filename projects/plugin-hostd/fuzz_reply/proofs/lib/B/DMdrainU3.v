(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU3.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 a439da6ae1b6) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU3.v at commit 2e76ed2595c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the two linked lists at Recycle's call of DoRecycle (0x33b54),
   from the dequeue loop's post DMdeq.ATDR (DMdeq.v:193-207): the TEMP list [P] at Recycle's sp and the KEPT
   list [R] in the quarantine.  The loop writes only each popped batch's NEXT word (DMdeq.DW, DMdeq.v:173-175),
   so a batch's size, count and slot words survive from the loop's entry memory and are carried over by the
   frame; the next words come from ATDR itself.
   - [cells_off_dw]: a batch's cells beyond its next word lie outside the loop's written set.  The stack and
     the quarantine header are apart from the primary space (DMdrainT7.prim_apart, layout_ok), and two batches
     are either the same object or 8192 apart (DMdeq.apart8192).
   - [lcn_from_parts]: a linked list from its next words (by index) and its other cells (by membership).
   - [plist_lcn] / [kept_lcn]: DMwalkIF.lcn for [P] and for [R] at the call's memory, which is what
     DMdrainC.dr_pre_at_call (DMdrainC.v:105) takes as HPL and what the kept quarantine's cut relation needs.
   rule 24: no function proved (kind: list and memory-shape lemmas at a cut of a loop already walked; the
   lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle
   QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMwalkIF DMdrainK DMdrainQ DMdrainG1 DMdrainT7.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMdeq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A linked list from its next words (by index) and its other cells (by membership). *)
Lemma lcn_from_parts : forall ly iw (m : word -> option byte) (l : list batch) (z : Z),
(forall i b, nth_error l i = Some b -> val_mem tfibsegs m (addrb ly b) 8 (fa ly (skipn (S i) l) z)) ->
(forall b, In b l ->
   val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b) /\
   val_mem tfibsegs m (addrb ly b + 16) 8 (zl (b_items b)) /\
   (forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k))) ->
lcn ly iw m l z.
Proof.
intros ly iw m l. induction l as [|b t IH]; intros z HN HC; [exact I|].
split.
- destruct (HC b (or_introl eq_refl)) as (C8 & C16 & CS).
  split; [|split; [exact C8 | split; [exact C16 | exact CS]]].
  exact (HN 0%nat b eq_refl).
- apply IH.
  + intros i b2 Hi. exact (HN (S i) b2 Hi).
  + intros b2 Hb2. exact (HC b2 (or_intror Hb2)).
Qed.

Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs1 : bvmap 5 word) (mem1 mem' : word -> option byte).
Variables (P R : list batch).
Let m1 := mrestrict (w_H W) mem1.
Let m' := mrestrict (w_H W) mem'.
Let sp1 : Z := bv_unsigned (getr regs1 2).
Local Notation iw := (DMdrainK.iwB B ly).

Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + YFeu.DRSTACK <= sp1 /\ sp1 + YFeu.LFRAME <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (P ++ R) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
Hypothesis HSLOT : forall b, In b (P ++ R) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
(* DMdeq.ATDR's raw frame (DMdeq.v:198), in address form *)
Hypothesis HFR : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 <= a < sp1 + 32) -> ~ (A_QUAR + 152 <= a < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= a < addrb ly b + 8)) ->
  mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).
(* the joined list at the loop's entry *)
Hypothesis HLL : lcn ly iw m1 (P ++ R) 0.
(* DMdeq.ATDR's next words (DMdeq.v:204-205) *)
Hypothesis HPN : forall i b, nth_error P i = Some b ->
  val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly P i).
Hypothesis HRN : forall i b, nth_error R i = Some b ->
  val_mem tfibsegs m' (addrb ly b) 8 (next_addr ly R i).
(* the same cells per batch, for an arm whose two lists are not one linked list at the loop's entry
   (the merge arm: the temp list ex and the global list gm; DMdrainU9.recyc_cut_in) *)
Hypothesis HCL : forall b, In b (P ++ R) ->
  val_mem tfibsegs m1 (addrb ly b + 8) 8 (b_bytes b) /\
  val_mem tfibsegs m1 (addrb ly b + 16) 8 (zl (b_items b)) /\
  (forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m1 (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).

(* A batch's cells beyond its next word are outside the loop's written set. *)
Lemma cells_off_dw : forall b a, In b (P ++ R) ->
addrb ly b + 8 <= a < addrb ly b + 24 + 8 * zl (b_items b) ->
0 <= a < 2 ^ 64 /\ ~ (sp1 <= a < sp1 + 32) /\ ~ (A_QUAR + 152 <= a < A_QUAR + 192) /\
(forall b2, In b2 P -> ~ (addrb ly b2 <= a < addrb ly b2 + 8)).
Proof.
intros b a Hb Ha.
destruct (BADDR b Hb) as (A1 & A2 & A3 & A4).
pose proof (HSLOT b Hb) as HS.
assert (HCB : 24 + 8 * zl (b_items b) <= kBatchBytes).
{ unfold zl, kBatchBytes. unfold kBatchSlots in HS. lia. }
pose proof (DMdrainG1.LYB2 ly LY) as (L1 & L2 & L3 & L4 & _).
pose proof (DMdrainT7.prim_apart ly LY) as [_ PS].
destruct HSP as [S1 S2]. ceil.
unfold A_QUAR, A_ALLOCATOR, o_quar, kSpaceSize, kPrimResvSize, kBatchBytes, kHighMemBeg, YFeu.DRSTACK, YFeu.LFRAME in *.
splits.
- lia.
- lia.
- intros HQ. lia.
- lia.
- intros b2 Hb2 HR2.
  assert (Hin2 : In b2 (P ++ R)) by (apply in_app_iff; left; exact Hb2).
  destruct (BADDR b2 Hin2) as (B1 & B2 & B3 & B4).
  destruct (Z.eq_dec (addrb ly b2) (addrb ly b)) as [E|NE]; [lia|].
  destruct (DMdeq.apart8192 (addrb ly b) (addrb ly b2) A3 B3 ltac:(lia)); lia.
Qed.

(* Every batch keeps its size, count and slot words at the call. *)
Lemma cells_keep : forall b, In b (P ++ R) ->
val_mem tfibsegs m' (addrb ly b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m' (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m' (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
Proof.
intros b Hb.
destruct (In_nth_error _ _ Hb) as [i Hi].
pose proof (DMdrainQ.lcn_nth ly iw m1 (P ++ R) 0 i b HLL Hi) as (N0 & C8 & C16 & CS).
pose proof (HSLOT b Hb) as HS.
assert (FRM : forall off (n : nat), 8 <= off -> off + Z.of_nat n <= 24 + 8 * zl (b_items b) ->
  forall v, val_mem tfibsegs m1 (addrb ly b + off) n v -> val_mem tfibsegs m' (addrb ly b + off) n v).
{ intros off n Hlo Hhi v HV. unfold m1, m' in *.
  apply (YF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
  intros k Hk. apply HFR.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (H1 & _). exact H1.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & H2 & _). exact H2.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & H3 & _). exact H3.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & _ & H4). exact H4. }
splits.
- exact (FRM 8 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C8).
- exact (FRM 16 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C16).
- intros j k Hj.
  assert (HJ : (j < length (b_items b))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  replace (addrb ly b + 24 + 8 * Z.of_nat j) with (addrb ly b + (24 + 8 * Z.of_nat j)) by lia.
  apply (FRM (24 + 8 * Z.of_nat j) 8%nat ltac:(lia) ltac:(unfold zl; lia)).
  replace (addrb ly b + (24 + 8 * Z.of_nat j)) with (addrb ly b + 24 + 8 * Z.of_nat j) by lia.
  exact (CS j k Hj).
Qed.

(* The temp list and the kept list, linked, at Recycle's call. *)
Lemma plist_lcn : lcn ly iw m' P 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HPN i b Hi).
- intros b Hb. apply cells_keep. apply in_app_iff. left. exact Hb.
Qed.

Lemma kept_lcn : lcn ly iw m' R 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HRN i b Hi).
- intros b Hb. apply cells_keep. apply in_app_iff. right. exact Hb.
Qed.
(* The same from the per-batch cells. *)
Lemma cells_keep_c : forall b, In b (P ++ R) ->
val_mem tfibsegs m' (addrb ly b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m' (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m' (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
Proof.
intros b Hb.
destruct (HCL b Hb) as (C8 & C16 & CS).
pose proof (HSLOT b Hb) as HS.
assert (FRM : forall off (n : nat), 8 <= off -> off + Z.of_nat n <= 24 + 8 * zl (b_items b) ->
  forall v, val_mem tfibsegs m1 (addrb ly b + off) n v -> val_mem tfibsegs m' (addrb ly b + off) n v).
{ intros off n Hlo Hhi v HV. unfold m1, m' in *.
  apply (YF0x.val_mem_frame (w_H W) mem1 mem'); [|exact HV].
  intros k Hk. apply HFR.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (H1 & _). exact H1.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & H2 & _). exact H2.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & H3 & _). exact H3.
  - destruct (cells_off_dw b (addrb ly b + off + Z.of_nat k) Hb ltac:(lia)) as (_ & _ & _ & H4). exact H4. }
splits.
- exact (FRM 8 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C8).
- exact (FRM 16 8%nat ltac:(lia) ltac:(unfold zl; lia) _ C16).
- intros j k Hj.
  assert (HJ : (j < length (b_items b))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  replace (addrb ly b + 24 + 8 * Z.of_nat j) with (addrb ly b + (24 + 8 * Z.of_nat j)) by lia.
  apply (FRM (24 + 8 * Z.of_nat j) 8%nat ltac:(lia) ltac:(unfold zl; lia)).
  replace (addrb ly b + (24 + 8 * Z.of_nat j)) with (addrb ly b + 24 + 8 * Z.of_nat j) by lia.
  exact (CS j k Hj).
Qed.


Lemma plist_lcn_c : lcn ly iw m' P 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HPN i b Hi).
- intros b Hb. apply cells_keep_c. apply in_app_iff. left. exact Hb.
Qed.

Lemma kept_lcn_c : lcn ly iw m' R 0.
Proof.
apply lcn_from_parts.
- intros i b Hi. rewrite DMdrainQ.fa_skipn. exact (HRN i b Hi).
- intros b Hb. apply cells_keep_c. apply in_app_iff. right. exact Hb.
Qed.
End g.
End f.
