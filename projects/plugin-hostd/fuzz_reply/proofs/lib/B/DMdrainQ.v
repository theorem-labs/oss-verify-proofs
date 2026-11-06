(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainQ.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 49093746176e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainQ.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the bridge between the MergeBatches slice's cell vocabulary
   (DMwalkIF.lcn / fa / la, the linked-list form the merge proves) and the dequeue loop's premise
   (DMdeq.deq_pre, which states the same cells as YFey.next_addr indices), plus the batch facts the loop asks of
   the post-merge lists.  No machine, no walk: these are list and memory-shape lemmas, so the drain's composition
   can be assembled before the slices land.
   rule 24: no function proved (kind: shape lemmas; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record),
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).

   - [lcn_next] / [lcn_size] / [lcn_count]: the linked list gives DMdeq's dq_CEX / dq_CLK cells;
   - [fa_firstaddr] / [la_lastaddr]: DMwalkIF's fa / la are DMdeq's firstaddr / lastaddr;
   - [b_bytes_lb]: a batch with non-negative items weighs at least kBatchBytes (DMdeq's dq_BF last conjunct);
   - [nodup_app_of_in]: NoDup over the two post-merge lists from NoDup over the entry list and the slice's
     membership and length facts (DMwalkIF.mb_model_facts);
   - [sum_split]: the byte bound of the two post-merge lists from the entry list's (dq_SUM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFeu YFey YFer.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The linked list's cells, by index.                                                                           *)
Lemma lcn_nth : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
bcell ly iw m b (fa ly (skipn (S i) l) z).
Proof.
intros ly iw m l z i. revert l. induction i as [|i IH]; intros [|b0 t] b HL HN; cbn [nth_error] in HN;
try discriminate; cbn [lcn skipn] in *.
- injection HN as <-. exact (proj1 HL).
- exact (IH t b (proj2 HL) HN).
Qed.

Lemma fa_skipn : forall ly l i, fa ly (skipn (S i) l) 0 = next_addr ly l i.
Proof.
intros ly l. unfold next_addr, fa, addrb.
induction l as [|b t IH]; intros [|i]; cbn [skipn nth_error]; try reflexivity.
- destruct t as [|b1 t1]; reflexivity.
- exact (IH i).
Qed.

Lemma lcn_next : forall ly iw m l i b,
lcn ly iw m l 0 -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b) 8 (next_addr ly l i).
Proof.
intros ly iw m l i b HL HN. pose proof (lcn_nth ly iw m l 0 i b HL HN) as HC.
rewrite fa_skipn in HC. exact (proj1 HC).
Qed.

Lemma lcn_size : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b).
Proof.
intros ly iw m l z i b HL HN. pose proof (lcn_nth ly iw m l z i b HL HN) as HC.
exact (proj1 (proj2 HC)).
Qed.

Lemma lcn_count : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b + 16) 8 (Z.of_nat (length (b_items b))).
Proof.
intros ly iw m l z i b HL HN. pose proof (lcn_nth ly iw m l z i b HL HN) as HC.
exact (proj1 (proj2 (proj2 HC))).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The list-head values: DMwalkIF's fa / la are the loop's first / last addresses.                              *)
Lemma fa_firstaddr : forall ly l, fa ly l 0 = YFer.firstaddr ly l.
Proof. intros ly [|b t]; reflexivity. Qed.

Lemma la_lastaddr : forall ly l, la ly l = YFer.lastaddr ly l.
Proof. intros ly l. unfold la, YFer.lastaddr, addrb, YFer.addr. destruct (rev l); reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The byte and placement facts of the post-merge lists.                                                        *)
Lemma b_bytes_lb : forall b, (forall k, In k (b_items b) -> 0 <= ck_n k) -> kBatchBytes <= b_bytes b.
Proof.
intros b H. unfold b_bytes.
assert (A : 0 <= fold_right (fun k acc => ck_n k + acc) 0 (b_items b)).
{ induction (b_items b) as [|k l IH]; cbn [fold_right]; [lia|].
  pose proof (H k (or_introl eq_refl)). pose proof (IH (fun k' Hk => H k' (or_intror Hk))). lia. }
lia.
Qed.

Lemma sum_bytes_app_q : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof.
induction l1 as [|b l IH]; intros l2; cbn [app]; [reflexivity|].
rewrite !YFey.sum_bytes_cons, IH. lia.
Qed.

(* The entry list's byte bound carries to the two post-merge lists: the kept bytes plus kBatchBytes per extracted
   batch are the entry bytes (DMwalkIF.mb_model_facts' first clause). *)
Lemma sum_split : forall L0 Lk ex,
sum_bytes Lk + kBatchBytes * Z.of_nat (length ex) = sum_bytes L0 ->
(forall b, In b ex -> b_items b = []) ->
sum_bytes L0 <= 2 ^ 31 -> (forall b, In b Lk -> forall k, In k (b_items b) -> 0 <= ck_n k) ->
sum_bytes (ex ++ Lk) <= 2 ^ 31.
Proof.
intros L0 Lk ex HS HE HB HN. rewrite sum_bytes_app_q.
assert (AE : sum_bytes ex = kBatchBytes * Z.of_nat (length ex)).
{ clear HS. induction ex as [|b t IH]; cbn [length]; [reflexivity|].
  rewrite YFey.sum_bytes_cons, (IH (fun b' Hb' => HE b' (or_intror Hb'))).
  unfold b_bytes. rewrite (HE b (or_introl eq_refl)). cbn [fold_right]. lia. }
rewrite AE. lia.
Qed.

(* NoDup over the two post-merge lists, from the entry list's and the slice's membership / length facts.
   List.NoDup, not stdpp's: DMdeq.dq_ND (DMdeq.v:679) is the Stdlib one.  [nodup_of_stdpp] bridges the other
   way, for DMiface.qview's qv_nodup (DMiface.v:96), which is stdpp's. *)
Lemma nodup_of_stdpp : forall (l : list Z), NoDup l -> List.NoDup l.
Proof. intros l H. apply NoDup_ListNoDup. exact H. Qed.

Lemma nodup_app_of_in : forall (L0 Lk ex : list batch),
List.NoDup (map b_self L0) ->
(forall s, In s (map b_self L0) <-> In s (map b_self Lk ++ map b_self ex)) ->
length L0 = (length Lk + length ex)%nat ->
List.NoDup (map b_self (ex ++ Lk)).
Proof.
intros L0 Lk ex HND HIN HL.
assert (HP : forall s, In s (map b_self L0) -> In s (map b_self (ex ++ Lk))).
{ intros s H. rewrite map_app. apply HIN in H. apply in_app_iff.
  apply in_app_iff in H as [H|H]; [right | left]; exact H. }
assert (HLen : length (map b_self (ex ++ Lk)) = length (map b_self L0)).
{ rewrite !length_map, length_app. lia. }
apply (NoDup_incl_NoDup HND); [lia | exact HP].
Qed.

End d.
