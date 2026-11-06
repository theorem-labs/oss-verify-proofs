(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainM.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 8ff451dee32c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the MODEL side of the real-merge drain top: the shared instance's
   drain tree [DMspec.drain_body_cf] cut at the two places the walk cuts it, and [DMspec.merge_split_cf] in the
   vocabulary the MergeBatches slice proves (DMwalkIF.MB).  No machine, no walk: every lemma is about the model
   of YG00cf.v / DMspec.v, so the drain's composition can be written against it before the walk slices land.
   rule 24: no function proved (kind: model lemmas; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record),
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).

   - [drain_body_cf_xfer]: when the transferred quarantine is within kQuarantineMax, the whole tree is the
     transfer (DMiface.drain_xfer's state);
   - [drain_body_cf_rec]: otherwise it is the transfer followed by [recycle_body_cf] at the transferred cache;
   - [merge_split_cf_MB] / [merge_split_cf_triv]: the merge split in terms of DMwalkIF.MB;
   - [recycle_body_cf_run]: recycle_body_cf unfolded at the kept cache and the extracted batches, the form
     DMiface.drain_recyc states;
   - [drain_recyc_intro]: drain_recyc from the walk's facts (the merge's (gm, ex) and the dequeue's (g', popped)).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DMwalkIF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* The transferred quarantine and the state after the transfer. *)
Definition gxf (X : astate) : qcache := YFeuC.transfer_g X.
Definition sxf (X : astate) : astate := set_qglobal (gxf X) (set_qthread qc0 X).

Lemma gxf_list : forall X, qc_list (gxf X) = qc_list (st_qglobal X) ++ qc_list (st_qthread X).
Proof. intros X. reflexivity. Qed.
Lemma gxf_bytes : forall X, qc_bytes (gxf X) = qc_bytes (st_qglobal X) + qc_bytes (st_qthread X).
Proof. intros X. reflexivity. Qed.

(* The drain tree's first cut: the transfer, then the test on the transferred bytes. *)
Lemma drain_body_cf_unfold : forall X,
drain_body_cf X X =
(if qc_bytes (gxf X) <=? kQuarantineMax then ret tt (sxf X) else recycle_body_cf (gxf X) (sxf X)).
Proof.
intros X. unfold drain_body_cf, gxf, sxf. unfold bind at 1. unfold put. cbn [ibind].
destruct (qc_bytes (YFeuC.transfer_g X) <=? kQuarantineMax); reflexivity.
Qed.

Lemma drain_body_cf_xfer : forall X,
qc_bytes (gxf X) <= kQuarantineMax -> drain_body_cf X X = ret tt (sxf X).
Proof.
intros X H. rewrite drain_body_cf_unfold.
destruct (Z.leb_spec (qc_bytes (gxf X)) kQuarantineMax); [reflexivity | lia].
Qed.

Lemma drain_body_cf_rec : forall X,
kQuarantineMax < qc_bytes (gxf X) -> drain_body_cf X X = recycle_body_cf (gxf X) (sxf X).
Proof.
intros X H. rewrite drain_body_cf_unfold.
destruct (Z.leb_spec (qc_bytes (gxf X)) kQuarantineMax); [lia | reflexivity].
Qed.

(* DMiface.drain_xfer holds exactly at that state. *)
Lemma drain_xfer_intro : forall X, qc_bytes (gxf X) <= kQuarantineMax -> drain_xfer X (sxf X).
Proof. intros X H. split; [exact H | reflexivity]. Qed.

(* The merge split in the slice's vocabulary (DMwalkIF.MB = merge_batches_cf with exact fuel). *)
Definition mtest (g : qcache) : bool :=
(kBatchBytes * Z.of_nat (length (qc_list g)) <? qc_bytes g) &&
(qc_bytes g <? 2 * (kBatchBytes * Z.of_nat (length (qc_list g)))).

Lemma merge_split_cf_MB : forall g, mtest g = true ->
merge_split_cf g =
(mkQC (fst (MB (qc_list g))) (qc_bytes g - kBatchBytes * Z.of_nat (length (snd (MB (qc_list g))))),
 snd (MB (qc_list g))).
Proof.
intros g H. unfold merge_split_cf, mtest in *. rewrite H. unfold MB.
destruct (merge_batches_cf (length (qc_list g)) (qc_list g)) as [l' ex] eqn:E. cbn [fst snd]. reflexivity.
Qed.

Lemma merge_split_cf_triv : forall g, mtest g = false -> merge_split_cf g = (g, []).
Proof. intros g H. unfold merge_split_cf, mtest in *. rewrite H. reflexivity. Qed.

(* recycle_body_cf at a kept cache [gm] and extracted batches [ex]: the dequeue, then do_recycle over
   [ex ++ popped], the tree DMiface.drain_recyc describes. *)
Lemma recycle_body_cf_run : forall g gm ex g' popped St,
merge_split_cf g = (gm, ex) -> pop_batches (S (length (qc_list gm))) gm [] = (g', popped) ->
recycle_body_cf g St =
do_recycle (length (ex ++ popped)) (ex ++ popped) (set_qglobal g' St).
Proof.
intros g gm ex g' popped St HM HP. unfold recycle_body_cf. rewrite HM, HP.
unfold bind at 1. unfold modify. cbn [ibind]. reflexivity.
Qed.

(* DMiface.drain_recyc from the two model steps. *)
Lemma drain_recyc_intro : forall X gm ex g' popped,
kQuarantineMax < qc_bytes (gxf X) ->
merge_split_cf (gxf X) = (gm, ex) ->
pop_batches (S (length (qc_list gm))) gm [] = (g', popped) ->
drain_recyc X (set_qglobal g' (set_qthread qc0 X)) (ex ++ popped).
Proof.
intros X gm ex g' popped HB HM HP. unfold drain_recyc. split; [exact HB|].
exists gm, ex, g', popped. split; [exact HM|]. split; [exact HP|]. split; reflexivity.
Qed.

End d.
