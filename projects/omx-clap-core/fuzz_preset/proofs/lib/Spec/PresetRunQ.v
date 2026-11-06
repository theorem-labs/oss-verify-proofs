(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Spec/PresetRunQ.v, with its module paths changed. *)
(* omx-clap-core/fuzz_preset, Spec: hfrees_q, the freed requests of an event list that ENTER the quarantine, and nothing
   else. Theorem Labs, 2026-10, for the kit.
   Quarantine::Put enqueues a chunk only when its user size is at most max_size = kQuarantineMax (compiler-rt
   llvmorg-20.1.8 sanitizer_quarantine.h:96-108); a larger chunk is recycled at once (YG00cf.free_cf's size test). So
   the quarantine's FIFO history (YGcfFrees.cf_frees_follow, P8's fifo_ok) follows hfrees_q, not hfrees: a free above
   kQuarantineMax is in the run's frees but never in the quarantine. iface_room_pos (PresetRoomPos.v) and P8
   (PresetP8.v, PresetClose17.v) read hfrees_q.
   The leaf adds no file to the kit's Require closure beyond YG00 and PresetRun, which PresetRoomPos already Requires.
   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetReqAt PresetRun.
Import ListNotations.
Local Open Scope Z_scope.

(* the frees that enter the quarantine: free_cf's enqueue side *)
Definition hfrees_q (es : list hev) : list Z := filter (fun n => req_size n <=? kQuarantineMax) (hfrees es).

(* the same filter on a list of requests (a bulk event's L, a prefix of it) *)
Definition qfilter (l : list Z) : list Z := filter (fun n => req_size n <=? kQuarantineMax) l.

Lemma hfrees_q_eq : forall es, hfrees_q es = qfilter (hfrees es).
Proof. reflexivity. Qed.

Lemma qfilter_app : forall a b, qfilter (a ++ b) = qfilter a ++ qfilter b.
Proof. intros a b. unfold qfilter. apply filter_app. Qed.

Lemma hfrees_q_app : forall a b, hfrees_q (a ++ b) = hfrees_q a ++ hfrees_q b.
Proof. intros a b. rewrite !hfrees_q_eq, hfrees_app. apply qfilter_app. Qed.

Lemma qfilter_nil : qfilter [] = [].
Proof. reflexivity. Qed.

Lemma qfilter_small : forall n, req_size n <= kQuarantineMax -> qfilter [n] = [n].
Proof. intros n H. unfold qfilter. cbn [filter]. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma qfilter_big : forall n, kQuarantineMax < req_size n -> qfilter [n] = [].
Proof. intros n H. unfold qfilter. cbn [filter]. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma qfilter_all : forall l, Forall (fun n => req_size n <= kQuarantineMax) l -> qfilter l = l.
Proof.
induction l as [|n l IH]; intros H; [reflexivity|].
apply Forall_cons_iff in H as [Hn Hl]. unfold qfilter in *. cbn [filter].
rewrite (proj2 (Z.leb_le _ _) Hn), (IH Hl). reflexivity.
Qed.

(* a request below the bound by its own value is below it as req_size *)
Lemma req_size_le : forall n, n <= kQuarantineMax -> req_size n <= kQuarantineMax.
Proof. intros n H. unfold req_size, kQuarantineMax in *. destruct (n =? 0); lia. Qed.

(* the filter only drops: a count over the filtered list is at most the count over the list *)
Lemma qfilter_filter_le : forall (f : Z -> bool) l, (length (filter f (qfilter l)) <= length (filter f l))%nat.
Proof.
intros f l. unfold qfilter. induction l as [|n l IH]; [reflexivity|]. cbn [filter].
destruct (req_size n <=? kQuarantineMax); cbn [filter]; destruct (f n); cbn [length]; lia.
Qed.
