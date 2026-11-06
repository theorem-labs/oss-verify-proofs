(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma enqueue_room_eq : forall k X, need_new_batch (st_qthread X) = false ->
enqueue k X = IRet (tt, set_qthread (qc_push (st_qthread X) k None) X).
Proof.
intros k X HNB. unfold enqueue, get, modify, ret, bind. cbn [ibind]. rewrite HNB. cbn [ibind]. img_refl.
Qed.
Lemma WfP_qpush_room : forall U pp cc bb s kq,
WfP U pp cc bb s ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
need_new_batch (st_qthread s) = false ->
WfP U pp cc bb (set_qthread (qc_push (st_qthread s) kq None) s).
Proof.
intros U pp cc bb s kq W Hk Hst Hnotin Hnb.
assert (QI' : all_batches s <> []).
{ unfold all_batches. intros E. apply app_eq_nil in E as [E _]. unfold need_new_batch in Hnb. rewrite E in Hnb. cbn in Hnb. discriminate. }
destruct (qc_list_push (st_qthread s) kq None ltac:(img_try (intros _; img_exact Hnb))) as (T0 & bl & EL & CASE & EB).
set (q' := qc_push (st_qthread s) kq None) in *.
wf_fields W. quar_fields Xq.
destruct CASE as (lastb & ET & Ebl & Hlen).
pose proof (proj1 (Forall_forall _ _) Qbat lastb ltac:(img_try (unfold all_batches; rewrite ET, <- app_assoc; img_apply in_elt))) as BL.
assert (AB : all_batches (set_qthread q' s) = (T0 ++ [bl]) ++ qc_list (st_qglobal s)) by (img_try (unfold all_batches; cbn [st_qthread st_qglobal set_qthread]; rewrite EL; img_refl)).
assert (AB0 : all_batches s = (T0 ++ [lastb]) ++ qc_list (st_qglobal s)) by (img_try (unfold all_batches; rewrite ET; img_refl)).
assert (QI : q_items (set_qthread q' s) = (flat_map b_items T0 ++ b_items lastb ++ [kq]) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB, !flat_map_app. cbn [flat_map]. rewrite Ebl. cbn [b_items]. rewrite app_nil_r, app_assoc. img_refl. }
assert (QI0 : q_items s = (flat_map b_items T0 ++ b_items lastb) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB0, !flat_map_app. cbn [flat_map]. rewrite app_nil_r. img_refl. }
assert (PQ : Permutation (q_items (set_qthread q' s)) (kq :: q_items s)).
{ rewrite QI, QI0. rewrite !app_assoc. rewrite <- (app_assoc (flat_map b_items T0 ++ b_items lastb) [kq]). cbn [app].
img_apply Permutation_sym. img_apply Permutation_middle. }
assert (SELF : map b_self (all_batches (set_qthread q' s)) = map b_self (all_batches s)).
{ rewrite AB, AB0, !map_app. cbn [map]. rewrite Ebl. img_refl. }
assert (PB : batch_offs (set_qthread q' s) kBatchClass = batch_offs s kBatchClass).
{ rewrite !batch_offs_24, !boffs_map, SELF. img_refl. }
constructor; wf_easy.
- intros c Hc. unfold wf_class. cbn [st_cache_inited set_qthread]. img_change (reg (set_qthread q' s) c) with (reg s c). img_change (cache (set_qthread q' s) c) with (cache s c).
rewrite (chunk_offs_begs s) by img_refl.
pose proof (Xcl c Hc) as C. unfold wf_class in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne]; [img_try (rewrite PB; img_exact C)|].
rewrite !batch_offs_other by img_exact Hne. rewrite batch_offs_other in C by img_exact Hne. img_exact C.
- constructor; cbn [st_qthread st_qglobal st_chunks set_qthread]; try assumption.
+ (subst q'; cbv beta). rewrite EB, EL, sum_bytes_app. rewrite Qbt, ET, sum_bytes_app. rewrite Ebl. cbn [sum_bytes fold_right]. rewrite b_bytes_app1. cbn [sum_bytes fold_right]. img_lia.
+ rewrite AB. rewrite AB0 in Qbat. rewrite <- app_assoc in Qbat |- *. apply Forall_app in Qbat as [Q1 Q2]. apply Forall_app in Q2 as [_ Q3].
img_apply Forall_app. split; [img_try (img_exact Q1)|]. constructor; [|img_try (img_exact Q3)]. rewrite Ebl. cbn [b_items]. rewrite length_app. cbn [length]. unfold kBatchSlots in *. img_lia.
+ eapply Forall_Permutation; [img_try (img_apply Permutation_sym; img_exact PQ)|]. constructor; [img_try (split; assumption) | img_try (img_exact Qit)].
+ eapply NoDup_Permutation; [img_try (img_apply Permutation_map; img_apply Permutation_sym; img_exact PQ)|]. cbn [map]. constructor; [img_try (img_exact Hnotin) | img_try (img_exact Qnd)].
+
(subst q'; cbv beta). rewrite EL. rewrite ET in Qtf. rewrite removelast_snoc in Qtf |- *. img_exact Qtf.
- cbn [st_nev set_qthread]. rewrite AB. rewrite AB0 in Xbev. rewrite !length_app in *. cbn [length] in *. img_lia.
- cbn [st_cache_inited set_qthread]. intros _. img_exact (Xqi QI').
- intros c Hc. eapply fa_room_xfer; [img_try (img_exact (Xroom c Hc)) | | img_try (img_apply Z.le_refl)].
cbn [st_nev set_qthread]. unfold class_elems. img_change (reg (set_qthread q' s) c) with (reg s c). img_change (cache (set_qthread q' s) c) with (cache s c).
img_change (chunk_offs (set_qthread q' s) c) with (chunk_offs s c).
destruct (Z.eq_dec c kBatchClass) as [->|Hne]; [img_try (rewrite PB; img_lia)|].
rewrite !(batch_offs_other (set_qthread q' s)), !(batch_offs_other s) by img_exact Hne. img_lia.
Qed.
