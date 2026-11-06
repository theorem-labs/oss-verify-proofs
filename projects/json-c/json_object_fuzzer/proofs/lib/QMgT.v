(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0.
Import ListNotations.
Open Scope Z_scope.

Definition qtot (a : AState) : Z := q_bytes (as_gq a) + q_bytes (as_tq a).

Section Q.
Variable L : ALay.

Lemma asan_free_qb X X' p s :
ainv X s -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 s kBatchClass + 17) <= kFreeArrayOffset ->
0 <= q_bytes (as_gq s) -> 0 <= q_bytes (as_tq s) ->
qroom s p ->
tall (aok s) (rok (fun s' => qtot s' <= qtot s + aptr_used p + kBatchBytes)) (asan_free L s p).
Proof.
intros [AI [QT QG]] HP Hroom Hg0 Ht0 QR. unfold asan_free, qroom in *.
assert (AI0 : ainvx X' [p] 0 s).
{ eapply ainvx_perm; [|exact AI]. rewrite app_nil_r. etransitivity; [exact HP|]. apply Permutation_cons_append. }
assert (Hroom' : sec24_room s).
{ unfold sec24_room. intros H0 H8.
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI _ H24) as Hcons. unfold acc in Hcons. rewrite H0 in Hcons.
pose proof (tot_nonneg X [] 0 s kBatchClass ltac:(lia)).
assert (0 <= class_size kBatchClass * tot X [] 0 s kBatchClass) by (apply Z.mul_nonneg_nonneg; lia).
nia. }
assert (HkB : 0 <= kBatchBytes) by (unfold kBatchBytes; lia).
eapply (tall_bind_rok (aok s) (fun s1 => as_gq s1 = as_gq s /\ q_bytes (as_tq s1) <= q_bytes (as_tq s) + aptr_used p + kBatchBytes)).
{ destruct (Z.ltb_spec kQMaxSize (aptr_used p)) as [Hbig|_]; [exfalso; lia|].
eapply tall_mono; [apply (enqueue_inv L (aok s) X' p 0 s AI0 Hroom')|].
intros [s1| |w]; cbn; auto. intros (_ & G1 & _ & _ & _ & T1 & _). auto. }
intros s1 [G1 T1].
destruct (Z.ltb_spec kQMaxCache (q_bytes (as_tq s1))) as [Hgt|Hle].
- unfold drain. cbn [q_bytes]. rewrite G1.
destruct (Z.ltb_spec kQMaxSize (q_bytes (as_gq s) + q_bytes (as_tq s1))) as [Hrec|_]; [exfalso; lia|].
apply tall_rok_ret. unfold qtot. cbn. lia.
- apply tall_rok_ret. unfold qtot. rewrite G1. lia.
Qed.

Definition kq {R} (s : AState) (r : R * AState) : Prop := as_tq (snd r) = as_tq s /\ as_gq (snd r) = as_gq s.

Lemma asan_malloc_kq X s n :
ainv X s -> 0 <= n -> too_big n = false ->
(from_primary n = true -> class_size (class_of n) * (tot X [] 0 s (class_of n) + 17) <= kFreeArrayOffset) ->
(from_primary n = false -> zlen (as_reg s) < kMaxNumChunks) ->
tall (aok s) (rok (kq s)) (asan_malloc L s n).
Proof.
intros [I QB] Hn Htb Hroom Hreg. unfold asan_malloc. rewrite Htb.
destruct (from_primary n) eqn:Hp.
- specialize (Hroom eq_refl). set (c := class_of n) in *.
pose proof (class_of_facts n Hn Hp) as (Hc & Hum & Hneed). fold c in Hc, Hum, Hneed.
assert (Hc31 : 1 <= c <= 31) by lia.
pose proof (class_facts c Hc31) as (Hsz & Hmc & Hev).
pose proof (ai_cons _ _ _ _ I c Hc31) as Hcons. pose proof (ai_cls _ _ _ _ I c) as W.
pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_nf _ _ W) as Wnf.
pose proof (tot_nonneg X [] 0 s c ltac:(lia)) as Htot.
assert (Hm1 : 0 <= class_size c * c_count (cls s c)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hm2 : 0 <= class_size c * tot X [] 0 s c) by (apply Z.mul_nonneg_nonneg; lia).
unfold acc in Hcons.
eapply tall_bind_rok.
{ apply (cache_alloc_spec L (aok s)); [exact Hc31| exact W| lia| intros H0 H8; nia]. }
intros [ok s1] (Ho & _). destruct Ho as (_ & _ & _ & _ & Ht & Hg).
destruct ok; cbn [negb]; apply tall_rok_ret; unfold kq; cbn [snd as_tq as_gq set_next]; auto.
- specialize (Hreg eq_refl).
pose proof (ai_nres _ _ _ _ I) as (Hnr1 & Hnr2 & Hnr3).
eapply tall_bind_rok.
{ apply (large_alloc_spec L (aok s) (fun _ _ H => H)); [exact Hnr1| exact Hreg]. }
intros [[mb|] s1] Hpost; cbn in Hpost.
+ destruct Hpost as (_ & Ho & _). destruct Ho as (_ & _ & Ht & Hg & _).
eapply tall_bind_rok; [apply clear_shadow_spec|]. intros [] _.
apply tall_rok_ret. unfold kq. cbn [snd]. auto.
+ subst s1. apply tall_rok_ret. unfold kq. cbn [snd]. auto.
Qed.

End Q.
