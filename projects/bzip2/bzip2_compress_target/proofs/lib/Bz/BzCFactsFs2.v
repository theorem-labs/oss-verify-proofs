(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma fs_bucket_iter_unfold : forall nb fm ec bh slo shi r nnd,
  fs_bucket_iter nb (FBS fm ec bh slo shi r nnd false) =
  (let k1 := bk1 nb bh (r + 1) in
   if nb <=? k1 - 1 then FBS fm ec bh slo shi r nnd true else
   let k2 := bk2 nb bh k1 in
   if nb <=? k2 - 1 then FBS fm ec bh slo shi (k2 - 1) nnd true else
   if k1 - 1 <? k2 - 1 then
     let q := fallbackQSort3 fm ec slo shi (k1 - 1) (k2 - 1) in
     FBS (fq_fm q) ec (fs_headers (Z.to_nat (k2 - 1 - (k1 - 1) + 1)) bh ec (fq_fm q) (k1 - 1) (-1)) (fq_slo q) (fq_shi q) (k2 - 1) (nnd + (k2 - 1 - (k1 - 1) + 1)) false
   else FBS fm ec bh slo shi (k2 - 1) nnd false)%Z.
Proof. intros. reflexivity. Qed.

Lemma fs_bucket_loop_done : forall u nb s, fb_done s = true -> fs_bucket_loop u nb s = s.
Proof. intros u nb s H. destruct u; [reflexivity|]. cbn [fs_bucket_loop]. rewrite H. reflexivity. Qed.
Lemma fs_bucket_loop_S : forall u nb s, fs_bucket_loop (S u) nb s = (if fb_done s then s else fs_bucket_loop u nb (fs_bucket_iter nb s)).
Proof. reflexivity. Qed.

Lemma bk2_ge : forall nb bh k1, k1 <= bk2 nb bh k1.
Proof.
  intros nb bh k1. unfold bk2. cbv zeta.
  pose proof (fs_scan_clr_unal_ge (FSC nb) bh k1).
  destruct (negb (isset_bh bh (fs_scan_clr_unal (FSC nb) bh k1))); [| lia].
  eapply Z.le_trans; [exact H|]. eapply Z.le_trans; [apply fs_scan_word_00_ge| apply fs_scan_clr_ge].
Qed.

(* [comment removed for export] *)
Lemma fs_bucket_iter_r : forall nb s, fb_done s = false -> bucket_ok nb s -> fb_done (fs_bucket_iter nb s) = false ->
  fb_r s + 1 <= fb_r (fs_bucket_iter nb s) < nb.
Proof.
  intros nb [fm ec bh slo shi r nnd dn] Hd BOK Hd'. cbn [fb_done] in Hd. subst dn.
  destruct BOK as [SOK _]. cbn [fb_bh fb_r] in SOK. unfold scan_ok in SOK. cbv zeta in SOK. cps_destruct SOK as (_ & H01 & _).
  pose proof (bk2_ge nb bh (bk1 nb bh (r + 1))) as G2.
  rewrite fs_bucket_iter_unfold in Hd' |- *. cbv zeta in Hd' |- *.
  destruct (Z.leb_spec nb (bk1 nb bh (r + 1) - 1)) as [C1|C1]; [cbn in Hd'; discriminate|].
  destruct (Z.leb_spec nb (bk2 nb bh (bk1 nb bh (r + 1)) - 1)) as [C2|C2]; [cbn in Hd'; discriminate|].
  destruct (Z.ltb _ _); cbn [fb_r]; lia.
Qed.

Lemma fs_bucket_loop_r : forall u nb s, fb_done s = false ->
  (forall v, fb_done (fs_bucket_loop v nb s) = false -> bucket_ok nb (fs_bucket_loop v nb s)) ->
  fb_done (fs_bucket_loop u nb s) = false ->
  fb_r s + Z.of_nat u <= fb_r (fs_bucket_loop u nb s) /\ ((0 < u)%nat -> fb_r (fs_bucket_loop u nb s) < nb).
Proof.
  induction u as [|u IH]; intros nb s Hd BF Hdu.
  - cbn. lia.
  - rewrite fs_bucket_loop_S, Hd in Hdu |- *.
    pose proof (BF 0%nat Hd) as BOK. cbn [fs_bucket_loop] in BOK.
    destruct (fb_done (fs_bucket_iter nb s)) eqn:Hd'.
    { rewrite fs_bucket_loop_done in Hdu by exact Hd'. rewrite Hd' in Hdu. discriminate. }
    pose proof (fs_bucket_iter_r nb s Hd BOK Hd') as R1.
    assert (BF' : forall v, fb_done (fs_bucket_loop v nb (fs_bucket_iter nb s)) = false -> bucket_ok nb (fs_bucket_loop v nb (fs_bucket_iter nb s))).
    { intros v Hv. specialize (BF (S v)). rewrite fs_bucket_loop_S, Hd in BF. exact (BF Hv). }
    specialize (IH nb (fs_bucket_iter nb s) Hd' BF' Hdu). destruct IH as [IH1 IH2].
    split; [lia|]. intros _. destruct u; [cbn [fs_bucket_loop]; lia|]. apply IH2. lia.
Qed.

Lemma fs_bucket_loop_term : forall nb s, 0 <= nb -> fb_r s = -1 -> fb_done s = false ->
  (forall v, fb_done (fs_bucket_loop v nb s) = false -> bucket_ok nb (fs_bucket_loop v nb s)) ->
  fb_done (fs_bucket_loop (Z.to_nat (nb + 2)) nb s) = true.
Proof.
  intros nb s Hnb Hr Hd BF. destruct (fb_done (fs_bucket_loop (Z.to_nat (nb + 2)) nb s)) eqn:E; [reflexivity|].
  pose proof (fs_bucket_loop_r (Z.to_nat (nb + 2)) nb s Hd BF E) as [R1 R2]. specialize (R2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma fs_H_loop_S : forall f nb s, fs_H_loop (S f) nb s = (if fh_done s then s else fs_H_loop f nb (fs_H_iter nb s)).
Proof. reflexivity. Qed.
Lemma fs_H_loop_done : forall f nb s, fh_done s = true -> fs_H_loop f nb s = s.
Proof. intros f nb s H. destruct f; [reflexivity|]. cbn [fs_H_loop]. rewrite H. reflexivity. Qed.
Lemma fs_H_loop_back : forall t nb s,
  fs_H_loop (S t) nb s = (let h := fs_H_loop t nb s in if fh_done h then h else fs_H_iter nb h).
Proof.
  induction t as [|t IH]; intros nb s.
  - cbn [fs_H_loop]. destruct (fh_done s); reflexivity.
  - rewrite fs_H_loop_S. cbv zeta. rewrite (fs_H_loop_S t nb s).
    destruct (fh_done s) eqn:Hd; [rewrite Hd; reflexivity|].
    rewrite IH. reflexivity.
Qed.
Lemma fp_hs_S : forall fm ec bh nb t, fh_done (fp_hs fm ec bh nb t) = false ->
  fp_hs fm ec bh nb (S t) = fs_H_iter nb (fp_hs fm ec bh nb t).
Proof. intros fm ec bh nb t Hd. unfold fp_hs in *. rewrite fs_H_loop_back. cbv zeta. rewrite Hd. reflexivity. Qed.
Lemma fp_hs_stay : forall fm ec bh nb t k, fh_done (fp_hs fm ec bh nb t) = true -> fp_hs fm ec bh nb (k + t) = fp_hs fm ec bh nb t.
Proof.
  intros fm ec bh nb t k Hd. induction k as [|k IH]; [reflexivity|].
  change (S k + t)%nat with (S (k + t)). unfold fp_hs in *. rewrite fs_H_loop_back. cbv zeta. rewrite IH, Hd. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma fp_hs_H : forall fm ec bh nb t, 1 <= nb -> fh_done (fp_hs fm ec bh nb t) = false ->
  fh_H (fp_hs fm ec bh nb t) = 2 ^ (Z.of_nat t) /\ 2 ^ (Z.of_nat t) <= nb.
Proof.
  intros fm ec bh nb t Hnb. induction t as [|t IH]; intros Hd.
  - cbn. lia.
  - destruct (fh_done (fp_hs fm ec bh nb t)) eqn:Hdt.
    { pose proof (fp_hs_stay fm ec bh nb t 1 Hdt) as E. change (1 + t)%nat with (S t) in E. rewrite E, Hdt in Hd. discriminate. }
    specialize (IH eq_refl). destruct IH as [IH1 IH2].
    rewrite fp_hs_S in Hd |- * by exact Hdt. unfold fs_H_iter in Hd |- *. cbn [fh_H fh_done] in Hd |- *.
    rewrite IH1 in Hd |- *. apply Bool.orb_false_iff in Hd. destruct Hd as [Hd _]. apply Z.ltb_ge in Hd.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma fp_hs_done21 : forall fm ec bh nb, 1 <= nb <= 900000 -> fh_done (fp_hs fm ec bh nb 21) = true.
Proof.
  intros fm ec bh nb Hnb. destruct (fh_done (fp_hs fm ec bh nb 21)) eqn:E; [reflexivity|].
  pose proof (fp_hs_H fm ec bh nb 21 ltac:(lia) E) as [_ H2]. cbn in H2. lia.
Qed.
(* [comment removed for export] *)
Lemma fs_H_loop_64_done : forall fm ec bh nb, 1 <= nb <= 900000 ->
  fh_done (fs_H_loop (Z.to_nat 64) nb (fp_hs0 fm ec bh nb)) = true.
Proof.
  intros fm ec bh nb Hnb. change (fs_H_loop (Z.to_nat 64) nb (fp_hs0 fm ec bh nb)) with (fp_hs fm ec bh nb (43 + 21)).
  rewrite fp_hs_stay by (apply fp_hs_done21; lia). apply fp_hs_done21. lia.
Qed.

(* [comment removed for export] *)
Lemma fs_distrib_zbok : forall n ft fm ec i, zbok fm -> zbok (snd (fs_distrib n ft fm ec i)).
Proof.
  induction n as [|n IH]; intros ft fm ec i H; [exact H|].
  rewrite fs_distrib_S. cbv zeta. apply IH. apply zbok_wr32. exact H.
Qed.
Lemma fp_fm1_zbok : forall fm ec nb, zbok fm -> zbok (fp_fm1 fm ec nb).
Proof. intros. unfold fp_fm1, fp_dist. apply fs_distrib_zbok. assumption. Qed.

(* [comment removed for export] *)
Lemma fallbackSort_eq : forall fm ec bh nb,
  fallbackSort fm ec bh znew znew znew znew nb =
  (let hs := fp_hsF fm ec bh nb in
   let rb := fs_rebuild (Z.to_nat nb) (fh_ec hs) (fp_fc0 ec nb) (fh_fm hs) 0 0 in
   FSR (fh_fm hs) (fst (fst rb)) (fh_bh hs) (fp_ft4 fm ec nb) (snd (fst rb)) (fh_slo hs) (fh_shi hs) (snd rb)).
Proof.
  intros. unfold fallbackSort, fp_hsF, fp_hs0, fp_fm1, fp_bh3, fp_ft4, fp_fc0, fp_dist, fp_ft3, fp_ft2, fp_ft1, fp_nB.
  rewrite (surjective_pairing (fs_distrib _ _ _ _ _)).
  rewrite (surjective_pairing (fs_rebuild _ _ _ _ _ _)). rewrite (surjective_pairing (fst (fs_rebuild _ _ _ _ _ _))) at 1.
  reflexivity.
Qed.
