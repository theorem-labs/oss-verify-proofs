(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCPermF2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCRebuildF BzCFactsFs BzCFactsFs2 BzCScanF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewH.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2.BzCQsortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCScanF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewH.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbok_fswap : forall fm a b, zbok fm -> zbok (fswap fm a b).
Proof. intros. unfold fswap. apply zbok_wr32, zbok_wr32. assumption. Qed.
Lemma zbok_fvswap : forall f fm p1 p2 n, zbok fm -> zbok (fvswap f fm p1 p2 n).
Proof. induction f; intros; cbn [fvswap]; [assumption|]. destruct (0 <? n); [apply IHf, zbok_fswap|]; assumption. Qed.
Lemma zbok_fss_in : forall f fm ec et j hi st, zbok fm -> zbok (fst (fss_in f fm ec et j hi st)).
Proof. induction f; intros; cbn [fss_in]; [assumption|]. destruct (_ && _); [apply IHf; apply zbok_wr32|]; assumption. Qed.
Lemma zbok_fss_iter : forall fm ec i hi st, zbok fm -> zbok (fss_iter fm ec i hi st).
Proof.
  intros. unfold fss_iter. pose proof (zbok_fss_in (S (Z.to_nat (hi - i))) fm ec (rd32 ec (rd32 fm i)) (i + st) hi st H).
  destruct (fss_in _ _ _ _ _ _ _) as [fm1 j]. cbn [fst] in H0. apply zbok_wr32. exact H0.
Qed.
Lemma zbok_fss_outer : forall n fm ec i hi st, zbok fm -> zbok (fss_outer n fm ec i hi st).
Proof. induction n; intros; cbn [fss_outer]; [assumption|]. apply IHn. apply zbok_fss_iter. assumption. Qed.
Lemma zbok_fss : forall fm ec lo hi, zbok fm -> zbok (fallbackSimpleSort fm ec lo hi).
Proof.
  intros. unfold fallbackSimpleSort. destruct (lo =? hi); [assumption|].
  apply zbok_fss_outer. destruct (3 <? hi - lo); [apply zbok_fss_outer|]; assumption.
Qed.
Lemma zbok_fpart_lo : forall f ec med p, zbok (fp_fm p) -> zbok (fp_fm (fpart_lo f ec med p)).
Proof.
  induction f; intros ec med p H; cbn [fpart_lo]; [exact H|].
  destruct (_ <? _); [exact H|]. destruct (_ =? 0); [apply IHf; cbn [fp_fm]; apply zbok_fswap; exact H|].
  destruct (0 <? _); [exact H| apply IHf; cbn [fp_fm]; exact H].
Qed.
Lemma zbok_fpart_hi : forall f ec med p, zbok (fp_fm p) -> zbok (fp_fm (fpart_hi f ec med p)).
Proof.
  induction f; intros ec med p H; cbn [fpart_hi]; [exact H|].
  destruct (_ <? _); [exact H|]. destruct (_ =? 0); [apply IHf; cbn [fp_fm]; apply zbok_fswap; exact H|].
  destruct (_ <? 0); [exact H| apply IHf; cbn [fp_fm]; exact H].
Qed.
Lemma zbok_fpart_loop : forall f sz ec med p, zbok (fp_fm p) -> zbok (fp_fm (fpart_loop f sz ec med p)).
Proof.
  induction f; intros sz ec med p H; cbn [fpart_loop]; [exact H|].
  pose proof (zbok_fpart_hi (S sz) ec med _ (zbok_fpart_lo (S sz) ec med p H)) as H2.
  destruct (_ <? _); [exact H2|]. apply IHf. cbn [fp_fm]. apply zbok_fswap. exact H2.
Qed.
Lemma zbok_fpush : forall q a b, zbok (fq_fm q) -> zbok (fq_fm (fpush q a b)).
Proof. intros. unfold fpush. cbn [fq_fm]. assumption. Qed.
Lemma zbok_fqs_iter : forall ec q, zbok (fq_fm q) -> zbok (fq_fm (fqs_iter ec q)).
Proof.
  intros ec q H. unfold fqs_iter.
  destruct (_ <? 10); [cbn [fq_fm]; apply zbok_fss; exact H|]. cbv zeta.
  match goal with |- context [fpart_loop ?f ?sz ?e ?md ?p] => pose proof (zbok_fpart_loop f sz e md p H) as HP; set (pp := fpart_loop f sz e md p) in * end.
  destruct (_ <? _); [cbn [fq_fm]; exact HP|].
  destruct (_ <? _); apply zbok_fpush, zbok_fpush; cbn [fq_fm]; apply zbok_fvswap, zbok_fvswap; exact HP.
Qed.
Lemma zbok_fqs_loop : forall f ec q, zbok (fq_fm q) -> zbok (fq_fm (fqs_loop f ec q)).
Proof. induction f; intros; [exact H|]. rewrite fqs_loop_S. destruct (0 <? _); [apply IHf, zbok_fqs_iter|]; assumption. Qed.
Lemma zbok_fqs3 : forall fm ec slo shi l r, zbok fm -> zbok (fq_fm (fallbackQSort3 fm ec slo shi l r)).
Proof. intros. unfold fallbackQSort3. apply zbok_fqs_loop. cbn [fq_fm fpush]. assumption. Qed.
Lemma zbok_fs_eclass : forall n ec fm bh H nb i j, zbok ec -> zbok (fs_eclass n ec fm bh H nb i j).
Proof. induction n; intros; cbn [fs_eclass]; [assumption|]. apply IHn. apply zbok_wr32. assumption. Qed.
Definition fb_ok (s : fbs) : Prop := zbok (fb_fm s) /\ zbok (fb_ec s) /\ bh_w32 (fb_bh s).
Lemma fs_bucket_iter_ok : forall nb s, fb_ok s -> fb_ok (fs_bucket_iter nb s).
Proof.
  (intros nb s; cps_intros (A & B & C)). unfold fs_bucket_iter. cbv zeta.
  destruct (nb <=? _); [split; [| split]; cbn [fb_fm fb_ec fb_bh]; assumption|].
  destruct (nb <=? _); [split; [| split]; cbn [fb_fm fb_ec fb_bh]; assumption|].
  destruct (_ <? _); [| split; [| split]; cbn [fb_fm fb_ec fb_bh]; assumption].
  split; [| split]; cbn [fb_fm fb_ec fb_bh].
  - apply zbok_fqs3. exact A.
  - exact B.
  - apply fs_headers_w32. exact C.
Qed.
Lemma fs_bucket_loop_ok : forall u nb s, fb_ok s -> fb_ok (fs_bucket_loop u nb s).
Proof. induction u; intros; cbn [fs_bucket_loop]; [assumption|]. destruct (fb_done s); [assumption| apply IHu, fs_bucket_iter_ok; assumption]. Qed.
Definition fh_ok (s : fhs) : Prop := zbok (fh_fm s) /\ zbok (fh_ec s) /\ bh_w32 (fh_bh s).
Lemma fs_H_iter_ok : forall nb s, fh_ok s -> fh_ok (fs_H_iter nb s).
Proof.
  (intros nb s; cps_intros (A & B & C)). unfold fs_H_iter. cbv zeta.
  match goal with |- context [fs_bucket_loop ?u ?n ?s0] => pose proof (fs_bucket_loop_ok u n s0) as K end.
  cps_destruct K as (A' & B' & C'); [split; [| split]; cbn [fb_fm fb_ec fb_bh]; [exact A| apply zbok_fs_eclass; exact B| exact C]|].
  split; [| split]; cbn [fh_fm fh_ec fh_bh]; assumption.
Qed.
Lemma fs_H_loop_ok : forall f nb s, fh_ok s -> fh_ok (fs_H_loop f nb s).
Proof. induction f; intros; cbn [fs_H_loop]; [assumption|]. destruct (fh_done s); [assumption| apply IHf, fs_H_iter_ok; assumption]. Qed.
Lemma zbok_fs_rebuild : forall n ec fc fm i j, zbok ec -> zbok (fst (fst (fs_rebuild n ec fc fm i j))).
Proof. induction n; intros; [cbn; assumption|]. rewrite fs_rebuild_S. cbv zeta. apply IHn. apply zbok_wr8. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma HI_allT : forall fm ec bh nb, zbok ec -> bh_w32 bh -> 1 <= nb <= 900000 -> forall t, HI nb (fp_hs fm ec bh nb t).
Proof.
  intros fm ec bh nb ECB BW NB t. induction t as [|t IH].
  - apply HI_all; [exact ECB| exact BW| exact NB| reflexivity].
  - destruct (fh_done (fp_hs fm ec bh nb t)) eqn:Hd.
    + change (S t) with (1 + t)%nat. rewrite fp_hs_stay by exact Hd. exact IH.
    + apply HI_step; [exact NB| exact Hd| exact IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cntP_ex : forall P n, 1 <= cntP P n -> exists i, 0 <= i < Z.of_nat n /\ P i = true.
Proof.
  induction n as [|n IH]; intros H; cbn [cntP] in H; [lia|].
  destruct (P (Z.of_nat n)) eqn:E.
  - exists (Z.of_nat n). split; [lia| exact E].
  - cps_destruct (IH ltac:(lia)) as (i & Hi & Pi). exists i. split; [lia| exact Pi].
Qed.
Lemma rd8_wr8 : forall a p v q, rd8 (wr8 a p v) q = if q =? p then v mod 256 else rd8 a q.
Proof. intros. unfold rd8, wr8. rewrite zget_zset. reflexivity. Qed.

Section Rebuild.
  Variables (fm ec bh : zarr) (nb : Z).
  Hypothesis ECB : zbok ec. Hypothesis BW : bh_w32 bh. Hypothesis NB : 1 <= nb <= 900000.
  Let fmF := fh_fm (fp_hsF fm ec bh nb).
  Lemma fmF_perm : fm_perm fmF nb.
  Proof. unfold fmF, fp_hsF. change (fs_H_loop (Z.to_nat 64) nb (fp_hs0 fm ec bh nb)) with (fp_hs fm ec bh nb (Z.to_nat 64)). apply (proj1 (HI_allT fm ec bh nb ECB BW NB _)). Qed.

  (* [comment removed for export] *)
  Definition occ (c : Z) : Prop := exists p, 0 <= p < nb /\ rd8 ec p = c.

  Definition RBX (i : nat) (s : zarr * zarr * Z) : Prop :=
    let e := fst (fst s) in let fc := snd (fst s) in
    (forall b, zget fc b <= Eq ec b (Z.to_nat nb)) /\
    (forall i', 0 <= i' < Z.of_nat i -> occ (rd8 e (rd32 fmF i'))).

  Lemma RBX0 : RBX 0 (fp_rb fm ec bh nb 0).
  Proof.
    unfold RBX, fp_rb. cbn [fs_rebuild fst snd]. split; [| intros; lia].
    intros b. rewrite (fc0_get ec nb). destruct (_ && _)%bool; [lia|]. pose proof (Eq_range ec nb b (Z.to_nat nb) ltac:(lia)). lia.
  Qed.

  Lemma RBX_step : forall i, Z.of_nat i < nb -> RB nb i (fp_rb fm ec bh nb i) -> RBX i (fp_rb fm ec bh nb i) -> RBX (S i) (fp_rb fm ec bh nb (S i)).
  Proof.
    intros i Hi R X. cps_destruct (RB_step ec nb fm bh i Hi R) as (A & B & C & D & R5). cbv zeta in A, B, C, D.
    unfold RB in R5. rewrite (fp_rb_S ec nb fm bh) in R5. cbv zeta in R5. cbn [fst snd] in R5. destruct R5 as (J5 & _).
    destruct X as [XF XO]. unfold RBX. rewrite (fp_rb_S ec nb fm bh). cbv zeta. cbn [fst snd].
    set (s := fp_rb fm ec bh nb i) in *. set (fc := snd (fst s)) in *. set (e := fst (fst s)) in *. set (j' := fs_skip0 258 fc (snd s)) in *.
    split.
    - intros b. rewrite zget_zset. destruct (Z.eqb_spec b j'); [subst b; pose proof (XF j'); lia| apply XF].
    - intros i' Hi'. rewrite rd8_wr8. fold fmF.
      destruct (Z.eqb_spec (rd32 fmF i') (rd32 fmF (Z.of_nat i))) as [E|NE].
      + (* [comment removed for export] *)
        assert (1 <= Eq ec j' (Z.to_nat nb)) as CNT by (pose proof (XF j'); lia).
        unfold Eq in CNT. cps_destruct (cntP_ex _ _ CNT) as (p & Hp & Pp). apply Z.eqb_eq in Pp. cbv beta zeta in Pp.
        exists p. split; [lia|]. rewrite Z.mod_small by lia. exact Pp.
      + apply XO. destruct (Z.eq_dec i' (Z.of_nat i)) as [->|]; [congruence| lia].
  Qed.

  Lemma RBX_all : forall i, Z.of_nat i <= nb -> RB nb i (fp_rb fm ec bh nb i) /\ RBX i (fp_rb fm ec bh nb i).
  Proof.
    induction i as [|i IH]; intros Hi; [split; [apply RB0; [exact ECB| lia]| apply RBX0]|].
    destruct (IH ltac:(lia)) as [R X]. split.
    - cps_destruct (RB_step ec nb fm bh i ltac:(lia) R) as (_ & _ & _ & _ & R'). exact R'.
    - apply RBX_step; [lia| exact R| exact X].
  Qed.

  (* [comment removed for export] *)
  Theorem rebuild_occ : forall q, 0 <= q < nb -> occ (rd8 (fst (fst (fp_rb fm ec bh nb (Z.to_nat nb)))) q).
  Proof.
    intros q Hq. cps_destruct (fm_perm_onto fmF nb fmF_perm q Hq) as (x & Hx & <-).
    destruct (RBX_all (Z.to_nat nb) ltac:(lia)) as [_ [_ XO]]. apply XO. lia.
  Qed.
End Rebuild.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fallbackSort_out : forall fm ec bh nb, zbok fm -> zbok ec -> bh_w32 bh -> 1 <= nb <= 900000 ->
  let r := fallbackSort fm ec bh znew znew znew znew nb in
  zbok (fr_fm r) /\ zbok (fr_ec r) /\ bh_w32 (fr_bh r) /\ fm_perm (fr_fm r) nb /\
  (forall q, 0 <= q < nb -> exists p, 0 <= p < nb /\ rd8 ec p = rd8 (fr_ec r) q).
Proof.
  intros fm ec bh nb FB EB BW NB. rewrite fallbackSort_eq. cbv zeta. cbn [fr_fm fr_ec fr_bh].
  assert (OK : fh_ok (fp_hsF fm ec bh nb)).
  { unfold fp_hsF. apply fs_H_loop_ok. unfold fp_hs0. split; [| split]; cbn [fh_fm fh_ec fh_bh].
    - apply fp_fm1_zbok. exact FB.
    - exact EB.
    - unfold fp_bh3. apply fs_sentinel_w32, fs_bh_init_w32, fs_bh_zero_w32. exact BW. }
  cps_destruct OK as (A & B & C).
  split; [exact A|]. split; [| split; [exact C| split; [apply fmF_perm; assumption|]]].
  - change (fs_rebuild (Z.to_nat nb) (fh_ec (fp_hsF fm ec bh nb)) (fp_fc0 ec nb) (fh_fm (fp_hsF fm ec bh nb)) 0 0) with (fp_rb fm ec bh nb (Z.to_nat nb)).
    unfold fp_rb. apply zbok_fs_rebuild. exact B.
  - change (fs_rebuild (Z.to_nat nb) (fh_ec (fp_hsF fm ec bh nb)) (fp_fc0 ec nb) (fh_fm (fp_hsF fm ec bh nb)) 0 0) with (fp_rb fm ec bh nb (Z.to_nat nb)).
    apply rebuild_occ; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zget_zincr : forall a i v, zget (zincr a i) v = if v =? i then zget a i + 1 else zget a v.
Proof. intros. unfold zincr. rewrite zget_zset. reflexivity. Qed.

Lemma radix1_frame : forall n a ft qoff i j, zbok a -> 0 <= j < 65536 ->
  forall v, (v < 0 \/ 65536 <= v) -> zget (snd (fst (ms_radix1 n a ft qoff i j))) v = zget ft v.
Proof.
  induction n as [|n IH]; intros a ft qoff i j ZA Hj v Hv; cbn [ms_radix1]; [reflexivity|].
  set (a' := qwr a qoff i 0). assert (ZA' : zbok a') by (subst a'; apply zbok_qwr; exact ZA).
  pose proof (zbok_rd8 a' i ZA') as R8.
  rewrite lor_step by lia.
  rewrite IH; [| exact ZA'| |exact Hv].
  - rewrite zget_zincr. destruct (Z.eqb_spec v (j / 256 + 256 * rd8 a' i)); [exfalso|reflexivity].
    assert (0 <= j / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
  - assert (0 <= j / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Lemma accum_frame : forall n ft i v, (v < i \/ i + Z.of_nat n <= v) -> zget (ms_accum n ft i) v = zget ft v.
Proof.
  induction n as [|n IH]; intros ft i v Hv; cbn [ms_accum]; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.
Lemma N65536 : Z.of_nat 65536%nat = 65536.
Proof. vm_compute. reflexivity. Qed.
Lemma N65537 : Z.of_nat 65537%nat = 65537.
Proof. vm_compute. reflexivity. Qed.
Lemma accum_frame65536 : forall ft v, (v < 1 \/ 65536 < v) -> zget (ms_accum 65536%nat ft 1) v = zget ft v.
Proof. intros ft v Hv. apply accum_frame. rewrite N65536. lia. Qed.

Lemma radix2_frame : forall n a1 a ft i s, zbok a -> 0 <= s < 65536 ->
  forall v, (v < 0 \/ 65536 <= v) -> zget (snd (fst (ms_radix2 n a1 a ft i s))) v = zget ft v.
Proof.
  induction n as [|n IH]; intros a1 a ft i s ZA Hs v Hv; cbn [ms_radix2]; [reflexivity|].
  pose proof (zbok_rd8 a i ZA) as R8. rewrite lor_step by lia.
  assert (0 <= s / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite IH; [| exact ZA| lia| exact Hv]. apply zget_zset_other. lia.
Qed.

Definition MK (ft ft' : zarr) : Prop := forall v, zget ft' v = zget ft v \/ zget ft' v = Z.lor (zget ft v) SETMASK.
Lemma MK_refl : forall ft, MK ft ft. Proof. intros ft v. left. reflexivity. Qed.
Lemma MK_trans : forall a b c, MK a b -> MK b c -> MK a c.
Proof.
  intros a b c AB BC v. destruct (BC v) as [E|E]; rewrite E; [apply AB|].
  destruct (AB v) as [F|F]; rewrite F; right; [reflexivity| apply lor_setmask_idem].
Qed.
Lemma MK_mark1 : forall ft x, MK ft (zset ft x (Z.lor (zget ft x) SETMASK)).
Proof. intros ft x v. rewrite zget_zset. destruct (Z.eqb_spec v x) as [->|]; [right| left]; reflexivity. Qed.

Lemma step1_MK : forall n qoff nb ss j s, MK (s_ft s) (s_ft (ms_step1 n qoff nb ss j s)).
Proof.
  induction n as [|n IH]; intros; [apply MK_refl|]. rewrite ms_step1_S.
  destruct (s_exit s); [apply MK_refl|]. destruct (j =? ss); [apply IH|]. cbv zeta.
  destruct (negb _).
  - destruct (_ <? _).
    + destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 b] l]. destruct (b <? 0); [cbn [s_ft]; apply MK_refl|].
      eapply MK_trans; [| apply IH]. cbn [s_ft]. apply MK_mark1.
    + eapply MK_trans; [| apply IH]. cbn [s_ft]. apply MK_mark1.
  - eapply MK_trans; [| apply IH]. cbn [s_ft]. apply MK_mark1.
Qed.
Lemma mark_MK : forall n ft ss j, MK ft (ms_mark n ft ss j).
Proof. induction n as [|n IH]; intros; [apply MK_refl|]. rewrite ms_mark_S. cbv zeta. eapply MK_trans; [apply MK_mark1| apply IH]. Qed.
Lemma big_MK : forall ro qoff nb i s, MK (s_ft s) (s_ft (ms_big ro qoff nb i s)).
Proof.
  intros. unfold ms_big. cbv zeta. pose proof (step1_MK 256 qoff nb (zget ro i) 0 s) as M1.
  destruct (s_exit _); [exact M1|].
  destruct (ms_copy_init _ _ _ _ _ _) as [cs ce]. destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[af csf] jf]. destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[ab ceb] jb].
  cbn [s_ft]. eapply MK_trans; [exact M1| apply mark_MK].
Qed.
Lemma bigs_MK : forall n ro qoff nb i s, MK (s_ft s) (s_ft (ms_bigs n ro qoff nb i s)).
Proof.
  induction n as [|n IH]; intros; [apply MK_refl|]. rewrite ms_bigs_S. cbv zeta.
  pose proof (big_MK ro qoff nb i s) as M. destruct (s_exit _); [exact M|]. eapply MK_trans; [exact M| apply IH].
Qed.

(* [comment removed for export] *)
Theorem mainSort_ftab : forall a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget,
  zbok a2 -> 1 <= nb <= 1000000 -> nb + 34 <= qoff -> (forall i, 0 <= zget ft i < 4294967296) ->
  forall i, 0 <= zget (mr_ftab (mainSort a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget)) i < 4294967296.
Proof.
  intros a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget BB NB QO FTR.
  apply (mainSort_shape a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget). intros a2a ft2 x1 a1a ft4 x2 bd ro st E1 E2 E3 Est i.
  cbn [mr_ftab].
  pose proof (BB' a2 BB) as BBr.
  pose proof (radix1_ft a2 nb qoff BBr ltac:(lia) ltac:(lia) a2 ft ltac:(intros; reflexivity)) as R1.
  cbv zeta in R1. rewrite E1 in R1. cbn [fst snd] in R1. destruct R1 as [AG1 FT2].
  assert (J0 : 0 <= Z.shiftl (rd8 a2 0) 8 < 65536) by (rewrite shl8; pose proof (BBr 0); lia).
  pose proof (radix1_frame (Z.to_nat nb) a2 (mft1 ft) qoff (nb - 1) _ BB J0) as FR1. rewrite E1 in FR1. cbn [fst snd] in FR1.
  pose proof (zbok_radix1 (Z.to_nat nb) a2 (mft1 ft) qoff (nb-1) (Z.shiftl (rd8 a2 0) 8) BB) as ZB2a. rewrite E1 in ZB2a. cbn [fst snd] in ZB2a.
  set (a2b := ms_overshoot 34 a2a qoff nb 0) in *.
  assert (AG2 : forall k, 0 <= k < nb -> rd8 a2b k = rd8 a2 k).
  { intros k Hk. subst a2b. rewrite (ms_overshoot_low nb qoff ltac:(lia) 34 a2a 0 ltac:(lia) ltac:(cbn; lia) k Hk). apply AG1. exact Hk. }
  assert (ZB2b : zbok a2b) by (subst a2b; apply zbok_overshoot; exact ZB2a).
  pose proof (ms_accum_ft a2 nb BBr ltac:(lia) ft2 FT2) as FT3.
  set (ft3 := ms_accum 65536 ft2 1) in *.
  pose proof (ms_radix_perm a2 nb BBr ltac:(lia) a1 a2b ft3 AG2 FT3) as R2. cbv zeta in R2. rewrite E2 in R2. cbn [fst snd] in R2. destruct R2 as (FT4 & _).
  assert (S0 : 0 <= Z.shiftl (rd8 a2b 0) 8 < 65536) by (rewrite shl8; pose proof (zbok_rd8 a2b 0 ZB2b); lia).
  pose proof (radix2_frame (Z.to_nat nb) a1 a2b ft3 (nb - 1) _ ZB2b S0) as FR2. rewrite E2 in FR2. cbn [fst snd] in FR2.
  pose proof (bigs_MK 256 (ms_shell 8 ro ft4 364) qoff nb 0 (MSS a1a a2b ft4 bd cs ce budget 0 (MQL sl sh sd sl sh sd) false)) as M.
  rewrite <- Est in M. cbn [s_ft] in M.
  destruct (Z.le_gt_cases 0 i) as [LO|LO]; [destruct (Z.le_gt_cases i 65536) as [HI|HI]|].
  - (* [comment removed for export] *)
    pose proof (ClM_lt a2 nb ltac:(lia) ltac:(lia) i) as CL.
    destruct (M i) as [E|E]; rewrite E, FT4 by lia; [lia| apply lor_setmask_range; lia].
  - assert (EQ : zget ft4 i = zget ft i).
    { rewrite FR2 by lia. subst ft3. rewrite accum_frame65536 by lia. rewrite FR1 by lia. unfold mft1. rewrite ms_ftab_zero_get.
      match goal with |- (if ?c then 0 else _) = _ => destruct c eqn:C; [exfalso| reflexivity] end.
      apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C2. lia. }
    destruct (M i) as [E|E]; rewrite E, EQ; [apply FTR| apply lor_w32; [apply FTR| unfold SETMASK; lia]].
  - assert (EQ : zget ft4 i = zget ft i).
    { rewrite FR2 by lia. subst ft3. rewrite accum_frame65536 by lia. rewrite FR1 by lia. unfold mft1. rewrite ms_ftab_zero_get.
      match goal with |- (if ?c then 0 else _) = _ => destruct c eqn:C; [exfalso| reflexivity] end.
      apply andb_prop in C. destruct C as [C1 C2]. apply Z.ltb_lt in C1. rewrite N65537 in C1. lia. }
    destruct (M i) as [E|E]; rewrite E, EQ; [apply FTR| apply lor_w32; [apply FTR| unfold SETMASK; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_orig_found : forall nb a1, 1 <= nb -> fm_perm a1 nb -> 0 <= find_orig (Z.to_nat nb) a1 0 < nb.
Proof.
  intros nb a1 NB PM. destruct (find_orig_spec (Z.to_nat nb) a1 0 ltac:(lia)) as [[E ALL]|[R _]]; [| lia].
  exfalso. cps_destruct (fm_perm_onto a1 nb PM 0 ltac:(lia)) as (x & Hx & Ex). apply (ALL x); [lia| exact Ex].
Qed.

Theorem blockSort_out : forall e,
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> (forall i, 0 <= zget (e_ftab e) i < 4294967296) -> 1 <= e_nblock e <= 899990 ->
  let nb := e_nblock e in
  let e' := fst (fst (fst (blockSort e znew))) in
  zbok (e_arr1 e') /\ zbok (e_arr2 e') /\ (forall i, 0 <= zget (e_ftab e') i < 4294967296) /\
  fm_perm (e_arr1 e') nb /\
  (forall q, 0 <= q < nb -> exists p, 0 <= p < nb /\ rd8 (e_arr2 e) p = rd8 (e_arr2 e') q) /\
  0 <= e_origPtr e' < nb /\ e_nblock e' = nb /\ e_inUse e' = e_inUse e /\ e_nInUse e' = e_nInUse e.
Proof.
  intros e B1 B2 FT NB. cbv zeta. unfold blockSort.
  destruct (Z.ltb_spec (e_nblock e) 10000) as [LT|GE].
  - cbv beta iota zeta. cbn [fst snd e_arr1 e_arr2 e_ftab e_origPtr e_nblock e_inUse e_nInUse].
    pose proof (fallbackSort_out (e_arr1 e) (e_arr2 e) (e_ftab e) (e_nblock e) B1 B2 FT ltac:(lia)) as FO. cbv zeta in FO.
    cps_destruct FO as (Z1 & Z2 & W3 & PM & OCC).
    exact (conj Z1 (conj Z2 (conj W3 (conj PM (conj OCC (conj (find_orig_found (e_nblock e) _ ltac:(lia) PM) (conj eq_refl (conj eq_refl eq_refl)))))))).
  - cbv beta iota zeta.
    match goal with |- context [mainSort ?a1 ?a2 ?ft ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?q ?n ?b] =>
      pose proof (mainSort_post a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b B2 B1 ltac:(lia)) as MP;
      pose proof (mainSort_ftab a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b B2 ltac:(lia)) as MF;
      set (m := mainSort a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b) in * end.
    assert (QO : e_nblock e + 34 <= (if Z.land (e_nblock e + BZ_N_OVERSHOOT) 1 =? 0 then e_nblock e + BZ_N_OVERSHOOT else e_nblock e + BZ_N_OVERSHOOT + 1)).
    { unfold BZ_N_OVERSHOOT. destruct (_ =? 0); lia. }
    specialize (MP QO). specialize (MF QO FT). cbv zeta in MP. cps_destruct MP as (Z1 & Z2 & AG & PMx).
    destruct (Z.ltb_spec (mr_budget m) 0) as [NEG|POS]; cbn [fst snd e_arr1 e_arr2 e_ftab e_origPtr e_nblock e_inUse e_nInUse].
    + pose proof (fallbackSort_out (mr_ptr m) (mr_block m) (mr_ftab m) (e_nblock e) Z1 Z2 MF ltac:(lia)) as FO. cbv zeta in FO.
      cps_destruct FO as (Y1 & Y2 & W3 & PM & OCC).
      refine (conj Y1 (conj Y2 (conj W3 (conj PM (conj _ (conj (find_orig_found (e_nblock e) _ ltac:(lia) PM) (conj eq_refl (conj eq_refl eq_refl)))))))).
      intros q Hq. cps_destruct (OCC q Hq) as (p & Hp & Ep). exists p. split; [exact Hp|]. rewrite <- Ep. symmetry. apply AG. exact Hp.
    + assert (PM : fm_perm (mr_ptr m) (e_nblock e)) by (apply PMx; reflexivity).
      refine (conj Z1 (conj Z2 (conj MF (conj PM (conj _ (conj (find_orig_found (e_nblock e) _ ltac:(lia) PM) (conj eq_refl (conj eq_refl eq_refl)))))))).
      intros q Hq. exists q. split; [exact Hq|]. symmetry. apply AG. exact Hq.
Qed.
End ACeilS1.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCStream. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpLaws.
Section ACeilS2. Context {BZP : BzParams}.


(* [comment removed for export] *)
Lemma cb_e0_fields : forall e,
  e_arr1 (cb_e0 e) = e_arr1 e /\ e_arr2 (cb_e0 e) = e_arr2 e /\ e_ftab (cb_e0 e) = e_ftab e /\ e_nblock (cb_e0 e) = e_nblock e /\
  e_inUse (cb_e0 e) = e_inUse e /\ e_nInUse (cb_e0 e) = e_nInUse e.
Proof. intros e. unfold cb_e0. cbv zeta. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Theorem cbm_gmf_ok : forall g e, cb_entry g e -> 0 < e_nblock e -> gm_facts (cb_sorted e).
Proof.
  intros g e [PRE CF] NB0. unfold cb_sorted.
  cps_destruct PRE as (OK & NBR & DEFR & COV & _). cps_destruct OK as (B1 & B2 & FTR & _). cps_destruct CF as (_ & _ & _ & IU).
  cps_destruct (cb_e0_fields e) as (E1 & E2 & E3 & E4 & E5 & E6).
  pose proof (blockSort_out (cb_e0 e)) as BO. rewrite E1, E2, E3, E4, E5, E6 in BO.
  specialize (BO B1 B2 FTR ltac:(bz_params; lia)). cbv zeta in BO.
  cps_destruct BO as (Z1 & Z2 & W3 & PM & OCC & OP & ENB & EIU & ENI).
  unfold gm_facts. rewrite ENB, EIU. split; [exact Z1|]. split; [exact Z2|]. split; [bz_params; lia|].
  split; [exact DEFR|]. split; [exact IU|]. split.
  - intros j Hj. cps_destruct (OCC j Hj) as (p & Hp & Ep). rewrite <- Ep. apply COV. exact Hp.
  - intros i Hi. apply (proj1 PM). exact Hi.
Qed.

End ACeilS2.
