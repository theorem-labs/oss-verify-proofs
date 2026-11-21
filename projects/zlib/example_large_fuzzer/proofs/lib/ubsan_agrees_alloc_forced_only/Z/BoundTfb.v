(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz FillWinModel CompressModel TrSmallModel FlushBlockModel DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE3 RefDeflSafeE5 OverlayCoreL BoundArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition Mloc (x : deflate_state) : Z := ds_pending x + cdiv8 (ds_bi_valid x).

Lemma Mloc_W : forall x, Mloc x = cdiv8 (ov_W x).
Proof.
  intros x. unfold Mloc, ov_W. replace (8 * ds_pending x + ds_bi_valid x) with (ds_bi_valid x + 8 * ds_pending x) by lia.
  rewrite cdiv8_mul8. lia.
Qed.

(* [comment removed for export] *)
Lemma branch_lenb : forall X6 buf len,
  0 <= ds_opt_len X6 < 2 ^ 40 -> 0 <= ds_static_len X6 < 2 ^ 40 -> 0 <= len < 2 ^ 40 ->
  let slb := cdiv8 (ds_static_len X6 + 3) in let olb := cdiv8 (ds_opt_len X6 + 3) in
  (tfb_branch X6 buf len = 0 -> buf <> None -> slb <= len + 3)
  /\ (tfb_branch X6 buf len = 1 -> buf <> None -> olb <= len + 3).
Proof.
  intros X6 buf len HO HS HL. cbv zeta. unfold tfb_branch.
  rewrite (wrap64_id (ds_opt_len X6 + 3 + 7)), (wrap64_id (ds_static_len X6 + 3 + 7)), (wrap64_id (len + 4)) by lia.
  rewrite !cdiv8_shiftr by lia.
  set (slb := cdiv8 (ds_static_len X6 + 3)). set (olb := cdiv8 (ds_opt_len X6 + 3)).
  destruct buf as [b|]; cbn [is_some]; [| split; intros _ C; exfalso; apply C; reflexivity].
  rewrite andb_true_r.
  destruct ((slb <=? olb) || (ds_strategy X6 =? Z_FIXED)) eqn:E.
  - destruct (Z.leb_spec (len + 4) slb) as [L1|L1]; [split; intros HH; discriminate HH|].
    rewrite Z.eqb_refl. split; [intros _ _; lia | intros HH; discriminate HH].
  - apply orb_false_iff in E as [E1 _]. apply Z.leb_gt in E1.
    destruct (Z.leb_spec (len + 4) olb) as [L1|L1]; [split; intros HH; discriminate HH|].
    destruct (Z.eqb_spec slb olb) as [E2|E2]; [lia|]. split; [intros HH; discriminate HH | intros _ _; lia].
Qed.

Lemma tsb_hP_small : forall x, ds_pending x = 0 -> 0 <= ds_bi_valid x <= 7 -> tsb_hP x <= cdiv8 (ds_bi_valid x) + 1.
Proof.
  intros x Hp Hb. unfold tsb_hP. rewrite Hp. unfold cdiv8.
  destruct (Z.leb_spec (ds_bi_valid x) 5); [Z.to_euclidean_division_equations; lia|].
  destruct (Z.leb_spec (ds_bi_valid x) 13); Z.to_euclidean_division_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma Mloc_bi_windup : forall x, 0 <= ds_bi_valid x <= 16 -> Mloc (bi_windup x) = Mloc x.
Proof.
  intros x H. unfold Mloc, bi_windup.
  destruct (Z.ltb_spec 8 (ds_bi_valid x)).
  - unfold put_short, put_byte. dsred. unfold cdiv8. change ((0 + 7) / 8) with 0. Z.to_euclidean_division_equations. lia.
  - destruct (Z.ltb_spec 0 (ds_bi_valid x)).
    + unfold put_byte. dsred. unfold cdiv8. change ((0 + 7) / 8) with 0. Z.to_euclidean_division_equations. lia.
    + dsred. unfold cdiv8. replace (ds_bi_valid x) with 0 by lia. reflexivity.
Qed.

Theorem tfb_bound : forall s last, fb_entry s last ->
  (fb_buf s = None -> zsum (scost s) 0 (Z.to_nat (nsym s)) <= 8 * fb_len s + 30) ->
  Mloc (tr_flush_block s (fb_buf s) (fb_len s) last) <= cdiv8 (ds_bi_valid s) + fb_len s + 5.
Proof.
  intros s last FE HNB.
  pose proof (X6n s last FE) as (P1 & P2 & P3 & P4 & _). pose proof (FEn s last FE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & _).
  pose proof (fe_diff _ _ FE) as Fd.
  assert (Elen : fb_len s = ds_strstart s - ds_block_start s) by (unfold fb_len; apply wrap64_id; lia).
  pose proof (emit_facts s last FE overlay_core_proof) as EF. cbv zeta in EF. destruct EF as [EMy _].
  assert (EPRE : tfb_pre s (fb_buf s) (fb_len s) last = tfb_emit (tfb_branch (ov_X6 s) (fb_buf s) (fb_len s)) (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) by (apply tfb_pre_ov; lia).
  rewrite tr_flush_block_eq, EPRE.
  set (d := tfb_branch (ov_X6 s) (fb_buf s) (fb_len s)) in *.
  set (y := tfb_emit d (ov_X6 s) (ov_mb s) (fb_buf s) (fb_len s) last) in *.
  pose proof (em_bv _ _ EMy) as BVy.
  (* [comment removed for export] *)
  assert (EFIN : Mloc (tfb_fin last y) = Mloc y).
  { unfold tfb_fin. cbv zeta. pose proof (init_block_facts y) as IB.
    assert (EI : Mloc (init_block y) = Mloc y) by (unfold Mloc; rewrite (ib_pend _ _ IB), (ib_bv _ _ IB); reflexivity).
    destruct (negb (last =? 0)); [| exact EI]. rewrite Mloc_bi_windup by (rewrite (ib_bv _ _ IB); exact BVy). exact EI. }
  rewrite EFIN, Mloc_W.
  (* [comment removed for export] *)
  pose proof (stat_val s last FE) as [SV SB].
  pose proof (tp_opt _ (tree_phase s (OP s last FE))) as HO. pose proof (tp_stat_range _ (tree_phase s (OP s last FE))) as HS.
  pose proof (branch_lenb (ov_X6 s) (fb_buf s) (fb_len s) HO HS ltac:(lia)) as [B0 B1]. cbv zeta in B0, B1. fold d in B0, B1.
  assert (SLB : fb_buf s = None -> cdiv8 (ds_static_len (ov_X6 s) + 3) <= fb_len s + 5).
  { intros EN. specialize (HNB EN). rewrite SV. unfold cdiv8. Z.to_euclidean_division_equations. lia. }
  destruct (branch_cases (ov_X6 s) (fb_buf s) (fb_len s)) as [E|[E|E]]; fold d in E.
  - (* [comment removed for export] *)
    subst y. rewrite E. rewrite (stat_W s last FE E).
    replace (ds_bi_valid s + 3 + ds_static_len (ov_X6 s)) with (ds_bi_valid s + (ds_static_len (ov_X6 s) + 3)) by lia.
    pose proof (cdiv8_add (ds_bi_valid s) (ds_static_len (ov_X6 s) + 3) ltac:(lia) ltac:(lia)).
    destruct (fb_buf s) eqn:EB; [specialize (B0 E ltac:(discriminate)); lia | specialize (SLB eq_refl); lia].
  - (* [comment removed for export] *)
    subst y. rewrite E. destruct (dyn_W s last FE overlay_core_proof E) as [WD LT].
    pose proof (cdiv8_le _ _ WD) as C1.
    replace (ds_bi_valid s + 3 + ds_opt_len (ov_X6 s)) with (ds_bi_valid s + (ds_opt_len (ov_X6 s) + 3)) in C1 by lia.
    pose proof (cdiv8_add (ds_bi_valid s) (ds_opt_len (ov_X6 s) + 3) ltac:(lia) ltac:(lia)).
    pose proof (cdiv8_le (ds_opt_len (ov_X6 s) + 3) (ds_static_len (ov_X6 s) + 3) ltac:(lia)).
    destruct (fb_buf s) eqn:EB; [specialize (B1 E ltac:(discriminate)); lia | specialize (SLB eq_refl); lia].
  - (* [comment removed for export] *)
    subst y. rewrite E. destruct (sto_W s last FE E) as [WS _]. rewrite WS.
    pose proof (tsb_hP_small (ov_X6 s) P2 ltac:(rewrite P4; lia)) as HP. rewrite P4 in HP.
    unfold cdiv8 at 1. replace (8 * (tsb_hP (ov_X6 s) + 4 + fb_len s) + 7) with (7 + (tsb_hP (ov_X6 s) + 4 + fb_len s) * 8) by lia.
    rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
Qed.
