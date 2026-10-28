(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Printf_lib F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof.
  intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
  mpad OUT_sn c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply OUT_sn_eq. exact H.
Qed.

(* [comment removed for export] *)
Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
  pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
  pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
  pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
  pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
  pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
  pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
  pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
  pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_sn; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  printf_loop OUT_sn OUTFP_sn fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
    rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma convx_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_piecesx cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (convx OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T H. unfold convx, conv_piecesx in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (d_t d =? 99). { eapply conv_tail_sn; eassumption. }
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
  - destruct ((d_ty d =? T_SIZET) || (d_ty d =? T_ULONG))%bool.
    + destruct (d_t d =? 117); [eapply conv_int_sn; eassumption|].
      destruct ((d_t d =? 120) || (d_t d =? 88))%bool; [|discriminate]. eapply conv_int_sn; eassumption.
    + destruct (d_ty d =? T_LONG); [|discriminate].
      destruct (INTMAX_MAX <? u);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_sn; eassumption.
  - discriminate.
Qed.

Lemma printf_loopx_sn : forall fuel s args cnt o ps r,
  printf_piecesx_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  printf_loopx OUT_sn OUTFP_sn fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_piecesx_loop] in P. cbn [printf_loopx].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_piecesx_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dirx s2) as [[[d0 ws] s3]|]; [|discriminate].
    destruct (dir_eff d0 ws args) as [[d [|a args']]|]; [discriminate| |discriminate].
    destruct (conv_piecesx cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_piecesx_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
    rewrite (convx_sn _ _ _ _ _ _ _ C) by lia.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_modelx_sn : forall fmt args ps r,
  printf_piecesx fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
  printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros fmt args ps r P H. unfold printf_modelx, printf_piecesx in *.
  exact (printf_loopx_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.
