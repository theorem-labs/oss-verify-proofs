(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import ITree.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Printf_lib F_printf_iface Printf_sn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition sn2 : Type := (list Z * list Z)%type.

(* [comment removed for export] *)
Definition sn2_push (st : sn2) (bs : list Z) : sn2 :=
  let '(d, o) := st in
  if zlength o + zlength bs <=? SN_CAP then (d, o ++ bs) else (d ++ o ++ bs, []).

Definition sn2_pushes (st : sn2) (ps : list (list Z)) : sn2 := fold_left sn2_push ps st.

Definition sn2_flat (st : sn2) : list Z := fst st ++ snd st.

Definition OUT_sn2 (bs : list Z) : M sn2 unit :=
  st <- mget ;; let '(d, o) := st in
  if zlength o + zlength bs <=? SN_CAP then mput (d, o ++ bs) else mput (d ++ o ++ bs, []).
Definition OUTFP_sn2 (y w p fl t : Z) : M sn2 Z := munr.

Lemma sn2_flat_push : forall st bs, sn2_flat (sn2_push st bs) = sn2_flat st ++ bs.
Proof.
  intros [d o] bs. unfold sn2_push, sn2_flat. destruct (zlength o + zlength bs <=? SN_CAP); cbn [fst snd].
  - rewrite app_assoc. reflexivity.
  - rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma sn2_flat_pushes : forall ps st, sn2_flat (sn2_pushes st ps) = sn2_flat st ++ concat ps.
Proof.
  induction ps as [|p ps IH]; intros st; cbn [sn2_pushes fold_left concat].
  - rewrite app_nil_r. reflexivity.
  - change (fold_left sn2_push ps (sn2_push st p)) with (sn2_pushes (sn2_push st p) ps).
    rewrite IH, sn2_flat_push, app_assoc. reflexivity.
Qed.

Lemma sn2_pushes_app : forall ps qs st, sn2_pushes st (ps ++ qs) = sn2_pushes (sn2_pushes st ps) qs.
Proof. intros. unfold sn2_pushes. apply fold_left_app. Qed.

Lemma sn2_pushes_cons : forall p ps st, sn2_pushes st (p :: ps) = sn2_pushes (sn2_push st p) ps.
Proof. reflexivity. Qed.

Lemma sn2_pushes_nil : forall st, sn2_pushes st [] = st.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sn2_push_cap : forall st bs, zlength (snd st) <= SN_CAP -> zlength (snd (sn2_push st bs)) <= SN_CAP.
Proof.
  intros [d o] bs H. unfold sn2_push. destruct (zlength o + zlength bs <=? SN_CAP) eqn:E; cbn [snd].
  - apply Z.leb_le in E. rewrite zlength_app. exact E.
  - unfold SN_CAP. rewrite zlength_nil. lia.
Qed.
Lemma sn2_pushes_cap : forall ps st, zlength (snd st) <= SN_CAP -> zlength (snd (sn2_pushes st ps)) <= SN_CAP.
Proof.
  induction ps as [|p ps IH]; intros st H; [exact H|]. rewrite sn2_pushes_cons. apply IH, sn2_push_cap, H.
Qed.

(* [comment removed for export] *)
Lemma OUT_sn2_eq : forall bs st, OUT_sn2 bs st = ITree.Ret (Ok (tt, sn2_push st bs)).
Proof.
  intros bs [d o]. unfold OUT_sn2, sn2_push. rewrite (mbind_eq mget _ (d, o) (d, o) (d, o)) by reflexivity.
  destruct (zlength o + zlength bs <=? SN_CAP); reflexivity.
Qed.

Lemma mpad_sn2_eq : forall c w l fl st ps,
  pad_pieces c w l fl = Some ps -> mpad OUT_sn2 c w l fl st = ITree.Ret (Ok (tt, sn2_pushes st ps)).
Proof.
  intros c w l fl st ps P. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. apply OUT_sn2_eq.
Qed.

Lemma conv_tail_sn2 : forall cnt fl w p prefix body (k : Z -> M sn2 Z) st ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) ->
  mbind (conv_tail OUT_sn2 cnt fl w p prefix body) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt fl w p prefix body k st ps r T. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  pose proof (mpad_sn2_eq _ _ _ _ st _ P1) as E1. msn E1.
  pose proof (OUT_sn2_eq prefix (sn2_pushes st p1)) as E2. msn E2.
  pose proof (mpad_sn2_eq _ _ _ _ (sn2_push (sn2_pushes st p1) prefix) _ P2) as E3. msn E3.
  pose proof (mpad_sn2_eq _ _ _ _ (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) _ P3) as E4. msn E4.
  pose proof (OUT_sn2_eq body (sn2_pushes (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) p3)) as E5. msn E5.
  pose proof (mpad_sn2_eq _ _ _ _ (sn2_push (sn2_pushes (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) p3) body) _ P4) as E6. msn E6.
  rewrite mbind_mret. f_equal.
  rewrite !sn2_pushes_app. cbn [app]. rewrite !sn2_pushes_cons, !sn2_pushes_app, !sn2_pushes_cons. reflexivity.
Qed.

Lemma conv_int_sn2 : forall cnt fl w p xp argi prefix body (k : Z -> M sn2 Z) st ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
  mbind (conv_int OUT_sn2 cnt fl w p xp argi prefix body) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt fl w p xp argi prefix body k st ps r T. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn2; eassumption.
Qed.

Lemma conv_sn2 : forall cnt d a (k : Z -> M sn2 Z) st ps r,
  conv_pieces cnt d a = Some (ps, r) ->
  mbind (conv OUT_sn2 OUTFP_sn2 cnt d a) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt d a k st ps r T. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn2; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn2; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn2; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn2; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_sn2; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn2 : forall fuel s args cnt st ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) ->
  printf_loop OUT_sn2 OUTFP_sn2 fuel s args cnt st = ITree.Ret (Ok (r, sn2_pushes st ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt st ps r P; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P.
    pose proof (OUT_sn2_eq lit st) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R). reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P.
    pose proof (OUT_sn2_eq [] st) as E1. msn E1.
    rewrite (conv_sn2 _ _ _ _ _ _ _ C).
    rewrite (IH _ _ _ _ _ _ R). rewrite sn2_pushes_cons, sn2_pushes_app. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem printf_model_sn2_pushes : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) ->
  printf_model OUT_sn2 OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, sn2_pushes ([], []) ps)).
Proof. intros fmt args ps r P. unfold printf_model, printf_pieces in *. exact (printf_loop_sn2 _ _ _ _ _ _ _ P). Qed.

Theorem printf_model_sn2 : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) ->
  exists d o, printf_model OUT_sn2 OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
              /\ d ++ o = concat ps /\ zlength o <= SN_CAP.
Proof.
  intros fmt args ps r P. rewrite (printf_model_sn2_pushes _ _ _ _ P).
  pose proof (sn2_flat_pushes ps ([], [])) as F. pose proof (sn2_pushes_cap ps ([], []) ltac:(cbn [snd]; rewrite zlength_nil; unfold SN_CAP; lia)) as Cp.
  destruct (sn2_pushes ([], []) ps) as [d o]. exists d, o. split; [reflexivity|]. split; [exact F | exact Cp].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OUT_sn2b (cap : Z) (bs : list Z) : M sn2 unit :=
  st <- mget ;; let '(d, o) := st in
  if zlength d + zlength o + zlength bs <=? cap
  then (if zlength o + zlength bs <=? SN_CAP then mput (d, o ++ bs) else mput (d ++ o ++ bs, []))
  else munr.

Lemma zlength_sn2_flat : forall st, zlength (sn2_flat st) = zlength (fst st) + zlength (snd st).
Proof. intros [d o]. unfold sn2_flat. cbn [fst snd]. apply zlength_app. Qed.

Lemma zlength_flat_pushes : forall ps st, zlength (sn2_flat (sn2_pushes st ps)) = zlength (sn2_flat st) + zlength (concat ps).
Proof. intros. rewrite sn2_flat_pushes. apply zlength_app. Qed.
Lemma zlength_flat_push : forall st bs, zlength (sn2_flat (sn2_push st bs)) = zlength (sn2_flat st) + zlength bs.
Proof. intros. rewrite sn2_flat_push. apply zlength_app. Qed.

Section Bounded.
Variable cap : Z.

Lemma OUT_sn2b_eq : forall bs st, zlength (sn2_flat st) + zlength bs <= cap ->
  OUT_sn2b cap bs st = ITree.Ret (Ok (tt, sn2_push st bs)).
Proof.
  intros bs [d o] H. rewrite zlength_sn2_flat in H. cbn [fst snd] in H.
  unfold OUT_sn2b, sn2_push. rewrite (mbind_eq mget _ (d, o) (d, o) (d, o)) by reflexivity.
  replace (zlength d + zlength o + zlength bs <=? cap) with true by (symmetry; apply Z.leb_le; exact H).
  destruct (zlength o + zlength bs <=? SN_CAP); reflexivity.
Qed.

Lemma mpad_sn2b_eq : forall c w l fl st ps,
  pad_pieces c w l fl = Some ps -> zlength (sn2_flat st) + zlength (concat ps) <= cap ->
  mpad (OUT_sn2b cap) c w l fl st = ITree.Ret (Ok (tt, sn2_pushes st ps)).
Proof.
  intros c w l fl st ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in H. rewrite app_nil_r in H.
    apply OUT_sn2b_eq. exact H.
Qed.

Lemma conv_tail_sn2b : forall cnt fl w p prefix body (k : Z -> M sn2 Z) st ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength (sn2_flat st) + zlength (concat ps) <= cap ->
  mbind (conv_tail (OUT_sn2b cap) cnt fl w p prefix body) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt fl w p prefix body k st ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
  pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
  pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body).
  pose proof (mpad_sn2b_eq _ _ _ _ st _ P1 ltac:(lia)) as E1. msn E1.
  pose proof (OUT_sn2b_eq prefix (sn2_pushes st p1) ltac:(rewrite zlength_flat_pushes; lia)) as E2. msn E2.
  pose proof (mpad_sn2b_eq _ _ _ _ (sn2_push (sn2_pushes st p1) prefix) _ P2 ltac:(rewrite zlength_flat_push, zlength_flat_pushes; lia)) as E3. msn E3.
  pose proof (mpad_sn2b_eq _ _ _ _ (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) _ P3
                ltac:(rewrite zlength_flat_pushes, zlength_flat_push, zlength_flat_pushes; lia)) as E4. msn E4.
  pose proof (OUT_sn2b_eq body (sn2_pushes (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) p3)
                ltac:(rewrite !zlength_flat_pushes, zlength_flat_push, zlength_flat_pushes; lia)) as E5. msn E5.
  pose proof (mpad_sn2b_eq _ _ _ _ (sn2_push (sn2_pushes (sn2_pushes (sn2_push (sn2_pushes st p1) prefix) p2) p3) body) _ P4
                ltac:(rewrite zlength_flat_push, !zlength_flat_pushes, zlength_flat_push, zlength_flat_pushes; lia)) as E6. msn E6.
  rewrite mbind_mret. f_equal.
  rewrite !sn2_pushes_app. cbn [app]. rewrite !sn2_pushes_cons, !sn2_pushes_app, !sn2_pushes_cons. reflexivity.
Qed.

Lemma conv_int_sn2b : forall cnt fl w p xp argi prefix body (k : Z -> M sn2 Z) st ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength (sn2_flat st) + zlength (concat ps) <= cap ->
  mbind (conv_int (OUT_sn2b cap) cnt fl w p xp argi prefix body) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt fl w p xp argi prefix body k st ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn2b; eassumption.
Qed.

Lemma conv_sn2b : forall cnt d a (k : Z -> M sn2 Z) st ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength (sn2_flat st) + zlength (concat ps) <= cap ->
  mbind (conv (OUT_sn2b cap) OUTFP_sn2 cnt d a) k st = k r (sn2_pushes st ps).
Proof.
  intros cnt d a k st ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn2b; eassumption.
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply conv_tail_sn2b; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn2b; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn2b; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_sn2b; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn2b : forall fuel s args cnt st ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength (sn2_flat st) + zlength (concat ps) <= cap ->
  printf_loop (OUT_sn2b cap) OUTFP_sn2 fuel s args cnt st = ITree.Ret (Ok (r, sn2_pushes st ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt st ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn2b_eq lit st ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_flat_push; lia). reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn2b_eq [] st ltac:(rewrite zlength_nil; lia)) as E1. msn E1.
    rewrite (conv_sn2b _ _ _ _ _ _ _ C) by (rewrite zlength_flat_push, zlength_nil; lia).
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_flat_pushes, zlength_flat_push, zlength_nil; lia).
    rewrite sn2_pushes_cons, sn2_pushes_app. reflexivity.
Qed.

Theorem printf_model_sn2b_pushes : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= cap ->
  printf_model (OUT_sn2b cap) OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, sn2_pushes ([], []) ps)).
Proof.
  intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (printf_loop_sn2b _ _ _ _ ([], []) _ _ P ltac:(rewrite zlength_sn2_flat; cbn [fst snd]; rewrite zlength_nil; lia)).
Qed.

Theorem printf_model_sn2b : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= cap ->
  exists d o, printf_model (OUT_sn2b cap) OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
              /\ d ++ o = concat ps /\ zlength o <= SN_CAP.
Proof.
  intros fmt args ps r P H. rewrite (printf_model_sn2b_pushes _ _ _ _ P H).
  pose proof (sn2_flat_pushes ps ([], [])) as F. pose proof (sn2_pushes_cap ps ([], []) ltac:(cbn [snd]; rewrite zlength_nil; unfold SN_CAP; lia)) as Cp.
  destruct (sn2_pushes ([], []) ps) as [d o]. exists d, o. split; [reflexivity|]. split; [exact F | exact Cp].
Qed.
End Bounded.
