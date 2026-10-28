(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Monad.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_pad_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import Printf_model.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_printf_iface_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_printf_core_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFpNF.
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

Lemma OUTFP_sn_eq : forall y w p fl t o o1 r, fmt_fp' o y w p fl t = Some (o1, r) -> zlength o1 <= SN_CAP ->
  OUTFP_sn y w p fl t o = ITree.Ret (Ok (r, o1)).
Proof.
  intros y w p fl t o o1 r E H. unfold OUTFP_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  rewrite E. replace (zlength o1 <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
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
  destruct a as [s|i|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
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
Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof.
  intros x Hx. destruct (Z_lt_le_dec x 10).
  - rewrite dec_digits_small by lia. rewrite Z.div_small, Z.mod_small, dec_digits_0 by lia. reflexivity.
  - apply dec_digits_step. lia.
Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. intros x Hx. rewrite dec_digits_step1 by lia. rewrite length_app. cbn. lia. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof.
  induction n as [|n IH]; intros x Hx H64.
  - cbn in Hx. replace x with 0 by lia. rewrite dec_digits_0. cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite dec_digits_0; cbn; lia|].
    rewrite dec_digits_step1 by lia. rewrite length_app. cbn [length].
    specialize (IH (x / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)). lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Lemma zsub_snoc : forall l i n, 0 <= i -> 0 <= n -> i + n + 1 <= zlength l ->
  zsub l i (n + 1) = zsub l i n ++ [znth l (i + n)].
Proof.
  intros l i n Hi Hn H. unfold zsub, zlength in *.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite firstn_S_snoc by (rewrite length_skipn; lia). rewrite nth_skipn.
  unfold znth. destruct (Z.ltb_spec0 (i + n) 0); [lia|].
  replace (Z.to_nat (i + n)) with (Z.to_nat i + Z.to_nat n)%nat by lia. reflexivity.
Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. intros. reflexivity. Qed.

Lemma fmt_u_loop_dec : forall (n : nat) fuel y s b,
  (n < fuel)%nat -> 0 <= y < 10 ^ Z.of_nat n -> y < 2^64 -> Z.of_nat n <= s -> s <= zlength b ->
  exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - zlength (dec_digits y), b')
    /\ length b' = length b
    /\ zsub b' (s - zlength (dec_digits y)) (zlength (dec_digits y)) = dec_digits y
    /\ (forall i, ~ (s - zlength (dec_digits y) <= i < s) -> znth b' i = znth b i).
Proof.
  induction n as [|n IH]; intros fuel y s b Hf Hy Hy64 Hs Hb.
  - cbn in Hy. destruct fuel as [|fuel]; [lia|]. exists b. cbn [fmt_u_loop].
    replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    replace y with 0 by lia. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
  - destruct fuel as [|fuel]; [lia|].
    destruct (Z.eq_dec y 0) as [->|NZ].
    + exists b. cbn [fmt_u_loop Z.eqb negb]. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
    + cbn [fmt_u_loop]. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      unfold fmt_u_loop_body at 1.
      rewrite Nat2Z.inj_succ in Hy, Hs. rewrite Z.pow_succ_r in Hy by lia.
      destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10)) ltac:(lia)
                  ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)
                  ltac:(lia) ltac:(rewrite zlength_zupd; lia))
        as (b' & E & LEN & SUB & OUT).
      pose proof (dec_digits_step1 y ltac:(lia)) as DD.
      assert (LD : zlength (dec_digits y) = zlength (dec_digits (y / 10)) + 1) by (rewrite DD, zlength_app; reflexivity).
      pose proof (zlength_nonneg (dec_digits (y / 10))) as L0.
      pose proof (dec_digits_len_bound n (y / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)) as L20.
      unfold zlength in *.
      exists b'. split; [rewrite E; f_equal; f_equal; f_equal; lia|].
      split; [rewrite LEN; apply zupd_length|].
      split.
      * rewrite LD. replace (s - (Z.of_nat (length (dec_digits (y / 10))) + 1)) with (s - 1 - Z.of_nat (length (dec_digits (y / 10)))) by lia.
        rewrite zsub_snoc by (unfold zlength; rewrite ?LEN, ?zupd_length; lia).
        rewrite SUB. replace (s - 1 - Z.of_nat (length (dec_digits (y / 10))) + Z.of_nat (length (dec_digits (y / 10)))) with (s - 1) by lia.
        rewrite OUT by lia. rewrite znth_zupd_eq by (unfold zlength; lia). rewrite DD. unfold CHR_0. reflexivity.
      * intros i Hi. rewrite OUT by lia. apply znth_zupd_neq. lia.
Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fmt_u_dec : forall x, 0 <= x < 2^64 ->
  exists b', fmt_u x (zrepeat 0 24) 24 = Some (24 - zlength (dec_digits x), b')
    /\ zlength b' = 24 /\ zsub b' (24 - zlength (dec_digits x)) (zlength (dec_digits x)) = dec_digits x.
Proof.
  intros x Hx. unfold fmt_u. change FMT_U_FUEL with 21%nat.
  destruct (fmt_u_loop_dec 20 21 x 24 (zrepeat 0 24) ltac:(lia) ltac:(pose proof pow10_20; lia) ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia) ltac:(change (zlength (zrepeat 0 24)) with 24; lia))
    as (b' & E & LEN & SUB & _).
  exists b'. rewrite E. split; [reflexivity|]. split; [unfold zlength; rewrite LEN; reflexivity| exact SUB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zb1 :=
  match goal with
  | |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
  | |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
  | |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
  end; cbn [andb orb negb]; cbv beta iota.

(* [comment removed for export] *)
Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. reflexivity. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. reflexivity. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. reflexivity. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

(* [comment removed for export] *)
Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

(* [comment removed for export] *)
Lemma tail_pieces_d : forall prefix body, zlength prefix <= 1 -> 1 <= zlength body <= 20 ->
  tail_pieces 0 0 0 (Z.max (-1) (zlength body + 0)) prefix body = Some ([prefix; body], zlength prefix + zlength body).
Proof.
  intros prefix body Hp Hb. pose proof (zlength_nonneg prefix). unfold tail_pieces. cbv zeta.
  replace (Z.max (Z.max (-1) (zlength body + 0)) (zlength body)) with (zlength body) by lia.
  replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
  unfold INT_MAX. zb1. zb1.
  unfold pad_pieces. fl0. zb1. zb1. reflexivity.
Qed.

Lemma printf_pieces_d_pos : forall x, 1 <= x < 2^31 ->
  printf_pieces FMT_d [PA_i x] = Some ([[]; []; dec_digits x], zlength (dec_digits x)).
Proof.
  intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
  rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1.
  unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
  pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x).
  zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma printf_pieces_d_neg : forall x, -2^31 <= x < 0 ->
  printf_pieces FMT_d [PA_i x] = Some ([[]; [45]; dec_digits (- x)], 1 + zlength (dec_digits (- x))).
Proof.
  intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
  replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
  unfold INTMAX_MAX. zb1.
  replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
  unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
  pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)).
  zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma fmt_d_pos : forall x, 1 <= x < 2^31 -> fmt_d x = Some (dec_digits x, zlength (dec_digits x)).
Proof.
  intros x Hx. unfold fmt_d. cbv zeta. unfold u64. rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1. fl0.
  destruct (fmt_u_dec x ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
  pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x). unfold zlength in *.
  repeat zb1.
  replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits x))) + 0)) with (Z.of_nat (length (dec_digits x))) by lia.
  unfold INT_MAX. repeat zb1.
  rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
  change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 0) with (@nil Z). cbn [app]. rewrite app_nil_r.
  replace (24 - (24 - Z.of_nat (length (dec_digits x)))) with (Z.of_nat (length (dec_digits x))) by lia.
  rewrite SUB. repeat f_equal; lia.
Qed.

Lemma fmt_d_neg : forall x, -2^31 <= x < 0 -> fmt_d x = Some (45 :: dec_digits (- x), 1 + zlength (dec_digits (- x))).
Proof.
  intros x Hx. unfold fmt_d. cbv zeta. unfold u64.
  replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
  unfold INTMAX_MAX. zb1.
  replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
  destruct (fmt_u_dec (- x) ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
  pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)). unfold zlength in *.
  repeat zb1.
  replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits (- x)))) + 0)) with (Z.of_nat (length (dec_digits (- x)))) by lia.
  unfold INT_MAX. repeat zb1.
  rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
  change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 1) with [45]. cbn [app]. rewrite app_nil_r.
  replace (24 - (24 - Z.of_nat (length (dec_digits (- x))))) with (Z.of_nat (length (dec_digits (- x)))) by lia.
  rewrite SUB. repeat f_equal; lia.
Qed.

Theorem printf_sn_d : forall i o r, -2^31 <= i < 2^31 -> fmt_d i = Some (o, r) ->
  printf_model OUT_sn OUTFP_sn FMT_d [PA_i i] [] = ITree.Ret (Ok (r, o)).
Proof.
  intros i o r Hi E.
  destruct (Z.eq_dec i 0) as [->|NZ].
  { vm_compute in E. inversion E; subst. vm_compute. reflexivity. }
  pose proof (dec_digits_length (Z.abs i)) as L.
  destruct (Z_lt_le_dec i 0).
  - rewrite fmt_d_neg in E by lia. inversion E; subst. rewrite Z.abs_neq in L by lia.
    rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_neg i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
    unfold zlength, SN_CAP. cbn [length]. lia.
  - rewrite fmt_d_pos in E by lia. inversion E; subst. rewrite Z.abs_eq in L by lia.
    rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_pos i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
    unfold zlength, SN_CAP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lhs_cbvg1 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp fmt_fp' f128_of_d conv OUT_sn OUTFP_sn mbind mret] in l in change l with l' end.
Ltac lhs_cbvg2 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp fmt_fp' f128_of_d OUT_sn OUTFP_sn mbind mret munr Z.ltb Z.leb orb Z.sub Z.add] in l in change l with l' end.

Lemma printf_sn_g_prec : forall d prec o l, (prec = 15 \/ prec = 17) ->
  fmt_fp' [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> 0 <= l <= INT_MAX -> zlength o <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn (if prec =? 15 then FMT_g15 else FMT_g17) [PA_g d] [] = ITree.Ret (Ok (l, o)).
Proof.
  intros d prec o l Hp F Hl Ho.
  destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb];
    unfold printf_model; lhs_cbvg1;
    (pose proof (OUT_sn_eq [] [] ltac:(rewrite zlength_nil; unfold SN_CAP; lia)) as E0; msn E0; clear E0);
    unfold conv; lhs_cbvg2.
  - replace (15 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 15))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
  - replace (17 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 17))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lzeqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && lzeqb a' b'
  | _, _ => false
  end.
Lemma lzeqb_eq : forall a b, lzeqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. apply IH. exact H2.
Qed.

Definition u04x_check (c : Z) : bool :=
  match printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] [] with
  | ITree.Ret (Ok (r, o)) => (r =? 5) && lzeqb o (117 :: hex4_lower c)
  | _ => false
  end.
Lemma u04x_check_all : forallb u04x_check (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem printf_sn_u04x : forall c, 0 <= c < 256 ->
  printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] [] = ITree.Ret (Ok (5, 117 :: hex4_lower c)).
Proof.
  intros c Hc.
  assert (CK : u04x_check c = true).
  { pose proof u04x_check_all as A. rewrite forallb_forall in A. apply A.
    apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  unfold u04x_check in CK.
  destruct (printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] []) as [[|[r o]]|n k]; try discriminate.
  apply andb_prop in CK. destruct CK as [H1 H2]. apply Z.eqb_eq in H1. apply lzeqb_eq in H2. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pass1_ok_d : pass1_ok FMT_d = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g15 : pass1_ok FMT_g15 = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g17 : pass1_ok FMT_g17 = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g : forall prec, pass1_ok (if prec =? 15 then FMT_g15 else FMT_g17) = true.
Proof. intros prec. destruct (prec =? 15); reflexivity. Qed.
Lemma pass1_ok_u04x : pass1_ok FMT_u04x = true. Proof. reflexivity. Qed.
Lemma fp_calls_d : forall i, fp_calls (length FMT_d) FMT_d [PA_i i] = [].
Proof. intros. reflexivity. Qed.
Lemma fp_calls_u04x : forall u, fp_calls (length FMT_u04x) FMT_u04x [PA_u u] = [].
Proof. intros. reflexivity. Qed.
Lemma fp_calls_g : forall prec d, (prec = 15 \/ prec = 17) ->
  fp_calls (length (if prec =? 15 then FMT_g15 else FMT_g17)) (if prec =? 15 then FMT_g15 else FMT_g17) [PA_g d] = [(f128_of_d d, 1, prec, 0, CHR_g)].
Proof. intros prec d [-> | ->]; reflexivity. Qed.
