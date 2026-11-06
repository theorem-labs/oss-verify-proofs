(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX PrintfFormats ApFmt.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_concat_app' : forall (ps qs : list (list Z)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app'. Qed.
Lemma zlength_concat_cons' : forall (p : list Z) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app'. Qed.
Lemma zlength_nonneg'' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

(* [comment removed for export] *)
Lemma pad_pieces_len : forall c w l fl pp, pad_pieces c w l fl = Some pp ->
  zlength (concat pp) = (if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then 0 else w - l).
Proof.
  intros c w l fl pp H. unfold pad_pieces in H.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool eqn:E.
  - injection H as <-. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. injection H as <-. cbn [concat]. rewrite app_nil_r.
    apply orb_false_iff in E. destruct E as [_ E]. apply Z.leb_gt in E. apply zlength_zrepeat. lia.
Qed.

(* [comment removed for export] *)
Lemma land_pow2 : forall a k, 0 <= k -> Z.land a (2^k) = (if Z.testbit a k then 2^k else 0).
Proof.
  intros a k Hk. apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.testbit a k) eqn:T.
  - rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec k n); [subst; rewrite T; reflexivity | apply andb_false_r].
  - rewrite Z.bits_0. destruct (Z.eqb_spec k n); [subst; rewrite T; reflexivity | apply andb_false_r].
Qed.
Lemma land_LA : forall fl, Z.land fl LEFT_ADJ = (if Z.testbit fl 13 then LEFT_ADJ else 0).
Proof. intros. unfold LEFT_ADJ. change 8192 with (2^13). apply land_pow2. lia. Qed.
Lemma land_ZP : forall fl, Z.land fl ZERO_PAD = (if Z.testbit fl 16 then ZERO_PAD else 0).
Proof. intros. unfold ZERO_PAD. change 65536 with (2^16). apply land_pow2. lia. Qed.

(* [comment removed for export] *)
Lemma padtest_plain : forall fl, (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = negb (Z.testbit fl 13 || Z.testbit fl 16).
Proof.
  intros fl. rewrite Z.land_lor_distr_r, land_LA, land_ZP.
  destruct (Z.testbit fl 13), (Z.testbit fl 16); reflexivity.
Qed.
Lemma padtest_xzp : forall fl, (Z.land (Z.lxor fl ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = negb (Z.testbit fl 13 || negb (Z.testbit fl 16)).
Proof.
  intros fl. rewrite Z.land_lor_distr_r, !land_LA, !land_ZP.
  rewrite !Z.lxor_spec. change (Z.testbit ZERO_PAD 13) with false. change (Z.testbit ZERO_PAD 16) with true.
  destruct (Z.testbit fl 13), (Z.testbit fl 16); reflexivity.
Qed.
Lemma padtest_xla : forall fl, (Z.land (Z.lxor fl LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = negb (negb (Z.testbit fl 13) || Z.testbit fl 16).
Proof.
  intros fl. rewrite Z.land_lor_distr_r, !land_LA, !land_ZP.
  rewrite !Z.lxor_spec. change (Z.testbit LEFT_ADJ 13) with true. change (Z.testbit LEFT_ADJ 16) with false.
  destruct (Z.testbit fl 13), (Z.testbit fl 16); reflexivity.
Qed.
Lemma padtest_zero : forall c p n, pad_pieces c p n 0 = (if p <=? n then Some [] else if 256 <=? p - n then None else Some [zrepeat c (p - n)]).
Proof. intros. unfold pad_pieces. cbn [Z.land Z.eqb negb orb]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tail_pieces_len : forall cnt fl w p prefix body ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) ->
  Z.testbit fl 13 && Z.testbit fl 16 = false ->
  zlength (concat ps) = r - cnt.
Proof.
  intros cnt fl w p prefix body ps r T B. unfold tail_pieces in T. cbv zeta in T.
  set (pl := zlength prefix) in T. set (n := zlength body) in T. set (p' := Z.max p n) in T.
  destruct (INT_MAX - pl <? p'); [discriminate|].
  set (w' := Z.max w (pl + p')) in T.
  destruct (INT_MAX - cnt <? w'); [discriminate|].
  destruct (pad_pieces 32 w' (pl + p') fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 w' (pl + p') (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 p' n 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 w' (pl + p') (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  injection T as <- <-.
  pose proof (pad_pieces_len _ _ _ _ _ P1) as L1. rewrite padtest_plain in L1.
  pose proof (pad_pieces_len _ _ _ _ _ P2) as L2. rewrite padtest_xzp in L2.
  pose proof (pad_pieces_len _ _ _ _ _ P3) as L3. cbn [Z.land Z.eqb negb orb] in L3.
  pose proof (pad_pieces_len _ _ _ _ _ P4) as L4. rewrite padtest_xla in L4.
  repeat first [rewrite zlength_concat_app' | rewrite zlength_concat_cons']. rewrite L1, L2, L3, L4. change (zlength (concat [])) with 0. rewrite ?Z.add_0_r.
  pose proof (zlength_nonneg'' prefix). pose proof (zlength_nonneg'' body). fold pl. fold n.
  change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD)) with 0.
  destruct (Z.testbit fl 13), (Z.testbit fl 16); cbn [negb orb andb] in *; try discriminate;
    destruct (Z.leb_spec w' (pl + p')); destruct (Z.leb_spec p' n); cbn [Z.eqb negb orb]; lia.
Qed.

Lemma int_pieces_len : forall cnt fl w p xp argi prefix body ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
  Z.testbit fl 13 && Z.testbit fl 16 = false ->
  zlength (concat ps) = r - cnt.
Proof.
  intros cnt fl w p xp argi prefix body ps r T B. unfold int_pieces in T.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T.
  assert (B' : Z.testbit (if xp then Z.land fl (Z.lnot ZERO_PAD) else fl) 13 && Z.testbit (if xp then Z.land fl (Z.lnot ZERO_PAD) else fl) 16 = false).
  { destruct xp; [|exact B]. rewrite !Z.land_spec, !Z.lnot_spec by lia. change (Z.testbit ZERO_PAD 16) with true. cbn [negb]. rewrite !andb_false_r. reflexivity. }
  destruct ((argi =? 0) && (p =? 0))%bool; eapply tail_pieces_len; eassumption.
Qed.

(* [comment removed for export] *)
Lemma convx_fl_ok : forall fl,
  let fl' := (if Z.land fl LEFT_ADJ =? 0 then fl else Z.land fl (Z.lnot ZERO_PAD)) in
  Z.testbit fl' 13 && Z.testbit fl' 16 = false.
Proof.
  intros fl. cbv zeta. rewrite land_LA. destruct (Z.testbit fl 13) eqn:T.
  - cbn [Z.eqb LEFT_ADJ]. rewrite !Z.land_spec, !Z.lnot_spec by lia. change (Z.testbit ZERO_PAD 16) with true. cbn [negb]. rewrite !andb_false_r. reflexivity.
  - cbn [Z.eqb]. rewrite T. reflexivity.
Qed.
Lemma nozp_ok : forall fl, Z.testbit (Z.land fl (Z.lnot ZERO_PAD)) 13 && Z.testbit (Z.land fl (Z.lnot ZERO_PAD)) 16 = false.
Proof.
  intros fl. rewrite !Z.land_spec, !Z.lnot_spec by lia. change (Z.testbit ZERO_PAD 16) with true. cbn [negb]. rewrite !andb_false_r. reflexivity.
Qed.

Lemma conv_piecesx_len : forall cnt d a ps r, conv_piecesx cnt d a = Some (ps, r) -> zlength (concat ps) = r - cnt.
Proof.
  intros cnt d a ps r T. unfold conv_piecesx in T.
  pose proof (convx_fl_ok (d_fl d)) as B. cbv zeta in B.
  set (fl' := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD)) in T, B.
  cbv zeta in T.
  destruct a as [s| |i|u|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|]. destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply tail_pieces_len; [exact T | apply nozp_ok].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|]. destruct ((d_p d <? 0) && (INT_MAX <=? zlength NULLSTR))%bool; [discriminate|].
    eapply tail_pieces_len; [exact T | apply nozp_ok].
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (d_t d =? 99). { eapply tail_pieces_len; [exact T | apply nozp_ok]. }
    destruct (INTMAX_MAX <? i mod 2 ^ 64); [|destruct (negb (Z.land fl' MARK_POS =? 0)); [|destruct (negb (Z.land fl' PAD_POS =? 0))]];
      eapply int_pieces_len; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply int_pieces_len; eassumption.
  - destruct ((d_ty d =? T_SIZET) || (d_ty d =? T_ULONG))%bool.
    + destruct (d_t d =? 117); [eapply int_pieces_len; eassumption|].
      destruct ((d_t d =? 120) || (d_t d =? 88))%bool; [|discriminate]. eapply int_pieces_len; eassumption.
    + destruct (d_ty d =? T_LONG); [|discriminate].
      destruct (INTMAX_MAX <? u); [|destruct (negb (Z.land fl' MARK_POS =? 0)); [|destruct (negb (Z.land fl' PAD_POS =? 0))]];
        eapply int_pieces_len; eassumption.
  - discriminate.
Qed.

Lemma printf_piecesx_loop_len : forall fuel s args cnt ps r,
  printf_piecesx_loop fuel s args cnt = Some (ps, r) -> zlength (concat ps) = r - cnt.
Proof.
  induction fuel as [|fuel IH]; intros s args cnt ps r P; [discriminate|].
  cbn [printf_piecesx_loop] in P.
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { injection P as <- <-. change (zlength (concat (@nil (list Z)))) with 0. lia. }
  cbv zeta in P. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_piecesx_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    injection P as <- <-. rewrite zlength_concat_cons', (IH _ _ _ _ _ R). lia.
  - destruct (parse_dirx s2) as [[[d0 ws] s3]|]; [|discriminate].
    destruct (dir_eff d0 ws args) as [[d [|a args']]|]; [discriminate| |discriminate].
    destruct (conv_piecesx cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_piecesx_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    injection P as <- <-. repeat first [rewrite zlength_concat_app' | rewrite zlength_concat_cons']. rewrite (IH _ _ _ _ _ R), (conv_piecesx_len _ _ _ _ _ C).
    change (zlength (@nil Z)) with 0. lia.
Qed.

Theorem printf_piecesx_count : forall fmt args ps r,
  printf_piecesx fmt args = Some (ps, r) -> zlength (concat ps) = r.
Proof. intros fmt args ps r P. pose proof (printf_piecesx_loop_len _ _ _ _ _ _ P). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ppx_unfold : forall fuel s args cnt,
  printf_piecesx_loop (S fuel) s args cnt =
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then Some ([], cnt) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if INT_MAX - cnt <? l then None
           else match printf_piecesx_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
        else
          match parse_dirx s2 with
          | Some (d0, ws, s3) =>
              match dir_eff d0 ws args with
              | Some (d, a :: args') =>
                  match conv_piecesx cnt d a with
                  | Some (ps1, cnt') =>
                      match printf_piecesx_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
                  | None => None
                  end
              | _ => None
              end
          | None => None
          end
      end
    end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ppx_lit_cons : forall fuel lit c1 s2 args cnt,
  lit <> [] -> Forall (fun c => c <> 0 /\ c <> 37) lit ->
  (c1 = 0 \/ (c1 = 37 /\ match s2 with [] => False | c2 :: _ => c2 <> 37 end)) ->
  zlength lit <= INT_MAX - cnt ->
  printf_piecesx_loop (S fuel) (lit ++ c1 :: s2) args cnt
  = match printf_piecesx_loop fuel (c1 :: s2) args (cnt + zlength lit) with
    | Some (ps, r) => Some (lit :: ps, r) | None => None end.
Proof.
  intros fuel lit c1 s2 args cnt NE HF HC HL.
  rewrite ppx_unfold. destruct lit as [|c0 lit']; [contradiction|]. cbn [app].
  pose proof HF as HF0. apply Forall_cons_iff in HF. destruct HF as [[H0 H37] HF].
  replace (c0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  cbv zeta.
  change (c0 :: lit' ++ c1 :: s2) with ((c0 :: lit') ++ c1 :: s2).
  rewrite (lit_run_app (c0 :: lit') (c1 :: s2) HF0 ltac:(cbn; lia)).
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
  replace ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool with false.
  2:{ symmetry. destruct HC as [-> | [-> HS]]; [reflexivity|]. cbn [Z.eqb Pos.eqb andb]. destruct s2 as [|c2 ?]; [contradiction|]. apply Z.eqb_neq. exact HS. }
  replace (0 <? zlength (c0 :: lit')) with true by (symmetry; apply Z.ltb_lt; unfold zlength; cbn; lia).
  replace (INT_MAX - cnt <? zlength (c0 :: lit')) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ppx_dir : forall fuel s2 args cnt d0 ws s3 d a args' ps1 c1,
  match s2 with c2 :: _ => c2 <> 37 | [] => False end ->
  parse_dirx s2 = Some (d0, ws, s3) -> dir_eff d0 ws args = Some (d, a :: args') ->
  conv_piecesx cnt d a = Some (ps1, c1) ->
  printf_piecesx_loop (S fuel) (37 :: s2) args cnt
  = match printf_piecesx_loop fuel s3 args' c1 with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end.
Proof.
  intros fuel s2 args cnt d0 ws s3 d a args' ps1 c1 HS PD DE C.
  rewrite ppx_unfold. cbn [Z.eqb Pos.eqb lit_run orb]. cbv zeta. cbn [zlength length Z.of_nat skipn Z.ltb].
  destruct s2 as [|c2 s2']; [contradiction|].
  replace (c2 =? 37) with false by (symmetry; apply Z.eqb_neq; exact HS). cbn [andb].
  rewrite PD, DE, C. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ppx_nul : forall fuel rest args cnt, printf_piecesx_loop (S fuel) (0 :: rest) args cnt = Some ([], cnt).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ppx_noargs_shift_gen : forall fuel s c0 ps r,
  printf_piecesx_loop fuel s [] c0 = Some (ps, r) ->
  c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_piecesx_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
  induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
  rewrite ppx_unfold in P. setoid_rewrite ppx_unfold.
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg'' lit).
  destruct (0 <? zlength lit).
  - destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
    destruct (printf_piecesx_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
    split; [lia|]. intros k Hk Hr.
    replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
  - destruct (parse_dirx s2) as [[[d0 [ws pst]] s3]|]; [|discriminate].
    unfold dir_eff, dir_eff_w, dir_eff_p in P |- *. cbn [fst snd] in P |- *. destruct ws; [discriminate|]. destruct pst; discriminate.
Qed.
Lemma ppx_noargs_shift : forall fuel s cnt ps r,
  printf_piecesx_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
  printf_piecesx_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
  intros fuel s cnt ps r P Hc Hr. destruct (ppx_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
  rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fl_simple (fl : Z) : Prop := fl = 0 \/ fl = LEFT_ADJ \/ fl = ZERO_PAD.

(* [comment removed for export] *)
Lemma tail_pieces_dec : forall cnt fl w v, fl_simple fl -> 0 <= v < 2^64 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, tail_pieces cnt fl w (zdigits v) [] (dec_digits v) = Some (ps, cnt + Z.max w (zdigits v)).
Proof.
  intros cnt fl w v Hfl Hv Hw Hc HI.
  pose proof (dec_digits_zlength v) as DL.
  assert (HL : zlength (dec_digits v) <= zdigits v <= zlength (dec_digits v) + 1 /\ 1 <= zdigits v).
  { unfold zdigits, zdec. destruct (Z.eqb_spec v 0) as [->|NZ].
    - rewrite dec_digits_0. unfold zlength. cbn. lia.
    - pose proof (dec_digits_nz v ltac:(lia)) as NE. destruct (dec_digits v); [contradiction|]. unfold zlength. cbn. lia. }
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  replace (Z.max (zdigits v) (zlength (dec_digits v))) with (zdigits v) by lia.
  replace (INT_MAX - 0 <? zdigits v) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (INT_MAX - cnt <? Z.max w (0 + zdigits v)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.add_0_l.
  unfold pad_pieces. rewrite padtest_plain, padtest_xzp, padtest_xla. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true. cbn [negb].
  assert (TB : (Z.testbit fl 13 = false /\ Z.testbit fl 16 = false) \/ (Z.testbit fl 13 = true /\ Z.testbit fl 16 = false) \/ (Z.testbit fl 13 = false /\ Z.testbit fl 16 = true)).
  { destruct Hfl as [-> | [-> | ->]]; [left | right; left | right; right]; split; reflexivity. }
  destruct (Z.leb_spec (Z.max w (zdigits v)) (zdigits v));
  destruct (Z.leb_spec (zdigits v) (zlength (dec_digits v)));
  destruct TB as [[E13 E16] | [[E13 E16] | [E13 E16]]]; rewrite E13, E16; cbn [negb orb];
  repeat (replace (256 <=? Z.max w (zdigits v) - zdigits v) with false by (symmetry; apply Z.leb_gt; lia));
  repeat (replace (256 <=? zdigits v - zlength (dec_digits v)) with false by (symmetry; apply Z.leb_gt; lia));
  eexists; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_gen : forall cnt fl w p body,
  Z.testbit fl 13 && Z.testbit fl 16 = false -> 0 <= fl ->
  zlength body <= p -> p - zlength body < 256 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w p <= INT_MAX -> p <= INT_MAX ->
  exists ps, tail_pieces cnt fl w p [] body = Some (ps, cnt + Z.max w p).
Proof.
  intros cnt fl w p body B Hfl Hp Hpn Hw Hc HI HpI. pose proof (zlength_nonneg'' body) as Hb.
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  replace (Z.max p (zlength body)) with p by lia.
  replace (INT_MAX - 0 <? p) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.add_0_l.
  replace (INT_MAX - cnt <? Z.max w p) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces. rewrite padtest_plain, padtest_xzp, padtest_xla. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true. cbn [negb].
  destruct (Z.leb_spec (Z.max w p) p); destruct (Z.leb_spec p (zlength body));
  destruct (Z.testbit fl 13), (Z.testbit fl 16); cbn [negb orb andb] in B |- *; try discriminate;
  repeat (replace (256 <=? Z.max w p - p) with false by (symmetry; apply Z.leb_gt; lia));
  repeat (replace (256 <=? p - zlength body) with false by (symmetry; apply Z.leb_gt; lia));
  eexists; reflexivity.
Qed.

Lemma fl_simple_bits : forall fl, fl_simple fl -> Z.testbit fl 13 && Z.testbit fl 16 = false /\ 0 <= fl
  /\ Z.land fl MARK_POS = 0 /\ Z.land fl PAD_POS = 0 /\ Z.land fl ALT_FORM = 0
  /\ (if Z.land fl LEFT_ADJ =? 0 then fl else Z.land fl (Z.lnot ZERO_PAD)) = fl.
Proof. intros fl [-> | [-> | ->]]; repeat split; first [reflexivity | unfold LEFT_ADJ, ZERO_PAD; lia]. Qed.
Lemma fl_simple_nozp : forall fl, fl_simple fl -> fl_simple (Z.land fl (Z.lnot ZERO_PAD)).
Proof. intros fl [-> | [-> | ->]]; [left | right; left | left]; reflexivity. Qed.

Lemma zdigits_eq : forall v, 0 <= v < 2^64 -> Z.max (-1) (zlength (dec_digits v) + (if v =? 0 then 1 else 0)) = zdigits v /\ zlength (dec_digits v) <= zdigits v <= zlength (dec_digits v) + 1 /\ 1 <= zdigits v <= 20.
Proof.
  intros v Hv. pose proof (dec_digits_zlength v) as DL. unfold zdigits, zdec. destruct (Z.eqb_spec v 0) as [->|NZ].
  - rewrite dec_digits_0. unfold zlength. cbn. lia.
  - pose proof (dec_digits_nz v ltac:(lia)) as NE. pose proof (zlength_nonneg'' (dec_digits v)).
    assert (1 <= zlength (dec_digits v)) by (destruct (dec_digits v); [contradiction|]; unfold zlength; cbn; lia). lia.
Qed.

Lemma int_pieces_dec : forall cnt fl w v, fl_simple fl -> 0 <= v < 2^64 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, int_pieces cnt fl w (-1) false v [] (dec_digits v) = Some (ps, cnt + Z.max w (zdigits v)).
Proof.
  intros cnt fl w v Hfl Hv Hw Hc HI. destruct (zdigits_eq v Hv) as (E & HL & H1).
  destruct (fl_simple_bits fl Hfl) as (B & F0 & _).
  unfold int_pieces. cbn [andb]. rewrite andb_false_r. rewrite E.
  apply tail_pieces_gen; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma convx_dec_l : forall cnt fl w v, fl_simple fl -> 0 <= v < 2^63 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 100 T_LONG) (PA_z v) = Some (ps, cnt + Z.max w (zdigits v)).
Proof.
  intros cnt fl w v Hfl Hv Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change ((T_LONG =? T_SIZET) || (T_LONG =? T_ULONG))%bool with false. change (T_LONG =? T_LONG) with true. cbv iota.
  replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
  rewrite M, P. cbn [Z.eqb negb]. apply int_pieces_dec; try assumption; lia.
Qed.
Lemma convx_dec_lu : forall cnt fl w v, fl_simple fl -> 0 <= v < 2^64 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 117 T_ULONG) (PA_z v) = Some (ps, cnt + Z.max w (zdigits v)).
Proof.
  intros cnt fl w v Hfl Hv Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change ((T_ULONG =? T_SIZET) || (T_ULONG =? T_ULONG))%bool with true. change (117 =? 117) with true. cbv iota.
  apply int_pieces_dec; try assumption; lia.
Qed.
Lemma convx_dec_d : forall cnt fl w i, fl_simple fl -> 0 <= i < 2^31 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 100 T_INT) (PA_i i) = Some (ps, cnt + Z.max w (zdigits i)).
Proof.
  intros cnt fl w i Hfl Hi Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_INT =? T_INT)) with false. change (100 =? 99) with false. cbv iota.
  rewrite (Z.mod_small i (2^64)) by lia.
  replace (INTMAX_MAX <? i) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
  rewrite M, P. cbn [Z.eqb negb]. apply int_pieces_dec; try assumption; lia.
Qed.
Lemma convx_dec_u : forall cnt fl w u, fl_simple fl -> 0 <= u < 2^32 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 117 T_UINT) (PA_u u) = Some (ps, cnt + Z.max w (zdigits u)).
Proof.
  intros cnt fl w u Hfl Hu Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_UINT =? T_UINT)) with false. change (117 =? 117) with true. cbv iota.
  apply int_pieces_dec; try assumption; lia.
Qed.

(* [comment removed for export] *)
Definition xdigits (t u : Z) : Z := if u =? 0 then 1 else zlength (hex_digits (Z.land t 32) u).
Lemma digits_aux_S' : forall f b d y acc,
  digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc' : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
  induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S'.
  destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_length' : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S'.
  destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [length] in IH. lia.
Qed.
Lemma hex_digits_zlength : forall l x, 0 <= zlength (hex_digits l x) <= 16.
Proof. intros l x. unfold zlength, hex_digits. pose proof (digits_aux_length' 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []). cbn [length Nat.add] in H. lia. Qed.
Lemma hex_digits_nz : forall l x, 0 < x -> 1 <= zlength (hex_digits l x).
Proof.
  intros l x Hx. unfold hex_digits. change 16%nat with (S 15). rewrite digits_aux_S'.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc'. unfold zlength. rewrite length_app. cbn [length]. lia.
Qed.
Lemma convx_hex_u : forall cnt fl w u t, fl_simple fl -> 0 <= u < 2^32 -> (t = 120 \/ t = 88) -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 17 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false t T_UINT) (PA_u u) = Some (ps, cnt + Z.max w (xdigits t u)).
Proof.
  intros cnt fl w u t Hfl Hu Ht Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  pose proof (hex_digits_zlength (Z.land t 32) u) as XL.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_UINT =? T_UINT)) with false. replace (t =? 117) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  rewrite A. cbn [Z.eqb negb]. rewrite andb_false_r.
  unfold int_pieces. cbn [andb]. rewrite andb_false_r.
  assert (E : Z.max (-1) (zlength (hex_digits (Z.land t 32) u) + (if u =? 0 then 1 else 0)) = xdigits t u /\ zlength (hex_digits (Z.land t 32) u) <= xdigits t u <= zlength (hex_digits (Z.land t 32) u) + 1 /\ 1 <= xdigits t u <= 16).
  { unfold xdigits. destruct (Z.eqb_spec u 0) as [->|NZ].
    - change (hex_digits (Z.land t 32) 0) with (@nil Z). unfold zlength. cbn. lia.
    - pose proof (hex_digits_nz (Z.land t 32) u ltac:(lia)). lia. }
  destruct E as (E & HL & H1). rewrite E. apply tail_pieces_gen; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma convx_s_w : forall cnt fl w s, fl_simple fl -> zlength s <= 255 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 255 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 115 T_PTR) (PA_s s) = Some (ps, cnt + Z.max w (zlength s)).
Proof.
  intros cnt fl w s Hfl Hs Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  destruct (fl_simple_bits _ (fl_simple_nozp fl Hfl)) as (B' & F0' & _).
  pose proof (zlength_nonneg'' s) as Hs0.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_PTR =? T_PTR)) with false. cbv iota. change (-1 <? 0) with true.
  replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; unfold INT_MAX; lia). cbn [andb].
  rewrite firstn_all2 by (unfold zlength in *; lia).
  apply tail_pieces_gen; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma convx_c : forall cnt fl w c, fl_simple fl -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 1 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 99 T_INT) (PA_i c) = Some (ps, cnt + Z.max w 1).
Proof.
  intros cnt fl w c Hfl Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  destruct (fl_simple_bits _ (fl_simple_nozp fl Hfl)) as (B' & F0' & _).
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_INT =? T_INT)) with false. change (99 =? 99) with true. cbv iota.
  apply tail_pieces_gen; try assumption; try (unfold zlength; cbn; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT_F1 : list Z := [37; 53; 108; 100; 58; 100; 61; 37; 45; 50; 100; 32; 104; 108; 61; 37; 108; 100; 32; 108; 61; 37; 52; 108; 100; 32; 37; 115; 0].   (* [comment removed for export] *)
Definition FMT_F2 : list Z := [37; 53; 108; 100; 58; 100; 61; 37; 45; 50; 100; 32; 104; 108; 61; 37; 108; 100; 32; 108; 61; 105; 110; 102; 32; 32; 37; 115; 0].   (* [comment removed for export] *)
Definition FMT_F3 : list Z := [112; 114; 105; 118; 32; 91; 32; 37; 100; 32; 93; 32; 0].   (* [comment removed for export] *)
Definition FMT_F4 : list Z := [99; 111; 110; 116; 32; 91; 32; 37; 100; 32; 93; 0].   (* [comment removed for export] *)
Definition FMT_F5 : list Z := [97; 112; 112; 108; 32; 91; 32; 37; 100; 32; 93; 0].   (* [comment removed for export] *)
Definition FMT_F6 : list Z := [60; 65; 83; 78; 49; 32; 37; 100; 62; 0].   (* [comment removed for export] *)
Definition FMT_F7 : list Z := [37; 45; 49; 56; 115; 0].   (* [comment removed for export] *)
Definition FMT_F8 : list Z := [37; 42; 115; 0].   (* [comment removed for export] *)
Definition FMT_F9 : list Z := [108; 101; 110; 103; 116; 104; 32; 105; 115; 32; 103; 114; 101; 97; 116; 101; 114; 32; 116; 104; 97; 110; 32; 37; 108; 100; 10; 0].   (* [comment removed for export] *)
Definition FMT_F10 : list Z := [58; 37; 117; 0].   (* [comment removed for export] *)
Definition FMT_F11 : list Z := [37; 48; 50; 88; 0].   (* [comment removed for export] *)
Definition FMT_F12 : list Z := [46; 37; 108; 117; 0].   (* [comment removed for export] *)
Definition FMT_F13 : list Z := [37; 108; 117; 0].   (* [comment removed for export] *)
Definition FMT_F14 : list Z := [37; 48; 49; 57; 108; 117; 0].   (* [comment removed for export] *)
Definition FMT_F15 : list Z := [37; 42; 115; 37; 48; 52; 120; 32; 45; 32; 0].   (* [comment removed for export] *)
Definition FMT_F16 : list Z := [37; 48; 50; 120; 37; 99; 0].   (* [comment removed for export] *)
Definition FMT_F17 : list Z := [37; 115; 37; 115; 37; 115; 0].   (* [comment removed for export] *)
Definition FMT_F18 : list Z := [99; 97; 108; 108; 105; 110; 103; 32; 102; 111; 112; 101; 110; 40; 37; 115; 44; 32; 37; 115; 41; 0].   (* [comment removed for export] *)

Lemma pass1x_ok_F1 : pass1x_ok FMT_F1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F2 : pass1x_ok FMT_F2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F3 : pass1x_ok FMT_F3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F4 : pass1x_ok FMT_F4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F5 : pass1x_ok FMT_F5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F6 : pass1x_ok FMT_F6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F7 : pass1x_ok FMT_F7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F8 : pass1x_ok FMT_F8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F9 : pass1x_ok FMT_F9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F10 : pass1x_ok FMT_F10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F11 : pass1x_ok FMT_F11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F12 : pass1x_ok FMT_F12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F13 : pass1x_ok FMT_F13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F14 : pass1x_ok FMT_F14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F15 : pass1x_ok FMT_F15 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F16 : pass1x_ok FMT_F16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F17 : pass1x_ok FMT_F17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_F18 : pass1x_ok FMT_F18 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
(* [comment removed for export] *)
Ltac ppx_head := rewrite ppx_unfold;
  lazymatch goal with |- exists p, ?l = _ => let l' := eval cbv -[printf_piecesx_loop conv_piecesx app] in l in change l with l' end.
(* [comment removed for export] *)
Ltac ppx_convC C := ppx_head; cbv delta [T_LONG T_ULONG T_INT T_UINT T_PTR LEFT_ADJ ZERO_PAD] in C; rewrite C; clear C.
(* [comment removed for export] *)
Ltac ppx_lit :=
  match goal with |- context [printf_piecesx_loop (S ?f) ?L ?a ?c] =>
    let lit := eval vm_compute in (lit_run L) in
    let rest := eval vm_compute in (skipn (Datatypes.length lit) L) in
    change (printf_piecesx_loop (S f) L a c) with (printf_piecesx_loop (S f) (lit ++ rest) a c);
    rewrite (ppx_lit_cons f lit);
    [ let n := eval vm_compute in (zlength lit) in change (zlength lit) with n
    | discriminate
    | repeat (apply Forall_cons; [split; discriminate|]); apply Forall_nil
    | first [left; reflexivity | right; split; [reflexivity | cbn; discriminate]]
    | let n := eval vm_compute in (zlength lit) in change (zlength lit) with n; unfold INT_MAX; lia ]
  end.
(* [comment removed for export] *)
Ltac ppx_cnt c := match goal with |- context [printf_piecesx_loop _ _ _ ?e] => remember e as c end.

(* [comment removed for export] *)
Ltac ppx_begin F :=
  unfold printf_piecesx; let n := eval vm_compute in (Datatypes.length F) in change (Datatypes.length F) with n; unfold F.
Ltac ppx_end := rewrite ppx_nul; cbv beta iota; eexists; f_equal; f_equal; subst.
(* [comment removed for export] *)
Ltac ppx_dec_l c fl w v := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_dec_l c fl w v ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_dec_lu c fl w v := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_dec_lu c fl w v ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_dec_d c fl w v := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_dec_d c fl w v ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_dec_u c fl w v := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_dec_u c fl w v ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_hex c fl w v t := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_hex_u c fl w v t ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_s c fl w sv := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_s_w c fl w sv ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.
Ltac ppx_c c fl w v := let ps := fresh "ps" in let C := fresh "C" in
  destruct (convx_c c fl w v ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C); ppx_convC C.

Lemma printf_piecesx_F1 : forall ofs dp hl ln cp,
  0 <= ofs < 2^63 -> 0 <= dp < 2^31 -> 0 <= hl < 2^63 -> 0 <= ln < 2^63 -> zlength cp = 6 ->
  exists ps, printf_piecesx FMT_F1 [PA_z ofs; PA_i dp; PA_z hl; PA_z ln; PA_s cp] = Some (ps, hdr_len ofs dp hl ln false).
Proof.
  intros ofs dp hl ln cp Ho Hd Hh Hl Hc.
  pose proof (proj2 (proj2 (zdigits_eq ofs ltac:(lia)))) as D1. pose proof (proj2 (proj2 (zdigits_eq dp ltac:(lia)))) as D2.
  pose proof (proj2 (proj2 (zdigits_eq hl ltac:(lia)))) as D3. pose proof (proj2 (proj2 (zdigits_eq ln ltac:(lia)))) as D4.
  ppx_begin FMT_F1.
  (* [comment removed for export] *)
  destruct (convx_dec_l 0 0 5 ofs ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C1). ppx_convC C1. ppx_cnt c1.
  (* [comment removed for export] *)
  ppx_lit. ppx_cnt c2.
  (* [comment removed for export] *)
  destruct (convx_dec_d c2 LEFT_ADJ 2 dp ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps2 & C2). ppx_convC C2. ppx_cnt c3.
  (* [comment removed for export] *)
  ppx_lit. ppx_cnt c4.
  (* [comment removed for export] *)
  destruct (convx_dec_l c4 0 0 hl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps3 & C3). ppx_convC C3. ppx_cnt c5.
  (* [comment removed for export] *)
  ppx_lit. ppx_cnt c6.
  (* [comment removed for export] *)
  destruct (convx_dec_l c6 0 4 ln ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps4 & C4). ppx_convC C4. ppx_cnt c7.
  (* [comment removed for export] *)
  ppx_lit. ppx_cnt c8.
  (* [comment removed for export] *)
  destruct (convx_s_w c8 0 0 cp ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps5 & C5). ppx_convC C5. ppx_cnt c9.
  (* [comment removed for export] *)
  rewrite ppx_nul. cbv beta iota.
  eexists. f_equal. f_equal.
  subst c9 c8 c7 c6 c5 c4 c3 c2 c1.
  unfold hdr_len, hdr_pieces_len, zsum, padw, sdigits, sdec, zdigits. cbn [fold_right app].
  replace (ofs <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (dp <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (hl <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ln <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold zdigits in *. lia.
Qed.

Lemma printf_piecesx_F2 : forall ofs dp hl ln cp,
  0 <= ofs < 2^63 -> 0 <= dp < 2^31 -> 0 <= hl < 2^63 -> zlength cp = 6 ->
  exists ps, printf_piecesx FMT_F2 [PA_z ofs; PA_i dp; PA_z hl; PA_s cp] = Some (ps, hdr_len ofs dp hl ln true).
Proof.
  intros ofs dp hl ln cp Ho Hd Hh Hc.
  pose proof (proj2 (proj2 (zdigits_eq ofs ltac:(lia)))) as D1. pose proof (proj2 (proj2 (zdigits_eq dp ltac:(lia)))) as D2.
  pose proof (proj2 (proj2 (zdigits_eq hl ltac:(lia)))) as D3.
  ppx_begin FMT_F2.
  ppx_dec_l 0 0 5 ofs. ppx_cnt c1. ppx_lit. ppx_cnt c2. ppx_dec_d c2 LEFT_ADJ 2 dp. ppx_cnt c3. ppx_lit. ppx_cnt c4.
  ppx_dec_l c4 0 0 hl. ppx_cnt c5. ppx_lit. ppx_cnt c6. ppx_s c6 0 0 cp. ppx_cnt c7.
  ppx_end. unfold hdr_len, hdr_pieces_len, zsum, padw, sdigits, sdec, zdigits. cbn [fold_right app].
  replace (ofs <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (dp <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (hl <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold zdigits in *. lia.
Qed.

Lemma printf_piecesx_F3 : forall tag, 0 <= tag < 2^31 ->
  exists ps, printf_piecesx FMT_F3 [PA_i tag] = Some (ps, 10 + zdigits tag).
Proof.
  intros tag Ht. pose proof (proj2 (proj2 (zdigits_eq tag ltac:(lia)))) as D1.
  ppx_begin FMT_F3. ppx_lit. ppx_cnt c1. ppx_dec_d c1 0 0 tag. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.
Lemma printf_piecesx_F4 : forall tag, 0 <= tag < 2^31 ->
  exists ps, printf_piecesx FMT_F4 [PA_i tag] = Some (ps, 9 + zdigits tag).
Proof.
  intros tag Ht. pose proof (proj2 (proj2 (zdigits_eq tag ltac:(lia)))) as D1.
  ppx_begin FMT_F4. ppx_lit. ppx_cnt c1. ppx_dec_d c1 0 0 tag. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.
Lemma printf_piecesx_F5 : forall tag, 0 <= tag < 2^31 ->
  exists ps, printf_piecesx FMT_F5 [PA_i tag] = Some (ps, 9 + zdigits tag).
Proof.
  intros tag Ht. pose proof (proj2 (proj2 (zdigits_eq tag ltac:(lia)))) as D1.
  ppx_begin FMT_F5. ppx_lit. ppx_cnt c1. ppx_dec_d c1 0 0 tag. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.
Lemma printf_piecesx_F6 : forall tag, 0 <= tag < 2^31 ->
  exists ps, printf_piecesx FMT_F6 [PA_i tag] = Some (ps, 7 + zdigits tag).
Proof.
  intros tag Ht. pose proof (proj2 (proj2 (zdigits_eq tag ltac:(lia)))) as D1.
  ppx_begin FMT_F6. ppx_lit. ppx_cnt c1. ppx_dec_d c1 0 0 tag. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.

Lemma printf_piecesx_F7 : forall p, zlength p <= 255 ->
  exists ps, printf_piecesx FMT_F7 [PA_s p] = Some (ps, Z.max 18 (zlength p)).
Proof.
  intros p Hp. pose proof (zlength_nonneg'' p).
  ppx_begin FMT_F7. ppx_s 0 LEFT_ADJ 18 p. ppx_cnt c1. ppx_end. lia.
Qed.

(* [comment removed for export] *)
Lemma Forall_zrepeat : forall (P : Z -> Prop) c n, P c -> Forall P (zrepeat c n).
Proof. intros P c n H. unfold zrepeat. apply Forall_forall. intros x IN. apply repeat_spec in IN. subst. exact H. Qed.

Lemma pad_pieces_forall : forall (P : Z -> Prop) c w l fl pp, pad_pieces c w l fl = Some pp -> P c -> Forall P (concat pp).
Proof.
  intros P c w l fl pp H Hc. unfold pad_pieces in H.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - injection H as <-. constructor.
  - destruct (256 <=? w - l); [discriminate|]. injection H as <-. cbn [concat]. rewrite app_nil_r. apply Forall_zrepeat. exact Hc.
Qed.

Lemma tail_pieces_forall : forall (P : Z -> Prop) cnt fl w p prefix body ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> Forall P prefix -> Forall P body -> P 32 -> P 48 -> Forall P (concat ps).
Proof.
  intros P cnt fl w p prefix body ps r H HP HB H32 H48. unfold tail_pieces in H. cbv zeta in H.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:E1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:E2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:E3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:E4; [|discriminate].
  injection H as <- _.
  apply (proj2 (Forall_concat _ _)).
  repeat first [ apply Forall_nil | apply Forall_cons | apply (proj2 (Forall_app _ _ _)); split ].
  all: try assumption.
  all: apply (proj1 (Forall_concat _ _)); eapply pad_pieces_forall; eauto.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_forall_sp : forall (P : Z -> Prop) cnt fl w prefix body ps r,
  tail_pieces cnt fl w (zlength body) prefix body = Some (ps, r) -> Z.testbit fl 16 = false ->
  Forall P prefix -> Forall P body -> P 32 -> Forall P (concat ps).
Proof.
  intros P cnt fl w prefix body ps r H H16 HP HB H32. unfold tail_pieces in H. cbv zeta in H.
  rewrite Z.max_id in H.
  destruct (INT_MAX - zlength prefix <? zlength body); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + zlength body)); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:E1; [|discriminate].
  unfold pad_pieces at 1 2 in H. rewrite padtest_xzp, H16, Z.leb_refl, Bool.orb_true_r in H.
  change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true in H. cbn [negb orb] in H.
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:E4; [|discriminate].
  injection H as <- _.
  apply (proj2 (Forall_concat _ _)).
  repeat first [ apply Forall_nil | apply Forall_cons | apply (proj2 (Forall_app _ _ _)); split ].
  all: try assumption.
  all: apply (proj1 (Forall_concat _ _)); eapply pad_pieces_forall; eauto.
Qed.

Lemma testbit16_nozp : forall fl, Z.testbit (Z.land fl (Z.lnot ZERO_PAD)) 16 = false.
Proof. intros fl. rewrite Z.land_spec, Z.lnot_spec by lia. change (Z.testbit ZERO_PAD 16) with true. apply Bool.andb_false_r. Qed.

(* [comment removed for export] *)
Lemma convx_s_w_forall : forall cnt fl w s, fl_simple fl -> zlength s <= 255 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 255 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir fl w (-1) false 115 T_PTR) (PA_s s) = Some (ps, cnt + Z.max w (zlength s))
    /\ (forall P : Z -> Prop, Forall P s -> P 32 -> Forall P (concat ps)).
Proof.
  intros cnt fl w s Hfl Hs Hw Hc HI. destruct (fl_simple_bits fl Hfl) as (B & F0 & M & P & A & FL).
  destruct (fl_simple_bits _ (fl_simple_nozp fl Hfl)) as (B' & F0' & _).
  pose proof (zlength_nonneg'' s) as Hs0.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty]. rewrite FL. cbv zeta.
  change (negb (T_PTR =? T_PTR)) with false. cbv iota. change (-1 <? 0) with true.
  replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; unfold INT_MAX; lia). cbn [andb].
  rewrite firstn_all2 by (unfold zlength in *; lia).
  destruct (tail_pieces_gen cnt (Z.land fl (Z.lnot ZERO_PAD)) w (zlength s) s B' F0' ltac:(lia) ltac:(lia) Hw Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T).
  exists ps. split; [exact T|]. intros P0 HP H32. eapply tail_pieces_forall_sp; eauto using testbit16_nozp.
Qed.

(* [comment removed for export] *)
Lemma printf_piecesx_F7_forall : forall p, zlength p <= 255 ->
  exists ps, printf_piecesx FMT_F7 [PA_s p] = Some (ps, Z.max 18 (zlength p))
    /\ (forall P : Z -> Prop, Forall P p -> P 32 -> Forall P (concat ps)).
Proof.
  intros p Hp. pose proof (zlength_nonneg'' p).
  destruct (convx_s_w_forall 0 LEFT_ADJ 18 p ltac:(unfold fl_simple; auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & C & F).
  exists ([] :: ps ++ []). split.
  - ppx_begin FMT_F7. rewrite ppx_unfold.
    lazymatch goal with |- ?l = _ => let l' := eval cbv -[printf_piecesx_loop conv_piecesx app] in l in change l with l' end.
    cbv delta [T_LONG T_ULONG T_INT T_UINT T_PTR LEFT_ADJ ZERO_PAD] in C. rewrite C. rewrite ppx_nul. cbv beta iota. f_equal; f_equal; lia.
  - intros P HP H32. cbn [concat]. rewrite app_nil_r. apply F; auto.
Qed.

Lemma printf_piecesx_F7_nolf : forall p, Forall (fun c => c <> 10) p -> zlength p <= 255 ->
  exists ps, printf_piecesx FMT_F7 [PA_s p] = Some (ps, Z.max 18 (zlength p)) /\ Forall (fun c => c <> 10) (concat ps).
Proof.
  intros p HP Hp. destruct (printf_piecesx_F7_forall p Hp) as (ps & E & F). exists ps. split; [exact E|]. apply F; [exact HP | lia].
Qed.

Lemma printf_piecesx_F8 : exists ps, printf_piecesx FMT_F8 [PA_i 0; PA_s []] = Some (ps, 0).
Proof.
  pose proof (eq_refl : zlength (@nil Z) = 0) as Z0.
  ppx_begin FMT_F8. ppx_s 0 0 0 (@nil Z). ppx_cnt c1. ppx_end. lia.
Qed.

Lemma printf_piecesx_F9 : forall ln, 0 <= ln < 2^63 ->
  exists ps, printf_piecesx FMT_F9 [PA_z ln] = Some (ps, 24 + zdigits ln).
Proof.
  intros ln Hl. pose proof (proj2 (proj2 (zdigits_eq ln ltac:(lia)))) as D1.
  ppx_begin FMT_F9. ppx_lit. ppx_cnt c1. ppx_dec_l c1 0 0 ln. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.

Lemma printf_piecesx_F10 : forall b, 0 <= b < 2^32 ->
  exists ps, printf_piecesx FMT_F10 [PA_u b] = Some (ps, 1 + zdigits b).
Proof.
  intros b Hb. pose proof (proj2 (proj2 (zdigits_eq b ltac:(lia)))) as D1.
  ppx_begin FMT_F10. ppx_lit. ppx_cnt c1. ppx_dec_u c1 0 0 b. ppx_cnt c2. ppx_end. lia.
Qed.

Lemma xdigits_range : forall t u, 0 <= u -> 1 <= xdigits t u <= 16.
Proof.
  intros t u Hu. unfold xdigits. destruct (Z.eqb_spec u 0) as [->|NZ]; [lia|].
  pose proof (hex_digits_nz (Z.land t 32) u ltac:(lia)). pose proof (hex_digits_zlength (Z.land t 32) u). lia.
Qed.

Lemma printf_piecesx_F11 : forall b, 0 <= b < 2^32 ->
  exists ps, printf_piecesx FMT_F11 [PA_u b] = Some (ps, Z.max 2 (xdigits 88 b)).
Proof.
  intros b Hb. pose proof (xdigits_range 88 b ltac:(lia)) as D1.
  ppx_begin FMT_F11. ppx_hex 0 ZERO_PAD 2 b 88. ppx_cnt c1. ppx_end. lia.
Qed.

Lemma printf_piecesx_F12 : forall l, 0 <= l < 2^64 ->
  exists ps, printf_piecesx FMT_F12 [PA_z l] = Some (ps, dotlu_len l).
Proof.
  intros l Hl. pose proof (proj2 (proj2 (zdigits_eq l ltac:(lia)))) as D1.
  ppx_begin FMT_F12. ppx_lit. ppx_cnt c1. ppx_dec_lu c1 0 0 l. ppx_cnt c2. ppx_end. unfold dotlu_len. lia.
Qed.
Lemma printf_piecesx_F13 : forall w, 0 <= w < 2^64 ->
  exists ps, printf_piecesx FMT_F13 [PA_z w] = Some (ps, zdigits w).
Proof.
  intros w Hw. pose proof (proj2 (proj2 (zdigits_eq w ltac:(lia)))) as D1.
  ppx_begin FMT_F13. ppx_dec_lu 0 0 0 w. ppx_cnt c1. ppx_end. lia.
Qed.
Lemma printf_piecesx_F14 : forall w, 0 <= w < 2^64 ->
  exists ps, printf_piecesx FMT_F14 [PA_z w] = Some (ps, Z.max 19 (zdigits w)).
Proof.
  intros w Hw. pose proof (proj2 (proj2 (zdigits_eq w ltac:(lia)))) as D1.
  ppx_begin FMT_F14. ppx_dec_lu 0 ZERO_PAD 19 w. ppx_cnt c1. ppx_end. lia.
Qed.

Lemma printf_piecesx_F15 : forall r, 0 <= r < 2^32 ->
  exists ps, printf_piecesx FMT_F15 [PA_i 0; PA_s []; PA_u r] = Some (ps, Z.max 4 (xdigits 120 r) + 3).
Proof.
  intros r Hr. pose proof (xdigits_range 120 r ltac:(lia)) as D1.
  pose proof (eq_refl : zlength (@nil Z) = 0) as Z0.
  ppx_begin FMT_F15. ppx_s 0 0 0 (@nil Z). ppx_cnt c1.
  ppx_hex c1 ZERO_PAD 4 r 120. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_end. lia.
Qed.

Lemma printf_piecesx_F16 : forall ch sep, 0 <= ch < 2^32 ->
  exists ps, printf_piecesx FMT_F16 [PA_u ch; PA_i sep] = Some (ps, Z.max 2 (xdigits 120 ch) + 1).
Proof.
  intros ch sep Hc. pose proof (xdigits_range 120 ch ltac:(lia)) as D1.
  ppx_begin FMT_F16. ppx_hex 0 ZERO_PAD 2 ch 120. ppx_cnt c1. ppx_c c1 0 0 sep. ppx_cnt c2. ppx_end. lia.
Qed.

Lemma printf_piecesx_F17 : forall a b c, zlength a <= 255 -> zlength b <= 255 -> zlength c <= 255 ->
  exists ps, printf_piecesx FMT_F17 [PA_s a; PA_s b; PA_s c] = Some (ps, zlength a + zlength b + zlength c).
Proof.
  intros a b c Ha Hb Hc. pose proof (zlength_nonneg'' a). pose proof (zlength_nonneg'' b). pose proof (zlength_nonneg'' c).
  ppx_begin FMT_F17. ppx_s 0 0 0 a. ppx_cnt c1. ppx_s c1 0 0 b. ppx_cnt c2. ppx_s c2 0 0 c. ppx_cnt c3. ppx_end. lia.
Qed.

Lemma printf_piecesx_F18 : forall f md, zlength f <= 255 -> zlength md <= 255 ->
  exists ps, printf_piecesx FMT_F18 [PA_s f; PA_s md] = Some (ps, 17 + zlength f + zlength md).
Proof.
  intros f md Hf Hm. pose proof (zlength_nonneg'' f). pose proof (zlength_nonneg'' md).
  ppx_begin FMT_F18. ppx_lit. ppx_cnt c1. ppx_s c1 0 0 f. ppx_cnt c2. ppx_lit. ppx_cnt c3. ppx_s c3 0 0 md. ppx_cnt c4. ppx_lit. ppx_cnt c5.
  ppx_end. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbytes_forall : forall l, forallb (fun c => (0 <=? c) && (c <? 256)) l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. apply Forall_forall. intros x Hx. apply forallb_forall with (x := x) in H; [|exact Hx].
  apply andb_true_iff in H. destruct H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma fmt_bytes_F1 : Forall (fun c => 0 <= c < 256) FMT_F1. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F2 : Forall (fun c => 0 <= c < 256) FMT_F2. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F3 : Forall (fun c => 0 <= c < 256) FMT_F3. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F4 : Forall (fun c => 0 <= c < 256) FMT_F4. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F5 : Forall (fun c => 0 <= c < 256) FMT_F5. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F6 : Forall (fun c => 0 <= c < 256) FMT_F6. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F7 : Forall (fun c => 0 <= c < 256) FMT_F7. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F8 : Forall (fun c => 0 <= c < 256) FMT_F8. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F9 : Forall (fun c => 0 <= c < 256) FMT_F9. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F10 : Forall (fun c => 0 <= c < 256) FMT_F10. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F11 : Forall (fun c => 0 <= c < 256) FMT_F11. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F12 : Forall (fun c => 0 <= c < 256) FMT_F12. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F13 : Forall (fun c => 0 <= c < 256) FMT_F13. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F14 : Forall (fun c => 0 <= c < 256) FMT_F14. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F15 : Forall (fun c => 0 <= c < 256) FMT_F15. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F16 : Forall (fun c => 0 <= c < 256) FMT_F16. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F17 : Forall (fun c => 0 <= c < 256) FMT_F17. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_F18 : Forall (fun c => 0 <= c < 256) FMT_F18. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fp_callsx_zizzs : forall n f a b c d s, fp_callsx n f [PA_z a; PA_i b; PA_z c; PA_z d; PA_s s] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_zizs : forall n f a b c s, fp_callsx n f [PA_z a; PA_i b; PA_z c; PA_s s] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_i : forall n f i, fp_callsx n f [PA_i i] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_u : forall n f u, fp_callsx n f [PA_u u] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_z : forall n f z, fp_callsx n f [PA_z z] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_s1 : forall n f s, fp_callsx n f [PA_s s] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_is : forall n f i s, fp_callsx n f [PA_i i; PA_s s] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_isu : forall n f i s u, fp_callsx n f [PA_i i; PA_s s; PA_u u] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_ui : forall n f u i, fp_callsx n f [PA_u u; PA_i i] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_ss : forall n f a b, fp_callsx n f [PA_s a; PA_s b] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.
Lemma fp_callsx_sss : forall n f a b c, fp_callsx n f [PA_s a; PA_s b; PA_s c] = []. Proof. intros; apply fp_callsx_nog; repeat constructor. Qed.

(* [comment removed for export] *)
Lemma printf_piecesx_facts : forall fmt args n,
  (exists ps, printf_piecesx fmt args = Some (ps, n)) ->
  exists ps, printf_piecesx fmt args = Some (ps, n) /\ zlength (concat ps) = n.
Proof. intros fmt args n (ps & P). exists ps. split; [exact P | exact (printf_piecesx_count _ _ _ _ P)]. Qed.

(* [comment removed for export] *)
Lemma zdigits_range : forall v, 0 <= v < 2^64 -> 1 <= zdigits v <= 20.
Proof. intros v Hv. exact (proj2 (proj2 (zdigits_eq v Hv))). Qed.
Lemma zdigits_le10 : forall v, 0 <= v < 10000000000 -> zdigits v <= 10.
Proof.
  intros v Hv. unfold zdigits, zdec. destruct (Z.eqb_spec v 0); [unfold zlength; cbn; lia|].
  unfold dec_digits, zlength.
  do 10 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
  rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
    replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end.
Qed.
(* [comment removed for export] *)
Lemma hdr_len_range : forall ofs dp hl ln inf, 0 <= ofs < 2^32 -> 0 <= dp < 2^31 -> 0 <= hl < 2^32 -> 0 <= ln < 2^32 ->
  29 <= hdr_len ofs dp hl ln inf <= 57.
Proof.
  intros ofs dp hl ln inf Ho Hd Hh Hl.
  pose proof (zdigits_range ofs ltac:(lia)). pose proof (zdigits_range dp ltac:(lia)). pose proof (zdigits_range hl ltac:(lia)). pose proof (zdigits_range ln ltac:(lia)).
  pose proof (zdigits_le10 ofs ltac:(lia)). pose proof (zdigits_le10 dp ltac:(lia)). pose proof (zdigits_le10 hl ltac:(lia)). pose proof (zdigits_le10 ln ltac:(lia)).
  unfold hdr_len, hdr_pieces_len, zsum, padw, sdigits, sdec. 
  replace (ofs <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (dp <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (hl <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ln <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold zdigits in *. destruct inf; cbn [fold_right app]; lia.
Qed.
