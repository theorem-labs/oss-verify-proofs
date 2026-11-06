(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX PrintfFormats ApFmt.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zpad (w v : Z) : list Z := zrepeat 48 (w - zdigits v) ++ zdec v.
Definition spad (w v : Z) : list Z := zrepeat 32 (w - zdigits v) ++ zdec v.
(* [comment removed for export] *)
Definition hexU (i : Z) : Z := znth XDIGITS i.
Definition hex2 (b : Z) : list Z := [hexU (b / 16); hexU (b mod 16)].

Lemma zrepeat_nonpos : forall c n, n <= 0 -> zrepeat c n = [].
Proof. intros c n H. unfold zrepeat. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.
Lemma zlength_zrepeat' : forall c n, zlength (zrepeat c n) = Z.max 0 n.
Proof.
  intros c n. destruct (Z.le_gt_cases n 0).
  - rewrite zrepeat_nonpos by lia. change (zlength (@nil Z)) with 0. lia.
  - rewrite zlength_zrepeat by lia. lia.
Qed.
Lemma zlength_zpad : forall w v, 0 <= v < 2^64 -> zlength (zpad w v) = Z.max w (zdigits v).
Proof. intros w v Hv. unfold zpad. rewrite zlength_app', zlength_zrepeat'. pose proof (zdigits_eq v Hv). unfold zdigits in *. lia. Qed.
Lemma zlength_spad : forall w v, 0 <= v < 2^64 -> zlength (spad w v) = Z.max w (zdigits v).
Proof. intros w v Hv. unfold spad. rewrite zlength_app', zlength_zrepeat'. pose proof (zdigits_eq v Hv). unfold zdigits in *. lia. Qed.

(* [comment removed for export] *)
Lemma zdec_split : forall v, 0 <= v < 2^64 -> zrepeat 48 (zdigits v - zlength (dec_digits v)) ++ dec_digits v = zdec v.
Proof.
  intros v Hv. unfold zdigits, zdec. destruct (Z.eqb_spec v 0) as [->|NZ].
  - rewrite dec_digits_0. reflexivity.
  - rewrite Z.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_exact0 : forall cnt w p body,
  zlength body <= p -> p - zlength body < 256 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w p <= INT_MAX -> p <= INT_MAX ->
  exists ps, tail_pieces cnt 0 w p [] body = Some (ps, cnt + Z.max w p)
    /\ concat ps = zrepeat 32 (w - p) ++ zrepeat 48 (p - zlength body) ++ body.
Proof.
  intros cnt w p body Hb Hp Hw Hc HI HP. pose proof (zlength_nonneg'' body) as B0.
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  replace (Z.max p (zlength body)) with p by lia.
  replace (INT_MAX - 0 <? p) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (INT_MAX - cnt <? Z.max w (0 + p)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.add_0_l. unfold pad_pieces.
  change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true.
  change (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false.
  change (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false. cbn [negb orb].
  destruct (Z.leb_spec (Z.max w p) p) as [W1|W1]; destruct (Z.leb_spec p (zlength body)) as [P1|P1];
    repeat (replace (256 <=? Z.max w p - p) with false by (symmetry; apply Z.leb_gt; lia));
    repeat (replace (256 <=? p - zlength body) with false by (symmetry; apply Z.leb_gt; lia));
    eexists; (split; [reflexivity|]); cbn [concat app]; rewrite ?app_nil_r;
    try rewrite (zrepeat_nonpos 32 (w - p)) by lia; try rewrite (zrepeat_nonpos 48 (p - zlength body)) by lia;
    try replace (Z.max w p - p) with (w - p) by lia; cbn [app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_pieces_exactZ : forall cnt w p body,
  zlength body <= p -> p - zlength body < 256 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w p <= INT_MAX -> p <= INT_MAX ->
  exists ps, tail_pieces cnt ZERO_PAD w p [] body = Some (ps, cnt + Z.max w p)
    /\ concat ps = zrepeat 48 (w - p) ++ zrepeat 48 (p - zlength body) ++ body.
Proof.
  intros cnt w p body Hb Hp Hw Hc HI HP. pose proof (zlength_nonneg'' body) as B0.
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  replace (Z.max p (zlength body)) with p by lia.
  replace (INT_MAX - 0 <? p) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (INT_MAX - cnt <? Z.max w (0 + p)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.add_0_l. unfold pad_pieces.
  change (Z.land ZERO_PAD (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false.
  change (Z.land (Z.lxor ZERO_PAD ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true.
  change (Z.land (Z.lxor ZERO_PAD LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false.
  change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with true. cbn [negb orb].
  destruct (Z.leb_spec (Z.max w p) p) as [W1|W1]; destruct (Z.leb_spec p (zlength body)) as [P1|P1];
    repeat (replace (256 <=? Z.max w p - p) with false by (symmetry; apply Z.leb_gt; lia));
    repeat (replace (256 <=? p - zlength body) with false by (symmetry; apply Z.leb_gt; lia));
    eexists; (split; [reflexivity|]); cbn [concat app]; rewrite ?app_nil_r;
    try rewrite (zrepeat_nonpos 48 (w - p)) by lia; try rewrite (zrepeat_nonpos 48 (p - zlength body)) by lia;
    try replace (Z.max w p - p) with (w - p) by lia; cbn [app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma convx_zpad_d : forall cnt w v, 0 <= v < 2^31 -> 1 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir ZERO_PAD w (-1) false 100 T_INT) (PA_i v) = Some (ps, cnt + Z.max w (zdigits v))
    /\ concat ps = zpad w v.
Proof.
  intros cnt w v Hv Hw Hc HI.
  pose proof (zdigits_eq v ltac:(lia)) as (E1 & E2 & E3). pose proof (dec_digits_zlength v) as DL.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land ZERO_PAD LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_INT =? T_INT)) with false. change (100 =? 99) with false. cbv iota.
  rewrite (Z.mod_small v (2^64)) by lia.
  replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
  change (Z.land ZERO_PAD MARK_POS =? 0) with true. change (Z.land ZERO_PAD PAD_POS =? 0) with true. cbn [negb]. cbv iota.
  unfold int_pieces. cbn [andb]. change (-1 =? 0) with false. rewrite Bool.andb_false_r. rewrite E1.
  destruct (tail_pieces_exactZ cnt w (zdigits v) (dec_digits v) ltac:(lia) ltac:(lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
  exists ps. split; [exact T|]. rewrite C. unfold zpad. rewrite <- (zdec_split v) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma convx_spad_d : forall cnt w v, 0 <= v < 2^31 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir 0 w (-1) false 100 T_INT) (PA_i v) = Some (ps, cnt + Z.max w (zdigits v))
    /\ concat ps = spad w v.
Proof.
  intros cnt w v Hv Hw Hc HI.
  pose proof (zdigits_eq v ltac:(lia)) as (E1 & E2 & E3). pose proof (dec_digits_zlength v) as DL.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_INT =? T_INT)) with false. change (100 =? 99) with false. cbv iota.
  rewrite (Z.mod_small v (2^64)) by lia.
  replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
  change (Z.land 0 MARK_POS =? 0) with true. change (Z.land 0 PAD_POS =? 0) with true. cbn [negb]. cbv iota.
  unfold int_pieces. cbn [andb]. change (-1 =? 0) with false. rewrite Bool.andb_false_r. rewrite E1.
  destruct (tail_pieces_exact0 cnt w (zdigits v) (dec_digits v) ltac:(lia) ltac:(lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
  exists ps. split; [exact T|]. rewrite C. unfold spad. rewrite <- (zdec_split v) by lia. reflexivity.
Qed.
Lemma convx_d : forall cnt v, 0 <= v < 2^31 -> 0 <= cnt -> cnt + 21 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i v) = Some (ps, cnt + zdigits v) /\ concat ps = zdec v.
Proof.
  intros cnt v Hv Hc HI. pose proof (zdigits_eq v ltac:(lia)) as (_ & _ & E3).
  destruct (convx_spad_d cnt 0 v Hv ltac:(lia) Hc ltac:(lia)) as (ps & T & C).
  exists ps. split; [rewrite T; f_equal; f_equal; lia|]. rewrite C. unfold spad. rewrite zrepeat_nonpos by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hex_digits_byte : forall b, 0 <= b < 256 ->
  hex_digits 0 b = (if b =? 0 then [] else if b <? 16 then [hexU b] else hex2 b).
Proof.
  intros b Hb. unfold hex_digits, hex2, hexU.
  change 16%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S 0)))))))))))))))).
  cbn [digits_aux]. destruct (Z.eqb_spec b 0) as [->|NZ]; [reflexivity|].
  destruct (Z.ltb_spec b 16) as [LT|GE].
  - rewrite (Z.div_small b 16) by lia. cbn [Z.eqb]. rewrite (Z.mod_small b 16) by lia. rewrite Z.lor_0_r. reflexivity.
  - destruct (Z.eqb_spec (b / 16) 0) as [E|NE]; [exfalso; Z.div_mod_to_equations; lia|].
    replace (b / 16 / 16) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb].
    rewrite (Z.mod_small (b / 16) 16) by (Z.div_mod_to_equations; lia). rewrite !Z.lor_0_r. reflexivity.
Qed.
Lemma convx_hex2 : forall cnt b, 0 <= b < 256 -> 0 <= cnt -> cnt + 17 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir ZERO_PAD 2 (-1) false 88 T_UINT) (PA_u b) = Some (ps, cnt + 2) /\ concat ps = hex2 b.
Proof.
  intros cnt b Hb Hc HI.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land ZERO_PAD LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_UINT =? T_UINT)) with false. change (88 =? 117) with false. change (88 =? 120) with false.
  change (Z.land ZERO_PAD ALT_FORM =? 0) with true. cbn [negb andb]. rewrite Bool.andb_false_r. cbv iota.
  change (Z.land 88 32) with 0. rewrite (hex_digits_byte b Hb).
  unfold int_pieces. cbn [andb]. change (-1 =? 0) with false. rewrite Bool.andb_false_r.
  destruct (Z.eqb_spec b 0) as [->|NZ].
  - change (Z.max (-1) (zlength (@nil Z) + 1)) with 1.
    destruct (tail_pieces_exactZ cnt 2 1 [] ltac:(change (zlength (@nil Z)) with 0; lia) ltac:(change (zlength (@nil Z)) with 0; lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
    exists ps. split; [exact T|]. rewrite C. reflexivity.
  - destruct (Z.ltb_spec b 16) as [LT|GE].
    + change (Z.max (-1) (zlength [hexU b] + 0)) with 1.
      destruct (tail_pieces_exactZ cnt 2 1 [hexU b] ltac:(change (zlength [hexU b]) with 1; lia) ltac:(change (zlength [hexU b]) with 1; lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
      exists ps. split; [exact T|]. rewrite C. unfold hex2. rewrite (Z.div_small b 16), (Z.mod_small b 16) by lia. reflexivity.
    + unfold hex2. change (Z.max (-1) (zlength [hexU (b / 16); hexU (b mod 16)] + 0)) with 2.
      destruct (tail_pieces_exactZ cnt 2 2 [hexU (b / 16); hexU (b mod 16)] ltac:(change (zlength [hexU (b / 16); hexU (b mod 16)]) with 2; lia)
                  ltac:(change (zlength [hexU (b / 16); hexU (b mod 16)]) with 2; lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
      exists ps. split; [exact T|]. rewrite C. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma convx_s_prec : forall cnt w p s, 0 <= p <= INT_MAX -> zlength s <= 255 \/ p <= 255 -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 255 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir 0 w p true 115 T_PTR) (PA_s s) = Some (ps, cnt + Z.max w (Z.min (zlength s) p))
    /\ concat ps = zrepeat 32 (w - Z.min (zlength s) p) ++ firstn (Z.to_nat p) s.
Proof.
  intros cnt w p s Hp Hs Hw Hc HI. pose proof (zlength_nonneg'' s) as S0.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_PTR =? T_PTR)) with false. cbv iota.
  replace (p <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  change (Z.land 0 (Z.lnot ZERO_PAD)) with 0.
  assert (LF : zlength (firstn (Z.to_nat (Z.min (zlength s) p)) s) = Z.min (zlength s) p).
  { unfold zlength in *. rewrite length_firstn. lia. }
  destruct (tail_pieces_exact0 cnt w (Z.min (zlength s) p) (firstn (Z.to_nat (Z.min (zlength s) p)) s)
              ltac:(lia) ltac:(lia) Hw Hc ltac:(lia) ltac:(lia)) as (ps & T & C).
  exists ps. split; [exact T|]. rewrite C, LF, Z.sub_diag. cbn [zrepeat Z.to_nat repeat app].
  f_equal. destruct (Z.le_gt_cases (zlength s) p).
  - rewrite Z.min_l by lia. rewrite !firstn_all2 by (unfold zlength in *; lia). reflexivity.
  - rewrite Z.min_r by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma convx_sn_prec : forall cnt w p, 6 <= p <= INT_MAX -> 0 <= w <= 255 -> 0 <= cnt -> cnt + Z.max w 255 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir 0 w p true 115 T_PTR) PA_sn = Some (ps, cnt + Z.max w 6) /\ concat ps = zrepeat 32 (w - 6) ++ NULLSTR.
Proof.
  intros cnt w p Hp Hw Hc HI.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_PTR =? T_PTR)) with false. cbv iota.
  replace (p <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  change (Z.land 0 (Z.lnot ZERO_PAD)) with 0. change (zlength NULLSTR) with 6. rewrite Z.min_l by lia.
  change (firstn (Z.to_nat 6) NULLSTR) with NULLSTR.
  destruct (tail_pieces_exact0 cnt w 6 NULLSTR ltac:(change (zlength NULLSTR) with 6; lia) ltac:(change (zlength NULLSTR) with 6; lia) Hw Hc ltac:(lia) ltac:(lia)) as (ps & T & C).
  exists ps. split; [exact T|]. rewrite C. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma convx_s0 : forall cnt s, zlength s <= 255 -> 0 <= cnt -> cnt + 255 <= INT_MAX ->
  exists ps, conv_piecesx cnt (mkDir 0 0 (-1) false 115 T_PTR) (PA_s s) = Some (ps, cnt + zlength s) /\ concat ps = s.
Proof.
  intros cnt s Hs Hc HI. pose proof (zlength_nonneg'' s) as S0.
  unfold conv_piecesx. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. cbv zeta.
  change (negb (T_PTR =? T_PTR)) with false. cbv iota. change (-1 <? 0) with true.
  replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; unfold INT_MAX; lia). cbn [andb].
  change (Z.land 0 (Z.lnot ZERO_PAD)) with 0. rewrite firstn_all2 by (unfold zlength in *; lia).
  destruct (tail_pieces_exact0 cnt 0 (zlength s) s ltac:(lia) ltac:(lia) ltac:(lia) Hc ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps & T & C).
  exists ps. split; [rewrite T; f_equal; f_equal; lia|]. rewrite C, Z.sub_diag, zrepeat_nonpos by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT_C1 : list Z := [37; 42; 115; 83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58; 0].   (* [comment removed for export] *)
Definition FMT_C2 : list Z := [10; 37; 42; 115; 86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32; 0].   (* [comment removed for export] *)
Definition FMT_C3 : list Z := [117; 110; 107; 110; 111; 119; 110; 10; 37; 42; 115; 0].   (* [comment removed for export] *)
Definition FMT_C4 : list Z := [118; 49; 32; 40; 48; 120; 48; 41; 0].   (* [comment removed for export] *)
Definition FMT_C5 : list Z := [10; 37; 42; 115; 76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32; 0].   (* [comment removed for export] *)
Definition FMT_C6 : list Z := [10; 37; 42; 115; 84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32; 0].   (* [comment removed for export] *)
Definition FMT_C7 : list Z := [10; 37; 42; 115; 69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32; 0].   (* [comment removed for export] *)
Definition FMT_C8 : list Z := [110; 111; 110; 101; 0].   (* [comment removed for export] *)
Definition FMT_C9 : list Z := [10; 37; 42; 115; 83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32; 0].   (* [comment removed for export] *)
Definition FMT_C10 : list Z := [37; 115; 0].   (* [comment removed for export] *)
Definition FMT_C11 : list Z := [10; 37; 42; 115; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 0].   (* [comment removed for export] *)
Definition FMT_C12 : list Z := [37; 42; 115; 0].   (* [comment removed for export] *)
Definition FMT_C13 : list Z := [37; 48; 50; 88; 58; 0].   (* [comment removed for export] *)
Definition FMT_C14 : list Z := [10; 0].   (* [comment removed for export] *)
Definition FMT_C15 : list Z := [37; 48; 50; 88; 0].   (* [comment removed for export] *)
Definition FMT_C16 : list Z := [37; 115; 32; 37; 50; 100; 32; 37; 48; 50; 100; 58; 37; 48; 50; 100; 58; 37; 48; 50; 100; 46; 37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].   (* [comment removed for export] *)
Definition FMT_C17 : list Z := [37; 48; 52; 100; 37; 48; 50; 100; 37; 48; 50; 100; 37; 48; 50; 100; 37; 48; 50; 100; 37; 48; 50; 100; 90; 0].   (* [comment removed for export] *)
Definition FMT_C18 : list Z := [37; 46; 49; 52; 115; 46; 37; 48; 51; 100; 90; 0].   (* [comment removed for export] *)

Lemma pass1x_ok_C1 : pass1x_ok FMT_C1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C2 : pass1x_ok FMT_C2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C3 : pass1x_ok FMT_C3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C4 : pass1x_ok FMT_C4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C5 : pass1x_ok FMT_C5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C6 : pass1x_ok FMT_C6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C7 : pass1x_ok FMT_C7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C8 : pass1x_ok FMT_C8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C9 : pass1x_ok FMT_C9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C10 : pass1x_ok FMT_C10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C11 : pass1x_ok FMT_C11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C12 : pass1x_ok FMT_C12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C13 : pass1x_ok FMT_C13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C14 : pass1x_ok FMT_C14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C15 : pass1x_ok FMT_C15 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C16 : pass1x_ok FMT_C16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C17 : pass1x_ok FMT_C17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1x_ok_C18 : pass1x_ok FMT_C18 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C1 : Forall (fun c => 0 <= c < 256) FMT_C1. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C2 : Forall (fun c => 0 <= c < 256) FMT_C2. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C3 : Forall (fun c => 0 <= c < 256) FMT_C3. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C4 : Forall (fun c => 0 <= c < 256) FMT_C4. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C5 : Forall (fun c => 0 <= c < 256) FMT_C5. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C6 : Forall (fun c => 0 <= c < 256) FMT_C6. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C7 : Forall (fun c => 0 <= c < 256) FMT_C7. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C8 : Forall (fun c => 0 <= c < 256) FMT_C8. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C9 : Forall (fun c => 0 <= c < 256) FMT_C9. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C10 : Forall (fun c => 0 <= c < 256) FMT_C10. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C11 : Forall (fun c => 0 <= c < 256) FMT_C11. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C12 : Forall (fun c => 0 <= c < 256) FMT_C12. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C13 : Forall (fun c => 0 <= c < 256) FMT_C13. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C14 : Forall (fun c => 0 <= c < 256) FMT_C14. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C15 : Forall (fun c => 0 <= c < 256) FMT_C15. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C16 : Forall (fun c => 0 <= c < 256) FMT_C16. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C17 : Forall (fun c => 0 <= c < 256) FMT_C17. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
Lemma fmt_bytes_C18 : Forall (fun c => 0 <= c < 256) FMT_C18. Proof. apply zbytes_forall. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fp_callsx_is0 : forall fmt i n, fp_callsx n fmt [PA_i i; PA_s []] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_nil : forall fmt n, fp_callsx n fmt [] = [].
Proof. intros. apply fp_callsx_nog. constructor. Qed.
Lemma fp_callsx_u : forall fmt u n, fp_callsx n fmt [PA_u u] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_si : forall fmt s i n, fp_callsx n fmt [PA_s s; PA_i i] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_sni : forall fmt i n, fp_callsx n fmt [PA_sn; PA_i i] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_i6 : forall fmt a b c d e f n, fp_callsx n fmt [PA_i a; PA_i b; PA_i c; PA_i d; PA_i e; PA_i f] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.
Lemma fp_callsx_C16 : forall fmt mon a b c d p f y n, fp_callsx n fmt [PA_s mon; PA_i a; PA_i b; PA_i c; PA_i d; PA_i p; PA_s f; PA_i y] = [].
Proof. intros. apply fp_callsx_nog. repeat constructor. Qed.

(* [comment removed for export] *)
Lemma arg_covs_C18 : forall g ms, arg_covs (length FMT_C18) FMT_C18 [PA_s g; PA_i ms] = [Some 14; None].
Proof. intros. reflexivity. Qed.
Lemma arg_covs_C18_null : forall ms, arg_covs (length FMT_C18) FMT_C18 [PA_sn; PA_i ms] = [Some 14; None].
Proof. intros. reflexivity. Qed.
Lemma arg_covs_C16 : forall mon a b c d f y,
  arg_covs (length FMT_C16) FMT_C16 [PA_s mon; PA_i a; PA_i b; PA_i c; PA_i d; PA_i 3; PA_s f; PA_i y] = [None; None; None; None; None; None; Some 3; None].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ppx_lit2 lit rest :=
  match goal with |- context [printf_piecesx_loop (S ?f) ?L ?a ?c] =>
    change (printf_piecesx_loop (S f) L a c) with (printf_piecesx_loop (S f) (lit ++ rest) a c);
    rewrite (ppx_lit_cons f lit);
    [ | discriminate
    | repeat (apply Forall_cons; [split; discriminate|]); apply Forall_nil
    | first [left; reflexivity | right; split; [reflexivity | cbn; discriminate]]
    | let n := eval vm_compute in (zlength lit) in change (zlength lit) with n; unfold INT_MAX; lia ]
  end.
(* [comment removed for export] *)
Lemma printf_piecesx_C1 : printf_piecesx FMT_C1 [PA_i 4; PA_s []]
  = Some ([[]; [32; 32; 32; 32]; []; []; [83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58]], 33).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C2 : printf_piecesx FMT_C2 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; [86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32]], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C3 : printf_piecesx FMT_C3 [PA_i 20; PA_s []]
  = Some ([[117; 110; 107; 110; 111; 119; 110; 10]; []; zrepeat 32 20; []; []], 28).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C4 : printf_piecesx FMT_C4 [] = Some ([[118; 49; 32; 40; 48; 120; 48; 41]], 8).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C5 : printf_piecesx FMT_C5 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; [76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32]], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C6 : printf_piecesx FMT_C6 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; [84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32]], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C7 : printf_piecesx FMT_C7 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; [69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32]], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C8 : printf_piecesx FMT_C8 [] = Some ([[110; 111; 110; 101]], 4).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C9 : printf_piecesx FMT_C9 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; [83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32]], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C11 : printf_piecesx FMT_C11 [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; zrepeat 32 12], 21).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C12 : printf_piecesx FMT_C12 [PA_i 20; PA_s []] = Some ([[]; zrepeat 32 20; []; []], 20).
Proof. vm_compute. reflexivity. Qed.
Lemma printf_piecesx_C14 : printf_piecesx FMT_C14 [] = Some ([[10]], 1).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma printf_piecesx_C10 : forall s, zlength s <= 255 ->
  exists ps, printf_piecesx FMT_C10 [PA_s s] = Some (ps, zlength s) /\ concat ps = s.
Proof.
  intros s Hs. pose proof (zlength_nonneg'' s) as S0.
  destruct (convx_s0 0 s Hs ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C & CC).
  unfold printf_piecesx. change (Datatypes.length FMT_C10) with 3%nat. unfold FMT_C10.
  rewrite (ppx_dir 2 [115; 0] [PA_s s] 0 (mkDir 0 0 (-1) false 115 T_PTR) nostars [0] (mkDir 0 0 (-1) false 115 T_PTR) (PA_s s) [] ps1 (0 + zlength s));
    [| cbn; lia | reflexivity | reflexivity | exact C].
  rewrite ppx_nul. eexists. split; [reflexivity|]. cbn [concat app]. rewrite app_nil_r. exact CC.
Qed.

(* [comment removed for export] *)
Lemma printf_piecesx_C13 : forall b, 0 <= b < 256 ->
  exists ps, printf_piecesx FMT_C13 [PA_u b] = Some (ps, 3) /\ concat ps = hex2 b ++ [58].
Proof.
  intros b Hb.
  destruct (convx_hex2 0 b Hb ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C & CC).
  unfold printf_piecesx. change (Datatypes.length FMT_C13) with 6%nat. unfold FMT_C13.
  rewrite (ppx_dir 5 [48; 50; 88; 58; 0] [PA_u b] 0 (mkDir ZERO_PAD 2 (-1) false 88 T_UINT) nostars [58; 0] (mkDir ZERO_PAD 2 (-1) false 88 T_UINT) (PA_u b) [] ps1 (0 + 2));
    [| cbn; lia | reflexivity | reflexivity | exact C].
  ppx_lit2 [58] [0]. rewrite ppx_nul. eexists. split; [reflexivity|].
  cbn [concat app]. rewrite concat_app, CC. cbn [concat app]. rewrite ?app_nil_r. reflexivity.
Qed.
Lemma printf_piecesx_C15 : forall b, 0 <= b < 256 ->
  exists ps, printf_piecesx FMT_C15 [PA_u b] = Some (ps, 2) /\ concat ps = hex2 b.
Proof.
  intros b Hb.
  destruct (convx_hex2 0 b Hb ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C & CC).
  unfold printf_piecesx. change (Datatypes.length FMT_C15) with 5%nat. unfold FMT_C15.
  rewrite (ppx_dir 4 [48; 50; 88; 0] [PA_u b] 0 (mkDir ZERO_PAD 2 (-1) false 88 T_UINT) nostars [0] (mkDir ZERO_PAD 2 (-1) false 88 T_UINT) (PA_u b) [] ps1 (0 + 2));
    [| cbn; lia | reflexivity | reflexivity | exact C].
  rewrite ppx_nul. eexists. split; [reflexivity|]. cbn [concat app]. rewrite app_nil_r. exact CC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ppx_dir2 C detac :=
  match goal with |- context [printf_piecesx_loop (S ?f) (37 :: ?s2) ?args ?c] =>
    let pd := eval vm_compute in (parse_dirx s2) in
    lazymatch pd with Some (?d0, ?st, ?s3) =>
      erewrite (ppx_dir f s2 args c d0 st s3);
      [ | cbn; lia | vm_compute; reflexivity | detac | exact C ]
    end end.
(* [comment removed for export] *)
Ltac zlen_lits := repeat match goal with |- context [zlength (?a :: ?l)] =>
  let n := eval vm_compute in (zlength (a :: l)) in change (zlength (a :: l)) with n end.
Ltac ppx_finish :=
  rewrite ppx_nul; eexists; split; [f_equal; f_equal; lia|];
  cbn [concat]; repeat (rewrite concat_app; cbn [concat]); rewrite ?app_nil_r.

Lemma zdigits_le2 : forall v, 0 <= v < 100 -> zdigits v <= 2.
Proof.
  intros v Hv. unfold zdigits, zdec. destruct (Z.eqb_spec v 0); [unfold zlength; cbn; lia|].
  unfold dec_digits, zlength.
  do 2 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
  rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
    replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end.
Qed.
Lemma zdigits_le4 : forall v, 0 <= v < 10000 -> zdigits v <= 4.
Proof.
  intros v Hv. unfold zdigits, zdec. destruct (Z.eqb_spec v 0); [unfold zlength; cbn; lia|].
  unfold dec_digits, zlength.
  do 4 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
  rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
    replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end.
Qed.

(* [comment removed for export] *)
Lemma printf_piecesx_C16 : forall mon mday hour min sec f year,
  zlength mon = 3 -> 1 <= mday <= 31 -> 0 <= hour < 100 -> 0 <= min < 100 -> 0 <= sec < 100 -> 3 <= zlength f <= 255 -> 0 <= year <= 9999 ->
  exists ps, printf_piecesx FMT_C16 [PA_s mon; PA_i mday; PA_i hour; PA_i min; PA_i sec; PA_i 3; PA_s f; PA_i year] = Some (ps, 24 + zdigits year).
Proof.
  intros mon mday hour min sec f year Hmon Hmd Hh Hmi Hs Hf Hy.
  pose proof (zdigits_le2 mday ltac:(lia)) as D1. pose proof (zdigits_le2 hour ltac:(lia)) as D2. pose proof (zdigits_le2 min ltac:(lia)) as D3.
  pose proof (zdigits_le2 sec ltac:(lia)) as D4. pose proof (zdigits_le4 year ltac:(lia)) as D5.
  pose proof (zdigits_range mday ltac:(lia)) as R1. pose proof (zdigits_range hour ltac:(lia)) as R2. pose proof (zdigits_range min ltac:(lia)) as R3.
  pose proof (zdigits_range sec ltac:(lia)) as R4. pose proof (zdigits_range year ltac:(lia)) as R5.
  unfold printf_piecesx. change (Datatypes.length FMT_C16) with 34%nat. unfold FMT_C16.
  destruct (convx_s0 0 mon ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C1 & _). ppx_dir2 C1 reflexivity. clear C1.
  rewrite Hmon. ppx_lit2 [32] [37; 50; 100; 32; 37; 48; 50; 100; 58; 37; 48; 50; 100; 58; 37; 48; 50; 100; 46; 37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c2.
  destruct (convx_spad_d c2 2 mday ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps2 & C2 & _). ppx_dir2 C2 reflexivity. clear C2.
  ppx_lit2 [32] [37; 48; 50; 100; 58; 37; 48; 50; 100; 58; 37; 48; 50; 100; 46; 37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c3.
  destruct (convx_zpad_d c3 2 hour ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps3 & C3 & _). ppx_dir2 C3 reflexivity. clear C3.
  ppx_lit2 [58] [37; 48; 50; 100; 58; 37; 48; 50; 100; 46; 37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c4.
  destruct (convx_zpad_d c4 2 min ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps4 & C4 & _). ppx_dir2 C4 reflexivity. clear C4.
  ppx_lit2 [58] [37; 48; 50; 100; 46; 37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c5.
  destruct (convx_zpad_d c5 2 sec ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps5 & C5 & _). ppx_dir2 C5 reflexivity. clear C5.
  ppx_lit2 [46] [37; 46; 42; 115; 32; 37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c6.
  destruct (convx_s_prec c6 0 3 f ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps6 & C6 & _).
  rewrite (Z.min_r (zlength f) 3) in C6 by lia. ppx_dir2 C6 reflexivity. clear C6.
  ppx_lit2 [32] [37; 100; 32; 71; 77; 84; 0].
  zlen_lits. ppx_cnt c7.
  destruct (convx_d c7 year ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps7 & C7 & _). ppx_dir2 C7 reflexivity. clear C7.
  ppx_lit2 [32; 71; 77; 84] [0].
  zlen_lits. rewrite ppx_nul. eexists. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ct_gentime (y mo d h mi s : Z) : list Z := zpad 4 y ++ zpad 2 mo ++ zpad 2 d ++ zpad 2 h ++ zpad 2 mi ++ zpad 2 s ++ [90].
Lemma zlength_ct_gentime : forall y mo d h mi s, 0 <= y <= 9999 -> 0 <= mo < 100 -> 0 <= d < 100 -> 0 <= h < 100 -> 0 <= mi < 100 -> 0 <= s < 100 ->
  zlength (ct_gentime y mo d h mi s) = 15.
Proof.
  intros y mo d h mi s Hy Hmo Hd Hh Hmi Hs. unfold ct_gentime.
  pose proof (zdigits_le4 y ltac:(lia)). pose proof (zdigits_le2 mo ltac:(lia)). pose proof (zdigits_le2 d ltac:(lia)).
  pose proof (zdigits_le2 h ltac:(lia)). pose proof (zdigits_le2 mi ltac:(lia)). pose proof (zdigits_le2 s ltac:(lia)).
  rewrite !zlength_app', !zlength_zpad by lia. change (zlength [90]) with 1. lia.
Qed.
Lemma printf_piecesx_C17 : forall y mo d h mi s,
  0 <= y <= 9999 -> 0 <= mo < 100 -> 0 <= d < 100 -> 0 <= h < 100 -> 0 <= mi < 100 -> 0 <= s < 100 ->
  exists ps, printf_piecesx FMT_C17 [PA_i y; PA_i mo; PA_i d; PA_i h; PA_i mi; PA_i s] = Some (ps, 15)
    /\ concat ps = ct_gentime y mo d h mi s.
Proof.
  intros y mo d h mi s Hy Hmo Hd Hh Hmi Hs.
  pose proof (zdigits_le4 y ltac:(lia)) as D1. pose proof (zdigits_le2 mo ltac:(lia)) as D2. pose proof (zdigits_le2 d ltac:(lia)) as D3.
  pose proof (zdigits_le2 h ltac:(lia)) as D4. pose proof (zdigits_le2 mi ltac:(lia)) as D5. pose proof (zdigits_le2 s ltac:(lia)) as D6.
  pose proof (zdigits_range y ltac:(lia)) as R1. pose proof (zdigits_range mo ltac:(lia)) as R2. pose proof (zdigits_range d ltac:(lia)) as R3.
  pose proof (zdigits_range h ltac:(lia)) as R4. pose proof (zdigits_range mi ltac:(lia)) as R5. pose proof (zdigits_range s ltac:(lia)) as R6.
  unfold printf_piecesx. change (Datatypes.length FMT_C17) with 26%nat. unfold FMT_C17.
  destruct (convx_zpad_d 0 4 y ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C1 & CC1). ppx_dir2 C1 reflexivity. clear C1.
  ppx_cnt c2.
  destruct (convx_zpad_d c2 2 mo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps2 & C2 & CC2). ppx_dir2 C2 reflexivity. clear C2.
  ppx_cnt c3.
  destruct (convx_zpad_d c3 2 d ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps3 & C3 & CC3). ppx_dir2 C3 reflexivity. clear C3.
  ppx_cnt c4.
  destruct (convx_zpad_d c4 2 h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps4 & C4 & CC4). ppx_dir2 C4 reflexivity. clear C4.
  ppx_cnt c5.
  destruct (convx_zpad_d c5 2 mi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps5 & C5 & CC5). ppx_dir2 C5 reflexivity. clear C5.
  ppx_cnt c6.
  destruct (convx_zpad_d c6 2 s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps6 & C6 & CC6). ppx_dir2 C6 reflexivity. clear C6.
  ppx_lit2 [90] [0]. zlen_lits.
  ppx_finish.
  rewrite CC1, CC2, CC3, CC4, CC5, CC6. unfold ct_gentime. rewrite <- ?app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ct_genstr (g : list Z) (ms : Z) : list Z := firstn 14 g ++ [46] ++ zpad 3 ms ++ [90].
Definition ct_genstr_null (ms : Z) : list Z := NULLSTR ++ [46] ++ zpad 3 ms ++ [90].
Lemma zlength_ct_genstr : forall g ms, 14 <= zlength g -> 0 <= ms < 1000 -> zlength (ct_genstr g ms) = 19.
Proof.
  intros g ms Hg Hms. unfold ct_genstr. pose proof (zdigits_le4 ms ltac:(lia)).
  assert (zdigits ms <= 3).
  { unfold zdigits, zdec. destruct (Z.eqb_spec ms 0); [unfold zlength; cbn; lia|]. unfold dec_digits, zlength.
    do 3 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
    rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
      replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end. }
  rewrite !zlength_app', zlength_zpad by lia. change (zlength [46]) with 1. change (zlength [90]) with 1.
  unfold zlength in *. rewrite length_firstn. lia.
Qed.
Lemma zlength_ct_genstr_null : forall ms, 0 <= ms < 1000 -> zlength (ct_genstr_null ms) = 11.
Proof.
  intros ms Hms. unfold ct_genstr_null.
  assert (zdigits ms <= 3).
  { unfold zdigits, zdec. destruct (Z.eqb_spec ms 0); [unfold zlength; cbn; lia|]. unfold dec_digits, zlength.
    do 3 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
    rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
      replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end. }
  rewrite !zlength_app', zlength_zpad by lia. change (zlength NULLSTR) with 6. change (zlength [46]) with 1. change (zlength [90]) with 1. lia.
Qed.
Lemma zdigits_le3 : forall v, 0 <= v < 1000 -> zdigits v <= 3.
Proof.
  intros v Hv. unfold zdigits, zdec. destruct (Z.eqb_spec v 0); [unfold zlength; cbn; lia|].
  unfold dec_digits, zlength.
  do 3 (rewrite digits_aux_S'; match goal with |- context [if ?x =? 0 then _ else _] => destruct (Z.eqb_spec x 0); [cbn [length]; lia|] end).
  rewrite digits_aux_S'. match goal with |- context [if ?x =? 0 then _ else _] =>
    replace (x =? 0) with true; [cbn [length]; lia | symmetry; apply Z.eqb_eq; Z.div_mod_to_equations; lia] end.
Qed.
Lemma printf_piecesx_C18 : forall g ms, 14 <= zlength g <= 255 -> 0 <= ms < 1000 ->
  exists ps, printf_piecesx FMT_C18 [PA_s g; PA_i ms] = Some (ps, 19) /\ concat ps = ct_genstr g ms.
Proof.
  intros g ms Hg Hms. pose proof (zdigits_le3 ms Hms) as D1. pose proof (zdigits_range ms ltac:(lia)) as R1.
  unfold printf_piecesx. change (Datatypes.length FMT_C18) with 12%nat. unfold FMT_C18.
  destruct (convx_s_prec 0 0 14 g ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C1 & CC1).
  rewrite (Z.min_r (zlength g) 14) in C1, CC1 by lia. ppx_dir2 C1 reflexivity. clear C1.
  ppx_lit2 [46] [37; 48; 51; 100; 90; 0]. zlen_lits. ppx_cnt c2.
  destruct (convx_zpad_d c2 3 ms ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps2 & C2 & CC2). ppx_dir2 C2 reflexivity. clear C2.
  ppx_lit2 [90] [0]. zlen_lits.
  ppx_finish.
  rewrite CC1, CC2. unfold ct_genstr. cbn [zrepeat Z.to_nat repeat Z.sub app]. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma printf_piecesx_C18_null : forall ms, 0 <= ms < 1000 ->
  exists ps, printf_piecesx FMT_C18 [PA_sn; PA_i ms] = Some (ps, 11) /\ concat ps = ct_genstr_null ms.
Proof.
  intros ms Hms. pose proof (zdigits_le3 ms Hms) as D1. pose proof (zdigits_range ms ltac:(lia)) as R1.
  unfold printf_piecesx. change (Datatypes.length FMT_C18) with 12%nat. unfold FMT_C18.
  destruct (convx_sn_prec 0 0 14 ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps1 & C1 & CC1).
  ppx_dir2 C1 reflexivity. clear C1.
  ppx_lit2 [46] [37; 48; 51; 100; 90; 0]. zlen_lits. ppx_cnt c2.
  destruct (convx_zpad_d c2 3 ms ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia)) as (ps2 & C2 & CC2). ppx_dir2 C2 reflexivity. clear C2.
  ppx_lit2 [90] [0]. zlen_lits.
  ppx_finish.
  rewrite CC1, CC2. unfold ct_genstr_null. cbn [zrepeat Z.to_nat repeat Z.sub app]. rewrite <- ?app_assoc. reflexivity.
Qed.
