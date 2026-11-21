(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool String.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio ZApi ZHarness.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Printf_pieces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FMT_err : list Z := (str "%s error: %d" ++ [10; 0])%list.

Lemma dec_digits_n_dec : forall fuel x acc, (0 < fuel)%nat -> 1 <= x < 10 ^ Z.of_nat fuel -> x < 2^64 ->
  dec_digits_n fuel x acc = (dec_digits x ++ acc)%list.
Proof.
  induction fuel as [|f IH]; intros x acc Hf Hx H64; [lia|]. cbn [dec_digits_n].
  destruct (Z.ltb_spec x 10) as [L|L].
  - rewrite dec_digits_small by lia. reflexivity.
  - assert (Hf' : (0 < f)%nat).
    { destruct f; [|lia]. cbn in Hx. lia. }
    rewrite IH; [| exact Hf'| | ].
    + rewrite (dec_digits_step x) by lia. rewrite <- app_assoc. reflexivity.
    + split; [apply Z.div_le_lower_bound; lia|]. apply Z.div_lt_upper_bound; [lia|].
      replace (10 * 10 ^ Z.of_nat f) with (10 ^ Z.of_nat (S f)); [lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
    + pose proof (Z.div_le_upper_bound x 10 x ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma Zdecimal_dec : forall x, 1 <= x < 2^64 -> Zdecimal x = dec_digits x.
Proof.
  intros x Hx. unfold Zdecimal. rewrite dec_digits_n_dec; [apply app_nil_r| lia| | lia].
  split; [lia|]. change (Z.of_nat 64) with 64. assert (2^64 < 10^64) by (vm_compute; reflexivity). lia.
Qed.

Definition pieces_d (i : Z) : list (list Z) :=
  if i <? 0 then [[45]; dec_digits (- i)] else if i =? 0 then [[]; [48]; []] else [[]; dec_digits i].

Lemma pieces_d_concat : forall i, - 2^31 <= i < 2^31 -> List.concat (pieces_d i) = Zsdecimal i.
Proof.
  intros i Hi. unfold pieces_d, Zsdecimal.
  destruct (Z.ltb_spec i 0) as [N|N].
  - cbn [List.concat app]. rewrite app_nil_r. rewrite Zdecimal_dec by lia. reflexivity.
  - destruct (Z.eqb_spec i 0) as [->|NZ]; [reflexivity|].
    cbn [List.concat app]. rewrite app_nil_r. rewrite Zdecimal_dec by lia. reflexivity.
Qed.

Lemma pieces_d_len : forall i, - 2^31 <= i < 2^31 -> 1 <= zlength (List.concat (pieces_d i)) <= 21.
Proof.
  intros i Hi. unfold pieces_d.
  destruct (Z.ltb_spec i 0) as [N|N]; [| destruct (Z.eqb_spec i 0) as [->|NZ]]; cbn [List.concat app]; rewrite ?app_nil_r.
  - pose proof (dec_digits_zlength (- i)). unfold zlength in *. cbn [Datatypes.length]. lia.
  - cbv. split; discriminate.
  - pose proof (dec_digits_zlength i). pose proof (dec_digits_nz i ltac:(lia)) as NE.
    destruct (dec_digits i); [contradiction|]. unfold zlength in *. cbn [Datatypes.length] in *. lia.
Qed.

Lemma conv_pieces_d : forall cnt i, 0 <= cnt -> cnt + 32 <= INT_MAX -> - 2^31 <= i < 2^31 ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i i)
  = Some (pieces_d i, cnt + zlength (List.concat (pieces_d i))).
Proof.
  intros cnt i Hc Hm Hi. unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty].
  cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_INT Pos.eqb andb MARK_POS PAD_POS].
  unfold pieces_d, INTMAX_MAX.
  destruct (Z.ltb_spec i 0) as [N|N].
  -
    assert (E1 : i mod 2^64 = i + 2^64) by (symmetry; apply (Z.mod_unique_pos _ _ (-1)); lia).
    rewrite E1. replace (9223372036854775807 <? i + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    assert (E2 : (- (i + 2^64)) mod 2^64 = - i) by (symmetry; apply (Z.mod_unique_pos _ _ (-1)); lia).
    rewrite E2. unfold int_pieces. cbn [andb]. replace (- i =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    pose proof (dec_digits_zlength (- i)) as DL. pose proof (dec_digits_nz (- i) ltac:(lia)) as NE.
    assert (L1 : 1 <= zlength (dec_digits (- i))) by (destruct (dec_digits (- i)); [contradiction| unfold zlength; cbn [Datatypes.length]; lia]).
    unfold tail_pieces. cbv zeta. change (zlength [45]) with 1. unfold INT_MAX in *.
    replace (Z.max (Z.max (-1) (zlength (dec_digits (- i)) + 0)) (zlength (dec_digits (- i)))) with (zlength (dec_digits (- i))) by lia.
    replace (2147483647 - 1 <? zlength (dec_digits (- i))) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Z.max 0 (1 + zlength (dec_digits (- i)))) with (1 + zlength (dec_digits (- i))) by lia.
    replace (2147483647 - cnt <? 1 + zlength (dec_digits (- i))) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold pad_pieces. rewrite !Z.leb_refl. rewrite !orb_true_r. cbn [app List.concat]. rewrite app_nil_r.
    do 2 f_equal. unfold zlength. cbn [Datatypes.length]. lia.
  - assert (E1 : i mod 2^64 = i) by (apply Z.mod_small; lia). rewrite E1.
    replace (9223372036854775807 <? i) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold int_pieces. cbn [andb].
    destruct (Z.eqb_spec i 0) as [->|NZ].
    + unfold INT_MAX in Hm. clear - Hc Hm. cbn [andb Z.eqb]. change (dec_digits 0) with (@nil Z).
      unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0. unfold INT_MAX.
      change (Z.max (Z.max (-1) (0 + 1)) 0) with 1. change (2147483647 - 0 <? 1) with false. change (0 + 1) with 1. change (Z.max 0 1) with 1. cbv iota.
      replace (2147483647 - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      reflexivity.
    + cbn [andb].
      pose proof (dec_digits_zlength i) as DL. pose proof (dec_digits_nz i ltac:(lia)) as NE.
      assert (L1 : 1 <= zlength (dec_digits i)) by (destruct (dec_digits i); [contradiction| unfold zlength; cbn [Datatypes.length]; lia]).
      unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0. unfold INT_MAX in *.
      replace (Z.max (Z.max (-1) (zlength (dec_digits i) + 0)) (zlength (dec_digits i))) with (zlength (dec_digits i)) by lia.
      replace (2147483647 - 0 <? zlength (dec_digits i)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (Z.max 0 (0 + zlength (dec_digits i))) with (zlength (dec_digits i)) by lia.
      replace (2147483647 - cnt <? zlength (dec_digits i)) with false by (symmetry; apply Z.ltb_ge; lia).
      unfold pad_pieces. rewrite !Z.leb_refl. rewrite !orb_true_r. cbn [app List.concat]. rewrite app_nil_r. reflexivity.
Qed.

Definition pieces_err (name : list Z) (rc : Z) : list (list Z) :=
  ([[]; []; name; str " error: "; []] ++ pieces_d rc ++ [[10]])%list.

Lemma pieces_err_concat : forall name rc, - 2^31 <= rc < 2^31 -> List.concat (pieces_err name rc) = msg_err name rc.
Proof.
  intros name rc Hrc. unfold pieces_err, msg_err. rewrite concat_app. cbn [List.concat app].
  rewrite concat_app. cbn [List.concat app]. rewrite (pieces_d_concat rc Hrc). rewrite app_nil_r. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma printf_pieces_err : forall name rc, zlength name < 2^20 -> - 2^31 <= rc < 2^31 ->
  printf_pieces FMT_err [PA_s name; PA_i rc] = Some (pieces_err name rc, zlength (msg_err name rc)).
Proof.
  intros name rc Hn Hrc. pose proof (zlength_nonneg' name) as H0. pose proof (pieces_d_len rc Hrc) as DL. unfold printf_pieces.
  change (Datatypes.length FMT_err) with 14%nat.
  ppl_step. rewrite conv_pieces_s by (unfold INT_MAX; lia).
  change [32; 101; 114; 114; 111; 114; 58; 32; 37; 100; 10; 0] with ([32; 101; 114; 114; 111; 114; 58; 32] ++ 37 :: [100; 10; 0])%list.
  rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia]
                        | change (zlength [32; 101; 114; 114; 111; 114; 58; 32]) with 8; unfold INT_MAX; lia ].
  change (zlength [32; 101; 114; 114; 111; 114; 58; 32]) with 8.
  remember (0 + zlength name + 8) as c1 eqn:Ec1.
  ppl_step. rewrite conv_pieces_d by (unfold INT_MAX; lia).
  rewrite (ppl_noargs_shift 11 [10; 0] (c1 + zlength (List.concat (pieces_d rc))) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
  unfold pieces_err. cbn [app]. do 2 f_equal.
  rewrite <- (pieces_err_concat name rc Hrc). unfold pieces_err. rewrite concat_app. cbn [List.concat app]. rewrite concat_app. cbn [List.concat app].
  rewrite app_nil_r. subst c1. unfold zlength. rewrite !length_app. cbn [Datatypes.length].
  change (Datatypes.length (str " error: ")) with 8%nat. lia.
Qed.

Lemma pass1_ok_err : pass1_ok FMT_err = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_err : forall name rc, fp_calls (Datatypes.length FMT_err) FMT_err [PA_s name; PA_i rc] = [].
Proof. intros. reflexivity. Qed.

Section Concat.
Context {St : Type}.
Lemma stderr_pieces_fit : forall ps buf (s : St), zlength buf + zlength (List.concat ps) <= INTERNAL_BUFSIZ ->
  stderr_pieces buf ps s = mret (buf ++ List.concat ps)%list s.
Proof.
  induction ps as [|p ps IH]; intros buf s H; cbn [stderr_pieces List.concat].
  - rewrite app_nil_r. reflexivity.
  - cbn [List.concat] in H. assert (L : zlength (p ++ List.concat ps) = zlength p + zlength (List.concat ps)) by (unfold zlength; rewrite length_app; lia).
    pose proof (zlength_nonneg' (List.concat ps)). pose proof (zlength_nonneg' p). pose proof (zlength_nonneg' buf).
    replace (INTERNAL_BUFSIZ - zlength buf <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite IH; [rewrite <- app_assoc; reflexivity|]. unfold zlength in *. rewrite length_app. lia.
Qed.

Lemma stderr_fprintf_concat : forall ps (s : St), zlength (List.concat ps) <= INTERNAL_BUFSIZ ->
  stderr_fprintf ps s = stderr_fprintf [List.concat ps] s.
Proof.
  intros ps s H. unfold stderr_fprintf. unfold mbind.
  rewrite (stderr_pieces_fit ps [] s) by (change (zlength (@nil Z)) with 0; lia).
  rewrite (stderr_pieces_fit [List.concat ps] [] s) by (change (zlength (@nil Z)) with 0; cbn [List.concat]; rewrite app_nil_r; lia).
  cbn [List.concat app]. rewrite app_nil_r. reflexivity.
Qed.
End Concat.
