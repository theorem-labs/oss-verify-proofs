(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import ECH_B64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma du_tail_rv : forall st b, dr_rv (du_tail st b) = -1 \/ dr_rv (du_tail st b) = 0 \/ dr_rv (du_tail st b) = 1.
Proof.
  intros st b. unfold du_tail.
  destruct (Nat.ltb 0 (length (du_d st))); [| cbn; destruct (b || (0 <? du_eof st)); lia].
  destruct (Nat.eqb (Nat.modulo (length (du_d st)) 4) 0).
  - destruct (decodeblock (du_d st) (du_eof st)) as [bs|]; [| cbn; lia].
    destruct (Nat.eqb (length bs) 0 && (0 <? du_eof st)); cbn; [lia|]. destruct (b || (0 <? du_eof st)); lia.
  - destruct b; cbn; lia.
Qed.

Lemma du_loop_rv : forall inp st,
  dr_rv (du_loop st inp) = -1 \/ dr_rv (du_loop st inp) = 0 \/ dr_rv (du_loop st inp) = 1.
Proof.
  induction inp as [|c inp IH]; intros st; cbn; [apply du_tail_rv|].
  destruct (du_step st c); [cbn; lia| apply IH| apply du_tail_rv].
Qed.

Lemma decode_update_rv : forall d inp,
  dr_rv (decode_update d inp) = -1 \/ dr_rv (decode_update d inp) = 0 \/ dr_rv (decode_update d inp) = 1.
Proof. intros d [|c inp]; [cbn; lia|]. unfold decode_update. apply du_loop_rv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma du_tail_d : forall st b, 0 <= dr_rv (du_tail st b) ->
  length (dr_d (du_tail st b)) = 0%nat \/ Nat.modulo (length (dr_d (du_tail st b))) 4 <> 0%nat.
Proof.
  intros st b. unfold du_tail.
  destruct (Nat.ltb 0 (length (du_d st))) eqn:L; [| cbn; intros _; left; reflexivity].
  destruct (Nat.eqb (Nat.modulo (length (du_d st)) 4) 0) eqn:M.
  - destruct (decodeblock (du_d st) (du_eof st)) as [bs|]; [| cbn; lia].
    destruct (Nat.eqb (length bs) 0 && (0 <? du_eof st)); cbn; [lia| intros _; left; reflexivity].
  - apply Nat.eqb_neq in M. destruct b; cbn; [lia| intros _; right; exact M].
Qed.

Lemma du_loop_d : forall inp st, 0 <= dr_rv (du_loop st inp) ->
  length (dr_d (du_loop st inp)) = 0%nat \/ Nat.modulo (length (dr_d (du_loop st inp))) 4 <> 0%nat.
Proof.
  induction inp as [|c inp IH]; intros st; cbn; [apply du_tail_d|].
  destruct (du_step st c); [cbn; lia| apply IH| apply du_tail_d].
Qed.

Lemma decode_update_d : forall d inp, inp <> [] -> 0 <= dr_rv (decode_update d inp) ->
  length (dr_d (decode_update d inp)) = 0%nat \/ Nat.modulo (length (dr_d (decode_update d inp))) 4 <> 0%nat.
Proof. intros d [|c inp] NE; [congruence|]. unfold decode_update. apply du_loop_d. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div4_S4 : forall n, (S (S (S (S n))) / 4 = 1 + n / 4)%nat.
Proof. intros n. replace (S (S (S (S n)))) with (n + 1 * 4)%nat by lia. rewrite Nat.div_add by lia. lia. Qed.

Lemma decode_groups_length : forall vs bs, decode_groups vs = Some bs -> (length bs <= 3 * (length vs / 4))%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|d rest]]]] bs H; cbn in H; try (injection H as <-; cbn; lia).
  destruct (128 <=? Z.lor (Z.lor (Z.lor a b) c) d); [discriminate|].
  destruct (decode_groups rest) as [bs'|] eqn:E; [| discriminate]. injection H as <-.
  specialize (IH rest bs' E). cbn [quad_bytes length app]. rewrite div4_S4. lia.
Qed.

Lemma trim_ws_front_length : forall f, (length (trim_ws_front f) <= length f)%nat.
Proof. induction f as [|c f IH]; cbn; [lia|]. destruct (a2b c =? B64_WS); cbn; lia. Qed.

Lemma trim_nb64_back_rev_length : forall r k, (length (trim_nb64_back_rev r k) <= length r)%nat.
Proof. induction r as [|c r IH]; intros k; cbn - [Nat.ltb]; [lia|]. destruct (Nat.ltb 3 (S (length r)) && b64_not_base64 (a2b c)); cbn - [Nat.ltb]; [| lia]. specialize (IH k). lia. Qed.

Lemma trim_block_length : forall f, (length (trim_block f) <= length f)%nat.
Proof.
  intros f. unfold trim_block. rewrite length_rev.
  pose proof (trim_nb64_back_rev_length (rev (trim_ws_front f)) 0). rewrite length_rev in H.
  pose proof (trim_ws_front_length f). lia.
Qed.

Lemma decodeblock_length : forall f eof bs, decodeblock f eof = Some bs -> (length bs <= 3 * (length f / 4))%nat.
Proof.
  intros f eof bs H. unfold decodeblock in H.
  destruct ((eof <? -1) || (2 <? eof)); [discriminate|].
  destruct (negb (Z.of_nat (length (trim_block f)) mod 4 =? 0)); [discriminate|].
  destruct (Z.of_nat (length (trim_block f)) =? 0); [injection H as <-; cbn; lia|].
  destruct (decode_groups (map a2b (trim_block f))) as [bs0|] eqn:E; [| discriminate].
  injection H as <-. rewrite length_firstn.
  apply decode_groups_length in E. rewrite length_map in E.
  pose proof (trim_block_length f).
  assert (length (trim_block f) / 4 <= length f / 4)%nat by (apply Nat.Div0.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma du_tail_out : forall st b, (length (du_d st) <= 64)%nat ->
  (length (dr_out (du_tail st b)) <= length (du_out st) + 3 * (length (du_d st) / 4))%nat.
Proof.
  intros st b L. unfold du_tail.
  destruct (Nat.ltb 0 (length (du_d st))); [| cbn [dr_out]; lia].
  destruct (Nat.eqb (Nat.modulo (length (du_d st)) 4) 0).
  - destruct (decodeblock (du_d st) (du_eof st)) as [bs|] eqn:E; [| cbn [dr_out]; lia].
    apply decodeblock_length in E.
    destruct (Nat.eqb (length bs) 0 && (0 <? du_eof st)); cbn [dr_out]; [lia|].
    rewrite length_app. lia.
  - destruct b; cbn [dr_out]; lia.
Qed.

Lemma du_loop_out : forall inp st, (length (du_d st) < 64)%nat ->
  (length (dr_out (du_loop st inp)) <= length (du_out st) + 3 * ((length (du_d st) + length inp) / 4))%nat.
Proof.
  induction inp as [|c inp IH]; intros st L; cbn [du_loop length].
  - pose proof (du_tail_out st false ltac:(lia)). rewrite Nat.add_0_r. exact H.
  - unfold du_step.
    destruct (a2b c =? B64_ERROR); [cbn [dr_out]; lia|].
    destruct (negb (c =? CH_EQ) && (0 <? du_eof st) && b64_base64 (a2b c)); [cbn [dr_out]; lia|].
    set (eof1 := if c =? CH_EQ then du_eof st + 1 else du_eof st).
    destruct (2 <? eof1); [cbn [dr_out]; lia|].
    destruct (a2b c =? B64_EOF).
    { pose proof (du_tail_out (mkDU (du_d st) eof1 (du_out st)) true ltac:(cbn [du_d]; lia)) as T. cbn [du_d du_out] in T.
      assert (length (du_d st) / 4 <= (length (du_d st) + S (length inp)) / 4)%nat by (apply Nat.Div0.div_le_mono; lia). lia. }
    destruct (b64_base64 (a2b c) && Nat.leb 64 (length (du_d st))); [cbn [dr_out]; lia|].
    set (d1 := if b64_base64 (a2b c) then du_d st ++ [c] else du_d st).
    assert (D1 : (length d1 <= length (du_d st) + 1)%nat).
    { subst d1. destruct (b64_base64 (a2b c)); [rewrite length_app; cbn; lia| lia]. }
    clearbody d1.
    destruct (Nat.eqb (length d1) 64) eqn:E64.
    + apply Nat.eqb_eq in E64.
      destruct (decodeblock d1 eof1) as [bs|] eqn:E; [| cbn [dr_out]; lia].
      destruct (Nat.eqb (length bs) 0 && (0 <? eof1)); [cbn [dr_out]; lia|].
      cbv beta iota.
      specialize (IH (mkDU [] eof1 (du_out st ++ bs)) ltac:(cbn; lia)). cbn [du_d du_out length] in IH.
      rewrite length_app in IH. apply decodeblock_length in E. rewrite E64 in E. change (64 / 4)%nat with 16%nat in E.
      rewrite Nat.add_0_l in IH.
      assert ((63 + S (length inp)) / 4 >= 16 + length inp / 4)%nat.
      { replace (63 + S (length inp))%nat with (length inp + 16 * 4)%nat by lia. rewrite Nat.div_add by lia. lia. }
      assert ((63 + S (length inp)) / 4 <= (length (du_d st) + S (length inp)) / 4)%nat by (apply Nat.Div0.div_le_mono; lia).
      lia.
    + apply Nat.eqb_neq in E64. cbv beta iota.
      specialize (IH (mkDU d1 eof1 (du_out st)) ltac:(cbn; lia)). cbn [du_d du_out] in IH.
      assert ((length d1 + length inp) / 4 <= (length (du_d st) + S (length inp)) / 4)%nat by (apply Nat.Div0.div_le_mono; lia).
      lia.
Qed.

Lemma decode_update_out : forall d inp, (length d < 64)%nat ->
  (length (dr_out (decode_update d inp)) <= 3 * ((length d + length inp) / 4))%nat.
Proof.
  intros d [|c inp] L; [cbn [decode_update dr_out length]; lia|]. unfold decode_update.
  pose proof (du_loop_out (c :: inp) (mkDU d (initial_eof d) []) ltac:(cbn; lia)) as B. cbn [du_d du_out length] in B. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma b64r_loop_outl_le0 : forall fuel rest d ret outl acc used, (0 < fuel)%nat -> outl <= 0 ->
  b64r_loop fuel rest d ret outl acc used = mkBR ret acc used.
Proof. intros [|fuel] rest d ret outl acc used F L; [lia|]. cbn [b64r_loop]. replace (outl <=? 0) with true by (symmetry; apply Z.leb_le; exact L). reflexivity. Qed.

Lemma b64r_loop_eof : forall fuel d ret outl acc used, 0 < outl ->
  b64r_loop (S fuel) [] d ret outl acc used = mkBR (if ret =? 0 then (if decode_final_rv d <? 0 then -1 else 0) else ret) acc used.
Proof. intros. cbn [b64r_loop]. replace (outl <=? 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma b64r_loop_trip : forall fuel rest d ret outl acc used, 0 < outl -> rest <> [] ->
  b64r_loop (S fuel) rest d ret outl acc used =
    (let chunk := firstn 1024 rest in
     let r := decode_update d chunk in
     let used' := (used + length chunk)%nat in
     if dr_rv r <? 0 then mkBR (if ret =? 0 then 0 else ret) acc used'
     else
       let i := Z.min (Z.of_nat (length (dr_out r))) outl in
       let acc' := acc ++ firstn (Z.to_nat i) (dr_out r) in
       if dr_rv r =? 0 then mkBR (if ret + i =? 0 then 0 else ret + i) acc' used'
       else b64r_loop fuel (skipn 1024 rest) (dr_d r) (ret + i) (outl - i) acc' used').
Proof.
  intros fuel rest d ret outl acc used L NE. cbn [b64r_loop]. replace (outl <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct rest; [congruence| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma b64r_loop_nofuel : forall rest d ret outl acc used, 0 < ret ->
  b64r_loop 0 rest d ret outl acc used = mkBR ret acc used.
Proof. intros. cbn. replace (ret =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_lnot15_15 : forall f, Z.land (Z.land f (Z.lnot 15)) 15 = 0.
Proof. intros f. rewrite <- Z.land_assoc. replace (Z.land (Z.lnot 15) 15) with 0 by reflexivity. apply Z.land_0_r. Qed.

Lemma b64_flags_facts : forall f, 0 <= f < 2^31 -> Z.land f 256 = 256 ->
  0 <= Z.land f (Z.lnot 15) < 2^31 /\ Z.land (Z.land f (Z.lnot 15)) 256 = 256.
Proof.
  intros f Hf H8. change (Z.land f (Z.lnot 15)) with (Z.ldiff f 15).
  assert (RNG : 0 <= Z.ldiff f 15 < 2^31).
  { change 15 with (Z.ones 4). rewrite Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    pose proof (Z.mul_div_le f (2^4) ltac:(lia)). pose proof (Z.div_pos f (2^4) ltac:(lia) ltac:(lia)). lia. }
  split; [exact RNG|].
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.ldiff_spec by lia.
  destruct (Z.eq_dec n 8) as [->|NE].
  - apply (f_equal (fun z => Z.testbit z 8)) in H8. rewrite Z.land_spec in H8. change (Z.testbit 256 8) with true in H8 |- *.
    change (Z.testbit 15 8) with false. rewrite Bool.andb_true_r in H8. rewrite H8. reflexivity.
  - replace (Z.testbit 256 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
    symmetry. destruct (Z.lt_ge_cases n 8) as [L|L].
    + destruct (Z.eq_dec n 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|]; [reflexivity|].
      destruct (Z.eq_dec n 3) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 5) as [->|]; [reflexivity|].
      destruct (Z.eq_dec n 6) as [->|]; [reflexivity|]. destruct (Z.eq_dec n 7) as [->|]; [reflexivity|]. lia.
    + apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma land_lnot15_8 : forall f, Z.land (Z.land f (Z.lnot 15)) 8 = 0.
Proof. intros f. rewrite <- Z.land_assoc. replace (Z.land (Z.lnot 15) 8) with 0 by reflexivity. apply Z.land_0_r. Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
