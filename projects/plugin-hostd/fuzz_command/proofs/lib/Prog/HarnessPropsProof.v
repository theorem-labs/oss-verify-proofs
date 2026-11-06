From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Strings.String Strings.Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel RecFacts RecModel
  sup_reply_code_c rec_code_declared_c rec_shape_of_c check_reply_answer_c check_reply_c check_arity_c check_words_c
  check_words_add_c check_words_chain_c check_words_pin_set_c printf_facts_c atoi_c
  check_round_trip_c verbs_receive_c HarnessProps.
Import ListNotations.
Open Scope Z_scope.

(** * Byte lists *)

Lemma map_unsigned_inj : forall a b : list byte, map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma bl_eqb_eq : forall a b, bl_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold bl_eqb.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b)) as [E|E].
  - split; [intros _; apply map_unsigned_inj; exact E | reflexivity].
  - split; [discriminate | intros ->; contradiction E; reflexivity].
Qed.

Lemma cm_bytes_eqb : forall a b, CommandModel.bytes_eqb a b = bl_eqb a b.
Proof. reflexivity. Qed.

Lemma rs_bytes_eqb : forall a b, rec_shape_of_c.bytes_eqb a b = bl_eqb a b.
Proof. reflexivity. Qed.

Lemma list_eqb_bl : forall a b, Verbs.list_eqb a b = bl_eqb a b.
Proof.
  intros a b. destruct (bl_eqb a b) eqn:E.
  - apply bl_eqb_eq in E. subst. apply Verbs.list_eqb_eq. reflexivity.
  - destruct (Verbs.list_eqb a b) eqn:F; [|reflexivity].
    apply Verbs.list_eqb_eq in F. subst. rewrite <- E. symmetry. apply bl_eqb_eq. reflexivity.
Qed.

Lemma lit_bstr : forall s, Verbs.Lit.lit s = bstr s.
Proof.
  unfold bstr. induction s as [|a s IH]; [reflexivity|].
  cbn [Verbs.Lit.lit String.list_ascii_of_string map]. rewrite IH. f_equal. f_equal.
  unfold Ascii.nat_of_ascii. apply N_nat_Z.
Qed.

(** * Words *)

Lemma words_acc_cons : forall cur b l, Verbs.words_acc cur (b :: l) =
  if Verbs.is_sep b then match cur with [] => Verbs.words_acc [] l | _ :: _ => cur :: Verbs.words_acc [] l end
  else Verbs.words_acc (cur ++ [b]) l.
Proof. reflexivity. Qed.

Lemma words_acc_nil_ne : forall cur, cur <> [] -> Verbs.words_acc cur [] = [cur].
Proof. intros [|c cur] H; [congruence|reflexivity]. Qed.

Lemma join_sp_cons_ne : forall w ws, ws <> [] -> join_sp (w :: ws) = w ++ SPACE :: join_sp ws.
Proof. intros w [|w2 ws] H; [congruence|reflexivity]. Qed.

Lemma words_go_acc : forall l cur, RecFacts.words_go cur l = Verbs.words_acc (rev cur) l.
Proof.
  induction l as [|b l IH]; intros cur.
  - destruct cur as [|c cur']; [reflexivity|].
    cbn [RecFacts.words_go]. rewrite words_acc_nil_ne; [reflexivity|].
    intros E. apply (f_equal (@length _)) in E. rewrite length_rev in E. discriminate.
  - cbn [RecFacts.words_go]. rewrite words_acc_cons.
    change (RecFacts.is_sep b) with (Verbs.is_sep b). destruct (Verbs.is_sep b).
    + destruct cur as [|c cur']; [apply (IH [])|].
      destruct (rev (c :: cur')) as [|h t] eqn:E.
      * apply (f_equal (@length _)) in E. rewrite length_rev in E. discriminate.
      * rewrite <- E. f_equal. apply (IH []).
    + rewrite IH. reflexivity.
Qed.

Lemma words_eq : forall l, RecFacts.words l = Verbs.words l.
Proof. intros l. apply (words_go_acc l []). Qed.

Lemma canon_line : forall D, canon (Verbs.line D) = join_sp (hwords D).
Proof. intros D. unfold canon, hwords. rewrite words_eq. reflexivity. Qed.

Lemma first_word_line : forall D, first_word (Verbs.line D) = nth 0 (hwords D) [].
Proof. intros D. unfold first_word, hwords. rewrite words_eq. destruct (Verbs.words _); reflexivity. Qed.

Lemma hwords_word : forall D w, In w (hwords D) ->
  w <> [] /\ forall b, In b w -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9 /\ bv_unsigned b <> 0.
Proof.
  intros D t H. unfold hwords in H.
  destruct (Verbs.words_acc_spec (fun b => bv_unsigned b <> 0) (Verbs.line D) [] (fun b H => False_ind _ H)
    (Verbs.line_nonul D) t H) as [Hn Hb].
  split; [exact Hn|]. intros b Hi. destruct (Hb b Hi) as [Z0 S]. apply Verbs.sep_false in S.
  destruct S as [S1 S2]. split; [|split]; assumption.
Qed.

Lemma hwords_sep : forall D w, In w (hwords D) -> w <> [] /\ forall b, In b w -> Verbs.is_sep b = false.
Proof.
  intros D w H. destruct (hwords_word D w H) as [Hn Hb]. split; [exact Hn|].
  intros b Hi. apply Verbs.sep_false. destruct (Hb b Hi) as (H1 & H2 & _). split; assumption.
Qed.

(** ** Re-reading the joined words *)

Lemma dropw_head : forall p (l : list byte), Verbs.dropw p l = [] \/ exists c r, Verbs.dropw p l = c :: r /\ p c = false.
Proof.
  intros p l; induction l as [|x l IH]; cbn [Verbs.dropw]; [left; reflexivity|].
  destruct (p x) eqn:E; [exact IH| right; exists x, l; split; [reflexivity|exact E]].
Qed.

Lemma trim_last : forall l, Verbs.trim l = [] \/ exists y b, Verbs.trim l = y ++ [b] /\ Verbs.is_trail b = false.
Proof.
  intros l. unfold Verbs.trim.
  destruct (dropw_head Verbs.is_trail (rev l)) as [E|(c & r & E & H)]; rewrite E; [left; reflexivity|].
  right. exists (rev r), c. split; [reflexivity|exact H].
Qed.

Lemma trim_app_last : forall y b, Verbs.is_trail b = false -> Verbs.trim (y ++ [b]) = y ++ [b].
Proof.
  intros y b H. unfold Verbs.trim. rewrite rev_app_distr. cbn [rev app Verbs.dropw]. rewrite H.
  cbn [rev]. rewrite rev_involutive. reflexivity.
Qed.

Lemma words_acc_last : forall l cur b, Verbs.is_sep b = false ->
  exists ws' w, Verbs.words_acc cur (l ++ [b]) = ws' ++ [w ++ [b]].
Proof.
  induction l as [|x l IH]; intros cur b Hb; cbn [app].
  - rewrite words_acc_cons, Hb. rewrite words_acc_nil_ne by (destruct cur; discriminate).
    exists [], cur. reflexivity.
  - rewrite words_acc_cons. destruct (Verbs.is_sep x).
    + destruct cur as [|c cur']; [exact (IH [] b Hb)|].
      destruct (IH [] b Hb) as (ws' & w & E). rewrite E. exists ((c :: cur') :: ws'), w. reflexivity.
    + exact (IH (cur ++ [x]) b Hb).
Qed.

Lemma join_last : forall ws' w (b : byte), exists y, join_sp (ws' ++ [w ++ [b]]) = y ++ [b].
Proof.
  induction ws' as [|w' ws'' IH]; intros w b; [exists w; reflexivity|].
  destruct (IH w b) as [y E]. exists (w' ++ SPACE :: y). cbn [app].
  rewrite join_sp_cons_ne by (destruct ws''; discriminate). rewrite E, <- app_assoc. reflexivity.
Qed.

Lemma in_join_sp : forall ws b, In b (join_sp ws) -> b = SPACE \/ exists w, In w ws /\ In b w.
Proof.
  induction ws as [|w ws IH]; intros b H; [destruct H|].
  destruct ws as [|w2 ws']; [right; exists w; split; [left; reflexivity|exact H]|].
  rewrite join_sp_cons_ne in H by discriminate. apply in_app_or in H. destruct H as [H|[H|H]].
  - right. exists w. split; [left; reflexivity|exact H].
  - left. symmetry. exact H.
  - destruct (IH b H) as [E|(w' & Hw & Hb)]; [left; exact E|]. right. exists w'. split; [right; exact Hw|exact Hb].
Qed.

Lemma line_join : forall D, Verbs.line (join_sp (hwords D)) = join_sp (hwords D).
Proof.
  intros D.
  assert (NZ : forall b, In b (join_sp (hwords D)) -> (bv_unsigned b =? 0) = false).
  { intros b Hb. apply Z.eqb_neq. destruct (in_join_sp _ b Hb) as [E|(w & Hw & Hi)].
    - subst. unfold SPACE. rewrite byte_unsigned by lia. discriminate.
    - destruct (hwords_word D w Hw) as [_ H]. apply (H b Hi). }
  unfold Verbs.line at 1, Verbs.upto0. rewrite (Verbs.upto_all _ _ NZ).
  unfold hwords in *. destruct (trim_last (Verbs.upto0 D)) as [E|(y & b & E & Hb)].
  - unfold Verbs.line. rewrite E. reflexivity.
  - unfold Verbs.line. rewrite E.
    assert (Hs : Verbs.is_sep b = false).
    { unfold Verbs.is_trail in Hb. apply orb_false_iff in Hb as [Hb _]. apply orb_false_iff in Hb as [Hb _]. exact Hb. }
    unfold Verbs.words. destruct (words_acc_last y [] b Hs) as (ws' & w & E2). rewrite E2.
    destruct (join_last ws' w b) as [y' E3]. rewrite E3. apply trim_app_last. exact Hb.
Qed.

Lemma words_acc_app : forall w cur rest, (forall b, In b w -> Verbs.is_sep b = false) ->
  Verbs.words_acc cur (w ++ rest) = Verbs.words_acc (cur ++ w) rest.
Proof.
  induction w as [|b w IH]; intros cur rest H; [rewrite app_nil_r; reflexivity|].
  cbn [app]. rewrite words_acc_cons, (H b (or_introl eq_refl)).
  rewrite IH by (intros c Hc; apply H; right; exact Hc). rewrite <- app_assoc. reflexivity.
Qed.

Lemma words_join : forall ws, (forall w, In w ws -> w <> [] /\ forall b, In b w -> Verbs.is_sep b = false) ->
  Verbs.words (join_sp ws) = ws.
Proof.
  induction ws as [|w ws IH]; intros H; [reflexivity|].
  destruct (H w (or_introl eq_refl)) as [Hn Hb].
  destruct ws as [|w2 ws'].
  - cbn [join_sp]. unfold Verbs.words. replace w with (w ++ []) at 1 by apply app_nil_r.
    rewrite words_acc_app by exact Hb. cbn [app]. apply words_acc_nil_ne. exact Hn.
  - rewrite join_sp_cons_ne by discriminate. unfold Verbs.words. rewrite words_acc_app by exact Hb.
    cbn [app]. rewrite words_acc_cons.
    replace (Verbs.is_sep SPACE) with true by reflexivity.
    destruct w as [|c w']; [congruence|]. f_equal. apply IH. intros w0 Hw0. apply H. right. exact Hw0.
Qed.

Lemma toks_join : forall D, Verbs.toks (join_sp (hwords D)) = Verbs.toks D.
Proof.
  intros D. unfold Verbs.toks. rewrite line_join, words_join; [reflexivity|].
  intros w Hw. exact (hwords_sep D w Hw).
Qed.

Lemma join_le_line : forall D, (length (join_sp (hwords D)) <= length (Verbs.line D))%nat.
Proof. intros D. rewrite <- canon_line. apply canon_length. Qed.

Lemma toks_firstn : forall D, Verbs.toks D = firstn 64 (hwords D).
Proof. reflexivity. Qed.

Lemma firstn64_small : forall (ws l : list (list byte)), l = firstn 64 ws -> (length l < 64)%nat -> ws = l.
Proof.
  intros ws l E H. subst l. rewrite length_firstn in H. rewrite firstn_all2 by lia. reflexivity.
Qed.

Lemma firstn64_nth : forall (ws l : list (list byte)) k, l = firstn 64 ws -> (k < length l)%nat ->
  nth k ws [] = nth k l [].
Proof.
  intros ws l k E H. subst l. rewrite length_firstn in H. rewrite nth_firstn.
  destruct (Nat.ltb_spec k 64); [reflexivity|lia].
Qed.

Lemma firstn64_len : forall (ws l : list (list byte)), l = firstn 64 ws ->
  Z.min (Z.of_nat (length ws)) 64 = Z.of_nat (length l).
Proof. intros ws l E. subst l. rewrite length_firstn. lia. Qed.

Lemma firstn64_nil : forall (ws : list (list byte)), firstn 64 ws = [] -> ws = [].
Proof. intros [|w ws] H; [reflexivity|discriminate]. Qed.

(** * Numbers *)

Lemma swr_range : forall z, -2^31 <= bv_swrap 32 z < 2^31.
Proof. intros z. apply (bv_swrap_in_range 32). discriminate. Qed.

Lemma swr_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z H. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma pf_digits_map : forall k x acc, map (Z_to_bv 8) (pf_digits k x acc) = digits k x (map (Z_to_bv 8) acc).
Proof.
  induction k as [|k IH]; intros x acc; cbn [pf_digits digits]; [reflexivity|].
  destruct (x <? 10); [reflexivity|]. apply IH.
Qed.

Lemma digits_extra : forall k x acc, (1 <= k)%nat -> 0 <= x < 10 ^ Z.of_nat k -> digits (S k) x acc = digits k x acc.
Proof.
  induction k as [|k IH]; intros x acc Hk Hx; [lia|].
  rewrite (digits_S (S k) x acc), (digits_S k x acc). destruct (Z.ltb_spec x 10) as [L|L]; [reflexivity|].
  destruct k as [|k]; [cbn in Hx; lia|].
  apply IH; [lia|]. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. lia.
Qed.

Lemma dec_pf : forall v, -2^31 <= v < 2^31 -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros v Hv. unfold pf_bytes, pf_dec, dec. destruct (Z.ltb_spec v 0) as [L|L].
  - cbn [map app]. rewrite pf_digits_map. rewrite digits_extra by (cbn; lia).
    replace (Z.abs v) with (- v) by lia. reflexivity.
  - cbn [app]. rewrite pf_digits_map. rewrite digits_extra by (cbn; lia).
    replace (Z.abs v) with v by lia. reflexivity.
Qed.

Lemma atoi_acc_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= atoi_acc n s < 2^31.
Proof.
  induction s as [|b s IH]; intros n Hn; cbn [atoi_acc]; [exact Hn|].
  destruct (CType.c_digit b); [apply IH; apply swr_range|exact Hn].
Qed.

Lemma atoi_range : forall s, -2^31 <= atoi_val s < 2^31.
Proof.
  intros s. unfold atoi_val. destruct (CType.skip_space s) as [|b r]; [lia|].
  destruct (bv_unsigned b =? 45); [apply atoi_acc_range; lia|].
  destruct (bv_unsigned b =? 43); apply swr_range.
Qed.

Lemma dec_atoi : forall s, pf_bytes (pf_dec (atoi_val s)) = dec (atoi_val s).
Proof. intros s. apply dec_pf. apply atoi_range. Qed.

Lemma skip_space_dropw : forall s, CType.skip_space s = Verbs.dropw Verbs.is_space s.
Proof.
  induction s as [|b s IH]; [reflexivity|]. cbn [CType.skip_space Verbs.dropw].
  replace (CType.c_space b) with (Verbs.is_space b) by (unfold CType.c_space, Verbs.is_space; apply orb_comm).
  destruct (Verbs.is_space b); [exact IH|reflexivity].
Qed.

Lemma digits_val_atoi : forall l acc d, 0 <= acc -> Verbs.digits_val acc l = Some d -> d < 2^31 ->
  atoi_acc (- acc) l = - d /\ acc <= d.
Proof.
  induction l as [|b l IH]; intros acc d Ha H Hd; cbn [Verbs.digits_val] in H.
  - injection H as <-. split; reflexivity.
  - destruct (Verbs.is_digit b) eqn:Db; [|discriminate].
    assert (Hb : 48 <= bv_unsigned b <= 57).
    { unfold Verbs.is_digit in Db. apply andb_true_iff in Db as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2. lia. }
    destruct (IH (10 * acc + (bv_unsigned b - 48)) d ltac:(lia) H Hd) as [E L].
    cbn [atoi_acc]. replace (CType.c_digit b) with true by (symmetry; exact Db).
    rewrite swr_id by lia. replace (10 * - acc - (bv_unsigned b - 48)) with (- (10 * acc + (bv_unsigned b - 48))) by lia.
    split; [exact E|lia].
Qed.

Lemma number_atoi : forall w v, Verbs.number_m w = Some v -> atoi_val w = v.
Proof.
  intros w v H. unfold Verbs.number_m in H. unfold atoi_val. rewrite skip_space_dropw.
  destruct (Verbs.dropw Verbs.is_space w) as [|b r]; [discriminate|].
  destruct (Verbs.signed_digits (b :: r)) as [x|] eqn:E; [|discriminate].
  destruct ((-1000000 <=? x) && (x <=? 1000000)) eqn:R; [|discriminate]. injection H as <-.
  apply andb_true_iff in R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
  cbn [Verbs.signed_digits] in E.
  destruct (Z.eqb_spec (bv_unsigned b) 43) as [B43|B43].
  - rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 45)) by lia.
    unfold Verbs.digits_m in E. destruct r as [|c r']; [discriminate|].
    destruct (digits_val_atoi (c :: r') 0 x ltac:(lia) E ltac:(lia)) as [A L].
    change (- 0) with 0 in A. rewrite A. rewrite swr_id by lia. lia.
  - destruct (Z.eqb_spec (bv_unsigned b) 45) as [B45|B45].
    + unfold Verbs.digits_m in E. destruct r as [|c r']; [discriminate|].
      destruct (Verbs.digits_val 0 (c :: r')) as [d|] eqn:Ed; [|discriminate]. cbn in E. injection E as <-.
      destruct (digits_val_atoi (c :: r') 0 d ltac:(lia) Ed ltac:(lia)) as [A L].
      change (- 0) with 0 in A. exact A.
    + unfold Verbs.digits_m in E.
      destruct (digits_val_atoi (b :: r) 0 x ltac:(lia) E ltac:(lia)) as [A L].
      change (- 0) with 0 in A. rewrite A. rewrite swr_id by lia. lia.
Qed.

Lemma numbers_atoi : forall l ids, Verbs.numbers_m l = Some ids -> map atoi_val l = ids.
Proof.
  induction l as [|w l IH]; intros ids H; cbn [Verbs.numbers_m] in H.
  - injection H as <-. reflexivity.
  - destruct (Verbs.number_m w) as [v|] eqn:E1; [|discriminate].
    destruct (Verbs.numbers_m l) as [vs|] eqn:E2; [|discriminate]. injection H as <-.
    cbn [map]. rewrite (number_atoi w v E1), (IH vs eq_refl). reflexivity.
Qed.

(** * Replies *)

Lemma declared_in : forall c, declared c = true -> In c rec_codes.
Proof.
  intros c H. unfold declared in H. apply existsb_exists in H as (v & Hv & E). apply Z.eqb_eq in E. subst. exact Hv.
Qed.

Definition decl_ok (c : Z) : bool := (reply_code (resp c) =? c) && bl_eqb (refusal_text c) (resp c).

Lemma decl_all : forallb decl_ok rec_codes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma resp_declared : forall c, declared c = true -> reply_code (resp c) = c /\ refusal_text c = resp c.
Proof.
  intros c H. pose proof decl_all as A. rewrite forallb_forall in A. specialize (A c (declared_in c H)).
  unfold decl_ok in A. apply andb_true_iff in A as [A1 A2]. apply Z.eqb_eq in A1. apply bl_eqb_eq in A2.
  split; assumption.
Qed.

Lemma reply_ok_neg : forall n w0 c, declared c = true -> reply_ok n w0 (resp c).
Proof.
  intros n w0 c H. destruct (resp_declared c H) as [E1 E2]. pose proof (declared_range c H) as Rg.
  unfold reply_ok. rewrite E1. split; [intros _; split; [exact H|symmetry; exact E2]|intros; lia].
Qed.

Lemma resp_declared_facts : forall c, declared c = true ->
  no0 (resp c) /\ Z.of_nat (length (resp c)) <= 28 /\ reply_code (resp c) = c /\ c < 0.
Proof.
  intros c H. pose proof (declared_range c H) as Rg. pose proof (resp_length c ltac:(lia)) as L.
  split; [apply resp_no0|split; [lia|split; [apply (resp_declared c H)|lia]]].
Qed.

Fixpoint tbl_ok (rows : list (Z * String.string * Z)) (tbl : list (list byte * list byte)) : bool :=
  match rows, tbl with
  | [], [] => true
  | (_, nm, rp) :: rows', (a, b) :: tbl' => bl_eqb (str_bytes nm) a && bl_eqb (img_str rp) b && tbl_ok rows' tbl'
  | _, _ => false
  end.

Lemma tbl_find : forall rows tbl, tbl_ok rows tbl = true ->
  img_str SHAPE_LIT = REC_MOD_HOST_SHAPE -> forall w, img_str (shape_find rows w) = shape_lookup tbl w.
Proof.
  induction rows as [|[[na nm] rp] rows IH]; intros [|[a b] tbl] H HL w.
  - exact HL.
  - cbn [tbl_ok] in H. exfalso. exact (diff_false_true H).
  - cbn [tbl_ok] in H. exfalso. exact (diff_false_true H).
  - idtac.
  cbn [tbl_ok] in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply bl_eqb_eq in H1. apply bl_eqb_eq in H2. cbn [shape_find shape_lookup]. rewrite rs_bytes_eqb, H1.
  destruct (bl_eqb a w); [exact H2|]. apply IH; assumption.
Qed.

Lemma img_lit : img_str SHAPE_LIT = REC_MOD_HOST_SHAPE.
Proof. apply bl_eqb_eq. vm_compute. reflexivity. Qed.

Lemma img_shape : forall w, img_str (shape_find shape_rows w) = shape_of w.
Proof. intros w. apply tbl_find; [vm_compute; reflexivity|exact img_lit]. Qed.

Definition sh_ok (s : list byte) : bool :=
  (0 <=? reply_code (inst s)) && reply_matches s (inst s) && nz (inst s) && (Z.of_nat (length (inst s)) <=? 28).

Lemma sh_all : forallb sh_ok shape_set = true.
Proof. vm_compute. reflexivity. Qed.

Lemma shape_inst : forall w, 0 <= reply_code (inst (shape_of w)) /\ reply_matches (shape_of w) (inst (shape_of w)) = true /\
  no0 (inst (shape_of w)) /\ Z.of_nat (length (inst (shape_of w))) <= 28.
Proof.
  intros w. pose proof sh_all as A. rewrite forallb_forall in A. specialize (A _ (shape_of_in w)).
  unfold sh_ok in A. repeat rewrite andb_true_iff in A. destruct A as [[[A1 A2] A3] A4].
  apply Z.leb_le in A1. apply no0_nz in A3. apply Z.leb_le in A4. repeat split; assumption.
Qed.

Lemma reply_ok_shape : forall n w, n <> 0 -> reply_ok n w (inst (shape_of w)).
Proof.
  intros n w Hn. destruct (shape_inst w) as (R & M & _). unfold reply_ok. split; [intros; lia|].
  intros _. left. unfold shape_addr. rewrite (proj2 (Z.eqb_neq n 0) Hn). rewrite img_shape. exact M.
Qed.

Lemma inst_host : inst REC_MOD_HOST_SHAPE = resp 0.
Proof. apply bl_eqb_eq. vm_compute. reflexivity. Qed.

Lemma resp0_facts : reply_code (resp 0) = 0 /\ no0 (resp 0) /\ Z.of_nat (length (resp 0)) <= 28.
Proof. split; [vm_compute; reflexivity|split; [apply resp_no0|vm_compute; discriminate]]. Qed.

Lemma reply_ok_resp0 : forall n w, reply_ok n w (resp 0).
Proof.
  intros n w. unfold reply_ok. rewrite (proj1 resp0_facts). split; [intros; lia|].
  intros _. right. rewrite img_lit. vm_compute. reflexivity.
Qed.

Lemma digits_val_digits : forall k n acc a, 0 <= n < 10 ^ Z.of_nat k ->
  exists m, 0 <= m /\ Verbs.digits_val a (digits k n acc) = Verbs.digits_val (a * 10 ^ m + n) acc.
Proof.
  induction k as [|k IH]; intros n acc a Hn.
  - cbn in Hn. exists 0. split; [lia|]. cbn [digits]. replace (a * 10 ^ 0 + n) with a by lia. reflexivity.
  - rewrite digits_S. destruct (Z.ltb_spec n 10) as [L|L].
    + exists 1. split; [lia|]. cbn [Verbs.digits_val]. unfold Verbs.is_digit. rewrite byte_unsigned by lia.
      replace ((48 <=? 48 + n) && (48 + n <=? 57)) with true
        by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      replace (a * 10 ^ 1 + n) with (10 * a + (48 + n - 48)) by (rewrite Z.pow_1_r; lia). reflexivity.
    + assert (Hq : 0 <= n / 10 < 10 ^ Z.of_nat k).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia.
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      destruct (IH (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc) a Hq) as (m & Hm & E).
      exists (m + 1). split; [lia|]. rewrite E. cbn [Verbs.digits_val]. unfold Verbs.is_digit.
      pose proof (Z.mod_pos_bound n 10 ltac:(lia)) as M. rewrite byte_unsigned by lia.
      replace ((48 <=? 48 + n mod 10) && (48 + n mod 10 <=? 57)) with true
        by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      pose proof (Z.div_mod n 10 ltac:(lia)) as DM.
      rewrite Z.pow_add_r, Z.pow_1_r by lia.
      replace (a * (10 ^ m * 10)) with (10 * (a * 10 ^ m)) by ring.
      replace (10 * (a * 10 ^ m + n / 10) + (48 + n mod 10 - 48)) with (10 * (a * 10 ^ m) + n) by lia.
      reflexivity.
Qed.

Lemma digits_all : forall k n acc, 0 <= n -> (forall b, In b acc -> 48 <= bv_unsigned b <= 57) ->
  forall b, In b (digits k n acc) -> 48 <= bv_unsigned b <= 57.
Proof.
  induction k as [|k IH]; intros n acc Hn Ha b H; cbn [digits] in H; [exact (Ha b H)|].
  destruct (Z.ltb_spec n 10) as [L|L].
  - destruct H as [<-|H]; [rewrite byte_unsigned by lia; lia|exact (Ha b H)].
  - apply (IH (n / 10) _ ltac:(apply Z.div_pos; lia)) in H; [exact H|].
    intros c [<-|Hc]; [|exact (Ha c Hc)].
    pose proof (Z.mod_pos_bound n 10 ltac:(lia)). rewrite byte_unsigned by lia. lia.
Qed.

Lemma digits_ne : forall k n acc, acc <> [] \/ (1 <= k)%nat -> digits k n acc <> [].
Proof.
  induction k as [|k IH]; intros n acc H; cbn [digits]; [destruct H; [exact H|lia]|].
  destruct (n <? 10); [discriminate|]. apply IH. left. discriminate.
Qed.

Lemma dec_pos : forall v, 0 <= v -> dec v = digits 10 v [].
Proof. intros v Hv. unfold dec. rewrite (proj2 (Z.ltb_ge v 0)) by lia. rewrite Z.abs_eq by lia. reflexivity. Qed.

Lemma dec_pos_facts : forall v, 0 <= v -> dec v <> [] /\ forall b, In b (dec v) -> 48 <= bv_unsigned b <= 57.
Proof.
  intros v Hv. rewrite dec_pos by exact Hv. split; [apply digits_ne; right; lia|].
  apply digits_all; [exact Hv|intros b []].
Qed.

Lemma atoi_val_dec : forall v, 0 <= v < 2^31 -> atoi_val (dec v) = v.
Proof.
  intros v Hv. destruct (dec_pos_facts v ltac:(lia)) as [Hne Hdig]. rewrite dec_pos in * by lia.
  destruct (digits_val_digits 10 v [] 0 ltac:(cbn; lia)) as (m & Hm & E).
  rewrite Z.mul_0_l, Z.add_0_l in E. change (Verbs.digits_val v []) with (Some v) in E.
  destruct (digits 10 v []) as [|b r] eqn:Edg; [congruence|].
  assert (Hb : 48 <= bv_unsigned b <= 57) by (apply Hdig; left; reflexivity).
  destruct (digits_val_atoi (b :: r) 0 v ltac:(lia) E ltac:(lia)) as [A _]. change (- 0) with 0 in A.
  unfold atoi_val. cbn [CType.skip_space].
  replace (CType.c_space b) with false by (unfold CType.c_space; symmetry; apply orb_false_iff; split;
    [apply Z.eqb_neq; lia | apply andb_false_iff; right; apply Z.leb_gt; lia]).
  rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 45)) by lia. rewrite (proj2 (Z.eqb_neq (bv_unsigned b) 43)) by lia.
  rewrite A. rewrite swr_id by lia. lia.
Qed.

Lemma atoi_digits_acc : forall s n, atoi_digits n s = atoi_acc n s.
Proof.
  induction s as [|c s IH]; intros n; [reflexivity|].
  cbn [atoi_digits atoi_acc]. unfold CType.c_digit.
  destruct ((48 <=? bv_unsigned c) && (bv_unsigned c <=? 57)); [apply IH | reflexivity].
Qed.

Lemma atoi_musl_val : forall s, atoi_musl s = atoi_val s.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  unfold atoi_val. cbn [atoi_musl CType.skip_space]. unfold CType.c_space.
  rewrite (orb_comm (bv_unsigned c =? 32)).
  destruct (((9 <=? bv_unsigned c) && (bv_unsigned c <=? 13)) || (bv_unsigned c =? 32)).
  - rewrite IH. reflexivity.
  - rewrite !atoi_digits_acc. reflexivity.
Qed.

Lemma reply_code_pos : forall v, 0 <= v < 2^31 -> reply_code (resp v) = v.
Proof.
  intros v Hv. unfold reply_code.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 (resp v))) [114; 101; 115; 112; 32]) as [_|NE].
  - change (skipn 5 (resp v)) with (dec v). rewrite atoi_musl_val. apply atoi_val_dec. exact Hv.
  - exfalso. apply NE. reflexivity.
Qed.

Lemma firstn_len_app : forall (p rest : list byte), firstn (length p) (p ++ rest) = p.
Proof. induction p as [|c p IH]; intros rest; [reflexivity|]. cbn. f_equal. apply IH. Qed.

Lemma skipn_len_app : forall (p rest : list byte), skipn (length p) (p ++ rest) = rest.
Proof. induction p as [|c p IH]; intros rest; [reflexivity|]. cbn. apply IH. Qed.

Lemma word_len_app : forall p rest, (forall b, In b p -> bz b <> 32) ->
  (match rest with [] => True | b :: _ => bz b = 32 end) -> word_len (p ++ rest) = length p.
Proof.
  induction p as [|c p IH]; intros rest Hp Hr; cbn [app word_len length].
  - destruct rest as [|b rest]; [reflexivity|]. cbn [word_len]. rewrite (proj2 (Z.eqb_eq _ _) Hr). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) (Hp c (or_introl eq_refl))). f_equal. apply IH; [|exact Hr].
    intros b Hb. apply Hp. right. exact Hb.
Qed.

Lemma rmi_word : forall it its p rest, p <> [] -> (forall b, In b p -> bz b <> 32) ->
  (match rest with [] => True | b :: _ => bz b = 32 end) ->
  (has_lt it = true \/ CommandModel.bytes_eqb it p = true) ->
  reply_matches_items (it :: its) (p ++ rest) =
  match rest with [] => reply_matches_items its [] | _ :: [] => false | _ :: r'' => reply_matches_items its r'' end.
Proof.
  intros it its p rest Hn Hp Hr Hi. cbn [reply_matches_items]. rewrite (word_len_app p rest Hp Hr).
  rewrite firstn_len_app, skipn_len_app.
  destruct p as [|c p']; [congruence|]. cbn [Nat.eqb length].
  destruct Hi as [Hi|Hi]; rewrite Hi; [reflexivity|]. rewrite andb_false_r. reflexivity.
Qed.

Lemma reply_matches_add : forall v, 0 <= v < 2^31 -> reply_matches (shape_of Verbs.Lit.verb_add) (resp v) = true.
Proof.
  intros v Hv. unfold reply_matches.
  replace (shape_items (shape_of Verbs.Lit.verb_add)) with [str [114; 101; 115; 112]; str [60; 105; 110; 115; 116; 97; 110; 99; 101; 62]]
    by (vm_compute; reflexivity).
  change (resp v) with (str [114; 101; 115; 112] ++ SPACE :: dec v).
  destruct (dec_pos_facts v ltac:(lia)) as [Hne Hdig].
  assert (Hr : forallb (fun b => negb (bz b =? 32)) (str [114; 101; 115; 112]) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hr.
  rewrite rmi_word; [| cbn; discriminate
                     | intros b Hb; specialize (Hr b Hb); apply negb_true_iff, Z.eqb_neq in Hr; exact Hr
                     | reflexivity | right; vm_compute; reflexivity].
  destruct (dec v) as [|d ds] eqn:E; [congruence|]. cbv iota beta. rewrite <- E in Hne, Hdig |- *.
  replace (dec v) with (dec v ++ []) by apply app_nil_r.
  rewrite rmi_word; [reflexivity | exact Hne
                    | intros b Hb; specialize (Hdig b Hb); unfold bz; lia
                    | exact I | left; vm_compute; reflexivity].
Qed.

Lemma resp_add : forall id, 0 <= id < 10000 ->
  reply_code (resp id) = id /\ reply_matches (shape_of Verbs.Lit.verb_add) (resp id) = true.
Proof. intros id H. split; [apply reply_code_pos; lia | apply reply_matches_add; lia]. Qed.

Lemma reply_ok_add : forall n id, n <> 0 -> 0 <= id < 10000 -> reply_ok n Verbs.Lit.verb_add (resp id).
Proof.
  intros n id Hn H. destruct (resp_add id H) as [E M]. unfold reply_ok. rewrite E. split; [intros; lia|].
  intros _. left. unfold shape_addr. rewrite (proj2 (Z.eqb_neq n 0) Hn). rewrite img_shape. exact M.
Qed.

Lemma resp_add_facts : forall id, 0 <= id < 10000 -> no0 (resp id) /\ Z.of_nat (length (resp id)) <= 28.
Proof. intros id H. pose proof (resp_length id ltac:(lia)). split; [apply resp_no0|lia]. Qed.

(** * The arity check *)

Definition arity_b (t : Z) (v : list byte) (q nc fn0 : Z) : bool :=
  (t =? 0) || (((q =? 0) && (nc =? 0)) || (((0 <? nc) && (fn0 =? 5) && passed_on_m v) ||
  match row_find v parsed_rows with
  | None => true
  | Some (mn, mx) => (mn <=? Z.min t 64 - 1) && (Z.min t 64 - 1 <=? mx)
  end)).

Lemma arity_of_b : forall t v q nc fn0, arity_b t v q nc fn0 = true -> arity_ok t v q nc fn0.
Proof.
  intros t v q nc fn0 H. unfold arity_b in H. unfold arity_ok.
  apply orb_true_iff in H as [H|H]; [left; apply Z.eqb_eq; exact H|right].
  apply orb_true_iff in H as [H|H]; [left; apply andb_true_iff in H as [H1 H2]; split; apply Z.eqb_eq; assumption|right].
  apply orb_true_iff in H as [H|H].
  - left. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. split; [exact H1|split; [exact H2|exact H3]].
  - right. destruct (row_find v parsed_rows) as [[mn mx]|]; [|exact I].
    apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** * The words check *)

Fixpoint items_ok (r : Z) (ws : list (list byte)) (A : list (list byte)) (its : list witem) : Prop :=
  match A, its with
  | x :: A', i :: its' => (match want r ws i with Some y => x = y | None => True end) /\ items_ok r ws A' its'
  | _, _ => True
  end.

Lemma items_ok_nth : forall r ws A its, items_ok r ws A its ->
  forall a x i y, nth_error A a = Some x -> nth_error its a = Some i -> want r ws i = Some y -> x = y.
Proof.
  intros r ws A; induction A as [|x0 A IH]; intros its H a x i y Hx Hi Hy; [destruct a; discriminate|].
  destruct its as [|i0 its]; [destruct a; discriminate|]. destruct H as [H0 H].
  destruct a as [|a]; cbn in Hx, Hi.
  - injection Hx as <-. injection Hi as <-. rewrite Hy in H0. exact H0.
  - exact (IH its H a x i y Hx Hi Hy).
Qed.

Lemma cwo_intro : forall r ws fn A, items_ok r ws A (call_items fn) ->
  (fn = 0 -> length A = 4%nat /\ nth 2 A [] = add_placement r (nth 3 ws []) /\
     nth 3 A [] = add_client r (nth 3 ws []) (nth 4 ws [])) ->
  (fn = 17 -> length A = 3%nat /\ nth 1 A [] = pf_bytes (pf_dec (r - 2)) /\ nth 2 A [] = pf_bytes (chain_list r ws)) ->
  (fn = 20 -> length A = 4%nat /\ nth 3 A [] = pin_verdict r (nth 4 ws [])) ->
  call_words_ok r ws (fn, A).
Proof.
  intros r ws fn A H H0 H17 H20. split; [|split; [exact H0|split; [exact H17|exact H20]]].
  cbn [fst snd]. intros a i x Hx Hi y Hy. exact (items_ok_nth r ws A (call_items fn) H a x i y Hx Hi Hy).
Qed.

(** * Running one message *)

Arguments resp : simpl never.
Arguments inst : simpl never.
Arguments dec : simpl never.
Arguments canon : simpl never.
Arguments join_sp : simpl never.
Arguments mixcall : simpl never.
Arguments shape_of : simpl never.
Arguments bstr : simpl never.
Arguments atoi_val : simpl never.
Arguments reply_code : simpl never.
Arguments pf_bytes : simpl never.
Arguments pf_dec : simpl never.
Arguments Verbs.Lit.lit : simpl never.
Arguments arity_ok : simpl never.
Arguments reply_ok : simpl never.
Arguments words_prop : simpl never.
Arguments call_words_ok : simpl never.
Arguments first_word : simpl never.
Arguments dec_list : simpl never.

Definition fin (R1 : rstate) (x : list byte) (af : option (Z * list byte)) : rstate :=
  let R2 := set_reply R1 (r_nreplies R1 + 1) (Some (x ++ [Z_to_bv 8 0])) in
  match af with Some (i, v) => sup_after_reply_m R2 i (Some v) | None => R2 end.

Definition run_out (R0 : rstate) (st : Verbs.step) (af : option (Z * list byte)) : rstate * list byte * bool :=
  let '(R1, x, q) := VerbsRun.run_step reply_code (rec_clear R0) st in (fin R1 x af, x, q).

Lemma ss_fst : forall R x, fst (socket_send_m R (x ++ [Z_to_bv 8 0])) =
  set_reply R (r_nreplies R + 1) (Some (x ++ [Z_to_bv 8 0])).
Proof. intros R x. unfold socket_send_m, rec_socket_send. destruct x; reflexivity. Qed.

Lemma vr_run_out : forall R0 D, vr_run (rec_clear R0) D =
  run_out R0 (fst (Verbs.receive atoi_val D)) (snd (Verbs.receive atoi_val D)).
Proof.
  intros R0 D. unfold vr_run, VerbsRun.run_receive, run_out.
  destruct (Verbs.receive atoi_val D) as [st af]. cbn [fst snd].
  destruct (VerbsRun.run_step reply_code (rec_clear R0) st) as [[R1 x] q]. cbv beta iota zeta.
  rewrite ss_fst. reflexivity.
Qed.

Definition P4 (R0 : rstate) (ws : list (list byte)) (R1 : rstate) (x : list byte) (quit : bool) : Prop :=
  r_nreplies R1 = 1 /\ r_reply R1 = Some (x ++ [Z_to_bv 8 0]) /\ no0 x /\ Z.of_nat (length x) <= 28 /\
  answer_ok_m (r_answer R1) x (Z.of_nat (length ws)) (nth 0 ws []) /\
  reply_ok (Z.of_nat (length ws)) (nth 0 ws []) x /\
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) (if quit then 1 else 0) (Z.of_nat (length (r_calls R1)))
    (fst (nth 0 (r_calls R1) (0, []))) /\
  words_prop R1 ws /\
  (reply_code x < 0 -> r_state R1 = r_state R0 /\ quit = false).

Definition af_calls (af : option (Z * list byte)) : list rcall :=
  match af with Some (i, v) => [(REC_AFTER_REPLY, [dec i; v])] | None => [] end.

Arguments fin : simpl never.
Arguments P4 : simpl never.

Lemma P4_intro : forall (R0 : rstate) (ws : list (list byte)) (R1 : rstate) (x : list byte) (q : bool)
    (af : option (Z * list byte)),
  (length (r_calls R1) < 16)%nat -> r_nreplies R1 = 0 -> no0 x -> Z.of_nat (length x) <= 28 ->
  answer_ok_m (r_answer R1) x (Z.of_nat (length ws)) (nth 0 ws []) ->
  reply_ok (Z.of_nat (length ws)) (nth 0 ws []) x ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) (if q then 1 else 0) (Z.of_nat (length (r_calls R1 ++ af_calls af)))
    (fst (nth 0 (r_calls R1 ++ af_calls af) (0, []))) ->
  Forall (call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws) (r_calls R1 ++ af_calls af) ->
  (reply_code x < 0 -> r_state R1 = r_state R0 /\ q = false) ->
  P4 R0 ws (fin R1 x af) x q.
Proof.
  intros R0 ws R1 x q af L N Z0 LX A RP AR W RF.
  assert (C : r_calls (fin R1 x af) = r_calls R1 ++ af_calls af).
  { unfold fin. destruct af as [[i v]|]; [|cbn; rewrite app_nil_r; reflexivity].
    unfold sup_after_reply_m. rewrite rec_record_calls by (cbn; exact L). reflexivity. }
  assert (F : r_nreplies (fin R1 x af) = r_nreplies R1 + 1 /\ r_reply (fin R1 x af) = Some (x ++ [Z_to_bv 8 0]) /\
              r_answer (fin R1 x af) = r_answer R1 /\ r_state (fin R1 x af) = r_state R1).
  { unfold fin. destruct af as [[i v]|]; [unfold sup_after_reply_m, rec_record; destruct (Nat.ltb _ 16)|];
      cbn; repeat split. }
  destruct F as (F1 & F2 & F3 & F4).
  unfold P4, words_prop. cbv zeta. rewrite C, F1, F2, F3, F4, N.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Z0|]. split; [exact LX|].
  split; [exact A|]. split; [exact RP|]. split; [exact AR|]. split; [exact W|]. exact RF.
Qed.

Lemma shape_set_inst : forall s, In s shape_set ->
  0 <= reply_code (inst s) /\ no0 (inst s) /\ Z.of_nat (length (inst s)) <= 28.
Proof.
  intros s Hs. pose proof sh_all as A. rewrite forallb_forall in A. specialize (A s Hs).
  unfold sh_ok in A. repeat rewrite andb_true_iff in A. destruct A as [[[A1 _] A3] A4].
  apply Z.leb_le in A1. apply no0_nz in A3. apply Z.leb_le in A4. repeat split; assumption.
Qed.

Lemma decl_of : forall R0, (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> (r_refuse R0 =? 0) = false ->
  declared (r_code R0) = true.
Proof. intros R0 H E. apply H. apply Z.eqb_neq. exact E. Qed.

Lemma P4_stub : forall R0 ws c af fn A shape changes,
  VerbsRun.run_call (rec_clear R0) c = rec_stub (rec_clear R0) fn A shape changes ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  In shape shape_set ->
  reply_ok (Z.of_nat (length ws)) (nth 0 ws []) (inst shape) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 (Z.of_nat (S (length (af_calls af)))) fn ->
  Forall (call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws) ((fn, A) :: af_calls af) ->
  let '(R1, x, q) := run_out R0 (Verbs.SCall c) af in P4 R0 ws R1 x q.
Proof.
  intros R0 ws c af fn A shape changes Hc Hd Hs Hr Ha Hw.
  destruct (shape_set_inst shape Hs) as (S1 & S2 & S3).
  unfold run_out. cbn [VerbsRun.run_step]. rewrite Hc. unfold rec_stub, rec_answer, hand_back. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0.
  - destruct changes; cbn; apply P4_intro; cbn;
      first [lia | reflexivity | exact S2 | exact S3 | exact Hr | exact Ha | exact Hw | intros ?; exfalso; lia].
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts _ Dc) as (D1 & D2 & D3 & D4).
    cbn. apply P4_intro; cbn;
      first [lia | reflexivity | exact D1 | exact D2 | (apply reply_ok_neg; exact Dc) | exact Ha | exact Hw
            | (intros _; split; reflexivity)].
Qed.

Lemma P4_rej : forall R0 ws, let '(R1, x, q) := run_out R0 Verbs.reject None in P4 R0 ws R1 x q.
Proof.
  intros R0 ws. assert (D : declared (-902) = true) by reflexivity.
  destruct (resp_declared_facts _ D) as (D1 & D2 & D3 & D4).
  unfold run_out, Verbs.reject, Verbs.err_invalid_operation. cbn. apply P4_intro; cbn.
  - lia.
  - reflexivity.
  - exact D1.
  - exact D2.
  - left. rewrite D3. lia.
  - apply reply_ok_neg. exact D.
  - unfold arity_ok. right. left. split; reflexivity.
  - constructor.
  - intros _. split; reflexivity.
Qed.

Lemma P4_quit : forall R0, let '(R1, x, q) := run_out R0 Verbs.SQuit None in P4 R0 [Verbs.Lit.verb_quit] R1 x q.
Proof.
  intros R0. destruct resp0_facts as (Q1 & Q2 & Q3).
  unfold run_out. cbn. apply P4_intro; cbn.
  - lia.
  - reflexivity.
  - exact Q2.
  - exact Q3.
  - right. split; [reflexivity|]. apply bl_eqb_eq. vm_compute. reflexivity.
  - apply reply_ok_resp0.
  - apply arity_of_b. vm_compute. reflexivity.
  - constructor.
  - intros H. rewrite Q1 in H. lia.
Qed.

Lemma P4_add : forall R0 ws u i p q,
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  Z.of_nat (length ws) <> 0 -> nth 0 ws [] = Verbs.Lit.verb_add ->
  arity_ok (Z.of_nat (length ws)) Verbs.Lit.verb_add 0 1 0 ->
  arity_ok (Z.of_nat (length ws)) Verbs.Lit.verb_add 0 2 0 ->
  call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws (0, [u; dec (atoi_val i); darg p S_DASH; darg q S_DASH]) ->
  call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws (22, [u]) ->
  let '(R1, x, q') := run_out R0 (Verbs.SAdd u (atoi_val i) p q) None in P4 R0 ws R1 x q'.
Proof.
  intros R0 ws u i p q Hd Hn H0 A1 A2 W1 W2.
  unfold run_out. cbn [VerbsRun.run_step]. unfold sup_add_m, hand_back. cbn.
  destruct ((atoi_val i <? 0) || (10000 <=? atoi_val i)) eqn:Hid.
  - assert (D : declared (-1) = true) by reflexivity.
    destruct (resp_declared_facts _ D) as (D1 & D2 & D3 & D4).
    cbn. rewrite D3. cbn. apply P4_intro; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg. exact D.
    + rewrite H0. exact A1.
    + apply Forall_cons; [exact W1|apply Forall_nil].
    + intros _. split; reflexivity.
  - apply orb_false_iff in Hid as [Hid1 Hid2]. apply Z.ltb_ge in Hid1. apply Z.leb_gt in Hid2.
    destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
    + destruct (resp_add (atoi_val i) ltac:(lia)) as [E M]. rewrite E.
      replace (0 <=? atoi_val i) with true by (symmetry; apply Z.leb_le; lia). cbn.
      destruct (resp_add_facts (atoi_val i) ltac:(lia)) as [F1 F2].
      apply P4_intro; cbn.
      * lia.
      * reflexivity.
      * exact F1.
      * exact F2.
      * reflexivity.
      * rewrite H0. apply reply_ok_add; [exact Hn | lia].
      * rewrite H0. exact A2.
      * apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
      * rewrite E. intros H; exfalso; lia.
    + pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts _ Dc) as (D1 & D2 & D3 & D4).
      rewrite D3. replace (0 <=? r_code R0) with false by (symmetry; apply Z.leb_gt; lia). cbn.
      apply P4_intro; cbn.
      * lia.
      * reflexivity.
      * exact D1.
      * exact D2.
      * reflexivity.
      * apply reply_ok_neg. exact Dc.
      * rewrite H0. exact A1.
      * apply Forall_cons; [exact W1|apply Forall_nil].
      * intros _. split; reflexivity.
Qed.

Lemma cwo_forget : forall r ws A, call_words_ok r ws (REC_LV2_REFUSALS_FORGET, A).
Proof.
  intros r ws A. apply cwo_intro; [|intros E; discriminate E ..].
  change (call_items REC_LV2_REFUSALS_FORGET) with [IStar].
  destruct A as [|x [|y A]]; cbn; repeat split.
Qed.

Lemma P4_pins : forall R0 ws st fn A,
  VerbsRun.run_step reply_code (rec_clear R0) st =
    (let '(R1, rc) := rec_stub_code (rec_clear R0) fn A in (VerbsRun.pins_follow R1 rc, false)) ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 1 fn ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 2 fn ->
  call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws (fn, A) ->
  let '(R1, x, q) := run_out R0 st None in P4 R0 ws R1 x q.
Proof.
  intros R0 ws st fn A Hst Hd A1 A2 W. destruct resp0_facts as (Q1 & Q2 & Q3).
  unfold run_out. rewrite Hst. unfold rec_stub_code, rec_answer_code, VerbsRun.pins_follow,
    lv2_refusals_forget_m, rec_stub_mix. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
  - apply P4_intro; cbn.
    + lia.
    + reflexivity.
    + exact Q2.
    + exact Q3.
    + reflexivity.
    + apply reply_ok_resp0.
    + exact A2.
    + apply Forall_cons; [exact W|apply Forall_cons; [apply cwo_forget|apply Forall_nil]].
    + rewrite Q1. intros H; exfalso; lia.
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts _ Dc) as (D1 & D2 & D3 & D4).
    replace (r_code R0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    apply P4_intro; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg. exact Dc.
    + exact A1.
    + apply Forall_cons; [exact W|apply Forall_nil].
    + intros _. split; reflexivity.
Qed.

Lemma P4_bc : forall R0 ws ln tk,
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 2 5 ->
  call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws (5, [canon ln]) ->
  call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws (6, [canon ln; dec (Z.of_nat (length tk)); join_sp tk]) ->
  let '(R1, x, q) := run_out R0 (Verbs.SBroadcast ln tk) None in P4 R0 ws R1 x q.
Proof.
  intros R0 ws ln tk Hd A2 W1 W2. destruct resp0_facts as (Q1 & Q2 & Q3).
  unfold run_out. cbn [VerbsRun.run_step]. unfold sup_broadcast_m, sup_host_setting_m, rec_stub, rec_answer,
    hand_back, rec_mix_host. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
  - rewrite inst_host. apply P4_intro; cbn.
    + lia.
    + reflexivity.
    + exact Q2.
    + exact Q3.
    + reflexivity.
    + apply reply_ok_resp0.
    + exact A2.
    + apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
    + rewrite Q1. intros H; exfalso; lia.
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts _ Dc) as (D1 & D2 & D3 & D4).
    apply P4_intro; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg. exact Dc.
    + exact A2.
    + apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
    + intros _. split; reflexivity.
Qed.

(** * Words facts per verb *)

Ltac znat := repeat match goal with |- context [Z.to_nat ?k] =>
  let v := eval vm_compute in (Z.to_nat k) in change (Z.to_nat k) with v end.

Lemma placement_eq : forall x, is_placement_b x = Verbs.is_placement_m x.
Proof.
  intros x. unfold is_placement_b, Verbs.is_placement_m, prefixb, Verbs.has_prefix.
  rewrite !list_eqb_bl. change CommandModel.bytes_eqb with bl_eqb.
  change Verbs.Lit.place_own with S_OWN. change Verbs.Lit.place_default with S_DEFAULT.
  change Verbs.Lit.place_pool_prefix with S_POOL.
  f_equal. change (length S_POOL) with 5%nat.
  destruct (Nat.leb_spec 5 (length x)) as [L|L]; [reflexivity|].
  destruct (bl_eqb (firstn 5 x) S_POOL) eqn:E; [|reflexivity].
  apply bl_eqb_eq in E. apply (f_equal (@length _)) in E. rewrite length_firstn in E.
  change (length S_POOL) with 5%nat in E. lia.
Qed.

Lemma placement_not_dash : forall x, Verbs.is_placement_m x = true -> CommandModel.bytes_eqb x S_DASH = false.
Proof.
  intros x H. destruct (CommandModel.bytes_eqb x S_DASH) eqn:E; [|reflexivity].
  rewrite cm_bytes_eqb in E. apply bl_eqb_eq in E. subst x. vm_compute in H. discriminate H.
Qed.

Lemma add_pl_yes : forall r x, 3 < r -> Verbs.is_placement_m x = true -> add_placement r x = x /\ add_next r x = 4.
Proof.
  intros r x Hr H. assert (P : add_placement r x = x).
  { unfold add_placement. rewrite placement_eq, H, (proj2 (Z.ltb_lt 3 r) Hr). reflexivity. }
  split; [exact P|]. unfold add_next. rewrite P, (placement_not_dash x H). reflexivity.
Qed.

Lemma add_pl_no : forall r x, Verbs.is_placement_m x = false \/ r <= 3 ->
  add_placement r x = S_DASH /\ add_next r x = 3.
Proof.
  intros r x H. assert (P : add_placement r x = S_DASH).
  { unfold add_placement. destruct H as [H|H]; [rewrite placement_eq, H, andb_false_r; reflexivity|].
    rewrite (proj2 (Z.ltb_ge 3 r) H). reflexivity. }
  split; [exact P|]. unfold add_next. rewrite P. reflexivity.
Qed.

Definition add_part (r : Z) (ws A : list (list byte)) : Prop :=
  length A = 4%nat /\ nth 2 A [] = add_placement r (nth 3 ws []) /\
  nth 3 A [] = add_client r (nth 3 ws []) (nth 4 ws []).

Lemma addw2 : forall u i, add_part 3 [Verbs.Lit.verb_add; u; i] [u; dec (atoi_val i); S_DASH; S_DASH].
Proof.
  intros u i. destruct (add_pl_no 3 [] (or_intror (Z.le_refl 3))) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw3p : forall u i x, Verbs.is_placement_m x = true ->
  add_part 4 [Verbs.Lit.verb_add; u; i; x] [u; dec (atoi_val i); x; S_DASH].
Proof.
  intros u i x H. destruct (add_pl_yes 4 x ltac:(lia) H) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw3c : forall u i x, Verbs.is_placement_m x = false ->
  add_part 4 [Verbs.Lit.verb_add; u; i; x] [u; dec (atoi_val i); S_DASH; x].
Proof.
  intros u i x H. destruct (add_pl_no 4 x (or_introl H)) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw4 : forall u i x y, Verbs.is_placement_m x = true ->
  add_part 5 [Verbs.Lit.verb_add; u; i; x; y] [u; dec (atoi_val i); x; y].
Proof.
  intros u i x y H. destruct (add_pl_yes 5 x ltac:(lia) H) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma prefix_verdict : forall vd, Verbs.has_prefix Verbs.Lit.word_verdict vd = true -> prefixb vd S_VERDICT = true.
Proof.
  intros vd H. unfold Verbs.has_prefix in H. apply andb_true_iff in H as [_ H]. rewrite list_eqb_bl in H.
  unfold prefixb. rewrite cm_bytes_eqb. change S_VERDICT with Verbs.Lit.word_verdict. exact H.
Qed.

Fixpoint ci (first : bool) (l : list (list byte)) : list Z :=
  match l with
  | [] => []
  | w :: l' => (if first then [] else [32]) ++ pf_dec (atoi_val w) ++ ci false l'
  end.

Lemma chain_items_ci : forall l k ws, (2 <= k)%nat ->
  (forall j, (j < length l)%nat -> nth (k + j) ws [] = nth j l []) ->
  chain_items k (length l) ws = ci (Nat.eqb k 2) l.
Proof.
  induction l as [|w l IH]; intros k ws Hk H; [reflexivity|].
  cbn [length chain_items ci].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. rewrite Nat.add_0_r in H0. cbn [nth] in H0. rewrite H0.
  rewrite (IH (S k) ws ltac:(lia)).
  - replace (Nat.eqb (S k) 2) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  - intros j Hj. replace (S k + j)%nat with (k + S j)%nat by lia. apply (H (S j)). cbn [length]. lia.
Qed.

Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros a b. apply map_app. Qed.

Lemma ci_false : forall l, pf_bytes (ci false l) = concat (map (fun j => SPACE :: dec j) (map atoi_val l)).
Proof.
  induction l as [|w l IH]; [reflexivity|]. cbn [ci map concat].
  rewrite !pf_bytes_app, IH, dec_atoi. reflexivity.
Qed.

Lemma chain_ok : forall ws c a rest, c :: a :: rest = firstn 64 ws -> rest <> [] ->
  dec_list (map atoi_val rest) = pf_bytes (chain_list (Z.of_nat (length (c :: a :: rest))) ws).
Proof.
  intros ws c a rest Hws Hne. unfold chain_list.
  replace (Z.to_nat (Z.of_nat (length (c :: a :: rest)) - 2)) with (length rest) by (cbn [length]; lia).
  rewrite (chain_items_ci rest 2 ws ltac:(lia)).
  - destruct rest as [|w rest']; [congruence|]. cbn [ci map Nat.eqb].
    rewrite !pf_bytes_app, ci_false, dec_atoi. reflexivity.
  - intros j Hj. rewrite (firstn64_nth ws (c :: a :: rest) (2 + j) Hws) by (cbn [length]; lia). reflexivity.
Qed.

Lemma ws_facts : forall (ws : list (list byte)) v rest, v :: rest = firstn 64 ws ->
  nth 0 ws [] = v /\ Z.of_nat (length ws) <> 0 /\ Z.min (Z.of_nat (length ws)) 64 = Z.of_nat (length (v :: rest)).
Proof.
  intros ws v rest H. split; [rewrite (firstn64_nth ws (v :: rest) 0 H) by (cbn; lia); reflexivity|].
  pose proof (firstn64_len ws (v :: rest) H) as L. split; [cbn [length] in L; lia | exact L].
Qed.

Lemma ws_nth1 : forall (ws : list (list byte)) v a rest, v :: a :: rest = firstn 64 ws -> nth 1 ws [] = a.
Proof. intros ws v a rest H. rewrite (firstn64_nth ws _ 1 H) by (cbn; lia). reflexivity. Qed.

Lemma after_cwo : forall ws tk, tk = firstn 64 ws ->
  Forall (call_words_ok (Z.min (Z.of_nat (length ws)) 64) ws) (af_calls (Verbs.after atoi_val tk)).
Proof.
  intros ws tk Hws. destruct tk as [|v [|a rest]]; try apply Forall_nil.
  unfold Verbs.after.
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load || Verbs.verb_is_m v Verbs.Lit.fmt_patch_set);
    [|apply Forall_nil].
  cbn [af_calls]. apply Forall_cons; [|apply Forall_nil].
  destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
  apply cwo_intro; [|intros E; discriminate E ..].
  change (call_items REC_AFTER_REPLY) with [INum 1; IWord 0]. cbn [items_ok want]. rewrite Hr.
  replace (1 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
  replace (0 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
  cbv beta iota. znat. rewrite Hn1, Hn0. split; [symmetry; apply dec_atoi | split; [reflexivity | exact I]].
Qed.

Lemma arity_afree_gen : forall t v nc, 0 < nc -> (row_find v parsed_rows = None \/ passed_on_m v = true) ->
  arity_ok t v 0 nc 5.
Proof.
  intros t v nc Hn [H|H]; unfold arity_ok; right; right;
    [right; rewrite H; exact I|left; split; [exact Hn|split; [reflexivity|exact H]]].
Qed.

Lemma arity_row_none : forall t v q nc fn, row_find v parsed_rows = None -> arity_ok t v q nc fn.
Proof. intros t v q nc fn H. unfold arity_ok. right; right; right. rewrite H. exact I. Qed.

(** * The plan, verb by verb *)

Definition tokp (t : list byte) : Prop := forall b, In b t -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9.
Definition afree (v : list byte) : Prop := row_find v parsed_rows = None \/ passed_on_m v = true.

Definition early (v : list byte) : bool :=
  Verbs.list_eqb v Verbs.Lit.verb_add || Verbs.list_eqb v Verbs.Lit.verb_descriptor_get ||
  Verbs.list_eqb v Verbs.Lit.verb_panel_get || Verbs.verb_is_m v Verbs.Lit.fmt_remove ||
  Verbs.list_eqb v Verbs.Lit.verb_worker_list || Verbs.list_eqb v Verbs.Lit.verb_instance_info ||
  Verbs.list_eqb v Verbs.Lit.verb_supervisor_reset || Verbs.list_eqb v Verbs.Lit.verb_quarantine_clear ||
  Verbs.list_eqb v Verbs.Lit.verb_policy_set || Verbs.list_eqb v Verbs.Lit.verb_lv2_worker_set ||
  Verbs.list_eqb v Verbs.Lit.verb_pool_config || Verbs.list_eqb v Verbs.Lit.verb_worker_env ||
  Verbs.list_eqb v Verbs.Lit.verb_chain || Verbs.list_eqb v Verbs.Lit.verb_chain_clear ||
  Verbs.list_eqb v Verbs.Lit.verb_pin_set || Verbs.list_eqb v Verbs.Lit.verb_pin_accept ||
  Verbs.list_eqb v Verbs.Lit.verb_pin_clear || Verbs.verb_is_m v Verbs.Lit.fmt_quit.

Lemma afree_of : forall v, early v = false -> afree v.
Proof.
  intros v H. unfold afree. destruct (row_find v parsed_rows) as [p|] eqn:E; [right|left; reflexivity].
  cbn [row_find parsed_rows] in E.
  repeat match type of E with
  | (if ?c then _ else _) = _ =>
      let B := fresh "B" in destruct c eqn:B;
      [apply bl_eqb_eq in B; subst v; vm_compute in H; first [discriminate H | vm_compute; reflexivity]
      | cbv iota in E]
  end.
  discriminate E.
Qed.

Lemma after_none : forall v args,
  (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load || Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) = false ->
  Verbs.after atoi_val (v :: args) = None.
Proof. intros v [|a args] H; [reflexivity|]. unfold Verbs.after. rewrite H. reflexivity. Qed.

Lemma after_bc : forall v args, tokp v -> Verbs.is_instance_verb v = false -> Verbs.after atoi_val (v :: args) = None.
Proof.
  intros v [|a args] Tv H; [reflexivity|]. unfold Verbs.after.
  destruct Verbs.format_words as (_ & _ & _ & _ & FW5 & FW6).
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load) eqn:E1.
  { apply (Verbs.verb_is_m_token v _ Tv) in E1. rewrite FW5 in E1. subst v. vm_compute in H. discriminate H. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) eqn:E2.
  { apply (Verbs.verb_is_m_token v _ Tv) in E2. rewrite FW6 in E2. subst v. vm_compute in H. discriminate H. }
  reflexivity.
Qed.

Lemma inst_row_none : forall v, tokp v -> Verbs.is_instance_verb v = true -> row_find v parsed_rows = None.
Proof.
  intros v Tv H. unfold Verbs.is_instance_verb in H. apply existsb_exists in H as (f & Hf & Ev).
  apply (Verbs.verb_is_m_token v f Tv) in Ev. subst v.
  unfold Verbs.Lit.instance_verb_formats in Hf. apply in_map_iff in Hf as (s & <- & Hs).
  repeat (destruct Hs as [<-|Hs]; [vm_compute; reflexivity|]). destruct Hs.
Qed.

Lemma ledger_row_none : forall v led, Verbs.ledger_of v Verbs.Lit.instance_info_verbs = Some led ->
  row_find v parsed_rows = None.
Proof.
  intros v led H. cbn [Verbs.ledger_of Verbs.Lit.instance_info_verbs] in H.
  repeat match type of H with
  | (if Verbs.list_eqb v ?n then _ else _) = _ =>
      let B := fresh "B" in destruct (Verbs.list_eqb v n) eqn:B;
      [apply Verbs.list_eqb_eq in B; subst v; vm_compute; reflexivity | cbv iota in H]
  end.
  discriminate H.
Qed.

Inductive pspec (ln : list byte) : list (list byte) -> Verbs.step -> option (Z * list byte) -> Prop :=
| p_rej : forall tk, pspec ln tk Verbs.reject None
| p_add2 : forall u i, pspec ln [Verbs.Lit.verb_add; u; i] (Verbs.SAdd u (atoi_val i) None None) None
| p_add3p : forall u i x, Verbs.is_placement_m x = true ->
    pspec ln [Verbs.Lit.verb_add; u; i; x] (Verbs.SAdd u (atoi_val i) (Some x) None) None
| p_add3c : forall u i x, Verbs.is_placement_m x = false ->
    pspec ln [Verbs.Lit.verb_add; u; i; x] (Verbs.SAdd u (atoi_val i) None (Some x)) None
| p_add4 : forall u i x y, Verbs.is_placement_m x = true ->
    pspec ln [Verbs.Lit.verb_add; u; i; x; y] (Verbs.SAdd u (atoi_val i) (Some x) (Some y)) None
| p_dget : forall a, pspec ln [Verbs.Lit.verb_descriptor_get; a] (Verbs.SCall (Verbs.descriptors_get a)) None
| p_pget : forall a, pspec ln [Verbs.Lit.verb_panel_get; a] (Verbs.SCall (Verbs.descriptors_panel_get a)) None
| p_remall : forall a, pspec ln [Verbs.Lit.verb_remove; a] (Verbs.SCall Verbs.sup_remove_all) None
| p_rem : forall a, pspec ln [Verbs.Lit.verb_remove; a] (Verbs.SCall (Verbs.sup_remove (atoi_val a))) None
| p_wlist : pspec ln [Verbs.Lit.verb_worker_list] (Verbs.SCall Verbs.sup_worker_list) None
| p_iinfo : forall a,
    pspec ln [Verbs.Lit.verb_instance_info; a] (Verbs.SCall (Verbs.sup_instance_info (atoi_val a))) None
| p_reset0 : pspec ln [Verbs.Lit.verb_supervisor_reset] (Verbs.SCall (Verbs.sup_reset Verbs.Lit.word_all)) None
| p_reset1 : forall a, pspec ln [Verbs.Lit.verb_supervisor_reset; a] (Verbs.SCall (Verbs.sup_reset a)) None
| p_qclear : forall a,
    pspec ln [Verbs.Lit.verb_quarantine_clear; a] (Verbs.SCall (Verbs.sup_quarantine_clear a)) None
| p_policy : forall a b, pspec ln [Verbs.Lit.verb_policy_set; a; b] (Verbs.SCall (Verbs.sup_policy_set a b)) None
| p_lv2 : forall a b,
    pspec ln [Verbs.Lit.verb_lv2_worker_set; a; b] (Verbs.SCall (Verbs.sup_lv2_worker_set a b)) None
| p_pool : forall a b,
    pspec ln [Verbs.Lit.verb_pool_config; a; b] (Verbs.SCall (Verbs.sup_pool_config a (atoi_val b))) None
| p_env : forall a b c,
    pspec ln [Verbs.Lit.verb_worker_env; a; b; c] (Verbs.SCall (Verbs.sup_worker_env a b c)) None
| p_chain : forall a rest id ids, rest <> [] -> Verbs.number_m a = Some id -> Verbs.numbers_m rest = Some ids ->
    pspec ln (Verbs.Lit.verb_chain :: a :: rest) (Verbs.SCall (Verbs.sup_chain id ids)) None
| p_cclear : forall a id, Verbs.number_m a = Some id ->
    pspec ln [Verbs.Lit.verb_chain_clear; a] (Verbs.SCall (Verbs.sup_chain_clear id)) None
| p_pin3 : forall u f l, pspec ln [Verbs.Lit.verb_pin_set; u; f; l] (Verbs.SPinSet u f l None) None
| p_pin4 : forall u f l vd, Verbs.has_prefix Verbs.Lit.word_verdict vd = true ->
    pspec ln [Verbs.Lit.verb_pin_set; u; f; l; vd] (Verbs.SPinSet u f l (Some (skipn 8 vd))) None
| p_paccept : forall a, pspec ln [Verbs.Lit.verb_pin_accept; a] (Verbs.SCall (Verbs.sup_pin_accept a)) None
| p_pclear : forall a, pspec ln [Verbs.Lit.verb_pin_clear; a] (Verbs.SPinClear a) None
| p_quit : pspec ln [Verbs.Lit.verb_quit] Verbs.SQuit None
| p_ledger : forall v args led, Verbs.ledger_of v Verbs.Lit.instance_info_verbs = Some led ->
    pspec ln (v :: args) (Verbs.SCall (Verbs.sup_instance_verb ln led)) (Verbs.after atoi_val (v :: args))
| p_bc0 : forall v, afree v -> pspec ln [v] (Verbs.SBroadcast ln [v]) None
| p_call : forall v a rest, row_find v parsed_rows = None ->
    pspec ln (v :: a :: rest) (Verbs.SCall (Verbs.sup_call (atoi_val a) ln)) (Verbs.after atoi_val (v :: a :: rest))
| p_conn : forall v a b, v = Verbs.Lit.verb_connect \/ v = Verbs.Lit.verb_disconnect ->
    pspec ln [v; a; b] (Verbs.SCall (Verbs.sup_connect v ln a b)) None
| p_bc : forall v a rest, afree v -> pspec ln (v :: a :: rest) (Verbs.SBroadcast ln (v :: a :: rest)) None.

Ltac dif := match goal with |- context [if ?c then _ else _] => destruct c eqn:? end.

Lemma pspec_holds : forall ln tk, (forall t, In t tk -> tokp t) ->
  pspec ln tk (Verbs.plan atoi_val ln tk) (Verbs.after atoi_val tk).
Proof.
  intros ln tk Htk. destruct tk as [|v args]; [apply p_rej|].
  assert (Tv : tokp v) by (apply Htk; left; reflexivity).
  destruct Verbs.format_words as (FW1 & FW2 & FW3 & FW4 & FW5 & FW6).
  unfold Verbs.plan.
  destruct (Verbs.list_eqb v Verbs.Lit.verb_add) eqn:E1.
  { apply Verbs.list_eqb_eq in E1. subst v. rewrite after_none by (vm_compute; reflexivity).
    unfold Verbs.add_m. destruct args as [|u [|i [|x [|y [|z rest]]]]]; cbv beta iota; try apply p_rej.
    - apply p_add2.
    - destruct (Verbs.is_placement_m x) eqn:P; [apply p_add3p | apply p_add3c]; exact P.
    - destruct (Verbs.is_placement_m x) eqn:P; [apply p_add4; exact P | apply p_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_descriptor_get) eqn:E2.
  { apply Verbs.list_eqb_eq in E2. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_dget. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_panel_get) eqn:E3.
  { apply Verbs.list_eqb_eq in E3. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_pget. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_remove) eqn:E4.
  { apply (Verbs.verb_is_m_token v _ Tv) in E4. rewrite FW1 in E4. subst v.
    rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej.
    destruct (atoi_val a =? -1); [apply p_remall | apply p_rem]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_worker_list) eqn:E5.
  { apply Verbs.list_eqb_eq in E5. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a rest]; cbv beta iota; try apply p_rej. apply p_wlist. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_instance_info) eqn:E6.
  { apply Verbs.list_eqb_eq in E6. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_iinfo. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_supervisor_reset) eqn:E7.
  { apply Verbs.list_eqb_eq in E7. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej; [apply p_reset0 | apply p_reset1]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_quarantine_clear) eqn:E8.
  { apply Verbs.list_eqb_eq in E8. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_qclear. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_policy_set) eqn:E9.
  { apply Verbs.list_eqb_eq in E9. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply p_rej. apply p_policy. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_lv2_worker_set) eqn:E10.
  { apply Verbs.list_eqb_eq in E10. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply p_rej. apply p_lv2. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pool_config) eqn:E11.
  { apply Verbs.list_eqb_eq in E11. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c rest]]]; cbv beta iota; try apply p_rej. apply p_pool. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_worker_env) eqn:E12.
  { apply Verbs.list_eqb_eq in E12. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b [|c [|d rest]]]]; cbv beta iota; try apply p_rej. apply p_env. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain) eqn:E13.
  { apply Verbs.list_eqb_eq in E13. subst v. rewrite after_none by (vm_compute; reflexivity).
    unfold Verbs.chain_words_m. destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej.
    destruct (Verbs.number_m a) as [id|] eqn:N1; [|apply p_rej].
    destruct (Verbs.numbers_m (b :: rest)) as [ids|] eqn:N2; [|apply p_rej].
    apply p_chain; [discriminate|exact N1|exact N2]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain_clear) eqn:E14.
  { apply Verbs.list_eqb_eq in E14. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej.
    destruct (Verbs.number_m a) as [id|] eqn:N; [apply p_cclear; exact N|apply p_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set) eqn:E15.
  { apply Verbs.list_eqb_eq in E15. subst v. rewrite after_none by (vm_compute; reflexivity).
    unfold Verbs.pin_set_words_m. destruct args as [|u [|f [|l [|vd [|z rest]]]]]; cbv beta iota; try apply p_rej.
    - dif; [apply p_rej|apply p_pin3].
    - dif; [apply p_rej|]. dif; [apply p_pin4; assumption|apply p_rej]. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_accept) eqn:E16.
  { apply Verbs.list_eqb_eq in E16. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_paccept. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_clear) eqn:E17.
  { apply Verbs.list_eqb_eq in E17. subst v. rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a [|b rest]]; cbv beta iota; try apply p_rej. apply p_pclear. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_quit) eqn:E18.
  { apply (Verbs.verb_is_m_token v _ Tv) in E18. rewrite FW2 in E18. subst v.
    rewrite after_none by (vm_compute; reflexivity).
    destruct args as [|a rest]; cbv beta iota; try apply p_rej. apply p_quit. }
  assert (EV : early v = false) by (unfold early; rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12,
    E13, E14, E15, E16, E17, E18; reflexivity).
  destruct (Verbs.ledger_of v Verbs.Lit.instance_info_verbs) as [led|] eqn:EL; [apply p_ledger; exact EL|].
  destruct args as [|a rest]; [apply p_bc0; apply afree_of; exact EV|].
  destruct (Verbs.is_instance_verb v) eqn:EI; [apply p_call; apply inst_row_none; assumption|].
  rewrite (after_bc v (a :: rest) Tv EI).
  destruct rest as [|b [|c rest']]; [apply p_bc; apply afree_of; exact EV| |apply p_bc; apply afree_of; exact EV].
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_connect || Verbs.verb_is_m v Verbs.Lit.fmt_disconnect) eqn:EC;
    [|apply p_bc; apply afree_of; exact EV].
  apply p_conn. apply orb_true_iff in EC. destruct EC as [EC|EC]; apply (Verbs.verb_is_m_token v _ Tv) in EC;
    [left; rewrite <- FW3 | right; rewrite <- FW4]; exact EC.
Qed.

Lemma receive_spec : forall D,
  pspec (Verbs.line D) (Verbs.toks D) (fst (Verbs.receive atoi_val D)) (snd (Verbs.receive atoi_val D)).
Proof.
  intros D. unfold Verbs.receive. destruct (Verbs.toks D) as [|t tl] eqn:Et; [apply p_rej|].
  apply pspec_holds. intros t' Ht'. rewrite <- Et in Ht'. destruct (Verbs.toks_word D t' Ht') as [_ H].
  intros b Hb. destruct (H b Hb) as (H1 & H2 & _). split; assumption.
Qed.

(** * The four per-message checks *)

Ltac itac Hc := cbn; repeat apply conj; first [exact I | exact Hc | (symmetry; apply dec_atoi) | reflexivity].
Ltac c1 Hc := apply cwo_intro; [itac Hc | intros E; discriminate E ..].
Ltac w1 Hc := apply Forall_cons; [c1 Hc | apply Forall_nil].
Ltac fixws Hws := let E := fresh "Ews" in pose proof (firstn64_small _ _ Hws ltac:(cbn; lia)) as E;
  match type of E with ?w = _ => subst w end.
Ltac arc := apply arity_of_b; vm_compute; reflexivity.
Ltac rdae := unfold daemon_shape; rewrite <- lit_bstr; apply reply_ok_shape; cbn; lia.
Ltac rhost := rewrite inst_host; apply reply_ok_resp0.
Ltac stubc Hd Hc := eapply P4_stub; [reflexivity | exact Hd | first [left; reflexivity | apply shape_of_in]
  | first [rhost | rdae] | arc | w1 Hc].

Lemma P4_spec : forall R0 ws ln tk st af, pspec ln tk st af -> tk = firstn 64 ws -> canon ln = join_sp ws ->
  first_word ln = nth 0 ws [] -> (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  let '(R1, x, q) := run_out R0 st af in P4 R0 ws R1 x q.
Proof.
  intros R0 ws ln tk st af HP.
  destruct HP as [tk|u i|u i x H|u i x H|u i x y H|a|a|a|a| |a| |a|a|a b|a b|a b|a b c
                 |a rest id ids H H0 H1|a id H|u f l|u f l vd H|a|a| |v args led H|v H|v a rest H|v a b H
                 |v a rest H]; intros Hws Hc Hf Hd.
  - (* reject *) apply P4_rej.
  - (* add u i *) fixws Hws. apply P4_add; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1 Hc].
    apply cwo_intro; [itac Hc | intros _; exact (addw2 u i) | intros E; discriminate E ..].
  - (* add u i placement *) fixws Hws. apply P4_add; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1 Hc].
    apply cwo_intro; [itac Hc | intros _; exact (addw3p u i x H) | intros E; discriminate E ..].
  - (* add u i client *) fixws Hws. apply P4_add; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1 Hc].
    apply cwo_intro; [itac Hc | intros _; exact (addw3c u i x H) | intros E; discriminate E ..].
  - (* add u i placement client *) fixws Hws. apply P4_add; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1 Hc].
    apply cwo_intro; [itac Hc | intros _; exact (addw4 u i x y H) | intros E; discriminate E ..].
  - (* descriptor_get *) fixws Hws. stubc Hd Hc.
  - (* panel_get *) fixws Hws. stubc Hd Hc.
  - (* remove all *) fixws Hws. stubc Hd Hc.
  - (* remove *) fixws Hws. stubc Hd Hc.
  - (* worker_list *) fixws Hws. stubc Hd Hc.
  - (* instance_info *) fixws Hws. stubc Hd Hc.
  - (* supervisor_reset *) fixws Hws. stubc Hd Hc.
  - (* supervisor_reset which *) fixws Hws. stubc Hd Hc.
  - (* quarantine_clear *) fixws Hws. stubc Hd Hc.
  - (* policy_set *) fixws Hws. stubc Hd Hc.
  - (* lv2_worker_set *) fixws Hws. stubc Hd Hc.
  - (* pool_config *) fixws Hws. stubc Hd Hc.
  - (* worker_env *) fixws Hws. stubc Hd Hc.
  - (* chain *)
    pose proof (number_atoi a id H0) as Ea. pose proof (Verbs.number_m_range a id H0) as Ra.
    pose proof (numbers_atoi rest ids H1) as Eids.
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
    assert (Lr : (length rest <= 62)%nat)
      by (pose proof (f_equal (@length _) Hws) as L; rewrite length_firstn in L; cbn [length] in L; lia).
    subst id ids.
    eapply P4_stub; [reflexivity | exact Hd | apply shape_of_in | | | ].
    + rewrite Hn0. unfold daemon_shape. rewrite <- lit_bstr. apply reply_ok_shape. exact Hne.
    + rewrite Hn0. unfold arity_ok. right; right; right.
      replace (row_find Verbs.Lit.verb_chain parsed_rows) with (Some (2, UNB)) by (vm_compute; reflexivity).
      cbv beta iota. rewrite Hr. unfold UNB. destruct rest as [|r0 rest']; [congruence|]. cbn [length] in *. lia.
    + apply Forall_cons; [|apply Forall_nil]. apply cwo_intro.
      * change (call_items REC_CHAIN) with [INum 1; IStar; IStar]. cbn [items_ok want]. rewrite Hr.
        replace (1 <? Z.of_nat (length (Verbs.Lit.verb_chain :: a :: rest))) with true
          by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
        cbv beta iota. znat. rewrite Hn1. split; [symmetry; apply dec_atoi | repeat split].
      * intros E; discriminate E.
      * intros _. split; [reflexivity|]. rewrite Hr. split.
        -- cbn [nth]. rewrite length_map.
           replace (Z.of_nat (length (Verbs.Lit.verb_chain :: a :: rest)) - 2) with (Z.of_nat (length rest))
             by (cbn [length]; lia).
           symmetry. apply dec_pf. lia.
        -- cbn [nth]. apply chain_ok; assumption.
      * intros E; discriminate E.
  - (* chain_clear *) pose proof (number_atoi a id H) as Ea. subst id. fixws Hws. stubc Hd Hc.
  - (* pin_set *) fixws Hws. eapply P4_pins; [reflexivity | exact Hd | arc | arc | ].
    apply cwo_intro; [itac Hc | intros E; discriminate E | intros E; discriminate E | intros _; split; reflexivity].
  - (* pin_set verdict *) fixws Hws. eapply P4_pins; [reflexivity | exact Hd | arc | arc | ].
    apply cwo_intro; [itac Hc | intros E; discriminate E | intros E; discriminate E | ].
    intros _. split; [reflexivity|]. cbn [nth darg]. unfold pin_verdict. rewrite (prefix_verdict vd H). reflexivity.
  - (* pin_accept *) fixws Hws. stubc Hd Hc.
  - (* pin_clear *) fixws Hws. eapply P4_pins; [reflexivity | exact Hd | arc | arc | c1 Hc].
  - (* quit *) fixws Hws. apply P4_quit.
  - (* instance info verbs *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr).
    eapply P4_stub; [reflexivity | exact Hd | apply shape_of_in | | | ].
    + rewrite Hf. apply reply_ok_shape. exact Hne.
    + rewrite Hn0. apply arity_row_none. exact (ledger_row_none v led H).
    + apply Forall_cons; [|exact (after_cwo ws (v :: args) Hws)].
      apply cwo_intro; [|intros E; discriminate E ..].
      change (call_items REC_INSTANCE_VERB) with [ILine; IStar]. cbn [items_ok want].
      split; [exact Hc | repeat split].
  - (* broadcast, one word *) fixws Hws. apply P4_bc; [exact Hd | apply arity_afree_gen; [lia | exact H] | c1 Hc | c1 Hc].
  - (* instance verbs *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
    eapply P4_stub; [reflexivity | exact Hd | left; reflexivity | rhost | rewrite Hn0; apply arity_row_none; exact H | ].
    apply Forall_cons; [|exact (after_cwo ws _ Hws)].
    apply cwo_intro; [|intros E; discriminate E ..].
    change (call_items REC_CALL) with [INum 1; ILine]. cbn [items_ok want]. rewrite Hr.
    replace (1 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
    cbv beta iota. znat. rewrite Hn1. split; [symmetry; apply dec_atoi | split; [exact Hc | exact I]].
  - (* connect, disconnect *) fixws Hws. destruct H as [->| ->]; stubc Hd Hc.
  - (* broadcast *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr).
    apply P4_bc; [exact Hd | rewrite Hn0; apply arity_afree_gen; [lia | exact H] | c1 Hc | c1 Hc].
Qed.

Lemma P4_holds : forall R0 D, (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  let '(R1, x, q) := vr_run (rec_clear R0) D in P4 R0 (hwords D) R1 x q.
Proof.
  intros R0 D Hd. rewrite vr_run_out.
  apply (P4_spec R0 (hwords D) (Verbs.line D) (Verbs.toks D));
    [apply receive_spec | apply toks_firstn | apply canon_line | apply first_word_line | exact Hd].
Qed.

(** * The round trip *)

Lemma step_frame : forall R0 s, let '(R1, x, q) := VerbsRun.run_step reply_code (rec_clear R0) s in
  r_refuse R1 = r_refuse R0 /\ r_code R1 = r_code R0 /\ r_spill R1 = r_spill R0 /\ (length (r_calls R1) <= 2)%nat.
Proof.
  intros R0 s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    unfold VerbsRun.run_step, VerbsRun.run_call, VerbsRun.pins_follow, sup_add_m, descriptors_get_m,
      descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m, sup_instance_info_m, sup_reset_m,
      sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
      sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m, sup_connect_m,
      sup_broadcast_m, sup_host_setting_m, pins_set_m, pins_clear_m, lv2_refusals_forget_m, descriptors_add_m,
      rec_stub, rec_answer, hand_back, rec_record, rec_mix, rec_mix_host, rec_stub_code, rec_answer_code,
      rec_stub_mix; cbn;
    repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbn);
    repeat split; cbn; lia.
Qed.

Lemma fin_frame : forall R1 x af, (length (r_calls R1) < 16)%nat ->
  r_refuse (fin R1 x af) = r_refuse R1 /\ r_code (fin R1 x af) = r_code R1 /\ r_spill (fin R1 x af) = r_spill R1.
Proof.
  intros R1 x af L. unfold fin. destruct af as [[i v]|];
    [unfold sup_after_reply_m; rewrite rec_record_calls by (cbn; exact L)|]; cbn; repeat split.
Qed.

Lemma run_frame : forall R0 st af, let '(R1, x, q) := run_out R0 st af in
  r_refuse R1 = r_refuse R0 /\ r_code R1 = r_code R0 /\ r_spill R1 = r_spill R0.
Proof.
  intros R0 st af. unfold run_out. pose proof (step_frame R0 st) as F.
  destruct (VerbsRun.run_step reply_code (rec_clear R0) st) as [[R1 x] q].
  destruct F as (F1 & F2 & F3 & F4). destruct (fin_frame R1 x af ltac:(lia)) as (G1 & G2 & G3).
  cbv beta iota. rewrite G1, G2, G3. split; [exact F1|split; [exact F2|exact F3]].
Qed.

Lemma plan_ln : forall atoi ln1 ln2 tk, canon ln1 = canon ln2 -> first_word ln1 = first_word ln2 ->
  (length ln2 <= length ln1)%nat ->
  Verbs.plan atoi ln1 tk = Verbs.reject \/
  forall rc R, VerbsRun.run_step rc R (Verbs.plan atoi ln1 tk) = VerbsRun.run_step rc R (Verbs.plan atoi ln2 tk).
Proof.
  intros atoi ln1 ln2 tk Hc Hf Hl.
  destruct tk as [|v args]; [left; reflexivity|].
  unfold Verbs.plan, Verbs.pin_set_words_m.
  repeat (match goal with
          | |- context [if ?c then _ else _] => destruct c eqn:?
          | |- context [match ?l with [] => _ | _ :: _ => _ end] => is_var l; destruct l
          | |- context [match ?o with Some _ => _ | None => _ end] => destruct o eqn:?
          end; cbv beta iota).
  all: try first
    [ left; reflexivity
    | right; intros ? ?; reflexivity
    | right; intros ? ?; cbn [VerbsRun.run_step VerbsRun.run_call];
      cbv delta [sup_call_m sup_connect_m sup_broadcast_m sup_host_setting_m sup_instance_verb_m] beta zeta;
      rewrite ?Hc, ?Hf; reflexivity
    | exfalso; match goal with
      | E1 : (Verbs.line_max <? Z.of_nat (length ?l1)) || ?b = false,
        E2 : (Verbs.line_max <? Z.of_nat (length ?l2)) || ?b = true |- _ =>
          apply orb_false_iff in E1; destruct E1 as [E1a E1b]; rewrite E1b, orb_false_r in E2;
          apply Z.ltb_lt in E2; apply Z.ltb_ge in E1a; lia
      end ].
Qed.

Lemma after_some : forall atoi ln tk p, (forall t, In t tk -> tokp t) ->
  Verbs.after atoi tk = Some p -> Verbs.plan atoi ln tk <> Verbs.reject.
Proof.
  intros atoi ln tk p Ht H. destruct tk as [|v [|a rest]]; try discriminate. unfold Verbs.after in H.
  assert (Tv : tokp v) by (apply Ht; left; reflexivity).
  destruct Verbs.format_words as (_ & _ & _ & _ & FW5 & FW6).
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load) eqn:E1.
  { apply (Verbs.verb_is_m_token v _ Tv) in E1. rewrite FW5 in E1. subst v.
    intros E. vm_compute in E. discriminate E. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) eqn:E2; [|discriminate H].
  apply (Verbs.verb_is_m_token v _ Tv) in E2. rewrite FW6 in E2. subst v.
  intros E. vm_compute in E. discriminate E.
Qed.

Lemma canon_join : forall D, canon (join_sp (hwords D)) = join_sp (hwords D).
Proof.
  intros D. unfold canon. rewrite words_eq, words_join; [reflexivity|]. intros w Hw. exact (hwords_sep D w Hw).
Qed.

Lemma first_word_join : forall D, first_word (join_sp (hwords D)) = nth 0 (hwords D) [].
Proof.
  intros D. unfold first_word. rewrite words_eq, words_join; [destruct (hwords D); reflexivity|].
  intros w Hw. exact (hwords_sep D w Hw).
Qed.

Lemma rt_holds : forall R0 D,
  let '(R1, x, q) := vr_run (rec_clear R0) D in rt_ok R1 (if q then 1 else 0) (r_state R0) (r_host R0) (hwords D).
Proof.
  intros R0 D. rewrite vr_run_out.
  pose proof (run_frame R0 (fst (Verbs.receive atoi_val D)) (snd (Verbs.receive atoi_val D))) as Fr.
  destruct (run_out R0 (fst (Verbs.receive atoi_val D)) (snd (Verbs.receive atoi_val D))) as [[R1 x] q] eqn:Erun.
  destruct Fr as (F1 & F2 & F3).
  unfold rt_ok. intros Hne Hact.
  replace (rec_clear (set_host (set_state R1 (r_state R0)) (r_host R0))) with (rec_clear R0)
    by (unfold rec_clear, set_host, set_state; cbn; rewrite F1, F2, F3; reflexivity).
  rewrite vr_run_out.
  unfold Verbs.receive in *. rewrite toks_join, line_join.
  destruct (Verbs.toks D) as [|t tl] eqn:Et.
  { exfalso. apply Hne. apply firstn64_nil. rewrite <- toks_firstn. exact Et. }
  cbn [fst snd] in *.
  assert (Tk : forall t', In t' (t :: tl) -> tokp t').
  { intros t' Ht'. rewrite <- Et in Ht'. destruct (Verbs.toks_word D t' Ht') as [_ H].
    intros b Hb. destruct (H b Hb) as (H1 & H2 & _). split; assumption. }
  destruct (plan_ln atoi_val (Verbs.line D) (join_sp (hwords D)) (t :: tl)) as [Hrej|Heq].
  - rewrite canon_line, canon_join. reflexivity.
  - rewrite first_word_line, first_word_join. reflexivity.
  - apply join_le_line.
  - assert (Ha : Verbs.after atoi_val (t :: tl) = None).
    { destruct (Verbs.after atoi_val (t :: tl)) as [p|] eqn:Ea; [|reflexivity].
      exfalso. exact (after_some atoi_val (Verbs.line D) (t :: tl) p Tk Ea Hrej). }
    rewrite Hrej, Ha in Erun. unfold run_out, Verbs.reject in Erun. cbn in Erun.
    injection Erun as <- <- <-. unfold fin in Hact. cbn in Hact. discriminate Hact.
  - assert (E : run_out R0 (Verbs.plan atoi_val (join_sp (hwords D)) (t :: tl)) (Verbs.after atoi_val (t :: tl))
                = (R1, x, q)).
    { rewrite <- Erun. unfold run_out. rewrite Heq. reflexivity. }
    rewrite E. cbv beta iota. repeat split.
Qed.

Theorem harness_props_holds : harness_props.
Proof.
  intros R0 D _ _ _ Hd. pose proof (P4_holds R0 D Hd) as H1. pose proof (rt_holds R0 D) as H2.
  revert H1 H2. unfold msg_props. cbv zeta. destruct (vr_run (rec_clear R0) D) as [[R1 x] q]. intros H1 H2.
  destruct H1 as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9).
  exact (conj h1 (conj h2 (conj h3 (conj h4 (conj h5 (conj h6 (conj h7 (conj h8 (conj h9 H2))))))))).
Qed.
