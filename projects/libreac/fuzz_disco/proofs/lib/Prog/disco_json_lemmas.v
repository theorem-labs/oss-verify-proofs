From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_text disco_json_reader_model.
Import ListNotations.
Open Scope Z_scope.

Definition seg (B : list Z) (i : Z) (w : list Z) : Prop := exists pre post, B = pre ++ w ++ post /\ i = jlen pre.

Lemma jlen_app : forall a b, jlen (a ++ b) = jlen a + jlen b.
Proof. intros a b. unfold jlen. rewrite length_app. lia. Qed.

Lemma jlen_cons : forall x a, jlen (x :: a) = 1 + jlen a.
Proof. intros x a. unfold jlen. cbn [length]. lia. Qed.

Lemma jlen_nil : jlen [] = 0.
Proof. reflexivity. Qed.

Lemma jlen_nonneg : forall a, 0 <= jlen a.
Proof. intros a. unfold jlen. lia. Qed.

Lemma seg_app : forall B i w1 w2, seg B i (w1 ++ w2) -> seg B i w1 /\ seg B (i + jlen w1) w2.
Proof.
  intros B i w1 w2 (pre & post & HB & Hi). subst. split.
  - exists pre, (w2 ++ post). split; [rewrite <- app_assoc; reflexivity | reflexivity].
  - exists (pre ++ w1), post. split; [rewrite <- !app_assoc; reflexivity | rewrite jlen_app; reflexivity].
Qed.

Lemma seg_cons : forall B i x w, seg B i (x :: w) -> seg B (i + 1) w.
Proof.
  intros B i x w H. apply (seg_app B i [x] w) in H. destruct H as [_ H]. exact H.
Qed.

Lemma seg_byte : forall B i c w, seg B i (c :: w) -> 0 <= i < jlen B /\ jbyte B i = c.
Proof.
  intros B i c w (pre & post & HB & Hi). subst. split.
  - rewrite !jlen_app, jlen_cons. pose proof (jlen_nonneg pre). pose proof (jlen_nonneg w).
    pose proof (jlen_nonneg post). lia.
  - unfold jbyte, jlen. rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma seg_bound : forall B i w, seg B i w -> 0 <= i /\ i + jlen w <= jlen B.
Proof.
  intros B i w (pre & post & HB & Hi). subst. rewrite !jlen_app.
  pose proof (jlen_nonneg pre). pose proof (jlen_nonneg post). lia.
Qed.

Lemma seg_skipn : forall B i w, seg B i w -> exists post, skipn (Z.to_nat i) B = w ++ post.
Proof.
  intros B i w (pre & post & HB & Hi). subst. exists post. unfold jlen. rewrite Nat2Z.id.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma seg_text : forall B s w k, seg B s w -> tv_text B (k, s, jlen w) = w.
Proof.
  intros B s w k H. destruct (seg_skipn B s w H) as [post Hs]. unfold tv_text. cbn [fst snd].
  rewrite Hs. unfold jlen. rewrite Nat2Z.id. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn.
  apply app_nil_r.
Qed.

Lemma json_ws_stop : forall B i c w, seg B i (c :: w) -> jws_char c = false -> json_ws B i = i.
Proof.
  intros B i c w H Hc. destruct (seg_byte B i c w H) as [Hr Hb]. unfold json_ws.
  destruct (length B) eqn:E.
  - unfold jlen in Hr. rewrite E in Hr. lia.
  - cbn [json_ws_f]. rewrite Hb, Hc, andb_false_r. reflexivity.
Qed.

Lemma json_ws_end : forall B, json_ws B (jlen B) = jlen B.
Proof.
  intros B. unfold json_ws. destruct (length B); cbn [json_ws_f]; [reflexivity|].
  rewrite Z.ltb_irrefl. reflexivity.
Qed.

Lemma at_byte_seg : forall B i c w d, seg B i (c :: w) -> at_byte B i d = (c =? d).
Proof.
  intros B i c w d H. destruct (seg_byte B i c w H) as [Hr Hb]. unfold at_byte.
  rewrite Hb. replace (i <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma some4 : forall (a b c d a' b' c' d' : Z), a = a' -> b = b' -> c = c' -> d = d' ->
  Some (a, b, c, d) = Some (a', b', c', d').
Proof. intros. subst. reflexivity. Qed.

Definition strc (c : Z) : Prop := 32 <= c /\ c <> 34 /\ c <> 92.

Lemma jstr_run : forall B i s2 j f, seg B j (s2 ++ [34]) -> Forall strc s2 -> (length s2 < f)%nat ->
  jstr B i j f = Some (j + jlen s2 + 1, 1, i + 1, j + jlen s2 - i - 1).
Proof.
  intros B i s2. induction s2 as [|x s2 IH]; intros j f H Hs Hf; destruct f as [|f]; try (cbn in Hf; lia).
  - cbn [app] in H. destruct (seg_byte B j 34 [] H) as [Hr Hb]. cbn [jstr].
    replace (jlen B <=? j) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb, Z.eqb_refl.
    rewrite jlen_nil. apply some4; lia.
  - cbn [app] in H. destruct (seg_byte B j x _ H) as [Hr Hb]. apply Forall_cons_iff in Hs as [[H1 [H2 H3]] Hs'].
    cbn [jstr]. replace (jlen B <=? j) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb.
    replace (x =? 34) with false by (symmetry; apply Z.eqb_neq; exact H2).
    replace (x <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (x =? 92) with false by (symmetry; apply Z.eqb_neq; exact H3).
    rewrite (IH (j + 1) f (seg_cons B j x _ H) Hs') by (cbn in Hf; lia).
    rewrite jlen_cons. apply some4; lia.
Qed.

Lemma jscalar_str : forall B i s, seg B i ([34] ++ s ++ [34]) -> Forall strc s ->
  jscalar B i = Some (i + jlen s + 2, 1, i + 1, jlen s).
Proof.
  intros B i s H Hs. cbn [app] in H. destruct (seg_byte B i 34 _ H) as [Hr Hb].
  pose proof (seg_bound B i _ H) as [_ Hl]. rewrite jlen_cons, jlen_app, jlen_cons, jlen_nil in Hl.
  unfold jscalar. replace (jlen B <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb.
  cbn [Z.eqb Pos.eqb]. rewrite (jstr_run B i s (i + 1) (length B) (seg_cons B i 34 _ H) Hs).
  - apply some4; lia.
  - unfold jlen in Hl. lia.
Qed.

Lemma jprefix_app : forall w r, jprefix w (w ++ r) = true.
Proof. intros w r. induction w as [|a w IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl, IH. reflexivity. Qed.

Lemma jprefix_neq : forall a w b r, a <> b -> jprefix (a :: w) (b :: r) = false.
Proof. intros a w b r H. cbn [jprefix]. replace (a =? b) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

Lemma jscalar_true : forall B i, seg B i s_true -> jscalar B i = Some (i + 4, 3, i, 4).
Proof.
  intros B i H. unfold s_true in H. destruct (seg_byte B i _ _ H) as [Hr Hb].
  pose proof (seg_bound B i _ H) as [_ Hl]. destruct (seg_skipn B i _ H) as [post Hs].
  unfold jscalar. replace (jlen B <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb.
  cbn [Z.eqb Pos.eqb]. unfold jlit_words. cbn [jlit]. rewrite Hs. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
  unfold jlen in Hl. cbn [length] in Hl.
  replace (4 <=? jlen B - i) with true by (symmetry; apply Z.leb_le; unfold jlen; lia).
  rewrite jprefix_app. reflexivity.
Qed.

Lemma jscalar_false : forall B i, seg B i s_false -> jscalar B i = Some (i + 5, 3, i, 5).
Proof.
  intros B i H. unfold s_false in H. destruct (seg_byte B i _ _ H) as [Hr Hb].
  pose proof (seg_bound B i _ H) as [_ Hl]. destruct (seg_skipn B i _ H) as [post Hs].
  unfold jscalar. replace (jlen B <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb.
  cbn [Z.eqb Pos.eqb]. unfold jlit_words. cbn [jlit]. rewrite Hs. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
  unfold jlen in Hl. cbn [length] in Hl.
  replace (jprefix [116; 114; 117; 101] ([102; 97; 108; 115; 101] ++ post)) with false by reflexivity.
  rewrite andb_false_r.
  replace (5 <=? jlen B - i) with true by (symmetry; apply Z.leb_le; unfold jlen; lia).
  rewrite jprefix_app. reflexivity.
Qed.

Definition digc (c : Z) : Prop := 48 <= c <= 57.

Lemma jdigit_digc : forall c, digc c -> jdigit c = true.
Proof. intros c [H1 H2]. unfold jdigit. apply andb_true_intro. split; apply Z.leb_le; lia. Qed.

Lemma jdigits_run : forall B ds j c f, seg B j (ds ++ [c]) -> Forall digc ds -> jdigit c = false ->
  (length ds < f)%nat -> jdigits B j f = j + jlen ds.
Proof.
  intros B ds. induction ds as [|x ds IH]; intros j c f H Hd Hc Hf; destruct f as [|f]; try (cbn in Hf; lia).
  - cbn [app] in H. destruct (seg_byte B j c [] H) as [Hr Hb]. cbn [jdigits]. rewrite Hb, Hc, andb_false_r.
    rewrite jlen_nil. lia.
  - cbn [app] in H. destruct (seg_byte B j x _ H) as [Hr Hb]. apply Forall_cons_iff in Hd as [Hx Hd'].
    cbn [jdigits]. rewrite Hb, (jdigit_digc x Hx).
    replace (j <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    rewrite (IH (j + 1) c f (seg_cons B j x _ H) Hd' Hc) by (cbn in Hf; lia). rewrite jlen_cons. lia.
Qed.

Lemma jscalar_num : forall B i d c, seg B i (d ++ [c]) -> Forall digc d -> d <> [] ->
  (hd 0 d = 48 -> d = [48]) -> jdigit c = false -> c <> 46 -> c <> 101 -> c <> 69 ->
  jscalar B i = Some (i + jlen d, 2, i, jlen d).
Proof.
  intros B i d c H Hd Hne H0 Hc C1 C2 C3. destruct d as [|x d']; [congruence|].
  inversion Hd as [|? ? Hx Hd']. subst.
  cbn [app] in H. destruct (seg_byte B i x _ H) as [Hr Hb].
  pose proof (seg_bound B i _ H) as [_ Hl]. destruct (seg_skipn B i _ H) as [post Hs].
  pose proof (seg_app B i (x :: d') [c] H) as [_ Hcseg]. destruct (seg_byte B _ c [] Hcseg) as [Hcr Hcb].
  assert (Hj1 : (if x =? 48 then i + 1 else jdigits B i (length B)) = i + jlen (x :: d')).
  { destruct (Z.eqb_spec x 48) as [E|E].
    - specialize (H0 E). inversion H0. subst. rewrite jlen_cons, jlen_nil. lia.
    - apply (jdigits_run B (x :: d') i c (length B) H Hd Hc). rewrite jlen_cons, jlen_app, jlen_cons, jlen_nil in Hl.
      unfold jlen in Hl. cbn [length]. lia. }
  unfold jscalar. replace (jlen B <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hb.
  replace (x =? 34) with false by (symmetry; apply Z.eqb_neq; unfold digc in Hx; lia).
  unfold jlit_words. cbn [jlit]. rewrite Hs. cbn [app].
  rewrite !(jprefix_neq _ _ x) by (unfold digc in Hx; lia).
  rewrite !andb_false_r. unfold jnum. rewrite Hb.
  replace (x =? 45) with false by (symmetry; apply Z.eqb_neq; unfold digc in Hx; lia).
  unfold jdig_at. rewrite Hb, (jdigit_digc x Hx).
  replace (i <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb].
  rewrite Hj1. unfold jfrac. rewrite Hcb.
  replace (c =? 46) with false by (symmetry; apply Z.eqb_neq; exact C1).
  rewrite andb_false_r. cbv beta iota. unfold jexp. rewrite Hcb.
  replace (c =? 101) with false by (symmetry; apply Z.eqb_neq; exact C2).
  replace (c =? 69) with false by (symmetry; apply Z.eqb_neq; exact C3).
  cbn [orb]. rewrite andb_false_r. cbv beta iota. apply some4; lia.
Qed.

Lemma dec_aux_spec : forall f v acc, 0 <= v < 10 ^ Z.of_nat f ->
  exists ds, dec_aux f v acc = ds ++ acc /\ Forall digc ds /\ (v = 0 -> ds = []) /\
    (0 < v -> exists x ds', ds = x :: ds' /\ x <> 48) /\
    (forall k, 0 <= k -> v < 10 ^ k -> (length ds <= Z.to_nat k)%nat).
Proof.
  induction f as [|f IH]; intros v acc Hv.
  - cbn in Hv. assert (v = 0) by lia. subst. exists []. cbn.
    split; [reflexivity|]. split; [constructor|]. split; [reflexivity|]. split; intros; lia.
  - cbn [dec_aux]. destruct (Z.eqb_spec v 0) as [E|E].
    + subst. exists []. cbn.
      split; [reflexivity|]. split; [constructor|]. split; [reflexivity|]. split; intros; lia.
    + assert (Hp : 10 ^ Z.of_nat (S f) = 10 * 10 ^ Z.of_nat f) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
      assert (Hq : 0 <= v / 10 < 10 ^ Z.of_nat f).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
      destruct (IH (v / 10) ((48 + v mod 10) :: acc) Hq) as (ds0 & D1 & D2 & D3 & D4 & D5).
      pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as Hm.
      exists (ds0 ++ [48 + v mod 10]). split; [rewrite D1, <- app_assoc; reflexivity|].
      split; [apply Forall_app; split; [exact D2|constructor; [unfold digc; lia|constructor]]|].
      split; [intros; lia|]. split.
      * intros Hv0. destruct (Z.eqb_spec (v / 10) 0) as [E0|E0].
        -- rewrite (D3 E0). exists (48 + v mod 10), []. split; [reflexivity|].
           assert (v mod 10 = v) by (rewrite Z.mod_small; [reflexivity|]; pose proof (Z.div_mod v 10); lia). lia.
        -- assert (0 < v / 10) by lia. destruct (D4 H) as (x & ds' & -> & Hx).
           exists x, (ds' ++ [48 + v mod 10]). split; [reflexivity|exact Hx].
      * intros k Hk Hvk. destruct (Z.eqb_spec k 0) as [K|K]; [subst; cbn in Hvk; lia|].
        assert (v / 10 < 10 ^ (k - 1)).
        { apply Z.div_lt_upper_bound; [lia|]. replace (10 * 10 ^ (k - 1)) with (10 ^ k); [lia|].
          replace k with (Z.succ (k - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. lia. }
        specialize (D5 (k - 1) ltac:(lia) H). rewrite length_app. cbn [length]. lia.
Qed.

Lemma dec_spec : forall v, 0 <= v < 10 ^ 20 ->
  Forall digc (dec v) /\ dec v <> [] /\ (hd 0 (dec v) = 48 -> dec v = [48]) /\
  (forall k, 1 <= k -> v < 10 ^ k -> (length (dec v) <= Z.to_nat k)%nat).
Proof.
  intros v Hv. unfold dec. destruct (Z.eqb_spec v 0) as [E|E].
  - split; [constructor; [unfold digc; lia|constructor]|]. split; [discriminate|].
    split; [intros; reflexivity|]. intros; cbn; lia.
  - destruct (dec_aux_spec 20 v [] Hv) as (ds & D1 & D2 & D3 & D4 & D5). rewrite D1, app_nil_r.
    destruct (D4 ltac:(lia)) as (x & ds' & -> & Hx).
    split; [exact D2|]. split; [discriminate|]. split.
    + cbn. intros H. congruence.
    + intros k Hk Hvk. apply D5; lia.
Qed.

Lemma hexc_range : forall d, 0 <= d <= 15 -> (48 <= hexc d <= 57) \/ (97 <= hexc d <= 102).
Proof. intros d H. unfold hexc. destruct (Z.ltb_spec d 10); lia. Qed.

Lemma hexc_inj : forall a b, 0 <= a <= 15 -> 0 <= b <= 15 -> hexc a = hexc b -> a = b.
Proof. intros a b Ha Hb H. unfold hexc in H. destruct (Z.ltb_spec a 10), (Z.ltb_spec b 10); lia. Qed.

Lemma div16_range : forall x, 0 <= x <= 255 -> 0 <= x / 16 <= 15.
Proof.
  intros x H. split; [apply Z.div_pos; lia|].
  assert (x / 16 < 16) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma hex_byte_inj : forall x y, byte_ok x -> byte_ok y -> hexc (x / 16) = hexc (y / 16) ->
  hexc (x mod 16) = hexc (y mod 16) -> x = y.
Proof.
  intros x y Hx Hy H1 H2. unfold byte_ok in *.
  assert (A1 : 0 <= x / 16 <= 15) by (apply div16_range; lia).
  assert (A2 : 0 <= y / 16 <= 15) by (apply div16_range; lia).
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  apply hexc_inj in H1; [|lia|lia]. apply hexc_inj in H2; [|lia|lia].
  rewrite (Z.div_mod x 16), (Z.div_mod y 16) by lia. lia.
Qed.

Lemma nth_byte_ok : forall m k, Forall byte_ok m -> byte_ok (nth k m 0).
Proof.
  intros m k H. destruct (Nat.lt_ge_cases k (length m)) as [L|L].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. unfold byte_ok. lia.
Qed.

Lemma mac6 : forall m, length m = 6%nat ->
  m = [nth 0 m 0; nth 1 m 0; nth 2 m 0; nth 3 m 0; nth 4 m 0; nth 5 m 0].
Proof.
  intros m H. destruct m as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|]]]]]]]; cbn in H; try discriminate. reflexivity.
Qed.

Lemma list6_eq : forall (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Z), a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 ->
  a4 = b4 -> a5 = b5 -> [a0; a1; a2; a3; a4; a5] = [b0; b1; b2; b3; b4; b5].
Proof. intros. subst. reflexivity. Qed.

Lemma mac_text_inj : forall m m', length m = 6%nat -> length m' = 6%nat -> Forall byte_ok m -> Forall byte_ok m' ->
  mac_text m = mac_text m' -> m = m'.
Proof.
  intros m m' L L' F F' H. rewrite (mac6 m L), (mac6 m' L').
  unfold mac_text, hex2 in H. cbn [app] in H. inversion H.
  apply list6_eq; apply hex_byte_inj; try apply nth_byte_ok; assumption.
Qed.

Lemma strc_hexc : forall d, 0 <= d <= 15 -> strc (hexc d).
Proof. intros d H. destruct (hexc_range d H); unfold strc; lia. Qed.

Lemma strc_mac : forall m, Forall byte_ok m -> Forall strc (mac_text m).
Proof.
  intros m F. unfold mac_text, hex2. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; try (unfold strc; lia);
  match goal with
  | |- strc (hexc (nth ?k m 0 / 16)) => apply strc_hexc, div16_range, (nth_byte_ok m k F)
  | |- strc (hexc (nth ?k m 0 mod 16)) => apply strc_hexc; pose proof (Z.mod_pos_bound (nth k m 0) 16 ltac:(lia)); lia
  end.
Qed.

Lemma strc_digits : forall ds, Forall digc ds -> Forall strc ds.
Proof. intros ds F. eapply Forall_impl; [|exact F]. intros c H. unfold digc, strc in *. lia. Qed.

Ltac strc_lit := repeat apply Forall_cons; try apply Forall_nil; unfold strc; lia.

Lemma strc_rolename : forall r, Forall strc (rolename r).
Proof. intros r. unfold rolename, s_box, s_master, s_unknown. destruct (r =? 1); [|destruct (r =? 2)]; strc_lit. Qed.

Lemma strc_model : forall tok e, tok_ok tok -> Forall strc (fst (model_of tok e)).
Proof.
  intros tok e Ht. unfold model_of. destruct (e_has_decl e =? 0); [cbn; unfold s_unknown; strc_lit|].
  destruct (tok (e_family e) (e_decl_in e) (e_decl_out e)) as [t|] eqn:E; [|cbn; unfold s_unknown; strc_lit].
  cbn. destruct (Ht _ _ _ _ E) as [_ F]. eapply Forall_impl; [|exact F]. intros c H. unfold tok_char, strc in *. lia.
Qed.

Lemma dec_small : forall v, 0 <= v <= 255 -> 0 <= v < 10 ^ 20.
Proof. intros v H. lia. Qed.

Lemma strc_width : forall tok e, entry_wf e -> Forall strc (snd (model_of tok e)).
Proof.
  intros tok e Hw. destruct Hw as (_ & _ & _ & Hi & Ho & _). unfold model_of.
  destruct (e_has_decl e =? 0); [cbn; unfold s_0x0; strc_lit|].
  destruct (tok (e_family e) (e_decl_in e) (e_decl_out e)); [|cbn; unfold s_0x0; strc_lit].
  cbn [snd]. unfold byte_ok in *. apply Forall_app; split.
  - apply strc_digits. apply (proj1 (dec_spec (e_decl_in e) ltac:(lia))).
  - cbn [app]. constructor; [unfold strc; lia|]. apply strc_digits. apply (proj1 (dec_spec (e_decl_out e) ltac:(lia))).
Qed.

Lemma jlen_key : forall k, jlen (key k) = jlen k + 3.
Proof. intros k. unfold key. rewrite !jlen_app, !jlen_cons, jlen_nil. lia. Qed.

Lemma jlen_qstr : forall s, jlen (qstr s) = jlen s + 2.
Proof. intros s. unfold qstr. rewrite !jlen_app, !jlen_cons, jlen_nil. lia. Qed.

Fixpoint slot_pure (kw : list Z) (ks : list (list Z)) (k : nat) : option nat :=
  match ks with
  | [] => None
  | w :: ks' => if (jlen kw =? Z.of_nat (length w)) && lzeqb kw w then Some k else slot_pure kw ks' (S k)
  end.

Lemma slot_of_text : forall B s kw, tv_text B (1, s, jlen kw) = kw -> slot_of B (1, s, jlen kw) = slot_pure kw keys 0.
Proof.
  intros B s kw H. unfold slot_of. generalize 0%nat. generalize keys as ks.
  induction ks as [|w ks IH]; intros k; [reflexivity|]. cbn [slot_from slot_pure].
  unfold jtok_is. cbn [tv_kind fst snd]. rewrite H. rewrite IH. reflexivity.
Qed.

Lemma seg_move : forall B i j w, seg B i w -> i = j -> seg B j w.
Proof. intros B i j w H E. subst. exact H. Qed.

Lemma seg_split3 : forall B i a b c, seg B i (a ++ b ++ c) -> seg B (i + jlen a) b.
Proof. intros B i a b c H. apply seg_app in H as [_ H]. apply seg_app in H as [H _]. exact H. Qed.

Lemma seg_after : forall B i a b, seg B i (a ++ b) -> seg B (i + jlen a) b.
Proof. intros B i a b H. apply seg_app in H as [_ H]. exact H. Qed.

Lemma seg_before : forall B i a b, seg B i (a ++ b) -> seg B i a.
Proof. intros B i a b H. apply seg_app in H as [H _]. exact H. Qed.

Lemma pair_step : forall B i kw vt c rest vk vs vl kidx cur f,
  seg B i (key kw ++ vt ++ c :: rest) -> Forall strc kw ->
  jscalar B (i + jlen kw + 3) = Some (i + jlen kw + 3 + jlen vt, vk, vs, vl) ->
  (exists x vt', vt = x :: vt' /\ jws_char x = false) -> jws_char c = false ->
  slot_pure kw keys 0 = Some kidx -> tv_kind (nth kidx cur tok_none) = 0 ->
  json_pairs B i cur (S f) =
    (if c =? 44 then json_pairs B (json_ws B (i + jlen kw + 3 + jlen vt + 1)) (set_nth kidx cur (vk, vs, vl)) f
     else if c =? 125 then Some (i + jlen kw + 3 + jlen vt + 1, set_nth kidx cur (vk, vs, vl)) else None).
Proof.
  intros B i kw vt c rest vk vs vl kidx cur f H Hkw Hv (x & vt' & Evt & Hx) Hc Hslot Hcur.
  assert (H1 : seg B i (([34] ++ kw ++ [34]) ++ (58 :: vt ++ c :: rest))).
  { unfold key in H. replace (([34] ++ kw ++ [34]) ++ 58 :: vt ++ c :: rest)
      with (([34] ++ kw ++ [34; 58]) ++ vt ++ c :: rest); [exact H|].
    cbn [app]. f_equal. rewrite <- !app_assoc. reflexivity. }
  pose proof (seg_before _ _ _ _ H1) as Hk. pose proof (seg_after _ _ _ _ H1) as Hcol.
  apply (seg_move _ _ (i + jlen kw + 2)) in Hcol; [|rewrite !jlen_app, !jlen_cons, !jlen_nil; lia].
  assert (Hks : jscalar B i = Some (i + jlen kw + 2, 1, i + 1, jlen kw)) by (apply jscalar_str; assumption).
  assert (Hws1 : json_ws B (i + jlen kw + 2) = i + jlen kw + 2)
    by (apply (json_ws_stop _ _ 58 _ Hcol); reflexivity).
  assert (Hat1 : at_byte B (i + jlen kw + 2) 58 = true) by (rewrite (at_byte_seg _ _ 58 _ _ Hcol); reflexivity).
  pose proof (seg_cons _ _ _ _ Hcol) as Hval. subst vt.
  assert (Hws2 : json_ws B (i + jlen kw + 2 + 1) = i + jlen kw + 3).
  { apply (seg_move _ _ (i + jlen kw + 2 + 1)) in Hval; [|lia].
    rewrite (json_ws_stop _ _ x _ Hval Hx). lia. }
  pose proof (seg_after _ _ _ _ Hval) as Hcs.
  apply (seg_move _ _ (i + jlen kw + 3 + jlen (x :: vt'))) in Hcs; [|lia].
  assert (Hws3 : json_ws B (i + jlen kw + 3 + jlen (x :: vt')) = i + jlen kw + 3 + jlen (x :: vt'))
    by exact (json_ws_stop _ _ c _ Hcs Hc).
  assert (Hkt : seg B (i + 1) kw) by (apply seg_cons in Hk; exact (seg_before _ _ _ _ Hk)).
  assert (Hsl : slot_of B (1, i + 1, jlen kw) = Some kidx)
    by (rewrite slot_of_text; [exact Hslot|apply seg_text; exact Hkt]).
  cbn [json_pairs]. rewrite Hks. cbv beta iota zeta.
  replace (negb (1 =? 1)) with false by reflexivity. cbv beta iota.
  rewrite Hws1, Hat1. cbv beta iota. cbn [negb]. cbv beta iota.
  rewrite Hws2, Hv. cbv beta iota zeta. rewrite Hws3, Hsl. cbv beta iota. rewrite Hcur, Z.eqb_refl.
  cbv beta iota. rewrite (at_byte_seg _ _ c _ 44 Hcs), (at_byte_seg _ _ c _ 125 Hcs). reflexivity.
Qed.

Lemma seg_val : forall B p kw X, seg B p (key kw ++ X) -> seg B (p + jlen kw + 3) X.
Proof. intros B p kw X H. apply seg_after in H. apply (seg_move _ _ _ _ H). rewrite jlen_key. lia. Qed.

Lemma ws_key : forall B p kw R, seg B p (key kw ++ R) -> json_ws B p = p.
Proof. intros B p kw R H. unfold key in H. cbn [app] in H. exact (json_ws_stop _ _ 34 _ H eq_refl). Qed.

Lemma pair_next : forall B p kw vt kw' R vk vs vl kidx cur f,
  seg B p (key kw ++ vt ++ 44 :: key kw' ++ R) -> Forall strc kw ->
  jscalar B (p + jlen kw + 3) = Some (p + jlen kw + 3 + jlen vt, vk, vs, vl) ->
  (exists x vt', vt = x :: vt' /\ jws_char x = false) ->
  slot_pure kw keys 0 = Some kidx -> tv_kind (nth kidx cur tok_none) = 0 ->
  json_pairs B p cur (S f) = json_pairs B (p + jlen kw + 3 + jlen vt + 1) (set_nth kidx cur (vk, vs, vl)) f /\
  seg B (p + jlen kw + 3 + jlen vt + 1) (key kw' ++ R).
Proof.
  intros B p kw vt kw' R vk vs vl kidx cur f H Hkw Hv Hx Hslot Hcur.
  assert (Hn : seg B (p + jlen kw + 3 + jlen vt + 1) (key kw' ++ R)).
  { pose proof (seg_val _ _ _ _ H) as H1. apply seg_after in H1. apply seg_cons in H1. exact H1. }
  split; [|exact Hn].
  rewrite (pair_step B p kw vt 44 (key kw' ++ R) vk vs vl kidx cur f H Hkw Hv Hx eq_refl Hslot Hcur).
  rewrite Z.eqb_refl. rewrite (ws_key _ _ _ _ Hn). reflexivity.
Qed.

Lemma pair_next_eq : forall B p kw vt kw' R vk vs vl kidx cur f,
  seg B p (key kw ++ vt ++ 44 :: key kw' ++ R) -> Forall strc kw ->
  jscalar B (p + jlen kw + 3) = Some (p + jlen kw + 3 + jlen vt, vk, vs, vl) ->
  (exists x vt', vt = x :: vt' /\ jws_char x = false) ->
  slot_pure kw keys 0 = Some kidx -> tv_kind (nth kidx cur tok_none) = 0 ->
  json_pairs B p cur (S f) = json_pairs B (p + jlen kw + 3 + jlen vt + 1) (set_nth kidx cur (vk, vs, vl)) f.
Proof. intros. eapply pair_next; eassumption. Qed.

Lemma pair_seg : forall B p kw vt kw' R, seg B p (key kw ++ vt ++ 44 :: key kw' ++ R) ->
  seg B (p + jlen kw + 3 + jlen vt + 1) (key kw' ++ R).
Proof. intros B p kw vt kw' R H. pose proof (seg_val _ _ _ _ H) as H1. apply seg_after in H1. apply seg_cons in H1. exact H1. Qed.

Lemma pair_last : forall B p kw vt R vk vs vl kidx cur f,
  seg B p (key kw ++ vt ++ 125 :: R) -> Forall strc kw ->
  jscalar B (p + jlen kw + 3) = Some (p + jlen kw + 3 + jlen vt, vk, vs, vl) ->
  (exists x vt', vt = x :: vt' /\ jws_char x = false) ->
  slot_pure kw keys 0 = Some kidx -> tv_kind (nth kidx cur tok_none) = 0 ->
  json_pairs B p cur (S f) = Some (p + jlen kw + 3 + jlen vt + 1, set_nth kidx cur (vk, vs, vl)).
Proof.
  intros B p kw vt R vk vs vl kidx cur f H Hkw Hv Hx Hslot Hcur.
  rewrite (pair_step B p kw vt 125 R vk vs vl kidx cur f H Hkw Hv Hx eq_refl Hslot Hcur). reflexivity.
Qed.

Lemma val_str : forall B p s r, seg B p (qstr s ++ r) -> Forall strc s ->
  jscalar B p = Some (p + jlen (qstr s), 1, p + 1, jlen s).
Proof.
  intros B p s r H F. apply seg_before in H. unfold qstr in H. rewrite (jscalar_str B p s H F).
  rewrite jlen_qstr. apply some4; lia.
Qed.

Lemma val_owned : forall B p e r, seg B p (owned_text e ++ r) ->
  jscalar B p = Some (p + jlen (owned_text e), 3, p, jlen (owned_text e)).
Proof.
  intros B p e r H. apply seg_before in H. unfold owned_text in *. destruct (e_owned e =? 0).
  - rewrite (jscalar_false B p H). reflexivity.
  - rewrite (jscalar_true B p H). reflexivity.
Qed.

Lemma val_dec : forall B p v r, seg B p (dec v ++ 125 :: r) -> 0 <= v < 10 ^ 20 ->
  jscalar B p = Some (p + jlen (dec v), 2, p, jlen (dec v)).
Proof.
  intros B p v r H Hv. destruct (dec_spec v Hv) as (D1 & D2 & D3 & _).
  apply (jscalar_num B p (dec v) 125); try assumption; try reflexivity; try lia.
  replace (dec v ++ 125 :: r) with ((dec v ++ [125]) ++ r) in H by (rewrite <- app_assoc; reflexivity).
  exact (seg_before _ _ _ _ H).
Qed.

Lemma digc_ws : forall x, digc x -> jws_char x = false.
Proof.
  intros x H. unfold digc in H. unfold jws_char.
  replace (x =? 32) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (x =? 9) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (x =? 10) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (x =? 13) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma qstr_start : forall s, exists x vt', qstr s = x :: vt' /\ jws_char x = false.
Proof. intros s. exists 34, (s ++ [34]). split; reflexivity. Qed.

Lemma owned_start : forall e, exists x vt', owned_text e = x :: vt' /\ jws_char x = false.
Proof. intros e. unfold owned_text. destruct (e_owned e =? 0); eexists; eexists; split; reflexivity. Qed.

Lemma dec_start : forall v, 0 <= v < 10 ^ 20 -> exists x vt', dec v = x :: vt' /\ jws_char x = false.
Proof.
  intros v Hv. destruct (dec_spec v Hv) as (D1 & D2 & _). destruct (dec v) as [|x d] eqn:E; [congruence|].
  exists x, d. split; [reflexivity|]. apply digc_ws. inversion D1. assumption.
Qed.

Definition body tok (now : Z) (e : entry) : list Z :=
  [123] ++ key k_mac ++ qstr (mac_text (e_mac e)) ++ P2 e ++ P3 tok e ++ P4 tok e ++ P5 e ++ P6 now e.

Definition exp_view tok (now : Z) (e : entry) : list (Z * Z * list Z) :=
  [(1, jlen (mac_text (e_mac e)), mac_text (e_mac e));
   (1, jlen (rolename (e_role e)), rolename (e_role e));
   (1, jlen (fst (model_of tok e)), fst (model_of tok e));
   (1, jlen (snd (model_of tok e)), snd (model_of tok e));
   (3, jlen (owned_text e), owned_text e);
   (2, jlen (dec (age_of now (e_last_seen e))), dec (age_of now (e_last_seen e)))].

Definition obj_view (B : list Z) (o : jobj) : list (Z * Z * list Z) :=
  map (fun t => (tv_kind t, snd t, tv_text B t)) o.

Lemma age_range : forall now ls, 0 <= now < 2 ^ 64 -> 0 <= ls < 2 ^ 64 ->
  0 <= age_of now ls <= 18446744073709.
Proof.
  intros now ls Hn Hl. unfold age_of. destruct (Z.ltb_spec ls now); [|lia]. split.
  - apply Z.div_pos; lia.
  - assert ((now - ls) / 1000000 < 18446744073710) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma some_pair : forall (a b : Z) (o : jobj), a = b -> Some (a, o) = Some (b, o).
Proof. intros. subst. reflexivity. Qed.

Lemma seg_qstr_text : forall B p s r k, seg B p (qstr s ++ r) -> tv_text B (k, p + 1, jlen s) = s.
Proof.
  intros B p s r k H. unfold qstr in H. rewrite <- !app_assoc in H. cbn [app] in H.
  apply seg_cons in H. apply seg_before in H. apply seg_text. exact H.
Qed.

Lemma seg_plain_text : forall B p w r k, seg B p (w ++ r) -> tv_text B (k, p, jlen w) = w.
Proof. intros B p w r k H. apply seg_before in H. apply seg_text. exact H. Qed.

Lemma obj_parse : forall tok now e B i c rest, tok_ok tok -> entry_wf e -> 0 <= now < 2 ^ 64 ->
  seg B i (body tok now e ++ c :: rest) ->
  exists o, json_pairs B (i + 1) jobj_empty (length B) = Some (i + jlen (body tok now e), o) /\
            obj_view B o = exp_view tok now e.
Proof.
  intros tok now e B i c rest Ht Hw Hn H.
  assert (Fm : Forall strc (mac_text (e_mac e))) by (apply strc_mac; apply Hw).
  pose proof (strc_rolename (e_role e)) as Fr.
  pose proof (strc_model tok e Ht) as Fmd.
  pose proof (strc_width tok e Hw) as Fwd.
  assert (Ha : 0 <= age_of now (e_last_seen e) < 10 ^ 20).
  { pose proof (age_range now (e_last_seen e) Hn ltac:(apply Hw)). lia. }
  assert (Hbl : jlen (body tok now e) = 1 + (jlen k_mac + 3) + jlen (qstr (mac_text (e_mac e))) +
     (1 + (jlen k_role + 3) + jlen (qstr (rolename (e_role e)))) +
     (1 + (jlen k_model + 3) + jlen (qstr (fst (model_of tok e)))) +
     (1 + (jlen k_width + 3) + jlen (qstr (snd (model_of tok e)))) +
     (1 + (jlen k_owned + 3) + jlen (owned_text e)) +
     (1 + (jlen k_age_ms + 3) + jlen (dec (age_of now (e_last_seen e))) + 1)).
  { unfold body, P2, P3, P4, P5, P6. rewrite !jlen_app, !jlen_key, !jlen_cons, !jlen_nil. lia. }
  unfold body, P2, P3, P4, P5, P6 in H. rewrite <- !app_assoc in H. cbn [app] in H.
  pose proof (seg_cons _ _ _ _ H) as S1.
  assert (EB : exists f, length B = S (S (S (S (S (S f)))))).
  { pose proof (seg_bound _ _ _ S1) as [Hi Hb]. rewrite jlen_app, jlen_key in Hb.
    change (jlen k_mac) with 3 in Hb. pose proof (jlen_nonneg (qstr (mac_text (e_mac e)) ++
      44 :: key k_role ++ qstr (rolename (e_role e)) ++ 44 :: key k_model ++ qstr (fst (model_of tok e)) ++
      44 :: key k_width ++ qstr (snd (model_of tok e)) ++ 44 :: key k_owned ++ owned_text e ++
      44 :: key k_age_ms ++ dec (age_of now (e_last_seen e)) ++ 125 :: c :: rest)).
    exists (length B - 6)%nat. unfold jlen in Hb. lia. }
  destruct EB as [f EB]. rewrite EB.
  assert (K1 : Forall strc k_mac) by (unfold k_mac; strc_lit).
  assert (K2 : Forall strc k_role) by (unfold k_role; strc_lit).
  assert (K3 : Forall strc k_model) by (unfold k_model; strc_lit).
  assert (K4 : Forall strc k_width) by (unfold k_width; strc_lit).
  assert (K5 : Forall strc k_owned) by (unfold k_owned; strc_lit).
  assert (K6 : Forall strc k_age_ms) by (unfold k_age_ms; strc_lit).
  pose proof (val_str _ _ _ _ (seg_val _ _ _ _ S1) Fm) as V1. pose proof (pair_seg _ _ _ _ _ _ S1) as S2.
  rewrite (pair_next_eq _ _ _ _ _ _ _ _ _ 0%nat _ _ S1 K1 V1 (qstr_start _) eq_refl) by reflexivity.
  pose proof (val_str _ _ _ _ (seg_val _ _ _ _ S2) Fr) as V2. pose proof (pair_seg _ _ _ _ _ _ S2) as S3.
  rewrite (pair_next_eq _ _ _ _ _ _ _ _ _ 1%nat _ _ S2 K2 V2 (qstr_start _) eq_refl) by reflexivity.
  pose proof (val_str _ _ _ _ (seg_val _ _ _ _ S3) Fmd) as V3. pose proof (pair_seg _ _ _ _ _ _ S3) as S4.
  rewrite (pair_next_eq _ _ _ _ _ _ _ _ _ 2%nat _ _ S3 K3 V3 (qstr_start _) eq_refl) by reflexivity.
  pose proof (val_str _ _ _ _ (seg_val _ _ _ _ S4) Fwd) as V4. pose proof (pair_seg _ _ _ _ _ _ S4) as S5.
  rewrite (pair_next_eq _ _ _ _ _ _ _ _ _ 3%nat _ _ S4 K4 V4 (qstr_start _) eq_refl) by reflexivity.
  pose proof (val_owned _ _ _ _ (seg_val _ _ _ _ S5)) as V5. pose proof (pair_seg _ _ _ _ _ _ S5) as S6.
  rewrite (pair_next_eq _ _ _ _ _ _ _ _ _ 4%nat _ _ S5 K5 V5 (owned_start _) eq_refl) by reflexivity.
  pose proof (val_dec _ _ _ _ (seg_val _ _ _ _ S6) Ha) as V6.
  rewrite (pair_last _ _ _ _ _ _ _ _ 5%nat _ _ S6 K6 V6 (dec_start _ Ha) eq_refl) by reflexivity.
  eexists. split.
  - apply some_pair. rewrite Hbl. lia.
  - unfold obj_view, exp_view, jobj_empty. cbn [repeat set_nth map tv_kind fst snd].
    rewrite (seg_qstr_text _ _ _ _ _ (seg_val _ _ _ _ S1)), (seg_qstr_text _ _ _ _ _ (seg_val _ _ _ _ S2)),
      (seg_qstr_text _ _ _ _ _ (seg_val _ _ _ _ S3)), (seg_qstr_text _ _ _ _ _ (seg_val _ _ _ _ S4)),
      (seg_plain_text _ _ _ _ _ (seg_val _ _ _ _ S5)), (seg_plain_text _ _ _ _ _ (seg_val _ _ _ _ S6)).
    reflexivity.
Qed.

Definition tail_text tok (now : Z) (T : list entry) : list Z := concat (map (fun e => [44] ++ body tok now e) T).

Lemma obj_text_body : forall tok now k e, obj_text tok now k e = (if Nat.eqb k 0 then [] else [44]) ++ body tok now e.
Proof. intros. unfold obj_text, P1, body. rewrite <- !app_assoc. reflexivity. Qed.

Lemma objs_text_S : forall tok now T k, objs_text tok now (S k) T = tail_text tok now T.
Proof.
  intros tok now T. induction T as [|e T IH]; intros k; [reflexivity|].
  cbn [objs_text]. rewrite obj_text_body, IH. reflexivity.
Qed.

Lemma tail_text_cons : forall tok now e T, tail_text tok now (e :: T) = [44] ++ body tok now e ++ tail_text tok now T.
Proof. intros. unfold tail_text. cbn [map concat]. rewrite <- app_assoc. reflexivity. Qed.

Lemma body_start : forall tok now e, exists w, body tok now e = 123 :: key k_mac ++ w.
Proof. intros. eexists. unfold body. reflexivity. Qed.

Lemma objs_run : forall tok now B T' e i count acc f, tok_ok tok -> Forall entry_wf (e :: T') -> 0 <= now < 2 ^ 64 ->
  seg B i (body tok now e ++ tail_text tok now T' ++ [93]) ->
  i + jlen (body tok now e ++ tail_text tok now T' ++ [93]) = jlen B ->
  (length T' < f)%nat -> 0 <= count -> count + 1 + Z.of_nat (length T') <= 9 ->
  exists os, json_objs B i count 9 acc f = Some (count + 1 + Z.of_nat (length T'), acc ++ os) /\
    Forall2 (fun e o => obj_view B o = exp_view tok now e) (e :: T') os.
Proof.
  intros tok now B T'. induction T' as [|e' T' IH]; intros e i count acc f Ht Hw Hn H HL Hf Hc0 Hc;
    destruct f as [|f]; try (cbn in Hf; lia); apply Forall_cons_iff in Hw as [He Hw].
  - destruct (body_start tok now e) as [w Ew].
    assert (H0 : seg B i (123 :: key k_mac ++ w ++ [93]))
      by (rewrite Ew in H; cbn [tail_text map concat app] in H; rewrite <- !app_assoc in H; exact H).
    assert (H1 : seg B i (body tok now e ++ 93 :: [])) by exact H.
    destruct (obj_parse tok now e B i 93 [] Ht He Hn H1) as (o & Eo & Vo).
    pose proof (seg_after _ _ _ _ H1) as Hend.
    cbn [json_objs]. rewrite (at_byte_seg _ _ _ _ _ H0). cbn [Z.eqb Pos.eqb negb]. cbv beta iota zeta.
    pose proof (seg_cons _ _ _ _ H0) as H2.
    rewrite (ws_key _ _ _ _ H2). unfold key in H2. cbn [app] in H2.
    rewrite (at_byte_seg _ _ _ _ _ H2). cbn [Z.eqb Pos.eqb]. cbv beta iota zeta.
    rewrite Eo. cbv beta iota zeta.
    replace (count <? 9) with true by (symmetry; apply Z.ltb_lt; cbn in Hc; lia).
    rewrite (json_ws_stop _ _ _ _ Hend eq_refl), (at_byte_seg _ _ _ _ _ Hend), (at_byte_seg _ _ _ _ _ Hend).
    cbn [Z.eqb Pos.eqb]. cbv beta iota.
    replace (i + jlen (body tok now e) + 1) with (jlen B)
      by (rewrite <- HL; cbn [tail_text map concat]; rewrite !jlen_app, jlen_cons, jlen_nil; lia).
    rewrite json_ws_end, Z.eqb_refl. exists [o]. split.
    + cbn [length Z.of_nat]. f_equal. f_equal. lia.
    + constructor; [exact Vo|constructor].
  - destruct (body_start tok now e) as [w Ew].
    assert (H0 : seg B i (123 :: key k_mac ++ w ++ tail_text tok now (e' :: T') ++ [93]))
      by (rewrite Ew in H; cbn [app] in H; rewrite <- !app_assoc in H; exact H).
    rewrite tail_text_cons in H, HL.
    assert (H1 : seg B i (body tok now e ++ 44 :: (body tok now e' ++ tail_text tok now T') ++ [93]))
      by (rewrite <- !app_assoc in H; rewrite <- !app_assoc; exact H).
    destruct (obj_parse tok now e B i 44 _ Ht He Hn H1) as (o & Eo & Vo).
    pose proof (seg_after _ _ _ _ H1) as Hnext.
    pose proof (seg_cons _ _ _ _ Hnext) as H3. rewrite <- !app_assoc in H3.
    destruct (body_start tok now e') as [w' Ew'].
    assert (H4 : seg B (i + jlen (body tok now e) + 1) (123 :: key k_mac ++ w' ++ tail_text tok now T' ++ [93]))
      by (rewrite Ew' in H3; cbn [app] in H3; rewrite <- !app_assoc in H3; exact H3).
    cbn [json_objs]. rewrite (at_byte_seg _ _ _ _ _ H0). cbn [Z.eqb Pos.eqb negb]. cbv beta iota zeta.
    pose proof (seg_cons _ _ _ _ H0) as H2.
    rewrite (ws_key _ _ _ _ H2). unfold key in H2. cbn [app] in H2.
    rewrite (at_byte_seg _ _ _ _ _ H2). cbn [Z.eqb Pos.eqb]. cbv beta iota zeta.
    rewrite Eo. cbv beta iota zeta.
    replace (count <? 9) with true by (symmetry; apply Z.ltb_lt; cbn [length] in Hc; lia).
    rewrite (json_ws_stop _ _ _ _ Hnext eq_refl), (at_byte_seg _ _ _ _ _ Hnext).
    cbn [Z.eqb Pos.eqb]. cbv beta iota.
    rewrite (json_ws_stop _ _ _ _ H4 eq_refl).
    destruct (IH e' (i + jlen (body tok now e) + 1) (count + 1) (acc ++ [o]) f Ht Hw Hn H3)
      as (os & E & F).
    + rewrite <- HL. rewrite !jlen_app, !jlen_cons, !jlen_nil. lia.
    + cbn in Hf. lia.
    + lia.
    + cbn [length] in Hc. lia.
    + rewrite E. exists (o :: os). split.
      * rewrite <- app_assoc. cbn [app length]. f_equal. f_equal. lia.
      * constructor; [exact Vo|exact F].
Qed.

Lemma tail_len : forall tok now T, Z.of_nat (length T) <= jlen (tail_text tok now T).
Proof.
  intros tok now T. induction T as [|e T IH]; [cbn; lia|]. rewrite tail_text_cons, !jlen_app, jlen_cons, jlen_nil.
  pose proof (jlen_nonneg (body tok now e)). cbn [length]. lia.
Qed.

Lemma text_cons : forall tok e T now,
  table_json_text tok (e :: T) now = [91] ++ body tok now e ++ tail_text tok now T ++ [93].
Proof.
  intros. unfold table_json_text. cbn [objs_text]. rewrite obj_text_body, objs_text_S. cbn [Nat.eqb app].
  rewrite <- !app_assoc. reflexivity.
Qed.

Theorem F1_2_json_read_table : forall tok T now, tok_ok tok -> table_ok T -> Forall entry_wf T -> 0 <= now < 2 ^ 64 ->
  exists os, json_read (table_json_text tok T now) 9 = Some (Z.of_nat (length T), os) /\
    Forall2 (fun e o => obj_view (table_json_text tok T now) o = exp_view tok now e) T os.
Proof.
  intros tok T now Ht HT Hw Hn. destruct T as [|e T'].
  - exists []. split; [reflexivity|constructor].
  - set (X := table_json_text tok (e :: T') now). assert (EX := text_cons tok e T' now). fold X in EX.
    assert (S1 : seg X 1 (body tok now e ++ tail_text tok now T' ++ [93]))
      by (exists [91], []; rewrite app_nil_r; split; [exact EX|reflexivity]).
    assert (S0 : seg X 0 (91 :: body tok now e ++ tail_text tok now T' ++ [93]))
      by (exists [], []; rewrite app_nil_r; split; [exact EX|reflexivity]).
    destruct (body_start tok now e) as [w Ew].
    assert (S1' : seg X 1 (123 :: key k_mac ++ w ++ tail_text tok now T' ++ [93]))
      by (rewrite Ew in S1; cbn [app] in S1; rewrite <- !app_assoc in S1; exact S1).
    assert (HL : 1 + jlen (body tok now e ++ tail_text tok now T' ++ [93]) = jlen X)
      by (rewrite EX, (jlen_app [91]); reflexivity).
    destruct HT as (HT1 & _).
    destruct (objs_run tok now X T' e 1 0 [] (length X) Ht Hw Hn S1 HL) as (os & E & F).
    + pose proof (tail_len tok now T'). rewrite !jlen_app in HL. pose proof (jlen_nonneg (body tok now e)).
      change (jlen [93]) with 1 in HL. assert (jlen X = Z.of_nat (length X)) by reflexivity. lia.
    + lia.
    + cbn [length] in HT1. lia.
    + exists os. split; [|exact F]. unfold json_read.
      rewrite (json_ws_stop X 0 91 _ S0 eq_refl), (at_byte_seg X 0 91 _ 91 S0). cbn [Z.eqb Pos.eqb negb].
      cbv beta iota zeta. change (0 + 1) with 1.
      rewrite (json_ws_stop X 1 123 _ S1' eq_refl), (at_byte_seg X 1 123 _ 93 S1'). cbn [Z.eqb Pos.eqb].
      cbv beta iota. rewrite E. cbn [app length]. f_equal. f_equal. lia.
Qed.

Lemma lzeqb_true : forall a b, lzeqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try congruence.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - inversion H. subst. rewrite Z.eqb_refl. apply IH. reflexivity.
Qed.

Lemma jtok_view : forall B o k kd l x kind text, nth_error (obj_view B o) k = Some (kd, l, x) ->
  jtok_is B (nth k o tok_none) kind text = (kd =? kind) && (l =? jlen text) && lzeqb x text.
Proof.
  intros B o k kd l x kind text H. unfold obj_view in H. rewrite nth_error_map in H.
  destruct (nth_error o k) as [t|] eqn:E; [|discriminate]. cbn in H. inversion H. subst.
  rewrite (nth_error_nth o k tok_none E). reflexivity.
Qed.

Lemma Forall2_nth : forall {A B} (P : A -> B -> Prop) l1 l2 k a b, Forall2 P l1 l2 ->
  nth_error l1 k = Some a -> nth_error l2 k = Some b -> P a b.
Proof.
  intros A B P l1 l2 k a b H. revert k. induction H as [|x y l1 l2 Hxy H IH]; intros k E1 E2.
  - destruct k; discriminate.
  - destruct k; cbn in E1, E2; [inversion E1; inversion E2; subst; exact Hxy|exact (IH k E1 E2)].
Qed.

Theorem F1_3_serialise_finds : forall tok T now os, tok_ok tok -> table_ok T -> Forall entry_wf T -> 0 <= now < 2 ^ 64 ->
  json_read (table_json_text tok T now) 9 = Some (Z.of_nat (length T), os) ->
  forall k o ek, nth_error os k = Some o -> nth_error T k = Some ek ->
    (forall j ej, nth_error T j = Some ej ->
       jtok_is (table_json_text tok T now) (nth 0 o tok_none) 1 (mac_text (e_mac ej)) = true <-> j = k) /\
    jtok_is (table_json_text tok T now) (nth 1 o tok_none) 1 (rolename (e_role ek)) = true /\
    jtok_is (table_json_text tok T now) (nth 2 o tok_none) 1 (fst (model_of tok ek)) = true /\
    jtok_is (table_json_text tok T now) (nth 3 o tok_none) 1 (snd (model_of tok ek)) = true /\
    jtok_is (table_json_text tok T now) (nth 4 o tok_none) 3 (owned_text ek) = true /\
    jtok_is (table_json_text tok T now) (nth 5 o tok_none) 2 (dec (age_of now (e_last_seen ek))) = true.
Proof.
  intros tok T now os Ht HT Hw Hn Hr k o ek Eo Ek.
  destruct (F1_2_json_read_table tok T now Ht HT Hw Hn) as (os' & Hr' & F).
  rewrite Hr in Hr'. inversion Hr'. subst os'.
  pose proof (Forall2_nth _ _ _ _ _ _ F Ek Eo) as V.
  set (X := table_json_text tok T now) in *.
  assert (G : forall n kd l x, nth_error (exp_view tok now ek) n = Some (kd, l, x) ->
    forall kind text, jtok_is X (nth n o tok_none) kind text = (kd =? kind) && (l =? jlen text) && lzeqb x text).
  { intros n kd l x E. rewrite <- V in E. intros. apply jtok_view. exact E. }
  split; [|repeat split].
  - intros j ej Ej. rewrite (G 0%nat _ _ _ eq_refl). cbn [Z.eqb Pos.eqb andb].
    rewrite Forall_forall in Hw. destruct (Hw ek (nth_error_In _ _ Ek)) as (Lk & Bk & _).
    destruct (Hw ej (nth_error_In _ _ Ej)) as (Lj & Bj & _).
    split.
    + intros H. apply andb_prop in H as [_ H]. apply lzeqb_true in H.
      apply mac_text_inj in H; try assumption.
      destruct HT as (_ & _ & ND & _). rewrite NoDup_nth_error in ND.
      apply ND; [rewrite length_map; apply nth_error_Some; congruence|].
      rewrite !nth_error_map, Ej, Ek. cbn. rewrite H. reflexivity.
    + intros ->. rewrite Ej in Ek. inversion Ek. subst. rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
  - rewrite (G 1%nat _ _ _ eq_refl). rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
  - rewrite (G 2%nat _ _ _ eq_refl). rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
  - rewrite (G 3%nat _ _ _ eq_refl). rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
  - rewrite (G 4%nat _ _ _ eq_refl). rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
  - rewrite (G 5%nat _ _ _ eq_refl). rewrite !Z.eqb_refl, (proj2 (lzeqb_true _ _) eq_refl). reflexivity.
Qed.

Lemma ge32_strc : forall s, Forall strc s -> Forall (fun c => 32 <= c) s.
Proof. intros s F. eapply Forall_impl; [|exact F]. intros c H. unfold strc in H. lia. Qed.

Lemma hex2_ge32 : forall x, 0 <= x -> Forall (fun c => 32 <= c) (hex2 x).
Proof.
  intros x H. pose proof (Z.div_pos x 16 H ltac:(lia)). pose proof (Z.mod_pos_bound x 16 ltac:(lia)).
  unfold hex2, hexc. destruct (x / 16 <? 10), (x mod 16 <? 10); repeat constructor; lia.
Qed.

Lemma body_ge32 : forall tok now e, tok_ok tok -> entry_wf e -> 0 <= now < 2 ^ 64 ->
  Forall (fun c => 32 <= c) (body tok now e).
Proof.
  intros tok now e Ht Hw Hn.
  assert (HmB : Forall byte_ok (e_mac e)) by apply Hw.
  assert (Fm : Forall strc (mac_text (e_mac e))) by (apply strc_mac; apply Hw).
  pose proof (strc_rolename (e_role e)) as Fr.
  pose proof (strc_model tok e Ht) as Fmd.
  pose proof (strc_width tok e Hw) as Fwd.
  assert (Ha : 0 <= age_of now (e_last_seen e) < 10 ^ 20).
  { pose proof (age_range now (e_last_seen e) Hn ltac:(apply Hw)). lia. }
  unfold body, P2, P3, P4, P5, P6, key, qstr, k_mac, k_role, k_model, k_width, k_owned, k_age_ms.
  repeat (apply Forall_app; split);
  try first [ apply ge32_strc; assumption
        | apply ge32_strc, strc_digits, (proj1 (dec_spec _ Ha))
        | unfold owned_text, s_true, s_false; destruct (e_owned e =? 0); repeat apply Forall_cons; try apply Forall_nil; lia
        | repeat apply Forall_cons; try apply Forall_nil; lia ].
  all: apply hex2_ge32; apply (proj1 (nth_byte_ok _ _ HmB)).
Qed.

Lemma objs_ge32 : forall tok now T k, tok_ok tok -> Forall entry_wf T -> 0 <= now < 2 ^ 64 ->
  Forall (fun c => 32 <= c) (objs_text tok now k T).
Proof.
  intros tok now T. induction T as [|e T IH]; intros k Ht Hw Hn; [constructor|].
  apply Forall_cons_iff in Hw as [He Hw]. cbn [objs_text]. rewrite obj_text_body.
  apply Forall_app; split; [apply Forall_app; split|].
  - destruct (Nat.eqb k 0); repeat apply Forall_cons; try apply Forall_nil; lia.
  - apply body_ge32; assumption.
  - apply IH; assumption.
Qed.

Theorem F1_1_text_shape : forall tok T now, tok_ok tok -> table_ok T -> Forall entry_wf T -> 0 <= now < 2 ^ 64 ->
  ~ In 0 (table_json_text tok T now) /\ nth 0 (table_json_text tok T now) 0 = 91 /\
  nth (length (table_json_text tok T now) - 1) (table_json_text tok T now) 0 = 93 /\
  (2 <= length (table_json_text tok T now))%nat.
Proof.
  intros tok T now Ht HT Hw Hn. split; [|split; [|split]].
  - intros H. assert (F : Forall (fun c => 32 <= c) (table_json_text tok T now)).
    { unfold table_json_text. apply Forall_app; split; [repeat constructor; lia|].
      apply Forall_app; split; [apply objs_ge32; assumption|repeat constructor; lia]. }
    rewrite Forall_forall in F. specialize (F 0 H). lia.
  - reflexivity.
  - unfold table_json_text. rewrite app_assoc, length_app. cbn [length]. rewrite Nat.add_sub.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - unfold table_json_text. rewrite !length_app. cbn [length]. lia.
Qed.

Definition entry_t4 (e : entry) : Prop :=
  (e_has_decl e = 0 \/ (e_has_decl e = 1 /\ e_decl_in e <= 40 /\ e_decl_out e <= 40)) /\
  (e_owned e = 0 \/ e_owned e = 1).

Lemma dec_len2 : forall v, 0 <= v <= 40 -> jlen (dec v) <= 2.
Proof.
  intros v H. destruct (dec_spec v ltac:(lia)) as (_ & _ & _ & D). specialize (D 2 ltac:(lia) ltac:(lia)).
  unfold jlen. cbn in D. lia.
Qed.

Lemma body_len : forall tok now e, tok_ok tok -> entry_wf e -> entry_t4 e -> 0 <= now < 2 ^ 64 ->
  jlen (body tok now e) <= 120.
Proof.
  intros tok now e Ht Hw H4 Hn.
  destruct Hw as (_ & _ & _ & Hi & Ho & _ & _ & _ & Hls). unfold byte_ok in Hi, Ho.
  assert (Lm : jlen (mac_text (e_mac e)) = 17) by reflexivity.
  assert (Lr : jlen (rolename (e_role e)) <= 7)
    by (unfold rolename; destruct (e_role e =? 1); [|destruct (e_role e =? 2)]; cbn; lia).
  assert (Lmd : jlen (fst (model_of tok e)) <= 11).
  { unfold model_of. destruct (e_has_decl e =? 0); [cbn; lia|].
    destruct (tok (e_family e) (e_decl_in e) (e_decl_out e)) as [t|] eqn:E; [|cbn; lia].
    cbn [fst]. destruct (Ht _ _ _ _ E) as [L _]. unfold jlen. lia. }
  assert (Lw : jlen (snd (model_of tok e)) <= 5).
  { unfold model_of. destruct (Z.eqb_spec (e_has_decl e) 0) as [E0|E0]; [cbn; lia|].
    destruct H4 as [[D|(D1 & D2 & D3)] _]; [congruence|].
    destruct (tok (e_family e) (e_decl_in e) (e_decl_out e)); [|cbn; lia].
    cbn [snd]. rewrite !jlen_app, jlen_cons, jlen_nil.
    pose proof (dec_len2 (e_decl_in e) ltac:(lia)). pose proof (dec_len2 (e_decl_out e) ltac:(lia)). lia. }
  assert (Lo : jlen (owned_text e) <= 5) by (unfold owned_text; destruct (e_owned e =? 0); cbn; lia).
  assert (Ld : jlen (dec (age_of now (e_last_seen e))) <= 14).
  { pose proof (age_range now (e_last_seen e) Hn Hls) as Ha.
    destruct (dec_spec (age_of now (e_last_seen e)) ltac:(lia)) as (_ & _ & _ & D).
    specialize (D 14 ltac:(lia) ltac:(lia)).
    unfold jlen. cbn in D. lia. }
  unfold body, P2, P3, P4, P5, P6. rewrite !jlen_app, !jlen_key, !jlen_qstr, !jlen_cons, !jlen_nil.
  change (jlen k_mac) with 3. change (jlen k_role) with 4. change (jlen k_model) with 5.
  change (jlen k_width) with 5. change (jlen k_owned) with 5. change (jlen k_age_ms) with 6. lia.
Qed.

Lemma tail_bound : forall tok now T, tok_ok tok -> Forall entry_wf T -> Forall entry_t4 T -> 0 <= now < 2 ^ 64 ->
  jlen (tail_text tok now T) <= 121 * Z.of_nat (length T).
Proof.
  intros tok now T Ht. induction T as [|e T IH]; intros Hw H4 Hn; [cbn; lia|].
  apply Forall_cons_iff in Hw as [He Hw]. apply Forall_cons_iff in H4 as [H4e H4].
  rewrite tail_text_cons, !jlen_app, jlen_cons, jlen_nil.
  pose proof (body_len tok now e Ht He H4e Hn). specialize (IH Hw H4 Hn). cbn [length]. lia.
Qed.

Theorem C7_text_bound : forall tok T now, tok_ok tok -> table_ok T -> Forall entry_wf T -> 0 <= now < 2 ^ 64 ->
  (length (table_json_text tok T now) <= 969)%nat.
Proof.
  intros tok T now Ht HT Hw Hn. destruct HT as (HT1 & _ & _ & HT4).
  assert (H4 : Forall entry_t4 T) by exact HT4.
  destruct T as [|e T']; [cbn; lia|].
  apply Forall_cons_iff in Hw as [He Hw]. apply Forall_cons_iff in H4 as [H4e H4].
  assert (J : jlen (table_json_text tok (e :: T') now) <= 969).
  { rewrite text_cons, !jlen_app, jlen_cons, jlen_cons, jlen_nil.
    pose proof (body_len tok now e Ht He H4e Hn). pose proof (tail_bound tok now T' Ht Hw H4 Hn).
    cbn [length] in HT1. lia. }
  unfold jlen in J. lia.
Qed.
