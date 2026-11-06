(* fuzz_preset lib/A, slice S4 (parse_string's decode stretch, S4_PsDec.v): the PURE model layer. Machine-state-free
   facts over PjGrammar (decode, escape, hex4, utf8, low, pair_cp, scan) and PRH_Reader's rest_atR, in the shape the
   walk's cuts use: one decode STEP of the loop at the read cursor r is `decode (rest r) = emit bs (decode (rest r'))`
   with r' the cursor after the step, and scan moves by the same bytes. Statements restate the shape of preset's plain
   lib/Prog/parse_string_loops.v (psl_acc, psl_hex_turn) for this walk's engine; no proof is taken from there.
   Numerals: byte values of the JSON grammar (WORD: 34 the quote, 92 the backslash, 117 u, 32, the escape letters) and the
   surrogate bounds 55296 / 56320 / 57344 / 1024 (WORD, PjGrammar's own); no ADDRESS. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Open Scope Z_scope.

(* ---- the text after a cursor ---- *)
Lemma psd_skipn_nth : forall (l : list Z) k c, nth_error l k = Some c -> skipn k l = c :: skipn (S k) l.
Proof.
  intros l. induction l as [|h t IH]; intros k c H; destruct k; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.
Lemma psd_rest_cons : forall tb text x c, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c ->
  rest_atR tb text x = c :: rest_atR tb text (x + 1).
Proof.
  intros tb text x c Hx Hc. unfold rest_atR. rewrite (psd_skipn_nth _ _ c Hc).
  replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia. reflexivity.
Qed.
Lemma psd_rest_shift : forall tb text x k, text <= x -> 0 <= k ->
  rest_atR tb text (x + k) = skipn (Z.to_nat k) (rest_atR tb text x).
Proof.
  intros tb text x k Hx Hk. unfold rest_atR. rewrite skipn_skipn. f_equal. lia.
Qed.
Lemma psd_rest_len : forall tb text x, text <= x ->
  length (rest_atR tb text x) = (length tb - Z.to_nat (x - text))%nat.
Proof. intros tb text x Hx. unfold rest_atR. apply length_skipn. Qed.
(* a byte of the rest: the list's i-th element is the text's (x + i)-th byte *)
Lemma psd_rest_nth : forall tb text x i, text <= x -> 0 <= i ->
  nth_error (rest_atR tb text x) (Z.to_nat i) = nth_error tb (Z.to_nat (x + i - text)).
Proof.
  intros tb text x i Hx Hi. unfold rest_atR. rewrite nth_error_skipn. f_equal. lia.
Qed.

(* ---- decode as the loop writes it: the outcome so far and the outcome of the rest ---- *)
(* `done` is what has been written; the decode of the whole text is `done` followed by the decode of x *)
Definition psd_rel (D : option (list Z * list Z)) (done x : list Z) : Prop :=
  (forall sx rx, decode x = Some (sx, rx) -> D = Some (done ++ sx, rx)) /\ (decode x = None -> D = None).
Lemma psd_rel_step : forall D done x bs x',
  psd_rel D done x -> decode x = emit bs (decode x') -> psd_rel D (done ++ bs) x'.
Proof.
  intros D done x bs x' [HS HN] Hx. split.
  - intros sx rx Hd. rewrite Hd in Hx. cbn [emit] in Hx. rewrite <- app_assoc. exact (HS _ _ Hx).
  - intros Hd. rewrite Hd in Hx. cbn [emit] in Hx. exact (HN Hx).
Qed.
Lemma psd_rel_none : forall D done x, psd_rel D done x -> decode x = None -> D = None.
Proof. intros D done x [_ HN] Hd. exact (HN Hd). Qed.
Lemma psd_rel_quote : forall D done x, psd_rel D done (34 :: x) -> D = Some (done, x).
Proof. intros D done x [HS _]. rewrite <- (app_nil_r done). apply HS. reflexivity. Qed.
Lemma psd_rel_init : forall x, psd_rel (decode x) [] x.
Proof. intros x. split; [intros sx rx H; rewrite H; reflexivity | intros H; exact H]. Qed.

(* ---- one decode step ---- *)
Lemma psd_dec_plain : forall b x, b <> 34 -> 32 <= b -> b <> 92 -> decode (b :: x) = emit [b] (decode x).
Proof.
  intros b x H34 H32 H92. cbn [decode].
  replace (b =? 34) with false by (symmetry; apply Z.eqb_neq; exact H34).
  replace (b <? 32) with false by (symmetry; apply Z.ltb_ge; exact H32).
  replace (negb (b =? 92)) with true by (rewrite (proj2 (Z.eqb_neq b 92) H92); reflexivity).
  reflexivity.
Qed.
Lemma psd_dec_ctl : forall b x, b <> 34 -> b < 32 -> decode (b :: x) = None.
Proof.
  intros b x H34 H32. cbn [decode].
  replace (b =? 34) with false by (symmetry; apply Z.eqb_neq; exact H34).
  replace (b <? 32) with true by (symmetry; apply Z.ltb_lt; exact H32). reflexivity.
Qed.
Lemma psd_dec_bs_end : decode [92] = None.
Proof. reflexivity. Qed.
Lemma psd_dec_esc : forall e c x, e <> 117 -> escape e = Some c -> decode (92 :: e :: x) = emit [c] (decode x).
Proof.
  intros e c x Hu He. cbn [decode]. replace (e =? 117) with false by (symmetry; apply Z.eqb_neq; exact Hu).
  rewrite He. reflexivity.
Qed.
Lemma psd_dec_esc_bad : forall e x, e <> 117 -> escape e = None -> decode (92 :: e :: x) = None.
Proof.
  intros e x Hu He. cbn [decode]. replace (e =? 117) with false by (symmetry; apply Z.eqb_neq; exact Hu).
  rewrite He. reflexivity.
Qed.
(* \u with fewer than four bytes after it *)
Lemma psd_dec_u_short : forall x, (length x < 4)%nat -> decode (92 :: 117 :: x) = None.
Proof.
  intros x Hx. cbn [decode Z.eqb Pos.eqb].
  destruct x as [|a [|b [|c [|d x]]]]; cbn in Hx; try lia; reflexivity.
Qed.
Lemma psd_dec_u_nohex : forall h0 h1 h2 h3 x, hex4 [h0; h1; h2; h3] = None ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = None.
Proof.
  intros h0 h1 h2 h3 x H. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity. rewrite H. reflexivity.
Qed.
Lemma psd_dec_u_zero : forall h0 h1 h2 h3 x, hex4 [h0; h1; h2; h3] = Some 0 ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = None.
Proof.
  intros h0 h1 h2 h3 x H. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity. rewrite H. reflexivity.
Qed.
Lemma psd_dec_u_lone_low : forall h0 h1 h2 h3 x cp, hex4 [h0; h1; h2; h3] = Some cp -> 56320 <= cp < 57344 ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = None.
Proof.
  intros h0 h1 h2 h3 x cp H Hc. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity. rewrite H.
  replace (cp =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((55296 <=? cp) && (cp <? 56320)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((56320 <=? cp) && (cp <? 57344)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.
Lemma psd_dec_u_bmp : forall h0 h1 h2 h3 x cp, hex4 [h0; h1; h2; h3] = Some cp -> cp <> 0 ->
  ~ (55296 <= cp < 57344) ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = emit (utf8 cp) (decode x).
Proof.
  intros h0 h1 h2 h3 x cp H H0 Hs. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity. rewrite H.
  replace (cp =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace ((55296 <=? cp) && (cp <? 56320)) with false
    by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec cp 55296); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
  replace ((56320 <=? cp) && (cp <? 57344)) with false
    by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec cp 56320); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
  reflexivity.
Qed.
(* a high surrogate with fewer than six bytes after its four digits *)
Lemma psd_dec_hi_short : forall h0 h1 h2 h3 x cp, hex4 [h0; h1; h2; h3] = Some cp -> 55296 <= cp < 56320 ->
  (length x < 6)%nat -> decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = None.
Proof.
  intros h0 h1 h2 h3 x cp H Hc Hx. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity. rewrite H.
  replace (cp =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((55296 <=? cp) && (cp <? 56320)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  destruct x as [|a [|b [|c [|d [|e [|f x]]]]]]; cbn in Hx; try lia; reflexivity.
Qed.
Lemma psd_dec_hi_nolow : forall h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x cp, hex4 [h0; h1; h2; h3] = Some cp ->
  55296 <= cp < 56320 -> low [b0; b1; b2; b3; b4; b5] = None ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x) = None.
Proof.
  intros h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x cp H Hc Hl. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity.
  rewrite H.
  replace (cp =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((55296 <=? cp) && (cp <? 56320)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (low (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x)) with (low [b0; b1; b2; b3; b4; b5]) by reflexivity.
  rewrite Hl. reflexivity.
Qed.
Lemma psd_dec_pair : forall h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x cp lo, hex4 [h0; h1; h2; h3] = Some cp ->
  55296 <= cp < 56320 -> low [b0; b1; b2; b3; b4; b5] = Some lo ->
  decode (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x) =
  emit (utf8 (pair_cp cp lo)) (decode x).
Proof.
  intros h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x cp lo H Hc Hl. cbn [decode Z.eqb Pos.eqb].
  replace (hex4 (h0 :: h1 :: h2 :: h3 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x)) with (hex4 [h0; h1; h2; h3]) by reflexivity.
  rewrite H.
  replace (cp =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((55296 <=? cp) && (cp <? 56320)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (low (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x)) with (low [b0; b1; b2; b3; b4; b5]) by reflexivity.
  rewrite Hl. reflexivity.
Qed.
(* low's three outcomes, as the code tests them: the '\', the 'u', then hex4 and the range *)
Lemma psd_low_nobs : forall b0 b1 b2 b3 b4 b5, b0 <> 92 -> low [b0; b1; b2; b3; b4; b5] = None.
Proof. intros b0 b1 b2 b3 b4 b5 H. cbn [low]. replace (b0 =? 92) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.
Lemma psd_low_nou : forall b1 b2 b3 b4 b5, b1 <> 117 -> low [92; b1; b2; b3; b4; b5] = None.
Proof. intros b1 b2 b3 b4 b5 H. cbn [low]. replace (b1 =? 117) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.
Lemma psd_low_hex : forall b2 b3 b4 b5,
  low [92; 117; b2; b3; b4; b5] =
  match hex4 [b2; b3; b4; b5] with
  | Some lo => if (56320 <=? lo) && (lo <=? 57343) then Some lo else None
  | None => None
  end.
Proof. reflexivity. Qed.

(* ---- scan moves with decode ---- *)
Lemma psd_scan_plain : forall b x, b <> 34 -> b <> 92 -> scan (b :: x) = option_map S (scan x).
Proof.
  intros b x H34 H92. cbn [scan].
  replace (b =? 34) with false by (symmetry; apply Z.eqb_neq; exact H34).
  replace (b =? 92) with false by (symmetry; apply Z.eqb_neq; exact H92). reflexivity.
Qed.
Lemma psd_scan_esc : forall e x, scan (92 :: e :: x) = option_map (fun q => S (S q)) (scan x).
Proof. intros e x. reflexivity. Qed.
(* a step that consumes c bytes moves the closing quote c bytes nearer *)
Lemma psd_scan_sync : forall x x' (c k : nat),
  scan x = option_map (fun q => (q + c)%nat) (scan x') -> scan x = Some k -> scan x' = Some (k - c)%nat /\ (c <= k)%nat.
Proof.
  intros x x' c k E Hk. rewrite Hk in E. destruct (scan x') as [q|]; cbn [option_map] in E; [|discriminate].
  injection E as E. subst k. split; [f_equal; lia | lia].
Qed.
Lemma psd_hex_nq : forall b v, hexval b = Some v -> b <> 34 /\ b <> 92.
Proof.
  intros b v H. unfold hexval in H. split; intros ->; cbn in H; discriminate.
Qed.
Lemma psd_scan_hex4 : forall h0 h1 h2 h3 x v, hex4 [h0; h1; h2; h3] = Some v ->
  scan (h0 :: h1 :: h2 :: h3 :: x) = option_map (fun q => (q + 4)%nat) (scan x).
Proof.
  intros h0 h1 h2 h3 x v H. cbn [hex4] in H.
  destruct (hexval h0) as [v0|] eqn:E0; [|discriminate]. destruct (hexval h1) as [v1|] eqn:E1; [|discriminate].
  destruct (hexval h2) as [v2|] eqn:E2; [|discriminate]. destruct (hexval h3) as [v3|] eqn:E3; [|discriminate].
  destruct (psd_hex_nq _ _ E0) as [A0 B0]. destruct (psd_hex_nq _ _ E1) as [A1 B1].
  destruct (psd_hex_nq _ _ E2) as [A2 B2]. destruct (psd_hex_nq _ _ E3) as [A3 B3].
  rewrite (psd_scan_plain _ _ A0 B0), (psd_scan_plain _ _ A1 B1), (psd_scan_plain _ _ A2 B2), (psd_scan_plain _ _ A3 B3).
  destruct (scan x); cbn; [f_equal; lia | reflexivity].
Qed.
Lemma psd_scan_u : forall h0 h1 h2 h3 x v, hex4 [h0; h1; h2; h3] = Some v ->
  scan (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: x) = option_map (fun q => (q + 6)%nat) (scan x).
Proof.
  intros h0 h1 h2 h3 x v H. rewrite psd_scan_esc, (psd_scan_hex4 _ _ _ _ _ _ H).
  destruct (scan x); cbn; [f_equal; lia | reflexivity].
Qed.
Lemma psd_low_hex4 : forall b0 b1 b2 b3 b4 b5 lo, low [b0; b1; b2; b3; b4; b5] = Some lo ->
  b0 = 92 /\ b1 = 117 /\ hex4 [b2; b3; b4; b5] = Some lo /\ 56320 <= lo <= 57343.
Proof.
  intros b0 b1 b2 b3 b4 b5 lo H. cbn [low] in H.
  destruct (b0 =? 92) eqn:E0; [|discriminate]. destruct (b1 =? 117) eqn:E1; [|discriminate]. cbn [andb] in H.
  apply Z.eqb_eq in E0, E1. replace (hex4 (b2 :: b3 :: b4 :: b5 :: [])) with (hex4 [b2; b3; b4; b5]) in H by reflexivity.
  destruct (hex4 [b2; b3; b4; b5]) as [l|] eqn:Eh; [|discriminate].
  destruct ((56320 <=? l) && (l <=? 57343)) eqn:Er; [|discriminate]. injection H as <-.
  apply andb_true_iff in Er as [R1 R2]. apply Z.leb_le in R1, R2. auto.
Qed.
Lemma psd_scan_pair : forall h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x v lo, hex4 [h0; h1; h2; h3] = Some v ->
  low [b0; b1; b2; b3; b4; b5] = Some lo ->
  scan (92 :: 117 :: h0 :: h1 :: h2 :: h3 :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: x) =
  option_map (fun q => (q + 12)%nat) (scan x).
Proof.
  intros h0 h1 h2 h3 b0 b1 b2 b3 b4 b5 x v lo H Hl.
  destruct (psd_low_hex4 _ _ _ _ _ _ _ Hl) as (-> & -> & Hh & _).
  rewrite (psd_scan_u _ _ _ _ _ _ H), (psd_scan_u _ _ _ _ _ _ Hh).
  destruct (scan x); cbn; [f_equal; lia | reflexivity].
Qed.

(* ---- the code's arithmetic against the model ---- *)
(* the hex loop's digit value: the three ranges the code tests (offsets 472..528) *)
Lemma psd_hexval_dec : forall b, 0 <= b < 256 -> 0 <= b - 48 < 10 -> hexval b = Some (b - 48).
Proof. intros b Hb H. unfold hexval. replace ((48 <=? b) && (b <=? 57)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le]; lia. Qed.
Lemma psd_hexval_low : forall b, 0 <= b < 256 -> ~ (0 <= b - 48 < 10) -> 0 <= b - 97 < 6 -> hexval b = Some (b - 87).
Proof.
  intros b Hb H1 H. unfold hexval.
  replace ((48 <=? b) && (b <=? 57)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 48); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  replace ((97 <=? b) && (b <=? 102)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.
Lemma psd_hexval_up : forall b, 0 <= b < 256 -> ~ (0 <= b - 48 < 10) -> ~ (0 <= b - 97 < 6) -> 0 <= b - 65 <= 5 ->
  hexval b = Some (b - 55).
Proof.
  intros b Hb H1 H2 H. unfold hexval.
  replace ((48 <=? b) && (b <=? 57)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 48); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  replace ((97 <=? b) && (b <=? 102)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 97); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  replace ((65 <=? b) && (b <=? 70)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.
Lemma psd_hexval_none : forall b, 0 <= b < 256 -> ~ (0 <= b - 48 < 10) -> ~ (0 <= b - 97 < 6) -> ~ (0 <= b - 65 <= 5) ->
  hexval b = None.
Proof.
  intros b Hb H1 H2 H3. unfold hexval.
  replace ((48 <=? b) && (b <=? 57)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 48); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  replace ((97 <=? b) && (b <=? 102)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 97); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  replace ((65 <=? b) && (b <=? 70)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec b 65); [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]).
  reflexivity.
Qed.
Lemma psd_hexval_range : forall b v, hexval b = Some v -> 0 <= v < 16.
Proof.
  intros b v H. unfold hexval in H.
  destruct ((48 <=? b) && (b <=? 57)) eqn:E1; [injection H as <-; apply andb_true_iff in E1 as [A B]; apply Z.leb_le in A, B; lia|].
  destruct ((97 <=? b) && (b <=? 102)) eqn:E2; [injection H as <-; apply andb_true_iff in E2 as [A B]; apply Z.leb_le in A, B; lia|].
  destruct ((65 <=? b) && (b <=? 70)) eqn:E3; [injection H as <-; apply andb_true_iff in E3 as [A B]; apply Z.leb_le in A, B; lia|].
  discriminate.
Qed.
(* hex4 as the loop accumulates it: s5 = 16 * s5 + digit, four times from 0 *)
Definition psd_acc (bs : list Z) : option Z :=
  fold_left (fun acc b => match acc, hexval b with Some a, Some v => Some (16 * a + v) | _, _ => None end) bs (Some 0).
Lemma psd_acc_hex4 : forall h0 h1 h2 h3, psd_acc [h0; h1; h2; h3] = hex4 [h0; h1; h2; h3].
Proof.
  intros h0 h1 h2 h3. unfold psd_acc. cbn [fold_left hex4].
  destruct (hexval h0); destruct (hexval h1); destruct (hexval h2); destruct (hexval h3); cbn; try reflexivity.
  f_equal. lia.
Qed.
Lemma psd_acc_snoc : forall bs b, psd_acc (bs ++ [b]) =
  match psd_acc bs, hexval b with Some a, Some v => Some (16 * a + v) | _, _ => None end.
Proof. intros bs b. unfold psd_acc. rewrite fold_left_app. reflexivity. Qed.
Lemma psd_acc_range : forall bs a, psd_acc bs = Some a -> 0 <= a < 16 ^ Z.of_nat (length bs).
Proof.
  intros bs. induction bs as [|b bs IH] using rev_ind; intros a H.
  - cbn in H. injection H as <-. cbn. lia.
  - rewrite psd_acc_snoc in H. destruct (psd_acc bs) as [a0|] eqn:E0; [|discriminate].
    destruct (hexval b) as [v|] eqn:Ev; [|discriminate]. injection H as <-.
    pose proof (IH a0 eq_refl). pose proof (psd_hexval_range b v Ev).
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. cbn [Z.of_nat]. lia.
Qed.
Lemma psd_acc_none : forall bs b, psd_acc bs = None \/ hexval b = None -> psd_acc (bs ++ [b]) = None.
Proof. intros bs b [H|H]; rewrite psd_acc_snoc, H; [reflexivity | destruct (psd_acc bs); reflexivity]. Qed.
(* the surrogate split by the masks at 884 / 896 / 904: cp & -1024 against 55296 and 56320 *)
Lemma psd_land_m1024 : forall cp, 0 <= cp -> Z.land cp (-1024) = cp - cp mod 1024.
Proof.
  intros cp Hc. replace (-1024) with (Z.lnot (Z.ones 10)) by reflexivity.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 10) with 1024.
  pose proof (Z.div_mod cp 1024 ltac:(lia)). lia.
Qed.
Lemma psd_mask_hi : forall cp, 0 <= cp -> (Z.land cp (-1024) = 55296 <-> 55296 <= cp < 56320).
Proof.
  intros cp Hc. rewrite (psd_land_m1024 cp Hc). pose proof (Z.mod_pos_bound cp 1024 ltac:(lia)) as M.
  pose proof (Z.div_mod cp 1024 ltac:(lia)) as D. split; intros Hx.
  - lia.
  - assert (cp / 1024 = 54) by (symmetry; apply (Z.div_unique cp 1024 54 (cp - 55296)); lia). lia.
Qed.
Lemma psd_mask_lo : forall cp, 0 <= cp -> (Z.land cp (-1024) = 56320 <-> 56320 <= cp < 57344).
Proof.
  intros cp Hc. rewrite (psd_land_m1024 cp Hc). pose proof (Z.mod_pos_bound cp 1024 ltac:(lia)) as M.
  pose proof (Z.div_mod cp 1024 ltac:(lia)) as D. split; intros Hx.
  - lia.
  - assert (cp / 1024 = 55) by (symmetry; apply (Z.div_unique cp 1024 55 (cp - 56320)); lia). lia.
Qed.
(* pair_cp as the code computes it at 1020..1032: (hi << 10) + lo + (-56613888), in 32 bits *)
Lemma psd_pair_cp : forall hi lo, pair_cp hi lo = hi * 1024 + lo + -56613888.
Proof. intros hi lo. unfold pair_cp. lia. Qed.
Lemma psd_pair_range : forall hi lo, 55296 <= hi < 56320 -> 56320 <= lo <= 57343 -> 65536 <= pair_cp hi lo <= 1114111.
Proof. intros hi lo Hh Hl. unfold pair_cp. lia. Qed.
Lemma psd_utf8_len : forall cp, 0 <= cp -> (1 <= length (utf8 cp) <= 4)%nat.
Proof.
  intros cp Hc. unfold utf8.
  destruct (cp <? 128); [cbn; lia|]. destruct (cp <? 2048); [cbn; lia|]. destruct (cp <? 65536); cbn; lia.
Qed.
