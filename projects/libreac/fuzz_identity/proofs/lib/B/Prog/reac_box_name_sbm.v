(* reac_box_name (fuzz_identity.asan-ubsan): pure model lemmas for the B walk. They relate the listing's sequence
   of out-of-line sb_ch / sb_dec calls on the four string buffers (wb cap 5, nb cap 24, tb cap 24, db cap 48) to
   the released model (lib/Prog/disco_box_name_model.v: bn_w4, bn_NM, bn_TK, bn_DP; lib/Prog/reac_box_name_c.v:
   bn_accept). No machine state here: a buffer is its content and its over flag, (list Z * Z).
   - sbm_ch is sb_ch's effect (lib/B/Prog/sb_ch.v tsb_ch_post): with room (n + 1 < cap) c is appended, else
     over := 1; sbm_str folds sbm_ch over a list. sbm_dec_post turns tsb_dec_post's result into sbm_str of the
     digits sb_dec_D v md, so each loop of the walk is one sbm_str and each sb_ch call one sbm_str_snoc /
     rbn_tok_snoc step.
   - rbn_w4 / rbn_nm / rbn_tok / rbn_dp / rbn_ok: steps 1-5 of the listing. Their specs: rbn_w4_spec,
     rbn_nm_tr / rbn_nm_spec, rbn_tok_spec, rbn_dp_spec, rbn_accept_spec. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c reac_box_name_c box_name_lemmas
  reac_box_name.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- The buffer model ---- *)
Definition sbm_ch (cap : Z) (st : list Z * Z) (c : Z) : list Z * Z :=
  if Z.of_nat (length (fst st)) + 1 <? cap then (fst st ++ [c], snd st) else (fst st, 1).
Definition sbm_str (cap : Z) (st : list Z * Z) (s : list Z) : list Z * Z := fold_left (sbm_ch cap) s st.
(* the listing's lower-casing: c | (((c - 65) mod 256 <u 26) << 5), written as an addition *)
Definition bn_low' (c : Z) : Z := (c + 32 * (if (c - 65) mod 256 <? 26 then 1 else 0)) mod 256.

(* A buffer that started empty with over 0 and was offered the chars L in order: the truncated content and the
   over flag. *)
Definition sbm_tr (cap : Z) (L : list Z) : list Z * Z :=
  (firstn (Z.to_nat (cap - 1)) L, if Z.of_nat (length L) <? cap then 0 else 1).

(* ---- Steps 1-5 of the listing ---- *)
(* 1. wb (cap 5): sb_dec(wb, i, 2); sb_dec(wb, o, 2). *)
Definition rbn_w4 (i o : Z) : list Z * Z :=
  sbm_str 5 (sbm_str 5 ([], 0) (sb_dec_c.sb_dec_D i 2)) (sb_dec_c.sb_dec_D o 2).
(* 2. nb (cap 24): the stem s; then, unless wb.n = 4 and s ends with w4, '-' and w4. The test is bn_NM's. *)
Definition rbn_skip (s w : list Z) : bool := (4 <=? Z.of_nat (length s)) && bn_leq (skipn (length s - 4) s) w.
Definition rbn_nm_of (s w : list Z) : list Z * Z :=
  if rbn_skip s w then sbm_str 24 ([], 0) s else sbm_str 24 (sbm_ch 24 (sbm_str 24 ([], 0) s) 45) w.
Definition rbn_nm (f : Z) (sd : list Z) (i o : Z) : list Z * Z := rbn_nm_of (bn_stem f sd) (bn_w4 i o).
(* 3. tb (cap 24): over nb's content, the first '-' is dropped (the seen flag), every other char c is pushed
   as bn_low' c. rbn_tk_run's state is (seen, tb); rbn_tok is tb. *)
Definition rbn_tk_step (acc : bool * (list Z * Z)) (c : Z) : bool * (list Z * Z) :=
  if (c =? 45) && negb (fst acc) then (true, snd acc) else (fst acc, sbm_ch 24 (snd acc) (bn_low' c)).
Definition rbn_tk_run (l : list Z) : bool * (list Z * Z) := fold_left rbn_tk_step l (false, ([], 0)).
Definition rbn_tok (nm : list Z) : list Z * Z := snd (rbn_tk_run nm).
(* 4. db (cap 48): nb's content, " (", sb_dec(db, i, 1), " in / ", sb_dec(db, o, 1), " out)". *)
Definition rbn_dp (nm : list Z) (i o : Z) : list Z * Z :=
  sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 ([], 0) nm) [32; 40])
    (sb_dec_c.sb_dec_D i 1)) [32; 105; 110; 32; 47; 32]) (sb_dec_c.sb_dec_D o 1)) [32; 111; 117; 116; 41].
(* 5. the acceptance test, in the listing's order: the four over flags, then nb.n < name_len,
   db.n < display_len, tb.n < token_len. *)
Definition rbn_ok (wb nb tb db : list Z * Z) (name_len token_len display_len : Z) : bool :=
  (snd wb =? 0) && (snd nb =? 0) && (snd tb =? 0) && (snd db =? 0) &&
  (Z.of_nat (length (fst nb)) <? name_len) && (Z.of_nat (length (fst db)) <? display_len) &&
  (Z.of_nat (length (fst tb)) <? token_len).

(* ---- List helpers ---- *)
Lemma fa2 : forall (l : list Z) n, (length l <= n)%nat -> firstn n l = l.
Proof. intros l n H. apply firstn_all2. exact H. Qed.

Lemma firstn_nil_h : forall n, firstn n (@nil Z) = [].
Proof. intros [|n]; reflexivity. Qed.

Lemma len_firstn_h : forall (l : list Z) n, length (firstn n l) = Nat.min n (length l).
Proof.
  induction l as [|x l IH]; intros [|n]; cbn [firstn length]; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma Forall_firstn_h : forall (P : Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H. revert n. induction H as [|x l Hx Hl IH]; intros n; destruct n; cbn [firstn]; constructor; auto.
Qed.

Lemma nth_skipn_h : forall (l : list Z) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
  induction l as [|x l IH]; intros k j d.
  - destruct k, j; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma list_eq_nth_h : forall (a b : list Z), length a = length b ->
  (forall j, (j < length a)%nat -> nth j a 0 = nth j b 0) -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] L H; cbn [length] in L; try discriminate.
  - reflexivity.
  - f_equal.
    + apply (H 0%nat). cbn [length]. lia.
    + apply IH; [lia|]. intros j Hj. apply (H (S j)). cbn [length]. lia.
Qed.

(* ---- (a) sb_ch step: tsb_ch_post's two cases are sbm_ch ---- *)
Lemma sbm_ch_post : forall cap cs ov c n, n = Z.of_nat (length cs) ->
  (if n + 1 <? cap then (cs ++ [c], ov) else (cs, 1)) = sbm_ch cap (cs, ov) c.
Proof. intros cap cs ov c n ->. reflexivity. Qed.

Lemma sbm_ch_room : forall cap cs ov c, Z.of_nat (length cs) + 1 < cap -> sbm_ch cap (cs, ov) c = (cs ++ [c], ov).
Proof.
  intros cap cs ov c H. unfold sbm_ch. cbn [fst snd].
  replace (Z.of_nat (length cs) + 1 <? cap) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

Lemma sbm_ch_full : forall cap cs ov c, cap <= Z.of_nat (length cs) + 1 -> sbm_ch cap (cs, ov) c = (cs, 1).
Proof.
  intros cap cs ov c H. unfold sbm_ch. cbn [fst snd].
  replace (Z.of_nat (length cs) + 1 <? cap) with false by (symmetry; apply Z.ltb_ge; exact H). reflexivity.
Qed.

(* ---- sbm_str: unfolding, append, snoc (one sb_ch call of a loop), closed form ---- *)
Lemma sbm_str_nil : forall cap st, sbm_str cap st [] = st.
Proof. intros cap st. reflexivity. Qed.

Lemma sbm_str_cons : forall cap st x s, sbm_str cap st (x :: s) = sbm_str cap (sbm_ch cap st x) s.
Proof. intros cap st x s. reflexivity. Qed.

Lemma sbm_str_app : forall cap st a b, sbm_str cap st (a ++ b) = sbm_str cap (sbm_str cap st a) b.
Proof. intros cap st a b. unfold sbm_str. apply fold_left_app. Qed.

Lemma sbm_str_snoc : forall cap st s k, (k < length s)%nat ->
  sbm_str cap st (firstn (S k) s) = sbm_ch cap (sbm_str cap st (firstn k s)) (nth k s 0).
Proof.
  intros cap st s k H. rewrite (box_name_lemmas.bl_firstn_snoc s k 0 H), sbm_str_app. reflexivity.
Qed.

(* (c) the closed form *)
Lemma sbm_str_closed : forall cap s cs ov, Z.of_nat (length cs) < cap ->
  sbm_str cap (cs, ov) s =
  (cs ++ firstn (Z.to_nat (cap - 1 - Z.of_nat (length cs))) s,
   if Z.of_nat (length cs + length s) <? cap then ov else 1).
Proof.
  intros cap s. induction s as [|x s IH]; intros cs ov H.
  - rewrite sbm_str_nil, firstn_nil_h, app_nil_r. cbn [length]. rewrite Nat.add_0_r.
    replace (Z.of_nat (length cs) <? cap) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
  - rewrite sbm_str_cons.
    destruct (Z.ltb_spec (Z.of_nat (length cs) + 1) cap) as [L|L].
    + rewrite sbm_ch_room by exact L. rewrite IH by (rewrite length_app; cbn [length]; lia).
      rewrite length_app, <- app_assoc. cbn [length].
      replace (Z.to_nat (cap - 1 - Z.of_nat (length cs)))
        with (S (Z.to_nat (cap - 1 - Z.of_nat (length cs + 1)))) by lia.
      cbn [firstn app].
      destruct (Z.ltb_spec (Z.of_nat (length cs + 1 + length s)) cap);
        destruct (Z.ltb_spec (Z.of_nat (length cs + S (length s))) cap); first [reflexivity | exfalso; lia].
    + rewrite sbm_ch_full by exact L. rewrite IH by exact H.
      replace (Z.to_nat (cap - 1 - Z.of_nat (length cs))) with 0%nat by lia. cbn [firstn length].
      destruct (Z.ltb_spec (Z.of_nat (length cs + length s)) cap);
        destruct (Z.ltb_spec (Z.of_nat (length cs + S (length s))) cap); first [reflexivity | exfalso; lia].
Qed.

Lemma sbm_str_fits : forall cap s cs ov, Z.of_nat (length cs + length s) < cap ->
  sbm_str cap (cs, ov) s = (cs ++ s, ov).
Proof.
  intros cap s cs ov H. rewrite sbm_str_closed by lia. rewrite (fa2 s) by lia.
  replace (Z.of_nat (length cs + length s) <? cap) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

Lemma sbm_str_full : forall cap s cs ov, Z.of_nat (length cs) < cap -> cap <= Z.of_nat (length cs + length s) ->
  sbm_str cap (cs, ov) s = (cs ++ firstn (Z.to_nat (cap - 1 - Z.of_nat (length cs))) s, 1) /\
  Z.of_nat (length (cs ++ firstn (Z.to_nat (cap - 1 - Z.of_nat (length cs))) s)) = cap - 1.
Proof.
  intros cap s cs ov H1 H2. rewrite sbm_str_closed by exact H1.
  replace (Z.of_nat (length cs + length s) <? cap) with false by (symmetry; apply Z.ltb_ge; exact H2).
  split; [reflexivity|]. rewrite length_app, len_firstn_h. lia.
Qed.

(* the bounds a walk carries across a loop: n stays below cap, over is ov or 1, the old content is kept *)
Lemma sbm_str_bound : forall cap s cs ov, Z.of_nat (length cs) < cap ->
  Z.of_nat (length (fst (sbm_str cap (cs, ov) s))) <= cap - 1 /\
  (snd (sbm_str cap (cs, ov) s) = ov \/ snd (sbm_str cap (cs, ov) s) = 1) /\
  firstn (length cs) (fst (sbm_str cap (cs, ov) s)) = cs.
Proof.
  intros cap s cs ov H. rewrite sbm_str_closed by exact H. cbn [fst snd].
  split; [rewrite length_app, len_firstn_h; lia|]. split.
  - destruct (Z.of_nat (length cs + length s) <? cap); [left|right]; reflexivity.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

Lemma sbm_str_Forall : forall (P : Z -> Prop) cap s cs ov, Forall P cs -> Forall P s ->
  Forall P (fst (sbm_str cap (cs, ov) s)).
Proof.
  intros P cap s. induction s as [|x s IH]; intros cs ov Hc Hs; [exact Hc|].
  apply Forall_cons_iff in Hs. destruct Hs as [Hx Hs]. rewrite sbm_str_cons.
  destruct (Z.ltb_spec (Z.of_nat (length cs) + 1) cap) as [L|L].
  - rewrite sbm_ch_room by exact L. apply IH; [|exact Hs].
    apply Forall_app. split; [exact Hc | constructor; [exact Hx | constructor]].
  - rewrite sbm_ch_full by exact L. apply IH; [exact Hc | exact Hs].
Qed.

(* ---- (b) sb_dec step: tsb_dec_post's result is sbm_str of the digits ---- *)
Lemma sbm_dec_post : forall cap cs ov v md n, n = Z.of_nat (length cs) -> n + 1 <= cap ->
  sbm_str cap (cs, ov) (sb_dec_c.sb_dec_D v md) =
  (cs ++ firstn (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md),
   if sb_dec_c.sb_dec_room cap n <? Z.of_nat (length (sb_dec_c.sb_dec_D v md)) then 1 else ov).
Proof.
  intros cap cs ov v md n En Hn. subst n.
  assert (R : sb_dec_c.sb_dec_room cap (Z.of_nat (length cs)) = cap - 1 - Z.of_nat (length cs)).
  { unfold sb_dec_c.sb_dec_room.
    replace (Z.of_nat (length cs) + 1 <=? cap) with true by (symmetry; apply Z.leb_le; exact Hn). reflexivity. }
  rewrite sbm_str_closed by lia. unfold sb_dec_c.sb_dec_acc. rewrite R.
  set (D := sb_dec_c.sb_dec_D v md).
  f_equal.
  - f_equal.
    destruct (Z.min_spec (Z.of_nat (length D)) (cap - 1 - Z.of_nat (length cs))) as [[M1 M2]|[M1 M2]];
      rewrite M2.
    + rewrite Nat2Z.id, firstn_all. apply fa2. lia.
    + reflexivity.
  - destruct (Z.ltb_spec (Z.of_nat (length cs + length D)) cap);
      destruct (Z.ltb_spec (cap - 1 - Z.of_nat (length cs)) (Z.of_nat (length D)));
      first [reflexivity | exfalso; lia].
Qed.

(* ---- The truncating-append form: from an empty buffer with over 0 ---- *)
Lemma sbm_ch_tr : forall cap L c, 0 < cap -> sbm_ch cap (sbm_tr cap L) c = sbm_tr cap (L ++ [c]).
Proof.
  intros cap L c Hc. unfold sbm_ch, sbm_tr. cbn [fst snd].
  pose proof (len_firstn_h L (Z.to_nat (cap - 1))) as LF. rewrite length_app. cbn [length].
  destruct (Z.ltb_spec (Z.of_nat (length (firstn (Z.to_nat (cap - 1)) L)) + 1) cap) as [H2|H2];
    destruct (Z.ltb_spec (Z.of_nat (length L)) cap) as [H1|H1];
    destruct (Z.ltb_spec (Z.of_nat (length L + 1)) cap) as [H3|H3]; try (exfalso; lia).
  - rewrite (fa2 L) by lia. rewrite (fa2 (L ++ [c])) by (rewrite length_app; cbn [length]; lia). reflexivity.
  - rewrite firstn_app. replace (Z.to_nat (cap - 1) - length L)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity.
  - rewrite firstn_app. replace (Z.to_nat (cap - 1) - length L)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma sbm_str_tr : forall cap s L, 0 < cap -> sbm_str cap (sbm_tr cap L) s = sbm_tr cap (L ++ s).
Proof.
  intros cap s. induction s as [|x s IH]; intros L Hc.
  - rewrite sbm_str_nil, app_nil_r. reflexivity.
  - rewrite sbm_str_cons, sbm_ch_tr by exact Hc. rewrite IH by exact Hc. rewrite <- app_assoc. reflexivity.
Qed.

Lemma sbm_tr_fit : forall cap L, Z.of_nat (length L) < cap -> sbm_tr cap L = (L, 0).
Proof.
  intros cap L H. unfold sbm_tr. rewrite (fa2 L) by lia.
  replace (Z.of_nat (length L) <? cap) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

Lemma sbm_tr_nil : forall cap, 0 < cap -> sbm_tr cap [] = ([], 0).
Proof. intros cap Hc. apply sbm_tr_fit. cbn [length]. lia. Qed.

(* ---- (d) step 1: wb = (bn_w4 i o, 0) ---- *)
Lemma rbn_w4_spec : forall i o, bn_ok i = true -> bn_ok o = true -> rbn_w4 i o = (bn_w4 i o, 0).
Proof.
  intros i o Hi Ho.
  destruct (reac_box_name.bn_ok_dec i Hi) as (_ & Li & _ & Di & _).
  destruct (reac_box_name.bn_ok_dec o Ho) as (_ & Lo & _ & Do & _).
  unfold rbn_w4. rewrite Di, Do, <- (sbm_tr_nil 5) by lia.
  rewrite !sbm_str_tr by lia. rewrite sbm_tr_fit by (rewrite !length_app; cbn [length]; lia). reflexivity.
Qed.

(* ---- (e) the listing's lower-casing is bn_low on bytes ---- *)
Lemma bn_low'_eq : forall c, 0 <= c < 256 -> bn_low' c = box_name_lemmas.bn_low c.
Proof.
  intros c Hc.
  assert (A : forallb (fun c => bn_low' c =? box_name_lemmas.bn_low c) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in A.
  specialize (A c ltac:(apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia])).
  apply Z.eqb_eq in A. exact A.
Qed.

(* ---- (f) the suffix test (strlen + bcmp of the last 4 chars against w4) ---- *)
Lemma rbn_suffix : forall s w, length w = 4%nat -> (4 <= length s)%nat ->
  bn_leq (skipn (length s - 4) s) w = true <->
  (forall j, (j < 4)%nat -> nth (length s - 4 + j) s 0 = nth j w 0).
Proof.
  intros s w Lw Ls. rewrite reac_box_name.bn_leq_eq. split.
  - intros E j Hj. rewrite <- E. symmetry. apply nth_skipn_h.
  - intros H. apply list_eq_nth_h; [rewrite length_skipn; lia|].
    intros j Hj. rewrite length_skipn in Hj. rewrite nth_skipn_h. apply H. lia.
Qed.

(* the same with the Z index the bcmp contract uses (aview at x + j for 0 <= j < 4) *)
Lemma rbn_suffix_Z : forall s w, length w = 4%nat -> 4 <= Z.of_nat (length s) ->
  bn_leq (skipn (length s - 4) s) w = true <->
  (forall j, 0 <= j < 4 -> nth (Z.to_nat (Z.of_nat (length s) - 4 + j)) s 0 = nth (Z.to_nat j) w 0).
Proof.
  intros s w Lw Ls. rewrite rbn_suffix by lia. split.
  - intros H j Hj. replace (Z.to_nat (Z.of_nat (length s) - 4 + j)) with (length s - 4 + Z.to_nat j)%nat by lia.
    apply H. lia.
  - intros H j Hj. specialize (H (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in H.
    replace (Z.to_nat (Z.of_nat (length s) - 4 + Z.of_nat j)) with (length s - 4 + j)%nat in H by lia. exact H.
Qed.

(* ---- (g) step 2: nb ---- *)
Lemma bn_STEM_chars : forall f, Forall (fun c => 0 < c < 256) (bn_STEM f).
Proof.
  intros f. unfold bn_STEM.
  destruct (f =? 1); [|destruct (f =? 2); [|destruct (f =? 3)]];
    apply Forall_forall; intros c Hc; cbn [In] in Hc; cbv beta; lia.
Qed.

Lemma bn_stem_chars : forall f sd, Forall (fun c => 0 < c < 256) sd -> Forall (fun c => 0 < c < 256) (bn_stem f sd).
Proof. intros f sd H. destruct sd as [|x r]; [cbn [bn_stem]; exact (bn_STEM_chars f) | exact H]. Qed.

Lemma rbn_nm_skip : forall s w, rbn_skip s w = true -> rbn_nm_of s w = sbm_str 24 ([], 0) s.
Proof. intros s w H. unfold rbn_nm_of. rewrite H. reflexivity. Qed.

Lemma rbn_nm_noskip : forall s w, rbn_skip s w = false ->
  rbn_nm_of s w = sbm_str 24 (sbm_ch 24 (sbm_str 24 ([], 0) s) 45) w.
Proof. intros s w H. unfold rbn_nm_of. rewrite H. reflexivity. Qed.

Lemma bn_NM_skip : forall f sd i o,
  bn_NM f sd i o = if rbn_skip (bn_stem f sd) (bn_w4 i o) then bn_stem f sd else bn_stem f sd ++ 45 :: bn_w4 i o.
Proof. intros f sd i o. reflexivity. Qed.

(* nb is the truncating append of the name *)
Lemma rbn_nm_of_tr : forall s w,
  rbn_nm_of s w = sbm_tr 24 (if rbn_skip s w then s else s ++ 45 :: w).
Proof.
  intros s w. unfold rbn_nm_of. rewrite <- (sbm_tr_nil 24) by lia.
  destruct (rbn_skip s w).
  - rewrite sbm_str_tr by lia. reflexivity.
  - rewrite sbm_str_tr, sbm_ch_tr, sbm_str_tr by lia. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma rbn_nm_tr : forall f sd i o, rbn_nm f sd i o = sbm_tr 24 (bn_NM f sd i o).
Proof. intros f sd i o. unfold rbn_nm. rewrite rbn_nm_of_tr, bn_NM_skip. reflexivity. Qed.

Lemma rbn_nm_spec : forall f sd i o, bn_ok i = true -> bn_ok o = true ->
  Forall (fun c => 0 < c < 256) (bn_stem f sd) ->
  (snd (rbn_nm f sd i o) = 0 <-> Z.of_nat (length (bn_NM f sd i o)) <= 23) /\
  (snd (rbn_nm f sd i o) =? 0) = (Z.of_nat (length (bn_NM f sd i o)) <=? 23) /\
  (snd (rbn_nm f sd i o) = 0 \/ snd (rbn_nm f sd i o) = 1) /\
  (snd (rbn_nm f sd i o) = 0 -> fst (rbn_nm f sd i o) = bn_NM f sd i o) /\
  (length (fst (rbn_nm f sd i o)) <= 23)%nat /\
  Forall (fun c => 0 < c < 256) (fst (rbn_nm f sd i o)).
Proof.
  intros f sd i o Hi Ho Hs. rewrite rbn_nm_tr. unfold sbm_tr. cbn [fst snd].
  pose proof (reac_box_name.NM_chars f sd i o Hs Hi Ho) as C.
  change (Z.to_nat (24 - 1)) with 23%nat.
  destruct (Z.ltb_spec (Z.of_nat (length (bn_NM f sd i o))) 24) as [L|L];
    destruct (Z.leb_spec (Z.of_nat (length (bn_NM f sd i o))) 23) as [L'|L']; try (exfalso; lia).
  - split; [split; intros; lia|]. split; [reflexivity|]. split; [left; reflexivity|].
    split; [intros _; apply fa2; lia|]. split; [rewrite len_firstn_h; lia|]. apply Forall_firstn_h. exact C.
  - split; [split; intros; lia|]. split; [reflexivity|]. split; [right; reflexivity|].
    split; [intros E; discriminate E|]. split; [rewrite len_firstn_h; lia|]. apply Forall_firstn_h. exact C.
Qed.

(* ---- (h) step 3: tb ---- *)
Lemma rbn_tk_step_eq : forall seen st c,
  rbn_tk_step (seen, st) c = if (c =? 45) && negb seen then (true, st) else (seen, sbm_ch 24 st (bn_low' c)).
Proof. intros seen st c. reflexivity. Qed.

Lemma rbn_tk_run_snoc : forall l k, (k < length l)%nat ->
  rbn_tk_run (firstn (S k) l) = rbn_tk_step (rbn_tk_run (firstn k l)) (nth k l 0).
Proof.
  intros l k H. unfold rbn_tk_run. rewrite (box_name_lemmas.bl_firstn_snoc l k 0 H), fold_left_app. reflexivity.
Qed.

(* the seen flag is "a '-' has been read" *)
Lemma rbn_tk_seen_gen : forall l seen st,
  fst (fold_left rbn_tk_step l (seen, st)) = seen || existsb (fun x => x =? 45) l.
Proof.
  induction l as [|c l IH]; intros seen st.
  - cbn [fold_left existsb fst]. rewrite orb_false_r. reflexivity.
  - cbn [fold_left existsb]. rewrite rbn_tk_step_eq.
    destruct (Z.eqb_spec c 45) as [E|E]; destruct seen; cbn [andb negb orb]; rewrite IH; reflexivity.
Qed.

Lemma rbn_tk_run_seen : forall l, fst (rbn_tk_run l) = existsb (fun x => x =? 45) l.
Proof. intros l. unfold rbn_tk_run. rewrite rbn_tk_seen_gen. reflexivity. Qed.

(* one iteration of the token loop (index k of nb's content) *)
Lemma rbn_tok_snoc : forall nm k, (k < length nm)%nat ->
  rbn_tok (firstn (S k) nm) =
  (if (nth k nm 0 =? 45) && negb (existsb (fun x => x =? 45) (firstn k nm))
   then rbn_tok (firstn k nm) else sbm_ch 24 (rbn_tok (firstn k nm)) (bn_low' (nth k nm 0))).
Proof.
  intros nm k H. unfold rbn_tok. rewrite rbn_tk_run_snoc by exact H.
  rewrite <- (rbn_tk_run_seen (firstn k nm)).
  destruct (rbn_tk_run (firstn k nm)) as [seen st]. cbn [fst snd]. rewrite rbn_tk_step_eq.
  destruct ((nth k nm 0 =? 45) && negb seen); reflexivity.
Qed.

Lemma rbn_tk_gen : forall l seen cs ov, (length cs + length l <= 23)%nat -> Forall (fun c => 0 <= c < 256) l ->
  fold_left rbn_tk_step l (seen, (cs, ov)) = (seen || existsb (fun c => c =? 45) l, (cs ++ bn_tk seen l, ov)).
Proof.
  induction l as [|c l IH]; intros seen cs ov L R.
  - cbn [fold_left existsb bn_tk]. rewrite orb_false_r, app_nil_r. reflexivity.
  - apply Forall_cons_iff in R. destruct R as [Rc Rl]. cbn [length] in L.
    cbn [fold_left existsb bn_tk]. rewrite rbn_tk_step_eq, (bn_low'_eq c Rc).
    destruct (Z.eqb_spec c 45) as [E|E]; destruct seen; cbn [andb negb orb].
    + rewrite sbm_ch_room by lia. rewrite IH by (first [exact Rl | rewrite length_app; cbn [length]; lia]).
      rewrite <- app_assoc. reflexivity.
    + rewrite IH by (first [exact Rl | lia]). reflexivity.
    + rewrite sbm_ch_room by lia. rewrite IH by (first [exact Rl | rewrite length_app; cbn [length]; lia]).
      rewrite <- app_assoc. reflexivity.
    + rewrite sbm_ch_room by lia. rewrite IH by (first [exact Rl | rewrite length_app; cbn [length]; lia]).
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma rbn_tk_run_spec : forall nm, (length nm <= 23)%nat -> Forall (fun c => 0 <= c < 256) nm ->
  rbn_tk_run nm = (existsb (fun c => c =? 45) nm, (bn_TK nm, 0)).
Proof.
  intros nm L R. unfold rbn_tk_run, bn_TK. rewrite rbn_tk_gen by (first [exact R | cbn [length]; lia]).
  reflexivity.
Qed.

Lemma rbn_tok_spec : forall nm, (length nm <= 23)%nat -> Forall (fun c => 0 <= c < 256) nm ->
  rbn_tok nm = (bn_TK nm, 0).
Proof. intros nm L R. unfold rbn_tok. rewrite rbn_tk_run_spec by assumption. reflexivity. Qed.

(* ---- (i) step 4: db ---- *)
Lemma rbn_dp_eq : forall nm i o,
  rbn_dp nm i o =
  sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 (sbm_str 48 ([], 0) nm) [32; 40])
    (sb_dec_c.sb_dec_D i 1)) [32; 105; 110; 32; 47; 32]) (sb_dec_c.sb_dec_D o 1)) [32; 111; 117; 116; 41].
Proof. intros nm i o. reflexivity. Qed.

Lemma rbn_dp_spec : forall nm i o, (length nm <= 23)%nat -> bn_ok i = true -> bn_ok o = true ->
  rbn_dp nm i o = (bn_DP nm i o, 0).
Proof.
  intros nm i o L Hi Ho.
  destruct (reac_box_name.bn_ok_dec i Hi) as (_ & _ & Li & _ & Di & _).
  destruct (reac_box_name.bn_ok_dec o Ho) as (_ & _ & Lo & _ & Do & _).
  unfold rbn_dp. rewrite Di, Do, <- (sbm_tr_nil 48) by lia.
  rewrite !sbm_str_tr by lia. rewrite <- !app_assoc.
  rewrite sbm_tr_fit by (rewrite !length_app; cbn [length]; lia). reflexivity.
Qed.

(* ---- (j) step 5: the acceptance test is bn_accept; on acceptance the three contents are the plain model's ---- *)
Lemma rbn_accept_spec : forall f sd i o name name_len token token_len display display_len,
  reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true ->
  Forall (fun c => 0 < c < 256) sd ->
  rbn_ok (rbn_w4 i o) (rbn_nm f sd i o) (rbn_tok (fst (rbn_nm f sd i o))) (rbn_dp (fst (rbn_nm f sd i o)) i o)
    name_len token_len display_len =
  reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len /\
  (reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len = true ->
   fst (rbn_nm f sd i o) = bn_NM f sd i o /\
   fst (rbn_tok (fst (rbn_nm f sd i o))) = bn_TK (bn_NM f sd i o) /\
   fst (rbn_dp (fst (rbn_nm f sd i o)) i o) = bn_DP (bn_NM f sd i o) i o).
Proof.
  intros f sd i o nm nl tk tl dp dl H Hsd.
  destruct (reac_box_name.args_ok_split _ _ _ _ _ _ _ _ H) as (_ & _ & _ & _ & _ & _ & Hi & Ho & _).
  rewrite (reac_box_name.acc_eq f sd i o nm nl tk tl dp dl H).
  destruct (rbn_nm_spec f sd i o Hi Ho (bn_stem_chars f sd Hsd)) as (_ & E0 & _ & EN & LN & CN).
  assert (CN' : Forall (fun c => 0 <= c < 256) (fst (rbn_nm f sd i o)))
    by (eapply Forall_impl; [|exact CN]; intros c Hc; cbv beta in Hc |- *; lia).
  rewrite (rbn_w4_spec i o Hi Ho), (rbn_tok_spec _ LN CN'), (rbn_dp_spec _ i o LN Hi Ho).
  unfold rbn_ok. cbn [fst snd]. rewrite E0, Z.eqb_refl.
  destruct (Z.leb_spec (Z.of_nat (length (bn_NM f sd i o))) 23) as [L|L].
  - assert (S0 : snd (rbn_nm f sd i o) = 0).
    { apply Z.eqb_eq. rewrite E0. first [reflexivity | apply Z.leb_le; exact L]. }
    rewrite (EN S0). cbn [andb]. split.
    + destruct (Z.of_nat (length (bn_NM f sd i o)) <? nl), (Z.of_nat (length (bn_TK (bn_NM f sd i o))) <? tl),
        (Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) <? dl); reflexivity.
    + intros _. split; [reflexivity|]. split; reflexivity.
  - cbn [andb]. split; [reflexivity | intros C; discriminate C].
Qed.
