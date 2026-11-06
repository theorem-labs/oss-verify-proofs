(** reac-pw/fuzz_segconf: the build-independent facts of piece P6 of reac_segconf_parse_file (the role branch,
    R:236-246 with reac_role_intent_parse inlined, RR:110-120; family F3). Both lib/Prog/pf_p6.v
    (plain, image 3776ca44d75c) and lib/U/Prog/pf_p6.v (UBSan, image 1696d6c34ffd) Require it; it Requires no image.

    - The spine: at ROLE the step r_key is pf_role_step (pf_kv's split and strcasecmp key "role" = 0), and the
      outcome of role_intent_parse from the five compares the binary makes (three bcmp, two word compares).
    - The fold buffer low[64] as a byte list: after li stores it holds the fold of val[0 .. li) and the old bytes
      after it (p6_lowb); the NUL store ends it, and then its prefix is r_low val 0 64 and the NUL (INTENT's LB).
    - The two stores of the role branch into seg[gi] (role = r, role_set = 1) in rconf_enc: c then holds
      pf_prov_mid (PRole r) rc gi (the field helpers are cross_check.v's ones, copied with this file's prefix).
    - The ranges of the compare results (memcmp_model's difference of two bytes, pf_word4). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** The spine *)
Lemma p6_rkey : forall rc gi nm ln line key val,
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) ->
  strcasecmp key S_role = 0 ->
  r_key rc (Some gi) nm ln line = pf_role_step rc gi nm ln val.
Proof.
  intros rc gi nm ln line key val (ei & E & -> & ->) K.
  unfold r_key, pf_role_step. rewrite E. cbv beta iota zeta. rewrite K. reflexivity.
Qed.

Lemma p6_rip_auto : forall l, strcmp l S_auto = 0 -> role_intent_parse l = Some 0.
Proof. intros l H. unfold role_intent_parse. rewrite H. reflexivity. Qed.

Lemma p6_rip_master : forall l, strcmp l S_auto <> 0 -> strcmp l S_master = 0 -> role_intent_parse l = Some 1.
Proof.
  intros l H1 H2. unfold role_intent_parse. rewrite (proj2 (Z.eqb_neq _ _) H1), H2. reflexivity.
Qed.

Lemma p6_rip_slave : forall l, strcmp l S_auto <> 0 -> strcmp l S_master <> 0 -> strcmp l S_slave = 0 ->
  role_intent_parse l = Some 2.
Proof.
  intros l H1 H2 H3. unfold role_intent_parse.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), H3. reflexivity.
Qed.

Lemma p6_rip_tap : forall l, strcmp l S_auto <> 0 -> strcmp l S_master <> 0 -> strcmp l S_slave <> 0 ->
  strcmp l S_tap = 0 -> role_intent_parse l = Some 3.
Proof.
  intros l H1 H2 H3 H4. unfold role_intent_parse.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3), H4. reflexivity.
Qed.

Lemma p6_rip_box : forall l, strcmp l S_auto <> 0 -> strcmp l S_master <> 0 -> strcmp l S_slave <> 0 ->
  strcmp l S_tap <> 0 -> strcmp l S_box = 0 -> role_intent_parse l = Some 4.
Proof.
  intros l H1 H2 H3 H4 H5. unfold role_intent_parse.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3),
    (proj2 (Z.eqb_neq _ _) H4), H5. reflexivity.
Qed.

Lemma p6_rip_none : forall l, strcmp l S_auto <> 0 -> strcmp l S_master <> 0 -> strcmp l S_slave <> 0 ->
  strcmp l S_tap <> 0 -> strcmp l S_box <> 0 -> role_intent_parse l = None.
Proof.
  intros l H1 H2 H3 H4 H5. unfold role_intent_parse.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3),
    (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5). reflexivity.
Qed.

(** The role step's two outcomes, as the exits KREF and PROV state them. *)
Lemma p6_step_none : forall rc gi nm ln val, role_intent_parse (r_low val 0 64) = None ->
  pf_role_step rc gi nm ln val = (refuse rc ln F_badrole [AS nm; AS val], Some gi, nm).
Proof. intros rc gi nm ln val H. unfold pf_role_step. rewrite H. reflexivity. Qed.

Lemma p6_step_some : forall rc gi nm ln val r, role_intent_parse (r_low val 0 64) = Some r ->
  pf_role_step rc gi nm ln val = (pf_prov_fin (PRole r) rc gi, Some gi, nm).
Proof. intros rc gi nm ln val r H. unfold pf_role_step. rewrite H. reflexivity. Qed.

(** ** The fold buffer low[64] *)
(** The 64 bytes at low after li passes of the fold loop, from the bytes LB0 the earlier lines left there. *)
Definition p6_lowb (val : list Z) (LB0 : list byte) (li : nat) : list byte :=
  zb (map lower (firstn li val)) ++ skipn li LB0.

Lemma p6_firstn_S : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [|x l IH]; intros [|n] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn nth app]. rewrite IH by lia. reflexivity.
Qed.

Lemma p6_zb_len : forall val li, (li <= length val)%nat -> length (zb (map lower (firstn li val))) = li.
Proof. intros val li H. unfold zb. rewrite !length_map, length_firstn. lia. Qed.

Lemma p6_lowb_len : forall val LB0 li, length LB0 = 64%nat -> (li <= length val)%nat -> (li <= 64)%nat ->
  length (p6_lowb val LB0 li) = 64%nat.
Proof.
  intros val LB0 li L H1 H2. unfold p6_lowb. rewrite length_app, p6_zb_len by exact H1.
  rewrite length_skipn. lia.
Qed.

Lemma p6_lowb_0 : forall val LB0, p6_lowb val LB0 0 = LB0.
Proof. reflexivity. Qed.

Lemma p6_lowb_step : forall val LB0 li, (li < length val)%nat -> (li < length LB0)%nat ->
  upd_bytes (p6_lowb val LB0 li) li [Z_to_bv 8 (lower (nth li val 0))] = p6_lowb val LB0 (S li).
Proof.
  intros val LB0 li H1 H2. pose proof (p6_zb_len val li ltac:(lia)) as L1.
  unfold upd_bytes, p6_lowb.
  assert (F1 : firstn li (zb (map lower (firstn li val))) = zb (map lower (firstn li val)))
    by (apply firstn_all2; lia).
  assert (S1 : skipn (li + 1) (zb (map lower (firstn li val))) = []) by (apply skipn_all2; lia).
  rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r, F1.
  cbn [length]. rewrite skipn_app, S1, L1. cbn [app].
  replace (li + 1 - li)%nat with 1%nat by lia. rewrite skipn_skipn.
  replace (1 + li)%nat with (S li) by lia.
  rewrite (p6_firstn_S val li H1). unfold zb. rewrite !map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma p6_lowb_fin : forall val LB0 li, (li <= length val)%nat -> (li < length LB0)%nat ->
  upd_bytes (p6_lowb val LB0 li) li [ZERO] = zb (map lower (firstn li val)) ++ ZERO :: skipn (S li) LB0.
Proof.
  intros val LB0 li H1 H2. pose proof (p6_zb_len val li H1) as L1.
  unfold upd_bytes, p6_lowb.
  assert (F1 : firstn li (zb (map lower (firstn li val))) = zb (map lower (firstn li val)))
    by (apply firstn_all2; lia).
  assert (S1 : skipn (li + 1) (zb (map lower (firstn li val))) = []) by (apply skipn_all2; lia).
  rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r, F1.
  cbn [length]. rewrite skipn_app, S1, L1. cbn [app].
  replace (li + 1 - li)%nat with 1%nat by lia. rewrite skipn_skipn.
  replace (1 + li)%nat with (S li) by lia. reflexivity.
Qed.

Lemma p6_lower_range : forall c, 0 <= c < 256 -> 0 <= lower c < 256.
Proof. intros c H. unfold lower. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|exact H].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma p6_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  unfold zs, zb in *. cbn [map]. f_equal; [|exact (IH Hl)].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma p6_lower_forall : forall l, Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (map lower l).
Proof.
  intros l H. apply Forall_map. eapply Forall_impl; [|exact H]. intros x Hx. cbv beta. apply p6_lower_range. exact Hx.
Qed.

Lemma p6_forall_firstn : forall (P : Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto.
Qed.

(** INTENT's LB: the prefix of the 64 bytes is the fold and its NUL. *)
Lemma p6_lb_prefix : forall val li rest, Forall (fun x => 0 <= x < 256) val -> (li <= length val)%nat ->
  firstn (S li) (zs (zb (map lower (firstn li val)) ++ ZERO :: rest)) = map lower (firstn li val) ++ [0].
Proof.
  intros val li rest R H. unfold zs at 1. rewrite map_app. fold (zs (zb (map lower (firstn li val)))).
  rewrite p6_zs_zb by (apply p6_lower_forall, p6_forall_firstn, R).
  assert (L : length (map lower (firstn li val)) = li) by (rewrite length_map, length_firstn; lia).
  assert (F : firstn (S li) (map lower (firstn li val)) = map lower (firstn li val)) by (apply firstn_all2; lia).
  rewrite firstn_app, L, F. replace (S li - li)%nat with 1%nat by lia. reflexivity.
Qed.

(** The fold loop ends at li = min (length val) 63: there the fold is r_low val 0 64. *)
Lemma p6_rlow : forall val li, ~ In 0 val -> (li = length val \/ li = 63%nat) -> (li <= length val)%nat ->
  (li <= 63)%nat -> r_low val 0 64 = map lower (firstn li val).
Proof.
  intros val li NZ E H1 H2. rewrite r_low_fold_go by exact NZ. cbn [Nat.sub]. f_equal.
  destruct E as [->| ->]; [|reflexivity].
  assert (F : firstn 63 val = val) by (apply firstn_all2; lia). rewrite F. symmetry. apply firstn_all.
Qed.

Lemma p6_rlow_len : forall val li, ~ In 0 val -> (li = length val \/ li = 63%nat) -> (li <= length val)%nat ->
  (li <= 63)%nat -> length (r_low val 0 64) = li.
Proof.
  intros val li NZ E H1 H2. rewrite (p6_rlow val li NZ E H1 H2), length_map, length_firstn. lia.
Qed.

Lemma p6_rlow_nz : forall val, ~ In 0 val -> ~ In 0 (r_low val 0 64).
Proof. intros val NZ. rewrite r_low_fold by exact NZ. apply h_fold_nulfree. exact NZ. Qed.

(** ** The ranges of the compare results *)
Lemma p6_memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H; [injection H as <-; lia|].
  destruct l as [|a l], r as [|b r]; cbn in H; try discriminate.
  destruct (bv_unsigned a =? bv_unsigned b); [exact (IH l r v H)|].
  injection H as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
  unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb. lia.
Qed.

Lemma p6_word4_range : forall B, - 2 ^ 31 <= pf_word4 B < 2 ^ 31.
Proof.
  intros B. unfold pf_word4.
  pose proof (bv_unsigned_in_range 8 (nth 0 B ZERO)) as R0. pose proof (bv_unsigned_in_range 8 (nth 1 B ZERO)) as R1.
  pose proof (bv_unsigned_in_range 8 (nth 2 B ZERO)) as R2. pose proof (bv_unsigned_in_range 8 (nth 3 B ZERO)) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
  destruct (bv_unsigned (nth 3 B ZERO) <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

(** ** The two stores into seg[gi] (R:244-245): role = r, role_set = 1 *)
Lemma p6_nth_error_fld : forall (l : list byte) a n i,
  nth_error (fld a n l) i = if (i <? n)%nat then nth_error l (a + i) else None.
Proof.
  intros l a n i. unfold fld. rewrite nth_error_firstn. destruct (i <? n)%nat; [|reflexivity].
  rewrite nth_error_skipn. f_equal; lia.
Qed.

Lemma p6_fld_length : forall (l : list byte) a n, (a + n <= length l)%nat -> length (fld a n l) = n.
Proof. intros l a n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma p6_upd_nth_error : forall (l ws : list byte) k i, (k + length ws <= length l)%nat ->
  nth_error (upd_bytes l k ws) i =
    if (k <=? i)%nat && (i <? k + length ws)%nat then nth_error ws (i - k) else nth_error l i.
Proof.
  intros l ws k i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None (upd_bytes l k ws) i)) by (rewrite upd_bytes_length; lia).
    rewrite (proj2 (nth_error_None l i)) by lia.
    destruct (Nat.leb_spec0 k i), (Nat.ltb_spec0 i (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma p6_fld_upd_out : forall (l ws : list byte) k a n, (k + length ws <= length l)%nat ->
  (a + n <= k \/ k + length ws <= a)%nat -> fld a n (upd_bytes l k ws) = fld a n l.
Proof.
  intros l ws k a n H D. apply nth_error_ext. intros i. rewrite !p6_nth_error_fld.
  destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite p6_upd_nth_error by exact H.
  destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma p6_fld_upd_in : forall (l ws : list byte) k a n, (a + n <= length l)%nat -> (a <= k)%nat ->
  (k + length ws <= a + n)%nat -> fld a n (upd_bytes l k ws) = upd_bytes (fld a n l) (k - a) ws.
Proof.
  intros l ws k a n H1 H2 H3. apply nth_error_ext. intros i.
  rewrite p6_nth_error_fld, (p6_upd_nth_error (fld a n l)) by (rewrite p6_fld_length by lia; lia).
  rewrite p6_upd_nth_error by lia. rewrite p6_nth_error_fld.
  destruct (Nat.ltb_spec0 i n), (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)),
    (Nat.leb_spec0 (k - a) i), (Nat.ltb_spec0 i (k - a + length ws)); cbn [andb]; try reflexivity; try lia.
  f_equal. lia.
Qed.

Lemma p6_fld_upd_same : forall (l ws : list byte) k n, (k + length ws <= length l)%nat -> length ws = n ->
  fld k n (upd_bytes l k ws) = ws.
Proof.
  intros l ws k n H <-. apply nth_error_ext. intros i. rewrite p6_nth_error_fld.
  destruct (Nat.ltb_spec0 i (length ws)).
  - rewrite p6_upd_nth_error by exact H.
    destruct (Nat.leb_spec0 k (k + i)), (Nat.ltb_spec0 (k + i) (k + length ws)); cbn [andb]; try lia.
    f_equal. lia.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma p6_nth_upd : forall {A} (l : list A) i f j d, (i < length l)%nat ->
  nth j (upd_nth i f l) d = if (j =? i)%nat then f (nth i l d) else nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros i f j d H; cbn [length] in H; [lia|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Ltac p6_nums :=
  unfold fldz, RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE, RS_ROLE_FILE,
    RS_IGNORE_FILE, RS_SEEN_GEN, RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN in *;
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.

Ltac p6_unf :=
  unfold fldz, RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN in *.

Lemma p6_role_enc : forall s f r, rseg_enc s f -> 0 <= r < 2 ^ 31 ->
  rseg_enc (rs_with_role r (rs_role_file s) s)
    (upd_bytes (upd_bytes f 16 (le4 (Z_to_bv 64 r))) 20 (le4 (Z_to_bv 64 1))).
Proof.
  intros s f r (L & NM & RO & RS & IG & IS & MO & MS & MF & RF & IF & SG) Hr.
  unfold rs_with_role. unfold rseg_enc. cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model
    rs_model_set rs_model_file rs_role_file rs_ignore_file rs_seen_gen].
  p6_nums.
  assert (Lr : length (le4 (Z_to_bv 64 r)) = 4%nat) by apply length_le4.
  assert (L1w : length (le4 (Z_to_bv 64 1)) = 4%nat) by apply length_le4.
  assert (L1 : length (upd_bytes f 16 (le4 (Z_to_bv 64 r))) = 356%nat) by (rewrite upd_bytes_length; lia).
  assert (O : forall a n, (a + n <= 16 \/ 24 <= a)%nat -> (a + n <= 356)%nat ->
            fld a n (upd_bytes (upd_bytes f 16 (le4 (Z_to_bv 64 r))) 20 (le4 (Z_to_bv 64 1))) = fld a n f).
  { intros a n D B. rewrite p6_fld_upd_out by lia. apply p6_fld_upd_out; lia. }
  split; [rewrite !upd_bytes_length; lia|].
  split; [rewrite O by lia; exact NM|].
  split.
  { rewrite p6_fld_upd_out by lia. rewrite p6_fld_upd_same by lia. unfold role_enc, u32_enc.
    split; [split; [lia | reflexivity] | lia]. }
  split; [rewrite p6_fld_upd_same by lia; unfold flag_enc; reflexivity|].
  split; [rewrite O by lia; exact IG|].
  split; [rewrite O by lia; exact IS|].
  split; [rewrite O by lia; exact MO|].
  split; [rewrite O by lia; exact MS|].
  split; [rewrite O by lia; exact MF|].
  split; [rewrite O by lia; exact RF|].
  split; [rewrite O by lia; exact IF|].
  rewrite O by lia; exact SG.
Qed.

(** One entry of seg[] replaced, every other byte of the block kept. *)
Lemma p6_rconf_seg : forall rc bs bs' i g,
  rconf_enc rc bs -> (i < length (rc_seg rc))%nat -> length bs' = length bs ->
  (forall a n, (a + n <= 356 * i \/ 356 * i + 356 <= a)%nat -> (a + n <= length bs)%nat -> fld a n bs' = fld a n bs) ->
  rseg_enc (g (nth i (rc_seg rc) rseg_d)) (fld (356 * i) 356 bs') ->
  rconf_enc (r_upd rc i g) bs'.
Proof.
  intros rc bs bs' i g (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) Hi Lb O E.
  unfold SEG_C_SIZE in L. unfold r_upd, r_set_segs, rconf_enc.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. rewrite upd_nth_len.
  p6_unf.
  split; [unfold SEG_C_SIZE; rewrite Lb; exact L|].
  split; [exact LS|].
  split.
  { intros j Hj. rewrite p6_nth_upd by exact Hi.
    destruct (Nat.eqb_spec j i) as [->|Hji]; [exact E|].
    rewrite O by lia. apply SEGS. exact Hj. }
  split; [rewrite O by lia; exact N|].
  split; [exact LR|].
  split; [intros j Hj; rewrite O by lia; apply REF; exact Hj|].
  split; [rewrite O by lia; exact NR|].
  split; [rewrite O by lia; exact RF|].
  split; [rewrite O by lia; exact OV|].
  split; [rewrite O by lia; exact RD|].
  rewrite O by lia; exact GEN.
Qed.

(** The stores of R:244-245 at seg[gi] (plain 0x15490 / 0x15498, UBSan 0x15b5c / 0x15b60) on the whole block. *)
Lemma p6_role_rconf : forall rc bs gi r, rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> 0 <= r < 2 ^ 31 ->
  rconf_enc (pf_prov_mid (PRole r) rc gi)
    (upd_bytes (upd_bytes bs (356 * gi + 16) (le4 (Z_to_bv 64 r))) (356 * gi + 20) (le4 (Z_to_bv 64 1))).
Proof.
  intros rc bs gi r HE Hi Hr. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  assert (Lr : length (le4 (Z_to_bv 64 r)) = 4%nat) by apply length_le4.
  assert (L1w : length (le4 (Z_to_bv 64 1)) = 4%nat) by apply length_le4.
  assert (L1 : Z.of_nat (length (upd_bytes bs (356 * gi + 16) (le4 (Z_to_bv 64 r)))) = 16616)
    by (rewrite upd_bytes_length; lia).
  change (pf_prov_mid (PRole r) rc gi) with (r_upd rc gi (fun g => rs_with_role r (rs_role_file g) g)).
  apply (p6_rconf_seg rc bs _ gi (fun g => rs_with_role r (rs_role_file g) g) HE Hi).
  - rewrite !upd_bytes_length; lia.
  - intros a n D B. rewrite p6_fld_upd_out by lia. apply p6_fld_upd_out; lia.
  - rewrite p6_fld_upd_in by lia. rewrite p6_fld_upd_in by lia.
    replace (356 * gi + 20 - 356 * gi)%nat with 20%nat by lia.
    replace (356 * gi + 16 - 356 * gi)%nat with 16%nat by lia.
    cbv beta. apply p6_role_enc; [apply SEGS; exact Hi | exact Hr].
Qed.

(** The reader's state facts other than c's bytes, after the edit. *)
Lemma p6_prov_cur_ok : forall k rc gi, (gi < length (rc_seg rc))%nat -> pf_cur_ok (pf_prov_mid k rc gi) (Some gi).
Proof.
  intros k rc gi H. change (gi < length (rc_seg (pf_prov_mid k rc gi)))%nat.
  unfold pf_prov_mid, r_upd, r_set_segs. cbn [rc_seg]. rewrite upd_nth_len. exact H.
Qed.

Lemma p6_prov_cnt : forall k rc gi n, pf_cnt rc n -> pf_cnt (pf_prov_mid k rc gi) n.
Proof. intros k rc gi n H. exact H. Qed.

(** ** The arithmetic of the loop body and of the compares *)
Lemma p6_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma p6_zbv_eqm : forall a b, a mod 18446744073709551616 = b mod 18446744073709551616 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. exact H.
Qed.

(** The fold of one byte (R:237, plain 0x15084 .. 0x15098, UBSan 0x156c8 .. 0x156d4): `addi -0x41; sltiu 0x1a;
    slli 5; add`, then `sb`: the byte stored is lower c. *)
Lemma p6_fold_val : forall c, 0 <= c < 256 ->
  c + Z.shiftl (Z.b2z ((c + -65) mod 18446744073709551616 <? 26)) 5 = lower c.
Proof.
  intros c Hc. unfold lower.
  destruct ((65 <=? c) && (c <=? 90)) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    change (Z.shiftl (Z.b2z true) 5) with 32. lia.
  - assert (H : c < 65 \/ 90 < c).
    { apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E]; lia. }
    destruct H as [H|H].
    + assert (Hm : (c + -65) mod 18446744073709551616 = c + -65 + 18446744073709551616).
      { rewrite <- (Z.mod_add (c + -65) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite Hm, (proj2 (Z.ltb_ge _ _)) by lia. change (Z.shiftl (Z.b2z false) 5) with 0. lia.
    + rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
      change (Z.shiftl (Z.b2z false) 5) with 0. lia.
Qed.

Lemma p6_fold_le1 : forall c, 0 <= c < 256 ->
  le1 (Z_to_bv 64 (c + Z.shiftl (Z.b2z ((c + -65) mod 18446744073709551616 <? 26)) 5)) = [Z_to_bv 8 (lower c)].
Proof.
  intros c Hc. rewrite p6_fold_val by exact Hc. rewrite <- le1_zxb. unfold zxb.
  pose proof (p6_lower_range c Hc) as R. rewrite (p6_u8 (lower c) R). reflexivity.
Qed.

(** Bits apart: an or of a multiple of 2^k and a number below 2^k is their sum. *)
Lemma p6_lor_add : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a b = a + b.
Proof.
  intros a b k Hk Hb Ha.
  assert (L : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    - rewrite <- (Z.mod_pow2_bits_low a k i) by lia. rewrite Ha, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  assert (X : Z.lxor a b = Z.lor a b).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.lor_spec.
    pose proof (f_equal (fun z => Z.testbit z i) L) as T. cbv beta in T. rewrite Z.land_spec, Z.bits_0 in T.
    destruct (Z.testbit a i), (Z.testbit b i); cbn in *; congruence. }
  rewrite <- X. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

(** The tap / box word (R:117-118 through reac_role.h): `lbu b1; lbu b0; lbu b2; lb b3; slli 8; or; slli 16; slli 24;
    or; or` gives pf_word4 of the four bytes as a 64-bit register. *)
Lemma p6_word_val : forall b0 b1 b2 b3 : byte,
  Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl (bv_unsigned (sxb b3)) 24) mod 18446744073709551616)
                           ((Z.shiftl (bv_unsigned b2) 16) mod 18446744073709551616))
                    (Z.lor ((Z.shiftl (bv_unsigned b1) 8) mod 18446744073709551616) (bv_unsigned b0)))
  = Z_to_bv 64 (pf_word4 [b0; b1; b2; b3]).
Proof.
  intros b0 b1 b2 b3. unfold pf_word4. cbv beta zeta. cbn [nth].
  assert (R : forall b : byte, 0 <= bv_unsigned b < 256).
  { intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
    change (2 ^ Z.of_N 8) with 256 in H. exact H. }
  pose proof (R b0) as R0. pose proof (R b1) as R1. pose proof (R b2) as R2. pose proof (R b3) as R3.
  assert (S3 : bv_unsigned (sxb b3) =
               (if bv_unsigned b3 <? 128 then bv_unsigned b3 else bv_unsigned b3 - 256) mod 18446744073709551616).
  { unfold sxb. rewrite Z_to_bv_unsigned. unfold bv_wrap at 1. unfold bv_modulus at 1.
    change (2 ^ Z.of_N 64) with 18446744073709551616. f_equal.
    unfold bv_signed, bv_swrap. replace (bv_half_modulus 8) with 128 by reflexivity.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    destruct (Z.ltb_spec (bv_unsigned b3) 128).
    - rewrite Z.mod_small by lia. lia.
    - replace (bv_unsigned b3 + 128) with ((bv_unsigned b3 - 128) + 1 * 256) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite S3.
  set (s3 := if bv_unsigned b3 <? 128 then bv_unsigned b3 else bv_unsigned b3 - 256).
  assert (Rs : -128 <= s3 < 128) by (unfold s3; destruct (Z.ltb_spec (bv_unsigned b3) 128); lia).
  set (u0 := bv_unsigned b0) in *. set (u1 := bv_unsigned b1) in *. set (u2 := bv_unsigned b2) in *.
  clearbody s3 u0 u1 u2.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (u2 * 65536)) by lia. rewrite (Z.mod_small (u1 * 256)) by lia.
  set (X3 := (s3 mod 18446744073709551616 * 16777216) mod 18446744073709551616).
  assert (RX : 0 <= X3 < 18446744073709551616) by (unfold X3; apply Z.mod_pos_bound; lia).
  assert (DX : X3 mod 16777216 = 0) by (unfold X3; Z.div_mod_to_equations; lia).
  assert (EX : X3 mod 18446744073709551616 = (s3 * 16777216) mod 18446744073709551616)
    by (unfold X3; Z.div_mod_to_equations; lia).
  clearbody X3.
  rewrite (p6_lor_add (u1 * 256) u0 8) by (change (2 ^ 8) with 256; Z.div_mod_to_equations; lia).
  rewrite (p6_lor_add X3 (u2 * 65536) 24) by (change (2 ^ 24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite (p6_lor_add (X3 + u2 * 65536) (u1 * 256 + u0) 16)
    by (change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
  apply p6_zbv_eqm. Z.div_mod_to_equations. lia.
Qed.

Lemma p6_bveq_small : forall a b, - 2 ^ 62 <= a < 2 ^ 62 -> - 2 ^ 62 <= b < 2 ^ 62 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hne]; [apply Z.eqb_refl|]. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(** ** Bytes in memory, for any segment list *)
Section P6Mem.
Variable segs : list Segment.

Lemma p6_zb8 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma p6_byte_at : forall bs sl i, (i <= length bs)%nat ->
  nth_error (bs ++ ZERO :: sl) i = Some (Z_to_bv 8 (nth i (zs bs) 0)).
Proof.
  intros bs sl i Hi. destruct (Nat.lt_ge_cases i (length bs)) as [Hl|Hg].
  - rewrite nth_error_app1 by exact Hl. unfold zs.
    rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; exact Hl).
    rewrite map_nth, p6_zb8. apply nth_error_nth'. exact Hl.
  - assert (i = length bs) as -> by lia. rewrite nth_error_app2, Nat.sub_diag by lia. cbn.
    rewrite nth_overflow by (unfold zs; rewrite length_map; lia). reflexivity.
Qed.

Lemma p6_firstn1 : forall (l : list byte) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  induction l as [|x l IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma p6_read1 : forall m a l i b, bytes_at segs m a l -> nth_error l i = Some b ->
  ov_read_bytes segs m (wa (a + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m a l i b H E. assert (Hi : (i < length l)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_ov_read segs m a l i 1 H) by lia. f_equal. apply p6_firstn1. exact E.
Qed.

Lemma p6_stk_wr : forall m lo hi, stk segs m lo hi -> lo <= hi -> wr_at segs m lo (hi - lo).
Proof.
  intros m lo hi (H1 & H2 & H) Hle. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

End P6Mem.

Lemma p6_nth_nz : forall (l : list Z) i, ~ In 0 l -> (i < length l)%nat -> nth i l 0 <> 0.
Proof. intros l i H Hi E. apply H. rewrite <- E. apply nth_In. exact Hi. Qed.
