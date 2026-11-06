(** reac-pw/fuzz_segconf: the build-independent part of piece P4 of reac_segconf_parse_file (the header branch,
    R:159-213, and the inlined seg_get, R:103-118). Both lib/Prog/pf_p4.v (plain, image
    3776ca44d75c) and lib/U/Prog/pf_p4.v (UBSan, image 1696d6c34ffd) Require it; it Requires no image.

    1. The spine: SegModel.r_header unfolded along each branch the code takes (the refusals, then seg_get), and
       r_find_go one entry at a time (the search loop's invariant).
    2. The rconf_enc edits P4's stores make: c->overflow + 1 (the bound), c->n + 1 with the new entry memset to zeros
       and its name written (snprintf), seen_gen of entry i.
    3. Memory over any segment list: a block after a callee wrote part of it, one byte of a C string, a frame slot of
       a saved_at list, and the C strings P4 makes in buf (`*close = 0`, trim's result). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** 1. The spine *)

(** The header's body (R:174, after `*close = 0`) and its name (R:184). *)
Definition p4_body (l : list Z) (ci : nat) : list Z := r_trim (slice 1 ci l).
Definition p4_name (b : list Z) : list Z := r_trim (skipn 7 b).

(** r_header from seg_get on (R:197-211). *)
Definition p4_get (rc : rconf) (nm : list Z) (ln : Z) (name : list Z) : rconf * option nat * list Z :=
  match seg_get rc name with
  | (c1, None) => (refuse c1 ln F_bound [AS name; AI 32], None, nm)
  | (c1, Some (i, is_new)) =>
    let c2 := if negb is_new && (rs_seen_gen (nth i (rc_seg c1) rseg_d) =? rc_gen c1)
              then refuse c1 ln F_twice [AS name] else c1 in
    (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])
  end.

(** seg_get's bound branch: c->overflow + 1. *)
Definition p4_ovf (rc : rconf) : rconf :=
  RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc + 1) (rc_reading rc) (rc_gen rc).

Lemma p4_hdr_notclosed rc nm ln l : strchr l RBR = None ->
  r_header rc nm ln l = (refuse rc ln F_notclosed [AS l], None, nm).
Proof. intros H. unfold r_header. rewrite H. reflexivity. Qed.

Lemma p4_hdr_after rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 <> 0 ->
  r_header rc nm ln l = (refuse rc ln F_after [AS l], None, nm).
Proof. intros H1 H2. unfold r_header. rewrite H1. apply Z.eqb_neq in H2. rewrite H2. reflexivity. Qed.

Lemma p4_hdr_kw rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  r_header rc nm ln l =
    if negb (strncasecmp (p4_body l ci) S_segment 7 =? 0) || negb (sp_tab (nth 7 (p4_body l ci) 0))
    then (refuse rc ln F_unknown [AS (p4_body l ci)], None, nm) else
    if hd0 (p4_name (p4_body l ci)) =? 0 then (refuse rc ln F_noname [], None, nm) else
    if (16 <=? strlen (p4_name (p4_body l ci)))%nat
    then (refuse rc ln F_toolong [AS (p4_name (p4_body l ci)); AI 15], None, nm)
    else p4_get rc nm ln (p4_name (p4_body l ci)).
Proof. intros H1 H2. unfold r_header. rewrite H1, H2. reflexivity. Qed.

Lemma p4_hdr_unknown rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  (strncasecmp (p4_body l ci) S_segment 7 <> 0 \/ sp_tab (nth 7 (p4_body l ci) 0) = false) ->
  r_header rc nm ln l = (refuse rc ln F_unknown [AS (p4_body l ci)], None, nm).
Proof.
  intros H1 H2 H3. rewrite (p4_hdr_kw rc nm ln l ci H1 H2).
  destruct H3 as [H3|H3].
  - apply Z.eqb_neq in H3. rewrite H3. reflexivity.
  - rewrite H3. cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

Lemma p4_hdr_noname rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (p4_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (p4_body l ci) 0) = true ->
  hd0 (p4_name (p4_body l ci)) = 0 ->
  r_header rc nm ln l = (refuse rc ln F_noname [], None, nm).
Proof. intros H1 H2 H3 H4 H5. rewrite (p4_hdr_kw rc nm ln l ci H1 H2), H3, H4, H5. reflexivity. Qed.

Lemma p4_hdr_toolong rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (p4_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (p4_body l ci) 0) = true ->
  hd0 (p4_name (p4_body l ci)) <> 0 -> (16 <= strlen (p4_name (p4_body l ci)))%nat ->
  r_header rc nm ln l = (refuse rc ln F_toolong [AS (p4_name (p4_body l ci)); AI 15], None, nm).
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite (p4_hdr_kw rc nm ln l ci H1 H2), H3, H4.
  apply Z.eqb_neq in H5. rewrite H5. apply Nat.leb_le in H6. rewrite H6. reflexivity.
Qed.

Lemma p4_hdr_get rc nm ln l ci : strchr l RBR = Some ci -> nth (S ci) l 0 = 0 ->
  strncasecmp (p4_body l ci) S_segment 7 = 0 -> sp_tab (nth 7 (p4_body l ci) 0) = true ->
  hd0 (p4_name (p4_body l ci)) <> 0 -> (strlen (p4_name (p4_body l ci)) < 16)%nat ->
  r_header rc nm ln l = p4_get rc nm ln (p4_name (p4_body l ci)).
Proof.
  intros H1 H2 H3 H4 H5 H6. rewrite (p4_hdr_kw rc nm ln l ci H1 H2), H3, H4.
  apply Z.eqb_neq in H5. rewrite H5. apply Nat.leb_gt in H6. rewrite H6. reflexivity.
Qed.

Lemma p4_get_seen rc nm ln name i : r_find_go (rc_seg rc) name 0 = Some i ->
  rs_seen_gen (nth i (rc_seg rc) rseg_d) = rc_gen rc ->
  p4_get rc nm ln name =
    (r_upd (refuse rc ln F_twice [AS name]) i (rs_with_gen (rc_gen (refuse rc ln F_twice [AS name]))), Some i,
     snprintf_s 16 F_s [AS name]).
Proof. intros H1 H2. unfold p4_get, seg_get. rewrite H1. cbn [negb andb]. rewrite H2, Z.eqb_refl. reflexivity. Qed.

Lemma p4_get_unseen rc nm ln name i : r_find_go (rc_seg rc) name 0 = Some i ->
  rs_seen_gen (nth i (rc_seg rc) rseg_d) <> rc_gen rc ->
  p4_get rc nm ln name = (r_upd rc i (rs_with_gen (rc_gen rc)), Some i, snprintf_s 16 F_s [AS name]).
Proof.
  intros H1 H2. unfold p4_get, seg_get. rewrite H1. cbn [negb andb]. apply Z.eqb_neq in H2. rewrite H2. reflexivity.
Qed.

Lemma p4_get_full rc nm ln name : r_find_go (rc_seg rc) name 0 = None -> (32 <= length (rc_seg rc))%nat ->
  p4_get rc nm ln name = (refuse (p4_ovf rc) ln F_bound [AS name; AI 32], None, nm).
Proof. intros H1 H2. unfold p4_get, seg_get. rewrite H1. apply Nat.leb_le in H2. rewrite H2. reflexivity. Qed.

Lemma p4_get_new rc nm ln name : r_find_go (rc_seg rc) name 0 = None -> (length (rc_seg rc) < 32)%nat ->
  p4_get rc nm ln name =
    (r_upd (r_set_segs rc (rc_seg rc ++ [rseg0 (snprintf_s 16 F_s [AS name])])) (length (rc_seg rc))
       (rs_with_gen (rc_gen rc)), Some (length (rc_seg rc)), snprintf_s 16 F_s [AS name]).
Proof. intros H1 H2. unfold p4_get, seg_get. rewrite H1. apply Nat.leb_gt in H2. rewrite H2. reflexivity. Qed.

(** The search loop, one entry at a time: the names before i differ, so the search goes on from i. *)
Lemma p4_find_step : forall segs name i k, (i < length segs)%nat ->
  r_find_go (skipn i segs) name k =
  if strcmp (rs_name (nth i segs rseg_d)) name =? 0 then Some k else r_find_go (skipn (S i) segs) name (S k).
Proof.
  induction segs as [|g segs IH]; intros name i k H; cbn [length] in H; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma p4_find_end : forall segs name k, r_find_go (skipn (length segs) segs) name k = None.
Proof. intros segs name k. rewrite skipn_all. reflexivity. Qed.

(** ** 2. The encodings *)

Lemma p4_nth_error_fld : forall (l : list byte) a n i,
  nth_error (fld a n l) i = if (i <? n)%nat then nth_error l (a + i) else None.
Proof.
  intros l a n i. unfold fld. rewrite nth_error_firstn. destruct (i <? n)%nat; [|reflexivity].
  rewrite nth_error_skipn. f_equal; lia.
Qed.

Lemma p4_fld_length : forall (l : list byte) a n, (a + n <= length l)%nat -> length (fld a n l) = n.
Proof. intros l a n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma p4_upd_nth_error : forall (l ws : list byte) k i, (k + length ws <= length l)%nat ->
  nth_error (upd_bytes l k ws) i =
    if (k <=? i)%nat && (i <? k + length ws)%nat then nth_error ws (i - k) else nth_error l i.
Proof.
  intros l ws k i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None (upd_bytes l k ws) i)) by (rewrite upd_bytes_length; lia).
    rewrite (proj2 (nth_error_None l i)) by lia.
    destruct (Nat.leb_spec0 k i), (Nat.ltb_spec0 i (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma p4_fld_upd_out : forall (l ws : list byte) k a n, (k + length ws <= length l)%nat ->
  (a + n <= k \/ k + length ws <= a)%nat -> fld a n (upd_bytes l k ws) = fld a n l.
Proof.
  intros l ws k a n H D. apply nth_error_ext. intros i. rewrite !p4_nth_error_fld.
  destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite p4_upd_nth_error by exact H.
  destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma p4_fld_upd_in : forall (l ws : list byte) k a n, (a + n <= length l)%nat -> (a <= k)%nat ->
  (k + length ws <= a + n)%nat -> fld a n (upd_bytes l k ws) = upd_bytes (fld a n l) (k - a) ws.
Proof.
  intros l ws k a n H1 H2 H3. apply nth_error_ext. intros i.
  rewrite p4_nth_error_fld, (p4_upd_nth_error (fld a n l)) by (rewrite p4_fld_length by lia; lia).
  rewrite p4_upd_nth_error by lia. rewrite p4_nth_error_fld.
  destruct (Nat.ltb_spec0 i n), (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)),
    (Nat.leb_spec0 (k - a) i), (Nat.ltb_spec0 i (k - a + length ws)); cbn [andb]; try reflexivity; try lia.
  f_equal. lia.
Qed.

Lemma p4_fld_upd_same : forall (l ws : list byte) k n, (k + length ws <= length l)%nat -> length ws = n ->
  fld k n (upd_bytes l k ws) = ws.
Proof.
  intros l ws k n H <-. apply nth_error_ext. intros i. rewrite p4_nth_error_fld.
  destruct (Nat.ltb_spec0 i (length ws)).
  - rewrite p4_upd_nth_error by exact H.
    destruct (Nat.leb_spec0 k (k + i)), (Nat.ltb_spec0 (k + i) (k + length ws)); cbn [andb]; try lia.
    f_equal. lia.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma p4_upd_len : forall (l ws : list byte) k, (k + length ws <= length l)%nat ->
  length (upd_bytes l k ws) = length l.
Proof. intros l ws k. exact (upd_bytes_length l k ws). Qed.

Lemma p4_nth_upd : forall {A} (l : list A) i f j d, (i < length l)%nat ->
  nth j (upd_nth i f l) d = if (j =? i)%nat then f (nth i l d) else nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros i f j d H; cbn [length] in H; [lia|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Ltac p4_unf := unfold fldz, RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN in *.

(** One entry of seg[] replaced, every other byte of the block kept. *)
Lemma p4_rconf_seg : forall rc bs bs' i g,
  rconf_enc rc bs -> (i < length (rc_seg rc))%nat -> length bs' = length bs ->
  (forall a n, (a + n <= 356 * i \/ 356 * i + 356 <= a)%nat -> (a + n <= length bs)%nat -> fld a n bs' = fld a n bs) ->
  rseg_enc (g (nth i (rc_seg rc) rseg_d)) (fld (356 * i) 356 bs') ->
  rconf_enc (r_upd rc i g) bs'.
Proof.
  intros rc bs bs' i g (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) Hi Lb O E.
  unfold SEG_C_SIZE in L. unfold r_upd, r_set_segs, rconf_enc.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. rewrite upd_nth_len.
  p4_unf.
  split; [unfold SEG_C_SIZE; rewrite Lb; exact L|].
  split; [exact LS|].
  split.
  { intros j Hj. rewrite p4_nth_upd by exact Hi.
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

(** seen_gen := g on one entry (R:210). *)
Lemma p4_seen_enc : forall s f g, rseg_enc s f -> 0 <= g < 2 ^ 32 ->
  rseg_enc (rs_with_gen g s) (upd_bytes f 352 (le4 (Z_to_bv 64 g))).
Proof.
  intros s f g (L & NM & RO & RS & IG & IS & MO & MS & MF & RF & IF & SG) Hg.
  unfold rs_with_gen, rseg_enc. cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model
    rs_model_set rs_model_file rs_role_file rs_ignore_file rs_seen_gen].
  unfold fldz, RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE, RS_ROLE_FILE,
    RS_IGNORE_FILE, RS_SEEN_GEN in *.
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
  assert (Lw : length (le4 (Z_to_bv 64 g)) = 4%nat) by apply length_le4.
  assert (O : forall a n, (a + n <= 352)%nat -> fld a n (upd_bytes f 352 (le4 (Z_to_bv 64 g))) = fld a n f).
  { intros a n D. apply p4_fld_upd_out; lia. }
  split; [rewrite p4_upd_len; lia|].
  split; [rewrite O by lia; exact NM|].
  split; [rewrite O by lia; exact RO|].
  split; [rewrite O by lia; exact RS|].
  split; [rewrite O by lia; exact IG|].
  split; [rewrite O by lia; exact IS|].
  split; [rewrite O by lia; exact MO|].
  split; [rewrite O by lia; exact MS|].
  split; [rewrite O by lia; exact MF|].
  split; [rewrite O by lia; exact RF|].
  split; [rewrite O by lia; exact IF|].
  rewrite p4_fld_upd_same by lia. split; [exact Hg | reflexivity].
Qed.

Lemma p4_rconf_seen : forall rc bs i g, rconf_enc rc bs -> (i < length (rc_seg rc))%nat -> 0 <= g < 2 ^ 32 ->
  rconf_enc (r_upd rc i (rs_with_gen g)) (upd_bytes bs (356 * i + 352) (le4 (Z_to_bv 64 g))).
Proof.
  intros rc bs i g HE Hi Hg. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  assert (Lw : length (le4 (Z_to_bv 64 g)) = 4%nat) by apply length_le4.
  apply (p4_rconf_seg rc bs _ i (rs_with_gen g) HE Hi).
  - rewrite p4_upd_len; lia.
  - intros a n D B. apply p4_fld_upd_out; lia.
  - rewrite p4_fld_upd_in by lia. replace (356 * i + 352 - 356 * i)%nat with 352%nat by lia.
    apply p4_seen_enc; [apply SEGS; exact Hi | exact Hg].
Qed.

(** c->overflow + 1 (R:110). *)
Lemma p4_rconf_ovf : forall rc bs, rconf_enc rc bs -> rc_overflow rc + 1 < 2 ^ 32 ->
  rconf_enc (p4_ovf rc) (upd_bytes bs (Z.to_nat RC_OVERFLOW) (le4 (Z_to_bv 64 (rc_overflow rc + 1)))).
Proof.
  intros rc bs (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) Hov.
  unfold SEG_C_SIZE in L. unfold p4_ovf, rconf_enc.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. p4_unf.
  assert (Lw : length (le4 (Z_to_bv 64 (rc_overflow rc + 1))) = 4%nat) by apply length_le4.
  pose proof OV as ((OV0 & _) & _).
  assert (O : forall a n, (a + n <= Z.to_nat 13520 \/ Z.to_nat 13524 <= a)%nat ->
            fld a n (upd_bytes bs (Z.to_nat 13520) (le4 (Z_to_bv 64 (rc_overflow rc + 1)))) = fld a n bs).
  { intros a n D. apply p4_fld_upd_out; lia. }
  split; [unfold SEG_C_SIZE; rewrite p4_upd_len; lia|].
  split; [exact LS|].
  split; [intros j Hj; rewrite O by lia; apply SEGS; exact Hj|].
  split; [rewrite O by lia; exact N|].
  split; [exact LR|].
  split; [intros j Hj; rewrite O by lia; apply REF; exact Hj|].
  split; [rewrite O by lia; exact NR|].
  split; [rewrite O by lia; exact RF|].
  split; [rewrite p4_fld_upd_same by lia; split; [lia | reflexivity]|].
  split; [rewrite O by lia; exact RD|].
  rewrite O by lia; exact GEN.
Qed.

Definition zbyte (x : Z) : Prop := 0 <= x < 256.

Lemma p4_zs_zb : forall l, Forall zbyte l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [|exact (IH Hl)]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold zbyte in Hx. change (bv_modulus 8) with 256. lia.
Qed.

Lemma p4_zb_zs : forall bs, zb (zs bs) = bs.
Proof.
  unfold zs, zb. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma p4_zs_byte : forall bs, Forall zbyte (zs bs).
Proof.
  intros bs. unfold zs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. unfold zbyte. lia.
Qed.

Lemma p4_length_zb : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma p4_fld_repeat : forall off n len, (off + n <= len)%nat -> fld off n (repeat ZERO len) = repeat ZERO n.
Proof. intros. apply fld_repeat. exact H. Qed.

(** The new entry: memset(seg[n], 0, 356) then its name and NUL (snprintf "%s", 16). *)
Lemma p4_rseg0_enc : forall name, Forall zbyte name -> ~ In 0 name -> (length name < 16)%nat ->
  rseg_enc (rseg0 name) (upd_bytes (repeat ZERO 356) 0 (zb name ++ [ZERO])).
Proof.
  intros name Hb Hn Hl.
  assert (Lw : length (zb name ++ [ZERO]) = S (length name))
    by (rewrite length_app, p4_length_zb; cbn [length]; lia).
  assert (Lr : length (repeat ZERO 356) = 356%nat) by apply repeat_length.
  assert (O : forall a n, (16 <= a)%nat -> (a + n <= 356)%nat ->
    fld a n (upd_bytes (repeat ZERO 356) 0 (zb name ++ [ZERO])) = repeat ZERO n).
  { intros a n H1 H2. rewrite p4_fld_upd_out by lia. apply p4_fld_repeat. lia. }
  unfold rseg0, rseg_enc. cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model
    rs_model_set rs_model_file rs_role_file rs_ignore_file rs_seen_gen].
  unfold fldz, RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE, RS_ROLE_FILE,
    RS_IGNORE_FILE, RS_SEEN_GEN.
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  split; [rewrite p4_upd_len; lia|].
  split.
  { rewrite p4_fld_upd_in by lia. rewrite Nat.sub_0_r, p4_fld_repeat by lia.
    unfold cstr_enc. unfold upd_bytes. rewrite firstn_O, app_nil_l, Lw.
    split; [rewrite length_app, Lw, length_skipn, repeat_length; lia|].
    split; [exact Hl|]. split; [exact Hn|].
    rewrite <- app_assoc. cbn [app]. unfold zs. rewrite map_app. cbn [map].
    rewrite firstn_app, length_map, p4_length_zb.
    replace (S (length name) - length name)%nat with 1%nat by lia.
    rewrite firstn_all2 by (rewrite length_map, p4_length_zb; lia). cbn [firstn].
    fold (zs (zb name)). rewrite p4_zs_zb by exact Hb. reflexivity. }
  split; [rewrite O by lia; split; [exact u32_enc_zero | lia]|].
  split; [rewrite O by lia; exact flag_enc_false_zero|].
  split; [rewrite O by lia; exact flag_enc_false_zero|].
  split; [rewrite O by lia; exact flag_enc_false_zero|].
  split; [rewrite O by lia; apply cstr_enc_nil_zero; lia|].
  split; [rewrite O by lia; exact flag_enc_false_zero|].
  split; [rewrite O by lia; apply cstr_enc_nil_zero; lia|].
  split; [rewrite O by lia; apply cstr_enc_nil_zero; lia|].
  split; [rewrite O by lia; apply cstr_enc_nil_zero; lia|].
  rewrite O by lia. exact u32_enc_zero.
Qed.

(** c->n = n + 1, seg[n] = zeros, then its name (R:113-115). *)
Lemma p4_rconf_new : forall rc bs name, rconf_enc rc bs -> (length (rc_seg rc) < 32)%nat ->
  Forall zbyte name -> ~ In 0 name -> (length name < 16)%nat ->
  rconf_enc (r_set_segs rc (rc_seg rc ++ [rseg0 name]))
    (upd_bytes (upd_bytes (upd_bytes bs (Z.to_nat RC_N) (le4 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc)) + 1))))
                  (356 * length (rc_seg rc)) (repeat ZERO 356))
       (356 * length (rc_seg rc)) (zb name ++ [ZERO])).
Proof.
  intros rc bs name (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) H32 Hb Hn Hl.
  unfold SEG_C_SIZE in L. unfold RC_N in *. set (k := length (rc_seg rc)) in *.
  set (W4 := le4 (Z_to_bv 64 (Z.of_nat k + 1))).
  assert (Lw4 : length W4 = 4%nat) by apply length_le4.
  assert (Lnm : length (zb name ++ [ZERO]) = S (length name))
    by (rewrite length_app, p4_length_zb; cbn [length]; lia).
  assert (Lr : length (repeat ZERO 356) = 356%nat) by apply repeat_length.
  set (bs1 := upd_bytes bs (Z.to_nat 11392) W4).
  set (bs2 := upd_bytes bs1 (356 * k) (repeat ZERO 356)).
  set (bs3 := upd_bytes bs2 (356 * k) (zb name ++ [ZERO])).
  assert (L1 : length bs1 = length bs) by (unfold bs1; rewrite p4_upd_len; lia).
  assert (L2 : length bs2 = length bs) by (unfold bs2; rewrite p4_upd_len; lia).
  assert (L3 : length bs3 = length bs) by (unfold bs3; rewrite p4_upd_len; lia).
  (* every byte outside seg[k] and n is kept *)
  assert (O : forall a n, (a + n <= 356 * k \/ 356 * k + 356 <= a)%nat ->
            (a + n <= Z.to_nat 11392 \/ Z.to_nat 11392 + 4 <= a)%nat ->
            (a + n <= length bs)%nat -> fld a n bs3 = fld a n bs).
  { intros a n D1 D2 B.
    unfold bs3. rewrite p4_fld_upd_out by (rewrite ?L2; lia).
    unfold bs2. rewrite p4_fld_upd_out by (rewrite ?L1; lia).
    unfold bs1. apply p4_fld_upd_out; lia. }
  unfold r_set_segs, rconf_enc.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. p4_unf.
  rewrite length_app. cbn [length].
  split; [unfold SEG_C_SIZE; rewrite L3; exact L|].
  split; [lia|].
  split.
  { intros j Hj. destruct (Nat.lt_ge_cases j k) as [Hjk|Hjk].
    - rewrite app_nth1 by exact Hjk. rewrite O by lia. apply SEGS. exact Hjk.
    - assert (Ej : j = k) by lia. subst j.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      unfold bs3. rewrite p4_fld_upd_in by (rewrite ?L2; lia). rewrite Nat.sub_diag.
      unfold bs2. rewrite p4_fld_upd_same by (rewrite ?L1; lia).
      apply p4_rseg0_enc; assumption. }
  split.
  { unfold bs3. rewrite p4_fld_upd_out by (rewrite ?L2; lia).
    unfold bs2. rewrite p4_fld_upd_out by (rewrite ?L1; lia). unfold bs1. rewrite p4_fld_upd_same by lia.
    split; [lia | unfold W4; f_equal; f_equal; lia]. }
  split; [exact LR|].
  split; [intros j Hj; rewrite O by lia; apply REF; exact Hj|].
  split; [rewrite O by lia; exact NR|].
  split; [rewrite O by lia; exact RF|].
  split; [rewrite O by lia; exact OV|].
  split; [rewrite O by lia; exact RD|].
  rewrite O by lia; exact GEN.
Qed.

(** ** 3. Memory, for any segment list *)
Section P4Mem.
Variable segs : list Segment.

(** A callee wrote ws at a (its munch W, ws read back after the call); the rest of the block at c is kept. *)
Lemma p4_bytes_upd_munch : forall W m m' c bs a ws,
  bytes_at segs m c bs -> munch W m m' -> bytes_at segs m' a ws ->
  c <= a -> a + Z.of_nat (length ws) <= c + Z.of_nat (length bs) ->
  (forall x, c <= x < c + Z.of_nat (length bs) -> ~ (a <= x < a + Z.of_nat (length ws)) -> outside W x) ->
  bytes_at segs m' c (upd_bytes bs (Z.to_nat (a - c)) ws).
Proof.
  intros W m m' c bs a ws (H0 & H1 & HB) MU (G0 & G1 & HW) Ha1 Ha2 OUT.
  assert (Lu : length (upd_bytes bs (Z.to_nat (a - c)) ws) = length bs) by (apply upd_bytes_length; lia).
  split; [lia|]. split; [rewrite Lu; lia|].
  intros i Hi. rewrite Lu in Hi. rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec0 (Z.to_nat (a - c)) i), (Nat.ltb_spec0 i (Z.to_nat (a - c) + length ws)); cbn [andb].
  - replace (c + Z.of_nat i) with (a + Z.of_nat (i - Z.to_nat (a - c))) by lia. apply HW. lia.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply OUT; lia.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply OUT; lia.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply OUT; lia.
Qed.

Lemma p4_firstn1_skipn : forall (L : list byte) k d, (k < length L)%nat -> firstn 1 (skipn k L) = [nth k L d].
Proof.
  induction L as [|x L IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(** One byte of a C string, its NUL included, as `lbu` reads it. *)
Lemma p4_cstr_byte : forall m a l k, cstr_at segs m a l -> (k <= length l)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) 1 = Some [Z_to_bv 8 (nth k l 0)].
Proof.
  intros m a l k (bs & sl & B & Hz & Hn & Hs) Hk.
  assert (Lb : length bs = length l) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  rewrite (bytes_at_ov_read segs m a _ k 1 B) by (rewrite length_app; cbn [length]; lia).
  rewrite (p4_firstn1_skipn _ k ZERO) by (rewrite length_app; cbn [length]; lia).
  f_equal. f_equal.
  destruct (Nat.lt_ge_cases k (length bs)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. rewrite <- Hz. unfold zs.
    rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; lia).
    rewrite map_nth. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    apply bv_unsigned_in_range.
  - rewrite app_nth2 by exact Hge. replace (k - length bs)%nat with 0%nat by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma p4_length_concat_le8 : forall ws : list word, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia.
Qed.

(** A frame slot of a saved_at list, as `ld` reads it. *)
Lemma p4_saved_read : forall m a ws k, saved_at segs m a ws -> (k < length ws)%nat ->
  ov_read_bytes segs m (wa (a + 8 * Z.of_nat k)) 8 = Some (le8 (nth k ws (Z_to_bv 64 0))).
Proof.
  intros m a ws k H Hk. unfold saved_at in H.
  replace (a + 8 * Z.of_nat k) with (a + Z.of_nat (8 * k)) by lia.
  rewrite (bytes_at_ov_read segs m a _ (8 * k) 8 H) by (rewrite p4_length_concat_le8; lia).
  f_equal. clear H. revert k Hk. induction ws as [|w ws IH]; intros k Hk; cbn [length] in Hk; [lia|].
  cbn [map concat]. destruct k as [|k].
  - rewrite Nat.mul_0_r, skipn_O, firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - replace (8 * S k)%nat with (8 * k + length (le8 w))%nat by (rewrite length_le8; lia).
    rewrite <- skipn_skipn, skipn_app, skipn_all, Nat.sub_diag, skipn_O, app_nil_l. cbn [nth].
    apply IH. lia.
Qed.

Lemma p4_snoc {A} : forall (l : list A) d, (0 < length l)%nat ->
  l = firstn (length l - 1) l ++ [nth (length l - 1) l d].
Proof.
  induction l as [|x l IH]; intros d H; cbn [length] in H; [lia|].
  destruct l as [|y l]; [reflexivity|].
  cbn [length] in *. replace (S (S (length l)) - 1)%nat with (S (length l)) by lia.
  cbn [firstn nth app]. f_equal. specialize (IH d ltac:(lia)).
  replace (S (length l) - 1)%nat with (length l) in IH by lia. exact IH.
Qed.

(** `*close = 0` at the ']' that ends the line (R:173): the bytes 1 .. ci of the line are a C string at lp + 1. *)
Lemma p4_cstr_close : forall m lp l ci, cstr_at segs m lp l -> S ci = length l -> (1 <= ci)%nat ->
  cstr_at segs (write_to_mem m (wa (lp + Z.of_nat ci)) [ZERO]) (lp + 1) (slice 1 ci l).
Proof.
  intros m lp l ci (bs & sl & B & Hz & Hn & Hs) Hl H1.
  assert (Lb : length bs = length l) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  destruct bs as [|b0 bs']; [cbn [length] in Lb; lia|].
  assert (Lb' : length bs' = ci) by (cbn [length] in Lb; lia).
  pose proof (p4_snoc bs' ZERO ltac:(lia)) as Eb. rewrite Lb' in Eb.
  set (u := firstn (ci - 1) bs') in *. set (x := nth (ci - 1) bs' ZERO) in *.
  assert (Lu : length u = (ci - 1)%nat) by (unfold u; rewrite length_firstn; lia).
  assert (Zs : zs u = slice 1 ci l).
  { rewrite <- Hz. unfold slice, u, zs. rewrite map_cons, skipn_cons, skipn_O, firstn_map. reflexivity. }
  rewrite Eb in B.
  pose proof (bytes_at_write_inside segs m lp ((b0 :: u ++ [x]) ++ ZERO :: sl) (Z.of_nat ci) [ZERO] B
    ltac:(lia) ltac:(rewrite length_app; cbn [length]; rewrite length_app; cbn [length]; lia)) as B1.
  rewrite Nat2Z.id in B1.
  assert (E : upd_bytes ((b0 :: u ++ [x]) ++ ZERO :: sl) ci [ZERO] = (b0 :: u) ++ [ZERO] ++ ZERO :: sl).
  { replace ((b0 :: u ++ [x]) ++ ZERO :: sl) with ((b0 :: u) ++ [x] ++ ZERO :: sl)
      by (cbn [app]; rewrite <- app_assoc; reflexivity).
    replace ci with (length (b0 :: u)) by (cbn [length]; lia). apply upd_bytes_mid. reflexivity. }
  rewrite E in B1. cbn [app] in B1.
  change (b0 :: u ++ ZERO :: ZERO :: sl) with ([b0] ++ (u ++ ZERO :: ZERO :: sl)) in B1.
  apply bytes_at_app in B1 as [_ B2]. cbn [length] in B2.
  replace (lp + Z.of_nat 1) with (lp + 1) in B2 by lia.
  exists u, (ZERO :: sl).
  split; [exact B2|]. split; [exact Zs|]. split.
  - apply nulfree_slice. exact Hn.
  - rewrite <- Zs. unfold zs. rewrite length_map, Lu. cbn [length].
    rewrite <- Lb in Hs. cbn [length] in Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma p4_firstn_add : forall {A} a b (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; [rewrite !firstn_nil; reflexivity|]. cbn [Nat.add firstn skipn app]. f_equal. apply IH.
Qed.

(** A present stack region is writable, and a store into it is allowed. *)
Lemma p4_stk_wr : forall m lo hi a n, stk segs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at segs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn Hh. split; [lia|]. split; [lia|]. intros i Hi.
  apply (H (a + i)). lia.
Qed.

Lemma p4_stk_store_ok : forall m lo hi a (k : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  store_ok segs m (wa a) k = true.
Proof.
  intros m lo hi a k ST H1 H2. pose proof (p4_stk_wr m lo hi a (Z.of_nat k) ST H1 ltac:(lia) H2) as W.
  pose proof (wr_at_store_ok segs m a (Z.of_nat k) 0 k W ltac:(lia) ltac:(lia)) as S.
  rewrite Z.add_0_r in S. exact S.
Qed.

(** A store is a munch of its own bytes. *)
Lemma p4_munch_write : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  munch [(a, a + Z.of_nat (length bs))] m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H1 H2. apply munch_write; [apply munch_refl | exact H1 | exact H2 |]. cbn [inside]. left. lia.
Qed.

(** trim(p) on the C string x at p (trim_c.v's post): the C string at p + trim_lead x is r_trim x, with the slack
    after it (the bytes after the stored NUL are the old ones). *)
Lemma p4_cstr_trim : forall W m m' p x,
  cstr_at segs m p x -> munch W m m' ->
  (forall y, p <= y < p + Z.of_nat (length x) + 8 -> outside W y \/ y = p + Z.of_nat (trim_lead x + length (r_trim x))) ->
  bytes_at segs m' p (zb (firstn (trim_lead x + length (r_trim x)) x) ++ [ZERO]) ->
  (trim_lead x + length (r_trim x) <= length x)%nat -> r_trim x = firstn (length (r_trim x)) (skipn (trim_lead x) x) ->
  ~ In 0 (r_trim x) ->
  cstr_at segs m' (p + Z.of_nat (trim_lead x)) (r_trim x).
Proof.
  intros W m m' p x (bs & sl & B & Hz & Hn & Hs) MU OUT B' T1 T2 T3.
  set (lead := trim_lead x) in *. set (rt := r_trim x) in *. set (e := (lead + length rt)%nat) in *.
  assert (Lb : length bs = length x) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length x) + 1)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (p + Z.of_nat (length x) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (p + Z.of_nat (length x) + 1)) mod 8) by (unfold k; lia).
  clearbody k.
  set (R := bs ++ ZERO :: firstn k sl).
  assert (LR : length R = (length x + 1 + k)%nat).
  { unfold R. rewrite length_app. cbn [length]. rewrite length_firstn. lia. }
  assert (BR : bytes_at segs m p R).
  { rewrite <- (firstn_skipn k sl) in B.
    replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with (R ++ skipn k sl) in B
      by (unfold R; rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B as [B _]. exact B. }
  set (TB := zb (firstn e x) ++ [ZERO]).
  assert (LTB : length TB = S e).
  { unfold TB. rewrite length_app, p4_length_zb, length_firstn. cbn [length]. lia. }
  pose proof (p4_bytes_upd_munch W m m' p R p TB BR MU B' ltac:(lia) ltac:(rewrite LTB, LR; lia)) as BU.
  specialize (BU ltac:(intros y Hy Hn'; destruct (OUT y ltac:(rewrite LR in Hy; lia)) as [O|O];
                        [exact O | exfalso; apply Hn'; rewrite LTB; lia])).
  replace (Z.to_nat (p - p)) with 0%nat in BU by lia.
  assert (EU : upd_bytes R 0 TB = zb (firstn lead x) ++ (zb rt ++ ZERO :: skipn (S e) R)).
  { unfold upd_bytes. rewrite firstn_O, app_nil_l, Nat.add_0_l, LTB. unfold TB. unfold e.
    rewrite p4_firstn_add, <- T2. unfold zb. rewrite map_app. rewrite <- !app_assoc. reflexivity. }
  rewrite EU in BU. apply bytes_at_app in BU as [_ BU].
  rewrite p4_length_zb, length_firstn, Nat.min_l in BU by lia.
  assert (Zr : zs (zb rt) = rt).
  { apply p4_zs_zb. rewrite T2. apply Forall_firstn'. apply Forall_skipn'. rewrite <- Hz.
    apply p4_zs_byte. }
  exists (zb rt), (skipn (S e) R).
  split; [exact BU|]. split; [exact Zr|]. split; [exact T3|].
  rewrite length_skipn, LR. unfold e. Z.div_mod_to_equations. lia.
Qed.

(** The 4-byte fields of struct reac_segconf P4 reads with `lw`. *)
Lemma p4_read_n : forall m c bs rc, bytes_at segs m c bs -> rconf_enc rc bs ->
  ov_read_bytes segs m (wa (c + 11392)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc))))).
Proof.
  intros m c bs rc HB HE. pose proof HE as (L & _ & _ & (_ & HN) & _). unfold SEG_C_SIZE in L.
  unfold fldz, RC_N in HN. rewrite (bytes_at_read segs m c bs 11392 4 HB) by lia. rewrite <- HN. reflexivity.
Qed.

Lemma p4_read_ovf : forall m c bs rc, bytes_at segs m c bs -> rconf_enc rc bs ->
  0 <= rc_overflow rc < 2 ^ 32 /\
  ov_read_bytes segs m (wa (c + 13520)) 4 = Some (le4 (Z_to_bv 64 (rc_overflow rc))).
Proof.
  intros m c bs rc HB HE. pose proof HE as (L & _ & _ & _ & _ & _ & _ & _ & (HR & HN) & _). unfold SEG_C_SIZE in L.
  unfold fldz, RC_OVERFLOW in HN. split; [exact HR|].
  rewrite (bytes_at_read segs m c bs 13520 4 HB) by lia. rewrite <- HN. reflexivity.
Qed.

Lemma p4_read_gen : forall m c bs rc, bytes_at segs m c bs -> rconf_enc rc bs ->
  0 <= rc_gen rc < 2 ^ 32 /\
  ov_read_bytes segs m (wa (c + 16608)) 4 = Some (le4 (Z_to_bv 64 (rc_gen rc))).
Proof.
  intros m c bs rc HB HE. pose proof HE as (L & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HR & HN)). unfold SEG_C_SIZE in L.
  unfold fldz, RC_GEN in HN. split; [exact HR|].
  rewrite (bytes_at_read segs m c bs 16608 4 HB) by lia. rewrite <- HN. reflexivity.
Qed.

Lemma p4_fld_seg : forall (bs : list byte) i a n, (a + n <= 356)%nat ->
  fld a n (fld (356 * i) 356 bs) = fld (356 * i + a) n bs.
Proof.
  intros bs i a n H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite Nat.min_l by lia. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma p4_read_seen : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  0 <= rs_seen_gen (nth i (rc_seg rc) rseg_d) < 2 ^ 32 /\
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + 352)) 4 =
    Some (le4 (Z_to_bv 64 (rs_seen_gen (nth i (rc_seg rc) rseg_d)))).
Proof.
  intros m c bs rc i HB HE Hi. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  destruct (SEGS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HR & HN)).
  unfold fldz, RS_SEEN_GEN in HN. change (Z.to_nat 352) with 352%nat in HN. change (Z.to_nat 4) with 4%nat in HN.
  rewrite p4_fld_seg in HN by lia. split; [exact HR|].
  replace (c + 356 * Z.of_nat i + 352) with (c + Z.of_nat (356 * i + 352)) by lia.
  rewrite (bytes_at_ov_read segs m c bs (356 * i + 352) 4 HB) by lia. rewrite <- HN. reflexivity.
Qed.

(** The C string of a char[cap] field of the block, with 7 bytes of slack after its NUL (cstr_at). *)
Lemma p4_cstr_in_block : forall m c bs off cap s, bytes_at segs m c bs -> cstr_enc cap s (fld off cap bs) ->
  (off + cap <= length bs)%nat -> (off + length s + 8 <= length bs)%nat ->
  cstr_at segs m (c + Z.of_nat off) s.
Proof.
  intros m c bs off cap s HB (Lf & Ls & Hn & Hz) B1 B2.
  set (L := length s) in *.
  assert (H : bytes_at segs m (c + Z.of_nat off) (firstn (L + 8) (skipn off bs))).
  { rewrite <- (firstn_skipn off bs) in HB. apply bytes_at_app in HB as [_ HB].
    rewrite length_firstn, Nat.min_l in HB by lia.
    rewrite <- (firstn_skipn (L + 8) (skipn off bs)) in HB. apply bytes_at_app in HB as [HB _]. exact HB. }
  exists (firstn L (skipn off bs)), (firstn 7 (skipn (off + L + 1) bs)).
  assert (E : firstn (L + 8) (skipn off bs) =
              firstn L (skipn off bs) ++ nth (off + L) bs ZERO :: firstn 7 (skipn (off + L + 1) bs)).
  { apply nth_error_ext. intros j. rewrite nth_error_firstn.
    destruct (Nat.ltb_spec0 j (L + 8)) as [J8|J8].
    - destruct (Nat.ltb_spec0 j L) as [J|J].
      + rewrite nth_error_app1 by (rewrite length_firstn, length_skipn; lia).
        rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j L); [reflexivity|lia].
      + rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
        rewrite length_firstn, length_skipn. replace (Nat.min L (length bs - off)) with L by lia.
        destruct (j - L)%nat as [|j'] eqn:Ej.
        * cbn [nth_error]. rewrite nth_error_skipn.
          match goal with |- nth_error bs ?k = _ => replace k with (off + L)%nat by lia end.
          apply nth_error_nth'. lia.
        * cbn [nth_error]. rewrite nth_error_firstn, !nth_error_skipn.
          destruct (Nat.ltb_spec0 j' 7); [|lia]. f_equal. lia.
    - symmetry. apply nth_error_None. rewrite length_app, length_firstn, length_skipn. cbn [length].
      rewrite length_firstn, length_skipn. lia. }
  rewrite E in H. unfold fld in Hz.
  assert (F : firstn (S L) (firstn cap (skipn off bs)) = firstn L (skipn off bs) ++ [nth (off + L) bs ZERO]).
  { rewrite firstn_firstn, Nat.min_l by lia. apply nth_error_ext. intros j. rewrite nth_error_firstn.
    destruct (Nat.ltb_spec0 j (S L)) as [J|J].
    - destruct (Nat.ltb_spec0 j L) as [J'|J'].
      + rewrite nth_error_app1 by (rewrite length_firstn, length_skipn; lia).
        rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j L); [reflexivity|lia].
      + rewrite nth_error_app2 by (rewrite length_firstn, length_skipn; lia).
        rewrite length_firstn, length_skipn. replace (j - Nat.min L (length bs - off))%nat with 0%nat by lia.
        cbn [nth_error]. rewrite nth_error_skipn.
        match goal with |- nth_error bs ?k = _ => replace k with (off + L)%nat by lia end.
        apply nth_error_nth'. lia.
    - symmetry. apply nth_error_None. rewrite length_app, length_firstn, length_skipn. cbn [length]. lia. }
  unfold zs in Hz. rewrite firstn_map, F, map_app in Hz. cbn [map] in Hz.
  apply app_inj_tail in Hz as [Z1 Z2].
  assert (Z0 : nth (off + L) bs ZERO = ZERO) by (apply bv_eq; rewrite Z2; reflexivity).
  rewrite Z0 in H.
  split; [exact H|]. split; [exact Z1|]. split; [exact Hn|].
  rewrite length_firstn, length_skipn. pose proof (Z.mod_pos_bound (- (c + Z.of_nat off + Z.of_nat L + 1)) 8). lia.
Qed.

Lemma p4_name_at : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  cstr_at segs m (c + 356 * Z.of_nat i) (rs_name (nth i (rc_seg rc) rseg_d)) /\
  (length (rs_name (nth i (rc_seg rc) rseg_d)) < 16)%nat.
Proof.
  intros m c bs rc i HB HE Hi. pose proof HE as (L & LS & SEGS & _). unfold SEG_C_SIZE in L.
  destruct (SEGS i Hi) as (_ & NM & _). pose proof NM as (_ & Ls & _).
  rewrite p4_fld_seg in NM by lia. rewrite Nat.add_0_r in NM.
  split; [|exact Ls].
  replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
  eapply p4_cstr_in_block; [exact HB | exact NM | lia | lia].
Qed.

End P4Mem.
