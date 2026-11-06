(** reac-pw/fuzz_segconf: the build-independent helpers of the walks of the pieces P7, P8 and P9 of
    reac_segconf_parse_file (family F3). No image and no machine: the spine's counters after a refusal or an entry
    edit, the line account (pf_next), byte-list edits (upd_bytes, fld) and the rconf_enc / rseg_enc edits of one seg
    entry (the ignore pair, the model and its flag, the provenance file field). The plain helpers
    (lib/Prog/pfC_facts.v) and the UBSan ones (lib/U/Prog/pfC_facts.v) both Require Export this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

Lemma pfc_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.
Lemma pfc_len_le8s : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map concat length]; [reflexivity|]. rewrite length_app, length_le8, IH. lia. Qed.
Lemma pfc_next_gt : forall s o, (o < length s)%nat -> (o < pf_next s o)%nat /\ (pf_next s o <= length s)%nat.
Proof.
  intros s o Ho. unfold pf_next. destruct (skipn o s) as [|b p] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - pose proof (break_nl_len_cons b p) as H. apply (f_equal (@length Z)) in E. rewrite length_skipn in E.
    cbn [length] in E. lia.
Qed.
(** * The spine's counters *)
Lemma pfc_refuse_fields : forall rc ln f a,
  rc_seg (refuse rc ln f a) = rc_seg rc /\ rc_refused (refuse rc ln f a) = rc_refused rc + 1 /\
  rc_overflow (refuse rc ln f a) = rc_overflow rc /\ rc_reading (refuse rc ln f a) = rc_reading rc /\
  rc_gen (refuse rc ln f a) = rc_gen rc.
Proof.
  intros rc ln f a. unfold refuse.
  destruct (8 <=? Z.of_nat (length (rc_refusal rc))); [cbn; tauto|].
  destruct ((snprintf_r (r_addr_fmt ln) (r_addr_args rc ln) <? 0) ||
            (200 <=? snprintf_r (r_addr_fmt ln) (r_addr_args rc ln))); cbn; tauto.
Qed.

(** After one refusal the counters still have room for the k' < k bytes left. *)
Lemma pfc_cnt_refuse : forall rc ln f a k k', pf_cnt rc k -> (k' < k)%nat -> pf_cnt (refuse rc ln f a) k'.
Proof.
  intros rc ln f a k k' [H1 H2] Hk. destruct (pfc_refuse_fields rc ln f a) as (_ & E1 & E2 & _).
  unfold pf_cnt. rewrite E1, E2. lia.
Qed.

Lemma pfc_cur_ok_refuse : forall rc ln f a cur, pf_cur_ok rc cur -> pf_cur_ok (refuse rc ln f a) cur.
Proof.
  intros rc ln f a cur H. destruct cur as [i|]; [|exact I]. cbn in *.
  destruct (pfc_refuse_fields rc ln f a) as (E & _). rewrite E. exact H.
Qed.

Lemma pfc_upd_fields : forall rc gi g,
  length (rc_seg (r_upd rc gi g)) = length (rc_seg rc) /\ rc_refused (r_upd rc gi g) = rc_refused rc /\
  rc_overflow (r_upd rc gi g) = rc_overflow rc /\ rc_reading (r_upd rc gi g) = rc_reading rc /\
  rc_gen (r_upd rc gi g) = rc_gen rc /\ rc_refusal (r_upd rc gi g) = rc_refusal rc.
Proof.
  intros rc gi g. unfold r_upd, r_set_segs. cbn. split; [|tauto].
  generalize (rc_seg rc) gi. induction l as [|x l IH]; intros [|i]; cbn; auto.
Qed.

Lemma pfc_cnt_upd : forall rc gi g k k', pf_cnt rc k -> (k' <= k)%nat -> pf_cnt (r_upd rc gi g) k'.
Proof.
  intros rc gi g k k' [H1 H2] Hk. destruct (pfc_upd_fields rc gi g) as (_ & E1 & E2 & _).
  unfold pf_cnt. rewrite E1, E2. lia.
Qed.

Lemma pfc_cur_ok_upd : forall rc gi g cur, pf_cur_ok rc cur -> pf_cur_ok (r_upd rc gi g) cur.
Proof.
  intros rc gi g cur H. destruct cur as [i|]; [|exact I]. unfold pf_cur_ok in *.
  destruct (pfc_upd_fields rc gi g) as (E & _). rewrite E. exact H.
Qed.

(** * Byte-list edits (upd_bytes, fld) *)
Definition pfc_zbyte (x : Z) : Prop := 0 <= x < 256.

Lemma pfc_len_zb : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma pfc_zs_zb : forall l, Forall pfc_zbyte l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [|exact (IH Hl)]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. unfold pfc_zbyte in Hx. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma pfc_zs_byte : forall bs, Forall pfc_zbyte (zs bs).
Proof.
  intros bs. unfold zs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256%Z in Hb. unfold pfc_zbyte. lia.
Qed.

Lemma pfc_nth_skipn : forall {A} (l : list A) off i d, nth i (skipn off l) d = nth (off + i) l d.
Proof.
  intros A l off. revert l. induction off as [|off IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; [cbn; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma pfc_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i] d H; cbn; try lia; try reflexivity. apply IH. lia.
Qed.

Lemma pfc_len_fld : forall off n (bs : list byte), (off + n <= length bs)%nat -> length (fld off n bs) = n.
Proof. intros. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma pfc_nth_fld : forall off n (bs : list byte) i d, (i < n)%nat -> nth i (fld off n bs) d = nth (off + i) bs d.
Proof. intros. unfold fld. rewrite pfc_nth_firstn by lia. apply pfc_nth_skipn. Qed.

Lemma pfc_nth_upd : forall (bs : list byte) k w j d, (k + length w <= length bs)%nat ->
  nth j (upd_bytes bs k w) d =
    if (j <? k)%nat then nth j bs d else if (j <? k + length w)%nat then nth (j - k) w d else nth j bs d.
Proof.
  intros bs k w j d H. unfold upd_bytes.
  destruct (Nat.ltb_spec j k).
  - rewrite app_nth1 by (rewrite length_firstn; lia). apply pfc_nth_firstn. lia.
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min k (length bs)) with k by lia.
    destruct (Nat.ltb_spec j (k + length w)).
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite pfc_nth_skipn. f_equal. lia.
Qed.

Ltac pfc_ltb := repeat match goal with |- context [if (?a <? ?b)%nat then _ else _] => destruct (Nat.ltb_spec a b) end.

Lemma pfc_fld_upd_out : forall bs k w off n, (k + length w <= length bs)%nat -> (off + n <= length bs)%nat ->
  (off + n <= k \/ k + length w <= off)%nat -> fld off n (upd_bytes bs k w) = fld off n bs.
Proof.
  intros bs k w off n H1 H2 H3. apply nth_ext with (d := ZERO) (d' := ZERO).
  - rewrite !pfc_len_fld; [reflexivity | lia | rewrite upd_bytes_length; lia].
  - intros i Hi. rewrite pfc_len_fld in Hi by (rewrite upd_bytes_length; lia).
    rewrite !pfc_nth_fld by lia. rewrite pfc_nth_upd by lia. pfc_ltb; try reflexivity. lia.
Qed.

Lemma pfc_fld_upd_in : forall bs k w n, n = length w -> (k + n <= length bs)%nat -> fld k n (upd_bytes bs k w) = w.
Proof.
  intros bs k w n -> H. apply nth_ext with (d := ZERO) (d' := ZERO).
  - rewrite pfc_len_fld; [reflexivity | rewrite upd_bytes_length; lia].
  - intros i Hi. rewrite pfc_len_fld in Hi by (rewrite upd_bytes_length; lia).
    rewrite pfc_nth_fld by lia. rewrite pfc_nth_upd by lia. pfc_ltb; try lia. f_equal. lia.
Qed.

Lemma pfc_fld_upd_sub : forall bs k w off n, (off <= k)%nat -> (k + length w <= off + n)%nat ->
  (off + n <= length bs)%nat -> fld off n (upd_bytes bs k w) = upd_bytes (fld off n bs) (k - off) w.
Proof.
  intros bs k w off n H1 H2 H3. apply nth_ext with (d := ZERO) (d' := ZERO).
  - rewrite pfc_len_fld by (rewrite upd_bytes_length; lia). rewrite upd_bytes_length; rewrite pfc_len_fld; lia.
  - intros i Hi. rewrite pfc_len_fld in Hi by (rewrite upd_bytes_length; lia).
    rewrite pfc_nth_fld by lia. rewrite (pfc_nth_upd (fld off n bs)) by (rewrite pfc_len_fld; lia).
    rewrite pfc_nth_upd by lia. pfc_ltb; try (exfalso; lia); try (rewrite pfc_nth_fld by lia; reflexivity).
    f_equal. lia.
Qed.

Lemma pfc_upd_nest : forall bs k n off w, (off + length w <= n)%nat -> (k + n <= length bs)%nat ->
  upd_bytes bs (k + off) w = upd_bytes bs k (upd_bytes (fld k n bs) off w).
Proof.
  intros bs k n off w H1 H2.
  assert (LF : length (fld k n bs) = n) by (apply pfc_len_fld; lia).
  assert (LU : length (upd_bytes (fld k n bs) off w) = n) by (rewrite upd_bytes_length; lia).
  apply nth_ext with (d := ZERO) (d' := ZERO).
  - rewrite !upd_bytes_length; lia.
  - intros j Hj. rewrite upd_bytes_length in Hj by lia.
    rewrite pfc_nth_upd by lia. rewrite (pfc_nth_upd bs k) by lia. rewrite LU.
    pfc_ltb; try (exfalso; lia);
      repeat (first [rewrite pfc_nth_upd by lia | rewrite pfc_nth_fld by lia]; pfc_ltb; try (exfalso; lia));
      try reflexivity; f_equal; lia.
Qed.

(** A char[cap] field that a string write (its bytes and its NUL, from the field's start) has replaced. *)
Lemma pfc_cstr_enc_new : forall cap s f, length f = cap -> (length s < cap)%nat -> ~ In 0 s -> Forall pfc_zbyte s ->
  cstr_enc cap s (upd_bytes f 0 (zb s ++ [ZERO])).
Proof.
  intros cap s f Hf Hl Hn Hb. unfold cstr_enc.
  split; [rewrite upd_bytes_length; [lia | rewrite length_app, pfc_len_zb; cbn [length]; lia]|].
  split; [exact Hl|]. split; [exact Hn|].
  unfold upd_bytes. change (firstn 0 f) with (@nil byte). rewrite app_nil_l.
  rewrite <- app_assoc. unfold zs. rewrite !map_app. fold (zs (zb s)). rewrite (pfc_zs_zb s Hb).
  cbn [map]. change (bv_unsigned ZERO) with 0.
  rewrite firstn_app, (firstn_all2 (n := S (length s)) s) by lia.
  replace (S (length s) - length s)%nat with 1%nat by lia. reflexivity.
Qed.

(** * The c block: one seg entry edited *)
Lemma pfc_nth_upd_nth : forall {A} i (f : A -> A) l j d, (i < length l)%nat ->
  nth j (upd_nth i f l) d = if (j =? i)%nat then f (nth i l d) else nth j l d.
Proof.
  intros A i f l. revert i. induction l as [|x l IH]; intros [|i] [|j] d H; cbn in *; try lia; try reflexivity.
  rewrite IH by lia. destruct (j =? i)%nat; reflexivity.
Qed.

Lemma pfc_enc_seg : forall rc bs gi F f',
  rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> length f' = 356%nat ->
  rseg_enc (F (nth gi (rc_seg rc) rseg_d)) f' ->
  rconf_enc (r_upd rc gi F) (upd_bytes bs (356 * gi) f').
Proof.
  intros rc bs gi F f' (HL & H32 & HS & HN & HR8 & HR & HNR & HRF & HOV & HRD & HG) Hgi Hf' HE.
  unfold SEG_C_SIZE in HL.
  unfold r_upd, r_set_segs, rconf_enc, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen] in *. rewrite upd_nth_len.
  refine (conj _ (conj H32 (conj _ (conj _ (conj HR8 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - rewrite upd_bytes_length by lia. exact HL.
  - intros i Hi. rewrite pfc_nth_upd_nth by lia.
    destruct (Nat.eqb_spec i gi) as [->|Hne].
    + rewrite pfc_fld_upd_in by lia. exact HE.
    + rewrite pfc_fld_upd_out by lia. apply HS. exact Hi.
  - rewrite pfc_fld_upd_out by (unfold RC_N; lia). exact HN.
  - intros i Hi. rewrite pfc_fld_upd_out by (unfold RC_REFUSAL; lia). apply HR. exact Hi.
  - rewrite pfc_fld_upd_out by (unfold RC_NREF; lia). exact HNR.
  - rewrite pfc_fld_upd_out by (unfold RC_REFUSED; lia). exact HRF.
  - rewrite pfc_fld_upd_out by (unfold RC_OVERFLOW; lia). exact HOV.
  - rewrite pfc_fld_upd_out by (unfold RC_READING; lia). exact HRD.
  - rewrite pfc_fld_upd_out by (unfold RC_GEN; lia). exact HG.
Qed.

Lemma pfc_rseg_len : forall g f, rseg_enc g f -> length f = 356%nat.
Proof. intros g f H. exact (proj1 H). Qed.

Lemma pfc_seg_fld : forall rc bs gi, rconf_enc rc bs -> (gi < length (rc_seg rc))%nat ->
  rseg_enc (nth gi (rc_seg rc) rseg_d) (fld (356 * gi) 356 bs).
Proof. intros rc bs gi (_ & _ & HS & _) Hgi. apply HS. exact Hgi. Qed.

Lemma pfc_upd_upd_same : forall (bs : list byte) k X Y, length X = length Y -> (k + length X <= length bs)%nat ->
  upd_bytes (upd_bytes bs k X) k Y = upd_bytes bs k Y.
Proof.
  intros bs k X Y HXY H. apply nth_ext with (d := ZERO) (d' := ZERO).
  - rewrite !upd_bytes_length; rewrite ?upd_bytes_length; lia.
  - intros j Hj. rewrite !upd_bytes_length in Hj by (rewrite ?upd_bytes_length; lia).
    rewrite pfc_nth_upd by (rewrite upd_bytes_length; lia). rewrite !pfc_nth_upd by lia.
    rewrite <- HXY. pfc_ltb; try reflexivity; try (exfalso; lia).
Qed.

(** One entry edited at the bytes [off, off + length w) of the entry: the whole block with the bytes replaced. *)
Lemma pfc_enc_seg_at : forall rc bs gi F off w,
  rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> (off + length w <= 356)%nat ->
  rseg_enc (F (nth gi (rc_seg rc) rseg_d)) (upd_bytes (fld (356 * gi) 356 bs) off w) ->
  rconf_enc (r_upd rc gi F) (upd_bytes bs (356 * gi + off) w).
Proof.
  intros rc bs gi F off w HE Hgi Hw HR.
  pose proof HE as (HL & H32 & _).
  unfold SEG_C_SIZE in HL.
  rewrite (pfc_upd_nest bs (356 * gi) 356 off w) by lia.
  apply pfc_enc_seg; [exact HE | exact Hgi | | exact HR].
  rewrite upd_bytes_length; rewrite pfc_len_fld; lia.
Qed.

(** Two edits of the same entry. *)
Lemma pfc_enc_seg_at2 : forall rc bs gi F off1 w1 off2 w2,
  rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> (off1 + length w1 <= 356)%nat ->
  (off2 + length w2 <= 356)%nat ->
  rseg_enc (F (nth gi (rc_seg rc) rseg_d)) (upd_bytes (upd_bytes (fld (356 * gi) 356 bs) off1 w1) off2 w2) ->
  rconf_enc (r_upd rc gi F) (upd_bytes (upd_bytes bs (356 * gi + off1) w1) (356 * gi + off2) w2).
Proof.
  intros rc bs gi F off1 w1 off2 w2 HE Hgi Hw1 Hw2 HR.
  pose proof HE as (HL & H32 & _).
  unfold SEG_C_SIZE in HL.
  set (X := upd_bytes (fld (356 * gi) 356 bs) off1 w1).
  assert (LX : length X = 356%nat) by (subst X; rewrite upd_bytes_length; rewrite pfc_len_fld; lia).
  rewrite (pfc_upd_nest bs (356 * gi) 356 off1 w1) by lia. fold X.
  rewrite (pfc_upd_nest (upd_bytes bs (356 * gi) X) (356 * gi) 356 off2 w2) by (rewrite ?upd_bytes_length; lia).
  rewrite pfc_fld_upd_in by lia.
  rewrite pfc_upd_upd_same by (rewrite ?upd_bytes_length; lia).
  apply pfc_enc_seg; [exact HE | exact Hgi | | exact HR].
  rewrite upd_bytes_length; lia.
Qed.

(** ** The field edits of the role / ignore / model / provenance branches *)
Ltac pfc_len := repeat (rewrite upd_bytes_length); rewrite ?length_le4, ?length_app, ?pfc_len_zb; cbn [length]; lia.

Ltac pfc_rseg_unfold :=
  unfold rseg_enc, fldz, RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE,
    RS_ROLE_FILE, RS_IGNORE_FILE, RS_SEEN_GEN in *;
  cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file rs_role_file
       rs_ignore_file rs_seen_gen] in *;
  simpl Z.to_nat in *.

(** A field that no edit touches, or a 4-byte field an edit replaced. *)
Ltac pfc_field :=
  first [ pfc_len
        | rewrite !pfc_fld_upd_out by pfc_len; assumption
        | rewrite !pfc_fld_upd_out by pfc_len; rewrite pfc_fld_upd_in by pfc_len; reflexivity
        | rewrite pfc_fld_upd_in by pfc_len; reflexivity ].

(** ignore = b, ignore_set = 1 (plain `sw` at seg + 0x18 and seg + 0x1c): rs_with_ignore with the old file. *)
Lemma pfc_rseg_ignore : forall g f b, rseg_enc g f ->
  rseg_enc (rs_with_ignore b (rs_ignore_file g) g)
    (upd_bytes (upd_bytes f 24 (le4 (Z_to_bv 64 (if b then 1 else 0)))) 28 (le4 (Z_to_bv 64 1))).
Proof.
  intros g f b (HL & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg).
  unfold rs_with_ignore. pfc_rseg_unfold.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))));
    pfc_field.
Qed.

(** model = mdl (snprintf at seg + 0x24: its bytes and NUL), model_set = 1 (`sw` at seg + 0x3c). *)
Lemma pfc_rseg_model : forall g f mdl, rseg_enc g f -> (length mdl < 24)%nat -> ~ In 0 mdl -> Forall pfc_zbyte mdl ->
  rseg_enc (rs_with_model mdl (rs_model_file g) g)
    (upd_bytes (upd_bytes f 36 (zb mdl ++ [ZERO])) 60 (le4 (Z_to_bv 64 1))).
Proof.
  intros g f mdl (HL & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg) Hl Hz Hb.
  unfold rs_with_model. pfc_rseg_unfold.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))));
    try pfc_field.
  rewrite pfc_fld_upd_out by pfc_len. rewrite pfc_fld_upd_sub by pfc_len.
  replace (36 - 36)%nat with 0%nat by lia. apply pfc_cstr_enc_new; [apply pfc_len_fld; lia | exact Hl | exact Hz | exact Hb].
Qed.

(** The old value fields of a provenance edit are kept by the file write; the file field holds file. *)
Lemma pfc_prov_set_twice : forall k f1 f2 g, pf_prov_set k f2 (pf_prov_set k f1 g) = pf_prov_set k f2 g.
Proof. intros [r|b|mdl] f1 f2 g; reflexivity. Qed.

Lemma pfc_rseg_file : forall k g f old file, rseg_enc (pf_prov_set k old g) f ->
  (length file < 96)%nat -> ~ In 0 file -> Forall pfc_zbyte file ->
  rseg_enc (pf_prov_set k file g) (upd_bytes f (Z.to_nat (pf_prov_off k)) (zb file ++ [ZERO])).
Proof.
  intros k g f old file HR Hl Hz Hb.
  destruct k as [r|b|mdl]; cbn [pf_prov_set pf_prov_off] in *;
    [unfold rs_with_role in * | unfold rs_with_ignore in * | unfold rs_with_model in *];
    destruct HR as (HL & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg); pfc_rseg_unfold;
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))));
    try pfc_field.
  all: rewrite pfc_fld_upd_sub by pfc_len; rewrite Nat.sub_diag;
    apply pfc_cstr_enc_new; [apply pfc_len_fld; lia | exact Hl | exact Hz | exact Hb].
Qed.

Lemma pfc_nth_upd_twice : forall {A} i (h g : A -> A) (l : list A) d, (i < length l)%nat ->
  upd_nth i (fun _ => h (nth i l d)) (upd_nth i g l) = upd_nth i h l.
Proof.
  intros A i h g l. revert i. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; try reflexivity.
  f_equal. apply IH. lia.
Qed.

(** The provenance site (P9's snprintf(field, 96, "%s", c->reading)): from pf_prov_mid to the file written. *)
Lemma pfc_enc_prov_fin : forall k rc gi bs file,
  rconf_enc (pf_prov_mid k rc gi) bs -> (gi < length (rc_seg rc))%nat ->
  (length file < 96)%nat -> ~ In 0 file -> Forall pfc_zbyte file ->
  rconf_enc (r_upd rc gi (pf_prov_set k file))
    (upd_bytes bs (356 * gi + Z.to_nat (pf_prov_off k)) (zb file ++ [ZERO])).
Proof.
  intros k rc gi bs file HE Hgi Hl Hz Hb.
  assert (Hgi' : (gi < length (rc_seg (pf_prov_mid k rc gi)))%nat)
    by (unfold pf_prov_mid; rewrite (proj1 (pfc_upd_fields rc gi _)); exact Hgi).
  assert (E : r_upd (pf_prov_mid k rc gi) gi (fun _ => pf_prov_set k file (nth gi (rc_seg rc) rseg_d)) =
              r_upd rc gi (pf_prov_set k file)).
  { unfold pf_prov_mid, r_upd, r_set_segs. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
    f_equal. apply pfc_nth_upd_twice. exact Hgi. }
  rewrite <- E. apply pfc_enc_seg_at; [exact HE | exact Hgi' | |].
  - rewrite length_app, pfc_len_zb. cbn [length].
    destruct k; cbn [pf_prov_off]; unfold RS_ROLE_FILE, RS_IGNORE_FILE, RS_MODEL_FILE; lia.
  - pose proof (pfc_seg_fld _ _ gi HE Hgi') as HS.
    unfold pf_prov_mid, r_upd, r_set_segs in HS. cbn [rc_seg] in HS.
    rewrite pfc_nth_upd_nth in HS by exact Hgi. rewrite Nat.eqb_refl in HS.
    exact (pfc_rseg_file k _ _ _ file HS Hl Hz Hb).
Qed.

(** The model hit (P7: snprintf(cur->model, 24, "%s", low), then model_set = 1). *)
Lemma pfc_enc_model : forall rc bs gi mdl, rconf_enc rc bs -> (gi < length (rc_seg rc))%nat ->
  (length mdl < 24)%nat -> ~ In 0 mdl -> Forall pfc_zbyte mdl ->
  rconf_enc (pf_prov_mid (PModel mdl) rc gi)
    (upd_bytes (upd_bytes bs (356 * gi + 36) (zb mdl ++ [ZERO])) (356 * gi + 60) (le4 (Z_to_bv 64 1))).
Proof.
  intros rc bs gi mdl HE Hgi Hl Hz Hb. unfold pf_prov_mid.
  apply pfc_enc_seg_at2; [exact HE | exact Hgi | rewrite length_app, pfc_len_zb; cbn [length]; lia
                         | rewrite length_le4; lia |].
  cbn [pf_prov_set pf_prov_old]. apply pfc_rseg_model; [apply pfc_seg_fld; assumption | exact Hl | exact Hz | exact Hb].
Qed.

Lemma pfc_nth_error_skipn : forall {A} (l : list A) off i, nth_error (skipn off l) i = nth_error l (off + i).
Proof.
  intros A l off. revert l. induction off as [|off IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [cbn; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma pfc_nth_error_firstn : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i] H; cbn; try lia; try reflexivity. apply IH. lia.
Qed.

Lemma pfc_nth_error_upd : forall (bs : list byte) k w j, (k + length w <= length bs)%nat ->
  nth_error (upd_bytes bs k w) j =
    if (j <? k)%nat then nth_error bs j else if (j <? k + length w)%nat then nth_error w (j - k) else nth_error bs j.
Proof.
  intros bs k w j H. unfold upd_bytes.
  destruct (Nat.ltb_spec j k).
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). apply pfc_nth_error_firstn. lia.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min k (length bs)) with k by lia.
    destruct (Nat.ltb_spec j (k + length w)).
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite pfc_nth_error_skipn. f_equal. lia.
Qed.
(** The large nat literal of pf_text's bound, for lia. *)
Lemma pfc_len65535 : forall (s : list Z), (length s <= 65535)%nat -> Z.of_nat (length s) <= 65535.
Proof. intros s H. apply Nat2Z.inj_le in H. exact H. Qed.
Lemma pfc_le65535 : forall k : nat, Z.of_nat k <= 65535 -> (k <= 65535)%nat.
Proof. intros k H. apply Nat2Z.inj_le. exact H. Qed.
(** snprintf(D, n, "%s", s) stores s when it fits. *)
Lemma pfc_snprintf_s_id : forall n s, nulfree s -> Z.of_nat (length s) < n -> snprintf_s n F_s [AS s] = s.
Proof.
  intros n s Hn Hl. unfold snprintf_s. change F_s with [37; 115]. cbn [fmt].
  replace (negb (37 =? PCT)) with false by reflexivity. cbn. rewrite app_nil_r, cut_nul_id by exact Hn.
  apply firstn_all2. lia.
Qed.

Lemma pfc_cnt_upd_iff : forall rc gi g k, pf_cnt (r_upd rc gi g) k <-> pf_cnt rc k.
Proof. intros rc gi g k. destruct (pfc_upd_fields rc gi g) as (_ & E1 & E2 & _). unfold pf_cnt. rewrite E1, E2. tauto. Qed.

Lemma pfc_cur_ok_upd_iff : forall rc gi g cur, pf_cur_ok (r_upd rc gi g) cur <-> pf_cur_ok rc cur.
Proof.
  intros rc gi g [i|]; [|cbn; tauto]. unfold pf_cur_ok. destruct (pfc_upd_fields rc gi g) as (E & _). rewrite E. tauto.
Qed.
Lemma pfc_cnt_mono : forall rc k k', pf_cnt rc k -> (k' <= k)%nat -> pf_cnt rc k'.
Proof. intros rc k k' [H1 H2] H. split; lia. Qed.

(** The provenance file fields lie in the entry and away from its other fields. *)
Lemma pfc_prov_off_range : forall k, 64 <= pf_prov_off k /\ pf_prov_off k + 96 <= 352.
Proof. intros [r|b|mdl]; cbn [pf_prov_off]; unfold RS_ROLE_FILE, RS_IGNORE_FILE, RS_MODEL_FILE; lia. Qed.
