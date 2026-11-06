(** reac-pw/fuzz_segconf: the image-free lemmas of piece P8 (the ignore key, R:271-280) of reac_segconf_parse_file,
    shared by the plain walk lib/Prog/pf_p8.v and the UBSan walk lib/U/Prog/pf_p8.v (family F3,
    lib/Prog/reac_segconf_parse_file_pieces_c.v and its U twin). No function of the binary is proved here, and no
    image is read: the lemmas are about SegModel's Gallina functions, seg_spec's encodings and byte lists.

    - [p8_spine]: r_key's ignore branch under H_IGN's premises (the key line split, the three strcasecmp results).
    - [p8_lower_eq]: strcasecmp_c's lower_eq of the value and a literal is SegModel.strcasecmp ... = 0 (for any
      function that is SegModel.tolower on a byte: the plain and the UBSan tolower_c.zlower).
    - [p8_strcmp1]: parse_bool's strcmp v "1" / "0" = 0 is v = [x] for a NUL-free v (the binary's val[0] / val[1]).
    - [p8_cstr_byte]: the byte i of a C string in memory (what `lbu` reads).
    - [p8_rconf_ign]: the two int stores ignore = b, ignore_set = 1 into seg[gi] give rconf_enc of
      pf_prov_mid (PIgn b) rc gi. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** * The spine *)
(** r_key's ignore branch (R:271-280): the key line split at ei, cur = Some gi, key neither "role" nor "model" and
    equal to "ignore" after the fold. The provenance edit is pf_prov_fin (PIgn b). *)
Lemma p8_spine : forall rc gi nm ln line ei key val,
  strchr line EQ = Some ei -> key = r_trim (firstn ei line) -> val = r_unquote (r_trim (skipn (S ei) line)) ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 -> strcasecmp key S_ignore = 0 ->
  r_key rc (Some gi) nm ln line =
    match parse_bool val with
    | None => (refuse rc ln F_badignore [AS nm; AS val], Some gi, nm)
    | Some b => (pf_prov_fin (PIgn b) rc gi, Some gi, nm)
    end.
Proof.
  intros rc gi nm ln line ei key val Hs Hk Hv H1 H2 H3. unfold r_key. rewrite Hs. cbv beta iota zeta.
  rewrite <- Hk, <- Hv.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_eq _ _) H3).
  destruct (parse_bool val); reflexivity.
Qed.

(** * Byte values (as Spec/SegBridge.v states them; restated here so that this file needs no
    build's contracts) *)
Definition p8_byte_vals (L : list Z) : Prop := forall x, In x L -> 0 < x < 256.

Lemma p8_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma p8_nul_val : bv_unsigned (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

Lemma p8_vals_zs : forall l : list byte, ~ In (Z_to_bv 8 0) l -> p8_byte_vals (zs l).
Proof.
  intros l H x Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & Hb). pose proof (p8_byte_range b).
  split; [|lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia]. exfalso. apply H.
  replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma p8_nul_free_bytes : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof. intros bs H Hin. apply H. unfold zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

(** * strcasecmp *)
Lemma p8_tolower_pos : forall x, 0 < x < 256 -> 0 < SegModel.tolower x.
Proof.
  intros x Hx.
  assert (H : forallb (fun z => 0 <? SegModel.tolower z) (map Z.of_nat (seq 1 255)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.ltb_lt. apply H. apply in_map_iff. exists (Z.to_nat x).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma p8_tolower_0 : SegModel.tolower 0 = 0.
Proof. reflexivity. Qed.

(** SegModel.strcasecmp of two NUL-free byte strings is 0 exactly when their folds are equal, for any fold f that is
    SegModel.tolower on a byte. *)
Lemma p8_sc_zero : forall (f : Z -> Z), (forall c, 0 <= c < 256 -> f c = SegModel.tolower c) ->
  forall L R, p8_byte_vals L -> p8_byte_vals R ->
  (SegModel.strcasecmp L R = 0 <-> map f L = map f R).
Proof.
  intros f Hf. induction L as [|a L IH]; intros R HL HR; destruct R as [|b R];
    cbn [SegModel.strcasecmp map SegModel.hd0].
  - split; intros; reflexivity.
  - assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    pose proof (p8_tolower_pos b Hb) as Pb. rewrite p8_tolower_0.
    split; intros H; [exfalso; lia | discriminate H].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    pose proof (p8_tolower_pos a Ha) as Pa. rewrite p8_tolower_0.
    split; intros H; [exfalso; lia | discriminate H].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    assert (HL' : p8_byte_vals L) by (intros x Hx; apply HL; right; exact Hx).
    assert (HR' : p8_byte_vals R) by (intros x Hx; apply HR; right; exact Hx).
    rewrite (Hf a), (Hf b) by lia.
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
    destruct (Z.eqb_spec (SegModel.tolower a) (SegModel.tolower b)) as [E|E].
    + rewrite orb_true_r. rewrite (IH R HL' HR'). rewrite E.
      split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
    + assert (Eab : (a =? b) = false) by (apply Z.eqb_neq; intros ->; apply E; reflexivity).
      rewrite Eab. cbn [orb].
      split; intros H; [exfalso; lia | injection H as H1 _; exfalso; exact (E H1)].
Qed.

Lemma p8_zs_zb : forall l, (forall x, In x l -> 0 <= x < 256) -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [map].
  rewrite IH by (intros y Hy; apply H; right; exact Hy). f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. apply H. left. reflexivity.
Qed.

Lemma p8_bv_lit : forall l, forallb (fun x => (0 <? x) && (x <? 256)) l = true -> p8_byte_vals l.
Proof.
  intros l H x Hx. rewrite forallb_forall in H. specialize (H x Hx).
  apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(** strcasecmp_c's lower_eq (the map of the fold over both strings) of a NUL-free byte string and a literal. *)
Lemma p8_lower_eq : forall (f : Z -> Z), (forall c, 0 <= c < 256 -> f c = SegModel.tolower c) ->
  forall (bs : list byte) lit, ~ In (Z_to_bv 8 0) bs -> p8_byte_vals lit ->
  (map f (map bv_unsigned bs) = map f (map bv_unsigned (map (Z_to_bv 8) lit)) <->
   SegModel.strcasecmp (zs bs) lit = 0).
Proof.
  intros f Hf bs lit Hn Hl.
  rewrite p8_zs_zb by (intros x Hx; pose proof (Hl x Hx); lia).
  rewrite (p8_sc_zero f Hf (zs bs) lit (p8_vals_zs bs Hn) Hl). unfold zs. reflexivity.
Qed.

(** * parse_bool's strcmp with "1" and "0" *)
Lemma p8_strcmp1 : forall val x, ~ In 0 val -> 0 < x -> (strcmp val [x] = 0 <-> val = [x]).
Proof.
  intros val x Hn Hx. destruct val as [|a [|b r]]; cbn [strcmp].
  - split; [intros H; exfalso; lia | intros H; discriminate H].
  - assert (Ha : a <> 0) by (intros ->; apply Hn; left; reflexivity).
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha). cbn [negb].
    destruct (Z.eqb_spec a x) as [->|E]; cbn [andb].
    + split; intros; reflexivity.
    + split; intros H; [exfalso; lia | injection H as H; exfalso; exact (E H)].
  - assert (Ha : a <> 0) by (intros ->; apply Hn; left; reflexivity).
    assert (Hb : b <> 0) by (intros ->; apply Hn; right; left; reflexivity).
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha). cbn [negb].
    destruct (Z.eqb_spec a x) as [->|E]; cbn [andb].
    + split; intros H; [exfalso; exact (Hb H) | discriminate H].
    + split; intros H; [exfalso; lia | injection H as H _; exfalso; exact (E H)].
Qed.

(** * Bytes of a C string *)
Lemma p8_firstn1 : forall {A} (l : list A) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof.
  intros A l. induction l as [|y l IH]; intros i x H; [destruct i; discriminate H|].
  destruct i as [|i]; cbn [nth_error skipn] in *; [injection H as ->; reflexivity|]. exact (IH i x H).
Qed.

Lemma p8_nth_of_error : forall {A} (l : list A) i x d, nth_error l i = Some x -> nth i l d = x.
Proof.
  intros A l. induction l as [|y l IH]; intros i x d H; [destruct i; discriminate H|].
  destruct i as [|i]; cbn [nth_error nth] in *; [injection H as ->; reflexivity|]. exact (IH i x d H).
Qed.

Lemma p8_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(** The byte i (i <= length s: the NUL at i = length s) of the C string s at a. *)
Lemma p8_cstr_byte : forall segs m a s i, cstr_at segs m a s -> (i <= length s)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i s 0)].
Proof.
  intros segs m a s i (bs & sl & B & Hz & Hn & Hsl) Hi.
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  rewrite (bytes_at_ov_read segs m a _ i 1 B) by (rewrite length_app; cbn [length]; lia).
  f_equal. apply p8_firstn1. rewrite <- Hz.
  destruct (Nat.lt_ge_cases i (length bs)) as [L|L].
  - rewrite nth_error_app1 by exact L.
    destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    f_equal. unfold zs. change 0 with (bv_unsigned ZERO). rewrite map_nth.
    rewrite (p8_nth_of_error bs i b ZERO E). symmetry. apply p8_byte_self.
  - rewrite nth_error_app2 by exact L. replace (i - length bs)%nat with 0%nat by lia. cbn [nth_error].
    f_equal. rewrite nth_overflow by (unfold zs; rewrite length_map; lia). reflexivity.
Qed.

Lemma p8_zxb : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hx.
Qed.

(** The values of a C string are bytes. *)
Lemma p8_cstr_vals : forall segs m a s, cstr_at segs m a s -> forall x, In x s -> 0 <= x < 256.
Proof.
  intros segs m a s (bs & sl & _ & Hz & _) x Hx. rewrite <- Hz in Hx. unfold zs in Hx.
  apply in_map_iff in Hx as (b & <- & _). exact (p8_byte_range b).
Qed.

Lemma p8_nth_val : forall s i, (forall x, In x s -> 0 <= x < 256) -> 0 <= nth i s 0 < 256.
Proof.
  intros s i H. destruct (Nat.lt_ge_cases i (length s)) as [L|L].
  - apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

(** * Byte lists and their updates *)
Lemma p8_list_ext : forall {A} (l1 l2 : list A), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros l2 HL H; destruct l2 as [|y l2]; cbn [length] in HL.
  - reflexivity.
  - discriminate HL.
  - discriminate HL.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth_error] in H0. injection H0 as ->.
    f_equal. apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma p8_fld_len : forall (l : list byte) o n, (o + n <= length l)%nat -> length (fld o n l) = n.
Proof. intros l o n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma p8_fld_nth : forall (l : list byte) o n i, (i < n)%nat -> nth_error (fld o n l) i = nth_error l (o + i).
Proof.
  intros l o n i H. unfold fld. rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia].
  apply nth_error_skipn.
Qed.

(** A field apart from the bytes written. *)
Lemma p8_fld_upd_out : forall cs k bs o n, (k + length bs <= length cs)%nat -> (o + n <= length cs)%nat ->
  ((k + length bs <= o)%nat \/ (o + n <= k)%nat) -> fld o n (upd_bytes cs k bs) = fld o n cs.
Proof.
  intros cs k bs o n H1 H2 H3. apply p8_list_ext.
  - rewrite (p8_fld_len (upd_bytes cs k bs)) by (rewrite upd_bytes_length; lia).
    rewrite p8_fld_len by lia. reflexivity.
  - intros i Hi. rewrite p8_fld_len in Hi by (rewrite upd_bytes_length; lia).
    rewrite !p8_fld_nth by lia. rewrite (upd_bytes_nth cs k bs (o + i)) by lia.
    destruct (Nat.leb_spec k (o + i)); destruct (Nat.ltb_spec (o + i) (k + length bs)); cbn [andb];
      try reflexivity; exfalso; lia.
Qed.

(** A field that holds the bytes written. *)
Lemma p8_fld_upd_in : forall cs k bs o n, (o <= k)%nat -> (k + length bs <= o + n)%nat -> (o + n <= length cs)%nat ->
  fld o n (upd_bytes cs k bs) = upd_bytes (fld o n cs) (k - o) bs.
Proof.
  intros cs k bs o n H1 H2 H3. apply p8_list_ext.
  - rewrite p8_fld_len by (rewrite upd_bytes_length; lia).
    rewrite upd_bytes_length by (rewrite p8_fld_len; lia). rewrite p8_fld_len by lia. reflexivity.
  - intros i Hi. rewrite p8_fld_len in Hi by (rewrite upd_bytes_length; lia).
    rewrite (p8_fld_nth (upd_bytes cs k bs)) by lia. rewrite (upd_bytes_nth cs k bs (o + i)) by lia.
    rewrite (upd_bytes_nth (fld o n cs) (k - o) bs i) by (rewrite p8_fld_len; lia).
    rewrite (p8_fld_nth cs) by lia.
    destruct (Nat.leb_spec k (o + i)); destruct (Nat.ltb_spec (o + i) (k + length bs));
      destruct (Nat.leb_spec (k - o) i); destruct (Nat.ltb_spec i (k - o + length bs)); cbn [andb];
      try (exfalso; lia); try reflexivity.
    replace (o + i - k)%nat with (i - (k - o))%nat by lia. reflexivity.
Qed.

(** A field inside the bytes written. *)
Lemma p8_fld_upd_sub : forall cs k bs o n, (k <= o)%nat -> (o + n <= k + length bs)%nat ->
  (k + length bs <= length cs)%nat -> fld o n (upd_bytes cs k bs) = fld (o - k) n bs.
Proof.
  intros cs k bs o n H1 H2 H3. apply p8_list_ext.
  - rewrite p8_fld_len by (rewrite upd_bytes_length; lia). rewrite p8_fld_len by lia. reflexivity.
  - intros i Hi. rewrite p8_fld_len in Hi by (rewrite upd_bytes_length; lia).
    rewrite !p8_fld_nth by lia. rewrite (upd_bytes_nth cs k bs (o + i)) by lia.
    destruct (Nat.leb_spec k (o + i)); destruct (Nat.ltb_spec (o + i) (k + length bs)); cbn [andb];
      try (exfalso; lia).
    f_equal. lia.
Qed.

(** Two adjacent writes are one. *)
Lemma p8_upd_upd : forall cs k b1 b2, (k + length b1 + length b2 <= length cs)%nat ->
  upd_bytes (upd_bytes cs k b1) (k + length b1) b2 = upd_bytes cs k (b1 ++ b2).
Proof.
  intros cs k b1 b2 H. apply p8_list_ext.
  - rewrite (upd_bytes_length (upd_bytes cs k b1)) by (rewrite upd_bytes_length; lia).
    rewrite (upd_bytes_length cs k b1) by lia. rewrite (upd_bytes_length cs k (b1 ++ b2)) by (rewrite length_app; lia).
    reflexivity.
  - intros i Hi.
    rewrite (upd_bytes_length (upd_bytes cs k b1)) in Hi by (rewrite upd_bytes_length; lia).
    rewrite (upd_bytes_length cs k b1) in Hi by lia.
    rewrite (upd_bytes_nth (upd_bytes cs k b1) (k + length b1) b2 i) by (rewrite upd_bytes_length; lia).
    rewrite (upd_bytes_nth cs k b1 i) by lia.
    rewrite (upd_bytes_nth cs k (b1 ++ b2) i) by (rewrite ?length_app; lia).
    rewrite length_app.
    destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + length b1));
      destruct (Nat.leb_spec (k + length b1) i); destruct (Nat.ltb_spec i (k + length b1 + length b2));
      destruct (Nat.ltb_spec i (k + (length b1 + length b2))); cbn [andb];
      try (exfalso; lia); try reflexivity.
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

(** * The ignore stores into seg[gi] (R:278-279) *)
Lemma p8_nth_upd_same : forall {A} (l : list A) i f d, (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A l. induction l as [|x l IH]; intros i f d H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [upd_nth nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma p8_nth_upd_other : forall {A} (l : list A) i j f d, i <> j -> nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros i j f d H; [destruct i; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth]; try reflexivity.
  - exfalso. apply H. reflexivity.
  - apply IH. intros E. apply H. rewrite E. reflexivity.
Qed.

Lemma p8_len_upd : forall {A} (l : list A) i f, length (upd_nth i f l) = length l.
Proof.
  intros A l. induction l as [|x l IH]; intros i f; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [upd_nth length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(** The bytes the two stores write at seg[gi] + 0x18: ignore = b, then ignore_set = 1. *)
Definition p8_ign_bytes (b : bool) : list byte := le4 (Z_to_bv 64 (b2z b)) ++ le4 (Z_to_bv 64 1).

Lemma p8_ign_bytes_len : forall b, length (p8_ign_bytes b) = 8%nat.
Proof. intros b. unfold p8_ign_bytes. rewrite length_app, !length_le4. reflexivity. Qed.

Lemma p8_rseg_ign : forall g f b, rseg_enc g f ->
  rseg_enc (rs_with_ignore b (rs_ignore_file g) g) (upd_bytes f 24 (p8_ign_bytes b)).
Proof.
  intros g f b (HL & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg).
  pose proof (p8_ign_bytes_len b) as LB.
  unfold rseg_enc, fldz in *.
  cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file rs_role_file
       rs_ignore_file rs_seen_gen rs_with_ignore].
  unfold RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE, RS_ROLE_FILE,
    RS_IGNORE_FILE, RS_SEEN_GEN in *.
  split; [rewrite upd_bytes_length; lia|].
  split; [rewrite p8_fld_upd_out by lia; exact Hn|].
  split; [rewrite p8_fld_upd_out by lia; exact Hr|].
  split; [rewrite p8_fld_upd_out by lia; exact Hrs|].
  split; [rewrite p8_fld_upd_sub by lia; destruct b; reflexivity|].
  split; [rewrite p8_fld_upd_sub by lia; destruct b; reflexivity|].
  split; [rewrite p8_fld_upd_out by lia; exact Hm|].
  split; [rewrite p8_fld_upd_out by lia; exact Hms|].
  split; [rewrite p8_fld_upd_out by lia; exact Hmf|].
  split; [rewrite p8_fld_upd_out by lia; exact Hrf|].
  split; [rewrite p8_fld_upd_out by lia; exact Hif|].
  rewrite p8_fld_upd_out by lia. exact Hsg.
Qed.

(** An edit of the bytes [k, k + length B) of seg[gi] (k + length B <= 356) that encodes h of the entry gives the
    rconf_enc of r_upd rc gi h. *)
Lemma p8_rconf_seg : forall rc bs gi (h : rseg -> rseg) k B,
  rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> (k + length B <= 356)%nat ->
  rseg_enc (h (nth gi (rc_seg rc) rseg_d)) (upd_bytes (fld (356 * gi) 356 bs) k B) ->
  rconf_enc (r_upd rc gi h) (upd_bytes bs (356 * gi + k) B).
Proof.
  intros rc bs gi h k B (HL & Hn32 & Hseg & HN & Hr8 & Href & HNR & HRD & HOV & HRE & HG) Hgi HkB HE.
  unfold SEG_C_SIZE in HL.
  unfold rconf_enc, r_upd, r_set_segs, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen] in *.
  rewrite p8_len_upd.
  unfold RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE in *.
  split; [rewrite upd_bytes_length by lia; lia|].
  split; [exact Hn32|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i gi) as [->|Ne].
    - rewrite p8_nth_upd_same by exact Hgi. rewrite p8_fld_upd_in by lia.
      replace (356 * gi + k - 356 * gi)%nat with k by lia. exact HE.
    - rewrite (p8_nth_upd_other _ gi i) by (intros E; apply Ne; symmetry; exact E).
      rewrite p8_fld_upd_out by lia. exact (Hseg i Hi). }
  split; [rewrite p8_fld_upd_out by lia; exact HN|].
  split; [exact Hr8|].
  split; [intros i Hi; rewrite p8_fld_upd_out by lia; exact (Href i Hi)|].
  split; [rewrite p8_fld_upd_out by lia; exact HNR|].
  split; [rewrite p8_fld_upd_out by lia; exact HRD|].
  split; [rewrite p8_fld_upd_out by lia; exact HOV|].
  split; [rewrite p8_fld_upd_out by lia; exact HRE|].
  rewrite p8_fld_upd_out by lia. exact HG.
Qed.

(** The two stores give c's bytes for pf_prov_mid (PIgn b) rc gi. *)
Lemma p8_rconf_ign : forall rc bs gi b, rconf_enc rc bs -> (gi < length (rc_seg rc))%nat ->
  rconf_enc (pf_prov_mid (PIgn b) rc gi) (upd_bytes bs (356 * gi + 24) (p8_ign_bytes b)).
Proof.
  intros rc bs gi b HE Hgi. unfold pf_prov_mid.
  apply p8_rconf_seg; [exact HE | exact Hgi | rewrite p8_ign_bytes_len; lia |].
  cbn [pf_prov_set pf_prov_old].
  destruct HE as (HL & Hn32 & Hseg & _). apply p8_rseg_ign. exact (Hseg gi Hgi).
Qed.

(** * parse_bool's answer from the binary's six tests *)
Lemma p8_pb_yes : forall v, strcasecmp v S_yes = 0 -> parse_bool v = Some true.
Proof. intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity. Qed.

Lemma p8_pb_true : forall v, strcasecmp v S_true = 0 -> parse_bool v = Some true.
Proof.
  intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H).
  destruct (strcasecmp v S_yes =? 0); reflexivity.
Qed.

Lemma p8_pb_one : forall v, strcmp v [49] = 0 -> parse_bool v = Some true.
Proof.
  intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H).
  destruct (strcasecmp v S_yes =? 0), (strcasecmp v S_true =? 0); reflexivity.
Qed.

Lemma p8_pb_false : forall v, strcasecmp v S_yes <> 0 -> strcasecmp v S_true <> 0 -> strcmp v [49] <> 0 ->
  (strcasecmp v S_no = 0 \/ strcasecmp v S_false = 0 \/ strcmp v [48] = 0) -> parse_bool v = Some false.
Proof.
  intros v H1 H2 H3 H4. unfold parse_bool.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3). cbn [orb].
  destruct H4 as [E|[E|E]]; rewrite (proj2 (Z.eqb_eq _ _) E).
  - reflexivity.
  - destruct (strcasecmp v S_no =? 0); reflexivity.
  - destruct (strcasecmp v S_no =? 0), (strcasecmp v S_false =? 0); reflexivity.
Qed.

Lemma p8_pb_none : forall v, strcasecmp v S_yes <> 0 -> strcasecmp v S_true <> 0 -> strcmp v [49] <> 0 ->
  strcasecmp v S_no <> 0 -> strcasecmp v S_false <> 0 -> strcmp v [48] <> 0 -> parse_bool v = None.
Proof.
  intros v H1 H2 H3 H4 H5 H6. unfold parse_bool.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3),
    (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5), (proj2 (Z.eqb_neq _ _) H6).
  reflexivity.
Qed.

(** The binary's `val[0] == x && val[1] == 0` for a NUL-free val. *)
Lemma p8_one_byte : forall val x, ~ In 0 val -> 0 < x -> nth 0 val 0 = x -> (val = [x] <-> nth 1 val 0 = 0).
Proof.
  intros val x Hn Hx H0. destruct val as [|a [|b r]]; cbn [nth] in *.
  - exfalso. lia.
  - subst a. split; intros; reflexivity.
  - assert (Hb : b <> 0) by (intros ->; apply Hn; right; left; reflexivity).
    split; intros H; [discriminate H | exfalso; exact (Hb H)].
Qed.

Lemma p8_len1 : forall val x, 0 < x -> nth 0 val 0 = x -> (1 <= length val)%nat.
Proof. intros val x Hx H. destruct val as [|a r]; cbn [nth length] in *; lia. Qed.

(** * Branch conditions *)
Lemma p8_eqb_t : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma p8_eqb_f : forall x y : word, bv_eqb x y = false -> x <> y.
Proof. intros x y H E. subst y. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.

Lemma p8_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy H. apply (f_equal bv_unsigned) in H. rewrite !unsigned_lit in H by lia. exact H.
Qed.

(** A loaded byte (`lbu`: zxb) against a byte constant. *)
Lemma p8_byte_eq : forall x y, bv_eqb (zxb (Z_to_bv 8 x)) (Z_to_bv 64 y) = true -> 0 <= x < 256 -> 0 <= y < 256 ->
  x = y.
Proof.
  intros x y H Hx Hy. apply p8_eqb_t in H. rewrite p8_zxb in H by exact Hx.
  exact (p8_lit_inj x y ltac:(lia) ltac:(lia) H).
Qed.

Lemma p8_byte_ne : forall x y, bv_eqb (zxb (Z_to_bv 8 x)) (Z_to_bv 64 y) = false -> 0 <= x < 256 -> x <> y.
Proof. intros x y H Hx E. subst y. apply p8_eqb_f in H. rewrite p8_zxb in H by exact Hx. exact (H eq_refl). Qed.

(** UBSan's alignment test `andi a0, a0, 3` on a 4-aligned pointer. *)
Lemma p8_and3 : forall x, 0 <= x < 2 ^ 64 -> x mod 4 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
Proof.
  intros x Hx H4. rewrite unsigned_lit by exact Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2 ^ 2) with 4. rewrite H4. reflexivity.
Qed.

(** * The bytes a store or a call writes *)
Lemma p8_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

Lemma p8_not_out1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H.
  destruct (Z_le_dec a x); destruct (Z_lt_dec x b); [lia | exfalso; apply H; split; [lia | exact I] ..].
Qed.

Lemma p8_out1 : forall a b x, ~ (a <= x < b) -> outside [(a, b)] x.
Proof. intros a b x H. cbn [outside]. split; [exact H | exact I]. Qed.

(** MemNorm's task_mem survives a write of bytes that were present (as the refuse walk states it). *)
Lemma p8_task_mem_munch : forall segs W m m', MemNorm.task_mem segs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd segs m x <> None) -> MemNorm.task_mem segs m'.
Proof.
  intros segs W m m' T MU P x b Hx.
  destruct (p8_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped segs x Hf).
Qed.

Lemma p8_bytes_present : forall segs m a bs (x : word), bytes_at segs m a bs ->
  a <= bv_unsigned x < a + Z.of_nat (length bs) -> mrd segs m x <> None.
Proof.
  intros segs m a bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (bv_unsigned x - a)) ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in E by lia.
  unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. intros C. apply nth_error_None in C. lia.
Qed.

Lemma p8_zb_nonul : forall l, p8_byte_vals l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l H Hin. apply (in_map bv_unsigned) in Hin.
  rewrite p8_zs_zb in Hin by (intros x Hx; pose proof (H x Hx); lia).
  rewrite p8_nul_val in Hin. pose proof (H 0 Hin). lia.
Qed.
