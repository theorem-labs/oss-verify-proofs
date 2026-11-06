(* reac-pw/fuzz_segconf, image A: the IMAGE-FREE lemmas of segment A12 of reac_segconf_parse_file's walk (the
   ignore key, reac_segconf.c:271-280 with parse_bool R:88-99 inlined; cuts IGN -> RS3 / PROV2, statements in
   lib/A/Prog/pf_pieces.v). No machine state, no image, no binary: every lemma is about SegModel's Gallina
   functions, seg_spec's encodings and byte lists.

   The bodies are the plain-build walk owner's file lib/Prog/pf_p8_lemmas.v at commit cfdd99183965, which the
   plain walk lib/Prog/pf_p8.v uses; that file is not on this branch and its machine-state lemmas are stated over
   the plain build's MState, so only its image-free part is carried here, under the names this walk uses:
     [a12_spine]    r_key's ignore branch under H_IGN's premises (pf_p8_lemmas.p8_spine).
     [a12_sc_zero]  SegModel.strcasecmp L R = 0 is "the two folds agree", for any fold that is SegModel.tolower
                    on a byte (p8_sc_zero). The ASan interceptor row 10 (lib/A/Rt/RtSeg.v astrcasecmp_realizes)
                    answers with `map lc (ZS sx ++ [0]) = map lc (ZS sy ++ [0])`, so [a12_sc_nul] strips the
                    common NUL and [a12_sc_of_fold] is the form the walk applies.
     [a12_pb_*]     parse_bool's answer from the six tests the code runs (p8_pb_yes .. p8_pb_none).
     [a12_strcmp1], [a12_one_byte], [a12_len1]  parse_bool's strcmp v "1" / "0" on a NUL-free v.
     [a12_rconf_ign]  the two int stores ignore = b, ignore_set = 1 into seg[gi] give the rconf_enc of
                    pf_prov_mid (PIgn b) rc gi (p8_rconf_ign), with the field lemmas it needs.
   Segment A12's proof, by the G3 walk owner, 2026-10-30. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(** * The spine: r_key's ignore branch *)
Lemma a12_spine : forall rc gi nm ln line ei key val,
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

(** * Byte values *)
Definition a12_byte_vals (L : list Z) : Prop := forall x, In x L -> 0 < x < 256.

Lemma a12_vals_zs : forall l : list byte, ~ In (Z_to_bv 8 0) l -> a12_byte_vals (zs l).
Proof.
  intros l H x Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & Hb). pose proof (StrFun.byte_range b).
  split; [|lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia]. exfalso. apply H.
  replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma a12_nul_free_bytes : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof. intros bs H Hin. apply H. unfold zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

Lemma a12_zs_zb : forall l, (forall x, In x l -> 0 <= x < 256) -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [map].
  rewrite IH by (intros y Hy; apply H; right; exact Hy). f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. apply H. left. reflexivity.
Qed.

Lemma a12_bv_lit : forall l, forallb (fun x => (0 <? x) && (x <? 256)) l = true -> a12_byte_vals l.
Proof.
  intros l H x Hx. rewrite forallb_forall in H. specialize (H x Hx).
  apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma a12_zb_nonul : forall l, a12_byte_vals l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l H Hin. apply (in_map bv_unsigned) in Hin.
  rewrite a12_zs_zb in Hin by (intros x Hx; pose proof (H x Hx); lia).
  cbn in Hin. pose proof (H 0 Hin). lia.
Qed.

Lemma a12_nth_val : forall s i, (forall x, In x s -> 0 <= x < 256) -> 0 <= nth i s 0 < 256.
Proof.
  intros s i H. destruct (Nat.lt_ge_cases i (length s)) as [L|L].
  - apply H. apply nth_In. exact L.
  - rewrite nth_overflow by lia. lia.
Qed.

(** * strcasecmp *)
Lemma a12_tolower_pos : forall x, 0 < x < 256 -> 0 < tolower x.
Proof.
  intros x Hx.
  assert (H : forallb (fun z => 0 <? tolower z) (map Z.of_nat (seq 1 255)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.ltb_lt. apply H. apply in_map_iff. exists (Z.to_nat x).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma a12_tolower_0 : tolower 0 = 0.
Proof. reflexivity. Qed.

(** SegModel.strcasecmp of two NUL-free byte strings is 0 exactly when their folds are equal, for any fold f that
    is SegModel.tolower on a byte. *)
Lemma a12_sc_zero : forall (f : Z -> Z), (forall c, 0 <= c < 256 -> f c = tolower c) ->
  forall L R, a12_byte_vals L -> a12_byte_vals R ->
  (strcasecmp L R = 0 <-> map f L = map f R).
Proof.
  intros f Hf. induction L as [|a L IH]; intros R HL HR; destruct R as [|b R];
    cbn [strcasecmp map hd0].
  - split; intros; reflexivity.
  - assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    pose proof (a12_tolower_pos b Hb) as Pb. rewrite a12_tolower_0.
    split; intros H; [exfalso; lia | discriminate H].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    pose proof (a12_tolower_pos a Ha) as Pa. rewrite a12_tolower_0.
    split; intros H; [exfalso; lia | discriminate H].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    assert (HL' : a12_byte_vals L) by (intros x Hx; apply HL; right; exact Hx).
    assert (HR' : a12_byte_vals R) by (intros x Hx; apply HR; right; exact Hx).
    rewrite (Hf a), (Hf b) by lia.
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
    destruct (Z.eqb_spec (tolower a) (tolower b)) as [E|E].
    + rewrite orb_true_r. rewrite (IH R HL' HR'). rewrite E.
      split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
    + assert (Eab : (a =? b) = false) by (apply Z.eqb_neq; intros ->; apply E; reflexivity).
      rewrite Eab. cbn [orb].
      split; intros H; [exfalso; lia | injection H as H1 _; exfalso; exact (E H1)].
Qed.

(** The interceptor answers over the string WITH its NUL; the common last element drops. *)
Lemma a12_sc_nul : forall (f : Z -> Z) (L R : list Z),
  (map f (L ++ [0]) = map f (R ++ [0]) <-> map f L = map f R).
Proof.
  intros f L R. rewrite !map_app. cbn [map].
  split; [apply app_inj_tail | intros H; rewrite H; reflexivity].
Qed.

(** The form the walk applies at each of the four calls: the wrapper's answer, over the byte lists it names, is
    SegModel.strcasecmp of the two texts. *)
Lemma a12_sc_of_fold : forall (f : Z -> Z), (forall c, 0 <= c < 256 -> f c = tolower c) ->
  forall (bs : list byte) (lit : list Z), ~ In (Z_to_bv 8 0) bs -> a12_byte_vals lit ->
  (map f (zs bs ++ [0]) = map f (map bv_unsigned (map (Z_to_bv 8) lit) ++ [0]) <->
   strcasecmp (zs bs) lit = 0).
Proof.
  intros f Hf bs lit Hn Hl.
  rewrite a12_zs_zb by (intros x Hx; pose proof (Hl x Hx); lia).
  rewrite (a12_sc_nul f (zs bs) lit).
  symmetry. exact (a12_sc_zero f Hf (zs bs) lit (a12_vals_zs bs Hn) Hl).
Qed.

(** * parse_bool's strcmp with "1" and "0" *)
Lemma a12_strcmp1 : forall val x, ~ In 0 val -> 0 < x -> (strcmp val [x] = 0 <-> val = [x]).
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

(** The binary's `val[0] == x && val[1] == 0` for a NUL-free val. *)
Lemma a12_one_byte : forall val x, ~ In 0 val -> 0 < x -> nth 0 val 0 = x -> (val = [x] <-> nth 1 val 0 = 0).
Proof.
  intros val x Hn Hx H0. destruct val as [|a [|b r]]; cbn [nth] in *.
  - exfalso. lia.
  - split; [intros _; reflexivity | intros _; rewrite H0; reflexivity].
  - assert (Hb : b <> 0) by (intros ->; apply Hn; right; left; reflexivity).
    split; [intros H; discriminate H | intros H; exfalso; exact (Hb H)].
Qed.

Lemma a12_len1 : forall val x, 0 < x -> nth 0 val 0 = x -> (1 <= length val)%nat.
Proof. intros val x Hx H. destruct val as [|a r]; cbn [nth length] in *; lia. Qed.

(** * parse_bool's answer from the binary's six tests *)
Lemma a12_pb_yes : forall v, strcasecmp v S_yes = 0 -> parse_bool v = Some true.
Proof. intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity. Qed.

Lemma a12_pb_true : forall v, strcasecmp v S_true = 0 -> parse_bool v = Some true.
Proof.
  intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H).
  destruct (strcasecmp v S_yes =? 0); reflexivity.
Qed.

Lemma a12_pb_one : forall v, strcmp v [49] = 0 -> parse_bool v = Some true.
Proof.
  intros v H. unfold parse_bool. rewrite (proj2 (Z.eqb_eq _ _) H).
  destruct (strcasecmp v S_yes =? 0), (strcasecmp v S_true =? 0); reflexivity.
Qed.

Lemma a12_pb_false : forall v, strcasecmp v S_yes <> 0 -> strcasecmp v S_true <> 0 -> strcmp v [49] <> 0 ->
  (strcasecmp v S_no = 0 \/ strcasecmp v S_false = 0 \/ strcmp v [48] = 0) -> parse_bool v = Some false.
Proof.
  intros v H1 H2 H3 H4. unfold parse_bool.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3).
  cbn [orb].
  destruct H4 as [H|[H|H]]; rewrite (proj2 (Z.eqb_eq _ _) H);
    [reflexivity | destruct (strcasecmp v S_no =? 0); reflexivity
    | destruct (strcasecmp v S_no =? 0), (strcasecmp v S_false =? 0); reflexivity].
Qed.

Lemma a12_pb_none : forall v, strcasecmp v S_yes <> 0 -> strcasecmp v S_true <> 0 -> strcmp v [49] <> 0 ->
  strcasecmp v S_no <> 0 -> strcasecmp v S_false <> 0 -> strcmp v [48] <> 0 -> parse_bool v = None.
Proof.
  intros v H1 H2 H3 H4 H5 H6. unfold parse_bool.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3),
    (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5), (proj2 (Z.eqb_neq _ _) H6).
  reflexivity.
Qed.

(** * Branch conditions, as the executor leaves them *)
Lemma a12_eqb_t : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma a12_eqb_f : forall x y : word, bv_eqb x y = false -> x <> y.
Proof. intros x y H E. subst y. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.

Lemma a12_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy H. apply (f_equal bv_unsigned) in H. rewrite !unsigned_lit in H by lia. exact H.
Qed.

Lemma a12_zxb : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hx.
Qed.

Lemma a12_byte_eq : forall x y, bv_eqb (zxb (Z_to_bv 8 x)) (Z_to_bv 64 y) = true -> 0 <= x < 256 -> 0 <= y < 256 ->
  x = y.
Proof.
  intros x y H Hx Hy. apply a12_eqb_t in H. rewrite a12_zxb in H by exact Hx.
  apply a12_lit_inj; [lia | lia | exact H].
Qed.

Lemma a12_byte_ne : forall x y, bv_eqb (zxb (Z_to_bv 8 x)) (Z_to_bv 64 y) = false -> 0 <= x < 256 -> x <> y.
Proof. intros x y H Hx E. subst y. apply a12_eqb_f in H. rewrite a12_zxb in H by exact Hx. exact (H eq_refl). Qed.

(** * Byte lists and their updates *)
Lemma a12_list_ext : forall {A} (l1 l2 : list A), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros l2 HL H; destruct l2 as [|y l2]; cbn [length] in HL;
    try discriminate HL; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth_error] in H0. injection H0 as ->.
  f_equal. apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma a12_fld_len : forall (l : list byte) o n, (o + n <= length l)%nat -> length (fld o n l) = n.
Proof. intros l o n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma a12_fld_nth : forall (l : list byte) o n i, (i < n)%nat -> nth_error (fld o n l) i = nth_error l (o + i).
Proof.
  intros l o n i H. unfold fld. rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia].
  apply nth_error_skipn.
Qed.

Lemma a12_upd_nth_in : forall cs k bs i, (k + length bs <= length cs)%nat -> (k <= i)%nat ->
  (i < k + length bs)%nat -> nth_error (upd_bytes cs k bs) i = nth_error bs (i - k).
Proof.
  intros cs k bs i HL H1 H2. unfold upd_bytes.
  rewrite nth_error_app2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (Nat.min k (length cs)) with k by lia.
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

Lemma a12_upd_nth_out : forall cs k bs i, (k + length bs <= length cs)%nat ->
  ((i < k)%nat \/ (k + length bs <= i)%nat) -> nth_error (upd_bytes cs k bs) i = nth_error cs i.
Proof.
  intros cs k bs i HL H. unfold upd_bytes. destruct H as [H|H].
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn.
    destruct (Nat.ltb_spec i k); [reflexivity | lia].
  - rewrite nth_error_app2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Nat.min k (length cs)) with k by lia.
    rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma a12_fld_upd_out : forall cs k bs o n, (k + length bs <= length cs)%nat -> (o + n <= length cs)%nat ->
  ((k + length bs <= o)%nat \/ (o + n <= k)%nat) -> fld o n (upd_bytes cs k bs) = fld o n cs.
Proof.
  intros cs k bs o n H1 H2 H3. apply a12_list_ext.
  - rewrite !a12_fld_len; [reflexivity | lia | rewrite upd_bytes_length by lia; lia].
  - intros i Hi. rewrite a12_fld_len in Hi by (rewrite upd_bytes_length by lia; lia).
    rewrite !a12_fld_nth by lia. apply a12_upd_nth_out; [lia | lia].
Qed.

Lemma a12_fld_upd_in : forall cs k bs o n, (o <= k)%nat -> (k + length bs <= o + n)%nat ->
  (o + n <= length cs)%nat -> fld o n (upd_bytes cs k bs) = upd_bytes (fld o n cs) (k - o) bs.
Proof.
  intros cs k bs o n H1 H2 H3. apply a12_list_ext.
  - rewrite a12_fld_len by (rewrite upd_bytes_length by lia; lia).
    rewrite upd_bytes_length by (rewrite a12_fld_len by lia; lia). rewrite a12_fld_len by lia. reflexivity.
  - intros i Hi. rewrite a12_fld_len in Hi by (rewrite upd_bytes_length by lia; lia).
    assert (HLf : (k - o + length bs <= length (fld o n cs))%nat) by (rewrite a12_fld_len by lia; lia).
    rewrite (a12_fld_nth (upd_bytes cs k bs) o n i Hi).
    destruct (Nat.lt_ge_cases i (k - o)) as [Hlt|Hge].
    + rewrite (a12_upd_nth_out (fld o n cs) (k - o) bs i HLf (or_introl Hlt)).
      rewrite (a12_fld_nth cs o n i Hi).
      rewrite (a12_upd_nth_out cs k bs (o + i) ltac:(lia) ltac:(left; lia)). reflexivity.
    + destruct (Nat.lt_ge_cases i (k - o + length bs)) as [Hin|Hout].
      * rewrite (a12_upd_nth_in (fld o n cs) (k - o) bs i HLf Hge Hin).
        rewrite (a12_upd_nth_in cs k bs (o + i) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
      * rewrite (a12_upd_nth_out (fld o n cs) (k - o) bs i HLf (or_intror Hout)).
        rewrite (a12_fld_nth cs o n i Hi).
        rewrite (a12_upd_nth_out cs k bs (o + i) ltac:(lia) ltac:(right; lia)). reflexivity.
Qed.

Lemma a12_fld_upd_sub : forall cs k bs o n, (k <= o)%nat -> (o + n <= k + length bs)%nat ->
  (k + length bs <= length cs)%nat -> fld o n (upd_bytes cs k bs) = fld (o - k) n bs.
Proof.
  intros cs k bs o n H1 H2 H3. apply a12_list_ext.
  - rewrite !a12_fld_len; [reflexivity | lia | rewrite upd_bytes_length by lia; lia].
  - intros i Hi. rewrite a12_fld_len in Hi by (rewrite upd_bytes_length by lia; lia).
    rewrite (a12_fld_nth (upd_bytes cs k bs) o n i Hi).
    rewrite (a12_fld_nth bs (o - k) n i Hi).
    rewrite (a12_upd_nth_in cs k bs (o + i) ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia.
Qed.

Lemma a12_upd_upd : forall cs k b1 b2, (k + length b1 + length b2 <= length cs)%nat ->
  upd_bytes (upd_bytes cs k b1) (k + length b1) b2 = upd_bytes cs k (b1 ++ b2).
Proof.
  intros cs k b1 b2 H. apply a12_list_ext.
  - rewrite !upd_bytes_length; [reflexivity | rewrite length_app; lia | lia | rewrite upd_bytes_length by lia; lia].
  - intros i Hi. rewrite upd_bytes_length in Hi by (rewrite upd_bytes_length by lia; lia).
    assert (HL1 : (k + length b1 <= length cs)%nat) by lia.
    assert (HL2 : (k + length b1 + length b2 <= length (upd_bytes cs k b1))%nat)
      by (rewrite upd_bytes_length by lia; lia).
    assert (HL3 : (k + length (b1 ++ b2) <= length cs)%nat) by (rewrite length_app; lia).
    destruct (Nat.lt_ge_cases i k) as [H1|H1].
    + rewrite (a12_upd_nth_out (upd_bytes cs k b1) (k + length b1) b2 i HL2 ltac:(left; lia)).
      rewrite (a12_upd_nth_out cs k b1 i HL1 (or_introl H1)).
      rewrite (a12_upd_nth_out cs k (b1 ++ b2) i HL3 (or_introl H1)). reflexivity.
    + destruct (Nat.lt_ge_cases i (k + length b1)) as [H2|H2].
      * rewrite (a12_upd_nth_out (upd_bytes cs k b1) (k + length b1) b2 i HL2 (or_introl H2)).
        rewrite (a12_upd_nth_in cs k b1 i HL1 H1 H2).
        rewrite (a12_upd_nth_in cs k (b1 ++ b2) i HL3 H1 ltac:(rewrite length_app; lia)).
        rewrite nth_error_app1 by lia. reflexivity.
      * destruct (Nat.lt_ge_cases i (k + length b1 + length b2)) as [H3|H3].
        -- rewrite (a12_upd_nth_in (upd_bytes cs k b1) (k + length b1) b2 i HL2 H2 ltac:(lia)).
           rewrite (a12_upd_nth_in cs k (b1 ++ b2) i HL3 ltac:(lia) ltac:(rewrite length_app; lia)).
           rewrite nth_error_app2 by lia. f_equal. lia.
        -- rewrite (a12_upd_nth_out (upd_bytes cs k b1) (k + length b1) b2 i HL2 ltac:(right; lia)).
           rewrite (a12_upd_nth_out cs k b1 i HL1 ltac:(right; lia)).
           rewrite (a12_upd_nth_out cs k (b1 ++ b2) i HL3 ltac:(right; rewrite length_app; lia)).
           reflexivity.
Qed.

(** * The ignore stores into seg[gi] (R:278-279) *)
Lemma a12_nth_upd_same : forall {A} (l : list A) i f d, (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A l. induction l as [|x l IH]; intros i f d H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [upd_nth nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma a12_nth_upd_other : forall {A} (l : list A) i j f d, i <> j -> nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros i j f d H; [destruct i; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth]; try reflexivity.
  - exfalso. apply H. reflexivity.
  - apply IH. intros E. apply H. rewrite E. reflexivity.
Qed.

Lemma a12_len_upd : forall {A} (l : list A) i f, length (upd_nth i f l) = length l.
Proof.
  intros A l. induction l as [|x l IH]; intros i f; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [upd_nth length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(** The bytes the two stores write at seg[gi] + 0x18: ignore = b, then ignore_set = 1. *)
Definition a12_ign_bytes (b : bool) : list byte := le4 (Z_to_bv 64 (b2z b)) ++ le4 (Z_to_bv 64 1).

Lemma a12_ign_bytes_len : forall b, length (a12_ign_bytes b) = 8%nat.
Proof. intros b. unfold a12_ign_bytes. rewrite length_app, !length_le4. reflexivity. Qed.

Lemma a12_rseg_ign : forall g f b, rseg_enc g f ->
  rseg_enc (rs_with_ignore b (rs_ignore_file g) g) (upd_bytes f 24 (a12_ign_bytes b)).
Proof.
  intros g f b (HL & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg).
  pose proof (a12_ign_bytes_len b) as LB.
  unfold rseg_enc, fldz in *.
  cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file rs_role_file
       rs_ignore_file rs_seen_gen rs_with_ignore].
  unfold RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET, RS_MODEL_FILE, RS_ROLE_FILE,
    RS_IGNORE_FILE, RS_SEEN_GEN in *.
  split; [rewrite upd_bytes_length; lia|].
  split; [rewrite a12_fld_upd_out by lia; exact Hn|].
  split; [rewrite a12_fld_upd_out by lia; exact Hr|].
  split; [rewrite a12_fld_upd_out by lia; exact Hrs|].
  split; [rewrite a12_fld_upd_sub by lia; destruct b; reflexivity|].
  split; [rewrite a12_fld_upd_sub by lia; destruct b; reflexivity|].
  split; [rewrite a12_fld_upd_out by lia; exact Hm|].
  split; [rewrite a12_fld_upd_out by lia; exact Hms|].
  split; [rewrite a12_fld_upd_out by lia; exact Hmf|].
  split; [rewrite a12_fld_upd_out by lia; exact Hrf|].
  split; [rewrite a12_fld_upd_out by lia; exact Hif|].
  rewrite a12_fld_upd_out by lia. exact Hsg.
Qed.

(** An edit of the bytes [k, k + length B) of seg[gi] (k + length B <= 356) that encodes h of the entry gives the
    rconf_enc of r_upd rc gi h. *)
Lemma a12_rconf_seg : forall rc bs gi (h : rseg -> rseg) k B,
  rconf_enc rc bs -> (gi < length (rc_seg rc))%nat -> (k + length B <= 356)%nat ->
  rseg_enc (h (nth gi (rc_seg rc) rseg_d)) (upd_bytes (fld (356 * gi) 356 bs) k B) ->
  rconf_enc (r_upd rc gi h) (upd_bytes bs (356 * gi + k) B).
Proof.
  intros rc bs gi h k B (HL & Hn32 & Hseg & HN & Hr8 & Href & HNR & HRD & HOV & HRE & HG) Hgi HkB HE.
  unfold SEG_C_SIZE in HL.
  unfold rconf_enc, r_upd, r_set_segs, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen] in *.
  rewrite a12_len_upd.
  unfold RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE in *.
  split; [rewrite upd_bytes_length by lia; lia|].
  split; [exact Hn32|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i gi) as [->|Ne].
    - rewrite a12_nth_upd_same by exact Hgi. rewrite a12_fld_upd_in by lia.
      replace (356 * gi + k - 356 * gi)%nat with k by lia. exact HE.
    - rewrite (a12_nth_upd_other _ gi i) by (intros E; apply Ne; symmetry; exact E).
      rewrite a12_fld_upd_out by lia. exact (Hseg i Hi). }
  split; [rewrite a12_fld_upd_out by lia; exact HN|].
  split; [exact Hr8|].
  split; [intros i Hi; rewrite a12_fld_upd_out by lia; exact (Href i Hi)|].
  split; [rewrite a12_fld_upd_out by lia; exact HNR|].
  split; [rewrite a12_fld_upd_out by lia; exact HRD|].
  split; [rewrite a12_fld_upd_out by lia; exact HOV|].
  split; [rewrite a12_fld_upd_out by lia; exact HRE|].
  rewrite a12_fld_upd_out by lia. exact HG.
Qed.

(** The two stores give c's bytes for pf_prov_mid (PIgn b) rc gi. *)
Lemma a12_rconf_ign : forall rc bs gi b, rconf_enc rc bs -> (gi < length (rc_seg rc))%nat ->
  rconf_enc (pf_prov_mid (PIgn b) rc gi) (upd_bytes bs (356 * gi + 24) (a12_ign_bytes b)).
Proof.
  intros rc bs gi b HE Hgi. unfold pf_prov_mid.
  apply a12_rconf_seg; [exact HE | exact Hgi | rewrite a12_ign_bytes_len; lia |].
  cbn [pf_prov_set pf_prov_old].
  destruct HE as (HL & Hn32 & Hseg & _). apply a12_rseg_ign. exact (Hseg gi Hgi).
Qed.
