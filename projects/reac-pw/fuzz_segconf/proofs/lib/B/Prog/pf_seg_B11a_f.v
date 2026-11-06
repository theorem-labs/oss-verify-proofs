(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the IMAGE-FREE lemmas of segment B11a
   of reac_segconf_parse_file's walk (S_B11a of lib/B/Prog/pf_pieces.v: the model key, MODEL 0x886d4 -> MISS 0x88a50
   or LOWOUT 0x88c70). No machine state, no executor, no listing. The B11a segment lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_a11a_f.v (commit dffd9f5c1c42, an
   image-A segment lane): the same lemmas with the prefix a11f_ renamed b11f_, Required over image B's kit copy lib/B/YG0f and
   the B contract bases lib/B/Prog/SegPgBase, SegABase; the C-level facts are image-independent (struct offsets of
   seg_spec, SegModel's r_key / r_low / by_token / r_upd), so no number changes.
   - 3. the spine step of the model branch (SegModel.r_key with key = "model");
   - 4. the fold of the value into model low (F + 0x2e0, 24 bytes; R:254-256) and snprintf(cur->model, 24, "%s", low);
   - 5. the catalogue index of a hit is one of the 11 rows;
   - 6. what SegModel.r_upd keeps (length, the other entries, the counters, reading, gen);
   - 7. byte-list surgery: b11f_put bs k p writes p over bs at k, b11f_put3 writes the three model windows of
        c->seg[gi] (model [0x24, +24), model_set [0x3c, +4), model_file [0x40, +96));
   - 8. the record update through the ASan reader: the bytes the two snprintf calls and the `sw` of model_set
        leave in the block c hold r_upd cf gi (rs_with_model m file) (b11f_rconf_model).
   Sections 3, 4 and 5 are the plain walk's image-free helpers (lib/Prog/pf_p7_lemmas.v at commit
   cfdd99183965, the plain parse_file piece lane) as the A file copies them. Lib.Mem's zxb is named by its full path. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** * 3. The spine step of the model branch (SegModel.r_key) *)

Lemma b11f_r_key : forall (rc : rconf) (gi : nat) (nm line key val : list Z) (ln : Z),
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model = 0 ->
  r_key rc (Some gi) nm ln line =
    match by_token (r_low val 0 24) with
    | None => (refuse rc ln F_badmodel [AS nm; AS val; AS known], Some gi, nm)
    | Some _ => (r_upd rc gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)])
                                            (snprintf_s 96 F_s [AS (rc_reading rc)])), Some gi, nm)
    end.
Proof.
  intros rc gi nm line key val ln (ei & Hei & Hk & Hv) Hrole Hmodel.
  subst key val.
  apply Z.eqb_neq in Hrole. apply Z.eqb_eq in Hmodel.
  unfold r_key. rewrite Hei. cbv iota zeta. rewrite Hrole, Hmodel. cbv iota. reflexivity.
Qed.

(** * 4. The fold into low[24] (R:254-256) *)

(** The bytes the loop stores before the NUL: the first min(cap - 1, |val|) bytes of val, folded. *)
Lemma b11f_low_map : forall (v : list Z) (cap : nat), nulfree v -> r_low v 0 cap = map lower (firstn (cap - 1) v).
Proof. intros v cap H. exact (r_low_fold_go cap v 0%nat H). Qed.

Lemma b11f_low_len : forall (v : list Z) (cap : nat), nulfree v ->
  length (r_low v 0 cap) = Nat.min (cap - 1) (length v).
Proof.
  intros v cap H. rewrite (b11f_low_map v cap H), length_map, length_firstn. reflexivity.
Qed.

Lemma b11f_low_nulfree : forall (v : list Z) (cap : nat), nulfree v -> nulfree (r_low v 0 cap).
Proof.
  intros v cap H. rewrite (b11f_low_map v cap H). apply nulfree_map_lower. apply nulfree_firstn. exact H.
Qed.

Lemma b11f_low_byte : forall (v : list Z) (cap : nat), nulfree v -> Forall (fun x => 0 <= x < 256) v ->
  Forall (fun x => 0 <= x < 256) (r_low v 0 cap).
Proof.
  intros v cap H HB. rewrite (b11f_low_map v cap H).
  apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x & <- & Hx).
  assert (Hx2 : 0 <= x < 256).
  { rewrite Forall_forall in HB. apply HB.
    rewrite <- (firstn_skipn (cap - 1) v). apply in_or_app. left. exact Hx. }
  unfold lower. destruct ((65 <=? x) && (x <=? 90)) eqn:E; [|exact Hx2].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma b11f_lower_range : forall x, 0 <= x < 256 -> 0 <= lower x < 256.
Proof.
  intros x Hx. unfold lower. destruct ((65 <=? x) && (x <=? 90)) eqn:E; [|exact Hx].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(** The byte the fold loop stores: `a3 = (b - 'A') <u 26`, `a0 = b + (a3 << 5)` (image A 0x882a4 .. 0x882b0). *)
Lemma b11f_fold_byte : forall x, 0 <= x < 256 ->
  x + Z.shiftl (Z.b2z ((x + -65) mod 18446744073709551616 <? 26)) 5 = lower x.
Proof.
  intros x Hx. unfold lower.
  destruct (Z.leb_spec 65 x) as [H1|H1]; destruct (Z.leb_spec x 90) as [H2|H2]; cbn [andb].
  - rewrite (Z.mod_small (x + -65)) by lia.
    rewrite (proj2 (Z.ltb_lt (x + -65) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 1 5) with 32. lia.
  - rewrite (Z.mod_small (x + -65)) by lia.
    rewrite (proj2 (Z.ltb_ge (x + -65) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 0 5) with 0. lia.
  - rewrite <- (Z.mod_add (x + -65) 1 18446744073709551616) by lia.
    rewrite (Z.mod_small (x + -65 + 1 * 18446744073709551616)) by lia.
    rewrite (proj2 (Z.ltb_ge (x + -65 + 1 * 18446744073709551616) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 0 5) with 0. lia.
  - lia.
Qed.

(** A byte value as a 64-bit register word. *)
Lemma b11f_byte_word : forall x, 0 <= x < 256 ->
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.zxb. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma b11f_unsigned_byte : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(** snprintf(dst, 24, "%s", low) stores low itself (at most 23 bytes, NUL-free). *)
Lemma b11f_snprintf_low : forall (v : list Z), nulfree v -> snprintf_s 24 F_s [AS (r_low v 0 24)] = r_low v 0 24.
Proof.
  intros v H. apply snprintf_s1; [apply b11f_low_nulfree; exact H|].
  rewrite (b11f_low_len v 24%nat H). lia.
Qed.

(** * 5. The catalogue index of a hit is one of the 11 rows *)

Lemma b11f_row_go_lt : forall toks tk i j, row_go toks tk i = Some j -> (i <= j < i + length toks)%nat.
Proof.
  induction toks as [|k r IH]; intros tk i j H; [discriminate|].
  cbn [row_go length] in *.
  destruct ((length k =? length tk)%nat && leqb k tk).
  - injection H as <-. lia.
  - specialize (IH tk (S i) j H). lia.
Qed.

Lemma b11f_by_token_lt : forall tok j, by_token tok = Some j -> (j < 11)%nat.
Proof.
  intros tok j H. unfold by_token, cat_row in H.
  pose proof (b11f_row_go_lt cat_toks (cut_nul tok) 0%nat j H) as HB.
  assert (E : length cat_toks = 11%nat) by (vm_compute; reflexivity). lia.
Qed.

(** * 6. What SegModel.r_upd keeps *)

Lemma b11f_upd_nth_len : forall {A} (i : nat) (f : A -> A) (l : list A), length (upd_nth i f l) = length l.
Proof.
  intros A i f l. revert i. induction l as [|x r IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + change (S (length (upd_nth i f r)) = S (length r)). rewrite IH. reflexivity.
Qed.

Lemma b11f_upd_nth_same : forall {A} (l : list A) (i : nat) (f : A -> A) (d : A),
  (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A l. induction l as [|x r IH]; intros i f d H.
  - cbn [length] in H. lia.
  - destruct i as [|i].
    + reflexivity.
    + change (nth i (upd_nth i f r) d = f (nth i r d)). apply IH. cbn [length] in H. lia.
Qed.

Lemma b11f_upd_nth_other : forall {A} (l : list A) (i j : nat) (f : A -> A) (d : A),
  j <> i -> nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A l. induction l as [|x r IH]; intros i j f d H.
  - destruct i; reflexivity.
  - destruct i as [|i]; destruct j as [|j].
    + exfalso. apply H. reflexivity.
    + reflexivity.
    + reflexivity.
    + change (nth j (upd_nth i f r) d = nth j r d). apply IH. intros E. apply H. rewrite E. reflexivity.
Qed.

Lemma b11f_upd_len : forall rc i f, length (rc_seg (r_upd rc i f)) = length (rc_seg rc).
Proof.
  intros rc i f. change (length (upd_nth i f (rc_seg rc)) = length (rc_seg rc)). apply b11f_upd_nth_len.
Qed.

Lemma b11f_upd_refused : forall rc i f, rc_refused (r_upd rc i f) = rc_refused rc.
Proof. intros rc i f. reflexivity. Qed.

Lemma b11f_upd_overflow : forall rc i f, rc_overflow (r_upd rc i f) = rc_overflow rc.
Proof. intros rc i f. reflexivity. Qed.

Lemma b11f_upd_reading : forall rc i f, rc_reading (r_upd rc i f) = rc_reading rc.
Proof. intros rc i f. reflexivity. Qed.

Lemma b11f_upd_gen : forall rc i f, rc_gen (r_upd rc i f) = rc_gen rc.
Proof. intros rc i f. reflexivity. Qed.

Lemma b11f_cur_ok_upd : forall rc i f j, pf_cur_ok rc (Some j) -> pf_cur_ok (r_upd rc i f) (Some j).
Proof.
  intros rc i f j H. change (j < length (rc_seg rc))%nat in H.
  change (j < length (rc_seg (r_upd rc i f)))%nat. rewrite b11f_upd_len. exact H.
Qed.

Lemma b11f_cnt_upd : forall rc i f k, pf_cnt rc k -> pf_cnt (r_upd rc i f) k.
Proof.
  intros rc i f k H. unfold pf_cnt in *. rewrite b11f_upd_refused, b11f_upd_overflow. exact H.
Qed.

Lemma b11f_nth_upd_same : forall (rc : rconf) (i : nat) (f : rseg -> rseg), (i < length (rc_seg rc))%nat ->
  nth i (rc_seg (r_upd rc i f)) rseg_d = f (nth i (rc_seg rc) rseg_d).
Proof.
  intros rc i f H. change (nth i (upd_nth i f (rc_seg rc)) rseg_d = f (nth i (rc_seg rc) rseg_d)).
  apply b11f_upd_nth_same. exact H.
Qed.

Lemma b11f_nth_upd_other : forall (rc : rconf) (i : nat) (f : rseg -> rseg) (j : nat), j <> i ->
  nth j (rc_seg (r_upd rc i f)) rseg_d = nth j (rc_seg rc) rseg_d.
Proof.
  intros rc i f j H. change (nth j (upd_nth i f (rc_seg rc)) rseg_d = nth j (rc_seg rc) rseg_d).
  apply b11f_upd_nth_other. exact H.
Qed.

(** * 7. Byte-list surgery *)

Lemma b11f_nth_firstn : forall {A} (l : list A) (n i : nat) (d : A), (i < n)%nat ->
  nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x r IH]; intros n i d H.
  - destruct n; destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|].
    change (nth i (firstn n r) d = nth i r d). apply IH. lia.
Qed.

Lemma b11f_nth_skipn : forall {A} (l : list A) (k i : nat) (d : A), nth i (skipn k l) d = nth (k + i)%nat l d.
Proof.
  intros A l. induction l as [|x r IH]; intros k i d.
  - destruct k; destruct i; reflexivity.
  - destruct k as [|k].
    + reflexivity.
    + change (nth i (skipn k r) d = nth (k + i)%nat r d). apply IH.
Qed.

Lemma b11f_list_ext : forall {A} (l l' : list A) (d : A), length l = length l' ->
  (forall n, (n < length l)%nat -> nth n l d = nth n l' d) -> l = l'.
Proof.
  intros A l. induction l as [|x r IH]; intros l' d HL HN.
  - destruct l' as [|y r']; [reflexivity|]. cbn [length] in HL. discriminate HL.
  - destruct l' as [|y r']; [cbn [length] in HL; discriminate HL|].
    cbn [length] in HL.
    assert (E1 : x = y) by exact (HN 0%nat ltac:(cbn [length]; lia)).
    assert (E2 : r = r').
    { apply (IH r' d); [lia|]. intros n Hn. exact (HN (S n) ltac:(cbn [length]; lia)). }
    rewrite E1, E2. reflexivity.
Qed.

(** p written over bs at offset k (the shape of Lib.Mem.upd_bytes). *)
Definition b11f_put (bs : list byte) (k : nat) (p : list byte) : list byte :=
  firstn k bs ++ p ++ skipn (k + length p) bs.

Lemma b11f_put_len : forall (bs : list byte) (k : nat) (p : list byte), (k + length p <= length bs)%nat ->
  length (b11f_put bs k p) = length bs.
Proof.
  intros bs k p H. unfold b11f_put. rewrite !length_app, length_firstn, pfa_len_skipn. lia.
Qed.

Lemma b11f_put_in : forall (bs : list byte) (k : nat) (p : list byte) (i : nat) (d : byte),
  (k + length p <= length bs)%nat -> (k <= i < k + length p)%nat ->
  nth i (b11f_put bs k p) d = nth (i - k)%nat p d.
Proof.
  intros bs k p i d Hl Hi. unfold b11f_put.
  assert (Lf : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma b11f_put_out : forall (bs : list byte) (k : nat) (p : list byte) (i : nat) (d : byte),
  (k + length p <= length bs)%nat -> (i < k \/ k + length p <= i)%nat ->
  nth i (b11f_put bs k p) d = nth i bs d.
Proof.
  intros bs k p i d Hl Hi. unfold b11f_put.
  assert (Lf : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  destruct Hi as [Hi|Hi].
  - rewrite app_nth1 by lia. apply b11f_nth_firstn. exact Hi.
  - rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth2 by lia. rewrite b11f_nth_skipn.
    f_equal; lia.
Qed.

Lemma b11f_fld_nth : forall (l : list byte) (o n i : nat) (d : byte), (i < n)%nat ->
  nth i (seg_spec.fld o n l) d = nth (o + i)%nat l d.
Proof.
  intros l o n i d H. unfold seg_spec.fld. rewrite (b11f_nth_firstn (skipn o l) n i d H).
  apply b11f_nth_skipn.
Qed.

Lemma b11f_fld_len : forall (l : list byte) (o n : nat),
  (length (seg_spec.fld o n l) = Nat.min n (length l - o))%nat.
Proof. intros l o n. unfold seg_spec.fld. rewrite length_firstn, pfa_len_skipn. reflexivity. Qed.

(** A window of bs apart from the written one reads the same after the write. *)
Lemma b11f_fld_put_out : forall (bs : list byte) (k : nat) (p : list byte) (o n : nat),
  (k + length p <= length bs)%nat -> (o + n <= k \/ k + length p <= o)%nat ->
  seg_spec.fld o n (b11f_put bs k p) = seg_spec.fld o n bs.
Proof.
  intros bs k p o n Hl Ho.
  apply (b11f_list_ext _ _ ZB0).
  - rewrite !b11f_fld_len, b11f_put_len by exact Hl. reflexivity.
  - intros i Hi. rewrite b11f_fld_len, b11f_put_len in Hi by exact Hl.
    rewrite !b11f_fld_nth by lia. apply b11f_put_out; [exact Hl | lia].
Qed.

(** The written window reads back the written bytes. *)
Lemma b11f_fld_put_at : forall (bs : list byte) (k : nat) (p : list byte) (n : nat),
  length p = n -> (k + n <= length bs)%nat ->
  seg_spec.fld k n (b11f_put bs k p) = p.
Proof.
  intros bs k p n Ln Hl. subst n.
  apply (b11f_list_ext _ _ ZB0).
  - rewrite b11f_fld_len, b11f_put_len by exact Hl. lia.
  - intros i Hi. rewrite b11f_fld_len, b11f_put_len in Hi by exact Hl.
    rewrite b11f_fld_nth by lia. rewrite b11f_put_in by lia. f_equal; lia.
Qed.

(** A field of a slice is a window of the whole. *)
Lemma b11f_fld_fld : forall (l : list byte) (o a n m : nat), (a + n <= m)%nat ->
  seg_spec.fld a n (seg_spec.fld o m l) = seg_spec.fld (o + a)%nat n l.
Proof.
  intros l o a n m H.
  apply (b11f_list_ext _ _ ZB0).
  - rewrite !b11f_fld_len. lia.
  - intros i Hi. rewrite !b11f_fld_len in Hi.
    rewrite !b11f_fld_nth by lia. f_equal; lia.
Qed.

(** The three model windows of c->seg[gi], at struct offsets 356 gi + 0x24 (model, 24 bytes), + 0x3c (model_set,
    4 bytes) and + 0x40 (model_file, 96 bytes): together the bytes [356 gi + 36, 356 gi + 160). *)
Definition b11f_put3 (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) : list byte :=
  b11f_put (b11f_put (b11f_put bs (356 * gi + 36)%nat f24) (356 * gi + 60)%nat f4) (356 * gi + 64)%nat f96.

Lemma b11f_put3_lens : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  length (b11f_put bs (356 * gi + 36)%nat f24) = length bs /\
  length (b11f_put (b11f_put bs (356 * gi + 36)%nat f24) (356 * gi + 60)%nat f4) = length bs.
Proof.
  intros bs gi f24 f4 f96 H L24 L4 L96.
  assert (E1 : length (b11f_put bs (356 * gi + 36)%nat f24) = length bs) by (apply b11f_put_len; lia).
  split; [exact E1|].
  rewrite b11f_put_len; [exact E1 | lia].
Qed.

Lemma b11f_put3_len : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  length (b11f_put3 bs gi f24 f4 f96) = length bs.
Proof.
  intros bs gi f24 f4 f96 H L24 L4 L96.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3. rewrite b11f_put_len; [exact E2 | lia].
Qed.

Lemma b11f_put3_out : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (i : nat) (d : byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  (i < 356 * gi + 36 \/ 356 * gi + 160 <= i)%nat ->
  nth i (b11f_put3 bs gi f24 f4 f96) d = nth i bs d.
Proof.
  intros bs gi f24 f4 f96 i d H L24 L4 L96 Hi.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_put_out by lia. rewrite b11f_put_out by lia. rewrite b11f_put_out by lia. reflexivity.
Qed.

Lemma b11f_put3_in24 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (i : nat) (d : byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  (356 * gi + 36 <= i < 356 * gi + 60)%nat ->
  nth i (b11f_put3 bs gi f24 f4 f96) d = nth (i - (356 * gi + 36))%nat f24 d.
Proof.
  intros bs gi f24 f4 f96 i d H L24 L4 L96 Hi.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_put_out by lia. rewrite b11f_put_out by lia. rewrite b11f_put_in by lia. reflexivity.
Qed.

Lemma b11f_put3_in4 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (i : nat) (d : byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  (356 * gi + 60 <= i < 356 * gi + 64)%nat ->
  nth i (b11f_put3 bs gi f24 f4 f96) d = nth (i - (356 * gi + 60))%nat f4 d.
Proof.
  intros bs gi f24 f4 f96 i d H L24 L4 L96 Hi.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_put_out by lia. rewrite b11f_put_in by lia. reflexivity.
Qed.

Lemma b11f_put3_in96 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (i : nat) (d : byte),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  (356 * gi + 64 <= i < 356 * gi + 160)%nat ->
  nth i (b11f_put3 bs gi f24 f4 f96) d = nth (i - (356 * gi + 64))%nat f96 d.
Proof.
  intros bs gi f24 f4 f96 i d H L24 L4 L96 Hi.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_put_in by lia. reflexivity.
Qed.

Lemma b11f_put3_fld_out : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (o n : nat),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  (o + n <= 356 * gi + 36 \/ 356 * gi + 160 <= o)%nat ->
  seg_spec.fld o n (b11f_put3 bs gi f24 f4 f96) = seg_spec.fld o n bs.
Proof.
  intros bs gi f24 f4 f96 o n H L24 L4 L96 Ho.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_fld_put_out by lia. rewrite b11f_fld_put_out by lia. rewrite b11f_fld_put_out by lia.
  reflexivity.
Qed.

Lemma b11f_put3_fld24 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (o n : nat),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  o = (356 * gi + 36)%nat -> n = 24%nat ->
  seg_spec.fld o n (b11f_put3 bs gi f24 f4 f96) = f24.
Proof.
  intros bs gi f24 f4 f96 o n H L24 L4 L96 Eo En. subst o n.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_fld_put_out by lia. rewrite b11f_fld_put_out by lia.
  apply b11f_fld_put_at; [exact L24 | lia].
Qed.

Lemma b11f_put3_fld4 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (o n : nat),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  o = (356 * gi + 60)%nat -> n = 4%nat ->
  seg_spec.fld o n (b11f_put3 bs gi f24 f4 f96) = f4.
Proof.
  intros bs gi f24 f4 f96 o n H L24 L4 L96 Eo En. subst o n.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  rewrite b11f_fld_put_out by lia.
  apply b11f_fld_put_at; [exact L4 | lia].
Qed.

Lemma b11f_put3_fld96 : forall (bs : list byte) (gi : nat) (f24 f4 f96 : list byte) (o n : nat),
  (356 * gi + 160 <= length bs)%nat -> length f24 = 24%nat -> length f4 = 4%nat -> length f96 = 96%nat ->
  o = (356 * gi + 64)%nat -> n = 96%nat ->
  seg_spec.fld o n (b11f_put3 bs gi f24 f4 f96) = f96.
Proof.
  intros bs gi f24 f4 f96 o n H L24 L4 L96 Eo En. subst o n.
  destruct (b11f_put3_lens bs gi f24 f4 f96 H L24 L4 L96) as [E1 E2].
  unfold b11f_put3.
  apply b11f_fld_put_at; [exact L96 | lia].
Qed.

(** * 8. The record update through the ASan reader *)

(** The gi-th 356-byte slice after the three windows are written holds rs_with_model m file of the old entry: every
    other field of seg_spec.rseg_enc lies outside [36, 160) and reads the old bytes. *)
Lemma b11f_rseg_model : forall (bs : list byte) (gi : nat) (s : rseg) (m file : list Z)
    (f24 f4 f96 : list byte),
  (356 * gi + 356 <= length bs)%nat ->
  seg_spec.rseg_enc s (seg_spec.fld (356 * gi)%nat 356 bs) ->
  length f24 = 24%nat -> seg_spec.cstr_enc 24 m f24 ->
  length f4 = 4%nat -> seg_spec.flag_enc true f4 ->
  length f96 = 96%nat -> seg_spec.cstr_enc 96 file f96 ->
  seg_spec.rseg_enc (rs_with_model m file s)
    (seg_spec.fld (356 * gi)%nat 356 (b11f_put3 bs gi f24 f4 f96)).
Proof.
  intros bs gi s m file f24 f4 f96 Hl Hs L24 C24 L4 F4 L96 C96.
  assert (ERo : seg_spec.RS_ROLE = 0x10) by reflexivity.
  assert (ERs : seg_spec.RS_ROLE_SET = 0x14) by reflexivity.
  assert (EIg : seg_spec.RS_IGNORE = 0x18) by reflexivity.
  assert (EIs : seg_spec.RS_IGNORE_SET = 0x1c) by reflexivity.
  assert (EMo : seg_spec.RS_MODEL = 0x24) by reflexivity.
  assert (EMs : seg_spec.RS_MODEL_SET = 0x3c) by reflexivity.
  assert (EMf : seg_spec.RS_MODEL_FILE = 0x40) by reflexivity.
  assert (ERf : seg_spec.RS_ROLE_FILE = 0xa0) by reflexivity.
  assert (EIf : seg_spec.RS_IGNORE_FILE = 0x100) by reflexivity.
  assert (ESg : seg_spec.RS_SEEN_GEN = 0x160) by reflexivity.
  (* a field outside [36, 160) of the slice reads the old bytes *)
  assert (Hkeep : forall a n, (a + n <= 36 \/ 160 <= a)%nat -> (a + n <= 356)%nat ->
    seg_spec.fld a n (seg_spec.fld (356 * gi)%nat 356 (b11f_put3 bs gi f24 f4 f96)) =
    seg_spec.fld a n (seg_spec.fld (356 * gi)%nat 356 bs)).
  { intros a n Ha Hn. rewrite !b11f_fld_fld by exact Hn. apply b11f_put3_fld_out; lia. }
  assert (HkeepZ : forall o n : Z, 0 <= o -> 0 <= n -> (o + n <= 36 \/ 160 <= o) -> o + n <= 356 ->
    seg_spec.fldz o n (seg_spec.fld (356 * gi)%nat 356 (b11f_put3 bs gi f24 f4 f96)) =
    seg_spec.fldz o n (seg_spec.fld (356 * gi)%nat 356 bs)).
  { intros o n Ho Hn H1 H2. unfold seg_spec.fldz. apply Hkeep; lia. }
  (* a field of the slice is a window of the whole block *)
  assert (Hat : forall a n, (a + n <= 356)%nat ->
    seg_spec.fld a n (seg_spec.fld (356 * gi)%nat 356 (b11f_put3 bs gi f24 f4 f96)) =
    seg_spec.fld (356 * gi + a)%nat n (b11f_put3 bs gi f24 f4 f96)).
  { intros a n Hn. apply b11f_fld_fld. exact Hn. }
  unfold seg_spec.rseg_enc in Hs |- *.
  destruct Hs as (Ls & Hname & Hrole & Hrs & Hig & Higs & Hmodel & Hms & Hmf & Hrf & Hif & Hsg).
  (* the slice's length *)
  split. { rewrite b11f_fld_len, b11f_put3_len by lia. lia. }
  (* name [0, 16) *)
  split. { rewrite Hkeep by lia. exact Hname. }
  (* role, role_set, ignore, ignore_set [16, 32) *)
  split. { rewrite HkeepZ by lia. exact Hrole. }
  split. { rewrite HkeepZ by lia. exact Hrs. }
  split. { rewrite HkeepZ by lia. exact Hig. }
  split. { rewrite HkeepZ by lia. exact Higs. }
  (* model [36, 60): the first snprintf's 24 bytes *)
  split.
  { unfold seg_spec.fldz. rewrite Hat by lia. rewrite b11f_put3_fld24 by lia. exact C24. }
  (* model_set [60, 64): the `sw` of 1 *)
  split.
  { unfold seg_spec.fldz. rewrite Hat by lia. rewrite b11f_put3_fld4 by lia. exact F4. }
  (* model_file [64, 160): the second snprintf's 96 bytes *)
  split.
  { unfold seg_spec.fldz. rewrite Hat by lia. rewrite b11f_put3_fld96 by lia. exact C96. }
  (* role_file, ignore_file, seen_gen [160, 356) *)
  split. { rewrite HkeepZ by lia. exact Hrf. }
  split. { rewrite HkeepZ by lia. exact Hif. }
  rewrite HkeepZ by lia. exact Hsg.
Qed.

(** What the model branch's hit path leaves in the block c (0x8855c snprintf into cur->model, 0x88578 `sw 1` into
    cur->model_set, 0x88590 snprintf into cur->model_file): every byte outside the three windows is the entry
    reader's, and the three windows hold the two C strings and the flag. *)
Definition b11f_wrote (rd0 rd : reader) (c : Z) (gi : nat) (m file : list Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL <= a
          < seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + 24) ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_SET <= a
          < seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_SET + 4) ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_FILE <= a
          < seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_FILE + 96) ->
     rd a = rd0 a) /\
  (exists f24, length f24 = 24%nat /\
     sa_bytes rd (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL) f24 /\
     seg_spec.cstr_enc 24 m f24) /\
  (exists f4, sa_bytes rd (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_SET) f4 /\
     seg_spec.flag_enc true f4) /\
  (exists f96, length f96 = 96%nat /\
     sa_bytes rd (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_FILE) f96 /\
     seg_spec.cstr_enc 96 file f96).

(** The record update: from sa_rconf at the entry reader and the three writes, sa_rconf of
    r_upd cf gi (rs_with_model m file) at the exit reader. The new byte list is the old one with the three windows
    of the gi-th slice replaced (b11f_put3). gi < 32 follows from rconf_enc (length (rc_seg cf) <= 32), so the
    windows lie below c->n (0x2c80 = 356 * 32) and every conjunct of rconf_enc after the table reads old bytes. *)
Lemma b11f_rconf_model :
  forall (rd0 rd : reader) (c : Z) (cf : SegModel.rconf) (gi : nat) (m file : list Z),
  sa_rconf rd0 c cf -> (gi < length (rc_seg cf))%nat ->
  0 <= c -> c + seg_spec.SEG_C_SIZE <= 2 ^ 64 ->
  b11f_wrote rd0 rd c gi m file ->
  sa_rconf rd c (SegModel.r_upd cf gi (SegModel.rs_with_model m file)).
Proof.
  intros rd0 rd c cf gi m file Hrc Hgi Hc0 Hc1 Hw.
  unfold sa_rconf in Hrc |- *. destruct Hrc as (bs & Hbs & Henc).
  unfold b11f_wrote in Hw.
  destruct Hw as (Hfr & (f24 & L24 & Hb24 & Hc24) & (f4 & Hb4 & Hf4) & (f96 & L96 & Hb96 & Hc96)).
  unfold seg_spec.rconf_enc in Henc.
  destruct Henc as (Hlen & Hn32 & Hseg & Hn & Hr8 & Href & Hnref & Hrefused & Hovf & Hread & Hgen).
  assert (L4 : length f4 = 4%nat).
  { unfold seg_spec.flag_enc in Hf4. rewrite Hf4.
    first [reflexivity | apply OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.length_le4]. }
  assert (Hgi32 : (gi < 32)%nat) by lia.
  assert (EC : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
  assert (Lbs : Z.of_nat (length bs) = 16616) by (rewrite Hlen; exact EC).
  assert (Hbig : (356 * gi + 356 <= length bs)%nat) by lia.
  assert (EA : seg_spec.rseg_addr c gi = c + 356 * Z.of_nat gi) by reflexivity.
  assert (EM : seg_spec.RS_MODEL = 0x24) by reflexivity.
  assert (ES : seg_spec.RS_MODEL_SET = 0x3c) by reflexivity.
  assert (EF : seg_spec.RS_MODEL_FILE = 0x40) by reflexivity.
  exists (b11f_put3 bs gi f24 f4 f96). split.
  - (* the exit reader holds the new bytes *)
    unfold sa_bytes. intros i Hi.
    rewrite b11f_put3_len in Hi by lia.
    assert (Hout : (i < 356 * gi + 36 \/ 356 * gi + 160 <= i)%nat ->
      rd (c + Z.of_nat i) = Some (bv_unsigned (nth i (b11f_put3 bs gi f24 f4 f96) ZB0))).
    { intros Hio. rewrite b11f_put3_out by lia. rewrite (Hfr (c + Z.of_nat i)) by lia. exact (Hbs i Hi). }
    destruct (Nat.ltb_spec i (356 * gi + 36)%nat) as [H1|H1]; [apply Hout; lia|].
    destruct (Nat.ltb_spec i (356 * gi + 60)%nat) as [H2|H2].
    { rewrite b11f_put3_in24 by lia.
      replace (c + Z.of_nat i) with
        (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + Z.of_nat (i - (356 * gi + 36))%nat) by lia.
      exact (Hb24 (i - (356 * gi + 36))%nat ltac:(lia)). }
    destruct (Nat.ltb_spec i (356 * gi + 64)%nat) as [H3|H3].
    { rewrite b11f_put3_in4 by lia.
      replace (c + Z.of_nat i) with
        (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_SET + Z.of_nat (i - (356 * gi + 60))%nat) by lia.
      exact (Hb4 (i - (356 * gi + 60))%nat ltac:(lia)). }
    destruct (Nat.ltb_spec i (356 * gi + 160)%nat) as [H4|H4].
    { rewrite b11f_put3_in96 by lia.
      replace (c + Z.of_nat i) with
        (seg_spec.rseg_addr c gi + seg_spec.RS_MODEL_FILE + Z.of_nat (i - (356 * gi + 64))%nat) by lia.
      exact (Hb96 (i - (356 * gi + 64))%nat ltac:(lia)). }
    apply Hout. lia.
  - (* the new bytes encode the updated record *)
    unfold seg_spec.rconf_enc.
    assert (Hfar : forall o n, 11392 <= Z.of_nat o ->
      seg_spec.fld o n (b11f_put3 bs gi f24 f4 f96) = seg_spec.fld o n bs).
    { intros o n Ho. apply b11f_put3_fld_out; lia. }
    assert (HfarZ : forall o n, 11392 <= o ->
      seg_spec.fldz o n (b11f_put3 bs gi f24 f4 f96) = seg_spec.fldz o n bs).
    { intros o n Ho. unfold seg_spec.fldz. apply Hfar. rewrite Z2Nat.id by lia. exact Ho. }
    assert (ERN : seg_spec.RC_N = 0x2c80) by reflexivity.
    assert (ERF : seg_spec.RC_REFUSAL = 0x2e88) by reflexivity.
    assert (ENR : seg_spec.RC_NREF = 0x34c8) by reflexivity.
    assert (ERD : seg_spec.RC_REFUSED = 0x34cc) by reflexivity.
    assert (EOV : seg_spec.RC_OVERFLOW = 0x34d0) by reflexivity.
    assert (ERE : seg_spec.RC_READING = 0x4080) by reflexivity.
    assert (EGE : seg_spec.RC_GEN = 0x40e0) by reflexivity.
    (* the block's length *)
    split. { rewrite b11f_put3_len by lia. exact Hlen. }
    (* c->n's bound *)
    split. { rewrite b11f_upd_len. exact Hn32. }
    (* the table: entry gi is the new one, every other entry reads its old slice *)
    split.
    { intros i Hi. rewrite b11f_upd_len in Hi.
      destruct (Nat.eq_dec i gi) as [E|Hne].
      - subst i. rewrite b11f_nth_upd_same by exact Hgi.
        apply b11f_rseg_model;
          [exact Hbig | exact (Hseg gi Hgi) | exact L24 | exact Hc24 | exact L4 | exact Hf4 | exact L96
          | exact Hc96].
      - rewrite b11f_nth_upd_other by exact Hne. rewrite b11f_put3_fld_out by lia. exact (Hseg i Hi). }
    (* c->n, the refusals, n_refusals, refused, overflow, reading, gen: all at or above 0x2c80 *)
    split. { rewrite b11f_upd_len. rewrite HfarZ by lia. exact Hn. }
    split. { exact Hr8. }
    split. { intros i Hi. rewrite Hfar by lia. exact (Href i Hi). }
    split. { rewrite HfarZ by lia. exact Hnref. }
    split. { rewrite HfarZ by lia. exact Hrefused. }
    split. { rewrite HfarZ by lia. exact Hovf. }
    split. { rewrite HfarZ by lia. exact Hread. }
    rewrite HfarZ by lia. exact Hgen.
Qed.
