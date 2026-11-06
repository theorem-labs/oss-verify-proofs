(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the pure model and byte-encoding lemmas that segment
   B8b of reac_segconf_parse_file (0x8890c..0x889f8 (image A); S_B8b in lib/B/Prog/pf_pieces.v) uses. The
   B8b segment lane of the image-B G3 walk owner (ported by a sub-lane), 2026-10-30.
   ADAPTED (port) from a working branch's lib/A/Prog/pf_a8b_m.v: module paths lib.A -> lib.B, names
   pfa8b_ -> pb8b_.

   proves no function (kind: model lemma): no instruction is walked here and no machine state is named. The lane's
   rule-24 record is the rule-24 lookup record.

   WHAT IS HERE.
   - The model side of the header step (pf_pieces.pf_seg_step on SegModel.seg_get): the NEW path (no entry has the
     name and n < 32) and the FOUND path (entry i has it), the bound of r_find_go's answer, what refuse keeps, and
     snprintf(dst, n, "%s", s) on a NUL-free s.
   - The byte splices: a reader rd' that differs from rd only on one named range still holds the struct
     reac_segconf, with the model changed in exactly the fields that range holds.
       pb8b_rconf_seengen  the 4 bytes of seg[i].seen_gen (FOUND / NEW: c->seg[i].seen_gen = c->gen);
       pb8b_rconf_newseg   the 356 bytes of seg[n] and the 4 bytes of n (NEW: c->n = n + 1, memset, name);
       pb8b_rconf_ignfile  the string and its NUL at seg[i].ignore_file (PROV2's snprintf; the bytes of the
                            96-byte field after the NUL are kept, and cstr_enc 96 does not fix them);
       pb8b_rconf_prov2    the same, stated from pf_prov_mid (PIgn b) to pf_prov_fin (PIgn b).
     One witness construction serves all of them: the new byte list is the old one with the written bytes
     spliced in (pb8b_splice), and rconf_enc / rseg_enc are conjunctions over disjoint fields, so each field is
     either inside the spliced range (it changed) or outside it (it did not).
   - pb8b_rseg0_enc: 356 bytes that are zero from offset 16 on, with a C string in the first 16, encode rseg0.
   - pb8b_reading_str / pb8b_segname_str: c->reading and c->seg[i].name as sa_str at the struct's reader.

   STRENGTHENED HYPOTHESES (each one forced: the statement without it is false).
   - pb8b_fmt_s, pb8b_snprintf_name16: `~ In 0 s`, since fmt F_s [AS s] = cut_nul s (pb8b_fmt_s_cut).
   - pb8b_rconf_ignfile: `rs_ignore_set (nth i (rc_seg cf) rseg_d) = true` (rs_with_ignore sets ignore_set, and
     only the ignore_file bytes are written), and `Forall (fun z => 0 <= z < 256) fl` (over an abstract reader a
     written value outside [0, 256) has no byte). pb8b_rconf_prov2 derives both. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Local Notation reader := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0f.reader.

(* ======================================= list helpers ======================================= *)
Section gen.
Context {A : Type}.

Lemma pb8b_nth_firstn : forall (l : list A) (n k : nat) (d : A),
  (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros n k d Hk.
  - destruct n; reflexivity.
  - destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|].
    cbn [firstn nth]. apply IH. lia.
Qed.

Lemma pb8b_nth_skipn : forall (l : list A) (a k : nat) (d : A), nth k (skipn a l) d = nth (a + k) l d.
Proof.
  intros l a. revert l. induction a as [|a IH]; intros l k d; [reflexivity|].
  destruct l as [|x l].
  - destruct k; reflexivity.
  - cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma pb8b_in_firstn : forall (n : nat) (l : list A) (x : A), In x (firstn n l) -> In x l.
Proof.
  induction n as [|n IH]; intros l x H; [destruct H|].
  destruct l as [|y l]; [destruct H|]. cbn [firstn In] in H.
  destruct H as [<-|H]; [left; reflexivity | right; exact (IH l x H)].
Qed.

(* bs with the bytes [off, off + length nw) replaced by nw *)
Definition pb8b_splice (off : nat) (nw bs : list A) : list A :=
  firstn off bs ++ nw ++ skipn (off + length nw) bs.

Lemma pb8b_splice_len : forall off nw bs, (off + length nw <= length bs)%nat ->
  length (pb8b_splice off nw bs) = length bs.
Proof.
  intros off nw bs H. unfold pb8b_splice. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma pb8b_splice_nth_out : forall off nw bs j d, (off + length nw <= length bs)%nat ->
  (j < off \/ off + length nw <= j)%nat -> nth j (pb8b_splice off nw bs) d = nth j bs d.
Proof.
  intros off nw bs j d H [Hj|Hj]; unfold pb8b_splice.
  - rewrite app_nth1 by (rewrite length_firstn; lia). apply pb8b_nth_firstn. exact Hj.
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    rewrite app_nth2 by lia. rewrite pb8b_nth_skipn. f_equal; lia.
Qed.

Lemma pb8b_splice_nth_in : forall off nw bs j d, (off + length nw <= length bs)%nat ->
  (off <= j < off + length nw)%nat -> nth j (pb8b_splice off nw bs) d = nth (j - off) nw d.
Proof.
  intros off nw bs j d H Hj. unfold pb8b_splice.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  rewrite app_nth1 by lia. f_equal; lia.
Qed.
End gen.

Lemma pb8b_upd_nth_eq : forall {B} (i : nat) (f : B -> B) (l : list B) (d : B),
  (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros B i f l. revert i. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [upd_nth nth]. apply IH. cbn in Hi. lia.
Qed.

Lemma pb8b_upd_nth_neq : forall {B} (i k : nat) (f : B -> B) (l : list B) (d : B),
  k <> i -> nth k (upd_nth i f l) d = nth k l d.
Proof.
  intros B i k f l. revert i k. induction l as [|x l IH]; intros i k d Hk; [destruct i; reflexivity|].
  destruct i as [|i], k as [|k]; cbn [upd_nth nth]; [lia | reflexivity | reflexivity | apply IH; lia].
Qed.

Lemma pb8b_upd_nth_twice : forall {B} (i : nat) (f g : B -> B) (l : list B),
  upd_nth i g (upd_nth i f l) = upd_nth i (fun x => g (f x)) l.
Proof.
  intros B i f g l. revert i. induction l as [|x l IH]; intros i; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [upd_nth]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma pb8b_in_cut_nul : forall (l : list Z) x, In x (cut_nul l) -> In x l.
Proof.
  induction l as [|y l IH]; intros x H; [destruct H|]. revert H. cbn [cut_nul].
  destruct (y =? 0); intros H; [destruct H|].
  destruct H as [<-|H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma pb8b_nth_map_bv : forall (l : list byte) k, (k < length l)%nat ->
  nth k (map bv_unsigned l) 0 = bv_unsigned (nth k l ZB0).
Proof.
  induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [map nth]. apply IH. cbn in Hk. lia.
Qed.

(* ======================================= fields of a splice ======================================= *)
Lemma pb8b_fld_len : forall a n (bs : list byte), length (fld a n bs) = Nat.min n (length bs - a).
Proof. intros a n bs. unfold fld. rewrite length_firstn, length_skipn. reflexivity. Qed.

Lemma pb8b_fld_nth : forall a n (bs : list byte) k d, (k < n)%nat -> nth k (fld a n bs) d = nth (a + k) bs d.
Proof. intros a n bs k d Hk. unfold fld. rewrite pb8b_nth_firstn by exact Hk. apply pb8b_nth_skipn. Qed.

Lemma pb8b_fld_fld : forall a n b m (bs : list byte), (a + n <= m)%nat -> fld a n (fld b m bs) = fld (b + a) n bs.
Proof.
  intros a n b m bs H. apply (nth_ext _ _ ZERO ZERO).
  - rewrite !pb8b_fld_len. lia.
  - intros k Hk. rewrite !pb8b_fld_len in Hk.
    rewrite pb8b_fld_nth by lia. rewrite pb8b_fld_nth by lia. rewrite pb8b_fld_nth by lia. f_equal; lia.
Qed.

(* a field wholly outside the spliced range is the old field *)
Lemma pb8b_fld_splice_out : forall a n off (nw bs : list byte),
  (off + length nw <= length bs)%nat -> (a + n <= off \/ off + length nw <= a)%nat ->
  fld a n (pb8b_splice off nw bs) = fld a n bs.
Proof.
  intros a n off nw bs H Ha. apply (nth_ext _ _ ZERO ZERO).
  - rewrite !pb8b_fld_len, pb8b_splice_len by exact H. reflexivity.
  - intros k Hk. rewrite pb8b_fld_len, pb8b_splice_len in Hk by exact H.
    rewrite !pb8b_fld_nth by lia. apply pb8b_splice_nth_out; [exact H | lia].
Qed.

(* a field that holds the spliced range is the old field with the same bytes spliced in *)
Lemma pb8b_fld_splice_in : forall a n off o (nw bs : list byte),
  off = (a + o)%nat -> (o + length nw <= n)%nat -> (a + n <= length bs)%nat ->
  fld a n (pb8b_splice off nw bs) = pb8b_splice o nw (fld a n bs).
Proof.
  intros a n off o nw bs -> Ho Hn.
  assert (Lf : length (fld a n bs) = n) by (rewrite pb8b_fld_len; lia).
  assert (H : (a + o + length nw <= length bs)%nat) by lia.
  apply (nth_ext _ _ ZERO ZERO).
  - rewrite pb8b_fld_len, (pb8b_splice_len (a + o)) by exact H.
    rewrite (pb8b_splice_len o) by lia. lia.
  - intros k Hk. rewrite pb8b_fld_len, (pb8b_splice_len (a + o)) in Hk by exact H.
    rewrite pb8b_fld_nth by lia.
    destruct (Nat.lt_ge_cases k o) as [K1|K1];
      [|destruct (Nat.lt_ge_cases k (o + length nw)) as [K2|K2]].
    + rewrite (pb8b_splice_nth_out (a + o)) by lia. rewrite (pb8b_splice_nth_out o) by lia.
      rewrite pb8b_fld_nth by lia. reflexivity.
    + rewrite (pb8b_splice_nth_in (a + o)) by lia. rewrite (pb8b_splice_nth_in o) by lia. f_equal; lia.
    + rewrite (pb8b_splice_nth_out (a + o)) by lia. rewrite (pb8b_splice_nth_out o) by lia.
      rewrite pb8b_fld_nth by lia. reflexivity.
Qed.

(* the spliced range itself reads back as what was spliced *)
Lemma pb8b_fld_splice_self : forall off off' n (nw bs : list byte),
  off' = off -> length nw = n -> (off + n <= length bs)%nat -> fld off' n (pb8b_splice off nw bs) = nw.
Proof.
  intros off off' n nw bs -> <- H. apply (nth_ext _ _ ZERO ZERO).
  - rewrite pb8b_fld_len, pb8b_splice_len by exact H. lia.
  - intros k Hk. rewrite pb8b_fld_len, pb8b_splice_len in Hk by exact H.
    rewrite pb8b_fld_nth by lia. rewrite pb8b_splice_nth_in by lia. f_equal; lia.
Qed.

Lemma pb8b_fld_zero : forall (f : list byte) off n, length f = 356%nat ->
  (forall k, (16 <= k < 356)%nat -> nth k f ZERO = ZERO) -> (16 <= off)%nat -> (off + n <= 356)%nat ->
  fld off n f = repeat ZERO n.
Proof.
  intros f off n Lf Hz Ho Hn. apply (nth_ext _ _ ZERO ZERO).
  - rewrite pb8b_fld_len, repeat_length. lia.
  - intros k Hk. rewrite pb8b_fld_len in Hk. rewrite pb8b_fld_nth by lia. rewrite nth_repeat. apply Hz. lia.
Qed.

(* ======================================= encodings ======================================= *)
Lemma pb8b_u32_len : forall v f, u32_enc v f -> length f = 4%nat.
Proof. intros v f [_ ->]. reflexivity. Qed.

Lemma pb8b_rseg_len : forall s f, rseg_enc s f -> length f = 356%nat.
Proof. intros s f H. exact (proj1 H). Qed.

Lemma pb8b_cstr_len : forall cap s f, cstr_enc cap s f -> length f = cap.
Proof. intros cap s f H. exact (proj1 H). Qed.

(* the bytes of an encoded C string are bytes *)
Lemma pb8b_cstr_rng : forall cap s f, cstr_enc cap s f -> Forall (fun z => 0 <= z < 256) s.
Proof.
  intros cap s f (_ & _ & _ & Hz). apply Forall_forall. intros z Iz.
  assert (I2 : In z (firstn (S (length s)) (zs f))) by (rewrite Hz; apply in_or_app; left; exact Iz).
  apply pb8b_in_firstn in I2. unfold zs in I2. apply in_map_iff in I2. destruct I2 as (bt & <- & _).
  pose proof (bv_unsigned_in_range _ bt) as R. change (bv_modulus 8) with 256 in R. cbv beta. lia.
Qed.

Lemma pb8b_firstn_app_exact : forall {T} (l1 l2 : list T) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
  intros T l1. induction l1 as [|x l1 IH]; intros l2 n ->; [reflexivity|].
  cbn [length app firstn]. f_equal. apply IH. reflexivity.
Qed.

(* a cap-byte field whose first |fl| + 1 bytes are replaced by fl and its NUL holds the C string fl *)
Lemma pb8b_cstr_splice0 : forall cap (g : list byte) fl, length g = cap -> (length fl < cap)%nat -> ~ In 0 fl ->
  Forall (fun z => 0 <= z < 256) fl -> cstr_enc cap fl (pb8b_splice 0 (zb (fl ++ [0])) g).
Proof.
  intros cap g fl Lg Hl Hn Hr.
  assert (Lnw : length (zb (fl ++ [0])) = S (length fl))
    by (unfold zb; rewrite length_map, length_app; cbn [length]; lia).
  assert (Hr0 : Forall (fun z => 0 <= z < 256) (fl ++ [0]))
    by (apply Forall_app; split; [exact Hr | constructor; [cbv beta; lia | constructor]]).
  split; [rewrite pb8b_splice_len by lia; exact Lg|]. split; [exact Hl|]. split; [exact Hn|].
  assert (E : pb8b_splice 0 (zb (fl ++ [0])) g = zb (fl ++ [0]) ++ skipn (length (zb (fl ++ [0]))) g)
    by reflexivity.
  rewrite E. unfold zs. rewrite map_app.
  rewrite pb8b_firstn_app_exact by (rewrite length_map; lia).
  exact (sa_zs_zb _ Hr0).
Qed.

Local Ltac pb8b_rs := unfold RS_ROLE, RS_ROLE_SET, RS_IGNORE, RS_IGNORE_SET, RS_MODEL, RS_MODEL_SET,
  RS_MODEL_FILE, RS_ROLE_FILE, RS_IGNORE_FILE, RS_SEEN_GEN in *; lia.
Local Ltac pb8b_rc := unfold RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN,
  SEG_C_SIZE, rseg_addr, RSEG_SIZE in *; lia.

(* entry s with its seen_gen field (offset 0x160 = 352) rewritten to g *)
Lemma pb8b_rseg_seengen : forall s f g nb, rseg_enc s f -> u32_enc g nb ->
  rseg_enc (rs_with_gen g s) (pb8b_splice 352 nb f).
Proof.
  intros s f g nb Hs Hg. pose proof (pb8b_u32_len _ _ Hg) as Ln.
  destruct Hs as (Lf & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  unfold rseg_enc, fldz in *.
  cbn [rs_with_gen rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file
       rs_role_file rs_ignore_file rs_seen_gen].
  split; [rewrite pb8b_splice_len by lia; exact Lf|].
  do 10 (split; [rewrite pb8b_fld_splice_out; [assumption | lia | pb8b_rs]|]).
  rewrite (pb8b_fld_splice_self 352) by pb8b_rs. exact Hg.
Qed.

(* entry s with the C string fl and its NUL written at ignore_file (offset 0x100 = 256), ignore kept and
   ignore_set already 1 *)
Lemma pb8b_rseg_ignfile : forall s f fl, rseg_enc s f -> rs_ignore_set s = true -> (length fl < 96)%nat ->
  ~ In 0 fl -> Forall (fun z => 0 <= z < 256) fl ->
  rseg_enc (rs_with_ignore (rs_ignore s) fl s) (pb8b_splice 256 (zb (fl ++ [0])) f).
Proof.
  intros s f fl Hs Hset Hl Hn Hr.
  assert (Lnw : length (zb (fl ++ [0])) = S (length fl))
    by (unfold zb; rewrite length_map, length_app; cbn [length]; lia).
  destruct Hs as (Lf & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  rewrite Hset in H5. unfold rseg_enc, fldz in *.
  cbn [rs_with_ignore rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file
       rs_role_file rs_ignore_file rs_seen_gen].
  split; [rewrite pb8b_splice_len by lia; exact Lf|].
  do 9 (split; [rewrite pb8b_fld_splice_out; [assumption | lia | pb8b_rs]|]).
  split.
  { rewrite (pb8b_fld_splice_in (Z.to_nat RS_IGNORE_FILE) (Z.to_nat 96) 256 0) by pb8b_rs.
    exact (pb8b_cstr_splice0 96 _ fl (proj1 H10) Hl Hn Hr). }
  rewrite pb8b_fld_splice_out; [assumption | lia | pb8b_rs].
Qed.

(* the struct with entry i's bytes [o, o + |nb|) replaced: the model changes in entry i only *)
Lemma pb8b_rconf_enc_entry : forall (cf : rconf) (bs : list byte) (i o : nat) (nb : list byte)
  (F : rseg -> rseg),
  rconf_enc cf bs -> (i < length (rc_seg cf))%nat -> (o + length nb <= 356)%nat ->
  (forall f, rseg_enc (nth i (rc_seg cf) rseg_d) f ->
     rseg_enc (F (nth i (rc_seg cf) rseg_d)) (pb8b_splice o nb f)) ->
  rconf_enc (r_upd cf i F) (pb8b_splice (356 * i + o) nb bs).
Proof.
  intros cf bs i o nb F Hc Hi Ho HF.
  destruct Hc as (L & Ls & Hseg & Hn & Lr & Hr & Hnr & Hrf & Hov & Hrd & Hg).
  unfold SEG_C_SIZE in L.
  assert (Lsp : (356 * i + o + length nb <= length bs)%nat) by lia.
  unfold rconf_enc, r_upd, r_set_segs, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
  split; [rewrite pb8b_splice_len by exact Lsp; exact L|].
  split; [rewrite upd_nth_len; exact Ls|].
  split.
  { intros k Hk. rewrite upd_nth_len in Hk. destruct (Nat.eq_dec k i) as [->|Hki].
    - rewrite pb8b_upd_nth_eq by exact Hi.
      rewrite (pb8b_fld_splice_in (356 * i) 356 (356 * i + o) o) by lia.
      apply HF. apply Hseg. exact Hi.
    - rewrite pb8b_upd_nth_neq by exact Hki.
      rewrite pb8b_fld_splice_out by lia. apply Hseg. exact Hk. }
  split; [rewrite upd_nth_len; rewrite pb8b_fld_splice_out by pb8b_rc; exact Hn|].
  split; [exact Lr|].
  split; [intros k Hk; rewrite pb8b_fld_splice_out by pb8b_rc; apply Hr; exact Hk|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; exact Hnr|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; exact Hrf|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; exact Hov|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; exact Hrd|].
  rewrite pb8b_fld_splice_out by pb8b_rc. exact Hg.
Qed.

(* ======================================= readers ======================================= *)
(* the reader holds the spliced list wherever it holds the old one outside the range and nw inside it *)
Lemma pb8b_sa_splice : forall (rd' : reader) (c : Z) (bs nw : list byte) (off : nat) (P : nat -> Prop),
  (off + length nw <= length bs)%nat ->
  (forall j, (j < length bs)%nat -> ~ (off <= j < off + length nw)%nat -> ~ P j ->
     rd' (c + Z.of_nat j) = Some (bv_unsigned (nth j bs ZB0))) ->
  sa_bytes rd' (c + Z.of_nat off) nw ->
  forall j, (j < length bs)%nat -> ~ P j ->
    rd' (c + Z.of_nat j) = Some (bv_unsigned (nth j (pb8b_splice off nw bs) ZB0)).
Proof.
  intros rd' c bs nw off P H Hout Hnw j Hj HP. unfold sa_bytes in Hnw.
  destruct (Nat.lt_ge_cases j off) as [J1|J1];
    [|destruct (Nat.lt_ge_cases j (off + length nw)) as [J2|J2]].
  - rewrite pb8b_splice_nth_out by lia. apply Hout; [exact Hj | lia | exact HP].
  - rewrite pb8b_splice_nth_in by lia.
    replace (c + Z.of_nat j) with (c + Z.of_nat off + Z.of_nat (j - off)) by lia.
    apply Hnw. lia.
  - rewrite pb8b_splice_nth_out by lia. apply Hout; [exact Hj | lia | exact HP].
Qed.

Lemma pb8b_sa_rconf_entry : forall (rd rd' : reader) (c : Z) (cf : rconf) (i o : nat) (nb : list byte)
  (F : rseg -> rseg),
  sa_rconf rd c cf -> (i < length (rc_seg cf))%nat -> 0 <= c -> (o + length nb <= 356)%nat ->
  (forall f, rseg_enc (nth i (rc_seg cf) rseg_d) f ->
     rseg_enc (F (nth i (rc_seg cf) rseg_d)) (pb8b_splice o nb f)) ->
  (forall x, 0 <= x ->
     ~ (rseg_addr c i + Z.of_nat o <= x < rseg_addr c i + Z.of_nat o + Z.of_nat (length nb)) -> rd' x = rd x) ->
  sa_bytes rd' (rseg_addr c i + Z.of_nat o) nb ->
  sa_rconf rd' c (r_upd cf i F).
Proof.
  intros rd rd' c cf i o nb F (bs & Hb & Hc) Hi Hc0 Ho HF Hfr Hnb.
  pose proof Hc as (L & Ls & _). unfold SEG_C_SIZE in L.
  assert (Lsp : (356 * i + o + length nb <= length bs)%nat) by lia.
  exists (pb8b_splice (356 * i + o) nb bs).
  split; [|exact (pb8b_rconf_enc_entry cf bs i o nb F Hc Hi Ho HF)].
  unfold sa_bytes in *. intros j Hj. rewrite pb8b_splice_len in Hj by exact Lsp.
  apply (pb8b_sa_splice rd' c bs nb (356 * i + o) (fun _ => False)); [exact Lsp | | | exact Hj | intros []].
  - intros j' Hj' Hout _. rewrite Hfr; [apply Hb; exact Hj' | lia | unfold rseg_addr, RSEG_SIZE; lia].
  - replace (c + Z.of_nat (356 * i + o)) with (rseg_addr c i + Z.of_nat o) by (unfold rseg_addr, RSEG_SIZE; lia).
    exact Hnb.
Qed.

(* the C string of a cap-byte field at off, with 7 more bytes of the block after the field, is an sa_str *)
Lemma pb8b_cstr_sa_str : forall (rd : reader) (c : Z) (bs : list byte) (off cap : nat) (s : list Z),
  sa_bytes rd c bs -> cstr_enc cap s (fld off cap bs) -> (off + cap + 7 <= length bs)%nat ->
  sa_str rd (c + Z.of_nat off) s.
Proof.
  intros rd c bs off cap s Hb (Lf & Ls & Hn & Hz) Hl.
  unfold sa_str, sa_strz, sa_zs, sa_tail, sa_bytes in *.
  split; [split|].
  - intros k Hk. rewrite length_app in Hk; cbn [length] in Hk.
    rewrite <- Hz. rewrite pb8b_nth_firstn by lia. unfold zs.
    rewrite pb8b_nth_map_bv by lia. rewrite pb8b_fld_nth by lia.
    replace (c + Z.of_nat off + Z.of_nat k) with (c + Z.of_nat (off + k)) by lia.
    apply Hb. lia.
  - exact Hn.
  - intros x Hx. pose proof (Z.mod_pos_bound (c + Z.of_nat off + Z.of_nat (length s)) 8 ltac:(lia)) as M.
    replace x with (c + Z.of_nat (Z.to_nat (x - c))) by lia.
    rewrite Hb by lia. discriminate.
Qed.

(* ======================================= the model side ======================================= *)
(* 1. snprintf's "%s" text *)
Lemma pb8b_fmt_s_cut : forall s : list Z, SegModel.fmt SegModel.F_s [SegModel.AS s] = cut_nul s.
Proof.
  intros s. change (fmt F_s [AS s]) with (arg_s (AS s) ++ fmt [] []).
  cbn [arg_s fmt]. apply app_nil_r.
Qed.

Lemma pb8b_fmt_s : forall s : list Z, ~ In 0 s -> SegModel.fmt SegModel.F_s [SegModel.AS s] = s.
Proof. intros s H. rewrite pb8b_fmt_s_cut. apply cut_nul_id. exact H. Qed.

(* 2. snprintf(dst, n, "%s", s) *)
Lemma pb8b_snprintf_s_gen : forall (n : Z) (s : list Z),
  SegModel.snprintf_s n SegModel.F_s [SegModel.AS s] = firstn (Z.to_nat (n - 1)) (cut_nul s).
Proof. intros n s. unfold snprintf_s. rewrite pb8b_fmt_s_cut. reflexivity. Qed.

Lemma pb8b_snprintf_name16 : forall s, ~ In 0 s -> (length s <= 15)%nat ->
  SegModel.snprintf_s 16 SegModel.F_s [SegModel.AS s] = s.
Proof.
  intros s H L. rewrite pb8b_snprintf_s_gen, cut_nul_id by exact H. apply firstn_all2. lia.
Qed.

Lemma pb8b_snprintf_cap : forall (n : Z) (s : list Z), ~ In 0 s -> Z.of_nat (length s) < n ->
  SegModel.snprintf_s n SegModel.F_s [SegModel.AS s] = s.
Proof.
  intros n s H L. rewrite pb8b_snprintf_s_gen, cut_nul_id by exact H. apply firstn_all2. lia.
Qed.

Lemma pb8b_sn96_len : forall r, (length (snprintf_s 96 F_s [AS r]) < 96)%nat.
Proof. intros r. unfold snprintf_s. rewrite length_firstn. lia. Qed.

Lemma pb8b_sn_nulfree : forall n r, ~ In 0 (snprintf_s n F_s [AS r]).
Proof. intros n r. rewrite pb8b_snprintf_s_gen. exact (nulfree_firstn _ _ (cut_nul_nulfree _)). Qed.

Lemma pb8b_sn_rng : forall n r, Forall (fun z => 0 <= z < 256) r ->
  Forall (fun z => 0 <= z < 256) (snprintf_s n F_s [AS r]).
Proof.
  intros n r H. rewrite pb8b_snprintf_s_gen. rewrite Forall_forall in *. intros z Iz.
  apply H. apply pb8b_in_cut_nul. exact (pb8b_in_firstn _ _ _ Iz).
Qed.

(* 3. seg_get on the NEW path *)
Lemma pb8b_seg_get_new : forall (cf : rconf) (name : list Z),
  r_find_go (rc_seg cf) name 0 = None -> (length (rc_seg cf) < 32)%nat ->
  seg_get cf name =
  (r_set_segs cf (rc_seg cf ++ [rseg0 (snprintf_s 16 F_s [AS name])]), Some (length (rc_seg cf), true)).
Proof.
  intros cf name Hf Hl. unfold seg_get. rewrite Hf.
  destruct (32 <=? length (rc_seg cf))%nat eqn:E; [apply Nat.leb_le in E; lia | reflexivity].
Qed.

(* 4. the header step on the NEW path *)
Lemma pb8b_step_new : forall cf nm name ln,
  r_find_go (rc_seg cf) name 0 = None -> (length (rc_seg cf) < 32)%nat ->
  pf_seg_step cf nm ln name =
  (r_upd (r_set_segs cf (rc_seg cf ++ [rseg0 (snprintf_s 16 F_s [AS name])])) (length (rc_seg cf))
     (rs_with_gen (rc_gen cf)),
   Some (length (rc_seg cf)), snprintf_s 16 F_s [AS name]).
Proof.
  intros cf nm name ln Hf Hl. unfold pf_seg_step. rewrite (pb8b_seg_get_new cf name Hf Hl). reflexivity.
Qed.

(* 5. the header step on the FOUND path *)
Lemma pb8b_step_found : forall cf nm name ln i,
  r_find_go (rc_seg cf) name 0 = Some i ->
  pf_seg_step cf nm ln name =
  (let c2 := if rs_seen_gen (nth i (rc_seg cf) rseg_d) =? rc_gen cf then refuse cf ln F_twice [AS name] else cf in
   (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])).
Proof. intros cf nm name ln i Hf. unfold pf_seg_step, seg_get. rewrite Hf. reflexivity. Qed.

(* 6. the search's answer is an entry *)
Lemma pb8b_find_go_rng : forall segs name k i, r_find_go segs name k = Some i -> (k <= i < k + length segs)%nat.
Proof.
  induction segs as [|s r IH]; intros name k i H; cbn [r_find_go] in H; [discriminate|].
  cbn [length]. revert H. destruct (strcmp (rs_name s) name =? 0); intros H.
  - injection H as <-. lia.
  - apply IH in H. lia.
Qed.

Lemma pb8b_find_lt : forall segs name i, r_find_go segs name 0 = Some i -> (i < length segs)%nat.
Proof. intros segs name i H. apply pb8b_find_go_rng in H. lia. Qed.

(* 7. refuse keeps the entries, gen and reading *)
Lemma pb8b_refuse_seg : forall cf ln f a,
  rc_seg (refuse cf ln f a) = rc_seg cf /\ rc_gen (refuse cf ln f a) = rc_gen cf /\
  rc_reading (refuse cf ln f a) = rc_reading cf.
Proof.
  intros cf ln f a. unfold refuse. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; (split; [|split]); reflexivity.
Qed.

(* ======================================= the byte splices ======================================= *)
(* 8a. seg[i].seen_gen = g (the whole 4-byte field written) *)
Lemma pb8b_rconf_seengen :
  forall (rd rd' : reader) (c : Z) (cf : rconf) (i : nat) (g : Z) (nb : list byte),
  sa_rconf rd c cf -> (i < length (rc_seg cf))%nat -> 0 <= c ->
  seg_spec.u32_enc g nb ->
  (forall x, 0 <= x ->
     ~ (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN <= x < seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN + 4) ->
     rd' x = rd x) ->
  sa_bytes rd' (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN) nb ->
  sa_rconf rd' c (r_upd cf i (rs_with_gen g)).
Proof.
  intros rd rd' c cf i g nb Hs Hi Hc0 Hg Hfr Hnb. pose proof (pb8b_u32_len _ _ Hg) as Ln.
  apply (pb8b_sa_rconf_entry rd rd' c cf i 352 nb (rs_with_gen g) Hs Hi Hc0); [lia | | |].
  - intros f Hf. exact (pb8b_rseg_seengen _ _ _ _ Hf Hg).
  - intros x Hx Hout. apply Hfr; [exact Hx|]. unfold RS_SEEN_GEN. lia.
  - replace (rseg_addr c i + Z.of_nat 352) with (rseg_addr c i + RS_SEEN_GEN) by (unfold RS_SEEN_GEN; lia).
    exact Hnb.
Qed.

(* 8b. a new entry g at seg[n] (all 356 bytes written) and n = n + 1 (all 4 bytes written) *)
Lemma pb8b_rconf_enc_newseg : forall (cf : rconf) (bs : list byte) (g : rseg) (f nb : list byte),
  rconf_enc cf bs -> (length (rc_seg cf) < 32)%nat -> rseg_enc g f ->
  u32_enc (Z.of_nat (length (rc_seg cf)) + 1) nb ->
  rconf_enc (r_set_segs cf (rc_seg cf ++ [g]))
    (pb8b_splice (Z.to_nat RC_N) nb (pb8b_splice (356 * length (rc_seg cf)) f bs)).
Proof.
  intros cf bs g f nb Hc Hn Hg Hnb.
  pose proof (pb8b_rseg_len _ _ Hg) as Lf. pose proof (pb8b_u32_len _ _ Hnb) as Lnb.
  destruct Hc as (L & Ls & Hseg & Hn0 & Lr & Hr & Hnr & Hrf & Hov & Hrd & Hgen).
  unfold SEG_C_SIZE in L.
  assert (L1 : (356 * length (rc_seg cf) + length f <= length bs)%nat) by lia.
  assert (E1 : length (pb8b_splice (356 * length (rc_seg cf)) f bs) = length bs)
    by (apply pb8b_splice_len; exact L1).
  assert (L2 : (Z.to_nat RC_N + length nb <= length (pb8b_splice (356 * length (rc_seg cf)) f bs))%nat)
    by (rewrite E1; unfold RC_N; lia).
  unfold rconf_enc, r_set_segs, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
  split; [rewrite pb8b_splice_len by exact L2; rewrite E1; exact L|].
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros k Hk. rewrite length_app in Hk; cbn [length] in Hk.
    rewrite (pb8b_fld_splice_out (356 * k) 356 (Z.to_nat RC_N)) by pb8b_rc.
    destruct (Nat.lt_ge_cases k (length (rc_seg cf))) as [K|K].
    - rewrite app_nth1 by exact K. rewrite pb8b_fld_splice_out by lia. apply Hseg. exact K.
    - assert (Ek : k = length (rc_seg cf)) by lia. subst k.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite (pb8b_fld_splice_self (356 * length (rc_seg cf))) by lia. exact Hg. }
  split.
  { rewrite (pb8b_fld_splice_self (Z.to_nat RC_N)) by lia.
    replace (Z.of_nat (length (rc_seg cf ++ [g]))) with (Z.of_nat (length (rc_seg cf)) + 1)
      by (rewrite length_app; cbn [length]; lia).
    exact Hnb. }
  split; [exact Lr|].
  split.
  { intros k Hk. rewrite pb8b_fld_splice_out by pb8b_rc. rewrite pb8b_fld_splice_out by pb8b_rc.
    apply Hr. exact Hk. }
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; rewrite pb8b_fld_splice_out by pb8b_rc; exact Hnr|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; rewrite pb8b_fld_splice_out by pb8b_rc; exact Hrf|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; rewrite pb8b_fld_splice_out by pb8b_rc; exact Hov|].
  split; [rewrite pb8b_fld_splice_out by pb8b_rc; rewrite pb8b_fld_splice_out by pb8b_rc; exact Hrd|].
  rewrite pb8b_fld_splice_out by pb8b_rc. rewrite pb8b_fld_splice_out by pb8b_rc. exact Hgen.
Qed.

Lemma pb8b_rconf_newseg :
  forall (rd rd' : reader) (c : Z) (cf : rconf) (g : rseg) (f nb : list byte),
  sa_rconf rd c cf -> (length (rc_seg cf) < 32)%nat -> 0 <= c ->
  seg_spec.rseg_enc g f -> seg_spec.u32_enc (Z.of_nat (length (rc_seg cf)) + 1) nb ->
  (forall x, 0 <= x ->
     ~ (seg_spec.rseg_addr c (length (rc_seg cf)) <= x < seg_spec.rseg_addr c (length (rc_seg cf)) + 356) ->
     ~ (c + seg_spec.RC_N <= x < c + seg_spec.RC_N + 4) -> rd' x = rd x) ->
  sa_bytes rd' (seg_spec.rseg_addr c (length (rc_seg cf))) f ->
  sa_bytes rd' (c + seg_spec.RC_N) nb ->
  sa_rconf rd' c (r_set_segs cf (rc_seg cf ++ [g])).
Proof.
  intros rd rd' c cf g f nb (bs & Hb & Hc) Hn Hc0 Hg Hnb Hfr Hf Hnbb.
  pose proof (pb8b_rseg_len _ _ Hg) as Lf. pose proof (pb8b_u32_len _ _ Hnb) as Lnb.
  pose proof Hc as (L & Ls & _). unfold SEG_C_SIZE in L.
  assert (L1 : (356 * length (rc_seg cf) + length f <= length bs)%nat) by lia.
  assert (E1 : length (pb8b_splice (356 * length (rc_seg cf)) f bs) = length bs)
    by (apply pb8b_splice_len; exact L1).
  assert (L2 : (Z.to_nat RC_N + length nb <= length (pb8b_splice (356 * length (rc_seg cf)) f bs))%nat)
    by (rewrite E1; unfold RC_N; lia).
  exists (pb8b_splice (Z.to_nat RC_N) nb (pb8b_splice (356 * length (rc_seg cf)) f bs)).
  split; [|exact (pb8b_rconf_enc_newseg cf bs g f nb Hc Hn Hg Hnb)].
  unfold sa_bytes in Hb |- *. intros j Hj. rewrite (pb8b_splice_len (Z.to_nat RC_N)), E1 in Hj by exact L2.
  apply (pb8b_sa_splice rd' c _ nb (Z.to_nat RC_N) (fun _ => False));
    [exact L2 | | | rewrite E1; exact Hj | intros []].
  - intros j' Hj' Hout2 _. rewrite E1 in Hj'.
    apply (pb8b_sa_splice rd' c bs f (356 * length (rc_seg cf))
             (fun j => (Z.to_nat RC_N <= j < Z.to_nat RC_N + length nb)%nat));
      [exact L1 | | | exact Hj' | exact Hout2].
    + intros j'' Hj'' Hout1 Hout2'. cbv beta in Hout2'.
      rewrite Hfr; [apply Hb; exact Hj'' | lia | pb8b_rc | pb8b_rc].
    + replace (c + Z.of_nat (356 * length (rc_seg cf))) with (rseg_addr c (length (rc_seg cf))) by pb8b_rc.
      exact Hf.
  - replace (c + Z.of_nat (Z.to_nat RC_N)) with (c + RC_N) by pb8b_rc. exact Hnbb.
Qed.

(* 9. the zeroed entry named nm *)
Lemma pb8b_rseg0_enc : forall (nm : list Z) (f : list byte), length f = 356%nat ->
  (forall k, (16 <= k < 356)%nat -> nth k f seg_spec.ZERO = seg_spec.ZERO) ->
  seg_spec.cstr_enc 16 nm (seg_spec.fld 0 16 f) -> seg_spec.rseg_enc (rseg0 nm) f.
Proof.
  intros nm f Lf Hz Hn. unfold rseg_enc, fldz.
  cbn [rseg0 rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file
       rs_role_file rs_ignore_file rs_seen_gen].
  split; [exact Lf|]. split; [exact Hn|].
  rewrite !pb8b_fld_zero by (first [exact Lf | exact Hz | pb8b_rs]).
  split; [split; [exact u32_enc_zero | lia]|].
  split; [exact flag_enc_false_zero|]. split; [exact flag_enc_false_zero|].
  split; [exact flag_enc_false_zero|].
  split; [exact (cstr_enc_nil_zero 24 ltac:(lia))|].
  split; [exact flag_enc_false_zero|].
  split; [exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  exact u32_enc_zero.
Qed.

(* 10. the C string fl and its NUL written at seg[i].ignore_file; the rest of the 96-byte field kept *)
Lemma pb8b_rconf_ignfile :
  forall (rd rd' : reader) (c : Z) (cf : rconf) (i : nat) (fl : list Z),
  sa_rconf rd c cf -> (i < length (rc_seg cf))%nat ->
  rs_ignore_set (nth i (rc_seg cf) rseg_d) = true -> 0 <= c ->
  (length fl < 96)%nat -> ~ In 0 fl -> Forall (fun z => 0 <= z < 256) fl ->
  (forall x, 0 <= x ->
     ~ (seg_spec.rseg_addr c i + seg_spec.RS_IGNORE_FILE <= x
        < seg_spec.rseg_addr c i + seg_spec.RS_IGNORE_FILE + Z.of_nat (S (length fl))) -> rd' x = rd x) ->
  (forall k, (k <= length fl)%nat ->
     rd' (seg_spec.rseg_addr c i + seg_spec.RS_IGNORE_FILE + Z.of_nat k) = Some (nth k (fl ++ [0]) 0)) ->
  sa_rconf rd' c (r_upd cf i (rs_with_ignore (rs_ignore (nth i (rc_seg cf) rseg_d)) fl)).
Proof.
  intros rd rd' c cf i fl Hs Hi Hset Hc0 Hl Hn Hr Hfr Hw.
  assert (Lnw : length (zb (fl ++ [0])) = S (length fl))
    by (unfold zb; rewrite length_map, length_app; cbn [length]; lia).
  assert (Hr0 : Forall (fun z => 0 <= z < 256) (fl ++ [0]))
    by (apply Forall_app; split; [exact Hr | constructor; [cbv beta; lia | constructor]]).
  apply (pb8b_sa_rconf_entry rd rd' c cf i 256 (zb (fl ++ [0])) _ Hs Hi Hc0); [lia | | |].
  - intros f Hf. exact (pb8b_rseg_ignfile _ _ _ Hf Hset Hl Hn Hr).
  - intros x Hx Hout. apply Hfr; [exact Hx|]. unfold RS_IGNORE_FILE. lia.
  - unfold sa_bytes. intros k Hk. rewrite Lnw in Hk.
    replace (rseg_addr c i + Z.of_nat 256 + Z.of_nat k) with (rseg_addr c i + RS_IGNORE_FILE + Z.of_nat k)
      by (unfold RS_IGNORE_FILE; lia).
    rewrite Hw by lia. f_equal.
    unfold zb, ZB0. rewrite (map_nth (Z_to_bv 8) (fl ++ [0]) 0 k).
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256.
    rewrite Forall_forall in Hr0. apply Hr0. apply nth_In. rewrite length_app. cbn [length]. lia.
Qed.

(* 11. the provenance edit of the ignore branch *)
Lemma pb8b_prov_fin_ign : forall (b : bool) (cf : rconf) (gi : nat),
  pf_prov_fin (PIgn b) cf gi = r_upd cf gi (rs_with_ignore b (snprintf_s 96 F_s [AS (rc_reading cf)])).
Proof. intros b cf gi. reflexivity. Qed.

Lemma pb8b_prov_mid_upd : forall (b : bool) (cf : rconf) (gi : nat) (nf : list Z),
  r_upd (pf_prov_mid (PIgn b) cf gi) gi (rs_with_ignore b nf) = r_upd cf gi (rs_with_ignore b nf).
Proof.
  intros b cf gi nf. unfold pf_prov_mid, r_upd, r_set_segs.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
  rewrite pb8b_upd_nth_twice. reflexivity.
Qed.

Lemma pb8b_prov_mid_fields : forall (b : bool) (cf : rconf) (gi : nat), (gi < length (rc_seg cf))%nat ->
  rc_reading (pf_prov_mid (PIgn b) cf gi) = rc_reading cf /\ rc_gen (pf_prov_mid (PIgn b) cf gi) = rc_gen cf /\
  length (rc_seg (pf_prov_mid (PIgn b) cf gi)) = length (rc_seg cf) /\
  rs_ignore (nth gi (rc_seg (pf_prov_mid (PIgn b) cf gi)) rseg_d) = b.
Proof.
  intros b cf gi Hgi. unfold pf_prov_mid, r_upd, r_set_segs. cbn [rc_seg rc_reading rc_gen].
  split; [reflexivity|]. split; [reflexivity|]. split; [apply upd_nth_len|].
  rewrite pb8b_upd_nth_eq by exact Hgi. reflexivity.
Qed.

Lemma pb8b_prov_mid_ignset : forall (b : bool) (cf : rconf) (gi : nat), (gi < length (rc_seg cf))%nat ->
  rs_ignore_set (nth gi (rc_seg (pf_prov_mid (PIgn b) cf gi)) rseg_d) = true.
Proof.
  intros b cf gi Hgi. unfold pf_prov_mid, r_upd, r_set_segs. cbn [rc_seg].
  rewrite pb8b_upd_nth_eq by exact Hgi. reflexivity.
Qed.

(* ======================================= strings of the struct ======================================= *)
Lemma pb8b_reading_rng : forall (rd : reader) (c : Z) (cf : rconf), sa_rconf rd c cf ->
  Forall (fun z => 0 <= z < 256) (rc_reading cf).
Proof.
  intros rd c cf (bs & _ & Hc). destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  exact (pb8b_cstr_rng _ _ _ Hrd).
Qed.

Lemma pb8b_reading_str : forall (rd : reader) (c : Z) (cf : rconf),
  sa_rconf rd c cf -> 0 <= c -> sa_str rd (c + seg_spec.RC_READING) (rc_reading cf).
Proof.
  intros rd c cf (bs & Hb & Hc) Hc0.
  destruct Hc as (L & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _). unfold SEG_C_SIZE in L. unfold fldz in Hrd.
  replace (c + RC_READING) with (c + Z.of_nat (Z.to_nat RC_READING)) by (unfold RC_READING; lia).
  apply (pb8b_cstr_sa_str rd c bs (Z.to_nat RC_READING) 96); [exact Hb | exact Hrd | unfold RC_READING; lia].
Qed.

Lemma pb8b_segname_str : forall rd c cf i, sa_rconf rd c cf -> (i < length (rc_seg cf))%nat -> 0 <= c ->
  sa_str rd (seg_spec.rseg_addr c i) (rs_name (nth i (rc_seg cf) rseg_d)).
Proof.
  intros rd c cf i (bs & Hb & Hc) Hi Hc0.
  destruct Hc as (L & Ls & Hseg & _). unfold SEG_C_SIZE in L.
  destruct (Hseg i Hi) as (_ & Hn & _).
  rewrite pb8b_fld_fld in Hn by lia.
  replace (rseg_addr c i) with (c + Z.of_nat (356 * i + 0)) by (unfold rseg_addr, RSEG_SIZE; lia).
  apply (pb8b_cstr_sa_str rd c bs (356 * i + 0) 16); [exact Hb | exact Hn | lia].
Qed.

(* PROV2 from pf_prov_mid to pf_prov_fin: snprintf(&c->seg[gi].ignore_file, 0x60, "%s", c->reading) wrote the
   string and its NUL *)
Lemma pb8b_rconf_prov2 :
  forall (rd rd' : reader) (c : Z) (cf : rconf) (gi : nat) (b : bool),
  sa_rconf rd c (pf_prov_mid (PIgn b) cf gi) -> (gi < length (rc_seg cf))%nat -> 0 <= c ->
  (forall x, 0 <= x ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_IGNORE_FILE <= x
        < seg_spec.rseg_addr c gi + seg_spec.RS_IGNORE_FILE
          + Z.of_nat (S (length (snprintf_s 96 F_s [AS (rc_reading cf)])))) -> rd' x = rd x) ->
  (forall k, (k <= length (snprintf_s 96 F_s [AS (rc_reading cf)]))%nat ->
     rd' (seg_spec.rseg_addr c gi + seg_spec.RS_IGNORE_FILE + Z.of_nat k) =
     Some (nth k (snprintf_s 96 F_s [AS (rc_reading cf)] ++ [0]) 0)) ->
  sa_rconf rd' c (pf_prov_fin (PIgn b) cf gi).
Proof.
  intros rd rd' c cf gi b Hs Hgi Hc0 Hfr Hw.
  destruct (pb8b_prov_mid_fields b cf gi Hgi) as (Er & _ & Ll & Hig).
  assert (Hrng : Forall (fun z => 0 <= z < 256) (rc_reading cf))
    by (rewrite <- Er; exact (pb8b_reading_rng rd c _ Hs)).
  assert (Hgi' : (gi < length (rc_seg (pf_prov_mid (PIgn b) cf gi)))%nat) by (rewrite Ll; exact Hgi).
  pose proof (pb8b_rconf_ignfile rd rd' c (pf_prov_mid (PIgn b) cf gi) gi
    (snprintf_s 96 F_s [AS (rc_reading cf)]) Hs Hgi' (pb8b_prov_mid_ignset b cf gi Hgi) Hc0
    (pb8b_sn96_len _) (pb8b_sn_nulfree _ _) (pb8b_sn_rng _ _ Hrng) Hfr Hw) as H.
  rewrite Hig, pb8b_prov_mid_upd in H. rewrite pb8b_prov_fin_ign. exact H.
Qed.
