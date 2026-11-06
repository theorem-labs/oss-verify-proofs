(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput, both builds: the facts the inner walks' inline
   m_cross loop needs (plain 0x13a48..0x13aa8, UBSan
   0x13b9c..0x13c08; fuzz_segconf.c:296-310). Build-independent: Spec/SegModel.v and Prog/seg_spec.v only, the
   memory lemmas over any segment list.
   - The model: the loop after i passes holds fold_left m_cross_seg (seq 0 i) m1 (mx_step), whose table keeps its
     length (mx_len) and whose refused counter grew by at most i (mx_refused).
   - The memory: what a struct mconf holding mc (seg_spec.mconf_at) gives the loop's loads (m->n, and role,
     role_set, model_set of m->seg[i]), and the struct after the loop's `sw zero` stores: model_set = 0 (c:303)
     holds m_upd mc i ms_drop_model, role = 0 then role_set = 0 (c:306-307) hold m_upd mc i ms_drop_role.
   Model and encoding lemmas of a segment walk. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** The model *)
Lemma mx_upd_nth_length : forall {A} i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof. intros A i f l. revert i. induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; auto. Qed.

Lemma mx_upd_nth_nth : forall {A} i j (f : A -> A) l d, (i < length l)%nat ->
  nth j (upd_nth i f l) d = if Nat.eqb j i then f (nth i l d) else nth j l d.
Proof.
  intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Lemma mx_refuse_seg : forall c l k, mc_seg (m_refuse c l k) = mc_seg c.
Proof. reflexivity. Qed.
Lemma mx_refuse_refused : forall c l k, mc_refused (m_refuse c l k) = mc_refused c + 1.
Proof. reflexivity. Qed.
Lemma mx_upd_seg : forall c i f, mc_seg (m_upd c i f) = upd_nth i f (mc_seg c).
Proof. reflexivity. Qed.
Lemma mx_upd_refused : forall c i f, mc_refused (m_upd c i f) = mc_refused c.
Proof. reflexivity. Qed.

(** One pass: nothing, or a refusal and one of the two edits of entry i. *)
Lemma mx_seg_cases : forall c i,
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_model \/
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_role \/ m_cross_seg c i = c.
Proof.
  intros c i. unfold m_cross_seg. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [left; reflexivity|].
  match goal with |- context [if ?b then _ else _] => destruct b end; [right; left; reflexivity|].
  right; right; reflexivity.
Qed.

Lemma mx_seg_len : forall c i, length (mc_seg (m_cross_seg c i)) = length (mc_seg c).
Proof.
  intros c i. destruct (mx_seg_cases c i) as [E|[E|E]]; rewrite E;
    rewrite ?mx_upd_seg, ?mx_upd_nth_length, ?mx_refuse_seg; reflexivity.
Qed.

Lemma mx_seg_refused : forall c i, mc_refused c <= mc_refused (m_cross_seg c i) <= mc_refused c + 1.
Proof.
  intros c i. destruct (mx_seg_cases c i) as [E|[E|E]]; rewrite E;
    rewrite ?mx_upd_refused, ?mx_refuse_refused; lia.
Qed.

Lemma mx_step : forall m1 i,
  fold_left m_cross_seg (seq 0 (S i)) m1 = m_cross_seg (fold_left m_cross_seg (seq 0 i) m1) i.
Proof. intros m1 i. rewrite seq_S, fold_left_app. reflexivity. Qed.

Lemma mx_len : forall m1 i, length (mc_seg (fold_left m_cross_seg (seq 0 i) m1)) = length (mc_seg m1).
Proof. intros m1 i. induction i as [|i IH]; [reflexivity|]. rewrite mx_step, mx_seg_len. exact IH. Qed.

Lemma mx_refused : forall m1 i,
  mc_refused m1 <= mc_refused (fold_left m_cross_seg (seq 0 i) m1) <= mc_refused m1 + Z.of_nat i.
Proof.
  intros m1 i. induction i as [|i IH]; [cbn; lia|].
  rewrite mx_step. pose proof (mx_seg_refused (fold_left m_cross_seg (seq 0 i) m1) i). lia.
Qed.

Lemma mx_all : forall m1, m_cross m1 = fold_left m_cross_seg (seq 0 (length (mc_seg m1))) m1.
Proof. reflexivity. Qed.

(** ** Byte lists: a field of an updated block *)
Lemma mx_nth_upd : forall (bs X : list byte) k j, (k + length X <= length bs)%nat ->
  nth_error (upd_bytes bs k X) j =
    if (Nat.leb k j && Nat.ltb j (k + length X))%bool then nth_error X (j - k) else nth_error bs j.
Proof.
  intros bs X k j H. destruct (Nat.ltb_spec0 j (length bs)) as [L|L].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None (upd_bytes bs k X) j)) by (rewrite upd_bytes_length by assumption; lia).
    rewrite (proj2 (nth_error_None bs j)) by lia.
    destruct (Nat.leb_spec0 k j), (Nat.ltb_spec0 j (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma mx_nth_fld : forall (l : list byte) a n i,
  nth_error (fld a n l) i = if Nat.ltb i n then nth_error l (a + i) else None.
Proof. intros l a n i. unfold fld. rewrite nth_error_firstn, nth_error_skipn. reflexivity. Qed.

Lemma mx_fld_upd_out : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a + n <= k \/ k + length X <= a)%nat ->
  fld a n (upd_bytes bs k X) = fld a n bs.
Proof.
  intros bs X k a n H D. apply nth_error_ext. intros i. rewrite !mx_nth_fld.
  destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (mx_nth_upd bs X k (a + i) H).
  destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma mx_fld_upd_inner : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (k <= a)%nat -> (a + n <= k + length X)%nat ->
  fld a n (upd_bytes bs k X) = fld (a - k) n X.
Proof.
  intros bs X k a n H1 H2 H3. apply nth_error_ext. intros i. rewrite !mx_nth_fld.
  destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (mx_nth_upd bs X k (a + i) H1).
  destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try lia.
  f_equal. lia.
Qed.

Lemma mx_fld_upd_sub : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a <= k)%nat -> (k + length X <= a + n)%nat -> (a + n <= length bs)%nat ->
  fld a n (upd_bytes bs k X) = upd_bytes (fld a n bs) (k - a) X.
Proof.
  intros bs X k a n H1 H2 H3 H4.
  assert (LF : length (fld a n bs) = n) by (unfold fld; rewrite length_firstn, length_skipn; lia).
  apply nth_error_ext. intros i.
  rewrite (mx_nth_upd (fld a n bs) X (k - a) i) by lia.
  rewrite !mx_nth_fld. rewrite (mx_nth_upd bs X k (a + i) H1).
  destruct (Nat.ltb_spec0 i n), (Nat.leb_spec0 (k - a) i), (Nat.ltb_spec0 i (k - a + length X)),
           (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb];
    try (exfalso; lia); try reflexivity.
  f_equal. lia.
Qed.

Lemma mx_upd_upd_adj : forall (bs X Y : list byte) k,
  (k + length X + length Y <= length bs)%nat ->
  upd_bytes (upd_bytes bs k X) (k + length X) Y = upd_bytes bs k (X ++ Y).
Proof.
  intros bs X Y k H.
  assert (L1 : length (upd_bytes bs k X) = length bs) by (apply upd_bytes_length; lia).
  apply nth_error_ext. intros j.
  rewrite (mx_nth_upd (upd_bytes bs k X) Y (k + length X) j) by lia.
  rewrite (mx_nth_upd bs (X ++ Y) k j) by (rewrite length_app; lia).
  rewrite (mx_nth_upd bs X k j) by lia. rewrite length_app.
  destruct (Nat.leb_spec0 (k + length X) j), (Nat.ltb_spec0 j (k + length X + length Y)),
           (Nat.leb_spec0 k j), (Nat.ltb_spec0 j (k + length X)), (Nat.ltb_spec0 j (k + (length X + length Y)));
    cbn [andb]; try (exfalso; lia); try reflexivity.
  - rewrite nth_error_app2 by lia. f_equal. lia.
  - rewrite nth_error_app1 by lia. reflexivity.
Qed.

(** ** The two edits of m->seg[i], on its 256 bytes *)
Definition Z4 : list byte := le4 (Z_to_bv 64 0).

Lemma mx_Z4_len : length Z4 = 4%nat.
Proof. apply length_le4. Qed.

Lemma mx_mseg_drop_model : forall g f, mseg_enc g f -> mseg_enc (ms_drop_model g) (upd_bytes f 32 Z4).
Proof.
  intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
  assert (HL : (32 + length Z4 <= length f)%nat) by (rewrite mx_Z4_len; lia).
  unfold ms_drop_model, mseg_enc, fldz. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
    ms_model ms_role_file ms_ignore_file ms_gen].
  unfold fldz in *. unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
    MS_IGNORE_FILE, MS_GEN in *.
  split; [rewrite upd_bytes_length by exact HL; exact L|].
  rewrite (mx_fld_upd_inner f Z4 32 (Z.to_nat 32) (Z.to_nat 4)) by (rewrite ?mx_Z4_len; lia).
  rewrite !(mx_fld_upd_out f Z4 32) by (rewrite ?mx_Z4_len; lia).
  refine (conj N (conj R (conj RS (conj I (conj IS (conj _ (conj M (conj RF (conj IF G))))))))).
  reflexivity.
Qed.

Lemma mx_mseg_drop_role : forall g f, mseg_enc g f -> mseg_enc (ms_drop_role g) (upd_bytes f 16 (Z4 ++ Z4)).
Proof.
  intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
  assert (HL : (16 + length (Z4 ++ Z4) <= length f)%nat) by (rewrite length_app, mx_Z4_len; lia).
  unfold ms_drop_role, mseg_enc, fldz. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
    ms_model ms_role_file ms_ignore_file ms_gen].
  unfold fldz in *. unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
    MS_IGNORE_FILE, MS_GEN in *.
  split; [rewrite upd_bytes_length by exact HL; exact L|].
  rewrite (mx_fld_upd_inner f (Z4 ++ Z4) 16 (Z.to_nat 16) (Z.to_nat 4)) by (rewrite ?length_app, ?mx_Z4_len; lia).
  rewrite (mx_fld_upd_inner f (Z4 ++ Z4) 16 (Z.to_nat 20) (Z.to_nat 4)) by (rewrite ?length_app, ?mx_Z4_len; lia).
  rewrite !(mx_fld_upd_out f (Z4 ++ Z4) 16) by (rewrite ?length_app, ?mx_Z4_len; lia).
  refine (conj N (conj _ (conj _ (conj I (conj IS (conj MS (conj M (conj RF (conj IF G))))))))).
  - split; [split; [lia | reflexivity] | lia].
  - reflexivity.
Qed.

(** ** The struct: one entry edited in place *)
Lemma mx_mconf_upd : forall mc bs i f X off,
  mconf_enc mc bs -> (i < length (mc_seg mc))%nat -> (off + length X <= 256)%nat ->
  mseg_enc (f (nth i (mc_seg mc) mseg_d)) (upd_bytes (fld (256 * i) 256 bs) off X) ->
  mconf_enc (m_upd mc i f) (upd_bytes bs (256 * i + off) X).
Proof.
  intros mc bs i f X off E Hi HX HG.
  destruct E as (L & LS & SG & N & O & RF & LK & KP & KN & NK & G & RD).
  unfold SEG_M_SIZE in L.
  assert (HB : (256 * i + off + length X <= length bs)%nat) by lia.
  assert (OUT : forall a n, (256 * 32 <= a)%nat -> fld a n (upd_bytes bs (256 * i + off) X) = fld a n bs)
    by (intros a n Ha; apply mx_fld_upd_out; [exact HB | right; lia]).
  unfold mconf_enc, mconf_encp, fldz in *. unfold m_upd, m_set_segs.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  unfold MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING in *.
  rewrite !mx_upd_nth_length.
  split; [rewrite upd_bytes_length by exact HB; exact L|]. split; [exact LS|].
  split.
  { intros j Hj. rewrite (mx_upd_nth_nth i j f (mc_seg mc) mseg_d Hi).
    destruct (Nat.eqb_spec j i) as [->|Ne].
    - rewrite (mx_fld_upd_sub bs X (256 * i + off) (256 * i) 256) by lia.
      replace (256 * i + off - 256 * i)%nat with off by lia. exact HG.
    - rewrite (mx_fld_upd_out bs X (256 * i + off) (256 * j) 256) by lia. apply SG. exact Hj. }
  rewrite !OUT by lia.
  split; [exact N|]. split; [exact O|]. split; [exact RF|]. split; [exact LK|].
  split; [intros j Hj; rewrite !OUT by lia; apply KP; exact Hj|].
  split; [intros j Hj; rewrite !OUT by lia; apply KN; exact Hj|].
  split; [exact NK|]. split; [exact G|exact RD].
Qed.

(** ** In memory *)
Section Mem.
Variable segs : list Segment.

Lemma mx_mconf_len : forall mc bs, mconf_enc mc bs -> Z.of_nat (length bs) = 9236 /\ (length (mc_seg mc) <= 32)%nat.
Proof. intros mc bs (L & LS & _). unfold SEG_M_SIZE in L. split; [exact L | exact LS]. Qed.

(** m->n: the 4 bytes at m + 0x2000. *)
Lemma mx_read_n : forall m a mc, mconf_at segs m a mc ->
  ov_read_bytes segs m (wa (a + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc))))).
Proof.
  intros m a mc (bs & B & E). pose proof (mx_mconf_len mc bs E) as [L _].
  destruct E as (_ & _ & _ & (_ & HN) & _). unfold fldz in HN.
  rewrite (bytes_at_read segs m a bs MC_N 4 B) by (unfold MC_N; lia).
  rewrite <- HN. reflexivity.
Qed.

(** A 4-byte field at offset off of m->seg[i]. *)
Lemma mx_read_seg4 : forall m a mc bs i off, bytes_at segs m a bs -> mconf_enc mc bs ->
  (i < length (mc_seg mc))%nat -> 0 <= off -> off + 4 <= 256 ->
  ov_read_bytes segs m (wa (a + 256 * Z.of_nat i + off)) 4 = Some (fldz off 4 (fld (256 * i) 256 bs)).
Proof.
  intros m a mc bs i off B E Hi H0 H1. destruct (mx_mconf_len mc bs E) as [L LS].
  replace (a + 256 * Z.of_nat i + off) with (a + (256 * Z.of_nat i + off)) by lia.
  rewrite (bytes_at_read segs m a bs _ 4 B) by lia.
  unfold fldz, fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Z.to_nat (256 * Z.of_nat i + off)) with (Z.to_nat off + 256 * i)%nat by lia.
  rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma mx_seg_enc : forall mc bs i, mconf_enc mc bs -> (i < length (mc_seg mc))%nat ->
  mseg_enc (nth i (mc_seg mc) mseg_d) (fld (256 * i) 256 bs).
Proof. intros mc bs i (_ & _ & SG & _) Hi. exact (SG i Hi). Qed.

Lemma mx_read_role_set : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  ov_read_bytes segs m (wa (a + 256 * Z.of_nat i + 0x14)) 4 =
    Some (le4 (Z_to_bv 64 (b2z (ms_role_set (nth i (mc_seg mc) mseg_d))))).
Proof.
  intros m a mc i (bs & B & E) Hi. rewrite (mx_read_seg4 m a mc bs i 0x14 B E Hi) by lia.
  destruct (mx_seg_enc mc bs i E Hi) as (_ & _ & _ & RS & _). exact (f_equal Some RS).
Qed.

Lemma mx_read_model_set : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  ov_read_bytes segs m (wa (a + 256 * Z.of_nat i + 0x20)) 4 =
    Some (le4 (Z_to_bv 64 (b2z (ms_model_set (nth i (mc_seg mc) mseg_d))))).
Proof.
  intros m a mc i (bs & B & E) Hi. rewrite (mx_read_seg4 m a mc bs i 0x20 B E Hi) by lia.
  destruct (mx_seg_enc mc bs i E Hi) as (_ & _ & _ & _ & _ & _ & MS & _). exact (f_equal Some MS).
Qed.

Lemma mx_read_role : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  0 <= ms_role (nth i (mc_seg mc) mseg_d) < 2 ^ 31 /\
  ov_read_bytes segs m (wa (a + 256 * Z.of_nat i + 0x10)) 4 =
    Some (le4 (Z_to_bv 64 (ms_role (nth i (mc_seg mc) mseg_d)))).
Proof.
  intros m a mc i (bs & B & E) Hi. rewrite (mx_read_seg4 m a mc bs i 0x10 B E Hi) by lia.
  destruct (mx_seg_enc mc bs i E Hi) as (_ & _ & ((R0 & RE) & R31) & _).
  split; [lia | exact (f_equal Some RE)].
Qed.

(** The stores of c:303 and c:306-307. *)
Lemma mx_store_drop_model : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  mconf_at segs (write_to_mem m (wa (a + 256 * Z.of_nat i + 0x20)) (le4 (Z_to_bv 64 0))) a
    (m_upd mc i ms_drop_model).
Proof.
  intros m a mc i (bs & B & E) Hi. destruct (mx_mconf_len mc bs E) as [L LS].
  exists (upd_bytes bs (256 * i + 32) Z4). split.
  - pose proof (bytes_at_write_inside segs m a bs (Z.of_nat (256 * i + 32)) Z4 B ltac:(lia)
      ltac:(rewrite mx_Z4_len; lia)) as Hw.
    rewrite Nat2Z.id in Hw.
    replace (a + 256 * Z.of_nat i + 0x20) with (a + Z.of_nat (256 * i + 32)) by lia. exact Hw.
  - apply mx_mconf_upd; [exact E | exact Hi | rewrite mx_Z4_len; lia |].
    apply mx_mseg_drop_model. exact (mx_seg_enc mc bs i E Hi).
Qed.

Lemma mx_store_drop_role : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  mconf_at segs (write_to_mem (write_to_mem m (wa (a + 256 * Z.of_nat i + 0x10)) (le4 (Z_to_bv 64 0)))
                              (wa (a + 256 * Z.of_nat i + 0x14)) (le4 (Z_to_bv 64 0))) a
    (m_upd mc i ms_drop_role).
Proof.
  intros m a mc i (bs & B & E) Hi. destruct (mx_mconf_len mc bs E) as [L LS].
  exists (upd_bytes bs (256 * i + 16) (Z4 ++ Z4)). split.
  - pose proof (bytes_at_write_inside segs m a bs (Z.of_nat (256 * i + 16)) Z4 B ltac:(lia)
      ltac:(rewrite mx_Z4_len; lia)) as B1.
    rewrite Nat2Z.id in B1.
    pose proof (bytes_at_write_inside segs _ a _ (Z.of_nat (256 * i + 16 + 4)) Z4 B1 ltac:(lia)
      ltac:(rewrite upd_bytes_length by (rewrite mx_Z4_len; lia); rewrite mx_Z4_len; lia)) as B2.
    rewrite Nat2Z.id in B2.
    assert (EQ : upd_bytes (upd_bytes bs (256 * i + 16) Z4) (256 * i + 16 + 4) Z4 =
                 upd_bytes bs (256 * i + 16) (Z4 ++ Z4)).
    { rewrite <- (mx_upd_upd_adj bs Z4 Z4 (256 * i + 16)) by (rewrite mx_Z4_len; lia).
      rewrite mx_Z4_len. reflexivity. }
    rewrite EQ in B2.
    replace (a + 256 * Z.of_nat i + 0x10) with (a + Z.of_nat (256 * i + 16)) by lia.
    replace (a + 256 * Z.of_nat i + 0x14) with (a + Z.of_nat (256 * i + 16 + 4)) by lia. exact B2.
  - apply mx_mconf_upd; [exact E | exact Hi | rewrite length_app, mx_Z4_len; lia |].
    apply mx_mseg_drop_role. exact (mx_seg_enc mc bs i E Hi).
Qed.

End Mem.
