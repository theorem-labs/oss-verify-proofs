(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the PURE facts
   that the piece files of segment B10b of reac_segconf_parse_file (pf_seg_B10b_c.v, pf_seg_B10b_r.v,
   pf_seg_B10b_s.v, pf_seg_B10b_j.v) share. The B10b segment lane of the image-B G3 walk owner, 2026-10-30. proves no function
   (kind: model and invariant lemmas).
   ADAPTED from a working branch's lib/A/Prog/pf_a10b_f.v (a B10b sub-lane of an image-A segment lane, 313e573b5900): the
   text is image-independent (no machine state, no SRr, no Section hypothesis); the changes are the module paths
   (the B kit copies lib.B YG0f / YG0n and lib.B.Prog SegABase in place of lib.Reusable and lib.A.Prog; this
   lane's kit pf_seg_B10b_k.v for the word list), the names (prefix b10f_ / b10b_ for a10f_ / a10b_,
   PB10_WORDS for PA10_WORDS).

   Facts of the model (lib/Spec/SegModel.v strcmp, r_low, role_intent_parse, r_upd, rs_with_role;
   lib/Prog/pf_pieces_spec.v pf_role_step), of the encoding (lib/Prog/seg_spec.v rconf_enc, rseg_enc, cstr_enc,
   u32_enc, role_enc) and of the reader forms (lib/B/Prog/SegABase.v sa_bytes, sa_zs, sa_str, sa_val, sa_rconf),
   over an abstract `rd : reader`.

   What the file gives (the statements the piece files are written against):
   - b10b_cmp_lit: the result of one bcmp of low[0 .. S (length w)) with the literal w, in the byte-equality
     form the kit's abcmp_realizes (lib/B/YG0d.v) states it, is strcmp l w = 0;
   - b10b_low_nulfree, b10b_low_len, b10b_words_nulfree: the side facts that comparison needs;
   - b10b_role_some, b10b_role_none: the chain of five comparisons is role_intent_parse;
   - b10b_step_some, b10b_step_none: the two shapes of pf_role_step;
   - b10b_role_range: the role value is in 0 .. 4;
   - b10b_upd_refused, b10b_upd_overflow, b10b_upd_len: r_upd keeps both counters and the number of entries;
   - b10b_rconf_role: sa_rconf after the two `sw` (0x88d90, 0x88dac) and the provenance snprintf (0x88dc4) into
     c->seg[gi].
   The method of b10b_rconf_role is refuse_f.v's (a sub-lane, rf_upd_refd / rf_upd_slot): the new block is the
   list of bytes the new reader holds at c .. c + 16616 ([b10f_view]); every field outside the three written ones
   is the old field byte for byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B10b_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Local Notation LE4 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.

(* rseg_addr first: its body names RSEG_SIZE, which the later names then unfold *)
Ltac b10f_lia :=
  unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL,
    seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF, seg_spec.RC_REFUSED, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
    seg_spec.RC_GEN, seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_ROLE_FILE in *;
  lia.

(* ===================================== lists and bytes ===================================== *)
Lemma b10f_nth_firstn : forall {A} n (l : list A) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A n. induction n as [|n IH]; intros l k d Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma b10f_nth_skipn : forall {A} m (l : list A) k d, nth k (skipn m l) d = nth (m + k) l d.
Proof.
  intros A m. induction m as [|m IH]; intros l k d; [reflexivity|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma b10f_nth_fld : forall (l : list byte) off n k d, (k < n)%nat ->
  nth k (seg_spec.fld off n l) d = nth (off + k) l d.
Proof. intros l off n k d Hk. unfold seg_spec.fld. rewrite b10f_nth_firstn by exact Hk. apply b10f_nth_skipn. Qed.

Lemma b10f_len_fld : forall (l : list byte) off n, (off + n <= length l)%nat -> length (seg_spec.fld off n l) = n.
Proof. intros l off n H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma b10f_nth_map_seq : forall {A} (f : nat -> A) k n d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f k n d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma b10f_byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply Z_to_bv_bv_unsigned. Qed.

Lemma b10f_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma b10f_unsigned_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small, Hz.
Qed.

Lemma b10f_le_byte_range : forall v w k, 0 <= le_byte v w k < 256.
Proof. intros v w k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma b10f_in_dec : forall lo hi x : Z, {lo <= x < hi} + {~ (lo <= x < hi)}.
Proof.
  intros lo hi x. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); [left; lia | right; lia ..].
Qed.

(* the byte k of a C-string field of a byte list, as a Z *)
Lemma b10f_nth_zs : forall (LB : list byte) k, (k < length LB)%nat ->
  nth k (seg_spec.zs LB) 0 = bv_unsigned (nth k LB ZB0).
Proof.
  intros LB k Hk. unfold seg_spec.zs.
  rewrite (nth_indep (map bv_unsigned LB) 0 (bv_unsigned ZB0)) by (rewrite length_map; exact Hk).
  rewrite map_nth. reflexivity.
Qed.

(* the four little-endian bytes of a u32 field *)
Lemma b10f_nth_Zle : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|]. cbn [Z_to_le_bytes].
  destruct k as [|k]; cbn [nth].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma b10f_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (LE4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
  rewrite b10f_nth_Zle by exact Hk.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* nested fields: a field of a field is a field of the whole *)
Lemma b10f_fld_fld : forall (l : list byte) a n b m, (a + n <= m)%nat -> (b + m <= length l)%nat ->
  seg_spec.fld a n (seg_spec.fld b m l) = seg_spec.fld (b + a) n l.
Proof.
  intros l a n b m H Hl.
  assert (L1 : length (seg_spec.fld b m l) = m) by (apply b10f_len_fld; exact Hl).
  apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite (b10f_len_fld (seg_spec.fld b m l)) by lia. rewrite b10f_len_fld by lia. reflexivity.
  - intros k Hk. rewrite (b10f_len_fld (seg_spec.fld b m l)) in Hk by lia.
    rewrite (b10f_nth_fld (seg_spec.fld b m l)) by exact Hk.
    rewrite (b10f_nth_fld l b m) by lia.
    rewrite (b10f_nth_fld l (b + a) n) by exact Hk.
    replace (b + (a + k))%nat with (b + a + k)%nat by lia. reflexivity.
Qed.

Lemma b10f_fld_ext : forall (l l' : list byte) off n, (off + n <= length l)%nat -> length l' = length l ->
  (forall i, (off <= i < off + n)%nat -> nth i l' ZB0 = nth i l ZB0) -> seg_spec.fld off n l' = seg_spec.fld off n l.
Proof.
  intros l l' off n Hl Hl' H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !b10f_len_fld by lia. reflexivity.
  - intros k Hk. rewrite b10f_len_fld in Hk by lia. rewrite !b10f_nth_fld by exact Hk. apply H. lia.
Qed.

(* one entry of upd_nth *)
Lemma b10f_nth_upd_eq : forall {A} (i : nat) (f : A -> A) (l : list A) d, (i < length l)%nat ->
  nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A i f l d. revert i. induction l as [|x l IH]; intros i H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [upd_nth nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma b10f_nth_upd_ne : forall {A} (i j : nat) (f : A -> A) (l : list A) d, j <> i ->
  nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j H; [destruct i; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth]; try reflexivity; [exfalso; exact (H eq_refl)|].
  apply IH. lia.
Qed.

(* ============================== the bytes a reader holds, as a list ============================== *)
Definition b10f_o0 (o : option Z) : Z := match o with Some v => v | None => 0 end.
(* the n bytes the reader rd holds at c .. c + n *)
Definition b10f_view (rd : reader) (c : Z) (n : nat) : list byte :=
  map (fun i => Z_to_bv 8 (b10f_o0 (rd (c + Z.of_nat i)))) (seq 0 n).

Lemma b10f_view_len : forall rd c n, length (b10f_view rd c n) = n.
Proof. intros. unfold b10f_view. rewrite length_map, length_seq. reflexivity. Qed.

Lemma b10f_view_nth : forall rd c n i, (i < n)%nat ->
  nth i (b10f_view rd c n) ZB0 = Z_to_bv 8 (b10f_o0 (rd (c + Z.of_nat i))).
Proof. intros rd c n i Hi. unfold b10f_view. rewrite b10f_nth_map_seq by exact Hi. reflexivity. Qed.

Lemma b10f_view_bytes : forall rd c n,
  (forall i, (i < n)%nat -> exists v, rd (c + Z.of_nat i) = Some v /\ 0 <= v < 256) ->
  sa_bytes rd c (b10f_view rd c n).
Proof.
  intros rd c n H i Hi. rewrite b10f_view_len in Hi. rewrite b10f_view_nth by exact Hi.
  destruct (H i Hi) as (v & Hv & Hr). rewrite Hv. cbn [b10f_o0]. rewrite b10f_unsigned_small by exact Hr.
  reflexivity.
Qed.

Lemma b10f_view_keep : forall rd rd' c bs i, sa_bytes rd c bs -> (i < length bs)%nat ->
  rd' (c + Z.of_nat i) = rd (c + Z.of_nat i) -> nth i (b10f_view rd' c (length bs)) ZB0 = nth i bs ZB0.
Proof.
  intros rd rd' c bs i HB Hi E. rewrite b10f_view_nth by exact Hi. rewrite E, HB by exact Hi. cbn [b10f_o0].
  apply b10f_byte_rt.
Qed.

(* a u32 word written at a = c + off reads back as its four little-endian bytes *)
Lemma b10f_view_u32 : forall rd' c N (off : nat) a v, sa_val rd' a 4 v -> a = c + Z.of_nat off ->
  0 <= v < 2 ^ 32 -> (off + 4 <= N)%nat ->
  seg_spec.fld off (Z.to_nat 4) (b10f_view rd' c N) = LE4 (Z_to_bv 64 v).
Proof.
  intros rd' c N off a v H -> Hv Hl. change (Z.to_nat 4) with 4%nat.
  apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite b10f_len_fld by (rewrite b10f_view_len; lia). reflexivity.
  - intros k Hk. rewrite b10f_len_fld in Hk by (rewrite b10f_view_len; lia).
    rewrite b10f_nth_fld by exact Hk. rewrite b10f_view_nth by lia.
    replace (c + Z.of_nat (off + k)) with (c + Z.of_nat off + Z.of_nat k) by lia.
    rewrite (H k Hk). cbn [b10f_o0]. apply bv_eq. rewrite (b10f_le4_nth v k Hv Hk).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* the bytes f written at a = c + off read back as f *)
Lemma b10f_view_fld_bytes : forall rd' c N (off n : nat) a (f : list byte), sa_bytes rd' a f ->
  a = c + Z.of_nat off -> length f = n -> (off + n <= N)%nat -> seg_spec.fld off n (b10f_view rd' c N) = f.
Proof.
  intros rd' c N off n a f H -> Hn Hl. subst n.
  apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite b10f_len_fld by (rewrite b10f_view_len; lia). reflexivity.
  - intros k Hk. rewrite b10f_len_fld in Hk by (rewrite b10f_view_len; lia).
    rewrite b10f_nth_fld by exact Hk. rewrite b10f_view_nth by lia.
    replace (c + Z.of_nat (off + k)) with (c + Z.of_nat off + Z.of_nat k) by lia.
    rewrite (H k Hk). cbn [b10f_o0]. apply b10f_byte_rt.
Qed.

Ltac b10f_keep HB Hk :=
  first [ apply b10f_view_len
        | intros ?j ?Hj; apply (b10f_view_keep _ _ _ _ _ HB); [b10f_lia | apply Hk; b10f_lia]
        | b10f_lia ].

(* one entry after the role stores: the role word, the role_set word and the role_file field are new, every
   other byte of the 356 is the old one *)
Lemma b10f_rseg_role : forall (s : rseg) (F F' : list byte) (r : Z) (file : list Z),
  seg_spec.rseg_enc s F -> length F' = 356%nat ->
  (forall j, (j < 356)%nat -> ~ (16 <= j < 24)%nat -> ~ (160 <= j < 256)%nat -> nth j F' ZB0 = nth j F ZB0) ->
  0 <= r < 2 ^ 31 ->
  seg_spec.fldz seg_spec.RS_ROLE 4 F' = LE4 (Z_to_bv 64 r) ->
  seg_spec.fldz seg_spec.RS_ROLE_SET 4 F' = LE4 (Z_to_bv 64 1) ->
  seg_spec.cstr_enc 96 file (seg_spec.fldz seg_spec.RS_ROLE_FILE 96 F') ->
  seg_spec.rseg_enc (rs_with_role r file s) F'.
Proof.
  intros s F F' r file HE HlF' Hk Hr Hro Hrs Hrf.
  destruct HE as (HlF & Hnm & Hro0 & Hrs0 & Hig & Higs & Hmd & Hmds & Hmf & Hrf0 & Hif & Hsg).
  assert (EN : forall a n : nat, (a + n <= 356)%nat -> (a + n <= 16 \/ 24 <= a)%nat ->
                 (a + n <= 160 \/ 256 <= a)%nat -> seg_spec.fld a n F' = seg_spec.fld a n F).
  { intros a n Han H1 H2. apply b10f_fld_ext; [lia | lia |]. intros j Hj. apply Hk; lia. }
  assert (EZ : forall a n : Z, 0 <= a -> 0 <= n -> a + n <= 356 -> (a + n <= 16 \/ 24 <= a) ->
                 (a + n <= 160 \/ 256 <= a) -> seg_spec.fldz a n F' = seg_spec.fldz a n F).
  { intros a n Ha Hn Han H1 H2. unfold seg_spec.fldz. apply EN; lia. }
  unfold seg_spec.rseg_enc. unfold rs_with_role.
  cbn [rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file rs_role_file
       rs_ignore_file rs_seen_gen].
  split; [exact HlF'|].
  split; [rewrite (EN 0%nat 16%nat) by lia; exact Hnm|].
  split; [split; [split; [lia | exact Hro] | lia]|].
  split; [exact Hrs|].
  split; [rewrite (EZ seg_spec.RS_IGNORE 4) by (unfold seg_spec.RS_IGNORE; lia); exact Hig|].
  split; [rewrite (EZ seg_spec.RS_IGNORE_SET 4) by (unfold seg_spec.RS_IGNORE_SET; lia); exact Higs|].
  split; [rewrite (EZ seg_spec.RS_MODEL 24) by (unfold seg_spec.RS_MODEL; lia); exact Hmd|].
  split; [rewrite (EZ seg_spec.RS_MODEL_SET 4) by (unfold seg_spec.RS_MODEL_SET; lia); exact Hmds|].
  split; [rewrite (EZ seg_spec.RS_MODEL_FILE 96) by (unfold seg_spec.RS_MODEL_FILE; lia); exact Hmf|].
  split; [exact Hrf|].
  split; [rewrite (EZ seg_spec.RS_IGNORE_FILE 96) by (unfold seg_spec.RS_IGNORE_FILE; lia); exact Hif|].
  rewrite (EZ seg_spec.RS_SEEN_GEN 4) by (unfold seg_spec.RS_SEEN_GEN; lia). exact Hsg.
Qed.

(* ======================================= strings ======================================= *)
Lemma b10f_strcmp_eq_iff : forall l w, ~ In 0 l -> ~ In 0 w -> (strcmp l w = 0 <-> l = w).
Proof.
  induction l as [|a l IH]; intros [|b w] Hl Hw; cbn [strcmp].
  - split; intros _; reflexivity.
  - split; [|intros H; discriminate H]. intros H. exfalso. apply Hw. left. lia.
  - split; [|intros H; discriminate H]. intros H. exfalso. apply Hl. left. exact H.
  - destruct (Z.eqb_spec a b) as [E|E]; destruct (Z.eqb_spec a 0) as [E0|E0]; cbn [andb negb].
    + exfalso. apply Hl. left. exact E0.
    + subst b.
      specialize (IH w ltac:(intros H; apply Hl; right; exact H) ltac:(intros H; apply Hw; right; exact H)).
      split; [intros H; f_equal; exact (proj1 IH H) | intros H; injection H as H; exact (proj2 IH H)].
    + exfalso. apply Hl. left. exact E0.
    + split; [intros H; exfalso; lia | intros H; injection H as H1 _; exfalso; exact (E H1)].
Qed.

(* two NUL-free strings whose bytes with the NUL agree up to the shorter one's NUL are equal *)
Lemma b10f_eq_of_nth : forall l w : list Z, ~ In 0 l -> ~ In 0 w ->
  (forall k, (k <= length l)%nat -> (k <= length w)%nat -> nth k (l ++ [0]) 0 = nth k (w ++ [0]) 0) -> l = w.
Proof.
  induction l as [|a l IH]; intros [|b w] Hl Hw H.
  - reflexivity.
  - exfalso. specialize (H 0%nat ltac:(cbn; lia) ltac:(cbn; lia)). cbn in H. apply Hw. left. lia.
  - exfalso. specialize (H 0%nat ltac:(cbn; lia) ltac:(cbn; lia)). cbn in H. apply Hl. left. lia.
  - pose proof (H 0%nat ltac:(cbn; lia) ltac:(cbn; lia)) as E0. cbn in E0. subst b.
    f_equal. apply IH.
    + intros Hin. apply Hl. right. exact Hin.
    + intros Hin. apply Hw. right. exact Hin.
    + intros k Hk1 Hk2. exact (H (S k) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma b10f_lower_nz : forall q, q <> 0 -> lower q <> 0.
Proof.
  intros q Hq. unfold lower. destruct ((65 <=? q) && (q <=? 90)) eqn:E; [|exact Hq].
  apply andb_true_iff in E as [E1 _]. apply Z.leb_le in E1. lia.
Qed.

Lemma b10f_nulfree_b : forall l : list Z, forallb (fun x => negb (x =? 0)) l = true -> ~ In 0 l.
Proof.
  induction l as [|x l IH]; cbn [forallb]; intros H Hin; [exact Hin|].
  apply andb_true_iff in H as [H1 H2]. destruct Hin as [E|Hin].
  - subst x. cbn in H1. discriminate H1.
  - exact (IH H2 Hin).
Qed.

Lemma b10f_eqb_ne : forall z, z <> 0 -> (z =? 0) = false.
Proof. intros z H. apply Z.eqb_neq, H. Qed.

Lemma b10f_in0 : In S_auto PB10_WORDS.
Proof. unfold PB10_WORDS. left. reflexivity. Qed.
Lemma b10f_in1 : In S_master PB10_WORDS.
Proof. unfold PB10_WORDS. right. left. reflexivity. Qed.
Lemma b10f_in2 : In S_slave PB10_WORDS.
Proof. unfold PB10_WORDS. right. right. left. reflexivity. Qed.
Lemma b10f_in3 : In S_tap PB10_WORDS.
Proof. unfold PB10_WORDS. right. right. right. left. reflexivity. Qed.
Lemma b10f_in4 : In S_box PB10_WORDS.
Proof. unfold PB10_WORDS. right. right. right. right. left. reflexivity. Qed.

(* ===================================== the shared facts ===================================== *)

(* the fold buffer never holds a NUL byte inside the string it builds *)
Lemma b10b_low_nulfree : forall v li cap, ~ In 0 (r_low v li cap).
Proof.
  induction v as [|q v IH]; intros li cap; cbn [r_low].
  - intros H. destruct H.
  - destruct (Z.eqb_spec q 0) as [Hq|Hq]; [intros H; destruct H|].
    destruct (li + 1 <? cap)%nat; [|intros H; destruct H].
    intros [H|H]; [exact (b10f_lower_nz q Hq H) | exact (IH (S li) cap H)].
Qed.

(* the C string in a 64-byte buffer is shorter than the buffer *)
Lemma b10b_low_len : forall (LB : list byte) (l : list Z),
  length LB = 64%nat -> firstn (S (length l)) (seg_spec.zs LB) = l ++ [0] -> (length l < 64)%nat.
Proof.
  intros LB l HL H. apply (f_equal (@length Z)) in H.
  rewrite length_firstn, length_app in H. unfold seg_spec.zs in H. rewrite length_map, HL in H.
  cbn [length] in H. lia.
Qed.

(* the five words the binary compares, in the order reac_role_intent_parse compares them *)
Lemma b10b_words_nulfree : forall w, In w PB10_WORDS -> ~ In 0 w.
Proof.
  intros w Hw. apply b10f_nulfree_b.
  assert (H : forallb (fun w => forallb (fun x => negb (x =? 0)) w) PB10_WORDS = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. exact (H w Hw).
Qed.

(* O1's bcmp half in the form the kit's abcmp_realizes gives it: the call's result is BYTE EQUALITY through
   the reader over [0, S (length w)), not memcmp_model, so pf_pieces_spec.O1_bcmp_lit is not the usable
   shape. low holds the 64 bytes LB whose C string is l; lit holds the literal w and its NUL. *)
Lemma b10b_cmp_lit : forall (rd : reader) (low lit : Z) (LB : list byte) (l w : list Z),
  length LB = 64%nat -> sa_bytes rd low LB ->
  firstn (S (length l)) (seg_spec.zs LB) = l ++ [0] -> ~ In 0 l ->
  sa_str rd lit w -> ~ In 0 w ->
  ((forall i, 0 <= i < Z.of_nat (S (length w)) -> rd (low + i) = rd (lit + i)) <-> strcmp l w = 0).
Proof.
  intros rd low lit LB l w HL HB HF Hl HS Hw.
  pose proof (b10b_low_len LB l HL HF) as Hl64.
  destruct HS as [[HZ _] _].
  assert (RL : forall k, (k <= length l)%nat -> rd (low + Z.of_nat k) = Some (nth k (l ++ [0]) 0)).
  { intros k Hk. rewrite HB by lia. f_equal. rewrite <- HF. rewrite b10f_nth_firstn by lia.
    rewrite b10f_nth_zs by lia. reflexivity. }
  assert (RW : forall k, (k <= length w)%nat -> rd (lit + Z.of_nat k) = Some (nth k (w ++ [0]) 0)).
  { intros k Hk. assert (Hk' : (k < length (w ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    exact (HZ k Hk'). }
  split.
  - intros H. apply (proj2 (b10f_strcmp_eq_iff l w Hl Hw)). apply b10f_eq_of_nth; [exact Hl | exact Hw |].
    intros k Hk1 Hk2. specialize (H (Z.of_nat k) ltac:(lia)).
    rewrite (RL k Hk1), (RW k Hk2) in H. injection H as H. exact H.
  - intros H. apply (proj1 (b10f_strcmp_eq_iff l w Hl Hw)) in H. subst w.
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (RL (Z.to_nat i) ltac:(lia)), (RW (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

(* the chain of five comparisons IS role_intent_parse *)
Lemma b10b_role_some : forall (l : list Z) (k : nat) (w : list Z), nth_error PB10_WORDS k = Some w ->
  (forall j wj, (j < k)%nat -> nth_error PB10_WORDS j = Some wj -> strcmp l wj <> 0) ->
  strcmp l w = 0 -> role_intent_parse l = Some (Z.of_nat k).
Proof.
  intros l k w Hk Hlt Hw.
  assert (N0 : (0 < k)%nat -> (strcmp l S_auto =? 0) = false)
    by (intros H; apply b10f_eqb_ne; exact (Hlt 0%nat S_auto H eq_refl)).
  assert (N1 : (1 < k)%nat -> (strcmp l S_master =? 0) = false)
    by (intros H; apply b10f_eqb_ne; exact (Hlt 1%nat S_master H eq_refl)).
  assert (N2 : (2 < k)%nat -> (strcmp l S_slave =? 0) = false)
    by (intros H; apply b10f_eqb_ne; exact (Hlt 2%nat S_slave H eq_refl)).
  assert (N3 : (3 < k)%nat -> (strcmp l S_tap =? 0) = false)
    by (intros H; apply b10f_eqb_ne; exact (Hlt 3%nat S_tap H eq_refl)).
  unfold role_intent_parse. unfold PB10_WORDS in Hk.
  destruct k as [|[|[|[|[|k]]]]]; cbn [nth_error] in Hk.
  - injection Hk as <-. rewrite Hw. reflexivity.
  - injection Hk as <-. rewrite N0 by lia. rewrite Hw. reflexivity.
  - injection Hk as <-. rewrite N0, N1 by lia. rewrite Hw. reflexivity.
  - injection Hk as <-. rewrite N0, N1, N2 by lia. rewrite Hw. reflexivity.
  - injection Hk as <-. rewrite N0, N1, N2, N3 by lia. rewrite Hw. reflexivity.
  - destruct k; cbn [nth_error] in Hk; discriminate Hk.
Qed.

Lemma b10b_role_none : forall l, (forall w, In w PB10_WORDS -> strcmp l w <> 0) ->
  role_intent_parse l = None.
Proof.
  intros l H. unfold role_intent_parse.
  rewrite (b10f_eqb_ne _ (H S_auto b10f_in0)), (b10f_eqb_ne _ (H S_master b10f_in1)),
    (b10f_eqb_ne _ (H S_slave b10f_in2)), (b10f_eqb_ne _ (H S_tap b10f_in3)),
    (b10f_eqb_ne _ (H S_box b10f_in4)).
  reflexivity.
Qed.

(* the two shapes of the line's step *)
Lemma b10b_step_some : forall cf gi nm ln val r, role_intent_parse (r_low val 0 64) = Some r ->
  pf_role_step cf gi nm ln val =
  (r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading cf)])), Some gi, nm).
Proof. intros cf gi nm ln val r H. unfold pf_role_step. rewrite H. reflexivity. Qed.

Lemma b10b_step_none : forall cf gi nm ln val, role_intent_parse (r_low val 0 64) = None ->
  pf_role_step cf gi nm ln val = (refuse cf ln F_badrole [AS nm; AS val], Some gi, nm).
Proof. intros cf gi nm ln val H. unfold pf_role_step. rewrite H. reflexivity. Qed.

(* the role value the binary stores on each arm is in range for role_enc *)
Lemma b10b_role_range : forall l r, role_intent_parse l = Some r -> 0 <= r <= 4.
Proof.
  intros l r H. unfold role_intent_parse in H.
  destruct (strcmp l S_auto =? 0); [injection H as <-; lia|].
  destruct (strcmp l S_master =? 0); [injection H as <-; lia|].
  destruct (strcmp l S_slave =? 0); [injection H as <-; lia|].
  destruct (strcmp l S_tap =? 0); [injection H as <-; lia|].
  destruct (strcmp l S_box =? 0); [injection H as <-; lia | discriminate H].
Qed.

(* r_upd touches neither counter nor the number of entries: what the exit cut's pf_cnt / pf_cur_ok need *)
Lemma b10b_upd_refused : forall cf gi f, rc_refused (r_upd cf gi f) = rc_refused cf.
Proof. intros cf gi f. reflexivity. Qed.
Lemma b10b_upd_overflow : forall cf gi f, rc_overflow (r_upd cf gi f) = rc_overflow cf.
Proof. intros cf gi f. reflexivity. Qed.
Lemma b10b_upd_len : forall cf gi f, length (rc_seg (r_upd cf gi f)) = length (rc_seg cf).
Proof. intros cf gi f. unfold r_upd, r_set_segs. cbn [rc_seg]. apply upd_nth_len. Qed.

(* sa_rconf of the block after the two `sw` and the provenance snprintf into c->seg[gi]: the role word, the
   role_set word, the role_file field, every other byte of the block as it was. *)
Lemma b10b_rconf_role : forall (rd rd' : reader) (c : Z) (cf : rconf) (gi : nat) (r : Z) (file : list Z),
  sa_rconf rd c cf -> (gi < length (rc_seg cf))%nat -> 0 <= r < 2 ^ 31 ->
  (length file < 96)%nat -> ~ In 0 file ->
  sa_val rd' (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE) 4 r ->
  sa_val rd' (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_SET) 4 1 ->
  (exists f, sa_bytes rd' (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_FILE) f /\
             seg_spec.cstr_enc 96 file f) ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE <= c + i
        < seg_spec.rseg_addr c gi + seg_spec.RS_ROLE + 4) ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_SET <= c + i
        < seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_SET + 4) ->
     ~ (seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_FILE <= c + i
        < seg_spec.rseg_addr c gi + seg_spec.RS_ROLE_FILE + 96) ->
     rd' (c + i) = rd (c + i)) ->
  sa_rconf rd' c (r_upd cf gi (rs_with_role r file)).
Proof.
  intros rd rd' c cf gi r file (bs & HB & HE) Hgi Hr Hfl Hfn HR HRS (f & HFb & HFc) Hk.
  pose proof HFc as (Hf96 & _).
  pose proof HE as (HL & Hsl & Hseg & Hn & Hrl & Hrf & Hnref & Hrefd & Hov & Hrd & Hgen).
  pose proof (b10f_view_len rd' c (length bs)) as HLv.
  exists (b10f_view rd' c (length bs)). split.
  - apply b10f_view_bytes. intros i Hi.
    destruct (b10f_in_dec (356 * Z.of_nat gi + 16) (356 * Z.of_nat gi + 20) (Z.of_nat i)) as [Ha|Ha].
    { assert (HK : (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 16)) < 4)%nat) by lia.
      pose proof (HR _ HK) as E.
      exists (le_byte r 4 (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 16)))).
      split; [|apply b10f_le_byte_range].
      rewrite <- E. f_equal. b10f_lia. }
    destruct (b10f_in_dec (356 * Z.of_nat gi + 20) (356 * Z.of_nat gi + 24) (Z.of_nat i)) as [Hb|Hb].
    { assert (HK : (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 20)) < 4)%nat) by lia.
      pose proof (HRS _ HK) as E.
      exists (le_byte 1 4 (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 20)))).
      split; [|apply b10f_le_byte_range].
      rewrite <- E. f_equal. b10f_lia. }
    destruct (b10f_in_dec (356 * Z.of_nat gi + 160) (356 * Z.of_nat gi + 256) (Z.of_nat i)) as [Hc|Hc].
    { assert (HK : (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 160)) < length f)%nat) by lia.
      pose proof (HFb _ HK) as E.
      exists (bv_unsigned (nth (Z.to_nat (Z.of_nat i - (356 * Z.of_nat gi + 160))) f ZB0)).
      split; [|apply b10f_byte_range].
      rewrite <- E. f_equal. b10f_lia. }
    rewrite Hk by b10f_lia. rewrite HB by exact Hi. eexists; split; [reflexivity | apply b10f_byte_range].
  - unfold seg_spec.rconf_enc, seg_spec.fldz in *. unfold r_upd, r_set_segs.
    cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
    rewrite upd_nth_len.
    split; [rewrite HLv; exact HL|].
    split; [exact Hsl|].
    split.
    { intros i Hi. destruct (Nat.eq_dec i gi) as [->|Hne].
      - rewrite b10f_nth_upd_eq by exact Hgi.
        apply (b10f_rseg_role _ (seg_spec.fld (356 * gi) 356 bs)).
        + exact (Hseg gi Hgi).
        + apply b10f_len_fld. b10f_lia.
        + intros j Hj Hj1 Hj2. rewrite !b10f_nth_fld by lia.
          apply (b10f_view_keep rd rd' c bs); [exact HB | b10f_lia | apply Hk; b10f_lia].
        + exact Hr.
        + unfold seg_spec.fldz. rewrite b10f_fld_fld by b10f_lia.
          apply (b10f_view_u32 rd' c (length bs) _ _ r HR); [b10f_lia | lia | b10f_lia].
        + unfold seg_spec.fldz. rewrite b10f_fld_fld by b10f_lia.
          apply (b10f_view_u32 rd' c (length bs) _ _ 1 HRS); [b10f_lia | lia | b10f_lia].
        + unfold seg_spec.fldz. rewrite b10f_fld_fld by b10f_lia.
          rewrite (b10f_view_fld_bytes rd' c (length bs) _ _ _ f HFb) by b10f_lia. exact HFc.
      - rewrite b10f_nth_upd_ne by exact Hne.
        rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk.
        exact (Hseg i Hi). }
    split; [rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hn|].
    split; [exact Hrl|].
    split; [intros i Hi; specialize (Hrf i Hi);
            rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hrf|].
    split; [rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hnref|].
    split; [rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hrefd|].
    split; [rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hov|].
    split; [rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk; exact Hrd|].
    rewrite (b10f_fld_ext bs (b10f_view rd' c (length bs))) by b10f_keep HB Hk. exact Hgen.
Qed.
