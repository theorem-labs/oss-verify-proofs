(** struct mconf in memory (seg_spec.mconf_at / mconf_atp / mconf_encp), build-independent (any segment list):
    the reads and the stores m_file's walks make, as lemmas over the block's bytes (the UBSan
    twin's walk can use them as they are). The stores are the single-field setters below, applied in the
    binary's order (0x14568-0x14578 role_set, role; 0x14558 / 0x14560 model, model_set; 0x146b8 / 0x146c0
    ignore, ignore_set; the snprintf of role_file / ignore_file; 0x14720 gen; 0x146e8 n++, then 0x146fc memset,
    0x14710 memcpy name, gen; 0x14638 overflow++; 0x1461c kept_knock[n_kept] = 1; 0x14038 gen++; the entry's
    snprintf of reading). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Frame Step.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** Single-field setters and SegModel's edits in their terms *)
Definition ms_set_role (r : Z) (g : mseg) : mseg :=
  MSeg (ms_name g) r (ms_role_set g) (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g)
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_role_set (b : bool) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) b (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g)
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_ignore (b : bool) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) b (ms_ignore_set g) (ms_model_set g) (ms_model g)
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_ignore_set (b : bool) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) b (ms_model_set g) (ms_model g)
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_model_set (b : bool) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) b (ms_model g)
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_model (s : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) (ms_model_set g) s
       (ms_role_file g) (ms_ignore_file g) (ms_gen g).
Definition ms_set_role_file (s : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g)
       s (ms_ignore_file g) (ms_gen g).
Definition ms_set_ignore_file (s : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g)
       (ms_role_file g) s (ms_gen g).

Lemma ms_with_role_eq : forall r f g, ms_with_role r f g = ms_set_role_file f (ms_set_role r (ms_set_role_set true g)).
Proof. intros r f g. destruct g; reflexivity. Qed.
Lemma ms_with_model_eq : forall s g, ms_with_model s g = ms_set_model_set true (ms_set_model s g).
Proof. intros s g. destruct g; reflexivity. Qed.
Lemma ms_with_ignore_eq : forall b f g,
  ms_with_ignore b f g = ms_set_ignore_file f (ms_set_ignore_set true (ms_set_ignore b g)).
Proof. intros b f g. destruct g; reflexivity. Qed.

Definition mc_set_gen (z : Z) (c : mconf) : mconf :=
  MConf (mc_seg c) (mc_overflow c) (mc_refused c) (mc_kept c) z (mc_reading c).
Definition mc_set_overflow (z : Z) (c : mconf) : mconf :=
  MConf (mc_seg c) z (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c).
Definition mc_set_reading (s : list Z) (c : mconf) : mconf :=
  MConf (mc_seg c) (mc_overflow c) (mc_refused c) (mc_kept c) (mc_gen c) s.

(** ** Helpers (prefix mcx_): byte windows of an updated list, model lists *)
Lemma mcx_nth_ext : forall {A} (l l' : list A), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros A l. induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma mcx_fld_nth : forall off n (L : list byte) i,
  nth_error (fld off n L) i = if (i <? n)%nat then nth_error L (off + i) else None.
Proof.
  intros off n L i. unfold fld. rewrite nth_error_firstn.
  destruct (i <? n)%nat; [|reflexivity]. rewrite nth_error_skipn. f_equal; lia.
Qed.

Lemma mcx_fld_length : forall off n (L : list byte), (off + n <= length L)%nat -> length (fld off n L) = n.
Proof. intros off n L H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

(** A window disjoint from the written range is unchanged. *)
Lemma mcx_fld_upd_out : forall (L : list byte) k nb off n, (k + length nb <= length L)%nat ->
  (off + n <= k \/ k + length nb <= off)%nat -> fld off n (upd_bytes L k nb) = fld off n L.
Proof.
  intros L k nb off n H1 H2. apply mcx_nth_ext. intros i. rewrite !mcx_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi]; [|reflexivity].
  destruct (Nat.ltb_spec0 (off + i) (length L)) as [Hl|Hl].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (off + i)); destruct (Nat.ltb_spec0 (off + i) (k + length nb)); cbn [andb];
      first [reflexivity | exfalso; lia].
  - rewrite (proj2 (nth_error_None L (off + i))) by lia.
    apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.

(** The written window itself holds the new bytes. *)
Lemma mcx_fld_upd_same : forall (L : list byte) k n nb, n = length nb -> (k + n <= length L)%nat ->
  fld k n (upd_bytes L k nb) = nb.
Proof.
  intros L k n nb -> H. apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. lia.
Qed.

(** A window that starts at the written range and covers it: the new bytes, then the old rest. *)
Lemma mcx_fld_upd_head : forall (L : list byte) k n nb, (k + n <= length L)%nat -> (length nb <= n)%nat ->
  fld k n (upd_bytes L k nb) = nb ++ fld (k + length nb) (n - length nb) L.
Proof.
  intros L k n nb H1 H2. apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite nth_error_app1 by lia. destruct (Nat.ltb_spec0 i n); [|exfalso; lia].
    rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - rewrite nth_error_app2 by lia. rewrite mcx_fld_nth.
    destruct (Nat.ltb_spec0 i n); destruct (Nat.ltb_spec0 (i - length nb) (n - length nb)); try (exfalso; lia).
    + rewrite upd_bytes_nth by lia.
      destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
        first [f_equal; lia | exfalso; lia].
    + reflexivity.
Qed.

(** A window [off, off + n) containing the written range: the window's own update. *)
Lemma mcx_fld_upd_sub : forall (L : list byte) off n k nb, (k + length nb <= n)%nat -> (off + n <= length L)%nat ->
  fld off n (upd_bytes L (off + k) nb) = upd_bytes (fld off n L) k nb.
Proof.
  intros L off n k nb H1 H2. pose proof (mcx_fld_length off n L H2) as HF.
  apply mcx_nth_ext. intros i. rewrite mcx_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi].
  - rewrite (upd_bytes_nth (fld off n L)) by lia. rewrite upd_bytes_nth by lia. rewrite mcx_fld_nth.
    destruct (Nat.ltb_spec0 i n); [|exfalso; lia].
    destruct (Nat.leb_spec0 (off + k) (off + i)); destruct (Nat.ltb_spec0 (off + i) (off + k + length nb));
    destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length nb)); cbn [andb];
      first [reflexivity | f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. rewrite upd_bytes_length by lia. lia.
Qed.

Lemma mcx_fld_fld : forall a n b k (L : list byte), (a + n <= k)%nat -> fld a n (fld b k L) = fld (b + a) n L.
Proof.
  intros a n b k L H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

Lemma mcx_zb_length : forall s, length (zb s) = length s.
Proof. intros s. unfold zb. apply length_map. Qed.

Lemma mcx_zbz_length : forall s, length (zb s ++ [ZERO]) = S (length s).
Proof. intros s. rewrite length_app, mcx_zb_length. cbn [length]. lia. Qed.

Lemma mcx_zs_app : forall a b, zs (a ++ b) = zs a ++ zs b.
Proof. intros a b. unfold zs. apply map_app. Qed.

Lemma mcx_zs_zb : forall s, Forall (fun x => 0 <= x < 256) s -> zs (zb s) = s.
Proof.
  induction s as [|x s IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hx. pose proof (Forall_inv_tail H) as Hs. cbv beta in Hx.
  unfold zs, zb in *. cbn [map]. f_equal; [|apply IH; exact Hs].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma mcx_zs_nul : forall s, Forall (fun x => 0 <= x < 256) s -> zs (zb s ++ [ZERO]) = s ++ [0].
Proof. intros s H. rewrite mcx_zs_app, mcx_zs_zb by exact H. reflexivity. Qed.

Lemma mcx_firstn_app_exact : forall {A} (l1 l2 : list A) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof. intros A l1 l2 n ->. induction l1 as [|x l1 IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

(** A char[cap] field after writing s and its NUL at its start. *)
Lemma mcx_cstr_upd : forall (L : list byte) k cap n s, n = cap -> (k + cap <= length L)%nat ->
  (length s < cap)%nat -> ~ In 0 s -> Forall (fun x => 0 <= x < 256) s ->
  cstr_enc cap s (fld k n (upd_bytes L k (zb s ++ [ZERO]))).
Proof.
  intros L k cap n s -> H1 H2 H3 H4.
  rewrite mcx_fld_upd_head by (rewrite ?mcx_zbz_length; lia).
  rewrite mcx_zbz_length.
  split; [rewrite length_app, mcx_zbz_length, mcx_fld_length by lia; lia|].
  split; [exact H2|]. split; [exact H3|].
  rewrite mcx_zs_app, (mcx_zs_nul s H4).
  apply mcx_firstn_app_exact. rewrite length_app. cbn [length]. lia.
Qed.

(** What a C-string field fixes: its bytes are bytes in range. *)
Lemma mcx_cstr_forall : forall cap s f, cstr_enc cap s f -> Forall (fun x => 0 <= x < 256) s.
Proof.
  intros cap s f (_ & _ & _ & Hz). apply Forall_forall. intros x Hx. cbv beta.
  assert (Hin : In x (zs f)).
  { rewrite <- (firstn_skipn (S (length s)) (zs f)). apply in_or_app. left. rewrite Hz.
    apply in_or_app. left. exact Hx. }
  unfold zs in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). subst x.
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. lia.
Qed.

(** ... and the field is the string's bytes, a NUL, then the rest. *)
Lemma mcx_cstr_bytes : forall s (f : list byte), firstn (S (length s)) (zs f) = s ++ [0] ->
  exists bs0 rest, f = bs0 ++ ZERO :: rest /\ zs bs0 = s.
Proof.
  induction s as [|x s IH]; intros [|b f] H; cbn [length firstn zs map app] in H; try discriminate H.
  - injection H as Hb. exists [], f. split; [|reflexivity]. cbn [app]. f_equal.
    apply bv_eq. rewrite Hb. reflexivity.
  - injection H as Hb Hf. destruct (IH f Hf) as (bs0 & rest & -> & Hz).
    exists (b :: bs0), rest. split; [reflexivity|]. unfold zs in *. cbn [map]. rewrite Hb, Hz. reflexivity.
Qed.

(** memset(g, 0, 256) + memcpy(g->name, nm, |nm|): the byte after the name is already 0. *)
Lemma mcx_upd_zeros_nul : forall n s, (length s < n)%nat ->
  upd_bytes (repeat ZERO n) 0 (zb s) = upd_bytes (repeat ZERO n) 0 (zb s ++ [ZERO]).
Proof.
  intros n s H. unfold upd_bytes. rewrite mcx_zbz_length, mcx_zb_length, !skipn_repeat_gen.
  cbn [firstn app Nat.add]. rewrite <- app_assoc. f_equal.
  replace (n - length s)%nat with (S (n - S (length s))) by lia. reflexivity.
Qed.

Lemma mcx_upd_nth_length : forall {A} i (f : A -> A) (l : list A), length (upd_nth i f l) = length l.
Proof.
  intros A i f l. revert i. induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma mcx_upd_nth_same : forall {A} i (f : A -> A) (l : list A) d, (i < length l)%nat ->
  nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A i f l d. revert i. induction l as [|x l IH]; intros [|i] H; cbn [length] in H.
  - exfalso; lia.
  - exfalso; lia.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

Lemma mcx_upd_nth_other : forall {A} i j (f : A -> A) (l : list A) d, i <> j ->
  nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j H; [destruct i; reflexivity|].
  destruct i as [|i]; destruct j as [|j].
  - exfalso. apply H. reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

Lemma mcx_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside].
  - left. exact I.
  - destruct (IH x) as [H|H].
    + destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
      destruct (Z_lt_le_dec x hi) as [H2|H2];
        [right; intros [H3 _]; apply H3; lia | left; split; [lia | exact H]].
    + right. intros [_ H3]. exact (H H3).
Qed.

(** The slack of m->reading: the block ends at c + 9236 = c + 4 (mod 8). *)
Lemma mcx_slack : forall c t r l, c mod 8 = 0 -> 0 <= t -> 0 <= r -> t + 1 + r = 96 -> (- (c + 9236)) mod 8 <= l ->
  (- (c + 9140 + t + 1)) mod 8 <= r + l.
Proof.
  intros c t r l Hc Ht Hr0 Hr Hl.
  assert (Ec : c = 8 * (c / 8)) by (pose proof (Z.div_mod c 8 ltac:(lia)) as E; rewrite Hc, Z.add_0_r in E; exact E).
  remember (c / 8) as q eqn:Eq. clear Eq Hc. subst c.
  replace (- (8 * q + 9236)) with (4 + (- q - 1155) * 8) in Hl by (clear Hl; lia).
  rewrite Z_mod_plus_full in Hl. change (4 mod 8) with 4 in Hl.
  replace (- (8 * q + 9140 + t + 1)) with ((99 - t) + (- q - 1155) * 8) by (clear Hl; lia).
  rewrite Z_mod_plus_full.
  pose proof (Z.mod_le (99 - t) 8 ltac:(lia) ltac:(lia)) as Hm.
  remember ((99 - t) mod 8) as u eqn:Eu. clear Eu. lia.
Qed.

Ltac mcx_lia := unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
  MS_IGNORE_FILE, MS_GEN, MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING,
  SEG_M_SIZE in *; lia.
Ltac mcx_out := rewrite mcx_fld_upd_out by mcx_lia.
Ltac mcx_keep H := mcx_out; exact H.

(** ** What an encoding bounds *)
Lemma mconf_enc_bounds : forall pend mc bs, mconf_encp pend mc bs ->
  length bs = 9236%nat /\ (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat /\
  0 <= mc_gen mc < 2 ^ 32 /\ 0 <= mc_refused mc < 2 ^ 32 /\ 0 <= mc_overflow mc < 2 ^ 32 /\
  (length (mc_reading mc) < 96)%nat /\ ~ In 0 (mc_reading mc) /\ Forall (fun x => 0 <= x < 256) (mc_reading mc) /\
  (forall i, (i < length (mc_seg mc))%nat ->
     (length (ms_name (nth i (mc_seg mc) mseg_d)) < 16)%nat /\ ~ In 0 (ms_name (nth i (mc_seg mc) mseg_d)) /\
     Forall (fun x => 0 <= x < 256) (ms_name (nth i (mc_seg mc) mseg_d)) /\
     0 <= ms_gen (nth i (mc_seg mc) mseg_d) < 2 ^ 32).
Proof.
  intros pend mc bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  pose proof H12 as (R1 & R2 & R3 & R4). destruct H5 as [O1 _]. destruct H6 as [F1 _]. destruct H11 as [G1 _].
  split; [apply Nat2Z.inj; rewrite H1; reflexivity|].
  split; [exact H2|]. split; [exact H7|]. split; [exact G1|]. split; [exact F1|]. split; [exact O1|].
  split; [exact R2|]. split; [exact R3|]. split; [exact (mcx_cstr_forall _ _ _ H12)|].
  intros i Hi. destruct (H3 i Hi) as (_ & N & _ & _ & _ & _ & _ & _ & _ & _ & (Gg & _)).
  pose proof N as (_ & N2 & N3 & _).
  split; [exact N2|]. split; [exact N3|]. split; [exact (mcx_cstr_forall _ _ _ N)|]. exact Gg.
Qed.

(** ** The field edits on the 256 bytes of an entry *)
Lemma mseg_enc_role : forall g f r, mseg_enc g f -> 0 <= r < 2 ^ 31 ->
  mseg_enc (ms_set_role r g) (upd_bytes f (Z.to_nat MS_ROLE) (le4 (Z_to_bv 64 r))).
Proof.
  intros g f r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hr.
  pose proof (length_le4 (Z_to_bv 64 r)) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_role ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; split; [split; [lia | reflexivity] | lia]|].
  split; [mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_role_set : forall g f b, mseg_enc g f ->
  mseg_enc (ms_set_role_set b g) (upd_bytes f (Z.to_nat MS_ROLE_SET) (le4 (Z_to_bv 64 (if b then 1 else 0)))).
Proof.
  intros g f b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  pose proof (length_le4 (Z_to_bv 64 (if b then 1 else 0))) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_role_set ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; reflexivity|].
  split; [mcx_keep H5|]. split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_ignore : forall g f b, mseg_enc g f ->
  mseg_enc (ms_set_ignore b g) (upd_bytes f (Z.to_nat MS_IGNORE) (le4 (Z_to_bv 64 (if b then 1 else 0)))).
Proof.
  intros g f b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  pose proof (length_le4 (Z_to_bv 64 (if b then 1 else 0))) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_ignore ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; reflexivity|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_ignore_set : forall g f b, mseg_enc g f ->
  mseg_enc (ms_set_ignore_set b g) (upd_bytes f (Z.to_nat MS_IGNORE_SET) (le4 (Z_to_bv 64 (if b then 1 else 0)))).
Proof.
  intros g f b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  pose proof (length_le4 (Z_to_bv 64 (if b then 1 else 0))) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_ignore_set ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; reflexivity|].
  split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_model_set : forall g f b, mseg_enc g f ->
  mseg_enc (ms_set_model_set b g) (upd_bytes f (Z.to_nat MS_MODEL_SET) (le4 (Z_to_bv 64 (if b then 1 else 0)))).
Proof.
  intros g f b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  pose proof (length_le4 (Z_to_bv 64 (if b then 1 else 0))) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_model_set ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; reflexivity|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_gen : forall g f z, mseg_enc g f -> 0 <= z < 2 ^ 32 ->
  mseg_enc (ms_with_gen z g) (upd_bytes f (Z.to_nat MS_GEN) (le4 (Z_to_bv 64 z))).
Proof.
  intros g f z (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hz.
  pose proof (length_le4 (Z_to_bv 64 z)) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_with_gen ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [mcx_keep H8|]. split; [mcx_keep H9|]. split; [mcx_keep H10|].
  rewrite mcx_fld_upd_same by mcx_lia. split; [lia | reflexivity].
Qed.
Lemma mseg_enc_model : forall g f s, mseg_enc g f -> (length s < 24)%nat -> ~ In 0 s ->
  Forall (fun x => 0 <= x < 256) s ->
  mseg_enc (ms_set_model s g) (upd_bytes f (Z.to_nat MS_MODEL) (zb s ++ [ZERO])).
Proof.
  intros g f s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hs Hs0 Hsf.
  pose proof (mcx_zbz_length s) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_model ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|].
  split; [apply mcx_cstr_upd; [reflexivity | mcx_lia | exact Hs | exact Hs0 | exact Hsf]|].
  split; [mcx_keep H9|]. split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_role_file : forall g f s, mseg_enc g f -> (length s < 96)%nat -> ~ In 0 s ->
  Forall (fun x => 0 <= x < 256) s ->
  mseg_enc (ms_set_role_file s g) (upd_bytes f (Z.to_nat MS_ROLE_FILE) (zb s ++ [ZERO])).
Proof.
  intros g f s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hs Hs0 Hsf.
  pose proof (mcx_zbz_length s) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_role_file ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|]. split; [mcx_keep H8|].
  split; [apply mcx_cstr_upd; [reflexivity | mcx_lia | exact Hs | exact Hs0 | exact Hsf]|].
  split; [mcx_keep H10|].
  mcx_keep H11.
Qed.
Lemma mseg_enc_ignore_file : forall g f s, mseg_enc g f -> (length s < 96)%nat -> ~ In 0 s ->
  Forall (fun x => 0 <= x < 256) s ->
  mseg_enc (ms_set_ignore_file s g) (upd_bytes f (Z.to_nat MS_IGNORE_FILE) (zb s ++ [ZERO])).
Proof.
  intros g f s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hs Hs0 Hsf.
  pose proof (mcx_zbz_length s) as Hn.
  unfold mseg_enc, fldz in *.
  cbn [ms_set_ignore_file ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [mcx_keep H2|]. split; [mcx_keep H3|]. split; [mcx_keep H4|]. split; [mcx_keep H5|].
  split; [mcx_keep H6|]. split; [mcx_keep H7|]. split; [mcx_keep H8|]. split; [mcx_keep H9|].
  split; [apply mcx_cstr_upd; [reflexivity | mcx_lia | exact Hs | exact Hs0 | exact Hsf]|].
  mcx_keep H11.
Qed.
(** A new entry: memset(g, 0, 256), memcpy(g->name, nm, |nm|), g->gen = z. *)
Lemma mseg_enc_new : forall nm z, (length nm < 16)%nat -> ~ In 0 nm -> Forall (fun x => 0 <= x < 256) nm ->
  0 <= z < 2 ^ 32 ->
  mseg_enc (ms_with_gen z (mseg0 nm))
    (upd_bytes (upd_bytes (repeat ZERO 256) 0 (zb nm)) (Z.to_nat MS_GEN) (le4 (Z_to_bv 64 z))).
Proof.
  intros nm z Hnm Hn0 Hnf Hz.
  rewrite (mcx_upd_zeros_nul 256 nm) by lia.
  pose proof (mcx_zbz_length nm) as Hnz. pose proof (length_le4 (Z_to_bv 64 z)) as Hn4.
  pose proof (repeat_length ZERO 256) as HR.
  assert (HL0 : length (upd_bytes (repeat ZERO 256) 0 (zb nm ++ [ZERO])) = 256%nat)
    by (rewrite upd_bytes_length by lia; exact HR).
  unfold mseg_enc, fldz.
  cbn [ms_with_gen mseg0 ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [rewrite upd_bytes_length by mcx_lia; exact HL0|].
  split; [mcx_out; apply mcx_cstr_upd; [reflexivity | lia | exact Hnm | exact Hn0 | exact Hnf]|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; split; [exact u32_enc_zero | lia]|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact flag_enc_false_zero|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 24 ltac:(lia))|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  split; [mcx_out; mcx_out; rewrite fld_repeat by mcx_lia; exact (cstr_enc_nil_zero 96 ltac:(lia))|].
  rewrite mcx_fld_upd_same by mcx_lia. split; [lia | reflexivity].
Qed.

(** ** The edits on the 9236 bytes of the block *)
Lemma mconf_enc_gen : forall pend mc bs z, mconf_encp pend mc bs -> 0 <= z < 2 ^ 32 ->
  mconf_encp pend (mc_set_gen z mc) (upd_bytes bs (Z.to_nat MC_GEN) (le4 (Z_to_bv 64 z))).
Proof.
  intros pend mc bs z (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hz.
  pose proof (length_le4 (Z_to_bv 64 z)) as Hn.
  unfold mconf_encp, fldz in *.
  cbn [mc_set_gen mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; mcx_out; apply H3; exact Hi|].
  split; [mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; split; [lia | reflexivity]|].
  mcx_keep H12.
Qed.
Lemma mconf_enc_overflow : forall pend mc bs z, mconf_encp pend mc bs -> 0 <= z < 2 ^ 32 ->
  mconf_encp pend (mc_set_overflow z mc) (upd_bytes bs (Z.to_nat MC_OVERFLOW) (le4 (Z_to_bv 64 z))).
Proof.
  intros pend mc bs z (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hz.
  pose proof (length_le4 (Z_to_bv 64 z)) as Hn.
  unfold mconf_encp, fldz in *.
  cbn [mc_set_overflow mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; mcx_out; apply H3; exact Hi|].
  split; [mcx_keep H4|].
  split; [rewrite mcx_fld_upd_same by mcx_lia; split; [lia | reflexivity]|].
  split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  mcx_keep H12.
Qed.
Lemma mconf_enc_reading : forall pend mc bs s, mconf_encp pend mc bs -> (length s < 96)%nat -> ~ In 0 s ->
  Forall (fun x => 0 <= x < 256) s ->
  mconf_encp pend (mc_set_reading s mc) (upd_bytes bs (Z.to_nat MC_READING) (zb s ++ [ZERO])).
Proof.
  intros pend mc bs s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hs Hs0 Hsf.
  pose proof (mcx_zbz_length s) as Hn.
  unfold mconf_encp, fldz in *.
  cbn [mc_set_reading mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; mcx_out; apply H3; exact Hi|].
  split; [mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  apply mcx_cstr_upd; [reflexivity | mcx_lia | exact Hs | exact Hs0 | exact Hsf].
Qed.
(** An edit of entry gi (k + |nb| <= 256: inside the entry), given the entry-level edit. *)
Lemma mconf_enc_seg : forall pend mc bs gi (f : mseg -> mseg) k nb, mconf_encp pend mc bs ->
  (gi < length (mc_seg mc))%nat -> (k + length nb <= 256)%nat ->
  (forall fb, mseg_enc (nth gi (mc_seg mc) mseg_d) fb -> mseg_enc (f (nth gi (mc_seg mc) mseg_d)) (upd_bytes fb k nb)) ->
  mconf_encp pend (m_upd mc gi f) (upd_bytes bs (256 * gi + k) nb).
Proof.
  intros pend mc bs gi f k nb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hgi Hk Hf.
  pose proof (mcx_upd_nth_length gi f (mc_seg mc)) as HU.
  unfold m_upd, m_set_segs, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [rewrite HU; exact H2|].
  split.
  { intros i Hi. rewrite HU in Hi. destruct (Nat.eq_dec i gi) as [->|Hne].
    - rewrite mcx_upd_nth_same by exact Hgi. rewrite mcx_fld_upd_sub by mcx_lia.
      apply Hf. apply H3. exact Hgi.
    - rewrite mcx_upd_nth_other by lia. mcx_out. apply H3. exact Hi. }
  split; [rewrite HU; mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; apply H9; exact Hi|].
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  mcx_keep H12.
Qed.
(** A new entry at n < 32 and n++. *)
Lemma mconf_enc_append : forall pend mc bs g gb, mconf_encp pend mc bs -> (length (mc_seg mc) < 32)%nat ->
  mseg_enc g gb ->
  mconf_encp pend (m_set_segs mc (mc_seg mc ++ [g]))
    (upd_bytes (upd_bytes bs (256 * length (mc_seg mc)) gb) (Z.to_nat MC_N)
       (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1)))).
Proof.
  intros pend mc bs g gb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hn32 Hg.
  pose proof Hg as (Hgl & _).
  pose proof (length_le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc)) + 1))) as Hn.
  assert (HL2 : Z.of_nat (length (upd_bytes bs (256 * length (mc_seg mc)) gb)) = SEG_M_SIZE)
    by (rewrite upd_bytes_length by mcx_lia; exact H1).
  unfold m_set_segs, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split; [rewrite upd_bytes_length by mcx_lia; exact HL2|].
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. mcx_out.
    destruct (Nat.lt_ge_cases i (length (mc_seg mc))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt. mcx_out. apply H3. exact Hlt.
    - assert (Ei : i = length (mc_seg mc)) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite mcx_fld_upd_same by mcx_lia. exact Hg. }
  split.
  { rewrite mcx_fld_upd_same by mcx_lia. rewrite length_app. cbn [length].
    replace (Z.of_nat (length (mc_seg mc) + 1)) with (Z.of_nat (length (mc_seg mc)) + 1) by lia.
    split; [lia | reflexivity]. }
  split; [mcx_out; mcx_keep H5|]. split; [mcx_out; mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_out; mcx_keep Ha | mcx_out; mcx_keep Hb]|].
  split; [intros i Hi; mcx_out; mcx_out; apply H9; exact Hi|].
  split; [mcx_out; mcx_keep H10|]. split; [mcx_out; mcx_keep H11|].
  mcx_out; mcx_keep H12.
Qed.
(** The knock flag kept_knock[n_kept] = 1 before m_refuse (n_kept < 8): the pending flag. *)
Lemma mconf_enc_knock : forall mc bs, mconf_enc mc bs -> (length (mc_kept mc) < 8)%nat ->
  mconf_encp true mc (upd_bytes bs (Z.to_nat MC_KNOCK + 4 * length (mc_kept mc)) (le4 (Z_to_bv 64 1))).
Proof.
  intros mc bs He Hk. unfold mconf_enc in He.
  destruct He as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  pose proof (length_le4 (Z_to_bv 64 1)) as Hn.
  unfold mconf_encp, fldz in *.
  split; [rewrite upd_bytes_length by mcx_lia; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; mcx_out; apply H3; exact Hi|].
  split; [mcx_keep H4|]. split; [mcx_keep H5|]. split; [mcx_keep H6|].
  split; [exact H7|].
  split; [intros i Hi; destruct (H8 i Hi) as [Ha Hb]; split; [mcx_keep Ha | mcx_keep Hb]|].
  split.
  { intros i Hi. destruct (Nat.eqb_spec i (length (mc_kept mc))) as [->|Hne].
    - rewrite mcx_fld_upd_same by mcx_lia. reflexivity.
    - mcx_out. exact (H9 i Hi). }
  split; [mcx_keep H10|]. split; [mcx_keep H11|].
  mcx_keep H12.
Qed.
(** With kept full the pending flag says nothing. *)
Lemma mconf_encp_full : forall pend pend' mc bs, (length (mc_kept mc) = 8)%nat ->
  mconf_encp pend mc bs -> mconf_encp pend' mc bs.
Proof.
  intros pend pend' mc bs Hk (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold mconf_encp.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  split; [intros i Hi; exfalso; lia|].
  split; [exact H10|]. split; [exact H11|]. exact H12.
Qed.

(** ** In memory *)
Section Mem.
Variable segs : list Segment.

(** The bytes [off, off + n) of a block at a are at a + off. *)
Lemma mcx_bytes_at_fldz : forall m a bs off n, bytes_at segs m a bs -> 0 <= off -> 0 <= n ->
  (Z.to_nat off + Z.to_nat n <= length bs)%nat -> bytes_at segs m (a + off) (fldz off n bs).
Proof.
  intros m a bs off n H H0 H1 L. unfold fldz, fld.
  rewrite <- (firstn_skipn (Z.to_nat off) bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat off) bs)) in H. apply bytes_at_app in H as [H _].
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma mconf_atp_bytes : forall pend m c mc, mconf_atp segs pend m c mc ->
  exists bs, bytes_at segs m c bs /\ mconf_encp pend mc bs /\ length bs = 9236%nat.
Proof.
  intros pend m c mc (bs & Hb & He). exists bs. split; [exact Hb|]. split; [exact He|].
  destruct He as (H1 & _). apply Nat2Z.inj. rewrite H1. reflexivity.
Qed.

Lemma mconf_atp_transport : forall pend m m' c mc W, mconf_atp segs pend m c mc -> munch W m m' ->
  disjoint_from W c SEG_M_SIZE -> mconf_atp segs pend m' c mc.
Proof.
  intros pend m m' c mc W (bs & Hb & He) Hmu Hd. exists bs. split; [|exact He].
  pose proof He as (H1 & _). eapply bytes_at_transport; [exact Hb | exact Hmu | rewrite H1; exact Hd].
Qed.

(** After writes W whose part inside the block is the range [a, a + |nb|), which now holds nb. *)
Lemma mconf_atp_upd : forall pend pend' m m' c mc mc' a nb W,
  mconf_atp segs pend m c mc -> munch W m m' ->
  (forall x : Z, c <= x < c + SEG_M_SIZE -> ~ outside W x -> a <= x < a + Z.of_nat (length nb)) ->
  bytes_at segs m' a nb -> c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE ->
  (forall bs, mconf_encp pend mc bs -> mconf_encp pend' mc' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  mconf_atp segs pend' m' c mc'.
Proof.
  intros pend pend' m m' c mc mc' a nb W (bs & Hb & He) Hmu Hin Hnb Hca Hac Hed.
  exists (upd_bytes bs (Z.to_nat (a - c)) nb). split; [|apply Hed; exact He].
  pose proof He as (H1 & _). unfold SEG_M_SIZE in *.
  pose proof Hb as (Hc0 & Hcl & Hbs). pose proof Hnb as (Ha0 & Hal & Hnbs).
  split; [lia|]. split; [rewrite upd_bytes_length by lia; lia|].
  intros i Hi. rewrite upd_bytes_length in Hi by lia.
  assert (Hout : ~ (a <= c + Z.of_nat i < a + Z.of_nat (length nb)) ->
                 mrd segs m' (wa (c + Z.of_nat i)) = nth_error bs i).
  { intros Hx. rewrite <- (Hbs i Hi). unfold mrd. rewrite (Hmu (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. destruct (mcx_outside_dec W (c + Z.of_nat i)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. apply Hin; [lia | exact Ho]. }
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec0 (Z.to_nat (a - c)) i); destruct (Nat.ltb_spec0 i (Z.to_nat (a - c) + length nb));
    cbn [andb]; [| apply Hout; lia | apply Hout; lia | apply Hout; lia].
  replace (c + Z.of_nat i) with (a + Z.of_nat (i - Z.to_nat (a - c))) by lia. apply Hnbs. lia.
Qed.

(** A store (the step's write_to_mem) inside the block. *)
Lemma mconf_atp_store : forall pend pend' m c mc mc' a nb,
  mconf_atp segs pend m c mc -> c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE ->
  (forall bs, mconf_encp pend mc bs -> mconf_encp pend' mc' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  mconf_atp segs pend' (write_to_mem m (wa a) nb) c mc'.
Proof.
  intros pend pend' m c mc mc' a nb (bs & Hb & He) Hca Hac Hed.
  pose proof He as (H1 & _).
  exists (upd_bytes bs (Z.to_nat (a - c)) nb). split; [|apply Hed; exact He].
  replace (wa a) with (wa (c + (a - c))) by (f_equal; lia).
  apply bytes_at_write_inside; [exact Hb | lia | unfold SEG_M_SIZE in *; lia].
Qed.

(** The fields the code loads. *)
Lemma mconf_rd_n : forall pend m c mc, mconf_atp segs pend m c mc ->
  ov_read_bytes segs m (wa (c + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc))))).
Proof.
  intros pend m c mc (bs & Hb & He). destruct He as (H1 & _ & _ & (_ & H4) & _).
  unfold fldz in H4. rewrite (bytes_at_read segs m c bs MC_N 4 Hb) by (unfold MC_N, SEG_M_SIZE in *; lia).
  f_equal. exact H4.
Qed.
Lemma mconf_rd_overflow : forall pend m c mc, mconf_atp segs pend m c mc ->
  ov_read_bytes segs m (wa (c + MC_OVERFLOW)) 4 = Some (le4 (Z_to_bv 64 (mc_overflow mc))).
Proof.
  intros pend m c mc (bs & Hb & He). destruct He as (H1 & _ & _ & _ & (_ & H5) & _).
  unfold fldz in H5.
  rewrite (bytes_at_read segs m c bs MC_OVERFLOW 4 Hb) by (unfold MC_OVERFLOW, SEG_M_SIZE in *; lia).
  f_equal. exact H5.
Qed.
Lemma mconf_rd_nkept : forall pend m c mc, mconf_atp segs pend m c mc ->
  ov_read_bytes segs m (wa (c + MC_NKEPT)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))).
Proof.
  intros pend m c mc (bs & Hb & He). destruct He as (H1 & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H10) & _).
  unfold fldz in H10.
  rewrite (bytes_at_read segs m c bs MC_NKEPT 4 Hb) by (unfold MC_NKEPT, SEG_M_SIZE in *; lia).
  f_equal. exact H10.
Qed.
Lemma mconf_rd_gen : forall pend m c mc, mconf_atp segs pend m c mc ->
  ov_read_bytes segs m (wa (c + MC_GEN)) 4 = Some (le4 (Z_to_bv 64 (mc_gen mc))).
Proof.
  intros pend m c mc (bs & Hb & He). destruct He as (H1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H11) & _).
  unfold fldz in H11.
  rewrite (bytes_at_read segs m c bs MC_GEN 4 Hb) by (unfold MC_GEN, SEG_M_SIZE in *; lia).
  f_equal. exact H11.
Qed.
Lemma mconf_rd_seg_gen : forall pend m c mc gi, mconf_atp segs pend m c mc -> (gi < length (mc_seg mc))%nat ->
  ov_read_bytes segs m (wa (mseg_addr c gi + MS_GEN)) 4 = Some (le4 (Z_to_bv 64 (ms_gen (nth gi (mc_seg mc) mseg_d)))).
Proof.
  intros pend m c mc gi (bs & Hb & He) Hgi.
  destruct He as (H1 & H2 & H3 & _).
  destruct (H3 gi Hgi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hg)).
  unfold fldz in Hg. rewrite mcx_fld_fld in Hg by (unfold MS_GEN; lia).
  replace (mseg_addr c gi + MS_GEN) with (c + Z.of_nat (256 * gi + Z.to_nat MS_GEN))
    by (unfold mseg_addr, MSEG_SIZE, MS_GEN; lia).
  rewrite (bytes_at_ov_read segs m c bs _ _ Hb) by (unfold MS_GEN, SEG_M_SIZE in *; lia).
  f_equal. exact Hg.
Qed.
(** The reading string with its slack (c 8-aligned: its slack is inside the field or in the block's slack). *)
Lemma mconf_reading_cstr : forall pend m c mc, mconf_atp segs pend m c mc -> blk_slack segs m c SEG_M_SIZE ->
  c mod 8 = 0 -> cstr_at segs m (c + MC_READING) (mc_reading mc).
Proof.
  intros pend m c mc (bs & Hb & He) (sl & Hsl & Hsl8) Hc8.
  destruct He as (H1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12).
  pose proof H12 as (Hfl & Hs96 & Hn0 & Hz).
  destruct (mcx_cstr_bytes _ _ Hz) as (bs0 & rest & Hf & Hzs).
  assert (Hw : bytes_at segs m (c + MC_READING) (fldz MC_READING 96 bs)).
  { apply mcx_bytes_at_fldz; [exact Hb | unfold MC_READING; lia | lia | unfold MC_READING, SEG_M_SIZE in *; lia]. }
  rewrite Hf in Hw, Hfl.
  assert (Hl0 : length bs0 = length (mc_reading mc)) by (rewrite <- Hzs; unfold zs; rewrite length_map; reflexivity).
  rewrite length_app in Hfl. cbn [length] in Hfl.
  exists bs0, (rest ++ sl).
  split; [|split; [exact Hzs | split; [exact Hn0 |]]].
  - replace (bs0 ++ ZERO :: rest ++ sl) with ((bs0 ++ ZERO :: rest) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact Hw|].
    replace (c + MC_READING + Z.of_nat (length (bs0 ++ ZERO :: rest))) with (c + SEG_M_SIZE)
      by (rewrite length_app; cbn [length]; unfold MC_READING, SEG_M_SIZE; lia).
    exact Hsl.
  - rewrite length_app, Nat2Z.inj_add. unfold MC_READING, SEG_M_SIZE in *.
    apply mcx_slack; [exact Hc8 | lia | lia | lia | exact Hsl8].
Qed.
(** The 96 bytes of a file field of entry gi, and the reading field, as writable cells (an snprintf destination). *)
Lemma mconf_field_cells : forall pend m c mc off, mconf_atp segs pend m c mc -> wr_at segs m c SEG_M_SIZE ->
  0 <= off -> off + 96 <= SEG_M_SIZE -> exists junk, rw_cells segs m (c + off) [CB 96 junk].
Proof.
  intros pend m c mc off (bs & Hb & He) Hw Hoff Hoff2.
  pose proof He as (H1 & _). unfold SEG_M_SIZE in *.
  exists (fldz off 96 bs). split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. unfold fldz. rewrite mcx_fld_length by lia. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply mcx_bytes_at_fldz; [exact Hb | lia | lia | lia].
  - destruct Hw as (Hw0 & Hw1 & Hw2). cbn [cells_size csize]. split; [lia|]. split; [lia|].
    intros i Hi. replace (c + off + i) with (c + (off + i)) by lia. apply Hw2. lia.
Qed.

End Mem.
