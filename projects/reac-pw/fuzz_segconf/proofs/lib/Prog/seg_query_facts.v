(** reac-pw/fuzz_segconf: facts the walks of the reader's queries share (reac_segconf_find and the accessors
    ignored / role / role_file / ignore_file / model; plain lib/Prog and UBSan lib/U/Prog). Build-independent, as
    seg_spec.v: the memory lemmas take the build's segment list.
    - The model: SegModel.strcmp of two NUL-free strings is 0 exactly when they are equal, and the steps of
      SegModel.r_find_go that find's loop takes.
    - The memory: what a struct reac_segconf holding rc (seg_spec.rconf_enc of the bytes bs at c) gives a load: c->n,
      the name of c->seg[i] with its NUL (strcmp's premise), and the fields of c->seg[i] the accessors read. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** The model *)
Lemma sq_strcmp_eq0 : forall l r, ~ In 0 l -> ~ In 0 r -> (strcmp l r = 0 <-> l = r).
Proof.
  induction l as [|a l IH]; intros [|b r] Hl Hr; cbn [strcmp].
  - split; reflexivity.
  - split; [|discriminate]. intros H. exfalso. apply Hr. left. lia.
  - split; [|discriminate]. intros H. exfalso. apply Hl. left. exact H.
  - destruct (Z.eqb_spec a b) as [E|E]; destruct (Z.eqb_spec a 0) as [E0|E0]; cbn [andb negb].
    + exfalso. apply Hl. left. exact E0.
    + subst b. rewrite IH by (intros H; first [apply Hl; right; exact H | apply Hr; right; exact H]).
      split; [intros ->; reflexivity | intros H; injection H as H; exact H].
    + exfalso. apply Hl. left. exact E0.
    + split; [intros H; lia | intros H; injection H as H _; contradiction].
Qed.

Lemma sq_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(** One pass of find's loop: entry k of the table, then the rest. *)
Lemma sq_find_go_step : forall segs nm k, (k < length segs)%nat ->
  r_find_go (skipn k segs) nm k =
  if strcmp (rs_name (nth k segs rseg_d)) nm =? 0 then Some k else r_find_go (skipn (S k) segs) nm (S k).
Proof. intros segs nm k H. rewrite (sq_skipn_cons segs k rseg_d H). reflexivity. Qed.

Lemma sq_find_go_end : forall segs nm, r_find_go (skipn (length segs) segs) nm (length segs) = None.
Proof. intros segs nm. rewrite skipn_all. reflexivity. Qed.

Lemma sq_find_go_lt : forall segs nm k i, r_find_go segs nm k = Some i -> (k <= i < k + length segs)%nat.
Proof.
  induction segs as [|s segs IH]; intros nm k i H; cbn [r_find_go] in H; [discriminate|].
  destruct (strcmp (rs_name s) nm =? 0); [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.

Lemma sq_find_lt : forall rc nm i, r_find rc nm = Some i -> (i < length (rc_seg rc))%nat.
Proof. intros rc nm i H. apply sq_find_go_lt in H. lia. Qed.

(** ** Bytes *)
Lemma sq_byte_eq : forall x y : byte, bv_unsigned x = bv_unsigned y -> x = y.
Proof. intros x y H. apply bv_eq. exact H. Qed.

Lemma sq_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma sq_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma sq_zs_nul : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof.
  intros bs H Hin. apply H. unfold zs. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply in_map. exact Hin.
Qed.

Lemma sq_zs_inj : forall a b : list byte, zs a = zs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply sq_byte_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma sq_fld_fld : forall (l : list byte) a n b k, (a + n <= k)%nat -> fld a n (fld b k l) = fld (b + a) n l.
Proof.
  intros l a n b k H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite Nat.min_l by lia. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma sq_firstn_S : forall (l : list byte) n d, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction l as [|x l IH]; intros n d H; cbn [length] in H; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

(** ** Memory *)
Section Mem.
Variable segs : list Segment.

Lemma sq_bytes_at_sub : forall m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H L.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** The facts of a struct reac_segconf the queries use. *)
Lemma sq_rconf_len : forall rc bs, rconf_enc rc bs -> Z.of_nat (length bs) = 16616 /\ (length (rc_seg rc) <= 32)%nat.
Proof. intros rc bs (L & LS & _). unfold SEG_C_SIZE in L. split; [exact L | exact LS]. Qed.

Lemma sq_rseg : forall rc bs i, rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  rseg_enc (r_seg rc i) (fld (356 * i) 356 bs).
Proof. intros rc bs i (_ & _ & H & _) Hi. exact (H i Hi). Qed.

(** c->n: the 4 bytes at c + 0x2c80. *)
Lemma sq_rc_n : forall m c bs rc, bytes_at segs m c bs -> rconf_enc rc bs ->
  ov_read_bytes segs m (wa (c + RC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc))))).
Proof.
  intros m c bs rc HB HE. destruct (sq_rconf_len rc bs HE) as [L _].
  destruct HE as (_ & _ & _ & (_ & HN) & _). unfold fldz in HN.
  rewrite (bytes_at_read segs m c bs RC_N 4 HB) by (unfold RC_N; lia).
  rewrite <- HN. reflexivity.
Qed.

(** A 4-byte field at offset off of c->seg[i]. *)
Lemma sq_seg_read4 : forall m c bs rc i off, bytes_at segs m c bs -> rconf_enc rc bs ->
  (i < length (rc_seg rc))%nat -> 0 <= off -> off + 4 <= 356 ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + off)) 4 = Some (fldz off 4 (fld (356 * i) 356 bs)).
Proof.
  intros m c bs rc i off HB HE Hi H0 H1. destruct (sq_rconf_len rc bs HE) as [L LS].
  replace (c + 356 * Z.of_nat i + off) with (c + (356 * Z.of_nat i + off)) by lia.
  rewrite (bytes_at_read segs m c bs _ 4 HB) by lia.
  unfold fldz. rewrite sq_fld_fld by lia. unfold fld.
  replace (Z.to_nat (356 * Z.of_nat i + off)) with (356 * i + Z.to_nat off)%nat by lia. reflexivity.
Qed.

Lemma sq_seg_flag : forall m c bs rc i off (b : bool), bytes_at segs m c bs -> rconf_enc rc bs ->
  (i < length (rc_seg rc))%nat -> 0 <= off -> off + 4 <= 356 ->
  flag_enc b (fldz off 4 (fld (356 * i) 356 bs)) ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + off)) 4 = Some (le4 (Z_to_bv 64 (b2z b))).
Proof.
  intros m c bs rc i off b HB HE Hi H0 H1 HF. rewrite (sq_seg_read4 m c bs rc i off HB HE Hi H0 H1).
  rewrite HF. reflexivity.
Qed.

(** The flags and the role of c->seg[i], as loads give them. *)
Lemma sq_role_set : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_ROLE_SET)) 4 = Some (le4 (Z_to_bv 64 (b2z (rs_role_set (r_seg rc i))))).
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_flag m c bs rc i _ _ HB HE Hi); [unfold RS_ROLE_SET; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & H & _). exact H.
Qed.

Lemma sq_ignore : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_IGNORE)) 4 = Some (le4 (Z_to_bv 64 (b2z (rs_ignore (r_seg rc i))))).
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_flag m c bs rc i _ _ HB HE Hi); [unfold RS_IGNORE; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & H & _). exact H.
Qed.

Lemma sq_ignore_set : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_IGNORE_SET)) 4 = Some (le4 (Z_to_bv 64 (b2z (rs_ignore_set (r_seg rc i))))).
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_flag m c bs rc i _ _ HB HE Hi); [unfold RS_IGNORE_SET; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma sq_model_set : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_MODEL_SET)) 4 = Some (le4 (Z_to_bv 64 (b2z (rs_model_set (r_seg rc i))))).
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_flag m c bs rc i _ _ HB HE Hi); [unfold RS_MODEL_SET; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma sq_role : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  0 <= rs_role (r_seg rc i) < 2 ^ 32 /\
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_ROLE)) 4 = Some (le4 (Z_to_bv 64 (rs_role (r_seg rc i)))).
Proof.
  intros m c bs rc i HB HE Hi.
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & [[R H] _] & _). split; [exact R|].
  rewrite (sq_seg_read4 m c bs rc i RS_ROLE HB HE Hi) by (unfold RS_ROLE; lia). rewrite H. reflexivity.
Qed.

(** The first byte of a char[96] field at offset off of c->seg[i] holding the C string s: the byte hd0 s. *)
Lemma sq_seg_byte0 : forall m c bs rc i off s, bytes_at segs m c bs -> rconf_enc rc bs ->
  (i < length (rc_seg rc))%nat -> 0 <= off -> off + 96 <= 356 ->
  cstr_enc 96 s (fldz off 96 (fld (356 * i) 356 bs)) ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + off)) 1 = Some [Z_to_bv 8 (hd0 s)].
Proof.
  intros m c bs rc i off s HB HE Hi H0 H1 (HL & _ & _ & HF). destruct (sq_rconf_len rc bs HE) as [L LS].
  replace (c + 356 * Z.of_nat i + off) with (c + (356 * Z.of_nat i + off)) by lia.
  rewrite (bytes_at_read segs m c bs _ 1 HB) by lia.
  unfold fldz in HL, HF. rewrite sq_fld_fld in HL, HF by lia.
  replace (Z.to_nat (356 * Z.of_nat i + off)) with (356 * i + Z.to_nat off)%nat by lia.
  replace (firstn 1 (skipn (356 * i + Z.to_nat off) bs)) with (firstn 1 (fld (356 * i + Z.to_nat off) (Z.to_nat 96) bs))
    by (unfold fld; rewrite firstn_firstn; reflexivity).
  remember (fld (356 * i + Z.to_nat off) (Z.to_nat 96) bs) as f eqn:Ef.
  destruct f as [|x f']; [cbn in HL; lia|]. cbn [firstn].
  unfold zs in HF. apply (f_equal (hd 0)) in HF. cbn [hd map firstn] in HF.
  replace (hd 0 (s ++ [0])) with (hd0 s) in HF by (destruct s; reflexivity).
  rewrite <- HF, sq_byte_lit. reflexivity.
Qed.

Lemma sq_role_file0 : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_ROLE_FILE)) 1 = Some [Z_to_bv 8 (hd0 (rs_role_file (r_seg rc i)))].
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_byte0 m c bs rc i _ _ HB HE Hi); [unfold RS_ROLE_FILE; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma sq_ignore_file0 : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  ov_read_bytes segs m (wa (c + 356 * Z.of_nat i + RS_IGNORE_FILE)) 1 = Some [Z_to_bv 8 (hd0 (rs_ignore_file (r_seg rc i)))].
Proof.
  intros m c bs rc i HB HE Hi. apply (sq_seg_byte0 m c bs rc i _ _ HB HE Hi); [unfold RS_IGNORE_FILE; lia..|].
  destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

(** That first byte is a byte value: 0 <= hd0 s < 256 (the walks need it where the byte is not 0). *)
Lemma sq_cstr_hd0_range : forall cap s f, cstr_enc cap s f -> 0 <= hd0 s < 256.
Proof.
  intros cap s f (_ & _ & _ & HF). destruct s as [|h s]; cbn [hd0]; [lia|].
  unfold zs in HF. destruct f as [|b f]; [cbn in HF; discriminate|].
  cbn [map firstn length app] in HF. injection HF as H _. rewrite <- H. apply sq_byte_range.
Qed.

Lemma sq_role_file0_range : forall rc bs i, rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  0 <= hd0 (rs_role_file (r_seg rc i)) < 256.
Proof.
  intros rc bs i HE Hi. destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (sq_cstr_hd0_range _ _ _ H).
Qed.

Lemma sq_ignore_file0_range : forall rc bs i, rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  0 <= hd0 (rs_ignore_file (r_seg rc i)) < 256.
Proof.
  intros rc bs i HE Hi. destruct (sq_rseg rc bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (sq_cstr_hd0_range _ _ _ H).
Qed.

(** The name of c->seg[i] with its NUL, strcmp's premise. *)
Lemma sq_seg_name : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  exists sx, bytes_at segs m (c + 356 * Z.of_nat i) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
    zs sx = rs_name (r_seg rc i) /\ ~ In 0 (rs_name (r_seg rc i)).
Proof.
  intros m c bs rc i HB HE Hi. destruct (sq_rconf_len rc bs HE) as [L LS].
  destruct (sq_rseg rc bs i HE Hi) as (_ & (HL & Hlt & HN & HF) & _).
  rewrite sq_fld_fld in HL, HF by lia. rewrite Nat.add_0_r in HL, HF.
  remember (rs_name (r_seg rc i)) as s eqn:Es.
  remember (fld (356 * i) 16 bs) as g eqn:Eg.
  exists (firstn (length s) g).
  assert (G : firstn (S (length s)) g = firstn (length s) g ++ [nth (length s) g ZERO]) by (apply sq_firstn_S; lia).
  unfold zs in HF. rewrite firstn_map, G, map_app in HF. cbn [map] in HF.
  apply app_inj_tail in HF as [H1 H2].
  assert (Z0 : nth (length s) g ZERO = Z_to_bv 8 0) by (apply sq_byte_eq; rewrite H2; reflexivity).
  split; [|split; [|split; [exact H1 | exact HN]]].
  - rewrite <- Z0, <- G. subst g. unfold fld. rewrite firstn_firstn, Nat.min_l by lia.
    replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
    apply sq_bytes_at_sub; [exact HB | lia].
  - apply sq_zs_nul. unfold zs. rewrite H1. exact HN.
Qed.

End Mem.

(** ** Addresses *)
(** c->seg[i] for i < 32 lies inside the block, so its address is nonzero and 4-aligned. *)
Lemma sq_seg_addr : forall c i, 0 < c -> c + 16616 <= 2 ^ 64 -> (i < 32)%nat ->
  0 < c + 356 * Z.of_nat i /\ c + 356 * Z.of_nat i + 356 <= 2 ^ 64.
Proof. intros c i H0 H1 Hi. lia. Qed.

Lemma sq_seg_mod4 : forall c i, c mod 16 = 0 -> (c + 356 * Z.of_nat i) mod 4 = 0.
Proof. intros c i H. Z.div_mod_to_equations. lia. Qed.

Lemma sq_find_ptr : forall c rc nm, find_ptr c rc nm =
  match r_find rc nm with Some i => c + 356 * Z.of_nat i | None => 0 end.
Proof. intros c rc nm. reflexivity. Qed.

(** strcmp's answer on the bytes of two C strings is the model's on their values. *)
Lemma sq_name_cmp : forall (sx sy : list byte) s nm, zs sx = s -> zs sy = nm -> ~ In 0 s -> ~ In 0 nm ->
  (sx = sy <-> strcmp s nm = 0).
Proof.
  intros sx sy s nm Hx Hy Hs Hn. rewrite sq_strcmp_eq0 by assumption. split.
  - intros ->. congruence.
  - intros E. apply sq_zs_inj. congruence.
Qed.

(** ** Words: the conditions and loads the walks meet *)
Lemma sq_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sq_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma sq_eqb_false : forall x y : word, bv_eqb x y = false -> x <> y.
Proof. intros x y H E. subst y. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.

(** `lw` of a small non-negative word. *)
Lemma sq_sx32 : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** The 4 bytes `sw` writes of the sign-extended `lw` of le4 v are le4 v. *)
Lemma sq_le4_sx32 : forall v, 0 <= v < 2 ^ 32 -> le4 (sx32 (Z_to_bv 64 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v Hv. unfold le4, sx32. rewrite !unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 (bv_swrap 32 (v mod 2 ^ 64)) 64) by lia.
  rewrite (Z_to_le_bytes_mod 4 v 64) by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32), <- (Z_to_le_bytes_mod 4 v 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
