From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table bcmp_c memset_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_observe_c.
Import ListNotations.
Open Scope Z_scope.

Lemma list_ext_nth : forall {X} (l1 l2 : list X), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros [|b l2] L H; cbn in L; try lia; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. inversion H0. subst b. f_equal.
  apply IH; [lia|]. intros i Hi. apply (H (S i)). cbn. lia.
Qed.

Lemma upd_len : forall X k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length (upd X k v) = length X.
Proof. intros X k v Hk H. unfold upd. apply upd_bytes_length. lia. Qed.

Lemma nth_sub : forall X k n j, 0 <= k -> (j < n)%nat ->
  nth_error (sub X k n) j = nth_error X (Z.to_nat k + j).
Proof. intros X k n j Hk Hj. unfold sub. rewrite nth_firstn by exact Hj. apply nth_skipn. Qed.

Lemma sub_upd_other : forall X k v j n, 0 <= k -> 0 <= j ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) -> j + Z.of_nat n <= Z.of_nat (length X) ->
  j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j ->
  sub (upd X k v) j n = sub X j n.
Proof.
  intros X k v j n Hk Hj Hv Hn D.
  assert (LU : length (upd X k v) = length X) by (apply upd_len; lia).
  apply list_ext_nth.
  - rewrite !length_sub by (try rewrite LU; lia). reflexivity.
  - intros i Hi. rewrite length_sub in Hi by (try rewrite LU; lia).
    rewrite !nth_sub by lia. unfold upd. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j + i));
      destruct (Nat.ltb_spec (Z.to_nat j + i) (Z.to_nat k + length v)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma sub_upd_in : forall X k v j n, 0 <= k -> k <= j ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) -> j + Z.of_nat n <= k + Z.of_nat (length v) ->
  sub (upd X k v) j n = sub v (j - k) n.
Proof.
  intros X k v j n Hk Hj Hv Hn.
  assert (LU : length (upd X k v) = length X) by (apply upd_len; lia).
  apply list_ext_nth.
  - rewrite !length_sub by (try rewrite LU; lia). reflexivity.
  - intros i Hi. rewrite length_sub in Hi by (try rewrite LU; lia).
    rewrite !nth_sub by lia. unfold upd. rewrite upd_bytes_nth by lia.
    destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j + i));
      destruct (Nat.ltb_spec (Z.to_nat j + i) (Z.to_nat k + length v)); cbn [andb]; try lia.
    f_equal. lia.
Qed.

Lemma sub_all : forall v, sub v 0 (length v) = v.
Proof. intros v. unfold sub. cbn [Z.to_nat skipn]. apply firstn_all. Qed.

Lemma sub_if_other : forall (c : bool) X k v j n, 0 <= k -> 0 <= j ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) -> j + Z.of_nat n <= Z.of_nat (length X) ->
  j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j ->
  sub (if c then upd X k v else X) j n = sub X j n.
Proof. intros [|] X k v j n Hk Hj Hv Hn D; [apply sub_upd_other; assumption | reflexivity]. Qed.

Lemma len_if : forall (c : bool) X k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length (if c then upd X k v else X) = length X.
Proof. intros [|] X k v Hk H; [apply upd_len; assumption | reflexivity]. Qed.

Lemma upd_split : forall X k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  upd X k v = sub X 0 (Z.to_nat k) ++ v ++
              sub X (k + Z.of_nat (length v)) (Z.to_nat (Z.of_nat (length X) - k - Z.of_nat (length v))).
Proof.
  intros X k v Hk H. unfold upd, upd_bytes, sub. cbn [Z.to_nat skipn]. f_equal. f_equal.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (Z.to_nat k + length v)%nat by lia.
  rewrite firstn_all2; [reflexivity|]. rewrite skipn_length. lia.
Qed.

Lemma u_at_range : forall bs k n, 0 <= u_at bs k n < 2 ^ (8 * Z.of_nat n).
Proof.
  intros bs k n. unfold u_at. pose proof (ble_range (sub bs k n)) as H.
  assert (L : (length (sub bs k n) <= n)%nat) by (unfold sub; rewrite firstn_length; lia).
  split; [lia|]. eapply Z.lt_le_trans; [apply H|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma swrap_mod : forall n u, bv_swrap n u mod bv_modulus n = u mod bv_modulus n.
Proof. intros n u. unfold bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

Lemma le8_word : forall x, le8 (Z_to_bv 64 x) = Z_to_le_bytes 8 x.
Proof.
  intros x. change (le8 (Z_to_bv 64 x)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 x))).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 x) with (x mod 2^64). apply Z_to_le_bytes_mod. lia.
Qed.

Lemma le4_word : forall x, le4 (Z_to_bv 64 x) = Z_to_le_bytes 4 x.
Proof.
  intros x. unfold le4. rewrite Z_to_bv_unsigned. change (bv_wrap 64 x) with (x mod 2^64).
  apply Z_to_le_bytes_mod. lia.
Qed.

Lemma le2_word : forall x, le2 (Z_to_bv 64 x) = Z_to_le_bytes 2 x.
Proof.
  intros x. unfold le2. rewrite Z_to_bv_unsigned. change (bv_wrap 64 x) with (x mod 2^64).
  apply Z_to_le_bytes_mod. lia.
Qed.

Lemma le1_word : forall x, le1 (Z_to_bv 64 x) = Z_to_le_bytes 1 x.
Proof.
  intros x. unfold le1. rewrite Z_to_bv_unsigned. change (bv_wrap 64 x) with (x mod 2^64).
  apply Z_to_le_bytes_mod. lia.
Qed.

Lemma le_sub : forall bs k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  Z_to_le_bytes n (u_at bs k n) = sub bs k n.
Proof.
  intros bs k n Hk H. unfold u_at. pose proof (Z_to_le_bytes_to_Z (sub bs k n)) as E.
  rewrite length_sub in E by lia. exact E.
Qed.

Lemma le4_s32 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  le4 (Z_to_bv 64 (s32_at bs k)) = sub bs k 4.
Proof.
  intros bs k Hk H. rewrite le4_word. unfold s32_at.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (u_at bs k 4)) 32) by lia.
  change (2 ^ 32) with (bv_modulus 32). rewrite swrap_mod. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z_to_le_bytes_mod by lia. apply le_sub; lia.
Qed.

Lemma le4_s32_add : forall bs k c, le4 (Z_to_bv 64 (s32_at bs k + c)) = Z_to_le_bytes 4 (u_at bs k 4 + c).
Proof.
  intros bs k c. rewrite le4_word. unfold s32_at.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (u_at bs k 4) + c) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (u_at bs k 4 + c) 32) by lia. f_equal.
  rewrite <- Zplus_mod_idemp_l. change (2 ^ 32) with (bv_modulus 32). rewrite swrap_mod.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma le1_u8 : forall bs k, 0 <= k -> k + 1 <= Z.of_nat (length bs) ->
  le1 (Z_to_bv 64 (u_at bs k 1)) = sub bs k 1.
Proof. intros bs k Hk H. rewrite le1_word. apply le_sub; lia. Qed.

Lemma lh_val : forall bs, length bs = 2%nat ->
  sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) = Z_to_bv 64 (bv_swrap 16 (bytes_le_to_Z bs)).
Proof.
  intros bs L. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. f_equal.
  pose proof (ble_range bs) as H. rewrite L in H. apply bv_wrap_small. unfold bv_modulus. cbn in H. lia.
Qed.

Lemma le2_s16 : forall bs k, 0 <= k -> k + 2 <= Z.of_nat (length bs) ->
  le2 (Z_to_bv 64 (bv_swrap 16 (u_at bs k 2))) = sub bs k 2.
Proof.
  intros bs k Hk H. rewrite le2_word.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 (u_at bs k 2)) 16) by lia.
  change (2 ^ 16) with (bv_modulus 16). rewrite swrap_mod. change (bv_modulus 16) with (2 ^ 16).
  rewrite Z_to_le_bytes_mod by lia. apply le_sub; lia.
Qed.

Lemma eqb_slit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|N].
  - unfold bv_eqb. apply Z.eqb_refl.
  - unfold bv_eqb. apply Z.eqb_neq. intro E. apply N.
    rewrite <- (signed_lit a Ha), <- (signed_lit b Hb). f_equal. apply bv_eq. exact E.
Qed.

Lemma ltu_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.ltb_spec x y) as [L|L]; [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Lemma rd_whole : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. unfold wa in R. rewrite R. f_equal. cbn [Z.to_nat skipn]. apply firstn_all.
Qed.

Lemma wr_at_sub : forall m a n k l, wr_at rsegs m a n -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at rsegs m (a + k) l.
Proof.
  intros m a n k l (H1 & H2 & H) Hk Hl Hkl. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma le1_one : le1 (Z_to_bv 64 1) = [Z_to_bv 8 1].
Proof. rewrite le1_word. reflexivity. Qed.

Lemma snez_le4 : forall ow, -2^31 <= ow < 2^31 ->
  le4 (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 ow)) = Z_to_le_bytes 4 (if ow =? 0 then 0 else 1).
Proof.
  intros ow H. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec ow 0) as [->|N].
  - reflexivity.
  - replace (0 <? ow mod 2^64) with true.
    + rewrite le4_word. reflexivity.
    + symmetry. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Definition cR (T G : list byte) (i : Z) : bool :=
  negb (s_role G =? 0) && negb (role_of_e T i =? s_role G) && negb ((role_of_e T i =? 1) && (s_role G =? 2)).
Definition cD (T G : list byte) (i : Z) : bool :=
  negb (s_hd G =? 0) && ((hd_of T i =? 0) || negb (din_of T i =? s_din G) || negb (dout_of T i =? s_dout G)).
Definition cS (T G : list byte) (i : Z) : bool := negb (s_slots G =? 0) && negb (slots_of T i =? s_slots G).
Definition cF (T G : list byte) (i : Z) : bool := negb (s_fam G =? 0) && negb (fam_of T i =? s_fam G).
Definition cC (T G : list byte) (i : Z) : bool := ch_of T i <? s_ch G.
Definition cO (T : list byte) (ow i : Z) : bool := negb (ow =? 0) && (owned_of T i =? 0).

Definition kA (T : list byte) (now i : Z) : list byte := upd T (48 * i + 40) (Z_to_le_bytes 8 now).
Definition kB (T G : list byte) (now i : Z) : list byte :=
  if cR T G i then upd (kA T now i) (48 * i + 8) (sub G 8 4) else kA T now i.
Definition kC (T G : list byte) (now i : Z) : list byte :=
  if cD T G i
  then upd (upd (upd (kB T G now i) (48 * i + 12) [Z_to_bv 8 1]) (48 * i + 13) (sub G 13 1)) (48 * i + 14) (sub G 14 1)
  else kB T G now i.
Definition kD (T G : list byte) (now i : Z) : list byte :=
  if cS T G i then upd (kC T G now i) (48 * i + 16) (sub G 16 1) else kC T G now i.
Definition kE (T G : list byte) (now i : Z) : list byte :=
  if cF T G i then upd (kD T G now i) (48 * i + 15) (sub G 15 1) else kD T G now i.
Definition kF (T G : list byte) (now i : Z) : list byte :=
  if cC T G i then upd (kE T G now i) (48 * i + 20) (sub G 20 4) else kE T G now i.
Definition kG (T G : list byte) (ow now i : Z) : list byte :=
  if cO T ow i then upd (kF T G now i) (48 * i + 24) (Z_to_le_bytes 4 1) else kF T G now i.

Lemma known_eq : forall T G ow now i, observe_known T G ow now i =
  if cR T G i || cD T G i || cS T G i || cF T G i || cC T G i || cO T ow i
  then (upd (kG T G ow now i) 392 (Z_to_le_bytes 4 (seq_of T + 1)), 1) else (kG T G ow now i, 0).
Proof. reflexivity. Qed.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.

Ltac sok A k j :=
  let m := cur_mem in
  lazymatch goal with
  | W : wr_at _ m A ?N |- _ => pose proof (wr_at_store_ok rsegs m A N k j W ltac:(lia) ltac:(lia))
  end.

Ltac rdx A k n :=
  let m := cur_mem in
  lazymatch goal with
  | H : bytes_at _ m A ?X, L : length ?X = _ |- _ => pose proof (rd_sub m A X k n H ltac:(lia) ltac:(rewrite L; lia))
  end.

Ltac rdf H := let R := fresh "R" in pose proof (rd_whole _ _ _ H) as R; rewrite ?length_sub in R by lia.

Ltac vals :=
  repeat first [ rewrite lw_val by (apply length_sub; lia)
               | rewrite lbu_val by (apply length_sub; lia)
               | rewrite lh_val by (apply length_sub; lia) ].

Ltac lens := cbn [length]; rewrite ?length_Z_to_le_bytes, ?length_le8, ?length_le4, ?length_le2, ?length_le1.

Ltac tstore_at A k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
    replace (write_to_mem m a bs) with (write_to_mem m (Z_to_bv 64 (A + k)) bs) by (f_equal; f_equal; lia);
    lazymatch goal with
    | HX : bytes_at _ m A ?X, LX : length ?X = ?N |- _ =>
      let HX' := fresh "HX" in let LX' := fresh "LX" in
      pose proof (bytes_at_write_inside rsegs m A X k bs HX ltac:(lia) ltac:(rewrite LX; lens; lia)) as HX';
      assert (LX' : length (upd X k bs) = N) by (rewrite upd_len; [exact LX | lia | rewrite LX; lens; lia]);
      change (upd_bytes X (Z.to_nat k) bs) with (upd X k bs) in HX';
      clear HX;
      store_done
    end
  end.

Ltac tstore A :=
  let m := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) => m end in
  lazymatch goal with
  | HS : store_ok _ m (Z_to_bv 64 (A + ?k)) _ = true |- _ => tstore_at A k
  | HS : store_ok _ m (wa (A + ?k)) _ = true |- _ => tstore_at A k
  end.

Ltac fold_u :=
  repeat match goal with
  | |- context [bytes_le_to_Z (sub ?X ?k ?n)] => change (bytes_le_to_Z (sub X k n)) with (u_at X k n)
  end;
  repeat match goal with
  | |- context [bv_swrap 32 (u_at ?X ?k 4)] => change (bv_swrap 32 (u_at X k 4)) with (s32_at X k)
  end.

Ltac cdec :=
  unfold cR, cD, cS, cF, cC, cO, role_of_e, hd_of, din_of, dout_of, owned_of, fam_of, slots_of, ch_of,
    s_role, s_hd, s_din, s_dout, s_fam, s_slots, s_ch;
  repeat match goal with
  | |- context [?a =? ?b] =>
      first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; congruence)
            | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; congruence)
            | destruct (a =? b) ]
  | |- context [?a <? ?b] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)
            | destruct (a <? b) ]
  end; reflexivity.

Lemma u8_range : forall bs k, 0 <= u_at bs k 1 < 256.
Proof. intros bs k. pose proof (u_at_range bs k 1) as H. change (2 ^ (8 * Z.of_nat 1)) with 256 in H. exact H. Qed.

Lemma u32_range : forall bs k, 0 <= u_at bs k 4 < 2 ^ 32.
Proof. intros bs k. pose proof (u_at_range bs k 4) as H. change (8 * Z.of_nat 4) with 32 in H. exact H. Qed.

Lemma eqb_u8 : forall X k Y j, bv_eqb (Z_to_bv 64 (u_at X k 1)) (Z_to_bv 64 (u_at Y j 1)) = (u_at X k 1 =? u_at Y j 1).
Proof. intros. pose proof (u8_range X k). pose proof (u8_range Y j). apply eqb_lit; lia. Qed.

Lemma eqb_u8_0 : forall X k, bv_eqb (Z_to_bv 64 (u_at X k 1)) (Z_to_bv 64 0) = (u_at X k 1 =? 0).
Proof. intros. pose proof (u8_range X k). apply eqb_lit; lia. Qed.

Lemma eqb_s32 : forall X k Y j, bv_eqb (Z_to_bv 64 (s32_at X k)) (Z_to_bv 64 (s32_at Y j)) = (s32_at X k =? s32_at Y j).
Proof. intros. pose proof (s32_range X k). pose proof (s32_range Y j). apply eqb_slit; lia. Qed.

Lemma eqb_s32_c : forall X k c, -2^31 <= c < 2^31 ->
  bv_eqb (Z_to_bv 64 (s32_at X k)) (Z_to_bv 64 c) = (s32_at X k =? c).
Proof. intros. pose proof (s32_range X k). apply eqb_slit; lia. Qed.

Lemma ltu_s32' : forall X k Y j, bv_ltu (Z_to_bv 64 (s32_at X k)) (Z_to_bv 64 (s32_at Y j)) = (u_at X k 4 <? u_at Y j 4).
Proof. intros. unfold s32_at. apply ltu_s32; apply u32_range. Qed.

Lemma b2z_eqb0 : forall b : bool, bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma mk_rw : forall m a X (n : nat), bytes_at rsegs m a X -> length X = n -> wr_at rsegs m a (Z.of_nat n) ->
  rw_cells rsegs m a [CB n X].
Proof.
  intros m a X n H L W. split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma stk_after : forall m m' lo hi a bs, stk rsegs m lo hi ->
  munch [(a, a + Z.of_nat (length bs))] m m' -> wmono rsegs m m' -> bytes_at rsegs m' a bs -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a bs (H1 & H2 & H) MU WM (Ha & Hl & Hb). split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [Hw (b & Hbx)]. split; [apply WM; exact Hw|].
  assert (OUT : ~ (a <= x < a + Z.of_nat (length bs)) -> exists b0, mrd rsegs m' (wa x) = Some b0).
  { intros N. exists b. unfold mrd in *. rewrite MU; [exact Hbx|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I]. }
  destruct (Z.ltb_spec x a); [apply OUT; lia|].
  destruct (Z.ltb_spec x (a + Z.of_nat (length bs))); [|apply OUT; lia].
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite Hb by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma join3 : forall m a P E S k, bytes_at rsegs m a P -> Z.of_nat (length P) = k ->
  bytes_at rsegs m (a + k) E -> bytes_at rsegs m (a + k + Z.of_nat (length E)) S -> bytes_at rsegs m a (P ++ E ++ S).
Proof.
  intros m a P E S k HP LP HE HS. apply bytes_at_app. split; [exact HP|]. rewrite LP.
  apply bytes_at_app. split; [exact HE | exact HS].
Qed.

Lemma entry_eq : forall G ow now, length G = 24%nat ->
  upd (upd (upd (upd (upd (upd (upd (upd (upd (zeros 48) 0 (sub G 0 4)) 4 (sub G 4 2)) 8 (sub G 8 4)) 12 (sub G 12 4))
    24 (Z_to_le_bytes 4 (if ow =? 0 then 0 else 1))) 40 (Z_to_le_bytes 8 now)) 16 (sub G 16 1)) 20 (sub G 20 4))
    32 (Z_to_le_bytes 8 now) = new_entry G ow now.
Proof.
  intros G ow now L.
  do 24 (destruct G as [|? G]; [discriminate|]). destruct G; [|discriminate].
  reflexivity.
Qed.

Ltac mf_vl := repeat first
  [ rewrite length_Z_to_le_bytes
  | rewrite length_sub by lia
  | rewrite upd_len by (mf_vl; lia)
  | rewrite len_if by (mf_vl; lia)
  | progress cbn [length] ].

Ltac mf_unf := match goal with H : ?V = _ |- context [sub ?V _ _] => is_var V; rewrite H end.

Ltac mf_go := repeat first
  [ rewrite sub_upd_other by (mf_vl; lia)
  | rewrite sub_if_other by (mf_vl; lia)
  | mf_unf
  | progress cbv iota ].

Lemma mf_sub_upd_at : forall X k v n, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length v = n -> sub (upd X k v) k n = v.
Proof. intros X k v n Hk H L. subst n. rewrite sub_upd_in by lia. rewrite Z.sub_diag. apply sub_all. Qed.

Lemma mf_fields : forall T T' i,
  (forall k n, 0 <= k -> k + Z.of_nat n <= 48 -> sub T' (48 * i + k) n = sub T (48 * i + k) n) ->
  mac_of T' i = mac_of T i /\ role_of_e T' i = role_of_e T i /\ hd_of T' i = hd_of T i /\
  din_of T' i = din_of T i /\ dout_of T' i = dout_of T i /\ owned_of T' i = owned_of T i.
Proof.
  intros T T' i E. unfold mac_of, role_of_e, hd_of, din_of, dout_of, owned_of, s32_at, u_at.
  pose proof (E 0 6%nat ltac:(lia) ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  rewrite E0, (E 8 4%nat), (E 12 1%nat), (E 13 1%nat), (E 14 1%nat), (E 24 4%nat) by lia.
  repeat split.
Qed.

Lemma mf_ne : forall G ow now, length G = 24%nat ->
  length (new_entry G ow now) = 48%nat /\ sub (new_entry G ow now) 0 6 = s_mac G /\
  sub (new_entry G ow now) 8 4 = sub G 8 4 /\ sub (new_entry G ow now) 12 1 = sub G 12 1 /\
  sub (new_entry G ow now) 13 1 = sub G 13 1 /\ sub (new_entry G ow now) 14 1 = sub G 14 1 /\
  sub (new_entry G ow now) 24 4 = Z_to_le_bytes 4 (if ow =? 0 then 0 else 1).
Proof.
  intros G ow now LG.
  do 24 (destruct G as [|? G]; [cbn in LG; lia|]). destruct G; [|cbn in LG; lia].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma mf_known : forall T G ow now r T' ret,
  length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  (T', ret) = observe_known T G ow now r ->
  length T' = 400%nat /\
  (forall j n, 0 <= j -> j + Z.of_nat n <= 400 ->
     (j + Z.of_nat n <= 48 * r + 8 \/ 48 * r + 48 <= j) -> (j + Z.of_nat n <= 392 \/ 396 <= j) ->
     sub T' j n = sub T j n) /\
  (sub T' (48 * r + 8) 4 = sub T (48 * r + 8) 4 \/ sub T' (48 * r + 8) 4 = sub G 8 4) /\
  ((sub T' (48 * r + 12) 1 = sub T (48 * r + 12) 1 /\ sub T' (48 * r + 13) 1 = sub T (48 * r + 13) 1 /\
    sub T' (48 * r + 14) 1 = sub T (48 * r + 14) 1) \/
   (s_hd G <> 0 /\ sub T' (48 * r + 12) 1 = [Z_to_bv 8 1] /\ sub T' (48 * r + 13) 1 = sub G 13 1 /\
    sub T' (48 * r + 14) 1 = sub G 14 1)) /\
  (sub T' (48 * r + 24) 4 = sub T (48 * r + 24) 4 \/ sub T' (48 * r + 24) 4 = Z_to_le_bytes 4 1).
Proof.
  intros T G ow now r T' ret LT LG Hr H.
  unfold observe_known in H. cbv zeta in H. revert H.
  match goal with |- context [if ?c then upd _ (48 * r + 8) _ else _] => remember c as c1 eqn:E1 end.
  match goal with |- context [if ?c then upd (upd (upd _ (48 * r + 12) _) _ _) _ _ else _] =>
    remember c as c2 eqn:E2 end.
  match goal with |- context [if ?c then upd _ (48 * r + 16) _ else _] => remember c as c3 eqn:E3 end.
  match goal with |- context [if ?c then upd _ (48 * r + 15) _ else _] => remember c as c4 eqn:E4 end.
  match goal with |- context [if ?c then upd _ (48 * r + 20) _ else _] => remember c as c5 eqn:E5 end.
  match goal with |- context [if ?c then upd _ (48 * r + 24) _ else _] => remember c as c6 eqn:E6 end.
  assert (C2 : c2 = true -> s_hd G <> 0).
  { intros C. rewrite E2 in C. apply andb_true_iff in C. destruct C as [C _].
    apply negb_true_iff, Z.eqb_neq in C. exact C. }
  clear E1 E2 E3 E4 E5 E6.
  remember (upd T (48 * r + 40) (Z_to_le_bytes 8 now)) as Ta eqn:HTa.
  remember (if c1 then upd Ta (48 * r + 8) (sub G 8 4) else Ta) as Tb eqn:HTb.
  remember (if c2 then upd (upd (upd Tb (48 * r + 12) [Z_to_bv 8 1]) (48 * r + 13) (sub G 13 1))
              (48 * r + 14) (sub G 14 1) else Tb) as Tc eqn:HTc.
  remember (if c3 then upd Tc (48 * r + 16) (sub G 16 1) else Tc) as Td eqn:HTd.
  remember (if c4 then upd Td (48 * r + 15) (sub G 15 1) else Td) as Te eqn:HTe.
  remember (if c5 then upd Te (48 * r + 20) (sub G 20 4) else Te) as Tf eqn:HTf.
  remember (if c6 then upd Tf (48 * r + 24) (Z_to_le_bytes 4 1) else Tf) as Tg eqn:HTg.
  intros H.
  assert (HT' : T' = Tg \/ T' = upd Tg 392 (Z_to_le_bytes 4 (seq_of T + 1))).
  { revert H. match goal with |- _ = (if ?C then _ else _) -> _ => destruct C end;
      cbv iota; intros H; injection H as H1 H2; [right|left]; exact H1. }
  clear H.
  assert (LTa : length Ta = 400%nat) by (rewrite HTa; mf_vl; lia).
  assert (LTb : length Tb = 400%nat) by (rewrite HTb; mf_vl; lia).
  assert (LTc : length Tc = 400%nat) by (rewrite HTc; destruct c2; cbv iota; mf_vl; lia).
  assert (LTd : length Td = 400%nat) by (rewrite HTd; mf_vl; lia).
  assert (LTe : length Te = 400%nat) by (rewrite HTe; mf_vl; lia).
  assert (LTf : length Tf = 400%nat) by (rewrite HTf; mf_vl; lia).
  assert (LTg : length Tg = 400%nat) by (rewrite HTg; mf_vl; lia).
  split; [destruct HT' as [-> | ->]; mf_vl; lia|].
  split; [|split; [|split]].
  - intros j n Hj Hn D1 D2. destruct c2; destruct HT' as [-> | ->]; mf_go; reflexivity.
  - destruct c1; [right|left]; destruct c2; destruct HT' as [-> | ->]; mf_go;
      first [apply mf_sub_upd_at; mf_vl; lia | reflexivity].
  - destruct c2; [right; split; [apply C2; reflexivity|] | left]; destruct HT' as [-> | ->];
      (split; [|split]); mf_go; first [apply mf_sub_upd_at; mf_vl; lia | reflexivity].
  - destruct c6; [right|left]; destruct c2; destruct HT' as [-> | ->]; mf_go;
      first [apply mf_sub_upd_at; mf_vl; lia | reflexivity].
Qed.

Lemma mf_full : forall T T' ret, length T = 400%nat -> (T', ret) = observe_full T ->
  length T' = 400%nat /\ (forall j n, 0 <= j -> j + Z.of_nat n <= 388 -> sub T' j n = sub T j n).
Proof.
  intros T T' ret LT H. unfold observe_full in H. revert H.
  destruct (ov_of T =? 0); intros H; injection H as H1 H2; subst T'.
  - split; [mf_vl; lia|]. intros j n Hj Hn. mf_go. reflexivity.
  - split; [exact LT|]. intros; reflexivity.
Qed.

Lemma mf_new : forall T G ow now T' ret, length T = 400%nat -> length G = 24%nat -> 0 <= n_of T < 8 ->
  (T', ret) = observe_new T G ow now ->
  length T' = 400%nat /\ sub T' 384 4 = Z_to_le_bytes 4 (n_of T + 1) /\
  (forall j n, 0 <= j -> j + Z.of_nat n <= 48 * n_of T -> sub T' j n = sub T j n) /\
  (forall k n, 0 <= k -> k + Z.of_nat n <= 48 -> sub T' (48 * n_of T + k) n = sub (new_entry G ow now) k n).
Proof.
  intros T G ow now T' ret LT LG Hn H. unfold observe_new in H. injection H as H1 H2. subst T'.
  destruct (mf_ne G ow now LG) as [LN _].
  split; [mf_vl; lia|]. split; [|split].
  - mf_go. apply mf_sub_upd_at; mf_vl; lia.
  - intros j n Hj Hk. mf_go. reflexivity.
  - intros k n Hk Hkn. rewrite sub_upd_other by (mf_vl; lia). rewrite sub_upd_in by (mf_vl; lia).
    f_equal. lia.
Qed.

Lemma observe_model_tbl : forall T G ow now T' ret,
  length T = 400%nat -> length G = 24%nat ->
  tbl_T1 T -> tbl_T2 T -> tbl_T3 T -> sighting_S1 G -> sighting_S2 G ->
  observe_model T G ow now T' ret ->
  tbl_T1 T' /\ tbl_T2 T' /\ tbl_T3 T' /\ (tbl_T4 T -> tbl_T4 T').
Proof.
  intros T G ow now T' ret LT LG H1 H2 H3 S1 S2 [r [F [[Hr E] | [[Hr [Hn E]] | [Hr [Hn E]]]]]];
    pose proof H1 as H1'; unfold tbl_T1 in H1'.
  - assert (Rr : 0 <= r < n_of T) by (destruct F as [[? _] | [? _]]; lia).
    destruct (mf_known T G ow now r T' ret LT LG ltac:(lia) E) as (L' & K & KR & KD & KO).
    assert (N' : n_of T' = n_of T) by (unfold n_of, s32_at, u_at; rewrite (K 384 4%nat) by lia; reflexivity).
    assert (FE : forall i, 0 <= i < 8 -> i <> r ->
      mac_of T' i = mac_of T i /\ role_of_e T' i = role_of_e T i /\ hd_of T' i = hd_of T i /\
      din_of T' i = din_of T i /\ dout_of T' i = dout_of T i /\ owned_of T' i = owned_of T i).
    { intros i Hi Ne. apply mf_fields. intros k n Hk Hkn. apply K; lia. }
    assert (ME : forall i, 0 <= i < 8 -> mac_of T' i = mac_of T i) by (intros i Hi; unfold mac_of; apply K; lia).
    assert (RE : role_of_e T' r = role_of_e T r \/ role_of_e T' r = s_role G).
    { destruct KR as [KR|KR]; [left|right]; unfold role_of_e, s_role, s32_at, u_at; rewrite KR; reflexivity. }
    assert (HD : (hd_of T' r = hd_of T r /\ din_of T' r = din_of T r /\ dout_of T' r = dout_of T r) \/
                 (s_hd G = 1 /\ hd_of T' r = 1 /\ din_of T' r = s_din G /\ dout_of T' r = s_dout G)).
    { destruct KD as [(D1 & D2 & D3) | (Hs & D1 & D2 & D3)]; [left|right];
        unfold hd_of, din_of, dout_of, s_din, s_dout, u_at; rewrite D1, D2, D3.
      - repeat split.
      - split; [destruct S2 as [[Q|Q] _]; [contradiction|exact Q]|]. split; [reflexivity|]. split; reflexivity. }
    assert (OW : owned_of T' r = owned_of T r \/ owned_of T' r = 1).
    { destruct KO as [O|O]; [left|right]; unfold owned_of, s32_at, u_at; rewrite O; reflexivity. }
    unfold tbl_T1, tbl_T2, tbl_T3, tbl_T4. rewrite N'.
    split; [exact H1'|]. split; [|split].
    + intros i Hi. destruct (Z.eq_dec i r) as [->|Ne].
      * destruct RE as [-> | ->]; [apply H2; exact Rr | exact S1].
      * destruct (FE i ltac:(lia) Ne) as (_ & ER & _). rewrite ER. apply H2. exact Hi.
    + intros i j Hi Hij Hj. rewrite (ME i), (ME j) by lia. apply H3; lia.
    + intros H4 i Hi. destruct (Z.eq_dec i r) as [->|Ne].
      * destruct (H4 r Rr) as (A1 & A2 & A3). split; [|split].
        -- destruct HD as [(D1 & _ & _) | (_ & D1 & _ & _)]; rewrite D1; [exact A1 | right; reflexivity].
        -- destruct HD as [(D1 & D2 & D3) | (Hs & D1 & D2 & D3)]; rewrite D1, D2, D3;
             [exact A2 | intros _; apply (proj2 S2); exact Hs].
        -- destruct OW as [-> | ->]; [exact A3 | right; reflexivity].
      * destruct (FE i ltac:(lia) Ne) as (_ & _ & E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4.
        apply H4. exact Hi.
  - destruct (mf_full T T' ret LT E) as (L' & K).
    assert (N' : n_of T' = n_of T) by (unfold n_of, s32_at, u_at; rewrite (K 384 4%nat) by lia; reflexivity).
    assert (FE : forall i, 0 <= i < 8 ->
      mac_of T' i = mac_of T i /\ role_of_e T' i = role_of_e T i /\ hd_of T' i = hd_of T i /\
      din_of T' i = din_of T i /\ dout_of T' i = dout_of T i /\ owned_of T' i = owned_of T i).
    { intros i Hi. apply mf_fields. intros k n Hk Hkn. apply K; lia. }
    unfold tbl_T1, tbl_T2, tbl_T3, tbl_T4. rewrite N'.
    split; [exact H1'|]. split; [|split].
    + intros i Hi. destruct (FE i ltac:(lia)) as (_ & ER & _). rewrite ER. apply H2. exact Hi.
    + intros i j Hi Hij Hj. destruct (FE i ltac:(lia)) as (EI & _). destruct (FE j ltac:(lia)) as (EJ & _).
      rewrite EI, EJ. apply H3; lia.
    + intros H4 i Hi. destruct (FE i ltac:(lia)) as (_ & _ & E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4.
      apply H4. exact Hi.
  - assert (Rn : 0 <= n_of T < 8) by lia.
    destruct (mf_new T G ow now T' ret LT LG Rn E) as (L' & N4 & K & KN).
    destruct (mf_ne G ow now LG) as (LN & F0 & F8 & F12 & F13 & F14 & F24).
    assert (N' : n_of T' = n_of T + 1).
    { unfold n_of at 1. unfold s32_at, u_at. rewrite N4. rewrite bytes_le_to_Z_to_le_bytes by lia.
      change (8 * Z.of_nat 4) with 32. rewrite Z.mod_small by lia. apply swrap32_small. lia. }
    assert (EQ : forall i, 0 <= i < n_of T ->
      mac_of T' i = mac_of T i /\ role_of_e T' i = role_of_e T i /\ hd_of T' i = hd_of T i /\
      din_of T' i = din_of T i /\ dout_of T' i = dout_of T i /\ owned_of T' i = owned_of T i).
    { intros i Hi. apply mf_fields. intros k n Hk Hkn. apply K; lia. }
    assert (NE : mac_of T' (n_of T) = s_mac G /\ role_of_e T' (n_of T) = s_role G /\
                 hd_of T' (n_of T) = s_hd G /\ din_of T' (n_of T) = s_din G /\ dout_of T' (n_of T) = s_dout G /\
                 owned_of T' (n_of T) = (if ow =? 0 then 0 else 1)).
    { unfold mac_of, role_of_e, hd_of, din_of, dout_of, owned_of, s_role, s_hd, s_din, s_dout, s32_at, u_at.
      pose proof (KN 0 6%nat ltac:(lia) ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
      rewrite K0, (KN 8 4%nat), (KN 12 1%nat), (KN 13 1%nat), (KN 14 1%nat), (KN 24 4%nat) by lia.
      rewrite F0, F8, F12, F13, F14, F24.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. destruct (ow =? 0); reflexivity. }
    unfold tbl_T1, tbl_T2, tbl_T3, tbl_T4. rewrite N'.
    split; [lia|]. split; [|split].
    + intros i Hi. destruct (Z.eq_dec i (n_of T)) as [->|Ne].
      * rewrite (proj1 (proj2 NE)). exact S1.
      * destruct (EQ i ltac:(lia)) as (_ & ER & _). rewrite ER. apply H2. lia.
    + intros i j Hi Hij Hj. destruct (EQ i ltac:(lia)) as (EI & _). rewrite EI.
      destruct (Z.eq_dec j (n_of T)) as [->|Ne].
      * rewrite (proj1 NE). destruct F as [[_ FF] | [FR _]]; [apply FF; lia | lia].
      * destruct (EQ j ltac:(lia)) as (EJ & _). rewrite EJ. apply H3; lia.
    + intros H4 i Hi. destruct (Z.eq_dec i (n_of T)) as [->|Ne].
      * destruct NE as (_ & _ & E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4.
        split; [exact (proj1 S2)|]. split; [exact (proj2 S2)|]. destruct (ow =? 0); [left|right]; reflexivity.
      * destruct (EQ i ltac:(lia)) as (_ & _ & E1 & E2 & E3 & E4). rewrite E1, E2, E3, E4. apply H4. lia.
Qed.

Theorem reac_disco_table_observe_holds : bcmp_contract -> memset_contract -> reac_disco_table_observe_contract.
Proof.
  intros BC MSC. unfold reac_disco_table_observe_contract, REAC_DISCO_TABLE_OBSERVE, REAC_DISCO_TABLE_OBSERVE_K.
  unfold BCMP in BC. unfold MEMSET in MSC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t s ow now T G -> -> -> -> Row Rnow Ht0 Ht8 RT LT Hs0 Hs4 HG LG DTS T1 T2 T3 S1 S2 MI ST LO DT DS.
  unfold tbl_T1 in T1. unfold off_window in DT, DS.
  destruct RT as [[_ HT] WT]. cbn [cells_bytes cbytes cells_size csize] in HT, WT. rewrite app_nil_r in HT.
  replace (Z.of_nat (400 + 0)) with 400 in WT by lia.
  pose proof (bytes_at_bound rsegs m t T HT) as TB. rewrite LT in TB.
  pose proof (bytes_at_bound rsegs m s G HG) as GB. rewrite LG in GB.
  pose proof (munch_refl [(t, t + 400); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 96%nat ST. rename junk into fjunk.
  do 12 step.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF _ ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  assert (CSF : cells_size FRC = 96%nat) by reflexivity.
  step. rewrite eqb_lit by lia. replace (s =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hs0). cbn [negb].
  do 4 step. rewrite land3_lit by lia. if_false.
  step. rewrite eqb_lit by lia. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ht0). cbn [negb].
  do 2 step. rewrite land7_lit by lia. if_false.
  do 2 step.
  pose proof (rd_sub _ t T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  set (n := n_of T) in *.
  step. rewrite not_lit by lia.
  step.
  rewrite lts_lit by lia.
  assert (EPI : forall (m2 : word -> option byte) (T' : list byte) (ret : Z)
                  (ra' x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t T' -> length T' = 400%nat -> observe_model T G ow now T' ret ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 ret) x11 x12 x13
                            x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15adc) fc None m2 (seg_rom rsegs))).
  { intros m2 T' ret ra' x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2 WT2 HG2 HT2 LT2 OM.
    unfold FRC in FR2.
    do 11 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    destruct (observe_model_tbl T G ow now T' ret LT LG T1 T2 T3 S1 S2 OM) as (U1 & U2 & U3 & U4).
    apply evt_done. unfold QQ. do 15 eexists. exists T', ret. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [apply mk_rw; assumption|].
    split; [exact HG2|]. split; [exact OM|]. tauto. }
  assert (SEQ : forall (m2 : word -> option byte) (X : list byte) (ret : Z)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t X -> length X = 400%nat -> bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      observe_model T G ow now (upd X 392 (Z_to_le_bytes 4 (seq_of T + 1))) ret ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 ret) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x19 (Z_to_bv 64 now)
                            x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15ad0) fc None m2 (seg_rom rsegs))).
  { intros m2 X ret ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FSq OM.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    rdf FSq.
    step. vals. fold_u.
    step.
    sok t 392 4%nat.
    step.
    tstore t.
    rewrite le4_s32_add in *.
    apply (EPI _ (upd X 392 (Z_to_le_bytes 4 (seq_of T + 1))) ret); assumption. }
  assert (LG7 : forall i (m2 : word -> option byte) (f : bool)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      f = cR T G i || cD T G i || cS T G i || cF T G i || cC T G i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t (kF T G now i) -> length (kF T G now i) = 400%nat ->
      bytes_at rsegs m2 (t + (48 * i + 24)) (sub T (48 * i + 24) 4) ->
      bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15abc) fc None m2 (seg_rom rsegs))).
  { intros i m2 f ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI Hf FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FOw FSq.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    assert (FIN : forall y11 : word, cO T ow i = false ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15ac8) fc None m2 (seg_rom rsegs))).
    { intros y11 CO.
      replace (kF T G now i) with (kG T G ow now i) in HX, LX by (unfold kG; rewrite CO; reflexivity).
      step. rewrite b2z_eqb0.
      destruct f; cbn [negb].
      - step.
        apply (SEQ _ (kG T G ow now i) 1); try assumption.
        exists i. split; [exact FI|]. left. split; [lia|].
        rewrite known_eq, <- Hf, CO. reflexivity.
      - apply (EPI _ (kG T G ow now i) 0); try assumption.
        exists i. split; [exact FI|]. left. split; [lia|].
        rewrite known_eq, <- Hf, CO. reflexivity. }
    step. rewrite eqb_slit by lia.
    destruct (Z.eqb_spec ow 0) as [W0|W0]; cbn [negb].
    - apply FIN. cdec.
    - rdf FOw. step. vals. fold_u.
      step. rewrite eqb_s32_c by lia.
      destruct (Z.eqb_spec (s32_at T (48 * i + 24)) 0) as [O0|O0]; cbn [negb].
      + assert (CO : cO T ow i = true) by cdec.
        step. sok t (48 * i + 24) 4%nat. step. tstore t. rewrite le4_word in *.
        replace (upd (kF T G now i) (48 * i + 24) (Z_to_le_bytes 4 1)) with (kG T G ow now i) in *
          by (unfold kG; rewrite CO; reflexivity).
        step.
        apply (SEQ _ (kG T G ow now i) 1); try assumption.
        exists i. split; [exact FI|]. left. split; [lia|].
        rewrite known_eq, <- Hf, CO, orb_true_r. reflexivity.
      + apply FIN. cdec. }
  assert (LF6 : forall i (m2 : word -> option byte) (f : bool)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      f = cR T G i || cD T G i || cS T G i || cF T G i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t (kE T G now i) -> length (kE T G now i) = 400%nat ->
      bytes_at rsegs m2 (t + (48 * i + 20)) (sub T (48 * i + 20) 4) ->
      bytes_at rsegs m2 (t + (48 * i + 24)) (sub T (48 * i + 24) 4) ->
      bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15aa8) fc None m2 (seg_rom rsegs))).
  { intros i m2 f ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI Hf FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FCh FOw FSq.
    pose proof (length_sub T (48 * i + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LCh.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    rdx s 20 4%nat. step. rdf FCh. step. vals. fold_u.
    step. rewrite ltu_s32'.
    destruct (Z.ltb_spec (u_at T (48 * i + 20) 4) (u_at G 20 4)) as [C1|C1]; cbn [negb].
    - assert (CC : cC T G i = true) by cdec.
      sok t (48 * i + 20) 4%nat. step. tstore t. rewrite le4_s32 in * by lia.
      replace (upd (kE T G now i) (48 * i + 20) (sub G 20 4)) with (kF T G now i) in *
        by (unfold kF; rewrite CC; reflexivity).
      step.
      apply (LG7 i _ true); try assumption. rewrite CC, orb_true_r. reflexivity.
    - assert (CC : cC T G i = false) by cdec.
      replace (kE T G now i) with (kF T G now i) in HX, LX by (unfold kF; rewrite CC; reflexivity).
      apply (LG7 i _ f); try assumption. rewrite CC, orb_false_r. exact Hf. }
  assert (LE5 : forall i (m2 : word -> option byte) (f : bool)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      f = cR T G i || cD T G i || cS T G i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t (kD T G now i) -> length (kD T G now i) = 400%nat ->
      bytes_at rsegs m2 (t + (48 * i + 15)) (sub T (48 * i + 15) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 20)) (sub T (48 * i + 20) 4) ->
      bytes_at rsegs m2 (t + (48 * i + 24)) (sub T (48 * i + 24) 4) ->
      bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a90) fc None m2 (seg_rom rsegs))).
  { intros i m2 f ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI Hf FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FFa FCh FOw FSq.
    pose proof (length_sub T (48 * i + 15) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LFa.
    pose proof (length_sub T (48 * i + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LCh.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    assert (SKIP : cF T G i = false -> forall y11 y12 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15aa8) fc None m2 (seg_rom rsegs))).
    { intros CF y11 y12.
      replace (kD T G now i) with (kE T G now i) in HX, LX by (unfold kE; rewrite CF; reflexivity).
      apply (LF6 i _ f); try assumption. rewrite CF, orb_false_r. exact Hf. }
    rdx s 15 1%nat. step. vals. fold_u.
    step. rewrite eqb_u8_0.
    destruct (Z.eqb_spec (u_at G 15 1) 0) as [Z0|Z0]; cbn [negb].
    - apply SKIP. cdec.
    - rdf FFa. step. vals. fold_u.
      step. rewrite eqb_u8.
      destruct (Z.eqb_spec (u_at T (48 * i + 15) 1) (u_at G 15 1)) as [E1|E1]; cbn [negb].
      + apply SKIP. cdec.
      + assert (CF : cF T G i = true) by cdec.
        sok t (48 * i + 15) 1%nat. step. tstore t. rewrite le1_u8 in * by lia.
        replace (upd (kD T G now i) (48 * i + 15) (sub G 15 1)) with (kE T G now i) in *
          by (unfold kE; rewrite CF; reflexivity).
        step.
        apply (LF6 i _ true); try assumption. rewrite CF, orb_true_r. reflexivity. }
  assert (LD4 : forall i (m2 : word -> option byte) (f : bool)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      f = cR T G i || cD T G i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t (kC T G now i) -> length (kC T G now i) = 400%nat ->
      bytes_at rsegs m2 (t + (48 * i + 16)) (sub T (48 * i + 16) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 15)) (sub T (48 * i + 15) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 20)) (sub T (48 * i + 20) 4) ->
      bytes_at rsegs m2 (t + (48 * i + 24)) (sub T (48 * i + 24) 4) ->
      bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a78) fc None m2 (seg_rom rsegs))).
  { intros i m2 f ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI Hf FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FSl FFa FCh FOw FSq.
    pose proof (length_sub T (48 * i + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LSl.
    pose proof (length_sub T (48 * i + 15) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LFa.
    pose proof (length_sub T (48 * i + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LCh.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    assert (SKIP : cS T G i = false -> forall y11 y12 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a90) fc None m2 (seg_rom rsegs))).
    { intros CS y11 y12.
      replace (kC T G now i) with (kD T G now i) in HX, LX by (unfold kD; rewrite CS; reflexivity).
      apply (LE5 i _ f); try assumption. rewrite CS, orb_false_r. exact Hf. }
    rdx s 16 1%nat. step. vals. fold_u.
    step. rewrite eqb_u8_0.
    destruct (Z.eqb_spec (u_at G 16 1) 0) as [Z0|Z0]; cbn [negb].
    - apply SKIP. cdec.
    - rdf FSl. step. vals. fold_u.
      step. rewrite eqb_u8.
      destruct (Z.eqb_spec (u_at T (48 * i + 16) 1) (u_at G 16 1)) as [E1|E1]; cbn [negb].
      + apply SKIP. cdec.
      + assert (CS : cS T G i = true) by cdec.
        sok t (48 * i + 16) 1%nat. step. tstore t. rewrite le1_u8 in * by lia.
        replace (upd (kC T G now i) (48 * i + 16) (sub G 16 1)) with (kD T G now i) in *
          by (unfold kD; rewrite CS; reflexivity).
        step.
        apply (LE5 i _ true); try assumption. rewrite CS, orb_true_r. reflexivity. }
  assert (LC3 : forall i (m2 : word -> option byte) (f : bool)
                  (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      f = cR T G i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G ->
      bytes_at rsegs m2 t (kB T G now i) -> length (kB T G now i) = 400%nat ->
      bytes_at rsegs m2 (t + (48 * i + 12)) (sub T (48 * i + 12) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 13)) (sub T (48 * i + 13) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 14)) (sub T (48 * i + 14) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 16)) (sub T (48 * i + 16) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 15)) (sub T (48 * i + 15) 1) ->
      bytes_at rsegs m2 (t + (48 * i + 20)) (sub T (48 * i + 20) 4) ->
      bytes_at rsegs m2 (t + (48 * i + 24)) (sub T (48 * i + 24) 4) ->
      bytes_at rsegs m2 (t + 392) (sub T 392 4) ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a38) fc None m2 (seg_rom rsegs))).
  { intros i m2 f ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI Hf FR2 ST2 MU2 WM2 MI2 WT2 HG2 HX LX FHd FDi FDo FSl FFa FCh FOw FSq.
    pose proof (length_sub T (48 * i + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LHd.
    pose proof (length_sub T (48 * i + 13) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LDi.
    pose proof (length_sub T (48 * i + 14) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LDo.
    pose proof (length_sub T (48 * i + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LSl.
    pose proof (length_sub T (48 * i + 15) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LFa.
    pose proof (length_sub T (48 * i + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LCh.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    assert (SKIP : cD T G i = false -> forall y11 y12 y13 y14 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) y11 y12 y13 y14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a78) fc None m2 (seg_rom rsegs))).
    { intros CD y11 y12 y13 y14.
      replace (kB T G now i) with (kC T G now i) in HX, LX by (unfold kC; rewrite CD; reflexivity).
      apply (LD4 i _ f); try assumption. rewrite CD, orb_false_r. exact Hf. }
    assert (DST : cD T G i = true -> forall y11 y12 y13 y14 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (Z.b2z f)) y11 y12 y13 y14 x15 x16 x17 (Z_to_bv 64 s)
                            (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a60) fc None m2 (seg_rom rsegs))).
    { intros CD y11 y12 y13 y14.
      rdx s 13 1%nat. step. rdx s 14 1%nat. step. vals. fold_u.
      step.
      sok t (48 * i + 12) 1%nat. step. tstore t. rewrite le1_one in *.
      sok t (48 * i + 13) 1%nat. step. tstore t. rewrite le1_u8 in * by lia.
      sok t (48 * i + 14) 1%nat. step. tstore t. rewrite le1_u8 in * by lia.
      replace (upd (upd (upd (kB T G now i) (48 * i + 12) [Z_to_bv 8 1]) (48 * i + 13) (sub G 13 1))
                   (48 * i + 14) (sub G 14 1))
        with (kC T G now i) in * by (unfold kC; rewrite CD; reflexivity).
      apply (LD4 i _ true); try assumption. rewrite CD, orb_true_r. reflexivity. }
    rdx s 12 1%nat. step. vals. fold_u.
    step. rewrite eqb_u8_0.
    destruct (Z.eqb_spec (u_at G 12 1) 0) as [H0|H0]; cbn [negb].
    - apply SKIP. cdec.
    - rdf FHd. step. vals. fold_u.
      step. rewrite eqb_u8_0.
      destruct (Z.eqb_spec (u_at T (48 * i + 12) 1) 0) as [E0|E0]; cbn [negb].
      + apply DST. cdec.
      + rdf FDi. step. rdx s 13 1%nat. step. vals. fold_u.
        step. rewrite eqb_u8.
        destruct (Z.eqb_spec (u_at T (48 * i + 13) 1) (u_at G 13 1)) as [D1|D1]; cbn [negb].
        * rdf FDo. step. rdx s 14 1%nat. step. vals. fold_u.
          step. rewrite eqb_u8.
          destruct (Z.eqb_spec (u_at T (48 * i + 14) 1) (u_at G 14 1)) as [D2|D2]; cbn [negb].
          -- apply SKIP. cdec.
          -- apply DST. cdec.
        * apply DST. cdec. }
  assert (KNOWN : forall i (m2 : word -> option byte)
                    (ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
      0 <= i < n -> find_res T (s_mac G) i ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G -> bytes_at rsegs m2 t T ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) (Z_to_bv 64 (t + 48 * i))
                            (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x159f8) fc None m2 (seg_rom rsegs))).
  { intros i m2 ra' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31
      Hi FI FR2 ST2 MU2 WM2 MI2 WT2 HG2 HT2.
    pose proof (bytes_at_sub _ t T (48 * i + 8) 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FRo.
    pose proof (bytes_at_sub _ t T (48 * i + 12) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FHd.
    pose proof (bytes_at_sub _ t T (48 * i + 13) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FDi.
    pose proof (bytes_at_sub _ t T (48 * i + 14) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FDo.
    pose proof (bytes_at_sub _ t T (48 * i + 16) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FSl.
    pose proof (bytes_at_sub _ t T (48 * i + 15) 1 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FFa.
    pose proof (bytes_at_sub _ t T (48 * i + 20) 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FCh.
    pose proof (bytes_at_sub _ t T (48 * i + 24) 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FOw.
    pose proof (bytes_at_sub _ t T 392 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FSq.
    pose proof (length_sub T (48 * i + 8) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LRo.
    pose proof (length_sub T (48 * i + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LHd.
    pose proof (length_sub T (48 * i + 13) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LDi.
    pose proof (length_sub T (48 * i + 14) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LDo.
    pose proof (length_sub T (48 * i + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LSl.
    pose proof (length_sub T (48 * i + 15) 1 ltac:(lia) ltac:(rewrite LT; lia)) as LFa.
    pose proof (length_sub T (48 * i + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LCh.
    pose proof (length_sub T (48 * i + 24) 4 ltac:(lia) ltac:(rewrite LT; lia)) as LOw.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    rdx s 8 4%nat. step. vals. fold_u.
    sok t (48 * i + 40) 8%nat. step. tstore t. rewrite le8_word in *.
    change (upd T (48 * i + 40) (Z_to_le_bytes 8 now)) with (kA T now i) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
    assert (RST : cR T G i = true -> forall y11 y12 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 (s32_at G 8)) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 s)
                            (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a30) fc None mA (seg_rom rsegs))).
    { intros CR y11 y12.
      sok t (48 * i + 8) 4%nat. step. tstore t. rewrite le4_s32 in * by lia.
      replace (upd (kA T now i) (48 * i + 8) (sub G 8 4)) with (kB T G now i) in *
        by (unfold kB; rewrite CR; reflexivity).
      step.
      apply (LC3 i _ true); try assumption. rewrite CR. reflexivity. }
    assert (KEEP : cR T G i = false -> forall y11 y12 : word,
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            (Z_to_bv 64 0) y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 s)
                            (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 now) x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15a38) fc None mA (seg_rom rsegs))).
    { intros CR y11 y12.
      replace (kA T now i) with (kB T G now i) in * by (unfold kB; rewrite CR; reflexivity).
      apply (LC3 i _ false); try assumption. rewrite CR. reflexivity. }
    step. rewrite eqb_s32_c by lia.
    destruct (Z.eqb_spec (s32_at G 8) 0) as [R0|R0]; cbn [negb].
    - rewrite R0. apply KEEP. cdec.
    - rdf FRo. step. vals. fold_u.
      step. rewrite eqb_s32.
      destruct (Z.eqb_spec (s32_at T (48 * i + 8)) (s32_at G 8)) as [E1|E1]; cbn [negb].
      + step. step. apply KEEP. cdec.
      + step. step. rewrite eqb_s32_c by lia.
        destruct (Z.eqb_spec (s32_at G 8) 2) as [R2|R2]; cbn [negb].
        * step. step. rewrite eqb_s32_c by lia.
          destruct (Z.eqb_spec (s32_at T (48 * i + 8)) 1) as [E2|E2]; cbn [negb].
          -- step. step. apply KEEP. cdec.
          -- apply RST. cdec.
        * apply RST. cdec. }
  assert (NEW : forall (m2 : word -> option byte)
                  (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 : word),
      n < 8 -> (forall j, 0 <= j < n -> mac_of T j <> s_mac G) ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G -> bytes_at rsegs m2 t T ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x19 (Z_to_bv 64 now)
                            (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 n) x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15980) fc None m2 (seg_rom rsegs))).
  { intros m2 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31
      Hn8 NF FR2 ST2 MU2 WM2 MI2 WT2 HG2 HT2.
    pose proof (bytes_at_sub _ t T 392 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FSq.
    pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
    step. step.
    sok t 384 4%nat. step. tstore t. rewrite le4_word in *.
    step. rewrite ltu_lit by lia. replace (n <? 9) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    do 3 step. rewrite mul48_lit by lia.
    step. rewrite ltu_lit by lia.
    replace (2^64 - 1 - t <? 48 * n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
    do 5 step.
    set (T1' := upd T 384 (Z_to_le_bytes 4 (n + 1))) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mB end.
    lazymatch goal with HX : bytes_at _ mB t T1', LX : length T1' = _ |- _ => rename HX into HX1; rename LX into LX1 end.
    pose proof (bytes_at_sub _ t T1' 0 (Z.to_nat (48 * n)) HX1 ltac:(lia) ltac:(rewrite LX1; lia)) as HP.
    pose proof (bytes_at_sub _ t T1' (48 * n) 48 HX1 ltac:(lia) ltac:(rewrite LX1; lia)) as HE.
    pose proof (bytes_at_sub _ t T1' (48 * n + 48) (Z.to_nat (400 - (48 * n + 48))) HX1 ltac:(lia)
                  ltac:(rewrite LX1; lia)) as HS.
    pose proof (length_sub T1' 0 (Z.to_nat (48 * n)) ltac:(lia) ltac:(rewrite LX1; lia)) as LP.
    pose proof (length_sub T1' (48 * n) 48 ltac:(lia) ltac:(rewrite LX1; lia)) as LE0.
    pose proof (length_sub T1' (48 * n + 48) (Z.to_nat (400 - (48 * n + 48))) ltac:(lia) ltac:(rewrite LX1; lia)) as LS.
    pose proof (wr_at_sub mB t 400 (48 * n) 48 WT2 ltac:(lia) ltac:(lia) ltac:(lia)) as WE.
    rewrite Z.add_0_r in HP.
    clear HX1.
    remember (t + 48 * n) as e eqn:He.
    eapply evt_cut.
    { eapply MSC.
      - rewrite (unsigned_lit e) by lia. apply mk_rw; [exact HE | exact LE0 | exact WE].
      - assumption. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                    EQ & MUc & WMc & MIc & RWc).
    subst ms'.
    rewrite (unsigned_lit e) in MUc, RWc by lia.
    change (bv_unsigned (Z_to_bv 64 48)) with 48 in MUc, RWc.
    destruct RWc as [[_ HE3] WE3]. cbn [cells_bytes cbytes cells_size csize] in HE3, WE3. rewrite app_nil_r in HE3.
    change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat 48)) with (zeros 48) in HE3.
    change (Z.of_nat (Z.to_nat 48 + 0)) with 48 in WE3.
    assert (LE3 : length (zeros 48) = 48%nat) by reflexivity.
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -96)).
    { apply (stk_after mB m3 lo (bv_unsigned sp + -96) e (zeros 48)); [assumption | | exact WMc | exact HE3].
      rewrite LE3. exact MUc. }
    clear ST2 HE.
    lazymatch goal with H : mem_inv _ mB |- _ => clear H end.
    transport_after_call rsegs mB m3 MUc WMc.
    clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x159b4)) with (Z_to_bv 64 0x159b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rdx s 0 4%nat. step. vals. fold_u.
    sok e 0 4%nat. step. tstore e. rewrite le4_s32 in * by lia.
    rdx s 4 2%nat. step. vals. fold_u.
    sok e 4 2%nat. step. tstore e. rewrite le2_s16 in * by lia.
    rdx s 8 4%nat. step. vals. fold_u.
    sok e 8 4%nat. step. tstore e. rewrite le4_s32 in * by lia.
    rdx s 12 4%nat. step. vals. fold_u.
    step.
    sok e 12 4%nat. step. tstore e. rewrite le4_s32 in * by lia.
    rdx s 16 1%nat. step. rdx s 20 4%nat. step. vals. fold_u.
    sok e 24 4%nat. step. tstore e. rewrite snez_le4 in * by lia.
    sok e 40 8%nat. step. tstore e. rewrite le8_word in *.
    sok e 16 1%nat. step. tstore e. rewrite le1_u8 in * by lia.
    sok e 20 4%nat. step. tstore e. rewrite le4_s32 in * by lia.
    sok e 32 8%nat. step. tstore e. rewrite le8_word in *.
    lazymatch goal with HX : bytes_at _ ?mm e ?E9, LX : length ?E9 = 48%nat |- _ =>
      rename HX into HE9; rename LX into LE9; rename mm into mC;
      assert (EE : E9 = new_entry G ow now) by (rewrite <- (entry_eq G ow now LG); reflexivity)
    end.
    rewrite EE in HE9, LE9.
    assert (HN : bytes_at rsegs mC t (sub T1' 0 (Z.to_nat (48 * n)) ++ new_entry G ow now ++
                                       sub T1' (48 * n + 48) (Z.to_nat (400 - (48 * n + 48))))).
    { apply join3 with (k := 48 * n).
      - exact HP.
      - rewrite LP. lia.
      - rewrite <- He. exact HE9.
      - rewrite LE9, <- He. replace (e + Z.of_nat 48) with (t + (48 * n + 48)) by lia. exact HS. }
    assert (EQN : upd T1' (48 * n) (new_entry G ow now) = sub T1' 0 (Z.to_nat (48 * n)) ++ new_entry G ow now ++
                    sub T1' (48 * n + 48) (Z.to_nat (400 - (48 * n + 48)))).
    { rewrite upd_split by (rewrite ?LE9, ?LX1; lia). rewrite LE9, LX1. do 3 f_equal; lia. }
    rewrite <- EQN in HN.
    assert (LN : length (upd T1' (48 * n) (new_entry G ow now)) = 400%nat)
      by (rewrite upd_len; [exact LX1 | lia | rewrite LE9, LX1; lia]).
    do 2 step.
    apply (SEQ _ (upd T1' (48 * n) (new_entry G ow now)) 1); try assumption.
    exists (-1). split; [left; split; [reflexivity | exact NF]|].
    right; right. split; [reflexivity|]. split; [lia|]. reflexivity. }
  assert (NOTF : forall (m2 : word -> option byte)
                   (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31 : word),
      (forall j, 0 <= j < n -> mac_of T j <> s_mac G) ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G -> bytes_at rsegs m2 t T ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x19 (Z_to_bv 64 now)
                            (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 n) x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15968) fc None m2 (seg_rom rsegs))).
  { intros m2 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x28 x29 x30 x31
      NF FR2 ST2 MU2 WM2 MI2 WT2 HG2 HT2.
    step. step. rewrite lts_lit by lia.
    destruct (Z.ltb_spec n 8) as [L8|L8]; cbn [negb].
    - apply NEW; assumption.
    - pose proof (bytes_at_sub _ t T 392 4 HT2 ltac:(lia) ltac:(rewrite LT; lia)) as FSq.
      pose proof (length_sub T 392 4 ltac:(lia) ltac:(rewrite LT; lia)) as LSq.
      rdx t 388 4%nat. step. vals. fold_u.
      step. rewrite eqb_s32_c by lia.
      destruct (Z.eqb_spec (s32_at T 388) 0) as [V0|V0]; cbn [negb].
      + step. sok t 388 4%nat. step. tstore t. rewrite le4_word in *. step.
        rewrite V0.
        apply (SEQ _ (upd T 388 (Z_to_le_bytes 4 1)) 0); try assumption.
        exists (-1). split; [left; split; [reflexivity | exact NF]|].
        right; left. split; [reflexivity|]. split; [lia|].
        unfold observe_full, ov_of. rewrite V0. reflexivity.
      + step. step.
        apply (EPI _ T 0); try assumption.
        exists (-1). split; [left; split; [reflexivity | exact NF]|].
        right; left. split; [reflexivity|]. split; [lia|].
        unfold observe_full, ov_of. replace (s32_at T 388 =? 0) with false by (symmetry; apply Z.eqb_neq; exact V0).
        reflexivity. }
  assert (LOOP : forall k i (m2 : word -> option byte)
                   (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      Z.of_nat k = n - i -> 0 <= i < n ->
      (forall j, 0 <= j < i -> mac_of T j <> s_mac G) ->
      rw_cells rsegs m2 (bv_unsigned sp + -96) FRC -> stk rsegs m2 lo (bv_unsigned sp + -96) ->
      munch [(t, t + 400); (bv_unsigned sp + -96, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
      wr_at rsegs m2 t 400 -> bytes_at rsegs m2 s G -> bytes_at rsegs m2 t T ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 ow)
                            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x19 (Z_to_bv 64 now)
                            (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 n) (Z_to_bv 64 (48 * i)) (Z_to_bv 64 (48 * n))
                            (Z_to_bv 64 384) s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15940) fc None m2 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m2 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 Hk Hi NP
        FR2 ST2 MU2 WM2 MI2 WT2 HG2 HT2; [lia|].
    step. rewrite eqb_lit by lia. replace (48 * i =? 384) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    step. rewrite ltu_lit by lia.
    replace (2^64 - 1 - t <? 48 * i) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
    do 5 step.
    destruct (memcmp6 (mac_of T i) (s_mac G) ltac:(unfold mac_of; apply length_sub; lia)
                ltac:(unfold s_mac; apply length_sub; lia)) as (v & Hv & Veq & Vr).
    eapply evt_cut.
    { eapply BC with (ls := mac_of T i) (rs := s_mac G) (v := v).
      - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact HT2 | lia | rewrite LT; lia].
      - rewrite unsigned_lit by lia. unfold s_mac.
        pose proof (bytes_at_sub _ s G 0 6 HG2 ltac:(lia) ltac:(rewrite LG; lia)) as X. rewrite Z.add_0_r in X. exact X.
      - exact Hv.
      - exact MI2. }
    post_call rsegs m2.
    step.
    rewrite eqb_small by exact Vr.
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb].
    - subst v.
      apply KNOWN; try assumption. right. split; [lia|]. split; [apply Veq; reflexivity | exact NP].
    - assert (NE : mac_of T i <> s_mac G) by (intro E; apply V0; apply Veq; exact E).
      step. step. rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (48 * n) (48 * i + 48)) as [Z0|Z0]; cbn [negb].
      + apply NOTF; try assumption.
        intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia.
      + replace (48 * i + 48) with (48 * (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; try lia.
        intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia. }
  destruct (Z.ltb_spec 0 n) as [Hn|Hn]; cbn [negb].
  - do 8 step. rewrite sgtz_and_lit by lia. rewrite mul48_lit by lia.
    apply (LOOP (Z.to_nat n) 0); try assumption; try lia.
  - apply NEW; try assumption; try lia; intros j Hj; lia.
Qed.
