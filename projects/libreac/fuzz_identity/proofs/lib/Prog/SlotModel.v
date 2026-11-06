From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of_c.
Import ListNotations.
Open Scope Z_scope.

Definition nlen (inp : list byte) : Z := Z.of_nat (length inp).
Definition inb (inp : list byte) (j : Z) : Z := bz (nthb inp (Z.to_nat j)).
Definition nrec (inp : list byte) : Z := inb inp 0 mod 65.
Definition nrecn (inp : list byte) : nat := Z.to_nat (nrec inp).

Definition h_left (inp : list byte) (c : Z) : Z := nlen inp - c.
Definition h_h (inp : list byte) (c : Z) : Z := Z.min (h_left inp c) 3.
Definition h_lo (inp : list byte) (c : Z) : Z := inb inp c.
Definition h_hi (inp : list byte) (c : Z) : Z := inb inp (c + 1).
Definition h_w (inp : list byte) (c : Z) : Z := inb inp (c + 2).
Definition h_raw (inp : list byte) (c : Z) : Z := h_lo inp c + 256 * h_hi inp c.
Definition pick (raw : Z) : Z :=
  if raw / 16384 =? 0 then ADDR_FIRMWARE
  else if raw / 16384 =? 1 then ADDR_REAC_VERSION
  else if raw / 16384 =? 2 then ADDR_MODEL_NAME
  else raw.
Definition h_Lp (inp : list byte) (c : Z) : Z := h_left inp c - h_h inp c.
Definition h_k (inp : list byte) (c : Z) : Z := Z.min (h_w inp c) (h_Lp inp c).
Definition h_body (inp : list byte) (c : Z) : Z := c + h_h inp c.
Definition h_pl (inp : list byte) (c : Z) : list byte :=
  firstn (Z.to_nat (h_k inp c)) (skipn (Z.to_nat (h_body inp c)) inp).
Definition h_next (inp : list byte) (c : Z) : Z := h_body inp c + h_k inp c.

Fixpoint rec_c (inp : list byte) (i : nat) : Z :=
  match i with
  | O => Z.min 1 (nlen inp)
  | S i' => h_next inp (rec_c inp i')
  end.
Definition rec_left (inp : list byte) (i : nat) : Z := h_left inp (rec_c inp i).
Definition rec_h (inp : list byte) (i : nat) : Z := h_h inp (rec_c inp i).
Definition rec_raw (inp : list byte) (i : nat) : Z := h_raw inp (rec_c inp i).
Definition rec_addr (inp : list byte) (i : nat) : Z := pick (rec_raw inp i).
Definition rec_w (inp : list byte) (i : nat) : Z := h_w inp (rec_c inp i).
Definition rec_Lp (inp : list byte) (i : nat) : Z := h_Lp inp (rec_c inp i).
Definition rec_k (inp : list byte) (i : nat) : Z := h_k inp (rec_c inp i).
Definition rec_body (inp : list byte) (i : nat) : Z := h_body inp (rec_c inp i).
Definition rec_pl (inp : list byte) (i : nat) : list byte := h_pl inp (rec_c inp i).

Fixpoint rec_id (inp : list byte) (i : nat) : list byte :=
  match i with
  | O => ID0
  | S i' => snd (ING (rec_id inp i') (rec_addr inp i') (rec_pl inp i'))
  end.
Definition rec_r (inp : list byte) (i : nat) : Z := fst (ING (rec_id inp i) (rec_addr inp i) (rec_pl inp i)).

Fixpoint rec_hw (inp : list byte) (i : nat) : option (list byte) :=
  match i with
  | O => None
  | S i' =>
      if (rec_addr inp i' =? ADDR_REAC_VERSION) && (8 <=? rec_k inp i')
      then Some (firstn 8 (rec_pl inp i'))
      else rec_hw inp i'
  end.
Definition rec_have (inp : list byte) (i : nat) : Z := match rec_hw inp i with Some _ => 1 | None => 0 end.
Definition rec_hwb (inp : list byte) (i : nat) : list byte :=
  match rec_hw inp i with Some h => h | None => repeat (zb 0) 8 end.

Definition idT (inp : list byte) : list byte := rec_id inp (nrecn inp).
Definition cT (inp : list byte) : Z := rec_c inp (nrecn inp).
Definition haveT (inp : list byte) : Z := rec_have inp (nrecn inp).
Definition hwbT (inp : list byte) : list byte := rec_hwb inp (nrecn inp).
Definition tb (inp : list byte) (j : Z) : Z := inb inp (cT inp + j).
Definition t_fam_raw (inp : list byte) : Z := tb inp 0.
Definition t_in (inp : list byte) : Z := tb inp 1.
Definition t_out (inp : list byte) : Z := tb inp 2.
Definition t_cap_fw (inp : list byte) : Z := tb inp 3 mod 16.
Definition t_cap_ver (inp : list byte) : Z := tb inp 4 mod 32.
Definition t_cap_name (inp : list byte) : Z := tb inp 5 mod 40.
Definition t_cap_tok (inp : list byte) : Z := tb inp 6 mod 40.
Definition t_cap_disp (inp : list byte) : Z := tb inp 7 mod 64.
Definition t_row (inp : list byte) : Z := tb inp 8.
Definition t_any_fw (inp : list byte) : Z := tb inp 9 + 256 * tb inp 10.

Definition FAM (idb : list byte) : Z := reac_box_family_of_c.FAMOF_FAM 1 idb.
Definition HWT (j : nat) : list Z :=
  nth j [reac_box_family_of_c.FAMOF_HW1; reac_box_family_of_c.FAMOF_HW2; reac_box_family_of_c.FAMOF_HW3] [].
Definition fam_cmp (hw : list byte) : Z :=
  let h := map bv_unsigned hw in
  if list_eq_dec Z.eq_dec h reac_box_family_of_c.FAMOF_HW1 then 1
  else if list_eq_dec Z.eq_dec h reac_box_family_of_c.FAMOF_HW2 then 2
  else if list_eq_dec Z.eq_dec h reac_box_family_of_c.FAMOF_HW3 then 3
  else 0.
Definition fam_hw (have : Z) (hw : list byte) : Z := if have =? 0 then 0 else fam_cmp hw.

Definition dot : byte := zb 46.
Definition dash : byte := zb 45.
Definition t_EF (inp : list byte) : list byte :=
  DEC (t_any_fw inp / 1000) 1 ++ [dot] ++ DEC (t_any_fw inp mod 1000) 3.

Definition str_bytes (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string s).
Definition stem_img (f : Z) : list byte :=
  str_bytes (if f =? 1 then "S-0808"%string
             else if f =? 2 then "S-1608"%string
             else if f =? 3 then "S-4000S"%string
             else "REAC"%string).
Definition name_str (idb : list byte) : list byte := firstn (first_zero (model_name idb)) (model_name idb).

Definition n_fam (inp : list byte) : Z :=
  if 128 <=? t_fam_raw inp then Z.land (t_fam_raw inp) 127 else FAM (idT inp).
Definition n_said (inp : list byte) : bool := negb (has_model_name (idT inp) =? 0).
Definition n_use_said (inp : list byte) : bool :=
  n_said inp && negb (bz (nthb (model_name (idT inp)) 0) =? 0).
Definition n_stem (inp : list byte) : list byte :=
  if n_use_said inp then name_str (idT inp) else stem_img (n_fam inp).
Definition okw (v : Z) : bool := (v =? 0) || ((2 <=? v) && (v <=? 40) && Z.even v).
Definition n_wok (inp : list byte) : bool :=
  okw (t_in inp) && okw (t_out inp) && negb ((t_in inp =? 0) && (t_out inp =? 0)).
Definition n_W4 (inp : list byte) : list byte := DEC (t_in inp) 2 ++ DEC (t_out inp) 2.
Definition n_ends_w4 (inp : list byte) : bool :=
  (4 <=? length (n_stem inp))%nat &&
  bytes_eqb (skipn (length (n_stem inp) - 4) (n_stem inp)) (firstn 4 (n_W4 inp)).
Definition n_EXP_NM (inp : list byte) : list byte :=
  if n_ends_w4 inp then n_stem inp else n_stem inp ++ [dash] ++ n_W4 inp.
Definition n_EXP_DP (inp : list byte) : list byte :=
  n_EXP_NM inp ++ str_bytes " ("%string ++ DEC (t_in inp) 1 ++ str_bytes " in / "%string ++
  DEC (t_out inp) 1 ++ str_bytes " out)"%string.
Definition has_dash (l : list byte) : bool := existsb (fun b => bz b =? 45) l.
Definition n_ln (inp : list byte) : Z := Z.of_nat (length (n_EXP_NM inp)).
Definition n_lt (inp : list byte) : Z := n_ln inp - (if has_dash (n_EXP_NM inp) then 1 else 0).
Definition n_ld (inp : list byte) : Z := Z.of_nat (length (n_EXP_DP inp)).
Definition n_fits (inp : list byte) : bool :=
  (n_ln inp <? t_cap_name inp) && (n_lt inp <? t_cap_tok inp) && (n_ld inp <? t_cap_disp inp).
Definition lower (b : byte) : byte := if (65 <=? bz b) && (bz b <=? 90) then zb (bz b + 32) else b.
Fixpoint tok_go (dropped : bool) (l : list byte) : list byte :=
  match l with
  | [] => []
  | b :: r => if negb dropped && (bz b =? 45) then tok_go true r else lower b :: tok_go dropped r
  end.
Definition TOK (l : list byte) : list byte := tok_go false l.
Definition n_TK (inp : list byte) : list byte := TOK (n_EXP_NM inp).
Definition n_r (inp : list byte) : Z := if n_wok inp && n_fits inp then 0 else -1.

Lemma bz_range : forall b : byte, 0 <= bz b < 256.
Proof. intro b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

Lemma inb_range : forall inp j, 0 <= inb inp j < 256.
Proof. intros. apply bz_range. Qed.

Lemma nlen_nonneg : forall inp, 0 <= nlen inp.
Proof. intro. unfold nlen. lia. Qed.

Lemma nrec_range : forall inp, 0 <= nrec inp <= 64.
Proof.
  intro inp. unfold nrec. pose proof (inb_range inp 0).
  pose proof (Z.mod_pos_bound (inb inp 0) 65 ltac:(lia)). lia.
Qed.

Lemma h_bounds : forall inp c, 0 <= c <= nlen inp ->
  0 <= h_h inp c <= 3 /\ 0 <= h_body inp c /\ h_body inp c + h_k inp c <= nlen inp /\
  0 <= h_k inp c <= 255 /\ h_Lp inp c = nlen inp - h_body inp c /\ h_k inp c <= h_Lp inp c /\
  c <= h_next inp c <= nlen inp.
Proof.
  intros inp c Hc. pose proof (inb_range inp (c + 2)).
  unfold h_next, h_body, h_k, h_Lp, h_h, h_left, h_w. lia.
Qed.

Lemma h_k_range : forall inp c, 0 <= h_k inp c <= 255.
Proof. intros. unfold h_k, h_Lp, h_h, h_w. pose proof (inb_range inp (c + 2)). lia. Qed.

Lemma rec_k_range : forall inp i, 0 <= rec_k inp i <= 255.
Proof. intros. apply h_k_range. Qed.

Lemma rec_c_range : forall inp i, 0 <= rec_c inp i <= nlen inp.
Proof.
  intros inp i. pose proof (nlen_nonneg inp). induction i as [|i IH]; cbn [rec_c]; [lia|].
  pose proof (h_bounds inp (rec_c inp i) IH). lia.
Qed.

Lemma rec_bounds : forall inp i,
  0 <= rec_h inp i <= 3 /\ 0 <= rec_body inp i /\ rec_body inp i + rec_k inp i <= nlen inp /\
  rec_Lp inp i = nlen inp - rec_body inp i /\ rec_k inp i <= rec_Lp inp i /\
  rec_c inp (S i) = rec_body inp i + rec_k inp i.
Proof.
  intros inp i. pose proof (h_bounds inp (rec_c inp i) (rec_c_range inp i)) as (H1 & H2 & H3 & _ & H5 & H6 & _).
  unfold rec_h, rec_body, rec_k, rec_Lp. cbn [rec_c]. unfold h_next. lia.
Qed.

Lemma h_pl_length : forall inp c, 0 <= c <= nlen inp -> length (h_pl inp c) = Z.to_nat (h_k inp c).
Proof.
  intros inp c Hc. pose proof (h_bounds inp c Hc) as (_ & H2 & H3 & H4 & _).
  unfold h_pl. rewrite length_firstn, length_skipn. unfold nlen in *. lia.
Qed.

Lemma rec_pl_length : forall inp i, length (rec_pl inp i) = Z.to_nat (rec_k inp i).
Proof. intros. unfold rec_pl, rec_k. apply h_pl_length. apply rec_c_range. Qed.

Lemma rec_id_length : forall inp i, length (rec_id inp i) = ID_SIZE.
Proof. intros inp i. induction i as [|i IH]; cbn [rec_id]; [reflexivity|]. apply ING_length. exact IH. Qed.

Lemma rec_r_range : forall inp i, rec_r inp i = 0 \/ rec_r inp i = 1.
Proof. intros. apply ING_ret. Qed.

Lemma nth_skip0 : forall (l : list byte) i d, nth i l d = nth 0 (skipn i l) d.
Proof. induction l as [|x l IH]; intros [|i] d; cbn; try reflexivity. apply IH. Qed.

Lemma nth_first : forall (l : list byte) k i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof. induction l as [|x l IH]; intros [|k] [|i] d H; cbn; try reflexivity; try lia. apply IH. lia. Qed.

Lemma skipn_upd_before : forall (l bs : list byte) off o,
  (off <= length l)%nat -> (off + length bs <= o)%nat -> skipn o (upd l off bs) = skipn o l.
Proof.
  intros l bs off o H1 H2. unfold upd. rewrite app_assoc, skipn_app.
  assert (E : skipn o (firstn off l ++ bs) = []) by (apply skipn_all2; rewrite length_app, length_firstn; lia).
  rewrite E, skipn_skipn, length_app, length_firstn. cbn [app]. f_equal. lia.
Qed.

Lemma nth_upd_after : forall (l bs : list byte) off i d,
  (off <= length l)%nat -> (off + length bs <= i)%nat -> nth i (upd l off bs) d = nth i l d.
Proof.
  intros l bs off i d H1 H2. rewrite (nth_skip0 (upd l off bs)), (nth_skip0 l).
  rewrite skipn_upd_before by assumption. reflexivity.
Qed.

Lemma nth_upd_before : forall (l bs : list byte) off i d,
  (i < off)%nat -> (off <= length l)%nat -> nth i (upd l off bs) d = nth i l d.
Proof.
  intros l bs off i d H1 H2. unfold upd. rewrite app_nth1 by (rewrite length_firstn; lia).
  apply nth_first. exact H1.
Qed.

Lemma nth_upd_in : forall (l bs : list byte) off i d,
  (off <= length l)%nat -> (off <= i < off + length bs)%nat -> nth i (upd l off bs) d = nth (i - off) bs d.
Proof.
  intros l bs off i d H1 H2. unfold upd.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  rewrite app_nth1 by lia. f_equal. lia.
Qed.

Lemma get_upd_before : forall (l bs : list byte) off o m,
  (off <= length l)%nat -> (off + length bs <= o)%nat -> get (upd l off bs) o m = get l o m.
Proof. intros l bs off o m H1 H2. unfold get. rewrite skipn_upd_before by assumption. reflexivity. Qed.

Lemma get_upd_after : forall (l bs : list byte) off o m,
  (o + m <= off)%nat -> (off <= length l)%nat -> get (upd l off bs) o m = get l o m.
Proof.
  intros l bs off o m H1 H2. unfold get, upd.
  rewrite skipn_app, firstn_app, length_skipn, length_firstn.
  replace (m - (Nat.min off (length l) - o))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn.
  replace (Nat.min m (off - o)) with m by lia. reflexivity.
Qed.

Lemma get_upd_same : forall (l bs : list byte) off m,
  length bs = m -> (off + m <= length l)%nat -> get (upd l off bs) off m = bs.
Proof.
  intros l bs off m Hm H. subst m. unfold get, upd.
  rewrite skipn_app, length_firstn.
  assert (E : skipn off (firstn off l) = []) by (apply skipn_all2; rewrite length_firstn; lia).
  rewrite E, app_nil_l. replace (off - Nat.min off (length l))%nat with 0%nat by lia.
  change (skipn 0 (bs ++ skipn (off + length bs) l)) with (bs ++ skipn (off + length bs) l).
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
Qed.

Ltac lsolve :=
  unfold ID_SIZE, OFF_FW, OFF_HAS_FW, OFF_NAME, OFF_HAS_NAME, OFF_MAJOR, OFF_MINOR, OFF_PATCH,
    OFF_RAW, OFF_HAS_VER, REAC_VER_LEN, NAME_CAP in *;
  repeat match goal with |- context [length (upd ?l ?o ?b)] => rewrite (upd_length l o b) by lsolve end;
  cbn [length le16 app] in *; rewrite ?length_app, ?length_firstn in *; cbn [length] in *; lia.

Lemma name_len_le : forall p, (name_len p <= 16)%nat /\ (name_len p <= length p - 1)%nat.
Proof. intro p. unfold name_len, NAME_CAP. lia. Qed.

Lemma ING_keep21 : forall idb a p, length idb = ID_SIZE -> a <> ADDR_REAC_VERSION ->
  skipn 21 (snd (ING idb a p)) = skipn 21 idb.
Proof.
  intros idb a p Hl Ha. pose proof (name_len_le p) as [Hw1 Hw2].
  unfold ING, ing_firmware, ing_name, ing_version. cbv zeta.
  destruct (a =? ADDR_FIRMWARE).
  - destruct ((4 <=? length p)%nat && all_digits (firstn 4 p)); cbn [snd]; [|reflexivity].
    rewrite skipn_upd_before by lsolve. rewrite skipn_upd_before by lsolve. reflexivity.
  - destruct (a =? ADDR_MODEL_NAME).
    + destruct ((2 <=? length p)%nat && (1 <=? name_len p)%nat); cbn [snd]; [|reflexivity].
      rewrite skipn_upd_before by lsolve. rewrite skipn_upd_before by lsolve. reflexivity.
    + destruct (Z.eqb_spec a ADDR_REAC_VERSION); [contradiction|]. reflexivity.
Qed.

Lemma ING_ver_dispatch : forall idb p, ING idb ADDR_REAC_VERSION p = ing_version idb p.
Proof. intros. reflexivity. Qed.

Lemma ING_ver_short : forall idb p, (length p < 8)%nat -> ING idb ADDR_REAC_VERSION p = (0, idb).
Proof.
  intros idb p Hp. rewrite ING_ver_dispatch. unfold ing_version.
  destruct (Nat.leb_spec REAC_VER_LEN (length p)) as [E|E]; [unfold REAC_VER_LEN in E; lia|]. reflexivity.
Qed.

Lemma ING_ver_long : forall idb p, length idb = ID_SIZE -> (8 <= length p)%nat ->
  has_reac_version (snd (ING idb ADDR_REAC_VERSION p)) = 1 /\
  raw (snd (ING idb ADDR_REAC_VERSION p)) = firstn 8 p /\
  nthb (snd (ING idb ADDR_REAC_VERSION p)) 19 = nthb idb 19.
Proof.
  intros idb p Hl Hp. rewrite ING_ver_dispatch. unfold ing_version.
  destruct (Nat.leb_spec REAC_VER_LEN (length p)) as [E|E]; [|unfold REAC_VER_LEN in E; lia]. cbn [snd].
  split; [|split].
  - unfold has_reac_version, nthb. rewrite nth_upd_in by lsolve. reflexivity.
  - unfold raw. rewrite get_upd_after by lsolve.
    rewrite get_upd_before by lsolve. rewrite get_upd_before by lsolve. rewrite get_upd_before by lsolve.
    rewrite get_upd_same by lsolve. reflexivity.
  - unfold nthb. rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve.
    rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve.
    reflexivity.
Qed.

Lemma win_eq : forall x y : list byte, skipn 21 x = skipn 21 y ->
  has_reac_version x = has_reac_version y /\ raw x = raw y.
Proof.
  intros x y E.
  assert (E36 : skipn 36 x = skipn 36 y).
  { change (skipn 36 x) with (skipn (15 + 21) x). change (skipn 36 y) with (skipn (15 + 21) y).
    rewrite <- (skipn_skipn 15 21 x), <- (skipn_skipn 15 21 y), E. reflexivity. }
  assert (E28 : skipn 28 x = skipn 28 y).
  { change (skipn 28 x) with (skipn (7 + 21) x). change (skipn 28 y) with (skipn (7 + 21) y).
    rewrite <- (skipn_skipn 7 21 x), <- (skipn_skipn 7 21 y), E. reflexivity. }
  unfold has_reac_version, raw, nthb, get, OFF_HAS_VER, OFF_RAW, REAC_VER_LEN.
  rewrite (nth_skip0 x), (nth_skip0 y), E36, E28. split; reflexivity.
Qed.

Lemma rec_hw_inv : forall inp i,
  match rec_hw inp i with
  | None => has_reac_version (rec_id inp i) = 0
  | Some h => has_reac_version (rec_id inp i) = 1 /\ h = raw (rec_id inp i)
  end.
Proof.
  intros inp i. induction i as [|i IH]; cbn [rec_hw rec_id]; [reflexivity|].
  pose proof (rec_id_length inp i) as Hl. pose proof (rec_pl_length inp i) as Hp.
  pose proof (rec_k_range inp i) as Hk.
  destruct (Z.eqb_spec (rec_addr inp i) ADDR_REAC_VERSION) as [Ea|Ea]; cbn [andb].
  - rewrite Ea. destruct (Z.leb_spec 8 (rec_k inp i)) as [E8|E8]; cbv beta iota.
    + destruct (ING_ver_long (rec_id inp i) (rec_pl inp i) Hl ltac:(lia)) as (H1 & H2 & _).
      split; [exact H1|]. rewrite H2. reflexivity.
    + rewrite ING_ver_short by lia. cbn [snd]. exact IH.
  - destruct (win_eq _ _ (ING_keep21 (rec_id inp i) (rec_addr inp i) (rec_pl inp i) Hl Ea)) as [W1 W2].
    cbv beta iota. revert IH. destruct (rec_hw inp i) as [h|]; intro IH.
    + rewrite W1, W2. exact IH.
    + rewrite W1. exact IH.
Qed.

Lemma rec_F2 : forall inp i,
  rec_have inp i = has_reac_version (rec_id inp i) /\
  (rec_have inp i = 1 -> rec_hwb inp i = raw (rec_id inp i)).
Proof.
  intros inp i. pose proof (rec_hw_inv inp i) as H. unfold rec_have, rec_hwb. revert H.
  destruct (rec_hw inp i) as [h|]; intro H.
  - destruct H as [H1 H2]. split; [symmetry; exact H1|]. intros _. exact H2.
  - split; [symmetry; exact H|]. intro E. discriminate E.
Qed.

Lemma FAM_unfold : forall idb, FAM idb = fam_hw (has_reac_version idb) (raw idb).
Proof. intros. reflexivity. Qed.

Lemma rec_P7 : forall inp i, FAM (rec_id inp i) = fam_hw (rec_have inp i) (rec_hwb inp i).
Proof.
  intros inp i. destruct (rec_F2 inp i) as [E1 E2]. rewrite FAM_unfold, <- E1. unfold fam_hw.
  destruct (Z.eqb_spec (rec_have inp i) 0) as [Z0|NZ]; [reflexivity|].
  rewrite E2; [reflexivity|]. revert NZ. unfold rec_have. destruct (rec_hw inp i); intro NZ; [reflexivity|].
  exfalso. apply NZ. reflexivity.
Qed.

Lemma first_zero_le : forall l i, (i < length l)%nat -> bz (nth i l (zb 0)) = 0 -> (first_zero l <= i)%nat.
Proof.
  intros l. induction l as [|x l IH]; intros i H1 H2.
  - cbn [length] in H1. lia.
  - cbn [first_zero]. destruct (Z.eqb_spec (bz x) 0) as [E|E]; [lia|].
    destruct i as [|i].
    + cbn [nth] in H2. contradiction.
    + cbn [length nth] in H1, H2. specialize (IH i ltac:(lia) H2). lia.
Qed.

Lemma ING_b19 : forall idb a p, length idb = ID_SIZE -> bz (nthb idb 19) = 0 ->
  bz (nthb (snd (ING idb a p)) 19) = 0.
Proof.
  intros idb a p Hl H19. pose proof (name_len_le p) as [Hw1 Hw2].
  unfold ING, ing_firmware, ing_name, ing_version. cbv zeta. unfold nthb in *.
  destruct (a =? ADDR_FIRMWARE).
  - destruct ((4 <=? length p)%nat && all_digits (firstn 4 p)); cbn [snd]; [|exact H19].
    rewrite nth_upd_after by lsolve. rewrite nth_upd_after by lsolve. exact H19.
  - destruct (a =? ADDR_MODEL_NAME).
    + destruct ((2 <=? length p)%nat && (1 <=? name_len p)%nat); cbn [snd]; [|exact H19].
      rewrite nth_upd_before by lsolve.
      assert (Lw : length (firstn (name_len p) (skipn 1 p)) = name_len p)
        by (rewrite length_firstn, length_skipn; lia).
      destruct (Nat.eq_dec (name_len p) 16) as [W|W].
      * rewrite nth_upd_in by lsolve. unfold OFF_NAME. rewrite app_nth2 by lia. rewrite Lw, W. reflexivity.
      * rewrite nth_upd_after by lsolve. exact H19.
    + destruct (a =? ADDR_REAC_VERSION); cbn [snd]; [|exact H19].
      destruct (REAC_VER_LEN <=? length p)%nat; cbn [snd]; [|exact H19].
      rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve.
      rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve. rewrite nth_upd_before by lsolve.
      exact H19.
Qed.

Lemma rec_id_b19 : forall inp i, bz (nthb (rec_id inp i) 19) = 0.
Proof.
  intros inp i. induction i as [|i IH]; cbn [rec_id]; [reflexivity|].
  apply ING_b19; [apply rec_id_length | exact IH].
Qed.

Lemma name_str_len : forall inp i, (length (name_str (rec_id inp i)) <= 16)%nat.
Proof.
  intros inp i. pose proof (rec_id_length inp i) as Hl. unfold ID_SIZE in Hl.
  assert (Lm : length (model_name (rec_id inp i)) = 17%nat)
    by (unfold model_name, get, OFF_NAME, NAME_CAP; rewrite length_firstn, length_skipn; lia).
  assert (Hm : nth 16 (model_name (rec_id inp i)) (zb 0) = nth 19 (rec_id inp i) (zb 0)).
  { unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
    rewrite (nth_skip0 (skipn 3 (rec_id inp i))), skipn_skipn, <- nth_skip0. reflexivity. }
  pose proof (first_zero_le (model_name (rec_id inp i)) 16 ltac:(lia)) as F.
  rewrite Hm in F. specialize (F (rec_id_b19 inp i)).
  unfold name_str. rewrite length_firstn. lia.
Qed.

Lemma stem_img_len : forall f, (length (stem_img f) <= 7)%nat.
Proof.
  intro f. unfold stem_img, str_bytes. rewrite length_map.
  destruct (f =? 1); [cbn; lia|]. destruct (f =? 2); [cbn; lia|]. destruct (f =? 3); cbn; lia.
Qed.

Lemma n_stem_len : forall inp, (length (n_stem inp) <= 16)%nat.
Proof.
  intro inp. unfold n_stem. destruct (n_use_said inp).
  - apply name_str_len.
  - pose proof (stem_img_len (n_fam inp)). lia.
Qed.

Lemma DEC2_len : forall x, 0 <= x <= 40 -> length (DEC x 2) = 2%nat.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => Nat.eqb (length (DEC x 2)) 2) (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x
    ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma DEC1_len : forall x, 0 <= x <= 40 -> (1 <= length (DEC x 1) <= 2)%nat.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => (1 <=? length (DEC x 1))%nat && (length (DEC x 1) <=? 2)%nat) (Z.to_nat 41) 0
    ltac:(vm_compute; reflexivity) x ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H1, H2. lia.
Qed.

Lemma okw_le : forall v, 0 <= v -> okw v = true -> v <= 40.
Proof.
  intros v Hv H. unfold okw in H. apply orb_true_iff in H as [H|H].
  - apply Z.eqb_eq in H. lia.
  - apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H]. apply Z.leb_le in H. exact H.
Qed.

Lemma wok_chans : forall inp, n_wok inp = true -> 0 <= t_in inp <= 40 /\ 0 <= t_out inp <= 40.
Proof.
  intros inp H. unfold n_wok in H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
  pose proof (inb_range inp (cT inp + 1)). pose proof (inb_range inp (cT inp + 2)).
  unfold t_in, t_out, tb in *. split; split; try lia; apply okw_le; auto; lia.
Qed.

Lemma n_ln_le : forall inp, n_wok inp = true -> 1 <= n_ln inp <= 21.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  pose proof (n_stem_len inp). pose proof (DEC2_len _ Hi). pose proof (DEC2_len _ Ho).
  unfold n_ln, n_EXP_NM, n_ends_w4, n_W4 in *.
  destruct (4 <=? length (n_stem inp))%nat eqn:E4; cbn [andb].
  - apply Nat.leb_le in E4.
    match goal with |- context [if bytes_eqb ?x ?y then _ else _] => destruct (bytes_eqb x y) end;
      rewrite ?length_app; cbn [length]; lia.
  - rewrite !length_app. cbn [length]. lia.
Qed.

Lemma n_ld_le : forall inp, n_wok inp = true -> n_ld inp <= 38.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  pose proof (n_ln_le inp H). pose proof (DEC1_len _ Hi). pose proof (DEC1_len _ Ho).
  unfold n_ld, n_EXP_DP, n_ln in *. rewrite !length_app.
  change (length (str_bytes " ("%string)) with 2%nat. change (length (str_bytes " in / "%string)) with 6%nat.
  change (length (str_bytes " out)"%string)) with 5%nat. lia.
Qed.
