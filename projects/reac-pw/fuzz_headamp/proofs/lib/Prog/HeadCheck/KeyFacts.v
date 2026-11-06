(** Facts for the key piece of the checking segment of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput (plain
    0x1433c-0x14600; fuzz_headamp.c:67-90, :122-143, :94-107): the byte tests the compiled read_channel makes, the model's
    read_channel (Pod/Headamp.v rc_blanks, rc_sign, rc_digits) one byte at a time as the code reads it, the strcmp chain
    against param_of_name, the channel range test and the three cases of cell_value. No function of a binary is proved
    here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

(** ** The byte tests of the compiled read_channel *)
Lemma zxb_unsigned : forall b, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Lemma zxb_eqb : forall b z, 0 <= z < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 z) = (bv_unsigned b =? z).
Proof. intros b z Hz. unfold bv_eqb. rewrite zxb_unsigned, (unsigned_lit z) by lia. reflexivity. Qed.

(** `addi x, c, k; bltu x, n` on a byte c, k <= 0: c + k in [0, n). *)
Lemma zxb_add_ltu : forall b k n, -256 <= k <= 0 -> 0 <= n <= 256 ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + k)) (Z_to_bv 64 n) = (0 <=? bv_unsigned b + k) && (bv_unsigned b + k <? n).
Proof.
  intros b k n Hk Hn. unfold bv_ltu. rewrite zxb_unsigned. pose proof (byte_range b) as Hb.
  rewrite (unsigned_lit n) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.leb_spec 0 (bv_unsigned b + k)) as [H|H]; cbn [andb].
  - rewrite Z.mod_small by lia. reflexivity.
  - replace ((bv_unsigned b + k) mod 2^64) with (bv_unsigned b + k + 2^64)
      by (apply Z.mod_unique with (q := -1); lia).
    apply Z.ltb_ge. lia.
Qed.

(** `addi x, c, k; bltu n, x` on a byte c, k <= 0: c + k outside [0, n]. *)
Lemma zxb_add_gtu : forall b k n, -256 <= k <= 0 -> 0 <= n <= 256 ->
  bv_ltu (Z_to_bv 64 n) (Z_to_bv 64 (bv_unsigned (zxb b) + k)) =
  negb ((0 <=? bv_unsigned b + k) && (bv_unsigned b + k <=? n)).
Proof.
  intros b k n Hk Hn. unfold bv_ltu. rewrite zxb_unsigned. pose proof (byte_range b) as Hb.
  rewrite (unsigned_lit n) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.leb_spec 0 (bv_unsigned b + k)) as [H|H]; cbn [andb negb].
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec n (bv_unsigned b + k)), (Z.leb_spec (bv_unsigned b + k) n); first [reflexivity | exfalso; lia].
  - replace ((bv_unsigned b + k) mod 2^64) with (bv_unsigned b + k + 2^64)
      by (apply Z.mod_unique with (q := -1); lia).
    apply Z.ltb_lt. lia.
Qed.

(** isspace: `addi a3, a1, -9; bgeu a3, 5` (9 <= c <= 13), then `beq a1, 0x20`. *)
Lemma rc_blank_code : forall b, rc_blank b =
  ((0 <=? bv_unsigned b + -9) && (bv_unsigned b + -9 <? 5)) || (bv_unsigned b =? 32).
Proof.
  intros b. unfold rc_blank. set (c := bv_unsigned b).
  destruct (Z.eqb_spec c 32) as [E|E]; cbn [orb]; [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
  destruct (Z.leb_spec 0 (c + -9)), (Z.ltb_spec (c + -9) 5); cbn [andb];
    repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
    cbn [orb]; first [reflexivity | exfalso; lia].
Qed.

(** isdigit: `addi a3, a1, -0x30; bltu 9, a3` and `addi a5, a1, -0x30; bltu a5, 10`. *)
Lemma digit_gtu9 : forall b, bv_ltu (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned (zxb b) + -48)) = negb (rc_digit b).
Proof.
  intros b. rewrite zxb_add_gtu by lia. unfold rc_digit. f_equal.
  destruct (Z.leb_spec 0 (bv_unsigned b + -48)), (Z.leb_spec (bv_unsigned b + -48) 9),
    (Z.leb_spec 48 (bv_unsigned b)), (Z.leb_spec (bv_unsigned b) 57); cbn [andb]; first [reflexivity | exfalso; lia].
Qed.

Lemma digit_ltu10 : forall b, bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + -48)) (Z_to_bv 64 10) = rc_digit b.
Proof.
  intros b. rewrite zxb_add_ltu by lia. unfold rc_digit.
  destruct (Z.leb_spec 0 (bv_unsigned b + -48)), (Z.ltb_spec (bv_unsigned b + -48) 10),
    (Z.leb_spec 48 (bv_unsigned b)), (Z.leb_spec (bv_unsigned b) 57); cbn [andb]; first [reflexivity | exfalso; lia].
Qed.

(** `andi a1, a1, 0xf` on a digit. *)
Lemma land15_digit : forall c, 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
  intros c Hc. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16.
  symmetry. apply Z.mod_unique with (q := 3); lia.
Qed.

Lemma digit_land : forall b, rc_digit b = true -> Z.land (bv_unsigned (zxb b)) 15 = bv_unsigned b - 48.
Proof.
  intros b H. unfold rc_digit in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite zxb_unsigned. apply land15_digit. lia.
Qed.

(** The sign flag `addi a2, a1, -0x2d; snez a2, a2` after a '+' or a '-'. *)
Lemma snez_sign : forall b, bv_unsigned b = 43 \/ bv_unsigned b = 45 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (zxb b) + -45)) = Z_to_bv 64 (if bv_unsigned b =? 45 then 0 else 1).
Proof. intros b [E|E]; unfold v_sltu, c_ltu; rewrite zxb_unsigned, E; vm_compute; reflexivity. Qed.

(** The channel test `bltu 0x2f, s9` (fuzz_headamp.c:136 ch < 0 || ch >= 48). *)
Lemma range_gtu47 : forall ch, -2^63 <= ch < 2^63 ->
  bv_ltu (Z_to_bv 64 47) (Z_to_bv 64 ch) = (ch <? 0) || (HA_CHANNELS <=? ch).
Proof.
  intros ch H. unfold bv_ltu, HA_CHANNELS. rewrite (unsigned_lit 47) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec ch 0) as [N|N]; cbn [orb].
  - replace (ch mod 2^64) with (ch + 2^64) by (apply Z.mod_unique with (q := -1); lia). apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec 47 ch), (Z.leb_spec 48 ch); first [reflexivity | exfalso; lia].
Qed.

(** cell_value's int test `bltu a1, 0x100` (fuzz_headamp.c:103 0 <= i < 256) on the sign-extended int32. *)
Lemma int_ltu256 : forall i, -2^31 <= i < 2^31 -> bv_ltu (Z_to_bv 64 i) (Z_to_bv 64 256) = (0 <=? i) && (i <=? 255).
Proof.
  intros i H. unfold bv_ltu. rewrite (unsigned_lit 256) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.leb_spec 0 i) as [N|N]; cbn [andb].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec i 256), (Z.leb_spec i 255); first [reflexivity | exfalso; lia].
  - replace (i mod 2^64) with (i + 2^64) by (apply Z.mod_unique with (q := -1); lia). apply Z.ltb_ge. lia.
Qed.

(** pod_bool's `snez a0, a0` on the sign-extended word. *)
Lemma snez_s32 : forall r, 0 <= r < 2^32 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (s32 r)) = Z_to_bv 64 (if negb (r =? 0) then 1 else 0).
Proof.
  intros r Hr. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  unfold s32. destruct (Z.ltb_spec r (2^31)).
  - rewrite Z.mod_small by lia. destruct (Z.eqb_spec r 0) as [E|E]; [subst r; reflexivity|].
    rewrite (proj2 (Z.ltb_lt 0 r)) by lia. reflexivity.
  - replace ((r - 2^32) mod 2^64) with (r - 2^32 + 2^64) by (apply Z.mod_unique with (q := -1); lia).
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.eqb_neq r 0)) by lia. reflexivity.
Qed.

(** ** read_channel one byte at a time *)
(** The code reads the C string s with its NUL: the byte at i of s ++ [NUL] is nth i s NUL. *)
Lemma nth_app_nul : forall (s : list byte) i, nth i (s ++ [NUL]) NUL = nth i s NUL.
Proof.
  intros s i. destruct (Nat.lt_ge_cases i (length s)) as [H|H].
  - apply app_nth1. exact H.
  - rewrite app_nth2 by exact H. rewrite (nth_overflow s) by exact H.
    destruct (i - length s)%nat as [|j]; [reflexivity | destruct j; reflexivity].
Qed.

Lemma nth_nonnul_lt : forall (s : list byte) i, bv_unsigned (nth i s NUL) <> 0 -> (i < length s)%nat.
Proof.
  intros s i H. destruct (Nat.lt_ge_cases i (length s)) as [L|L]; [exact L|].
  rewrite nth_overflow in H by exact L. exfalso. apply H. reflexivity.
Qed.

Lemma rc_blanks_le : forall s, (rc_blanks s <= length s)%nat.
Proof. induction s as [|b s IH]; cbn [rc_blanks length]; [lia|]. destruct (rc_blank b); lia. Qed.

(** The blanks loop (fuzz_headamp.c:70-72): a blank at i <= rc_blanks s is before rc_blanks s; a non-blank there is
    at rc_blanks s. *)
Lemma rc_blanks_go : forall s i, (i <= rc_blanks s)%nat -> rc_blank (nth i s NUL) = true -> (S i <= rc_blanks s)%nat.
Proof.
  induction s as [|b s IH]; intros i Hi Hb; cbn [rc_blanks] in *.
  - destruct i; cbn [nth] in Hb; vm_compute in Hb; discriminate Hb.
  - destruct (rc_blank b) eqn:Eb.
    + destruct i as [|i]; [lia|]. cbn [nth] in Hb. specialize (IH i ltac:(lia) Hb). lia.
    + destruct i as [|i]; [cbn [nth] in Hb; rewrite Eb in Hb; discriminate Hb | lia].
Qed.

Lemma rc_blanks_stop : forall s i, (i <= rc_blanks s)%nat -> rc_blank (nth i s NUL) = false -> i = rc_blanks s.
Proof.
  induction s as [|b s IH]; intros i Hi Hb; cbn [rc_blanks] in *.
  - lia.
  - destruct (rc_blank b) eqn:Eb.
    + destruct i as [|i]; [cbn [nth] in Hb; rewrite Eb in Hb; discriminate Hb|].
      cbn [nth] in Hb. rewrite (IH i ltac:(lia) Hb). reflexivity.
    + lia.
Qed.

(** The sign (fuzz_headamp.c:74-75) at byte i. *)
Lemma rc_sign_at : forall s i, rc_sign (skipn i s) =
  (if (bv_unsigned (nth i s NUL) =? 43) || (bv_unsigned (nth i s NUL) =? 45)
   then (bv_unsigned (nth i s NUL) =? 45, 1%nat) else (false, 0%nat)).
Proof.
  intros s i. destruct (Nat.lt_ge_cases i (length s)) as [H|H].
  - rewrite (skipn_nth_cons s i NUL H). reflexivity.
  - rewrite skipn_all2 by exact H. rewrite nth_overflow by exact H. vm_compute. reflexivity.
Qed.

(** One digit of the digits loop (fuzz_headamp.c:79-85) at byte j. *)
Lemma rc_digits_at : forall s j acc big, rc_digits acc big (skipn j s) =
  (if rc_digit (nth j s NUL) then
     let r := if 1000000 <? acc then rc_digits acc true (skipn (S j) s)
              else rc_digits (acc * 10 + (bv_unsigned (nth j s NUL) - 48)) big (skipn (S j) s) in
     (fst (fst r), snd (fst r), S (snd r))
   else (acc, big, O)).
Proof.
  intros s j acc big. destruct (Nat.lt_ge_cases j (length s)) as [H|H].
  - rewrite (skipn_nth_cons s j NUL H). reflexivity.
  - rewrite skipn_all2 by exact H. rewrite nth_overflow by exact H. reflexivity.
Qed.

(** read_channel from the sign and the digits. *)
Lemma read_channel_eq : forall s neg sn acc big kk,
  rc_sign (skipn (rc_blanks s) s) = (neg, sn) ->
  rc_digits 0 false (skipn (rc_blanks s + sn) s) = (acc, big, kk) ->
  read_channel s =
  (if (kk =? 0)%nat then (0%nat, 0, big) else ((rc_blanks s + sn + kk)%nat, if neg then - acc else acc, big)).
Proof. intros s neg sn acc big kk E1 E2. unfold read_channel. rewrite E1. cbn [fst snd]. rewrite E2. reflexivity. Qed.

Lemma expect_key_read : forall s used ch big, read_channel s = (used, ch, big) ->
  expect_key s =
  (if (used =? 0)%nat || negb (bv_unsigned (nth used s NUL) =? 46) then KBad
   else match param_of_name (cstr (skipn (S used) s)) with
        | None => KBad
        | Some p => if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p
        end).
Proof. intros s used ch big E. unfold expect_key. rewrite E. reflexivity. Qed.

(** ** The name: strcmp against "phantom", "pad", "sens" *)
Lemma cstr_id : forall l, ~ In NUL l -> cstr l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. unfold cstr. cbn [nul_idx].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
  - exfalso. apply H. left. apply bv_eq. rewrite E. reflexivity.
  - cbn [firstn]. f_equal. apply IH. intros Hn. apply H. right. exact Hn.
Qed.

Lemma no_nul_skipn : forall (l : list byte) n, ~ In NUL l -> ~ In NUL (skipn n l).
Proof. intros l n H Hin. apply H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact Hin. Qed.

Lemma no_nul_nth : forall (l : list byte) i, ~ In NUL l -> (i < length l)%nat -> bv_unsigned (nth i l NUL) <> 0.
Proof.
  intros l i H Hi E. apply H. replace NUL with (nth i l NUL) by (apply bv_eq; rewrite E; reflexivity).
  apply nth_In. exact Hi.
Qed.

Lemma names_no_nul : ~ In NUL NAME_PHANTOM /\ ~ In NUL NAME_PAD /\ ~ In NUL NAME_SENS.
Proof.
  assert (G : forall l, forallb (fun b : byte => negb (bv_unsigned b =? 0)) l = true -> ~ In NUL l).
  { intros l F Hin. rewrite forallb_forall in F. specialize (F _ Hin). vm_compute in F. discriminate F. }
  split; [|split]; apply G; vm_compute; reflexivity.
Qed.

Lemma bytes_eqb_neq : forall a b, a <> b -> bytes_eqb a b = false.
Proof. intros a b H. destruct (bytes_eqb a b) eqn:E; [apply bytes_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma param_phantom : forall n, n = NAME_PHANTOM -> param_of_name n = Some HA_PHANTOM.
Proof. intros n ->. vm_compute. reflexivity. Qed.

Lemma param_pad : forall n, n <> NAME_PHANTOM -> n = NAME_PAD -> param_of_name n = Some HA_PAD.
Proof. intros n _ ->. vm_compute. reflexivity. Qed.

Lemma param_sens : forall n, n <> NAME_PHANTOM -> n <> NAME_PAD -> n = NAME_SENS -> param_of_name n = Some HA_SENS.
Proof. intros n _ _ ->. vm_compute. reflexivity. Qed.

Lemma param_none : forall n, n <> NAME_PHANTOM -> n <> NAME_PAD -> n <> NAME_SENS -> param_of_name n = None.
Proof. intros n H1 H2 H3. unfold param_of_name. rewrite !bytes_eqb_neq by assumption. reflexivity. Qed.

Lemma ha_prefix_len : forall k, ha_prefix k = true -> (13 <= length k)%nat.
Proof.
  intros k H. unfold ha_prefix in H. apply bytes_eqb_eq in H.
  assert (L : length (firstn (length HA_PREFIX) k) = length HA_PREFIX) by (rewrite H; reflexivity).
  rewrite length_firstn in L. change (length HA_PREFIX) with 13%nat in L. lia.
Qed.

(** ** expect_cell and cell_value *)
(** The value's bound for param p (fuzz_headamp.c:141: HA_SENS_MAX for sens, 1 for phantom / pad). *)
Definition ktop (p : Z) : Z := if p =? HA_SENS then HA_SENS_MAX else 1.

Lemma ktop_range : forall p, 1 <= ktop p <= 0x37.
Proof. intros p. unfold ktop, HA_SENS_MAX. destruct (p =? HA_SENS); lia. Qed.

Lemma expect_cell_key : forall k e, expect_cell k e =
  match expect_key (skipn 13 k) with
  | KBad => inl REFUSE_BAD_KEY
  | KRange => inl REFUSE_OUT_OF_RANGE
  | KCell ch p =>
      if (cell_value e <? 0) || (ktop p <? cell_value e) then inl REFUSE_OUT_OF_RANGE else inr (ch, p, cell_value e)
  end.
Proof. reflexivity. Qed.

Lemma cv_float : forall e, e_type e = POD_FLOAT -> 4 <= e_size e ->
  cell_value e = match nearest (rd32 (e_body e)) 0 255 with Some n => n | None => -1 end.
Proof.
  intros e Ht Hs. unfold cell_value, bool_of, int_of, float_of. rewrite Ht. rewrite (proj2 (Z.leb_le 4 _) Hs).
  reflexivity.
Qed.

Lemma cv_int : forall e, e_type e = POD_INT -> 4 <= e_size e ->
  cell_value e =
  (if (0 <=? s32 (rd32 (e_body e))) && (s32 (rd32 (e_body e)) <=? 255) then s32 (rd32 (e_body e)) else -1).
Proof.
  intros e Ht Hs. unfold cell_value, bool_of, int_of, float_of. rewrite Ht. rewrite (proj2 (Z.leb_le 4 _) Hs).
  reflexivity.
Qed.

Lemma cv_bool : forall e, e_type e = POD_BOOL -> 4 <= e_size e ->
  cell_value e = (if negb (rd32 (e_body e) =? 0) then 1 else 0).
Proof.
  intros e Ht Hs. unfold cell_value, bool_of, int_of, float_of. rewrite Ht. rewrite (proj2 (Z.leb_le 4 _) Hs).
  cbn [Z.eqb andb]. destruct (negb (rd32 (e_body e) =? 0)); reflexivity.
Qed.

Lemma cv_small : forall e, e_size e < 4 -> cell_value e = -1.
Proof.
  intros e Hs. unfold cell_value, bool_of, int_of, float_of. rewrite (proj2 (Z.leb_gt 4 _) Hs).
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma cv_other : forall e, e_type e <> POD_BOOL -> e_type e <> POD_INT -> e_type e <> POD_FLOAT -> cell_value e = -1.
Proof.
  intros e H1 H2 H3. unfold cell_value, bool_of, int_of, float_of.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3). reflexivity.
Qed.
