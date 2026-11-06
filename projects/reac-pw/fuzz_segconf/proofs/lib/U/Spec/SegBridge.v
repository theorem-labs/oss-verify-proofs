(** * SegBridge: from each libc leaf contract's Gallina value to the spine's name (lib/Spec/SegModel.v).

    Proves no function (kind: bridge lemmas between two Gallina definitions; no machine walk). The reader's and the
    harness model's contracts (lib/Prog/*_c.v,
    lib/U/Prog/*_c.v) state their answers in SegModel's terms; the libc leaf contracts state theirs in their donors'
    terms. A walk that calls a leaf cites the lemma below to turn the one into the other.

    Two builds, two copies: lib/Spec/SegBridge.v requires the plain build's donors (lib/Spec/StrFun.v, StrFun2.v,
    StrStr.v, CType.v, lib/Prog/*_c.v); lib/U/Spec/SegBridge.v is the same text with the UBSan build's donors
    (lib/U/Spec/*, lib/U/Prog/*_c.v): the two files differ only in their Require lines. SegModel.v, Prog/pin_spec.v
    and Prog/seg_spec.v are shared. A donor's bytes are read as the spine's values through seg_spec.zs
    (= map bv_unsigned).

    Donors (the definitions are the same text in both builds):
    - strlen_c.v (post: length str), strcmp_c.v (r = 0 <-> sx = sy), StrFun.find_byte / memchr_res / memchr_ok
      (memchr_c.v), StrFun.strncmp_model (strncmp_c.v), StrFun.memcmp_model (bcmp_c.v): the frame leaves of the base.
    - __intscan_c.s10_val / s10_errno (strtol_c.v, strtol_null_c.v: their post is [s10_val str] for the bytes str
      before the NUL), strspn_c.spn_len.
    - strrchr_c.strrchr_res (memrchr_c.rfind_byte).
    - strchr_c.strchr_val (StrFun2.strchr_res), StrStr.strstr_val (strstr_c.v), strncasecmp_c.ncase_eq,
      tolower_c.zlower, isalnum_c.alnum_b.
    - pin_spec.row_ptr (fuzz_catalogue_row_c.v, reac_box_catalogue_by_token_c.v).

    The lemmas, each for the shapes the contracts supply (the hypotheses):
    1. bridge_strlen, bridge_strlen_nul: SegModel.strlen of a NUL-free string (and of it with its NUL and slack).
    2. bridge_strcmp: SegModel.strcmp = 0 <-> equal strings.
    3. bridge_memchr, bridge_memchr_res, bridge_memchr_ok: StrFun.find_byte is SegModel.memchr; memchr's premise.
    4. bridge_strchr: strchr_val is A + SegModel.strchr's index, else 0.
    5. bridge_strrchr: strrchr_res is A + SegModel.strrchr's index, else 0.
    6. bridge_strspn: spn_len with the set " \t\r" is SegModel.strspn_blank.
    7. bridge_strtol10 (on str ++ NUL), bridge_strtol10_str (the contracts' form, s10_val str),
       bridge_strtol10_errno (strtol keeps the errno cell): on 1..18 decimal digits.
    8. bridge_tolower: zlower is SegModel.tolower on a byte.
    9. bridge_strncasecmp: ncase_eq <-> SegModel.strncasecmp = 0.
    10. bridge_isalnum: alnum_b is SegModel.isalnum on a byte.
    11. bridge_strstr (0 < A: strstr_val <> 0 <-> SegModel.strstr_found), bridge_strstr_val (the value is A + the first
        index where the needle starts).
    12. bridge_strncmp_val, bridge_strncmp (strncmp_model = Some v: v is SegModel.strncmp, so v = 0 <-> it is 0),
        bridge_strncmp_some and strncmp_model_cstr (on two C strings strncmp_model IS Some of SegModel.strncmp: the
        existence strncmp_contract's premise needs; strncmp_model_cstr is the form check_address.v uses).
    13. bridge_memcmp, bridge_memcmp_total, bridge_memcmp_leqb (equal-length buffers: v = 0 <-> equal, the value
        exists, and v =? 0 is SegModel.leqb); bridge_lit_prefix, bridge_memcmp_lit, bridge_memcmp_lit_total
        (bcmp(low, lit, |lit| + 1) = 0 iff strcmp = 0 when low holds a C string,
        whatever bytes follow its NUL).
    14. bridge_cat_row (row_ptr = cat_ptr of SegModel.cat_row), bridge_by_token (the by_token case: a NUL-free
        token), bridge_row_tok (row i's own token names row i). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun StrFun2 StrStr CType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import
  memrchr_c strchr_c strrchr_c strspn_c __intscan_c tolower_c strncasecmp_c isalnum_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Bytes as values *)

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma nul_val : bv_unsigned (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

(** A byte list with no NUL byte has values with no 0, and back. *)
Lemma zs_nulfree : forall l : list byte, ~ In (Z_to_bv 8 0) l -> nulfree (zs l).
Proof.
  intros l H Hin. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hinb).
  apply H. replace (Z_to_bv 8 0) with b; [exact Hinb|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma nul_free_bytes : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof. intros bs H Hin. apply H. unfold zs. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

Lemma zs_inj : forall a b : list byte, zs a = zs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold zs in H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma zs_app_nul : forall a b : list byte, zs (a ++ Z_to_bv 8 0 :: b) = zs a ++ 0 :: zs b.
Proof. intros a b. unfold zs. rewrite map_app. reflexivity. Qed.

Lemma cut_nul_app0 : forall l r, nulfree l -> cut_nul (l ++ 0 :: r) = l.
Proof.
  induction l as [|a l IH]; intros r H; cbn; [reflexivity|].
  apply nulfree_cons in H as [Ha Hl]. destruct (Z.eqb_spec a 0) as [E|E]; [contradiction|].
  rewrite IH by exact Hl. reflexivity.
Qed.

(** ** 1. strlen *)

Lemma bridge_strlen : forall str : list byte, ~ In (Z_to_bv 8 0) str -> SegModel.strlen (zs str) = length str.
Proof.
  intros str H. rewrite SegModel.strlen_id by (apply zs_nulfree; exact H). unfold zs. apply length_map.
Qed.

Lemma bridge_strlen_nul : forall str slack : list byte, ~ In (Z_to_bv 8 0) str ->
  SegModel.strlen (zs (str ++ Z_to_bv 8 0 :: slack)) = length str.
Proof.
  intros str slack H. unfold SegModel.strlen. rewrite zs_app_nul, cut_nul_app0 by (apply zs_nulfree; exact H).
  unfold zs. apply length_map.
Qed.

(** ** 2. strcmp *)

Lemma bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  (SegModel.strcmp (zs sx) (zs sy) = 0 <-> sx = sy).
Proof.
  intros sx sy Hx Hy. split.
  - intros H. apply zs_inj. apply SegModel.leqb_eq.
    rewrite <- SegModel.strcmp_eq by (apply zs_nulfree; assumption). apply Z.eqb_eq. exact H.
  - intros ->. apply SegModel.strcmp_refl.
Qed.

(** ** 3. memchr *)

Lemma bridge_memchr : forall c (l : list byte), StrFun.find_byte c l = SegModel.memchr (zs l) c.
Proof.
  intros c l. unfold zs. induction l as [|b l IH]; cbn [StrFun.find_byte SegModel.memchr map]; [reflexivity|].
  rewrite <- IH. destruct (bv_unsigned b =? c); [reflexivity|]. destruct (StrFun.find_byte c l); reflexivity.
Qed.

Lemma bridge_memchr_res : forall A c n (buf : list byte),
  StrFun.memchr_res A c n buf =
  match SegModel.memchr (zs (firstn (Z.to_nat n) buf)) c with Some i => A + Z.of_nat i | None => 0 end.
Proof. intros A c n buf. unfold StrFun.memchr_res. rewrite bridge_memchr. reflexivity. Qed.

(** memchr_contract's premise holds whenever the count lies within the buffer. *)
Lemma bridge_memchr_ok : forall A c n (buf : list byte), n <= Z.of_nat (length buf) -> StrFun.memchr_ok A c n buf.
Proof.
  intros A c n buf H. unfold StrFun.memchr_ok.
  destruct (StrFun.find_byte c (firstn (Z.to_nat n) buf)); [left|]; exact H.
Qed.

(** ** 4. strchr *)

Lemma bridge_strchr : forall A c (str : list byte), ~ In (Z_to_bv 8 0) str -> 0 < c < 256 ->
  strchr_c.strchr_val A c str =
  match SegModel.strchr (zs str) c with Some i => A + Z.of_nat i | None => 0 end.
Proof.
  intros A c str H Hc. unfold strchr_c.strchr_val. destruct (Z.eqb_spec c 0) as [E|_]; [lia|].
  unfold StrFun2.strchr_res. rewrite bridge_memchr.
  rewrite SegModel.strchr_memchr; [reflexivity | apply zs_nulfree; exact H | lia].
Qed.

(** ** 5. strrchr *)

Lemma last_idx_rfind : forall c (l : list byte) i acc,
  SegModel.last_idx c (zs l) i acc = match rfind_byte c l with Some j => Some (i + j)%nat | None => acc end.
Proof.
  intros c l. unfold zs. induction l as [|b l IH]; intros i acc; cbn [map SegModel.last_idx rfind_byte];
    [reflexivity|].
  rewrite IH. destruct (rfind_byte c l) as [j|]; cbn.
  - f_equal; lia.
  - destruct (bv_unsigned b =? c); cbn; [f_equal; lia | reflexivity].
Qed.

Lemma bridge_strrchr : forall A c (str : list byte), ~ In (Z_to_bv 8 0) str -> 0 < c < 256 ->
  strrchr_c.strrchr_res A c str =
  match SegModel.strrchr (zs str) c with Some i => A + Z.of_nat i | None => 0 end.
Proof.
  intros A c str H Hc. rewrite strrchr_c.strrchr_res_nonnul by lia.
  unfold SegModel.strrchr. rewrite SegModel.cut_nul_id by (apply zs_nulfree; exact H).
  rewrite last_idx_rfind. destruct (rfind_byte c str); reflexivity.
Qed.

(** ** 6. strspn with the set " \t\r" *)

Lemma in_set_blank : forall set x, zs set = [32; 9; 13] -> strspn_c.in_set set x = SegModel.blank (bv_unsigned x).
Proof.
  intros set x Hs. unfold strspn_c.in_set. unfold zs in Hs.
  destruct set as [|y1 [|y2 [|y3 [|y4 set]]]]; cbn in Hs; try discriminate.
  injection Hs as H1 H2 H3. cbn [existsb]. rewrite H1, H2, H3. unfold SegModel.blank.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), (Z.eqb_sym 13).
  destruct (bv_unsigned x =? 32), (bv_unsigned x =? 9), (bv_unsigned x =? 13); reflexivity.
Qed.

Lemma spn_len_blank : forall set (str : list byte), zs set = [32; 9; 13] ->
  strspn_c.spn_len set str = length (SegModel.takewhile SegModel.blank (zs str)).
Proof.
  intros set str Hs. unfold zs. induction str as [|x str IH]; [reflexivity|].
  cbn [strspn_c.spn_len map SegModel.takewhile]. rewrite in_set_blank by exact Hs.
  destruct (SegModel.blank (bv_unsigned x)); cbn [length]; [rewrite IH; reflexivity | reflexivity].
Qed.

Lemma bridge_strspn : forall set (str : list byte), ~ In (Z_to_bv 8 0) str -> zs set = [32; 9; 13] ->
  Z.of_nat (strspn_c.spn_len set str) = Z.of_nat (SegModel.strspn_blank (zs str)).
Proof.
  intros set str H Hs. f_equal. unfold SegModel.strspn_blank.
  rewrite SegModel.cut_nul_id by (apply zs_nulfree; exact H). apply spn_len_blank. exact Hs.
Qed.

(** ** 7. strtol(s, NULL, 10) on decimal digits *)

(** The byte after the digits (if any) is not a digit: the NUL, or nothing. *)
Definition no_digit_head (rest : list byte) : Prop :=
  match rest with [] => True | b :: _ => c_digit b = false end.

Lemma dval_digits : forall (l rest : list byte) acc, forallb SegModel.isdigit (zs l) = true -> no_digit_head rest ->
  __intscan_c.dval acc (l ++ rest) = fold_left SegModel.dstep (zs l) acc.
Proof.
  unfold zs. induction l as [|b l IH]; intros rest acc H Hr.
  - destruct rest as [|b rest]; cbn [app __intscan_c.dval]; [reflexivity|].
    cbn [no_digit_head] in Hr. rewrite Hr. reflexivity.
  - cbn [map forallb] in H. apply andb_true_iff in H as [Hb Hl].
    cbn [app __intscan_c.dval map fold_left]. unfold c_digit. unfold SegModel.isdigit in Hb. rewrite Hb.
    rewrite IH by assumption. f_equal. unfold SegModel.dstep. lia.
Qed.

Lemma ndig_digits : forall (l rest : list byte), forallb SegModel.isdigit (zs l) = true -> no_digit_head rest ->
  __intscan_c.ndig (l ++ rest) = length l.
Proof.
  unfold zs. induction l as [|b l IH]; intros rest H Hr.
  - destruct rest as [|b rest]; cbn [app __intscan_c.ndig length]; [reflexivity|].
    cbn [no_digit_head] in Hr. rewrite Hr. reflexivity.
  - cbn [map forallb] in H. apply andb_true_iff in H as [Hb Hl].
    cbn [app __intscan_c.ndig length]. unfold c_digit. unfold SegModel.isdigit in Hb. rewrite Hb.
    rewrite IH by assumption. reflexivity.
Qed.

Lemma s10_head : forall (d : byte) (r rest : list byte), 48 <= bv_unsigned d <= 57 ->
  skip_space ((d :: r) ++ rest) = (d :: r) ++ rest /\
  __intscan_c.sign_split ((d :: r) ++ rest) = (false, (d :: r) ++ rest).
Proof.
  intros d r rest Hd. split.
  - cbn [app skip_space]. unfold c_space.
    destruct (Z.eqb_spec (bv_unsigned d) 32); [lia|].
    destruct (Z.leb_spec 9 (bv_unsigned d)); [|lia].
    destruct (Z.leb_spec (bv_unsigned d) 13); [lia|]. reflexivity.
  - cbn [app __intscan_c.sign_split].
    destruct (Z.eqb_spec (bv_unsigned d) 45); [lia|]. destruct (Z.eqb_spec (bv_unsigned d) 43); [lia|].
    reflexivity.
Qed.

Lemma s10_digits : forall (str rest : list byte), str <> [] -> forallb SegModel.isdigit (zs str) = true ->
  no_digit_head rest ->
  __intscan_c.s10_signed (str ++ rest) = SegModel.strtol10 (zs str) /\
  __intscan_c.s10_nd (str ++ rest) = length str.
Proof.
  intros str rest Hne Hd Hr. destruct str as [|d r]; [exfalso; apply Hne; reflexivity|].
  assert (Hd0 : 48 <= bv_unsigned d <= 57).
  { apply SegModel.isdigit_range. unfold zs in Hd. cbn [map forallb] in Hd.
    apply andb_true_iff in Hd as [H _]. exact H. }
  destruct (s10_head d r rest Hd0) as [Hsk Hsg].
  unfold __intscan_c.s10_signed, __intscan_c.s10_nd, __intscan_c.s10_neg, __intscan_c.s10_mag,
    __intscan_c.s10_rest.
  rewrite Hsk, Hsg. cbn [fst snd]. split.
  - rewrite dval_digits by assumption. reflexivity.
  - apply ndig_digits; assumption.
Qed.

Lemma fold_dstep_lt : forall l acc, 0 <= acc -> forallb SegModel.isdigit l = true ->
  0 <= fold_left SegModel.dstep l acc < (acc + 1) * 10 ^ Z.of_nat (length l).
Proof.
  induction l as [|d l IH]; intros acc Hacc H.
  - cbn [fold_left length Z.of_nat]. rewrite Z.pow_0_r. lia.
  - cbn [forallb] in H. apply andb_true_iff in H as [Hd Hl]. apply SegModel.isdigit_range in Hd.
    cbn [fold_left length].
    assert (Hs : 0 <= SegModel.dstep acc d) by (unfold SegModel.dstep; lia).
    destruct (IH (SegModel.dstep acc d) Hs Hl) as [IH1 IH2].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (HP : 0 < 10 ^ Z.of_nat (length l)) by (apply Z.pow_pos_nonneg; lia).
    set (P := 10 ^ Z.of_nat (length l)) in *.
    assert (Hm : (SegModel.dstep acc d + 1) * P <= (acc + 1) * (10 * P)).
    { replace ((acc + 1) * (10 * P)) with (((acc + 1) * 10) * P) by ring.
      apply Z.mul_le_mono_nonneg_r; [lia|]. unfold SegModel.dstep. lia. }
    split; [exact IH1 | lia].
Qed.

Lemma strtol10_bound : forall str : list byte, forallb SegModel.isdigit (zs str) = true -> (length str <= 18)%nat ->
  0 <= SegModel.strtol10 (zs str) < 1000000000000000000.
Proof.
  intros str Hd Hl. rewrite SegModel.strtol10_fold.
  destruct (fold_dstep_lt (zs str) 0 ltac:(lia) Hd) as [H0 H1].
  assert (Hlen : Z.of_nat (length (zs str)) <= 18) by (unfold zs; rewrite length_map; lia).
  assert (Hp : 10 ^ Z.of_nat (length (zs str)) <= 10 ^ 18) by (apply Z.pow_le_mono_r; lia).
  change (10 ^ 18) with 1000000000000000000 in Hp. lia.
Qed.

(** The form on the digits and their NUL: s10_val of them. *)
Lemma bridge_strtol10 : forall str : list byte, str <> [] -> forallb SegModel.isdigit (zs str) = true ->
  (length str <= 18)%nat -> __intscan_c.s10_val (str ++ [Z_to_bv 8 0]) = SegModel.strtol10 (zs str).
Proof.
  intros str Hne Hd Hl. destruct (s10_digits str [Z_to_bv 8 0] Hne Hd eq_refl) as [Hs _].
  pose proof (strtol10_bound str Hd Hl). unfold __intscan_c.s10_val. rewrite Hs. unfold __intscan_c.LMIN. lia.
Qed.

(** The contracts' form (strtol_c.v, strtol_null_c.v: [s10_val str], str the bytes before the NUL). *)
Lemma bridge_strtol10_str : forall str : list byte, str <> [] -> forallb SegModel.isdigit (zs str) = true ->
  (length str <= 18)%nat -> __intscan_c.s10_val str = SegModel.strtol10 (zs str).
Proof.
  intros str Hne Hd Hl. destruct (s10_digits str [] Hne Hd I) as [Hs _]. rewrite app_nil_r in Hs.
  pose proof (strtol10_bound str Hd Hl). unfold __intscan_c.s10_val. rewrite Hs. unfold __intscan_c.LMIN. lia.
Qed.

(** On such a string strtol leaves the errno cell as it was. *)
Lemma bridge_strtol10_errno : forall (str : list byte) ev, str <> [] -> forallb SegModel.isdigit (zs str) = true ->
  (length str <= 18)%nat -> __intscan_c.s10_errno str ev = ev.
Proof.
  intros str ev Hne Hd Hl. destruct (s10_digits str [] Hne Hd I) as [Hs Hn]. rewrite app_nil_r in Hs, Hn.
  pose proof (strtol10_bound str Hd Hl) as Hb.
  unfold __intscan_c.s10_errno, __intscan_c.s10_inrange. rewrite Hn, Hs.
  destruct str as [|d r]; [exfalso; apply Hne; reflexivity|]. cbn [length Nat.eqb].
  assert (E1 : (- __intscan_c.LMIN <=? SegModel.strtol10 (zs (d :: r))) = true)
    by (apply Z.leb_le; unfold __intscan_c.LMIN; lia).
  assert (E2 : (SegModel.strtol10 (zs (d :: r)) <=? __intscan_c.LMIN - 1) = true)
    by (apply Z.leb_le; unfold __intscan_c.LMIN; lia).
  rewrite E1, E2. reflexivity.
Qed.

(** ** 8. tolower *)

Lemma bridge_tolower : forall c, 0 <= c < 256 -> tolower_c.zlower c = SegModel.tolower c.
Proof.
  intros c Hc.
  assert (H : forallb (fun z => Z.eqb (tolower_c.zlower z) (SegModel.tolower z)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

(** ** 9. strncasecmp *)

Definition byte_vals (L : list Z) : Prop := forall x, In x L -> 0 < x < 256.

Lemma byte_vals_zs : forall l : list byte, ~ In (Z_to_bv 8 0) l -> byte_vals (zs l).
Proof.
  intros l H x Hx. pose proof (zs_nulfree l H) as Hn. unfold zs in Hx.
  apply in_map_iff in Hx as (b & <- & Hb). pose proof (byte_range b). split; [|lia].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia]. exfalso. apply Hn. unfold zs.
  apply in_map_iff. exists b. split; assumption.
Qed.

Lemma zlower_pos : forall x, 0 < x -> 0 < tolower_c.zlower x.
Proof. intros x H. unfold tolower_c.zlower. destruct ((65 <=? x) && (x <=? 90)); lia. Qed.

Lemma zlower_0 : tolower_c.zlower 0 = 0.
Proof. reflexivity. Qed.

Lemma tolower_0 : SegModel.tolower 0 = 0.
Proof. reflexivity. Qed.

Lemma ncase_go : forall n L R, byte_vals L -> byte_vals R ->
  (SegModel.strncasecmp_go L R n = 0 <->
   map tolower_c.zlower (firstn (S n) (L ++ [0])) = map tolower_c.zlower (firstn (S n) (R ++ [0]))).
Proof.
  induction n as [|n IH]; intros L R HL HR;
    destruct L as [|a L], R as [|b R]; cbn [SegModel.strncasecmp_go SegModel.hd0 app firstn map].
  - rewrite tolower_0. split; intros _; reflexivity.
  - assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    rewrite tolower_0, zlower_0, <- (bridge_tolower b) by lia. pose proof (zlower_pos b ltac:(lia)) as Pb.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    rewrite tolower_0, zlower_0, <- (bridge_tolower a) by lia. pose proof (zlower_pos a ltac:(lia)) as Pa.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    rewrite <- (bridge_tolower a), <- (bridge_tolower b) by lia.
    split; intros H; [f_equal; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - rewrite tolower_0. split; intros _; reflexivity.
  - assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    rewrite tolower_0, zlower_0, <- (bridge_tolower b) by lia. pose proof (zlower_pos b ltac:(lia)) as Pb.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    rewrite tolower_0, zlower_0, <- (bridge_tolower a) by lia. pose proof (zlower_pos a ltac:(lia)) as Pa.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - assert (Ha : 0 < a < 256) by (apply HL; left; reflexivity).
    assert (Hb : 0 < b < 256) by (apply HR; left; reflexivity).
    assert (HL' : byte_vals L) by (intros x Hx; apply HL; right; exact Hx).
    assert (HR' : byte_vals R) by (intros x Hx; apply HR; right; exact Hx).
    destruct (Z.eqb_spec a 0) as [E0|_]; [lia|]. destruct (Z.eqb_spec b 0) as [E0|_]; [lia|].
    rewrite <- (bridge_tolower a), <- (bridge_tolower b) by lia. cbn [negb andb].
    destruct (Z.eqb_spec (tolower_c.zlower a) (tolower_c.zlower b)) as [E|E].
    + destruct (a =? b); cbn [orb];
        (rewrite (IH L R HL' HR'), E;
         split; [intros H; rewrite H; reflexivity | intros H; apply (f_equal (@tl Z)) in H; exact H]).
    + assert (Eab : (a =? b) = false) by (apply Z.eqb_neq; intros ->; apply E; reflexivity).
      rewrite Eab. cbn [orb].
      split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; exfalso; exact (E H)].
Qed.

Lemma bridge_strncasecmp : forall (ls rs : list byte) n, ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs ->
  (strncasecmp_c.ncase_eq ls rs n <-> SegModel.strncasecmp (zs ls) (zs rs) (Z.to_nat n) = 0).
Proof.
  intros ls rs n Hl Hr. unfold strncasecmp_c.ncase_eq.
  destruct (Z.to_nat n) as [|k].
  - cbn [firstn map SegModel.strncasecmp]. split; intros _; reflexivity.
  - change (SegModel.strncasecmp (zs ls) (zs rs) (S k)) with (SegModel.strncasecmp_go (zs ls) (zs rs) k).
    rewrite ncase_go by (apply byte_vals_zs; assumption). reflexivity.
Qed.

(** ** 10. isalnum *)

Lemma bridge_isalnum : forall c, 0 <= c < 256 -> isalnum_c.alnum_b c = SegModel.isalnum c.
Proof.
  intros c Hc.
  assert (H : forallb (fun z => Bool.eqb (isalnum_c.alnum_b z) (SegModel.isalnum z)) (map Z.of_nat (seq 0 256))
              = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

(** ** 11. strstr *)

Lemma prefix_eqb_prefixb : forall nd h, StrStr.prefix_eqb nd h = SegModel.prefixb nd h.
Proof. induction nd as [|a nd IH]; intros [|b h]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

Lemma find_first_some : forall h nd, StrStr.find_first h nd <> None <-> SegModel.infixb nd h = true.
Proof.
  induction h as [|b h IH]; intros nd; cbn [StrStr.find_first SegModel.infixb]; rewrite prefix_eqb_prefixb.
  - destruct (SegModel.prefixb nd []); cbn [orb]; split; intros H; congruence.
  - destruct (SegModel.prefixb nd (b :: h)); cbn [orb]; [split; intros H; congruence|].
    rewrite <- IH. destruct (StrStr.find_first h nd); cbn [option_map]; split; intros H; congruence.
Qed.

Lemma find_first_spec : forall h nd i, StrStr.find_first h nd = Some i ->
  SegModel.prefixb nd (skipn i h) = true /\ (forall j, (j < i)%nat -> SegModel.prefixb nd (skipn j h) = false).
Proof.
  induction h as [|b h IH]; intros nd i H; cbn [StrStr.find_first] in H; rewrite prefix_eqb_prefixb in H; revert H.
  - destruct (SegModel.prefixb nd []) eqn:E; intros H; cbn in H; [|discriminate]. injection H as <-.
    split; [exact E | intros j Hj; lia].
  - destruct (SegModel.prefixb nd (b :: h)) eqn:E; intros H; cbn in H.
    + injection H as <-. split; [exact E | intros j Hj; lia].
    + revert H. destruct (StrStr.find_first h nd) as [i'|] eqn:F; intros H; cbn in H; [|discriminate].
      injection H as <-. destruct (IH nd i' F) as [H1 H2]. cbn [skipn]. split; [exact H1|].
      intros [|j] Hj; cbn [skipn]; [exact E | apply H2; lia].
Qed.

(** strstr's answer is nonzero exactly when the needle occurs (0 < A: strstr_contract's [bv_unsigned a0 <> 0]; with
    A = 0 a match at index 0 would read as NULL). *)
Lemma bridge_strstr : forall A (hb nb : list byte), 0 < A -> ~ In (Z_to_bv 8 0) hb -> ~ In (Z_to_bv 8 0) nb ->
  (StrStr.strstr_val A hb nb <> 0 <-> SegModel.strstr_found (zs hb) (zs nb) = true).
Proof.
  intros A hb nb HA Hh Hn. unfold SegModel.strstr_found.
  rewrite SegModel.cut_nul_id by (apply zs_nulfree; exact Hh).
  rewrite <- find_first_some. unfold StrStr.strstr_val.
  change (map bv_unsigned hb) with (zs hb). change (map bv_unsigned nb) with (zs nb).
  destruct (StrStr.find_first (zs hb) (zs nb)); split; intros H; [congruence | lia | congruence | congruence].
Qed.

(** And the value: A + the first index where the needle starts. *)
Lemma bridge_strstr_val : forall A (hb nb : list byte), ~ In (Z_to_bv 8 0) hb ->
  SegModel.strstr_found (zs hb) (zs nb) = true ->
  exists i, StrStr.strstr_val A hb nb = A + Z.of_nat i /\
    SegModel.prefixb (zs nb) (skipn i (zs hb)) = true /\
    (forall j, (j < i)%nat -> SegModel.prefixb (zs nb) (skipn j (zs hb)) = false).
Proof.
  intros A hb nb Hh Hf. unfold SegModel.strstr_found in Hf.
  rewrite SegModel.cut_nul_id in Hf by (apply zs_nulfree; exact Hh).
  apply find_first_some in Hf. unfold StrStr.strstr_val.
  change (map bv_unsigned hb) with (zs hb). change (map bv_unsigned nb) with (zs nb).
  destruct (StrStr.find_first (zs hb) (zs nb)) as [i|] eqn:F; [|congruence].
  exists i. split; [reflexivity|]. apply find_first_spec. exact F.
Qed.

(** ** 12. strncmp *)

Lemma strncmp_walk_go : forall (l r : list byte) k v, StrFun.strncmp_walk l r k = Some v ->
  v = SegModel.strncmp_go (zs l) (zs r) k.
Proof.
  unfold zs. induction l as [|a l IH]; intros r k v H; [cbn in H; discriminate|].
  destruct r as [|b r]; [cbn in H; discriminate|].
  revert H. cbn [StrFun.strncmp_walk map].
  destruct k as [|k]; cbn [SegModel.strncmp_go SegModel.hd0 Nat.eqb];
    destruct (bv_unsigned a =? 0), (bv_unsigned b =? 0), (bv_unsigned a =? bv_unsigned b);
    cbn [orb andb negb]; intros H; first [injection H as <-; reflexivity | apply IH; exact H].
Qed.

(** Whatever v strncmp_model gives is SegModel.strncmp (n is a count: n = bv_unsigned a2, so 0 <= n). *)
Lemma bridge_strncmp_val : forall (l r : list byte) n v, 0 <= n -> StrFun.strncmp_model l r n = Some v ->
  v = SegModel.strncmp (zs l) (zs r) (Z.to_nat n).
Proof.
  intros l r n v Hn H. unfold StrFun.strncmp_model in H. revert H.
  destruct (Z.eqb_spec n 0) as [->|Hn0]; intros H.
  - cbn in H. injection H as <-. reflexivity.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
    change (SegModel.strncmp (zs l) (zs r) (S (Z.to_nat (n - 1))))
      with (SegModel.strncmp_go (zs l) (zs r) (Z.to_nat (n - 1))).
    apply strncmp_walk_go. exact H.
Qed.

Lemma bridge_strncmp : forall (l r : list byte) n v, 0 <= n -> StrFun.strncmp_model l r n = Some v ->
  (v = 0 <-> SegModel.strncmp (zs l) (zs r) (Z.to_nat n) = 0).
Proof. intros l r n v Hn H. rewrite (bridge_strncmp_val l r n v Hn H). reflexivity. Qed.

(** On two C strings (the first with its NUL, the second with its NUL and any slack) the walk never runs off a list:
    each NUL stops it (check_address.v). *)
Lemma walk_bridge : forall (bg bw sl : list byte) (k : nat),
  ~ In 0 (zs bg) -> ~ In 0 (zs bw) ->
  StrFun.strncmp_walk (bg ++ [ZERO]) (bw ++ ZERO :: sl) k = Some (SegModel.strncmp_go (zs bg) (zs bw) k).
Proof.
  unfold zs.
  induction bg as [|x bg IH]; intros bw sl k NG NW.
  - destruct bw as [|y bw]; destruct k; reflexivity.
  - cbn [map In] in NG. assert (Hx : bv_unsigned x <> 0) by tauto.
    assert (NG' : ~ In 0 (map bv_unsigned bg)) by tauto.
    destruct bw as [|y bw].
    + cbn [app map StrFun.strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Hx). destruct k; reflexivity.
    + cbn [map In] in NW. assert (Hy : bv_unsigned y <> 0) by tauto.
      assert (NW' : ~ In 0 (map bv_unsigned bw)) by tauto.
      destruct k as [|k].
      * cbn [app map StrFun.strncmp_walk SegModel.strncmp_go SegModel.hd0].
        rewrite (proj2 (Z.eqb_neq _ _) Hx), (proj2 (Z.eqb_neq _ _) Hy). reflexivity.
      * cbn [app map StrFun.strncmp_walk SegModel.strncmp_go].
        rewrite !(proj2 (Z.eqb_neq _ _) Hx), !(proj2 (Z.eqb_neq _ _) Hy).
        destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E]; cbn [negb orb andb Nat.eqb].
        -- apply IH; assumption.
        -- reflexivity.
Qed.

(** The existence strncmp_contract's premise needs, for any count: strncmp_model IS Some of SegModel.strncmp. *)
Lemma bridge_strncmp_some : forall (bg bw sl : list byte) n, 0 <= n ->
  ~ In 0 (zs bg) -> ~ In 0 (zs bw) ->
  StrFun.strncmp_model (bg ++ [ZERO]) (bw ++ ZERO :: sl) n = Some (SegModel.strncmp (zs bg) (zs bw) (Z.to_nat n)).
Proof.
  intros bg bw sl n Hn NG NW. unfold StrFun.strncmp_model.
  destruct (Z.eqb_spec n 0) as [->|Hn0]; [reflexivity|].
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
  change (SegModel.strncmp (zs bg) (zs bw) (S (Z.to_nat (n - 1))))
    with (SegModel.strncmp_go (zs bg) (zs bw) (Z.to_nat (n - 1))).
  exact (walk_bridge bg bw sl (Z.to_nat (n - 1)) NG NW).
Qed.

(** The form check_address.v uses: n = the length of the second string. *)
Lemma strncmp_model_cstr : forall (bg bw sl : list byte),
  ~ In 0 (zs bg) -> ~ In 0 (zs bw) ->
  StrFun.strncmp_model (bg ++ [ZERO]) (bw ++ ZERO :: sl) (Z.of_nat (length bw)) =
  Some (SegModel.strncmp (zs bg) (zs bw) (length bw)).
Proof.
  intros bg bw sl NG NW. rewrite bridge_strncmp_some by (try lia; assumption). rewrite Nat2Z.id. reflexivity.
Qed.

(** ** 13. memcmp (bcmp) *)

Lemma bridge_memcmp : forall (ls rs : list byte) n v, length ls = n -> length rs = n ->
  StrFun.memcmp_model ls rs n = Some v -> (v = 0 <-> ls = rs).
Proof.
  intros ls rs n. revert ls rs. induction n as [|n IH]; intros ls rs v Hl Hr H.
  - destruct ls as [|a ls]; [|cbn in Hl; discriminate]. destruct rs as [|b rs]; [|cbn in Hr; discriminate].
    cbn in H. injection H as <-. split; intros _; reflexivity.
  - destruct ls as [|a ls]; [cbn in Hl; discriminate|]. destruct rs as [|b rs]; [cbn in Hr; discriminate|].
    cbn [length] in Hl, Hr. injection Hl as Hl. injection Hr as Hr.
    revert H. cbn [StrFun.memcmp_model].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E]; intros H.
    + assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
      rewrite (IH ls rs v Hl Hr H).
      split; [intros ->; reflexivity | intros Heq; apply (f_equal (@tl byte)) in Heq; exact Heq].
    + cbn in H. injection H as <-.
      split; [intros H0; exfalso; lia | intros Heq; injection Heq as Ea Er; subst; exfalso; apply E; reflexivity].
Qed.

(** The existence bcmp_contract's premise needs, on two buffers of the compared length. *)
Lemma bridge_memcmp_total : forall (ls rs : list byte) n, length ls = n -> length rs = n ->
  exists v, StrFun.memcmp_model ls rs n = Some v /\ (v = 0 <-> ls = rs).
Proof.
  intros ls rs n Hl Hr. destruct (StrFun.memcmp_model_total ls rs n ltac:(lia) ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv | exact (bridge_memcmp ls rs n v Hl Hr Hv)].
Qed.

(** The same zero test in the spine's terms (m_find_go's and row_go's [leqb]). *)
Lemma bridge_memcmp_leqb : forall (ls rs : list byte) n v, length ls = n -> length rs = n ->
  StrFun.memcmp_model ls rs n = Some v -> (v =? 0) = SegModel.leqb (zs ls) (zs rs).
Proof.
  intros ls rs n v Hl Hr H. pose proof (bridge_memcmp ls rs n v Hl Hr H) as E.
  destruct (Z.eqb_spec v 0) as [Hv|Hv]; destruct (SegModel.leqb (zs ls) (zs rs)) eqn:Q; try reflexivity.
  - exfalso. apply E in Hv. subst rs. rewrite SegModel.leqb_refl in Q. discriminate.
  - exfalso. apply Hv. apply E. apply zs_inj. apply SegModel.leqb_eq. exact Q.
Qed.

Lemma memcmp_some0_firstn : forall n (l r : list byte), StrFun.memcmp_model l r n = Some 0 ->
  firstn n l = firstn n r /\ (n <= length l)%nat.
Proof.
  induction n as [|n IH]; intros l r H; [split; [reflexivity | lia]|].
  destruct l as [|a l]; [cbn in H; discriminate|]. destruct r as [|b r]; [cbn in H; discriminate|].
  revert H. cbn [StrFun.memcmp_model].
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E]; intros H.
  - destruct (IH l r H) as [H1 H2]. assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
    cbn [firstn length]. rewrite H1. split; [reflexivity | lia].
  - cbn in H. injection H as H. lia.
Qed.

Lemma memcmp_model_refl : forall n (l : list byte), (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros l H; [reflexivity|].
  destruct l as [|a l]; [cbn in H; lia|]. cbn [StrFun.memcmp_model]. rewrite Z.eqb_refl.
  cbn in H. exact (IH l ltac:(lia)).
Qed.

Lemma firstn_S_nth_error : forall {A} (l : list A) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; intros k x H; [destruct k; discriminate|].
  destruct k as [|k]; cbn in H |- *.
  - injection H as ->. reflexivity.
  - rewrite (IH k x H). reflexivity.
Qed.

(** A buffer holding lit, its NUL and then anything: a C string at its start that ends at a NUL is lit. *)
Lemma first_nul_unique : forall (lit rest low : list byte) k,
  low = lit ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) lit ->
  ~ In (Z_to_bv 8 0) (firstn k low) -> nth_error low k = Some (Z_to_bv 8 0) -> firstn k low = lit.
Proof.
  intros lit rest low k -> Hlit Hlow Hk.
  destruct (Nat.lt_trichotomy k (length lit)) as [Hlt|[->|Hgt]].
  - exfalso. apply Hlit. rewrite nth_error_app1 in Hk by exact Hlt. eapply nth_error_In. exact Hk.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
  - exfalso. apply Hlow. rewrite firstn_app, firstn_all2 by lia.
    destruct (k - length lit)%nat as [|j] eqn:Ej; [lia|]. cbn [firstn]. apply in_or_app. right. left. reflexivity.
Qed.

(** O1, the word form: low's first |lit| + 1 bytes are lit and its NUL iff the C string at low is lit, for low whose
    first k bytes are a C string followed by its NUL (the bytes after that NUL unknown). *)
Lemma bridge_lit_prefix : forall (lit low : list byte) k,
  ~ In (Z_to_bv 8 0) lit -> ~ In (Z_to_bv 8 0) (firstn k low) -> nth_error low k = Some (Z_to_bv 8 0) ->
  (firstn (length lit + 1) low = lit ++ [Z_to_bv 8 0] <-> SegModel.strcmp (zs (firstn k low)) (zs lit) = 0).
Proof.
  intros lit low k Hlit Hlow Hk. rewrite bridge_strcmp by assumption. split.
  - intros H1. apply (first_nul_unique lit (skipn (length lit + 1) low) low k); [|exact Hlit|exact Hlow|exact Hk].
    transitivity (firstn (length lit + 1) low ++ skipn (length lit + 1) low); [symmetry; apply firstn_skipn|].
    rewrite H1, <- app_assoc. reflexivity.
  - intros Hf.
    assert (Hkl : (k < length low)%nat) by (apply nth_error_Some; congruence).
    assert (HL : length lit = k) by (rewrite <- Hf, length_firstn; lia).
    rewrite HL, Nat.add_1_r. rewrite (firstn_S_nth_error low k _ Hk). rewrite Hf. reflexivity.
Qed.

(** O1, the bcmp form the role branch needs (bcmp(low, lit, |lit| + 1) with the literal's NUL compared). *)
Lemma bridge_memcmp_lit : forall (lit low : list byte) k,
  ~ In (Z_to_bv 8 0) lit -> ~ In (Z_to_bv 8 0) (firstn k low) -> nth_error low k = Some (Z_to_bv 8 0) ->
  (StrFun.memcmp_model (firstn (length lit + 1) low) (lit ++ [Z_to_bv 8 0]) (length lit + 1) = Some 0 <->
   SegModel.strcmp (zs (firstn k low)) (zs lit) = 0).
Proof.
  intros lit low k Hlit Hlow Hk. rewrite <- (bridge_lit_prefix lit low k Hlit Hlow Hk). split.
  - intros H. apply memcmp_some0_firstn in H as [H1 _].
    rewrite firstn_firstn, Nat.min_id in H1.
    assert (E1 : firstn (length lit + 1) (lit ++ [Z_to_bv 8 0]) = lit ++ [Z_to_bv 8 0])
      by (apply firstn_all2; rewrite length_app; cbn [length]; lia).
    rewrite E1 in H1. exact H1.
  - intros H. rewrite H. apply memcmp_model_refl. rewrite length_app. cbn [length]. lia.
Qed.

(** And its existence, for a buffer of at least |lit| + 1 bytes. *)
Lemma bridge_memcmp_lit_total : forall (lit low : list byte) k,
  ~ In (Z_to_bv 8 0) lit -> ~ In (Z_to_bv 8 0) (firstn k low) -> nth_error low k = Some (Z_to_bv 8 0) ->
  (length lit + 1 <= length low)%nat ->
  exists v, StrFun.memcmp_model (firstn (length lit + 1) low) (lit ++ [Z_to_bv 8 0]) (length lit + 1) = Some v /\
    (v = 0 <-> SegModel.strcmp (zs (firstn k low)) (zs lit) = 0).
Proof.
  intros lit low k Hlit Hlow Hk Hlen.
  assert (H1 : (length lit + 1 <= length (firstn (length lit + 1) low))%nat) by (rewrite length_firstn; lia).
  assert (H2 : (length lit + 1 <= length (lit ++ [Z_to_bv 8 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  destruct (StrFun.memcmp_model_total _ _ _ H1 H2) as [v Hv].
  exists v. split; [exact Hv|]. rewrite <- (bridge_memcmp_lit lit low k Hlit Hlow Hk). rewrite Hv.
  split; [intros ->; reflexivity | intros H; injection H as H; exact H].
Qed.

(** ** 14. The box-model table *)

Lemma bytes_eqb_leqb : forall a b : list byte, pin_spec.bytes_eqb a b = SegModel.leqb (zs a) (zs b).
Proof. unfold zs. induction a as [|x a IH]; intros [|y b]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

Lemma len_leqb_and : forall a b, (length a =? length b)%nat && SegModel.leqb a b = SegModel.leqb a b.
Proof.
  intros a b. destruct (SegModel.leqb a b) eqn:E; [|apply andb_false_r].
  rewrite (SegModel.leqb_len _ _ E), Nat.eqb_refl. reflexivity.
Qed.

Lemma row_scan_go : forall f i t,
  pin_spec.row_scan f i t = SegModel.row_go (map (fun j => zs (pin_spec.tok_bytes j)) (seq i f)) (zs t) i.
Proof.
  induction f as [|f IH]; intros i t; [reflexivity|].
  cbn [pin_spec.row_scan seq map SegModel.row_go]. rewrite len_leqb_and, <- bytes_eqb_leqb, IH. reflexivity.
Qed.

Lemma row_of_cat_row : forall t : list byte, pin_spec.row_of t = SegModel.cat_row (zs t).
Proof.
  intros t. unfold pin_spec.row_of, pin_spec.row_from, SegModel.cat_row. rewrite row_scan_go.
  rewrite <- seg_spec.cat_toks_bytes. reflexivity.
Qed.

(** fuzz_catalogue_row's answer on the bytes s is cat_ptr of the spine's row of their values. *)
Lemma bridge_cat_row : forall cat (s : list byte),
  pin_spec.row_ptr cat s = seg_spec.cat_ptr cat (SegModel.cat_row (zs s)).
Proof.
  intros cat s. unfold pin_spec.row_ptr, seg_spec.cat_ptr, pin_spec.row_addr. rewrite row_of_cat_row. reflexivity.
Qed.

(** reac_box_catalogue_by_token: fuzz_catalogue_row on the token's bytes (strlen of a NUL-free token) is cat_ptr of
    SegModel.by_token. *)
Lemma bridge_by_token : forall cat (s : list byte), ~ In (Z_to_bv 8 0) s ->
  pin_spec.row_ptr cat s = seg_spec.cat_ptr cat (SegModel.by_token (zs s)).
Proof.
  intros cat s H. unfold SegModel.by_token. rewrite SegModel.cut_nul_id by (apply zs_nulfree; exact H).
  apply bridge_cat_row.
Qed.

(** Row i's own token names row i, in both models. *)
Lemma bridge_row_tok : forall cat i, (i < pin_spec.CAT_N)%nat ->
  pin_spec.row_ptr cat (pin_spec.tok_bytes i) = seg_spec.cat_ptr cat (Some i) /\
  SegModel.cat_row (nth i SegModel.cat_toks []) = Some i.
Proof.
  intros cat i Hi. split.
  - unfold pin_spec.row_ptr. rewrite (pin_spec.row_of_token i Hi). reflexivity.
  - rewrite <- (seg_spec.cat_tok_nth i Hi), <- row_of_cat_row. apply pin_spec.row_of_token. exact Hi.
Qed.
