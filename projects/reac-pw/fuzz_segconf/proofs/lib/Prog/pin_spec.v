(** The `--box MODEL[:LABEL]` pin of reac-pw (src/reac_box_pin.h:42-54, restated in fuzz/fuzz_pin.c:4-19 and
    :30-69) and the box-model table the harness links (fuzz/catalogue.c:12-35), over byte lists. Shared by the plain
    and the UBSan contracts of reac-pw/fuzz_pin (lib/Prog/*_c.v, lib/U/Prog/*_c.v), as qdisc_spec.v is for
    reac-pw/fuzz_qdisc. Statement text only: no function of the binary is proved here.

    The rows: fuzz_catalogue is 3256 bytes of .data.rel.ro (0x20ad0 in the plain image, 0x21468 in the UBSan one;
    each build's fuzz_catalogue_row_c.v names it FUZZ_CATALOGUE), 11 rows of 0x128 bytes (struct reac_box_model). Row i
    holds its token pointer at +0 and its display pointer at +8. Both pointers point into .rodata (in the r-- segment
    [0x10000, 0x121d8) of the plain image and [0x10000, 0x1229c) of the UBSan one) and have the same values in the two images. The pointers and
    strings below were read from the unstripped twins fuzz_pin.{plain,ubsan} (PT_LOAD-equal to the pinned files).

    The lookup: fuzz_catalogue_row (catalogue.c:29-35) and reac_box_pin_parse (src/reac_box_pin.c; not in the tree,
    read from the binary, plain 0x12e90) both scan rows 0..10 and stop at the FIRST row whose token equals the probe:
    fuzz_catalogue_row by `strlen(token) == n && memcmp(token, s, n) == 0`, reac_box_pin_parse by
    `strlen(token) == toklen && strncmp(spec, token, toklen) == 0`. [row_of] is that first-match scan.

    The grammar: the token is the text before the FIRST ':' ([colon_idx], strcspn(spec, ":")); a pin names a model
    only when its token is a whole token of the table; the label is the text after that ':' when it is not empty,
    else the model's display string. *)
From Stdlib Require Import String Ascii.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition sbytes (s : string) : list byte :=
  map (fun a => Z_to_bv 8 (Z.of_N (N_of_ascii a))) (list_ascii_of_string s).

Definition NUL : byte := Z_to_bv 8 0.
Definition COLON : Z := 58.

(** ** The table *)
Record row := Row { r_tok : string; r_disp : string; r_tokp : Z; r_dispp : Z }.

Local Open Scope string_scope.
Definition rows : list row :=
  [ Row "s1608" "S-1608 (16 in / 8 out)" 0x108f1 0x10556;
    Row "s0808" "S-0808 (8 in / 8 out)" 0x1087e 0x102e3;
    Row "s4000s" "S-4000S-3208 (32 in / 8 out)" 0x10934 0x1051c;
    Row "s4000s-0832" "S-4000S-0832 (8 in / 32 out)" 0x10340 0x107f4;
    Row "s0816" "S-0816 (8 in / 16 out)" 0x1038f 0x103e4;
    Row "s2416" "S-2416 (24 in / 16 out)" 0x1067a 0x1056d;
    Row "s4000d" "S-4000D (0 in / 32 out)" 0x1045c 0x105f2;
    Row "s4000m" "S-4000M (32 in / 0 out)" 0x1060a 0x1073d;
    Row "fr4000" "FreeREAC 40 in / 0 out" 0x10755 0x1034c;
    Row "fr0040" "FreeREAC 0 in / 40 out" 0x10307 0x10611;
    Row "fr2020" "FreeREAC 20 in / 20 out" 0x103fb 0x10320 ].
Definition row0 : row := Row "" "" 0 0.
Local Close Scope string_scope.

Definition CAT_N : nat := 11.
Definition CAT_ROW : Z := 0x128.
Definition CAT_BYTES : Z := 3256.

Definition row_at (i : nat) : row := nth i rows row0.
Definition tok_bytes (i : nat) : list byte := sbytes (r_tok (row_at i)).
Definition disp_bytes (i : nat) : list byte := sbytes (r_disp (row_at i)).
Definition tok_ptr (i : nat) : Z := r_tokp (row_at i).
Definition disp_ptr (i : nat) : Z := r_dispp (row_at i).
(** The address of row i of a table at [cat]. *)
Definition row_addr (cat : Z) (i : nat) : Z := cat + CAT_ROW * Z.of_nat i.

(** ** The first-match lookup *)
Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (bv_unsigned x =? bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.

(** [row_from i t]: the first row j with i <= j < 11 whose token is t. *)
Fixpoint row_scan (fuel i : nat) (t : list byte) : option nat :=
  match fuel with
  | O => None
  | S f => if bytes_eqb (tok_bytes i) t then Some i else row_scan f (S i) t
  end.
Definition row_from (i : nat) (t : list byte) : option nat := row_scan (CAT_N - i) i t.
Definition row_of (t : list byte) : option nat := row_from 0 t.
(** fuzz_catalogue_row(s, n)'s result when the n bytes at s are t: &table[i] for the first row i whose token is t,
    else NULL. *)
Definition row_ptr (cat : Z) (t : list byte) : Z := match row_of t with Some i => row_addr cat i | None => 0 end.

(** ** The grammar *)
(** Index of the first ':' of s, or its length (strcspn(spec, ":") on spec = s ++ NUL :: _). *)
Fixpoint colon_idx (s : list byte) : nat :=
  match s with
  | [] => O
  | x :: s' => if bv_unsigned x =? COLON then O else S (colon_idx s')
  end.
Definition pin_token (s : list byte) : list byte := firstn (colon_idx s) s.
Definition pin_row (s : list byte) : option nat := row_of (pin_token s).
(** Offset in the spec of the label: just past the first ':' when at least one byte follows it. *)
Definition pin_label_off (s : list byte) : option nat :=
  if (S (colon_idx s) <? length s)%nat then Some (S (colon_idx s)) else None.
(** The label pointer of an accepted pin whose spec string s is at [spec] and whose row is i. *)
Definition label_addr (spec : Z) (s : list byte) (i : nat) : Z :=
  match pin_label_off s with Some k => spec + Z.of_nat k | None => disp_ptr i end.

(** reac_box_pin_parse(spec, model, label): [live] is "spec, model and label are all non-NULL"; s is the string at
    spec. Some (row, label) when the pin is accepted (it returns 0 and stores row in *model, label in *label), None
    when refused (it returns -1). *)
Definition parse_out (cat spec : Z) (live : bool) (s : list byte) : option (Z * Z) :=
  if live then
    match pin_row s with Some i => Some (row_addr cat i, label_addr spec s i) | None => None end
  else None.
Definition parse_rc (o : option (Z * Z)) : Z := match o with Some _ => 0 | None => -1 end.

(** ** The harness's view (fuzz/fuzz_pin.c:71-104, fuzz/fuzz.h:31-97) *)
(** Index of the first NUL of l, or its length. *)
Fixpoint nul_idx (l : list byte) : nat :=
  match l with
  | [] => O
  | x :: l' => if bv_unsigned x =? 0 then O else S (nul_idx l')
  end.
(** fuzz_u8: the flags byte (0 for an empty input); fuzz_take: the rest; fuzz_str: the rest cut at its first NUL. *)
Definition pin_flags (inp : list byte) : Z := match inp with [] => 0 | b :: _ => bv_unsigned b end.
Definition pin_rest (inp : list byte) : list byte := tl inp.
Definition pin_k (inp : list byte) : nat := nul_idx (pin_rest inp).
Definition pin_str (inp : list byte) : list byte := firstn (pin_k inp) (pin_rest inp).

(** Flag bit 0 hands reac_box_pin_parse a NULL spec, bit 1 a NULL model out, bit 2 a NULL label out. *)
Definition fl_live (fl : Z) : bool := negb (Z.testbit fl 0) && negb (Z.testbit fl 1) && negb (Z.testbit fl 2).

(** The expectation, from the grammar alone: `tok` is the harness's scan `while (tok < len && spec[tok] != ':')`, the
    same index as [colon_idx]; want is fuzz_catalogue_row(spec, tok) when `!(flags & 7) && len`. *)
Definition harness_want (fl : Z) (s : list byte) : option nat :=
  if (Z.land fl 7 =? 0) && negb (Nat.eqb (length s) 0) then row_of (firstn (colon_idx s) s) else None.
(** want_label's condition as the harness writes it: `tok < len && spec[tok + 1]`, on the spec bytes s ++ [NUL]. *)
Definition harness_label_off (s : list byte) : option nat :=
  if (colon_idx s <? length s)%nat && negb (bv_unsigned (nth (S (colon_idx s)) (s ++ [NUL]) NUL) =? 0)
  then Some (S (colon_idx s)) else None.
Definition want_ptr (cat fl : Z) (s : list byte) : Z :=
  match harness_want fl s with Some i => row_addr cat i | None => 0 end.
Definition want_label (spec fl : Z) (s : list byte) : Z :=
  match harness_want fl s with
  | Some i => match harness_label_off s with Some k => spec + Z.of_nat k | None => disp_ptr i end
  | None => 0
  end.

(** ** Sanity, by computation *)
Lemma rows_length : length rows = CAT_N.
Proof. reflexivity. Qed.

Lemma cat_bytes_rows : CAT_BYTES = CAT_ROW * Z.of_nat CAT_N.
Proof. reflexivity. Qed.

Lemma cat_row_mod8 : CAT_ROW mod 8 = 0.
Proof. reflexivity. Qed.

Definition all_rows (P : nat -> bool) : bool := forallb P (seq 0 CAT_N).

Lemma all_rows_spec : forall P, all_rows P = true -> forall i, (i < CAT_N)%nat -> P i = true.
Proof.
  intros P H i Hi. unfold all_rows in H. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

Lemma tok_lengths : map (fun i => length (tok_bytes i)) (seq 0 CAT_N) = [5; 5; 6; 11; 5; 5; 6; 6; 6; 6; 6]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma tokens_nonempty : forall i, (i < CAT_N)%nat -> (0 < length (tok_bytes i))%nat.
Proof.
  intros i Hi. apply Nat.ltb_lt. revert i Hi.
  apply (all_rows_spec (fun i => 0 <? length (tok_bytes i))%nat). vm_compute. reflexivity.
Qed.

Lemma tokens_no_colon : forall i b, (i < CAT_N)%nat -> In b (tok_bytes i) -> bv_unsigned b <> COLON.
Proof.
  intros i b Hi Hb.
  pose proof (all_rows_spec (fun i => forallb (fun c => negb (bv_unsigned c =? COLON)) (tok_bytes i))
                ltac:(vm_compute; reflexivity) i Hi) as H. cbn beta in H.
  rewrite forallb_forall in H. specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma tokens_no_nul : forall i b, (i < CAT_N)%nat -> In b (tok_bytes i) -> bv_unsigned b <> 0.
Proof.
  intros i b Hi Hb.
  pose proof (all_rows_spec (fun i => forallb (fun c => negb (bv_unsigned c =? 0)) (tok_bytes i))
                ltac:(vm_compute; reflexivity) i Hi) as H. cbn beta in H.
  rewrite forallb_forall in H. specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma displays_no_nul : forall i b, (i < CAT_N)%nat -> In b (disp_bytes i) -> bv_unsigned b <> 0.
Proof.
  intros i b Hi Hb.
  pose proof (all_rows_spec (fun i => forallb (fun c => negb (bv_unsigned c =? 0)) (disp_bytes i))
                ltac:(vm_compute; reflexivity) i Hi) as H. cbn beta in H.
  rewrite forallb_forall in H. specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst b. f_equal. apply bv_eq. exact H1.
  - injection H as -> ->. apply andb_true_intro. split; [apply Z.eqb_refl | apply IH; reflexivity].
Qed.

Lemma tokens_distinct : forall i j, (i < CAT_N)%nat -> (j < CAT_N)%nat -> tok_bytes i = tok_bytes j -> i = j.
Proof.
  intros i j Hi Hj E.
  assert (H : all_rows (fun i => all_rows (fun j => implb (bytes_eqb (tok_bytes i) (tok_bytes j)) (Nat.eqb i j)))
              = true) by (vm_compute; reflexivity).
  pose proof (all_rows_spec _ (all_rows_spec _ H i Hi) j Hj) as Hij. cbn beta in Hij.
  rewrite (proj2 (bytes_eqb_eq _ _) E) in Hij. apply Nat.eqb_eq. exact Hij.
Qed.

Lemma row_from_step : forall i t, (i < CAT_N)%nat ->
  row_from i t = if bytes_eqb (tok_bytes i) t then Some i else row_from (S i) t.
Proof.
  intros i t Hi. unfold row_from. replace (CAT_N - i)%nat with (S (CAT_N - S i)) by (unfold CAT_N in *; lia).
  reflexivity.
Qed.

Lemma row_from_end : forall t, row_from CAT_N t = None.
Proof. reflexivity. Qed.

Lemma bytes_eqb_refl : forall a, bytes_eqb a a = true.
Proof. intros a. apply bytes_eqb_eq. reflexivity. Qed.

Lemma row_scan_spec : forall f i t j, row_scan f i t = Some j ->
  (i <= j < i + f)%nat /\ tok_bytes j = t /\ (forall j', (i <= j' < j)%nat -> tok_bytes j' <> t).
Proof.
  induction f as [|f IH]; intros i t j H; cbn [row_scan] in H; [discriminate|].
  destruct (bytes_eqb (tok_bytes i) t) eqn:E.
  - injection H as <-. apply bytes_eqb_eq in E. split; [lia|]. split; [exact E|]. intros j' Hj'. exfalso. lia.
  - destruct (IH (S i) t j H) as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
    intros j' Hj' Ej'. destruct (Nat.eq_dec j' i) as [->|Hne].
    + rewrite Ej' in E. rewrite bytes_eqb_refl in E. discriminate.
    + apply (H3 j'); [lia | exact Ej'].
Qed.

Lemma row_scan_none : forall f i t, row_scan f i t = None -> forall j, (i <= j < i + f)%nat -> tok_bytes j <> t.
Proof.
  induction f as [|f IH]; intros i t H j Hj; [exfalso; lia|]. cbn [row_scan] in H.
  destruct (bytes_eqb (tok_bytes i) t) eqn:E; [discriminate|].
  destruct (Nat.eq_dec j i) as [->|Hne].
  - intros Ej. rewrite Ej in E. rewrite bytes_eqb_refl in E. discriminate.
  - apply (IH (S i) t H). lia.
Qed.

(** [row_of t = Some i]: row i's token is t, and no earlier row's is. *)
Lemma row_of_some : forall t i, row_of t = Some i ->
  (i < CAT_N)%nat /\ tok_bytes i = t /\ (forall j, (j < i)%nat -> tok_bytes j <> t).
Proof.
  intros t i H. destruct (row_scan_spec _ _ _ _ H) as (H1 & H2 & H3). split; [unfold CAT_N in *; lia|].
  split; [exact H2|]. intros j Hj. apply H3. lia.
Qed.

Lemma row_of_none : forall t, row_of t = None -> forall i, (i < CAT_N)%nat -> tok_bytes i <> t.
Proof. intros t H i Hi. apply (row_scan_none _ _ _ H). unfold CAT_N in *. lia. Qed.

Lemma row_of_token : forall i, (i < CAT_N)%nat -> row_of (tok_bytes i) = Some i.
Proof.
  intros i Hi.
  assert (H : all_rows (fun i => match row_of (tok_bytes i) with Some j => Nat.eqb i j | None => false end) = true)
    by (vm_compute; reflexivity).
  pose proof (all_rows_spec _ H i Hi) as Hj. cbn beta in Hj.
  destruct (row_of (tok_bytes i)) as [j|]; [|discriminate]. apply Nat.eqb_eq in Hj. subst j. reflexivity.
Qed.

Lemma row_addr_pos : forall cat i, 0 < cat -> 0 < row_addr cat i.
Proof. intros cat i H. unfold row_addr, CAT_ROW. lia. Qed.

Lemma row_addr_mod8 : forall cat i, cat mod 8 = 0 -> row_addr cat i mod 8 = 0.
Proof.
  intros cat i H. unfold row_addr, CAT_ROW. rewrite Z.add_mod, H by lia.
  replace (0x128 * Z.of_nat i) with ((37 * Z.of_nat i) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma colon_idx_le : forall s, (colon_idx s <= length s)%nat.
Proof.
  induction s as [|x s IH]; cbn [colon_idx length]; [lia|]. destruct (bv_unsigned x =? COLON); lia.
Qed.

(** The token has no ':'; when the scan stops before the end, it stops on a ':'. *)
Lemma colon_idx_before : forall s j b, (j < colon_idx s)%nat -> nth_error s j = Some b -> bv_unsigned b <> COLON.
Proof.
  induction s as [|x s IH]; intros j b Hj Hn; cbn [colon_idx] in Hj; [exfalso; lia|].
  destruct (bv_unsigned x =? COLON) eqn:E; [exfalso; lia|]. destruct j as [|j]; cbn [nth_error] in Hn.
  - injection Hn as <-. apply Z.eqb_neq. exact E.
  - apply (IH j b); [lia | exact Hn].
Qed.

Lemma colon_idx_at : forall s, (colon_idx s < length s)%nat ->
  exists b, nth_error s (colon_idx s) = Some b /\ bv_unsigned b = COLON.
Proof.
  induction s as [|x s IH]; intros H; cbn [colon_idx length] in H |- *; [exfalso; lia|].
  destruct (bv_unsigned x =? COLON) eqn:E.
  - exists x. split; [reflexivity | apply Z.eqb_eq; exact E].
  - apply IH. lia.
Qed.

Lemma pin_row_nil : pin_row [] = None.
Proof. vm_compute. reflexivity. Qed.

Lemma nul_idx_le : forall l, (nul_idx l <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [nul_idx length]; [lia|]. destruct (bv_unsigned x =? 0); lia.
Qed.

Lemma pin_str_length : forall inp, length (pin_str inp) = pin_k inp.
Proof. intros inp. unfold pin_str. rewrite length_firstn. pose proof (nul_idx_le (pin_rest inp)). unfold pin_k. lia. Qed.

Lemma firstn_nul_idx_no_nul : forall l, ~ In NUL (firstn (nul_idx l) l).
Proof.
  induction l as [|x l IH]; cbn [nul_idx firstn In]; [tauto|].
  destruct (bv_unsigned x =? 0) eqn:E; cbn [firstn In]; [tauto|].
  intros [Hx|Hin]; [|exact (IH Hin)]. subst x. vm_compute in E. discriminate.
Qed.

Lemma pin_str_no_nul : forall inp, ~ In NUL (pin_str inp).
Proof. intros inp. apply firstn_nul_idx_no_nul. Qed.

Lemma pin_flags_range : forall inp, 0 <= pin_flags inp < 256.
Proof.
  intros [|b inp]; cbn; [lia|]. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.

(** ** The expectation agrees with the library *)
Lemma land7_live : forall fl, 0 <= fl < 256 -> (Z.land fl 7 =? 0) = fl_live fl.
Proof.
  intros fl Hfl.
  assert (H : forallb (fun z => Bool.eqb (Z.land z 7 =? 0) (fl_live z)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff. exists (Z.to_nat fl).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma nth_app_nul : forall s j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL = nth j s NUL.
Proof. intros s j Hj. rewrite app_nth1 by exact Hj. reflexivity. Qed.

(** want_label's test is pin_label_off for a string with no NUL. *)
Lemma harness_label_off_eq : forall s, ~ In NUL s -> harness_label_off s = pin_label_off s.
Proof.
  intros s Hs. unfold harness_label_off, pin_label_off. pose proof (colon_idx_le s) as Hle.
  destruct (Nat.ltb_spec (colon_idx s) (length s)) as [Hlt|Hge]; cbn [andb].
  - destruct (Nat.ltb_spec (S (colon_idx s)) (length s)) as [Hlt2|Hge2].
    + rewrite nth_app_nul by exact Hlt2.
      assert (Hb : bv_unsigned (nth (S (colon_idx s)) s NUL) <> 0).
      { intros E. apply Hs. assert (Hin : In (nth (S (colon_idx s)) s NUL) s) by (apply nth_In; exact Hlt2).
        replace (nth (S (colon_idx s)) s NUL) with NUL in Hin; [exact Hin|].
        apply bv_eq. rewrite E. reflexivity. }
      apply Z.eqb_neq in Hb. rewrite Hb. reflexivity.
    + replace (S (colon_idx s)) with (length s) by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - destruct (Nat.ltb_spec (S (colon_idx s)) (length s)); [exfalso; lia | reflexivity].
Qed.

(** The harness's expectation is reac_box_pin_parse's result: for the flags byte fl the harness hands
    reac_box_pin_parse (fl_live fl) and the spec string s (no NUL) at [spec], the parse accepts exactly when want is
    a row, names that row, and names want_label. *)
Lemma harness_agrees : forall cat spec fl s, 0 <= fl < 256 -> ~ In NUL s ->
  parse_out cat spec (fl_live fl) s =
  match harness_want fl s with
  | Some i => Some (row_addr cat i,
                    match harness_label_off s with Some k => spec + Z.of_nat k | None => disp_ptr i end)
  | None => None
  end.
Proof.
  intros cat spec fl s Hfl Hs. rewrite (harness_label_off_eq s Hs). unfold parse_out, harness_want.
  rewrite (land7_live fl Hfl). destruct (fl_live fl); cbn [andb]; [|reflexivity].
  destruct s as [|x s'].
  - rewrite pin_row_nil. reflexivity.
  - cbn [length Nat.eqb negb]. unfold pin_row, pin_token, label_addr. destruct (row_of _); reflexivity.
Qed.

(** check_known's premise, check_row's and check_label's, at the values the harness passes: rc is parse_rc of
    parse_out, want is want_ptr, the model and label outs are the pair of parse_out. *)
Lemma harness_known : forall cat spec fl s, 0 < cat -> 0 <= fl < 256 -> ~ In NUL s ->
  (parse_rc (parse_out cat spec (fl_live fl) s) = 0 <-> want_ptr cat fl s <> 0).
Proof.
  intros cat spec fl s Hc Hfl Hs. rewrite (harness_agrees cat spec fl s Hfl Hs). unfold want_ptr.
  destruct (harness_want fl s) as [i|]; cbn [parse_rc]; split; intros H; try lia.
  pose proof (row_addr_pos cat i Hc). lia.
Qed.

Lemma harness_row_label : forall cat spec fl s row lab, 0 <= fl < 256 -> ~ In NUL s ->
  parse_out cat spec (fl_live fl) s = Some (row, lab) -> row = want_ptr cat fl s /\ lab = want_label spec fl s.
Proof.
  intros cat spec fl s row lab Hfl Hs H. rewrite (harness_agrees cat spec fl s Hfl Hs) in H.
  unfold want_ptr, want_label. destruct (harness_want fl s) as [i|]; [|discriminate].
  injection H as <- <-. split; reflexivity.
Qed.

(** want, as the harness computes it: fuzz_catalogue_row(spec, tok) when `!(flags & 7) && len`, else NULL. *)
Lemma want_ptr_row : forall cat fl s,
  want_ptr cat fl s =
  if (Z.land fl 7 =? 0) && negb (Nat.eqb (length s) 0) then row_ptr cat (firstn (colon_idx s) s) else 0.
Proof. intros cat fl s. unfold want_ptr, harness_want, row_ptr. destruct (_ && _); reflexivity. Qed.
