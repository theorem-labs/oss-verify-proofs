(** Facts for the middle segment of reac-pw/fuzz_pin's LLVMFuzzerTestOneInput (plain): the harness's scan as
    pin_spec.colon_idx, the spec bytes s ++ NUL :: slack, the harness's want / want_label at the asm's branches, the
    table's image (its bytes are present in the image, its display pointers), and the memory transports the walk
    uses. No function of the binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec fuzz_catalogue_row_c reac_box_pin_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The scan `while (tok < len && spec[tok] != ':') tok++` *)
Lemma colon_idx_hit : forall s j, (j <= colon_idx s)%nat -> (j < length s)%nat ->
  bv_unsigned (nth j s NUL) = COLON -> colon_idx s = j.
Proof.
  induction s as [|x s IH]; intros j Hj Hl Hb; cbn [length] in Hl; [lia|].
  cbn [colon_idx] in *. destruct (bv_unsigned x =? COLON) eqn:E; [lia|].
  destruct j as [|j]; cbn [nth] in Hb.
  - rewrite Hb, Z.eqb_refl in E. discriminate.
  - f_equal. apply IH; [lia | lia | exact Hb].
Qed.

Lemma colon_idx_miss : forall s j, (j <= colon_idx s)%nat -> (j < length s)%nat ->
  bv_unsigned (nth j s NUL) <> COLON -> (S j <= colon_idx s)%nat.
Proof.
  induction s as [|x s IH]; intros j Hj Hl Hb; cbn [length] in Hl; [lia|].
  cbn [colon_idx] in *. destruct (bv_unsigned x =? COLON) eqn:E.
  - assert (j = 0)%nat by lia. subst j. cbn [nth] in Hb. apply Z.eqb_eq in E. contradiction.
  - destruct j as [|j]; [lia|]. cbn [nth] in Hb. specialize (IH j ltac:(lia) ltac:(lia) Hb). lia.
Qed.

Lemma colon_idx_end : forall s, (length s <= colon_idx s)%nat -> colon_idx s = length s.
Proof. intros s H. pose proof (colon_idx_le s). lia. Qed.

(** The byte at the colon index, when it is before the end, is ':'; the last byte, when the scan ran to the end, is
    not. *)
Lemma colon_idx_at_nth : forall s, (colon_idx s < length s)%nat -> bv_unsigned (nth (colon_idx s) s NUL) = COLON.
Proof.
  intros s H. destruct (colon_idx_at s H) as (b & Hb & Hc).
  rewrite (nth_error_nth s (colon_idx s) NUL Hb). exact Hc.
Qed.

(** ** The spec bytes s ++ NUL :: slack *)
Lemma nth_str_lt : forall s slack j, (j < length s)%nat -> nth j (s ++ NUL :: slack) NUL = nth j s NUL.
Proof. intros s slack j Hj. apply app_nth1. exact Hj. Qed.

Lemma nth_str_le : forall s slack j, (j <= length s)%nat ->
  nth j (s ++ NUL :: slack) NUL = nth j (s ++ [NUL]) NUL.
Proof.
  intros s slack j Hj. destruct (Nat.eq_dec j (length s)) as [->|Hne].
  - rewrite !app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite !app_nth1 by lia. reflexivity.
Qed.

Lemma length_str : forall s slack, length (s ++ NUL :: slack) = (length s + S (length slack))%nat.
Proof. intros. rewrite length_app. reflexivity. Qed.

(** One byte of a bytes_at run. *)
Lemma bytes_at_byte : forall m a bs j, bytes_at rsegs m a bs -> (j < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat j)) 1 = Some [nth j bs NUL].
Proof.
  intros m a bs j H Hj.
  rewrite (bytes_at_ov_read rsegs m a bs j 1 H) by lia.
  f_equal. clear H. revert j Hj. induction bs as [|x bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(** The 8 bytes of a bytes_at run of length 8. *)
Lemma bytes_at_read8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H L. pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. cbn [skipn]. f_equal. rewrite <- L. apply firstn_all.
Qed.

(** ** The harness's expectation at the asm's branches *)
Lemma row_ptr_zero : forall t, row_ptr FUZZ_CATALOGUE t = 0 -> row_of t = None.
Proof.
  intros t H. unfold row_ptr in H. destruct (row_of t) as [i|]; [|reflexivity].
  pose proof (row_addr_pos FUZZ_CATALOGUE i ltac:(unfold FUZZ_CATALOGUE; lia)). lia.
Qed.

Lemma want_none : forall cat spec fl s, harness_want fl s = None -> want_ptr cat fl s = 0 /\ want_label spec fl s = 0.
Proof. intros cat spec fl s H. unfold want_ptr, want_label. rewrite H. split; reflexivity. Qed.

Lemma want_off : forall fl s, Z.land fl 7 <> 0 -> harness_want fl s = None.
Proof.
  intros fl s H. unfold harness_want. apply Z.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma want_nil : forall fl s, length s = 0%nat -> harness_want fl s = None.
Proof.
  intros fl s H. unfold harness_want. rewrite H. cbn [Nat.eqb negb]. rewrite andb_false_r. reflexivity.
Qed.

Lemma want_on : forall fl s, Z.land fl 7 = 0 -> length s <> 0%nat ->
  harness_want fl s = row_of (firstn (colon_idx s) s).
Proof.
  intros fl s H1 H2. unfold harness_want. rewrite H1, Z.eqb_refl.
  destruct (Nat.eqb_spec (length s) 0) as [E|E]; [contradiction|]. reflexivity.
Qed.

(** want_label's test `tok < len && spec[tok + 1]` when tok is the colon index: before the end, the byte after the
    ':' (a byte of s ++ [NUL]); at the end, no label. *)
Lemma label_off_lt : forall s, (colon_idx s < length s)%nat ->
  harness_label_off s =
  if bv_unsigned (nth (S (colon_idx s)) (s ++ [NUL]) NUL) =? 0 then None else Some (S (colon_idx s)).
Proof.
  intros s H. unfold harness_label_off. apply Nat.ltb_lt in H. rewrite H. cbn [andb].
  destruct (Z.eqb (bv_unsigned (nth (S (colon_idx s)) (s ++ [NUL]) NUL)) 0); reflexivity.
Qed.

Lemma label_off_end : forall s, colon_idx s = length s -> harness_label_off s = None.
Proof.
  intros s H. unfold harness_label_off. rewrite H, Nat.ltb_irrefl. reflexivity.
Qed.

(** ** The table: every byte present in the image; the display pointer of each row *)
Definition rom_some (a : Z) : bool := match seg_rom rsegs (wa a) with Some _ => true | None => false end.

Lemma rom_range : forall base n, forallb (fun j => rom_some (base + Z.of_nat j)) (seq 0 n) = true ->
  forall a, base <= a < base + Z.of_nat n -> seg_rom rsegs (wa a) <> None.
Proof.
  intros base n H a Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - base)) ltac:(apply in_seq; lia)). unfold rom_some in H.
  replace (base + Z.of_nat (Z.to_nat (a - base))) with a in H by lia.
  destruct (seg_rom rsegs (wa a)); [discriminate | discriminate H].
Qed.

Lemma table_rom : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> seg_rom rsegs (wa a) <> None.
Proof. intros a Ha. apply (rom_range FUZZ_CATALOGUE 3256); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma got_rom : forall a, PARSE_SSP_GOT <= a < PARSE_SSP_GOT + 8 -> seg_rom rsegs (wa a) <> None.
Proof. intros a Ha. apply (rom_range PARSE_SSP_GOT 8); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma guard_rom : forall a, PARSE_SSP_GUARD <= a < PARSE_SSP_GUARD + 8 -> seg_rom rsegs (wa a) <> None.
Proof. intros a Ha. apply (rom_range PARSE_SSP_GUARD 8); [vm_compute; reflexivity | exact Ha]. Qed.

(** The table premise of the contracts: its bytes read as the image's. *)
Definition tbl (m : word -> option byte) : Prop :=
  forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).

Lemma rdn_tbl : forall m n a, tbl m -> FUZZ_CATALOGUE <= a -> a + Z.of_nat n <= FUZZ_CATALOGUE + CAT_BYTES ->
  rdn rsegs m (wa a) n = rdn rsegs (fun _ => None) (wa a) n.
Proof.
  intros m n. induction n as [|n IH]; intros a T H1 H2; [reflexivity|].
  cbn [rdn]. rewrite (wa_succ a). rewrite (IH (a + 1) T) by lia.
  pose proof (T a ltac:(lia)) as Ta. unfold mrd in Ta. rewrite Ta. reflexivity.
Qed.

Definition bytes_eqo (o : option (list byte)) (l : list byte) : bool :=
  match o with Some bs => bytes_eqb bs l | None => false end.

Lemma bytes_eqo_eq : forall o l, bytes_eqo o l = true -> o = Some l.
Proof.
  intros [bs|] l H; cbn [bytes_eqo] in H; [|discriminate]. apply bytes_eqb_eq in H. subst. reflexivity.
Qed.

Lemma disp_image : forall i, (i < CAT_N)%nat ->
  rdn rsegs (fun _ => None) (wa (row_addr FUZZ_CATALOGUE i + 8)) 8 = Some (le8 (Z_to_bv 64 (disp_ptr i))).
Proof.
  intros i Hi. apply bytes_eqo_eq. revert i Hi.
  apply (all_rows_spec (fun i => bytes_eqo (rdn rsegs (fun _ => None) (wa (row_addr FUZZ_CATALOGUE i + 8)) 8)
                                   (le8 (Z_to_bv 64 (disp_ptr i))))).
  vm_compute. reflexivity.
Qed.

Lemma disp_read : forall m i, tbl m -> (i < CAT_N)%nat ->
  ov_read_bytes rsegs m (wa (row_addr FUZZ_CATALOGUE i + 8)) 8 = Some (le8 (Z_to_bv 64 (disp_ptr i))).
Proof.
  intros m i T Hi. rewrite ov_rdn.
  assert (R : FUZZ_CATALOGUE <= row_addr FUZZ_CATALOGUE i + 8 /\
              row_addr FUZZ_CATALOGUE i + 8 + Z.of_nat 8 <= FUZZ_CATALOGUE + CAT_BYTES)
    by (unfold row_addr, CAT_ROW, CAT_BYTES, CAT_N in *; lia).
  rewrite (rdn_tbl m 8 _ T (proj1 R) (proj2 R)). apply disp_image. exact Hi.
Qed.

Lemma row_addr_range : forall i, (i < CAT_N)%nat ->
  0 < row_addr FUZZ_CATALOGUE i /\ row_addr FUZZ_CATALOGUE i + 16 < 2 ^ 64.
Proof. intros i Hi. unfold row_addr, FUZZ_CATALOGUE, CAT_ROW, CAT_N in *. lia. Qed.

(** ** Memory transports *)
Lemma tbl_munch : forall W m1 m2, tbl m1 -> munch W m1 m2 ->
  (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> outside W a) -> tbl m2.
Proof.
  intros W m1 m2 T MU H a Ha. unfold mrd. rewrite (MU (wa a)).
  - exact (T a Ha).
  - rewrite wa_unsigned by (unfold FUZZ_CATALOGUE, CAT_BYTES in *; lia). apply H. exact Ha.
Qed.

(** Two ranges apart pointwise are apart as intervals. *)
Lemma ivl_apart : forall A n x y, (forall a, A <= a < A + n -> ~ (x <= a < y)) -> 0 < n -> x < y ->
  A + n <= x \/ y <= A.
Proof.
  intros A n x y H Hn Hxy. destruct (Z.le_gt_cases (A + n) x) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases y A) as [|H2]; [right; lia|].
  exfalso. apply (H (Z.max A x)); lia.
Qed.

(** A range where the image has no byte is apart from a range where it has every byte. *)
Lemma rom_apart : forall X Y U V,
  (forall a, X <= a < Y -> seg_rom rsegs (wa a) = None) ->
  (forall a, U <= a < V -> seg_rom rsegs (wa a) <> None) ->
  forall a, U <= a < V -> ~ (X <= a < Y).
Proof. intros X Y U V H1 H2 a Ha Hx. exact (H2 a Ha (H1 a Hx)). Qed.

Lemma wr_at_sub : forall m a n b k, wr_at rsegs m a n -> a <= b -> b + k <= a + n -> 0 <= k -> wr_at rsegs m b k.
Proof.
  intros m a n b k (H1 & H2 & H) Hb Hk Hk0. split; [lia|]. split; [lia|].
  intros i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

Lemma munch_nil_eq : forall m1 m2 x, munch [] m1 m2 -> m2 x = m1 x.
Proof. intros m1 m2 x H. apply H. exact I. Qed.

Lemma bytes_at_firstn : forall m a l n, bytes_at rsegs m a l -> bytes_at rsegs m a (firstn n l).
Proof. intros m a l n H. rewrite <- (firstn_skipn n l) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma firstn_str : forall s slack c, (c <= length s)%nat -> firstn c (s ++ NUL :: slack) = firstn c s.
Proof.
  intros s slack c Hc. rewrite firstn_app. replace (c - length s)%nat with 0%nat by lia. cbn [firstn].
  apply app_nil_r.
Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw_cells_CB_wr : forall m A n bs, rw_cells rsegs m A [CB n bs] -> wr_at rsegs m A (Z.of_nat n).
Proof. intros m A n bs [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw. Qed.

Lemma rw_cells_CB_prefix : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k bs)].
Proof.
  intros m A n bs k H Hk. pose proof H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_firstn. exact (rw_cells_CB_bytes _ _ _ _ H).
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (wr_at_sub m A (Z.of_nat n)); [exact (rw_cells_CB_wr _ _ _ _ H) | lia | lia | lia].
Qed.

Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. apply unsigned_lit. lia.
Qed.

Lemma byte_lit : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. exact (zxb_unsigned b). Qed.

(** ** reac_box_pin_parse's arguments (0x12d84 .. 0x12db4): each a mask of a flag bit, and-ed with the pointer *)
Lemma mask_gen : forall (g : Z -> Z) (k : Z),
  forallb (fun z => g z =? (if Z.testbit z k then 0 else 2 ^ 64 - 1)) (map Z.of_nat (seq 0 256)) = true ->
  forall fl, 0 <= fl < 256 -> g fl = if Z.testbit fl k then 0 else 2 ^ 64 - 1.
Proof.
  intros g k H fl Hfl. rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  apply in_map_iff. exists (Z.to_nat fl). split; [lia | apply in_seq; lia].
Qed.

Lemma mask0 : forall fl, 0 <= fl < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1 + -1)) = if Z.testbit fl 0 then 0 else 2 ^ 64 - 1.
Proof.
  apply (mask_gen (fun fl => bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 fl)) 1 + -1))) 0).
  vm_compute. reflexivity.
Qed.

Lemma mask1 : forall fl, 0 <= fl < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fl)) 62))) 63 + -1))
  = if Z.testbit fl 1 then 0 else 2 ^ 64 - 1.
Proof.
  apply (mask_gen (fun fl => bv_unsigned (Z_to_bv 64
           (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fl)) 62))) 63 + -1))) 1).
  vm_compute. reflexivity.
Qed.

Lemma mask2 : forall fl, 0 <= fl < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fl)) 61))) 63 + -1))
  = if Z.testbit fl 2 then 0 else 2 ^ 64 - 1.
Proof.
  apply (mask_gen (fun fl => bv_unsigned (Z_to_bv 64
           (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fl)) 61))) 63 + -1))) 2).
  vm_compute. reflexivity.
Qed.

Lemma land_mask : forall (b : bool) y, 0 <= y < 2 ^ 64 -> Z.land (if b then 0 else 2 ^ 64 - 1) y = if b then 0 else y.
Proof.
  intros [|] y Hy; [apply Z.land_0_l|].
  change (Z.land (2 ^ 64 - 1) y = y). rewrite Z.land_comm. change (2 ^ 64 - 1) with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma ue : forall (b : bool) x, 0 < x < 2 ^ 64 -> (bv_unsigned (Z_to_bv 64 (if b then 0 else x)) =? 0) = b.
Proof.
  intros [|] x Hx.
  - change (if true then 0 else x) with 0. reflexivity.
  - change (if false then 0 else x) with x. rewrite unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma live_eq : forall fl p y z, 0 < p < 2 ^ 64 -> 0 < y < 2 ^ 64 -> 0 < z < 2 ^ 64 ->
  parse_live (Z_to_bv 64 (if Z.testbit fl 0 then 0 else p)) (Z_to_bv 64 (if Z.testbit fl 1 then 0 else y))
             (Z_to_bv 64 (if Z.testbit fl 2 then 0 else z)) = fl_live fl.
Proof. intros fl p y z Hp Hy Hz. unfold parse_live, fl_live. rewrite !ue by lia. reflexivity. Qed.

Lemma po_eq : forall cat fl p s, 0 <= p < 2 ^ 64 ->
  parse_out cat (bv_unsigned (Z_to_bv 64 (if Z.testbit fl 0 then 0 else p))) (fl_live fl) s =
  parse_out cat p (fl_live fl) s.
Proof.
  intros cat fl p s Hp. unfold fl_live. destruct (Z.testbit fl 0); cbn [negb andb]; [reflexivity|].
  change (if false then 0 else p) with p. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma live_bits : forall fl, fl_live fl = true ->
  Z.testbit fl 0 = false /\ Z.testbit fl 1 = false /\ Z.testbit fl 2 = false.
Proof.
  intros fl H. unfold fl_live in H.
  destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); cbn in H; try discriminate; auto.
Qed.

Lemma live_out : forall cat p fl s r, parse_out cat p (fl_live fl) s = Some r -> fl_live fl = true.
Proof. intros cat p fl s r H. destruct (fl_live fl); [reflexivity | discriminate H]. Qed.

(** ** check_known's premise at the harness's values *)
Lemma want_ptr_range : forall fl s, 0 <= want_ptr FUZZ_CATALOGUE fl s < 2 ^ 64.
Proof.
  intros fl s. unfold want_ptr. destruct (harness_want fl s) as [i|] eqn:E; [|lia].
  unfold harness_want in E. destruct ((Z.land fl 7 =? 0) && negb (Nat.eqb (length s) 0)); [|discriminate].
  destruct (row_of_some _ _ E) as (Hi & _ & _). unfold row_addr, FUZZ_CATALOGUE, CAT_ROW, CAT_N in *. lia.
Qed.

Lemma known_iff : forall p fl s, 0 <= fl < 256 -> ~ In NUL s ->
  (bv_unsigned (Z_to_bv 64 (parse_rc (parse_out FUZZ_CATALOGUE p (fl_live fl) s))) = 0 <->
   bv_unsigned (Z_to_bv 64 (want_ptr FUZZ_CATALOGUE fl s)) <> 0).
Proof.
  intros p fl s Hfl Hs.
  pose proof (harness_known FUZZ_CATALOGUE p fl s ltac:(unfold FUZZ_CATALOGUE; lia) Hfl Hs) as HK.
  pose proof (want_ptr_range fl s) as R. rewrite (unsigned_lit (want_ptr FUZZ_CATALOGUE fl s)) by lia.
  destruct (parse_out FUZZ_CATALOGUE p (fl_live fl) s) as [o|]; cbn [parse_rc] in *.
  - rewrite unsigned_lit by lia. exact HK.
  - replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    destruct HK as [HK1 HK2]. split; intros X; [lia | specialize (HK2 X); lia].
Qed.
