(** Helper definitions and lemmas for the UBSan proof of pin_mid_contract (U/Prog/LLVMFuzzerTestOneInput_c.v):
    the footprint, the memory facts carried along the walk, image facts (the catalogue table, the stack-protector
    GOT slot and guard), byte and cell lemmas, and the list facts of the harness's scan. No step of the program. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c reac_box_pin_parse_c
  LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The footprint and the carried memory facts *)
Definition mid_fp (sp : word) (phi K : Z) : list ivl :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp + MID_OUT); (phi, phi + K + 1)].

Definition cat_ok (m : word -> option byte) : Prop :=
  forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).

(** What every memory of the walk keeps against the start memory m0. *)
Definition minv (sp : word) (phi K lo : Z) (can : word) (m0 m : word -> option byte) : Prop :=
  munch (mid_fp sp phi K) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp) /\
  cat_ok m /\ bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  bytes_at rsegs m PARSE_SSP_GUARD (le8 can) /\ wr_at rsegs m (bv_unsigned sp + 8) 16.

(** An address the image maps lies outside the footprint (both of its pieces map nothing). *)
Definition rom_out (sp : word) (phi K : Z) : Prop :=
  forall a, 0 <= a < 2^64 -> seg_rom rsegs (wa a) <> None -> outside (mid_fp sp phi K) a.

(** pin_mid_contract's post, with the length of s as K. *)
Definition Qpost (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (phi K lo : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 PIN_JOIN) fc None m' (seg_rom rsegs) /\
    munch (mid_fp sp phi K) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

(** ** Image facts *)
Lemma image_bytes_some : forall segs n A bs, image_bytes segs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs. induction n as [|n IH]; intros A bs H i Hi; [lia|].
  cbn [image_bytes] in H.
  destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-.
  destruct i as [|i].
  - cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E2 i) by lia. f_equal. unfold wa. f_equal. lia.
Qed.

Lemma image_bytes_rom : forall segs A n bs, image_bytes segs A n = Some bs ->
  forall a, A <= a < A + Z.of_nat n -> seg_rom segs (wa a) <> None.
Proof.
  intros segs A n bs H a Ha. pose proof (image_bytes_length segs n A bs H) as Hl.
  replace a with (A + Z.of_nat (Z.to_nat (a - A))) by lia.
  rewrite (image_bytes_some segs n A bs H) by lia.
  intros E. apply nth_error_None in E. lia.
Qed.

Lemma image_bytes_at : forall m A n bs, image_bytes rsegs A n = Some bs ->
  (forall a, A <= a < A + Z.of_nat n -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  0 <= A -> A + Z.of_nat n <= 2^64 -> bytes_at rsegs m A bs.
Proof.
  intros m A n bs H Hm HA HB. pose proof (image_bytes_length rsegs n A bs H) as Hl.
  split; [lia|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite Hm by lia. apply (image_bytes_some rsegs n A bs H). lia.
Qed.

Lemma cat_rom : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha.
  assert (E : match image_bytes rsegs FUZZ_CATALOGUE 3256 with Some _ => true | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (image_bytes rsegs FUZZ_CATALOGUE 3256) as [bs|] eqn:Eb; [|discriminate].
  apply (image_bytes_rom rsegs FUZZ_CATALOGUE 3256 bs Eb).
  change (Z.of_nat 3256) with 3256. unfold CAT_BYTES in Ha. lia.
Qed.

Lemma got_rom : forall a, PARSE_SSP_GOT <= a < PARSE_SSP_GOT + 8 -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha.
  assert (E : match image_bytes rsegs PARSE_SSP_GOT 8 with Some _ => true | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (image_bytes rsegs PARSE_SSP_GOT 8) as [bs|] eqn:Eb; [|discriminate].
  apply (image_bytes_rom rsegs PARSE_SSP_GOT 8 bs Eb). change (Z.of_nat 8) with 8. lia.
Qed.

Lemma guard_rom : forall a, PARSE_SSP_GUARD <= a < PARSE_SSP_GUARD + 8 -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha.
  assert (E : match image_bytes rsegs PARSE_SSP_GUARD 8 with Some _ => true | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (image_bytes rsegs PARSE_SSP_GUARD 8) as [bs|] eqn:Eb; [|discriminate].
  apply (image_bytes_rom rsegs PARSE_SSP_GUARD 8 bs Eb). change (Z.of_nat 8) with 8. lia.
Qed.

(** Row i's display pointer, at +8 of the row, read from the image. *)
Lemma disp_img : forall i, (i < CAT_N)%nat ->
  image_bytes rsegs (row_addr FUZZ_CATALOGUE i + 8) 8 = Some (le8 (Z_to_bv 64 (disp_ptr i))).
Proof.
  intros i Hi.
  assert (H : all_rows (fun i => match image_bytes rsegs (row_addr FUZZ_CATALOGUE i + 8) 8 with
                                 | Some bs => bytes_eqb bs (le8 (Z_to_bv 64 (disp_ptr i)))
                                 | None => false
                                 end) = true) by (vm_compute; reflexivity).
  pose proof (all_rows_spec _ H i Hi) as Hj. cbn beta in Hj.
  destruct (image_bytes rsegs (row_addr FUZZ_CATALOGUE i + 8) 8) as [bs|]; [|discriminate].
  apply bytes_eqb_eq in Hj. subst bs. reflexivity.
Qed.

(** ** Bytes and cells *)
Lemma bytes_at_read_all : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r, firstn_all in E. exact E.
Qed.

Lemma bytes_at_read8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof. intros m a v H. pose proof (bytes_at_read_all m a (le8 v) H) as E. rewrite length_le8 in E. exact E. Qed.

Lemma firstn1_skipn : forall (bs : list byte) k, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs NUL].
Proof.
  induction bs as [|x bs IH]; intros [|k] Hk; cbn [length] in Hk; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bytes_at_nth : forall m a bs (k : nat), bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs NUL].
Proof.
  intros m a bs k H Hk. rewrite (bytes_at_ov_read rsegs m a bs k 1 H) by lia. f_equal. apply firstn1_skipn. exact Hk.
Qed.

Lemma bytes_at_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof. intros m a bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma bytes_at_munch_out : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall i, (i < length bs)%nat -> outside W (a + Z.of_nat i)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) MU HO. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite MU; [exact (H i Hi)|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma wr_at_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (H1 & H2 & H) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(** The last byte of a block, split off. *)
Lemma rw_cells_CB_last : forall m A k junk, rw_cells rsegs m A [CB (S k) junk] ->
  rw_cells rsegs m A [CB k (firstn k junk)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB 1 (skipn k junk)].
Proof.
  intros m A k junk [[Hwf Hb] (Ha & Hl & Hw)]. cbn in Hwf. destruct Hwf as [Hlen _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn k junk) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  cbn [cells_size csize] in Hl, Hw.
  rewrite firstn_length_le in B2 by lia.
  split.
  - split; [split|].
    + cbn. split; [rewrite firstn_length_le by lia; reflexivity | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split|].
    + cbn. split; [rewrite length_skipn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

(** ** The carried facts through a step of memory *)
Lemma rom_out_of : forall (sp : word) phi K lo,
  (forall a, lo <= a < bv_unsigned sp + MID_OUT -> seg_rom rsegs (wa a) = None) ->
  (forall a, phi <= a < phi + K + 1 -> seg_rom rsegs (wa a) = None) ->
  lo + MID_STACK <= bv_unsigned sp -> rom_out sp phi K.
Proof.
  intros sp phi K lo SN RN LO a Ha Hr. unfold mid_fp. cbn [outside].
  split; [|split; [|exact I]]; intros Hin; apply Hr; [apply SN | apply RN]; unfold MID_STACK, MID_OUT in *; lia.
Qed.

Lemma minv_trans : forall sp phi K lo can m0 m1 m2, rom_out sp phi K -> minv sp phi K lo can m0 m1 ->
  munch (mid_fp sp phi K) m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp) ->
  minv sp phi K lo can m0 m2.
Proof.
  intros sp phi K lo can m0 m1 m2 RO (MU & WM & _ & _ & CA & GO & GU & WR) MU2 WM2 MI2 ST2.
  split; [exact (munch_trans _ _ _ _ MU MU2)|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|].
  split; [|split; [|split]].
  - intros a Ha. rewrite <- (CA a Ha). unfold mrd. rewrite MU2; [reflexivity|].
    unfold FUZZ_CATALOGUE, CAT_BYTES in Ha. rewrite wa_unsigned by lia.
    apply RO; [lia|]. apply cat_rom. unfold FUZZ_CATALOGUE, CAT_BYTES. lia.
  - apply (bytes_at_munch_out _ m1 m2 _ _ GO MU2). intros i Hi. rewrite length_le8 in Hi.
    apply RO; [unfold PARSE_SSP_GOT; lia|]. apply got_rom. lia.
  - apply (bytes_at_munch_out _ m1 m2 _ _ GU MU2). intros i Hi. rewrite length_le8 in Hi.
    apply RO; [unfold PARSE_SSP_GUARD; lia|]. apply guard_rom. lia.
  - exact (wr_at_transport rsegs _ _ _ _ WR WM2).
Qed.

Lemma minv_store : forall sp phi K lo can m0 m a bs, rom_out sp phi K -> minv sp phi K lo can m0 m ->
  inside (mid_fp sp phi K) a (Z.of_nat (length bs)) -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  store_ok rsegs m (wa a) (length bs) = true -> minv sp phi K lo can m0 (write_to_mem m (wa a) bs).
Proof.
  intros sp phi K lo can m0 m a bs RO HM Hin Ha Hl Hok.
  pose proof HM as (_ & _ & MI & ST & _).
  apply (minv_trans sp phi K lo can m0 m); [exact RO | exact HM | | | |].
  - apply munch_write; [apply munch_refl | exact Ha | exact Hl | exact Hin].
  - apply wmono_write. apply wmono_refl.
  - apply mem_inv_store; assumption.
  - apply stk_write; assumption.
Qed.

Lemma minv_call : forall sp phi K lo can m0 m1 m2 W, rom_out sp phi K -> minv sp phi K lo can m0 m1 ->
  munch W m1 m2 -> sub_fp W (mid_fp sp phi K) -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo (bv_unsigned sp) -> minv sp phi K lo can m0 m2.
Proof.
  intros sp phi K lo can m0 m1 m2 W RO HM MU HS WM MI ST.
  apply (minv_trans sp phi K lo can m0 m1); try assumption. eapply munch_weaken; eassumption.
Qed.

Lemma minv_cat : forall sp phi K lo can m0 m, minv sp phi K lo can m0 m -> cat_ok m.
Proof. intros sp phi K lo can m0 m (_ & _ & _ & _ & H & _). exact H. Qed.

(** Row i's display pointer, read through a memory that agrees with the image on the table. *)
Lemma disp_read : forall m i, cat_ok m -> (i < CAT_N)%nat ->
  ov_read_bytes rsegs m (wa (row_addr FUZZ_CATALOGUE i + 8)) 8 = Some (le8 (Z_to_bv 64 (disp_ptr i))).
Proof.
  intros m i HC Hi.
  apply bytes_at_read8.
  apply (image_bytes_at m _ 8 _ (disp_img i Hi)).
  - intros a Ha. apply HC. change (Z.of_nat 8) with 8 in Ha.
    unfold row_addr, CAT_ROW, CAT_BYTES, FUZZ_CATALOGUE, CAT_N in *. lia.
  - unfold row_addr, CAT_ROW, FUZZ_CATALOGUE. lia.
  - change (Z.of_nat 8) with 8. unfold row_addr, CAT_ROW, FUZZ_CATALOGUE, CAT_N in *. lia.
Qed.

(** ** The scan and the expectation *)
Lemma colon_idx_eq : forall s tok, (tok <= length s)%nat ->
  (forall j, (j < tok)%nat -> bv_unsigned (nth j s NUL) <> COLON) ->
  (tok = length s \/ bv_unsigned (nth tok s NUL) = COLON) -> colon_idx s = tok.
Proof.
  induction s as [|x s IH]; intros tok Hle Hb He; cbn [length] in *.
  - cbn. lia.
  - cbn [colon_idx]. destruct tok as [|tok].
    + destruct He as [He|He]; [lia|]. cbn [nth] in He. rewrite He, Z.eqb_refl. reflexivity.
    + assert (Hx : bv_unsigned x <> COLON) by exact (Hb 0%nat ltac:(lia)).
      apply Z.eqb_neq in Hx. rewrite Hx. f_equal. apply IH; [lia | |].
      * intros j Hj. exact (Hb (S j) ltac:(lia)).
      * destruct He as [He|He]; [left; lia | right; exact He].
Qed.

Lemma nth_app_slack : forall s slack j, (j <= length s)%nat ->
  nth j (s ++ NUL :: slack) NUL = nth j (s ++ [NUL]) NUL.
Proof.
  intros s slack j Hj. destruct (Nat.lt_ge_cases j (length s)) as [Hlt|Hge].
  - rewrite !app_nth1 by exact Hlt. reflexivity.
  - rewrite !app_nth2 by exact Hge. replace (j - length s)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma want_flags : forall cat spec fl s, Z.land fl 7 <> 0 -> want_ptr cat fl s = 0 /\ want_label spec fl s = 0.
Proof.
  intros cat spec fl s H. unfold want_ptr, want_label, harness_want. apply Z.eqb_neq in H. rewrite H.
  cbn [andb]. split; reflexivity.
Qed.

Lemma want_len0 : forall cat spec fl s, length s = 0%nat -> want_ptr cat fl s = 0 /\ want_label spec fl s = 0.
Proof.
  intros cat spec fl s H. unfold want_ptr, want_label, harness_want. rewrite H. cbn [Nat.eqb negb].
  rewrite andb_false_r. split; reflexivity.
Qed.

Lemma want_row : forall fl s, Z.land fl 7 = 0 -> length s <> 0%nat ->
  harness_want fl s = row_of (firstn (colon_idx s) s).
Proof.
  intros fl s H H0. unfold harness_want. rewrite H. apply Nat.eqb_neq in H0. rewrite H0. reflexivity.
Qed.

Lemma want_none : forall cat spec fl s, Z.land fl 7 = 0 -> length s <> 0%nat ->
  row_of (firstn (colon_idx s) s) = None -> want_ptr cat fl s = 0 /\ want_label spec fl s = 0.
Proof.
  intros cat spec fl s H H0 Hr. unfold want_ptr, want_label. rewrite (want_row fl s H H0), Hr.
  split; reflexivity.
Qed.

Lemma want_some : forall cat spec fl s i, Z.land fl 7 = 0 -> length s <> 0%nat ->
  row_of (firstn (colon_idx s) s) = Some i ->
  want_ptr cat fl s = row_addr cat i /\
  want_label spec fl s = match harness_label_off s with Some k => spec + Z.of_nat k | None => disp_ptr i end.
Proof.
  intros cat spec fl s i H H0 Hr. unfold want_ptr, want_label. rewrite (want_row fl s H H0), Hr.
  split; reflexivity.
Qed.

(** want_label's test when the scan ran to the end, and when it stopped on a ':'. *)
Lemma label_off_end : forall s, colon_idx s = length s -> harness_label_off s = None.
Proof.
  intros s H. unfold harness_label_off. rewrite H, Nat.ltb_irrefl. reflexivity.
Qed.

Lemma label_off_colon : forall s, (colon_idx s < length s)%nat ->
  harness_label_off s =
  if bv_unsigned (nth (S (colon_idx s)) (s ++ [NUL]) NUL) =? 0 then None else Some (S (colon_idx s)).
Proof.
  intros s H. unfold harness_label_off. apply Nat.ltb_lt in H. rewrite H. cbn [andb].
  destruct (bv_unsigned (nth (S (colon_idx s)) (s ++ [NUL]) NUL) =? 0); reflexivity.
Qed.

Lemma row_of_lt : forall t i, row_of t = Some i -> (i < CAT_N)%nat.
Proof. intros t i H. exact (proj1 (row_of_some t i H)). Qed.

Lemma cat_mod8 : FUZZ_CATALOGUE mod 8 = 0.
Proof. reflexivity. Qed.

(** ** The flags and reac_box_pin_parse's arguments *)
Lemma flag_bits : forall fl, 0 <= fl < 256 ->
  Z.land fl 1 = Z.b2z (Z.testbit fl 0) /\
  Z.shiftr (Z.shiftl fl 62 mod 18446744073709551616) 63 = Z.b2z (Z.testbit fl 1) /\
  Z.shiftr (Z.shiftl fl 61 mod 18446744073709551616) 63 = Z.b2z (Z.testbit fl 2).
Proof.
  intros fl Hfl.
  assert (H : forallb (fun z => (Z.land z 1 =? Z.b2z (Z.testbit z 0)) &&
                               (Z.shiftr (Z.shiftl z 62 mod 18446744073709551616) 63 =? Z.b2z (Z.testbit z 1)) &&
                               (Z.shiftr (Z.shiftl z 61 mod 18446744073709551616) 63 =? Z.b2z (Z.testbit z 2)))
                      (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H fl ltac:(apply in_map_iff; exists (Z.to_nat fl); split; [lia | apply in_seq; lia])).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H2, H3. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma mask_sel : forall (b : bool) x, 0 <= x < 2^64 ->
  Z.land ((Z.b2z b + -1) mod 18446744073709551616) x = if b then 0 else x.
Proof.
  intros [|] x Hx; cbn [Z.b2z].
  - reflexivity.
  - change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
Qed.

Lemma unsigned_ite : forall (b : bool) x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 (if b then 0 else x)) = if b then 0 else x.
Proof. intros [|] x Hx; apply unsigned_lit; lia. Qed.

Lemma parse_live_fl : forall fl phi spv, 0 < phi < 2^64 -> 0 <= spv -> spv + 24 <= 2^64 ->
  parse_live (Z_to_bv 64 (if Z.testbit fl 0 then 0 else phi)) (Z_to_bv 64 (if Z.testbit fl 1 then 0 else spv + 16))
             (Z_to_bv 64 (if Z.testbit fl 2 then 0 else spv + 8)) = fl_live fl.
Proof.
  intros fl phi spv Hp Hs Hs'. unfold parse_live, fl_live. rewrite !unsigned_ite by lia.
  assert (E1 : (phi =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (E2 : (spv + 16 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (E3 : (spv + 8 =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); rewrite ?E1, ?E2, ?E3; reflexivity.
Qed.

Lemma parse_out_fl : forall cat fl phi s,
  parse_out cat (if Z.testbit fl 0 then 0 else phi) (fl_live fl) s = parse_out cat phi (fl_live fl) s.
Proof. intros cat fl phi s. unfold fl_live. destruct (Z.testbit fl 0); reflexivity. Qed.

Lemma fl_live_bits : forall fl, fl_live fl = true ->
  Z.testbit fl 0 = false /\ Z.testbit fl 1 = false /\ Z.testbit fl 2 = false.
Proof.
  intros fl H. unfold fl_live in H.
  destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); cbn in H; try discriminate; auto.
Qed.

Lemma parse_some_live : forall cat spec l s r, parse_out cat spec l s = Some r -> l = true.
Proof. intros cat spec [|] s r H; [reflexivity | discriminate]. Qed.

Lemma want_ptr_range : forall fl s, 0 <= want_ptr FUZZ_CATALOGUE fl s < 2^64.
Proof.
  intros fl s. unfold want_ptr. destruct (harness_want fl s) as [i|] eqn:E; [|lia].
  unfold harness_want in E. destruct (_ && _); [|discriminate].
  apply row_of_some in E. destruct E as [Hi _]. unfold row_addr, CAT_ROW, FUZZ_CATALOGUE, CAT_N in *. lia.
Qed.

Lemma rc_iff : forall fl s phi, 0 <= fl < 256 -> ~ In NUL s ->
  (bv_unsigned (Z_to_bv 64 (parse_rc (parse_out FUZZ_CATALOGUE phi (fl_live fl) s))) = 0 <->
   want_ptr FUZZ_CATALOGUE fl s <> 0).
Proof.
  intros fl s phi Hfl Hs.
  pose proof (harness_known FUZZ_CATALOGUE phi fl s ltac:(unfold FUZZ_CATALOGUE; lia) Hfl Hs) as HKn.
  destruct (parse_out FUZZ_CATALOGUE phi (fl_live fl) s) as [r|]; cbn [parse_rc] in *.
  - rewrite unsigned_lit by lia. split; intros _; [apply HKn; reflexivity | reflexivity].
  - rewrite unsigned_lit_wrap. split; intros Hc.
    + exfalso. change ((-1) mod 2^64) with 18446744073709551615 in Hc. lia.
    + exfalso. apply HKn in Hc. lia.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** The end of the walk: pin_mid_contract's post. *)
Ltac qfin := apply evt_done; unfold Qpost; do 22 eexists; split; [reflexivity|];
  split; [assumption|]; split; [assumption|]; split; assumption.

Lemma wr_store_ok : forall m a n b (j : nat), wr_at rsegs m a n -> a <= b -> b - a + Z.of_nat j <= n ->
  store_ok rsegs m (wa b) j = true.
Proof.
  intros m a n b j H Hab Hj. replace b with (a + (b - a)) by lia.
  apply (wr_at_store_ok rsegs m a n); [exact H | lia | lia].
Qed.

(** A store into the harness's frame cells keeps the carried facts and the spec string. *)
Lemma stack_store : forall sp phi K lo can m0 m (str : list byte) a bs, rom_out sp phi K ->
  minv sp phi K lo can m0 m -> bytes_at rsegs m phi str ->
  0 <= bv_unsigned sp - MID_STACK -> bv_unsigned sp - MID_STACK <= a ->
  a + Z.of_nat (length bs) <= bv_unsigned sp + MID_OUT ->
  (phi + Z.of_nat (length str) <= bv_unsigned sp - MID_STACK \/ bv_unsigned sp + MID_OUT <= phi) ->
  store_ok rsegs m (wa a) (length bs) = true ->
  minv sp phi K lo can m0 (write_to_mem m (wa a) bs) /\ bytes_at rsegs (write_to_mem m (wa a) bs) phi str.
Proof.
  intros sp phi K lo can m0 m str a bs RO HM HS H0 H1 H2 HD Hok.
  pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (_ & Hw & _)).
  unfold MID_STACK, MID_OUT in *.
  split.
  - apply minv_store; try assumption; [| lia | lia]. unfold mid_fp, MID_STACK, MID_OUT. cbn [inside]. left. lia.
  - apply bytes_at_write_other; [exact HS | lia | lia | lia].
Qed.

Ltac fp_tac := unfold sub_fp; intros ?x ?Hx;
  unfold mid_fp, MID_STACK, MID_OUT, PARSE_STACK, FCR_STACK in *; cbn [outside] in *;
  repeat split; try exact I; lia.
