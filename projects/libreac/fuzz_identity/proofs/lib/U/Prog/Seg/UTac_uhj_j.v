From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import RcIdentModel reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma sj_vm_vm : forall a b m, with_vmmaps a (with_vmmaps b m) = with_vmmaps a m.
Proof. intros a b m. reflexivity. Qed.

Lemma sj_fds_vm : forall a m, m_fds (with_vmmaps a m) = m_fds m.
Proof. intros a m. reflexivity. Qed.

Lemma sj_pairwise_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros T R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|exact (IH H2)].
    intros y Hy. apply H1. apply (Permutation_in y (Permutation_sym HP) Hy).
  - destruct H as [Hy [Hx Hl]]. split.
    + intros z [<-|Hz]; [apply Hs, Hy; left; reflexivity | exact (Hx z Hz)].
    + split; [intros z Hz; apply Hy; right; exact Hz | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.

Lemma sj_disj_head : forall x l y, pairwise ranges_disjoint (x :: l) -> In y l -> ranges_disjoint x y.
Proof. intros x l y [H _] Hy. exact (H y Hy). Qed.

Lemma sj_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

Lemma sj_in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma sj_blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

Lemma sj_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact unsigned_lit. Qed.

Lemma sj_bv_neq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof.
  intros a b Ha Hb Hn E. apply (f_equal bv_unsigned) in E. rewrite !sj_unsigned in E by assumption. lia.
Qed.

Lemma sj_bv_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof. intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !sj_unsigned in E by assumption. exact E. Qed.

Lemma sj_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zmod_mod. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia | rewrite kb_mod2_land; exact Hz].
Qed.

Lemma sj_bytes_le8 : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (wa a) 8 = Some (le8 v).
Proof.
  intros segs m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma sj_bytes_le4 : forall segs m a v, bytes_at segs m a (le4 v) -> ov_read_bytes segs m (wa a) 4 = Some (le4 v).
Proof.
  intros segs m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read segs m a (le4 v) 0 4 H) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma sj_sx32 : forall I, -2 ^ 31 <= I < 2 ^ 31 -> sx32 (Z_to_bv 64 I) = Z_to_bv 64 I.
Proof.
  intros I HI. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sj_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

Lemma sj_remu : forall a b, 0 <= a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  mul_div Instr.M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small b) by lia.
  rewrite (Z.mod_small (a mod b)); [reflexivity|]. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

Lemma sj_beqb_refl : forall l, bytes_eqb l l = true.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl, IH. reflexivity. Qed.

Lemma sj_beq_dec : forall x y : list byte, bool_decide (x = y) = bytes_eqb x y.
Proof.
  intros x y. destruct (bytes_eqb x y) eqn:E.
  - apply bytes_eqb_eq in E. subst. apply bool_decide_true. reflexivity.
  - apply bool_decide_false. intros ->. rewrite sj_beqb_refl in E. discriminate.
Qed.

Lemma sj_cat_e_pos : forall inp, CAT <= cat_e inp < CAT + CAT_ROW * CAT_N.
Proof.
  intros inp. unfold cat_e, CAT, CAT_ROW, CAT_N. pose proof (Z.mod_pos_bound (t_row inp) 11 ltac:(lia)). lia.
Qed.

Lemma sj_mask_eq : forall inp dp I O P sP, dp <> 0 -> cat_mask inp dp I O P sP = exp_mask inp I O P sP.
Proof.
  intros inp dp I O P sP Hd. unfold cat_mask, exp_mask, CATALOGUE_DEFECT_MASK.
  pose proof (sj_cat_e_pos inp) as He. unfold CAT in He.
  replace (cat_e inp =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (dp =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
  rewrite sj_beq_dec. cbn [orb]. destruct (P =? 0); reflexivity.
Qed.

Lemma sj_sltu_or : forall x9 x w, x9 = Z_to_bv 64 w -> 0 <= w <= 1 ->
  Z_to_bv 64 (Z.lor (bv_unsigned x9) (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (PropExec.v_sltu (Z_to_bv 64 0) x)) 1)))) =
  Z_to_bv 64 (w + (if bv_eqb x (Z_to_bv 64 0) then 0 else 2)).
Proof.
  intros x9 x w -> Hw. unfold PropExec.v_sltu, PropExec.c_ltu, bv_ltu, bv_eqb.
  rewrite (unsigned_lit w) by lia. rewrite (unsigned_lit 0) by lia.
  pose proof (bv_unsigned_in_range 64 x) as Hx. change (bv_modulus 64) with (2 ^ 64) in Hx.
  assert (Hw' : w = 0 \/ w = 1) by lia.
  destruct (Z.ltb_spec 0 (bv_unsigned x)) as [L|L]; destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; try lia.
  - cbv beta iota. rewrite (unsigned_lit 1) by lia. change (Z.shiftl 1 1) with 2. rewrite (unsigned_lit 2) by lia.
    destruct Hw' as [-> | ->]; reflexivity.
  - cbv beta iota. rewrite (unsigned_lit 0) by lia. rewrite Z.shiftl_0_l. rewrite (unsigned_lit 0) by lia.
    destruct Hw' as [-> | ->]; reflexivity.
Qed.

Definition NZ (l : list byte) : Prop := forall b, In b l -> bz b <> 0.

Lemma NZ_app : forall l1 l2, NZ l1 -> NZ l2 -> NZ (l1 ++ l2).
Proof. intros l1 l2 H1 H2 b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (H1 b Hb) | exact (H2 b Hb)]. Qed.

Lemma NZ_b : forall l, forallb (fun b => negb (bz b =? 0)) l = true -> NZ l.
Proof.
  intros l H b Hb. rewrite forallb_forall in H. specialize (H b Hb). apply negb_true_iff in H.
  apply Z.eqb_neq in H. exact H.
Qed.

Lemma NZ_notin : forall l, NZ l -> ~ In z8 l.
Proof. intros l H Hin. apply (H z8 Hin). reflexivity. Qed.

Lemma NZ_dg : forall y, NZ [dg (y mod 10)].
Proof.
  intros y b [<-|[]]. unfold dg, bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. pose proof (Z.mod_pos_bound y 10 ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma NZ_dec_digits : forall n x, NZ (dec_digits n x).
Proof.
  induction n as [|n IH]; intros x; cbn [dec_digits]; [intros b []|].
  apply NZ_app; [|apply NZ_dg]. destruct (x <? 10); [intros b []| apply IH].
Qed.

Lemma NZ_repeat0 : forall k, NZ (repeat (dg 0) k).
Proof.
  intros k b Hb. apply repeat_spec in Hb. subst b. exact (NZ_dg 0 (dg (0 mod 10)) (or_introl eq_refl)).
Qed.

Lemma NZ_DEC : forall x m, NZ (DEC x m).
Proof. intros x m. unfold DEC. apply NZ_app; [apply NZ_repeat0 | apply NZ_dec_digits]. Qed.

Lemma NZ_firstn_fz : forall l, NZ (firstn (first_zero l) l).
Proof.
  induction l as [|x l IH]; cbn [first_zero]; [intros b Hb; destruct Hb|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [intros b []|].
  cbn [firstn]. intros b [<-|Hb]; [exact E | exact (IH b Hb)].
Qed.

Lemma NZ_stem_img : forall f, NZ (stem_img f).
Proof.
  intros f. apply NZ_b. unfold stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma NZ_EXP_DP : forall inp, ~ In z8 (n_EXP_DP inp).
Proof.
  intros inp. apply NZ_notin. unfold n_EXP_DP.
  assert (HS : NZ (n_stem inp)).
  { unfold n_stem. destruct (n_use_said inp); [unfold name_str; apply NZ_firstn_fz | apply NZ_stem_img]. }
  assert (HN : NZ (n_EXP_NM inp)).
  { unfold n_EXP_NM. destruct (n_ends_w4 inp); [exact HS|].
    apply NZ_app; [exact HS|]. apply NZ_app; [apply NZ_b; vm_compute; reflexivity|].
    unfold n_W4. apply NZ_app; apply NZ_DEC. }
  apply NZ_app; [exact HN|]. apply NZ_app; [apply NZ_b; vm_compute; reflexivity|].
  apply NZ_app; [apply NZ_DEC|]. apply NZ_app; [apply NZ_b; vm_compute; reflexivity|].
  apply NZ_app; [apply NZ_DEC|]. apply NZ_b; vm_compute; reflexivity.
Qed.

Lemma sj_tok_len : forall d l, (length (tok_go d l) <= length l)%nat.
Proof.
  intros d l. revert d. induction l as [|x l IH]; intros d; cbn [tok_go length]; [lia|].
  destruct (negb d && (bz x =? 45)); cbn [length]; [specialize (IH true) | specialize (IH d)]; lia.
Qed.

Lemma sj_r0_lens : forall inp, n_r inp = 0 ->
  n_ln inp < 40 /\ zlen (n_TK inp) < 40 /\ n_ld inp < 64 /\ n_wok inp = true /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. unfold n_fits in E2. apply andb_prop in E2 as [E2 E5].
  apply andb_prop in E2 as [E3 E4]. apply Z.ltb_lt in E3, E4, E5.
  pose proof (Z.mod_pos_bound (tb inp 5) 40 ltac:(lia)). pose proof (Z.mod_pos_bound (tb inp 7) 64 ltac:(lia)).
  unfold t_cap_name, t_cap_disp in *. unfold zlen, n_TK, TOK. pose proof (sj_tok_len false (n_EXP_NM inp)).
  unfold n_ln in *. repeat split; try lia. exact E1.
Qed.

Definition in_relro_b (a : Z) : bool :=
  ((0x1e3c8 <=? a) && (a <? 0x1e3c8 + 3440)) || ((0x1f140 <=? a) && (a <? 0x1f140 + 16)).

Lemma in_relro_sound : forall a, in_relro_b a = true -> in_globals frame_RELRO a.
Proof.
  intros a H. unfold in_relro_b in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2.
  - exists 0x1e3c8, 3440. split; [left; reflexivity | lia].
  - exists 0x1f140, 16. split; [right; left; reflexivity | lia].
Qed.

Definition bopt_eqb (o : option byte) (b : byte) : bool := match o with Some x => bz x =? bz b | None => false end.

Definition relro_b (a : Z) (bs : list byte) : bool :=
  (0 <=? a) && (a + Z.of_nat (length bs) <=? 2 ^ 64) &&
  forallb (fun i => in_relro_b (a + Z.of_nat i) && bopt_eqb (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) (nth i bs z8))
    (seq 0 (length bs)).

Definition rbyte (a : Z) : byte := match seg_rom rsegs (Z_to_bv 64 a) with Some b => b | None => z8 end.
Definition rword (a : Z) (n : nat) : Z := fold_right (fun i acc => bz (rbyte (a + Z.of_nat i)) + 256 * acc) 0 (seq 0 n).
Fixpoint rstr (a : Z) (fuel : nat) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom rsegs (Z_to_bv 64 a) with
           | Some b => if bz b =? 0 then [] else b :: rstr (a + 1) f
           | None => []
           end
  end.

Definition cat_row (r : Z) : Z := CAT + CAT_ROW * r.
Definition catI (r : Z) : Z := rword (cat_row r + 16) 4.
Definition catO (r : Z) : Z := rword (cat_row r + 20) 4.
Definition catP (r : Z) : Z := rword (cat_row r + 8) 8.
Definition catS (r : Z) : list byte := rstr (catP r) 64.

Definition cat_check (r : Z) : bool :=
  (-2 ^ 31 <=? catI r) && (catI r <? 2 ^ 31) && (-2 ^ 31 <=? catO r) && (catO r <? 2 ^ 31) &&
  (0 <=? catP r) && (catP r <? 2 ^ 64) &&
  relro_b (cat_row r + 8) (le8 (Z_to_bv 64 (catP r))) && relro_b (cat_row r + 16) (le4 (Z_to_bv 64 (catI r))) &&
  relro_b (cat_row r + 20) (le4 (Z_to_bv 64 (catO r))) &&
  ((catP r =? 0) || (ro_bytes_b rsegs (catP r) (catS r ++ [z8]) && forallb (fun b => negb (bz b =? 0)) (catS r) &&
                      (catP r + Z.of_nat (length (catS r)) + 1 <=? 2 ^ 40))).

Lemma cat_check_all : forall r, 0 <= r < 11 -> cat_check r = true.
Proof.
  intros r Hr.
  assert (E : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma sj2_outside1 : forall lo hi x, outside [(lo, hi)] x <-> ~ (lo <= x < hi).
Proof. intros lo hi x. cbn. tauto. Qed.

Lemma sj2_munch_widen : forall lo hi lo' hi' m m',
  munch [(lo, hi)] m m' -> lo' <= lo -> hi <= hi' -> munch [(lo', hi')] m m'.
Proof.
  intros lo hi lo' hi' m m' H H1 H2 x Hx. apply H. apply sj2_outside1.
  apply sj2_outside1 in Hx. lia.
Qed.

Lemma sj2_munch_nil : forall W m m', munch [] m m' -> munch W m m'.
Proof. intros W m m' H x _. apply H. exact I. Qed.

Lemma sj2_munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma sj2_mbyte_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma sj2_wr_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.

Lemma sj2_ba_keep : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd, wa. rewrite (Hk (Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma sj2_ba_munch : forall segs W m m' a bs, bytes_at segs m a bs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> outside W (a + i)) -> bytes_at segs m' a bs.
Proof.
  intros segs W m m' a bs H HM HO. pose proof (bytes_at_bound segs m a bs H) as HB.
  apply (sj2_ba_keep segs m); [exact H|]. intros i Hi. apply HM.
  rewrite MState.unsigned_lit by lia. apply HO. exact Hi.
Qed.

Lemma sj2_img_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Hra Ha Hl Hb. pose proof (ro_bytes_b_sound rsegs bs a Hb) as H.
  split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b H E) as [H1 H2]. rewrite (Hra _ H2). exact H1.
Qed.

Lemma sj2_ovr : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. cbn [skipn] in E. rewrite firstn_all in E. exact E.
Qed.

Lemma sj2_le8_len : forall v : word, length (le8 v) = 8%nat.
Proof. intros v. apply length_le8. Qed.

Lemma sj2_q64_ovr : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (sj2_ovr m a _ H) as E. rewrite sj2_le8_len in E. exact E. Qed.

Section TacSJ.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Local Abbreviation API := (APIf rc).
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR (APIf rc)).

Lemma sj_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma sj_ra : ra mod 2 = 0.
Proof. exact (proj1 (proj2 FF)). Qed.

Lemma sj_free : ms_free B = 0x15974.
Proof. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma sj_errno_ceil : errno_addr B + 4 <= alloc_ceiling.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc). Qed.

Lemma sj_errno : errno_addr B = 0x3040c.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _).
  unfold errno_addr. rewrite H1, H2. reflexivity.
Qed.

Lemma sj_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & H & _). exact H.
Qed.

Lemma sj_alloc : frame_allocator B API.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma sj_ax : AllocExtra B MR.
Proof. destruct sj_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma sj_relro_unowned : forall L A mem md a, MR L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Proof. destruct sj_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma sj_img_low : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite sj_segs. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma sj_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof. intros L A mem md H. exact (kb_md B API L A mem md H). Qed.

Lemma cut_open : forall g pc km hb P c (Q : config -> Prop),
  CUTST B APIf ra empty g pc km hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     Rz segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) Q) ->
  Rz segs c Q.
Proof.
  intros g pc km hb P c Q (L & A & regs & mem & md & -> & H1 & H2 & H3) K. exact (K L A regs mem md H1 H2 H3).
Qed.

Lemma cut_close : forall g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
  CUTST B APIf ra empty g pc km hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md).
Proof.
  intros g pc km hb P L A regs mem md H1 H2 H3. exists L, A, regs, mem, md. split; [reflexivity|].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma FR_regs : forall g km hb L A regs regs' mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof.
  intros g km hb L A regs regs' mem md (H0 & H2 & H3 & H4 & HR) E2 E3 E4.
  split; [exact H0|]. rewrite E2, E3, E4. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact HR].
Qed.

Lemma FR_MR : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md -> MR L A mem md.
Proof. intros g km hb L A regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma run_to : forall g km hb L A regs mem md pc R' pc' mem' (Q : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Exec.evt rsegs (fun ms => ms = MS R' fp_regs pc' fp_csr None mem' (seg_rom rsegs))
    (MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall regs', (forall r, getr regs' r = getr R' r) -> Rz segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) Q) ->
  Rz segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb L A regs mem md pc R' pc' mem' Q HF HE HK.
  destruct (sj_md L A mem md (FR_MR _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  apply (kb_run_rz B regs pc mem md (fun R p m => R = R' /\ p = pc' /\ m = mem') Q Hh Hl).
  - rewrite sj_segs. eapply Exec.evt_mono; [exact HE|]. intros ms ->. exists R', pc', mem'.
    split; [reflexivity | repeat split].
  - intros R p m regs' (-> & -> & ->) HG. exact (HK regs' HG).
Qed.

Lemma run_ex : forall g km hb L A regs mem md pc (Rf : word -> bvmap 5 word) pc' mem' (Q : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Exec.evt rsegs (fun ms => exists y, ms = MS (Rf y) fp_regs pc' fp_csr None mem' (seg_rom rsegs))
    (MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall y regs', (forall r, getr regs' r = getr (Rf y) r) ->
     Rz segs (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) Q) ->
  Rz segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb L A regs mem md pc Rf pc' mem' Q HF HE HK.
  destruct (sj_md L A mem md (FR_MR _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  apply (kb_run_rz B regs pc mem md (fun R p m => (exists y, R = Rf y) /\ p = pc' /\ m = mem') Q Hh Hl).
  - rewrite sj_segs. eapply Exec.evt_mono; [exact HE|]. intros ms (y & ->). exists (Rf y), pc', mem'.
    split; [reflexivity | split; [exists y; reflexivity | split; reflexivity]].
  - intros R p m regs' ((y & ->) & -> & ->) HG. exact (HK y regs' HG).
Qed.

Lemma sj_GV_S : forall g, GV B APIf empty g -> spZ (g_regs g) = g_S g /\ alloc_ceiling + SLOT_K <= g_S g <= 2 ^ 47.
Proof.
  intros g (_ & _ & _ & _ & H1 & H2 & _ & H3 & _). unfold spZ. rewrite H3.
  pose proof alloc_ceiling_value. unfold SLOT_K, SLOT_STACK in *. rewrite sj_unsigned by lia. lia.
Qed.

Lemma post_FR : forall g km L A regs0 regs mem md,
  FR B APIf ra empty g km [] L A regs0 mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (g_regs g) regs ->
  Post B APIf ra g (mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md).
Proof.
  intros g km L A regs0 regs mem md HF HP H10 HRP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & HWF & HBD & HIN & HVM & HFA & HFI & HFB & HER & HSN & HRES
    & HSW).
  destruct (sj_GV_S g HGV) as [HSP HS].
  exists L, A, regs, mem, md. split; [reflexivity|].
  split.
  - unfold lib_post. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
    split; [exact H10|]. split; [exact HRP|]. split; [exact HVM|].
    split.
    { intros q k Hq. pose proof (sj_blocks_in (g_L g) (g_A g) q k Hq) as Hb.
      apply (Permutation_in _ (Permutation_sym HP)) in Hb.
      destruct (sj_in_blocks L A _ _ Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
    split.
    { intros a Ha Hn. unfold lib_scratch in Hn. rewrite HSP in Hn.
      assert (N1 : ~ (g_S g - SLOT_K <= a < g_S g)) by (unfold SLOT_K; tauto).
      assert (N2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (HFA a Ha N1 N2) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros a H1 H2 H3 H4. destruct (HFI a H1 H2 H3 H4) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq _ Hi. apply (HFB (ptr_addr (g_L g) q) k i); [apply sj_blocks_in; exact Hq | exact Hi]. }
    intros a [Ha|Ha]; [apply HSW; rewrite HSP in Ha; unfold SLOT_K; exact Ha | apply HER; exact Ha].
  - split; [exact HSN|]. split; [exact HMI|].
    split.
    + exact (resb_end (g_b g) km A HRES).
    + intros i Hi. destruct HGV as (_ & [[Hn _]|[_ Hp]] & _); [lia|].
      apply (HFB (g_p g) (g_n g) i Hp Hi).
Qed.

Lemma sj_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma sj_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < alloc_ceiling.
Proof. intros x seg H. destruct sj_img_low as [_ HI]. rewrite sj_segs in HI. exact (HI x seg H). Qed.

Lemma sj_img_lt : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof. intros a H. destruct sj_img_low as [HI _]. exact (HI a H). Qed.

Lemma sj_stk_of_wr : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 -> alloc_ceiling <= lo ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi H1 H2 H3 HW. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  pose proof (HW a Ha) as Hw. unfold writable_at in Hw. change (Z_to_bv 64 a) with (wa a) in Hw.
  assert (Hu : bv_unsigned (wa a) = a) by (unfold wa; apply sj_unsigned; lia).
  assert (Hn : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
  { destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:E; [|reflexivity].
    pose proof (sj_seg_low _ seg E). lia. }
  split; [exact Hw|].
  unfold wview in Hw. rewrite Hn in Hw. unfold Mem.mrd.
  destruct (m (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.

Lemma sj_pw_app : forall (T : Type) (R : T -> T -> Prop) l1 l2, pairwise R (l1 ++ l2) -> pairwise R l2.
Proof. intros T R l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H | exact (IH (proj2 H))]. Qed.

Lemma sj_in_img_b : forall a, existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) &&
    (a <? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true -> in_img B a.
Proof.
  intros a H. unfold in_img. rewrite sj_segs. split; [discriminate|].
  apply existsb_exists in H as (s & Hs & E). apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exists s. split; [exact Hs | lia].
Qed.

Lemma sj_errno_val : errno_addr B = 197644.
Proof. rewrite sj_errno. reflexivity. Qed.

Lemma sj_syms : ms_ctx B = 0x507b8 /\ ms_lock B = 0x507b0 /\ ms_libc B = 0x50740 /\ ms_guard B = 0x50720 /\
  ms_got_guard B = 0x1f138 /\ ms_size_classes B = 0x10678 /\ ms_small_cnt B = 0x106d8 /\ ms_med_cnt B = 0x106f3 /\
  ms_debruijn B = 0x10658 /\ @sk_ofl_head SH = 0x50b70 /\ @sk_ofl_lock SK = 0x50b68 /\ @sk_threaded SK = 0x50741.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _ & _ & _ &
    H20 & H21 & H22 & _). repeat split; assumption.
Qed.

Lemma sj_sink_addr : forall a, (0x50741 <= a < 0x50742 \/ 0x50b68 <= a < 0x50b6c \/ 0x50b70 <= a < 0x50b78) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof sj_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
  rewrite sj_errno_val. unfold static_owned, vml_lo, vml_len. rewrite (ff_vmlock_u _ _ _ _ _ _ _ FF).
  rewrite (ff_dbl_u _ _ _ _ _ _ _ FF), Z.max_id.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. unfold CTX_SIZE.
  split; [|lia]. apply sj_in_img_b.
  destruct Ha as [Ha|[Ha|Ha]];
    [ assert (a = 0x50741) by lia; subst a
    | assert (a = 0x50b68 \/ a = 0x50b69 \/ a = 0x50b6a \/ a = 0x50b6b) as [->|[->|[->| ->]]] by lia
    | assert (a = 0x50b70 \/ a = 0x50b71 \/ a = 0x50b72 \/ a = 0x50b73 \/ a = 0x50b74 \/ a = 0x50b75 \/ a = 0x50b76 \/
        a = 0x50b77) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] by lia ];
    vm_compute; reflexivity.
Qed.

Lemma sj_sink_frame : forall mem mem' md md',
  (forall a, (0x50741 <= a < 0x50742 \/ 0x50b68 <= a < 0x50b6c \/ 0x50b70 <= a < 0x50b78) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4). pose proof sj_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

Lemma sj_call_pre : forall g km hb L A regs mem md regs_c,
  FR B APIf ra empty g km hb L A regs mem md -> getr regs_c 2 = getr regs 2 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> call_pre B MR L A regs_c mem md.
Proof.
  intros g km hb L A regs mem md regs_c HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0).
  pose proof alloc_ceiling_value as HAC. unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 384).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply sj_unsigned. lia. }
  unfold call_pre. rewrite HSP. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSW; lia|].
  split; [rewrite E4, Htp; exact (proj1 HTP0)|].
  split; [exact HER|].
  intros H. rewrite HIN in H. discriminate.
Qed.

Lemma sj_FR_free : forall g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g km (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  call_post B MR L A regs_c mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
  blocks L A = b1 ++ (ptr_addr L p, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) ->
  ro_agree segs mem' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  res_ok_slots A' (sb_free (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2)) n) ->
  FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' /\
  Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)).
Proof.
  intros g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES'.
  pose proof sj_segs as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof sj_errno_ceil as HEC. pose proof sj_errno_val as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 384).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply sj_unsigned. lia. }
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HMR Hpn) as [Hp1 Hp2].
  assert (HEimg : forall a, ptr_addr L p <= a < ptr_addr L p + n -> ~ in_img B a).
  { intros a Ha. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
    apply (ax_blocks_img sj_ax L A mem md p n); [exact HMR | exact Hpn | lia]. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha H1 H2 H3. pose proof (sj_img_lt a Ha) as Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img sj_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img sj_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros He. exact (HEimg a He Ha). }
  assert (HH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 384 - 8192 <= a < g_S g - 384) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha Hs. apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - lia. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at segs mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 384 - 8192)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 384)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  assert (HPW : pairwise ranges_disjoint (hb1 ++ (ptr_addr L p, n) :: hb2 ++ blocks (g_L g) (g_A g))).
  { rewrite app_comm_cons, app_assoc. apply (sj_pairwise_perm _ _ sj_rd_sym (blocks L A)); [exact HP|].
    exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMR). }
  apply sj_pw_app in HPW. destruct HPW as [HPW _].
  split.
  2:{ rewrite EB'. rewrite <- app_assoc. apply (Permutation_app_inv b1 b2 hb1 (hb2 ++ blocks (g_L g) (g_A g))
        (ptr_addr L p, n)). rewrite <- EB. rewrite app_comm_cons, app_assoc. exact HP. }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (sj_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sj_stk_of_wr; [lia | lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (sj_relro_img a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact (INIT Hin)|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [F1 F2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [F1 F2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi). unfold blocks_kept in KEPT. apply (KEPT a k i); [| |exact Hi].
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak.
    - intros Ea. subst a. pose proof (HPW (ptr_addr L p, k) ltac:(apply in_or_app; right; exact Hak)) as D.
      unfold ranges_disjoint in D. cbn in D. lia. }
  split; [intros a Ha; apply SCW; unfold scratch; right; exact Ha|].
  split.
  { apply (sj_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (sj_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) km (hb1 ++ (ptr_addr L p, n) :: hb2) (hb1 ++ hb2) A' (ptr_addr L p) n
                   (Permutation_sym (Permutation_middle hb1 hb2 (ptr_addr L p, n))) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma sj_free_call : forall g km hb1 hb2 L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g km (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 1 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     Rz segs (mkCfg (mkst regs' (getr regs_c 1) mem' (seg_rom segs)) md') Q) ->
  Rz segs (mkCfg (mkst regs_c (Z_to_bv 64 0x15974) mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb1 hb2 L A regs mem md regs_c p n Q HF HP Hpn Hn E2 E3 E4 Hra H10 K.
  pose proof (sj_call_pre g km _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  rewrite <- sj_free.
  eapply rz_bind; [exact (rz_free L A regs_c mem md p n (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2))
                            CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (sj_FR_free g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT RO' INIT RES') as [HF' HP'].
  exact (K L' A' regs' mem' md' HF' HP' RP').
Qed.

Lemma sj2_img : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite sj_segs. vm_compute. reflexivity.
  - pose proof alloc_ceiling_val. lia.
Qed.

Lemma sj2_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < alloc_ceiling.
Proof. intros x seg H. destruct sj2_img as [_ HI]. rewrite sj_segs in HI. exact (HI x seg H). Qed.

Lemma sj2_img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof. intros a H. destruct sj2_img as [HI _]. exact (HI a H). Qed.

Lemma sj2_ro_low : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < alloc_ceiling.
Proof.
  intros a H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  exact (proj2 (sj2_seg_low _ seg E)).
Qed.

Lemma sj2_hi_noseg : forall a : word, alloc_ceiling <= bv_unsigned a -> find_segment rsegs (bv_unsigned a) 1 = None.
Proof.
  intros a H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (sj2_seg_low _ seg E). lia.
Qed.

Lemma sj2_stk_norm : forall m lo hi, stk rsegs m lo hi -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hl Hh. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (Hr : ro_addr rsegs (wa a) = false).
  { destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity]. pose proof (sj2_ro_low _ E) as X.
    unfold wa in X. rewrite MState.unsigned_lit in X by lia. lia. }
  destruct (H a Ha) as (Hw & b & Hb). unfold wview, mrd, normalize in *. rewrite Hr. split; [exact Hw|]. exists b. exact Hb.
Qed.

Lemma sj2_FR_frame : forall g km hb L A regs mem md mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch [(g_S g - SLOT_K, g_S g - 104)] mem mem' ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs mem' md.
Proof.
  intros g km hb L A regs mem md mem' HF HP HM HW.
  pose proof sj_segs as ES.
  pose proof FF as (_ & _ & _ & _ & _ & _ & HERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTP & HEO & _ &
                    HOH & HOL & HTH & _ & _ & _ & _ & HRL & _).
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn & Hp & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  pose proof alloc_ceiling_val as Hc. pose proof (HERR rc) as Herrc.
  unfold FR. unfold SLOT_K, SLOT_STACK in *.
  assert (Hout : forall a, 0 <= a < 2 ^ 64 -> a < g_S g - 65536 \/ g_S g - 104 <= a ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hx. apply HM. rewrite MState.unsigned_lit by exact Ha. apply sj2_outside1. lia. }
  assert (Hlow : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
    by (intros a Ha; apply Hout; lia).
  assert (HE0 : 0 <= errno_addr B) by (unfold errno_addr; rewrite HTP, HEO; lia).
  split; [exact HGV|]. split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|].
  split.
  { apply (sj2_ba_keep rsegs mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. apply Hout; lia. }
  split.
  { destruct Hstk as (S1 & S2 & SH0). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (SH0 a Ha) as (Hw & _).
    assert (Hu : bv_unsigned (wa a) = a) by (unfold wa; apply MState.unsigned_lit; lia).
    pose proof (HW (wa a) Hw) as Hw'. split; [exact Hw'|].
    assert (Hns : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (apply sj2_hi_noseg; lia).
    unfold wview in Hw'. rewrite Hns in Hw'. unfold mrd.
    destruct (mem' (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw'; reflexivity]. }
  split.
  { unfold MI in *. intros a Ha. rewrite <- (HMI a Ha). unfold mrd.
    pose proof Ha as Ha'. rewrite ES in Ha'.
    pose proof (sj2_ro_low a Ha') as X. pose proof (bv_unsigned_in_range 64 a) as R.
    change (bv_modulus 64) with (2 ^ 64) in R.
    rewrite (HM a); [reflexivity|]. apply sj2_outside1. lia. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (HRL a Ha) as (Hi & _). pose proof (sj2_img_low a Hi). apply sj2_mbyte_eq. apply Hlow. lia. }
  assert (Hcond : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      outside [(g_S g - 65536, g_S g - 104)] x) by (intros x Hx _; apply sj2_outside1; lia).
  split; [exact (kb_MR_A B (APIf rc) L A mem mem' md _ HMR HM Hcond)|].
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hin|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [E1 E2].
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hout; lia).
    rewrite (sj2_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply sj2_wr_eq. exact Hx. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [E1 E2]. pose proof (sj2_img_low a Ha).
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hlow; lia).
    rewrite (sj2_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply sj2_wr_eq. exact Hx. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi).
    apply (kb_blocks_munch B (APIf rc) L A mem mem' md _ HMR HM Hcond a k i); [|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak. }
  split.
  { intros a Ha. apply (sj2_wr_eq _ mem mem' a); [apply Hlow; lia | exact (Herr a Ha)]. }
  split.
  { unfold sink_none, closed_stdio_env in *. destruct Hsink as ((V1 & V2) & V3 & V4).
    split; [split|]; [| |split; [|exact V4]].
    - intros k Hk. rewrite <- (V1 k Hk). apply sj2_mbyte_eq. apply Hlow. rewrite HTH. lia.
    - intros k Hk. rewrite <- (V2 k Hk). apply sj2_mbyte_eq. apply Hlow. rewrite HOL. lia.
    - intros k Hk. rewrite <- (V3 k Hk). apply sj2_mbyte_eq. apply Hlow. rewrite HOH. lia. }
  split; [exact HRES|].
  intros a Ha. pose proof (Hwr a Ha) as X. unfold writable_at in *. rewrite ES in X |- *. apply HW. exact X.
Qed.

Lemma sj2_run : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md ->
  Exec.evt rsegs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
      K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md L A K P HM HE HK.
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hz].
  apply (kb_run_rz B regs pc mem md K P Hh Hz); [rewrite sj_segs; exact HE | exact HK].
Qed.

Lemma sj2_run_norm : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md -> ro_agree rsegs mem ->
  Exec.evt rsegs (fun ms => exists R pc' m0, ms = MState.MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs) /\
      forall mem', mem_rel rsegs mem' m0 -> ro_same rsegs mem mem' -> K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md L A K P HM Hro HE HK.
  apply (sj2_run regs pc mem md L A K P HM); [|exact HK].
  eapply Exec.evt_mono; [exact (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs Hro HE)|].
  intros s (s0 & (R & pc' & m0 & E & HQ) & Hrel & Hsame). subst s0.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  exists R, pc', (ms_mem s). split.
  - destruct s. cbn in *. subst. reflexivity.
  - apply HQ; assumption.
Qed.


Lemma sj_stk_sub : forall segs m lo hi lo' hi', stk segs m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' -> stk segs m lo' hi'.
Proof.
  intros segs m lo hi lo' hi' (H1 & H2 & H) E1 E2 E3. split; [exact E3|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma sj_relro_bytes : forall m a bs, relro B m -> relro_b a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR H. unfold relro_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite forallb_forall in H3.
  split; [exact H1|]. split; [exact H2|]. intros i Hi.
  specialize (H3 i ltac:(apply in_seq; lia)). apply andb_prop in H3 as [Hin Heq].
  unfold relro, G_img_c in HR. pose proof (HR _ (in_relro_sound _ Hin)) as E. rewrite sj_segs in E.
  transitivity (mbyte rsegs m (a + Z.of_nat i)); [reflexivity|]. rewrite E.
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [x|] eqn:Ex; cbn in Heq; [|discriminate].
  apply Z.eqb_eq in Heq. rewrite (nth_error_nth' bs z8 Hi). f_equal. apply bv_eq. exact Heq.
Qed.

Lemma sj_ro_bytes : forall m a bs, MI B m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Hra Ha Hl Hb. unfold MI in Hra. rewrite sj_segs in Hra.
  pose proof (ro_bytes_b_sound rsegs bs a Hb) as H.
  split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b H E) as [H1 H2]. rewrite (Hra _ H2). exact H1.
Qed.

Lemma sj_cat_entry : forall m r, relro B m -> MI B m -> 0 <= r < 11 ->
  cat_entry m (cat_row r) (catI r) (catO r) (catP r) (catS r) /\
  (catP r <> 0 -> catP r + Z.of_nat (length (catS r)) + 1 <= 2 ^ 40).
Proof.
  intros m r HR HM Hr. pose proof (cat_check_all r Hr) as C. unfold cat_check in C.
  repeat match type of C with (_ && _) = true => apply andb_prop in C as [C ?] end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  match goal with H : (catP r =? 0) || _ = true |- _ => rename H into HP end.
  split.
  - split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply sj_relro_bytes; assumption|]. split; [apply sj_relro_bytes; assumption|].
    split; [apply sj_relro_bytes; assumption|].
    intros Hne. apply orb_prop in HP as [HP|HP]; [apply Z.eqb_eq in HP; contradiction|].
    apply andb_prop in HP as [HP H40]. apply andb_prop in HP as [HB HZ]. apply Z.leb_le in H40.
    split; [apply sj_ro_bytes; [exact HM | lia | rewrite length_app; cbn [length]; lia | exact HB]|].
    apply NZ_notin. apply NZ_b. exact HZ.
  - intros Hne. apply orb_prop in HP as [HP|HP]; [apply Z.eqb_eq in HP; contradiction|].
    apply andb_prop in HP as [_ H40]. apply Z.leb_le in H40. exact H40.
Qed.

Lemma sj_cat_e_row : forall inp, cat_e inp = cat_row (t_row inp mod CAT_N).
Proof. intros inp. reflexivity. Qed.

Lemma sj_block_pos : forall g km hb L A regs mem md a k, FR B APIf ra empty g km hb L A regs mem md ->
  In (a, k) (blocks L A) -> 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros g km hb L A regs mem md a k HF Hin. destruct (sj_in_blocks L A a k Hin) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k (FR_MR _ _ _ _ _ _ _ _ HF) Hp).
Qed.

End TacSJ.

Ltac rgj HG := rewrite HG; first [reflexivity | assumption | match goal with H : _ |- _ => exact H end].

Lemma andi7_zero : forall e, 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 e)) (bv_wrap 64 7))) (Z_to_bv 64 0) = true.
Proof.
  intros e He H8. unfold bv_eqb. rewrite (unsigned_lit e) by lia.
  change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite H8.
  reflexivity.
Qed.
