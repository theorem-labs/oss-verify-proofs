From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState PropExec Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Ltac greg2 := unfold YK11.getr;
  lazymatch goal with |- (if ?b then _ else _) = _ => let v := eval vm_compute in b in change b with v; cbv iota end;
  Step.simp_regs.

Ltac br_if :=
  repeat match goal with
  | |- context [bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)] =>
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity
  | |- context [negb true] => replace (negb true) with false by reflexivity
  | |- context [negb false] => replace (negb false) with true by reflexivity
  | |- context [if false then ?x else ?y] => replace (if false then x else y) with y by reflexivity
  | |- context [if true then ?x else ?y] => replace (if true then x else y) with x by reflexivity
  end.

Lemma bytes_at_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof. intros m a H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma ro_agree_inv : forall m, Mem.mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m H a Ha. unfold mrd. destruct (m a) as [b|] eqn:E; [|reflexivity].
  rewrite (H a b E) in Ha. discriminate.
Qed.

Lemma fs_bound_sh2 : forall (l : list Segment) (x n : Z) s, find_segment l x n = Some s ->
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 40) l = true -> x + n <= 2 ^ 40.
Proof.
  induction l as [|s0 l IH]; intros x n s E F; cbn [find_segment] in E; [discriminate|].
  cbv zeta in E. cbn [forallb] in F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1.
  revert E. match goal with |- (if ?k then _ else _) = _ -> _ => destruct k eqn:C end; intros E.
  - apply andb_prop in C as [_ C2]. apply Z.leb_le in C2. lia.
  - exact (IH x n s E F2).
Qed.

Lemma ro_hi_sh2 : forall a : word, 2 ^ 40 <= bv_unsigned a -> Mem.ro_addr rsegs a = false.
Proof.
  intros a H. unfold Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (fs_bound_sh2 rsegs (bv_unsigned a) 1 s E ltac:(vm_compute; reflexivity)). lia.
Qed.

Lemma stk_rel_sh2 : forall m m0 lo hi, mem_rel rsegs m m0 -> 2 ^ 40 <= lo -> hi <= 2 ^ 64 ->
  (Frame.stk rsegs m lo hi <-> Frame.stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi. unfold Frame.stk. split; intros (H1 & H2 & H); split; try lia; split; try lia;
    intros a Ha; destruct (H a Ha) as [Hw (b & Hb)];
    assert (Hro : Mem.ro_addr rsegs (wa a) = false) by (apply ro_hi_sh2; rewrite wa_unsigned by lia; lia);
    pose proof (wview_rel_rw rsegs m m0 (wa a) HR Hro) as EW; pose proof (mrd_rel rsegs m m0 (wa a) HR) as ER.
  - split; [rewrite EW; exact Hw | exists b; rewrite <- ER; exact Hb].
  - split; [rewrite <- EW; exact Hw | exists b; rewrite ER; exact Hb].
Qed.

Lemma tok_go_true_len : forall l, length (tok_go true l) = length l.
Proof. induction l as [|b l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma tok_go_false_len : forall l,
  (length (tok_go false l) + (if has_dash l then 1 else 0) = length l)%nat.
Proof.
  unfold has_dash in *. induction l as [|b l IH]; [reflexivity|].
  cbn [tok_go existsb negb andb].
  destruct (RcIdentModel.bz b =? 45) eqn:E; cbn [orb].
  - rewrite tok_go_true_len. cbn [length]. lia.
  - cbn [length]. lia.
Qed.

Lemma TK_len : forall inp, zlen (n_TK inp) = n_lt inp.
Proof.
  intros inp. unfold zlen, n_TK, TOK, n_lt, n_ln. pose proof (tok_go_false_len (n_EXP_NM inp)).
  destruct (has_dash (n_EXP_NM inp)); lia.
Qed.

Lemma nr0_fits : forall inp, n_r inp = 0 ->
  n_wok inp = true /\ n_ln inp < t_cap_name inp /\ n_lt inp < t_cap_tok inp /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_r in H.
  destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. unfold n_fits in E2.
  apply andb_prop in E2 as [E2 E4]. apply andb_prop in E2 as [E2 E3].
  apply Z.ltb_lt in E2, E3, E4. auto.
Qed.

Lemma nr_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (n_wok inp && n_fits inp); auto. Qed.

Lemma EXPDP_eq : forall inp, n_EXP_DP inp = dp2 inp ++ s_out.
Proof. intros inp. unfold n_EXP_DP, dp2, dp1, s_open, s_in, s_out. rewrite <- !app_assoc. reflexivity. Qed.

Lemma ld_bounds : forall inp, n_wok inp = true ->
  1 <= n_ln inp <= 21 /\ 1 <= zlen (DEC (t_in inp) 1) <= 2 /\ 1 <= zlen (DEC (t_out inp) 1) <= 2 /\
  ld1 inp = n_ln inp + 2 + zlen (DEC (t_in inp) 1) /\
  ld2 inp = ld1 inp + 6 + zlen (DEC (t_out inp) 1) /\ n_ld inp = ld2 inp + 5.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  pose proof (n_ln_le inp H). pose proof (DEC1_len _ Hi). pose proof (DEC1_len _ Ho).
  unfold n_ld. rewrite EXPDP_eq. unfold ld2, ld1, dp2, dp1, zlen, n_ln. rewrite !length_app.
  assert (L1 : length s_open = 2%nat) by reflexivity.
  assert (L2 : length s_in = 6%nat) by reflexivity.
  assert (L3 : length s_out = 5%nat) by reflexivity.
  rewrite L1, L2, L3. unfold n_ln in *. lia.
Qed.

Lemma bv_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma bv_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma sltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  PropExec.v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof.
  intros x y Hx Hy. unfold PropExec.v_sltu, PropExec.c_ltu. rewrite bv_ltu_lit by lia.
  destruct (x <? y); reflexivity.
Qed.

Lemma sub_wrap : forall x y, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (x - y).
Proof. intros x y. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Zminus_mod. Qed.

Lemma bv_mod_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. exact H. Qed.

Lemma sub_wrapc : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - c) = Z_to_bv 64 (x - c).
Proof. intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Zminus_mod_idemp_l. Qed.

Lemma sub_lit_neg : forall x c k, k = 2 ^ 64 - c -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - k) = Z_to_bv 64 (x + c).
Proof.
  intros x c k ->. rewrite sub_wrapc. apply bv_mod_eq.
  rewrite <- (Z_mod_plus_full (x + c) (-1) (2 ^ 64)). f_equal. lia.
Qed.

Lemma fits_nr : forall inp, n_wok inp = true -> n_ln inp < t_cap_name inp -> n_lt inp < t_cap_tok inp ->
  n_ld inp < t_cap_disp inp -> n_r inp = 0.
Proof.
  intros inp Hw H1 H2 H3. unfold n_r, n_fits. rewrite Hw.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.ltb_lt _ _) H3). reflexivity.
Qed.

Lemma caps_range : forall inp, 0 <= t_cap_name inp < 40 /\ 0 <= t_cap_tok inp < 40 /\ 0 <= t_cap_disp inp < 64 /\
  0 <= t_in inp < 256 /\ 0 <= t_out inp < 256 /\ 0 <= t_row inp < 256.
Proof.
  intros inp. unfold t_cap_name, t_cap_tok, t_cap_disp, t_in, t_out, t_row, tb.
  pose proof (Z.mod_pos_bound (inb inp (cT inp + 5)) 40 ltac:(lia)).
  pose proof (Z.mod_pos_bound (inb inp (cT inp + 6)) 40 ltac:(lia)).
  pose proof (Z.mod_pos_bound (inb inp (cT inp + 7)) 64 ltac:(lia)).
  pose proof (inb_range inp (cT inp + 1)). pose proof (inb_range inp (cT inp + 2)).
  pose proof (inb_range inp (cT inp + 8)). lia.
Qed.

Lemma bv_eqb_small : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. Z.div_mod_to_equations. lia.
Qed.

Definition SWIN (g : ghost) : list (Z * Z) := [(g_S g - SLOT_K, g_S g - 104)].

Lemma st_ok : forall g m a j, Mem.wr_at rsegs m (g_S g - 65536) 65536 -> g_S g - 65536 <= a ->
  a + Z.of_nat j <= g_S g -> store_ok rsegs m (wa a) j = true.
Proof.
  intros g m a j H H1 H2. replace a with (g_S g - 65536 + (a - (g_S g - 65536))) by lia.
  apply (wr_at_store_ok rsegs m (g_S g - 65536) 65536); [exact H | lia | lia].
Qed.

Lemma rd8 : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w H. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a _ 0 8 H) by (rewrite ?length_le8; lia).
  reflexivity.
Qed.

Lemma rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a _ 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma keep_bytes : forall W mem m0 m' a bs, ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs mem a bs ->
  bytes_at rsegs m' a bs.
Proof.
  intros W mem m0 m' a bs HRO HMU HREL HD H.
  apply (proj2 (bytes_at_rel rsegs m' m0 a bs HREL)).
  apply (Frame.bytes_at_transport rsegs W (normalize rsegs mem) m0 a bs); [|exact HMU|exact HD].
  apply bytes_at_normalize; assumption.
Qed.

Lemma fin_bytes : forall m' m0 a bs, mem_rel rsegs m' m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m' a bs.
Proof. intros m' m0 a bs HREL H. exact (proj2 (bytes_at_rel rsegs m' m0 a bs HREL) H). Qed.

Lemma sltu0_nz : forall w : word, w <> Z_to_bv 64 0 -> PropExec.v_sltu (Z_to_bv 64 0) w = Z_to_bv 64 1.
Proof.
  intros w H. unfold PropExec.v_sltu, PropExec.c_ltu, bv_ltu.
  rewrite (MState.unsigned_lit 0) by lia.
  pose proof (bv_unsigned_in_range 64 w) as R.
  assert (N : bv_unsigned w <> 0).
  { intro E. apply H. apply bv_eq. rewrite E. rewrite MState.unsigned_lit by lia. reflexivity. }
  replace (0 <? bv_unsigned w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma sub_lit : forall x y, 0 <= y <= x -> x < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (x - y).
Proof. intros x y H1 H2. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Fixpoint ro_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => Mem.ro_addr rsegs (wa a) &&
      match PropExec.seg_rom rsegs (wa a) with Some b' => Z.eqb (bv_unsigned b') (bv_unsigned b) | None => false end &&
      ro_chk (a + 1) r
  end.

Lemma ro_chk_sound : forall bs a, ro_chk a bs = true -> Mem.ro_bytes rsegs a bs.
Proof.
  induction bs as [|b r IH]; intros a H; [exact I|]. cbn [ro_chk] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [|apply IH; exact H3].
  split; [|exact H1].
  destruct (PropExec.seg_rom rsegs (wa a)) as [b'|]; [|discriminate]. apply Z.eqb_eq in H2. f_equal. apply bv_eq.
  exact H2.
Qed.

Lemma bytes_at_one : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k (H1 & H2 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  replace (a + Z.of_nat k + Z.of_nat 0) with (a + Z.of_nat k) by lia. rewrite (H k Hk).
  cbn [nth_error]. apply nth_error_nth'. exact Hk.
Qed.

Lemma firstn_snoc : forall (l : list byte) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  induction l as [|x l IH]; intros [|k] d H; cbn [length] in H; try lia; [reflexivity|].
  change (firstn (S (S k)) (x :: l)) with (x :: firstn (S k) l).
  change (firstn (S k) (x :: l)) with (x :: firstn k l). change (nth (S k) (x :: l) d) with (nth k l d).
  rewrite (IH k d) by lia. reflexivity.
Qed.

Lemma bytes_at_snoc : forall m a bs b, bytes_at rsegs m a bs -> a + Z.of_nat (length bs) + 1 <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa (a + Z.of_nat (length bs))) [b]) a (bs ++ [b]).
Proof.
  intros m a bs b H Hl. pose proof (bytes_at_bound rsegs m a bs H) as [H0 _].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact H | lia | cbn [length]; lia | left; lia].
  - apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma le1_byte : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  unfold le1. rewrite (MState.unsigned_lit (bv_unsigned b)) by lia.
  pose proof (kb_nth_le_bytes 1 (bv_unsigned b) 0 ltac:(lia)) as N.
  change (8 * Z.of_nat 0) with 0 in N. rewrite Z.shiftr_0_r in N.
  pose proof (length_Z_to_le_bytes 1 (bv_unsigned b)) as L.
  revert N L. destruct (Z_to_le_bytes 1 (bv_unsigned b)) as [|x [|y r]]; intros N L; cbn [length] in L;
    try discriminate.
  cbn [nth_error] in N. injection N as ->. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition KM (W : list (Z * Z)) (mem m' : word -> option byte) : Prop :=
  forall a bs, disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.

Lemma KM_of : forall W mem m0 m', ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> KM W mem m'.
Proof. intros W mem m0 m' HRO HMU HREL a bs HD H. exact (keep_bytes W mem m0 m' a bs HRO HMU HREL HD H). Qed.

Lemma munch_SWIN : forall g W m m', Frame.munch W m m' ->
  Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) W -> Frame.munch (SWIN g) m m'.
Proof.
  intros g W m m' HM HF. apply (Frame.munch_weaken W); [|exact HM].
  intros x Hx. unfold SWIN, SLOT_K, SLOT_STACK in Hx. cbn in Hx. destruct Hx as [Hx _].
  clear HM. induction HF as [|[lo hi] W' Hiv HF IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma NB_keep : forall g nm tk dp regs mem R m' W,
  NB g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 40) 8 ->
  YK11.getr R 20 = YK11.getr regs 20 -> YK11.getr R 21 = YK11.getr regs 21 ->
  YK11.getr R 22 = YK11.getr regs 22 -> YK11.getr R 23 = YK11.getr regs 23 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  NB g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HID & Hw & E20 & E21 & E22 & E23 & E24 & E25 & HCD & _) KMm HO D1 D2
    F20 F21 F22 F23 F24 F25.
  unfold NB. split; [|split; [exact Hw|]].
  { apply KMm; [rewrite rec_id_length; exact D1 | exact HID]. }
  rewrite F20, F21, F22, F23, F24, F25.
  split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|]. split; [exact E24|].
  split; [exact E25|]. split; [|exact HO].
  apply KMm; [rewrite length_le8; exact D2 | exact HCD].
Qed.

Lemma NC_keep : forall g nm tk dp regs mem R m' W,
  NC g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 40) 8 -> disjoint_from W (spk g 32) 8 ->
  disjoint_from W (spk g 226) (n_ln (g_in g) + 1) ->
  YK11.getr R 20 = YK11.getr regs 20 -> YK11.getr R 21 = YK11.getr regs 21 ->
  YK11.getr R 22 = YK11.getr regs 22 -> YK11.getr R 23 = YK11.getr regs 23 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  YK11.getr R 26 = YK11.getr regs 26 -> YK11.getr R 19 = YK11.getr regs 19 ->
  NC g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HNB & E26 & E19 & HROW & HNM) KMm HO D1 D2 D3 D4
    F20 F21 F22 F23 F24 F25 F26 F19.
  unfold NC. split; [exact (NB_keep g nm tk dp regs mem R m' W HNB KMm HO D1 D2 F20 F21 F22 F23 F24 F25)|].
  rewrite F26, F19. split; [exact E26|]. split; [exact E19|].
  split; [apply KMm; [rewrite length_le8; exact D3 | exact HROW]|].
  apply KMm; [|exact HNM]. unfold n_ln in D4. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D4.
Qed.

Lemma N0_keep : forall g nm tk dp regs mem R m' W,
  N0 g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 40) 8 -> disjoint_from W (spk g 16) 8 ->
  disjoint_from W (stem_addr g) (zlen (n_stem (g_in g)) + 1) ->
  YK11.getr R 20 = YK11.getr regs 20 -> YK11.getr R 21 = YK11.getr regs 21 ->
  YK11.getr R 22 = YK11.getr regs 22 -> YK11.getr R 23 = YK11.getr regs 23 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  YK11.getr R 9 = YK11.getr regs 9 -> YK11.getr R 18 = YK11.getr regs 18 ->
  N0 g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HNB & E9 & E18 & HQ & HCS) KMm HO D1 D2 D3 D4
    F20 F21 F22 F23 F24 F25 F9 F18.
  unfold N0. split; [exact (NB_keep g nm tk dp regs mem R m' W HNB KMm HO D1 D2 F20 F21 F22 F23 F24 F25)|].
  rewrite F9, F18. split; [exact E9|]. split; [exact E18|].
  split; [apply KMm; [rewrite length_le8; exact D3 | exact HQ]|].
  apply KMm; [|exact HCS]. unfold zlen in D4. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D4.
Qed.

Lemma N1_keep : forall g nm tk dp regs mem R m' W,
  N1 g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 40) 8 -> disjoint_from W (spk g 16) 8 ->
  disjoint_from W (stem_addr g) (zlen (n_stem (g_in g)) + 1) ->
  disjoint_from W (spk g 176) 5 -> disjoint_from W (spk g 200) 8 -> disjoint_from W (spk g 168) 8 ->
  YK11.getr R 20 = YK11.getr regs 20 -> YK11.getr R 21 = YK11.getr regs 21 ->
  YK11.getr R 22 = YK11.getr regs 22 -> YK11.getr R 23 = YK11.getr regs 23 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  YK11.getr R 9 = YK11.getr regs 9 -> YK11.getr R 18 = YK11.getr regs 18 ->
  YK11.getr R 8 = YK11.getr regs 8 ->
  N1 g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HN0 & E8 & HW4 & HQ2 & HQ1) KMm HO D1 D2 D3 D4 D5 D6 D7
    F20 F21 F22 F23 F24 F25 F9 F18 F8.
  unfold N1. split; [exact (N0_keep g nm tk dp regs mem R m' W HN0 KMm HO D1 D2 D3 D4
    F20 F21 F22 F23 F24 F25 F9 F18)|].
  rewrite F8. split; [exact E8|].
  split; [apply KMm; [|exact HW4]|].
  { pose proof (HN0) as (HNB & _). destruct HNB as (_ & Hw & _).
    destruct (wok_chans _ Hw) as [Hi Ho]. unfold n_W4. rewrite !length_app, (DEC2_len _ Hi), (DEC2_len _ Ho).
    exact D5. }
  split; [apply KMm; [rewrite length_le8; exact D6 | exact HQ2]|].
  apply KMm; [rewrite length_le8; exact D7 | exact HQ1].
Qed.

Lemma nzb_W4 : forall inp, n_wok inp = true -> Tac_si.nzb (n_W4 inp) = true /\ length (n_W4 inp) = 4%nat.
Proof.
  intros inp Hw. destruct (wok_chans _ Hw) as [Hi Ho].
  destruct (Tac_si.nzb_dec_all _ Hi) as [_ Ni]. destruct (Tac_si.nzb_dec_all _ Ho) as [_ No].
  unfold n_W4. rewrite Tac_si.nzb_app, Ni, No, length_app, (DEC2_len _ Hi), (DEC2_len _ Ho). split; reflexivity.
Qed.

Lemma H9a_keep : forall g nm tk dp regs mem R m' W,
  H9a g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 40) 8 -> disjoint_from W (spk g 16) 8 ->
  disjoint_from W (stem_addr g) (zlen (n_stem (g_in g)) + 1) ->
  disjoint_from W (spk g 176) 5 -> disjoint_from W (spk g 200) 8 -> disjoint_from W (spk g 168) 8 ->
  disjoint_from W (spk g 32) 8 -> disjoint_from W (spk g 226) (n_ln (g_in g) + 1) ->
  YK11.getr R 20 = YK11.getr regs 20 -> YK11.getr R 21 = YK11.getr regs 21 ->
  YK11.getr R 22 = YK11.getr regs 22 -> YK11.getr R 23 = YK11.getr regs 23 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  YK11.getr R 9 = YK11.getr regs 9 -> YK11.getr R 18 = YK11.getr regs 18 ->
  YK11.getr R 8 = YK11.getr regs 8 -> YK11.getr R 26 = YK11.getr regs 26 ->
  H9a g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HN1 & E26 & HROW & HNM) KMm HO D1 D2 D3 D4 D5 D6 D7 D8 D9
    F20 F21 F22 F23 F24 F25 F9 F18 F8 F26.
  split; [exact (N1_keep g nm tk dp regs mem R m' W HN1 KMm HO D1 D2 D3 D4 D5 D6 D7
    F20 F21 F22 F23 F24 F25 F9 F18 F8)|].
  rewrite F26. split; [exact E26|].
  split; [apply KMm; [rewrite length_le8; exact D8 | exact HROW]|].
  apply KMm; [|exact HNM]. unfold n_ln in D9. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D9.
Qed.

Lemma stem_addr_cases : forall g, (stem_addr g = spk g 133 /\ zlen (n_stem (g_in g)) <= 16) \/
  (0 <= stem_addr g /\ stem_addr g + 8 <= 0x10600 /\ zlen (n_stem (g_in g)) <= 7).
Proof.
  intros g. pose proof (n_stem_len (g_in g)) as L16. unfold stem_addr, zlen in *. unfold n_stem in *.
  destruct (n_use_said (g_in g)).
  - left. split; [reflexivity | lia].
  - right. pose proof (stem_img_len (n_fam (g_in g))). unfold reac_box_family_stem_c.STEM_Addr.
    destruct (n_fam (g_in g) =? 1); [|destruct (n_fam (g_in g) =? 2); [|destruct (n_fam (g_in g) =? 3)]]; lia.
Qed.

Lemma ro_agree_munch : forall W m m', ro_agree rsegs m -> Frame.munch W m m' ->
  Forall (fun iv => 2 ^ 40 <= fst iv) W -> ro_agree rsegs m'.
Proof.
  intros W m m' HR HM HF a Ha. rewrite <- (HR a Ha). unfold mrd. rewrite (HM a); [reflexivity|].
  assert (Hlt : bv_unsigned a < 2 ^ 40).
  { destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 40)) as [H|H]; [exact H|]. rewrite (ro_hi_sh2 a H) in Ha.
    discriminate. }
  clear HM. induction HF as [|[lo hi] W' Hiv HF IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma IRb_keep : forall g nm tk dp regs mem R m' W,
  IRb g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 226) (n_ln (g_in g) + 1) ->
  disjoint_from W (spk g 48) (n_ld (g_in g) + 1) ->
  YK11.getr R 9 = YK11.getr regs 9 -> YK11.getr R 18 = YK11.getr regs 18 ->
  YK11.getr R 19 = YK11.getr regs 19 -> YK11.getr R 20 = YK11.getr regs 20 ->
  YK11.getr R 21 = YK11.getr regs 21 -> YK11.getr R 22 = YK11.getr regs 22 ->
  YK11.getr R 23 = YK11.getr regs 23 -> YK11.getr R 24 = YK11.getr regs 24 ->
  YK11.getr R 25 = YK11.getr regs 25 -> YK11.getr R 27 = YK11.getr regs 27 ->
  IRb g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HID & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E27 & _ & HE)
    KMm HO D1 D2 D3 F9 F18 F19 F20 F21 F22 F23 F24 F25 F27.
  unfold IRb. split; [apply KMm; [rewrite rec_id_length; exact D1 | exact HID]|].
  rewrite F9, F18, F19, F20, F21, F22, F23, F24, F25, F27.
  do 10 (split; [assumption|]). split; [exact HO|].
  intros Hr. destruct (HE Hr) as [H1 H2]. split.
  - apply KMm; [|exact H1]. unfold n_ln in D2. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D2.
  - apply KMm; [|exact H2]. unfold n_ld in D3. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D3.
Qed.

Lemma IRc_keep : forall g nm tk dp regs mem R m' W,
  IRc g nm tk dp regs mem -> KM W mem m' -> OUTS g nm tk dp m' ->
  disjoint_from W (spk g 130) 38 -> disjoint_from W (spk g 226) (n_ln (g_in g) + 1) ->
  disjoint_from W (spk g 48) (n_ld (g_in g) + 1) ->
  YK11.getr R 18 = YK11.getr regs 18 -> YK11.getr R 20 = YK11.getr regs 20 ->
  YK11.getr R 21 = YK11.getr regs 21 -> YK11.getr R 22 = YK11.getr regs 22 ->
  YK11.getr R 24 = YK11.getr regs 24 -> YK11.getr R 25 = YK11.getr regs 25 ->
  YK11.getr R 27 = YK11.getr regs 27 ->
  IRc g nm tk dp R m'.
Proof.
  intros g nm tk dp regs mem R m' W (HID & E18 & E20 & E21 & E22 & E24 & E25 & E27 & _ & Hr & H1 & H2)
    KMm HO D1 D2 D3 F18 F20 F21 F22 F24 F25 F27.
  unfold IRc. split; [apply KMm; [rewrite rec_id_length; exact D1 | exact HID]|].
  rewrite F18, F20, F21, F22, F24, F25, F27.
  do 7 (split; [assumption|]). split; [exact HO|]. split; [exact Hr|]. split.
  - apply KMm; [|exact H1]. unfold n_ln in D2. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D2.
  - apply KMm; [|exact H2]. unfold n_ld in D3. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D3.
Qed.

Lemma cat_entry_keep : forall W mem m' e I O P sP, KM W mem m' -> cat_entry mem e I O P sP ->
  disjoint_from W (e + 8) 8 -> disjoint_from W (e + 16) 4 -> disjoint_from W (e + 20) 4 ->
  (P <> 0 -> disjoint_from W P (zlen sP + 1)) -> cat_entry m' e I O P sP.
Proof.
  intros W mem m' e I O P sP KMm (H1 & H2 & H3 & B8 & B16 & B20 & HS) D8 D16 D20 DP.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply KMm; [rewrite length_le8; exact D8 | exact B8]|].
  split; [apply KMm; [rewrite length_le4; exact D16 | exact B16]|].
  split; [apply KMm; [rewrite length_le4; exact D20 | exact B20]|].
  intros HP. destruct (HS HP) as [HC HN]. split; [|exact HN].
  apply KMm; [|exact HC]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact (DP HP).
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma FF_segs : ms_segs B = rsegs.
Proof. destruct FF as (H & _). exact H. Qed.

Lemma FF_errno : 0 <= errno_addr B /\ errno_addr B + 4 <= alloc_ceiling.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & H & _ & _ & _ & _ & _ & _ & _ & _ & _ & T & O & _).
  split; [unfold errno_addr; rewrite T, O; lia | apply H].
Qed.

Lemma FF_sink : @sk_ofl_head SH = 0x50640 /\ @sk_ofl_lock SK = 0x50638 /\ @sk_threaded SK = 0x50210 + 1.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  auto.
Qed.

Lemma FF_img : img_low B.
Proof.
  apply (img_low_of_check B (2 ^ 40)).
  - unfold img_check. rewrite FF_segs. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma FR_frame : forall g km hb L A regs mem md regs' mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  Frame.munch (SWIN g) mem mem' -> Frame.wmono rsegs mem mem' ->
  Frame.stk rsegs mem' (g_S g - SLOT_K) (g_S g) -> ro_agree rsegs mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HFR HPM E2 E3 E4 HMU HWM HSTK' HRO'.
  pose proof FF_segs as SEG. pose proof FF_errno as [HE0 HER]. pose proof FF_img as [HIM _].
  pose proof alloc_ceiling_value as HAC.
  destruct HFR as (HGV & H2 & H3 & H4 & HSV & HSTK & HMI & HRL & HMR & HWF & HBD & HIN & HMD & H14 & H15 & H16 &
    H17 & HSN & HRES & HWIN).
  pose proof HGV as (Hn & Hp & Hblk & HS16 & HSK & HS47 & Hroom & HgS & HgT).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HO : forall x, 0 <= x < g_S g - 65536 -> Frame.outside (SWIN g) x).
  { intros x Hx. unfold SWIN, SLOT_K, SLOT_STACK. apply outside_one. lia. }
  assert (HMB : forall x, 0 <= x < g_S g - 65536 -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
  { intros x Hx. apply (KindBGlue.mbyte_munch (ms_segs B) (SWIN g)); [exact HMU | lia | apply HO; lia]. }
  assert (HWB : forall x, 0 <= x < g_S g - 65536 ->
    (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx. apply (writable_munch (ms_segs B) (SWIN g)); [exact HMU | lia | apply HO; lia]. }
  unfold FR, SLOT_K, SLOT_STACK.
  split; [exact HGV|]. split; [rewrite E2; exact H2|]. split; [rewrite E3; exact H3|].
  split; [rewrite E4; exact H4|].
  split.
  { apply (Frame.bytes_at_transport rsegs (SWIN g) mem mem' _ _ HSV HMU).
    unfold SWIN, SLOT_K, SLOT_STACK. cbn [disjoint_from]. split; [right; lia | exact I]. }
  split; [exact HSTK'|].
  split; [unfold MI; rewrite SEG; exact HRO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite HMB; [apply HRL; exact Ha|].
    destruct Ha as (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split; [apply (kb_MR_A B (APIf rc) L A mem mem' md (SWIN g) HMR HMU); intros x Hx _; apply HO; lia|].
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|]. split; [exact HMD|].
  split.
  { intros a Ha Hns Hne. destruct (H14 a Ha Hns Hne) as [E W].
    assert (Ho : Frame.outside (SWIN g) a) by (unfold SWIN, SLOT_K, SLOT_STACK; apply outside_one; lia).
    rewrite (KindBGlue.mbyte_munch (ms_segs B) (SWIN g) mem mem' a HMU ltac:(lia) Ho).
    pose proof (writable_munch (ms_segs B) (SWIN g) mem mem' a HMU ltac:(lia) Ho) as W'.
    split; [exact E | tauto]. }
  split.
  { intros a Ha Hs Hc Hne. destruct (H15 a Ha Hs Hc Hne) as [E W]. pose proof (HIM a Ha) as Hl.
    rewrite HMB by lia. pose proof (HWB a ltac:(lia)) as W'. split; [exact E | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (H16 a k i Hin Hi).
    refine (kb_blocks_munch B (APIf rc) L A mem mem' md (SWIN g) HMR HMU _ a k i _ Hi).
    - intros x Hx _. apply HO. lia.
    - eapply Permutation_in; [apply Permutation_sym; exact HPM|]. apply in_or_app. right. exact Hin. }
  split.
  { intros a Ha. pose proof (HWB a ltac:(lia)) as W. apply W. apply H17. exact Ha. }
  split.
  { destruct FF_sink as (Q1 & Q2 & Q3).
    unfold sink_none, closed_stdio_env, val_mem, word_mem in *.
    destruct HSN as ((T1 & T2) & W3 & N3).
    split; [split|split].
    - intros k Hk. rewrite HMB; [apply T1; exact Hk | lia].
    - intros k Hk. rewrite HMB; [apply T2; exact Hk | lia].
    - intros k Hk. rewrite HMB; [apply W3; exact Hk | lia].
    - exact N3. }
  split; [exact HRES|].
  intros a Ha. pose proof (HWIN a Ha) as W. unfold writable_at in *. rewrite SEG in *. apply HWM. exact W.
Qed.

Definition RUNK (g : ghost) (mem : word -> option byte) (regs : bvmap 5 word) (pc' : Z)
    (P' : bvmap 5 word -> (word -> option byte) -> Prop)
    (R : bvmap 5 word) (pcw : word) (m0 : word -> option byte) : Prop :=
  pcw = Z_to_bv 64 pc' /\
  Frame.munch (SWIN g) (normalize rsegs mem) m0 /\ Frame.wmono rsegs (normalize rsegs mem) m0 /\
  Frame.stk rsegs m0 (g_S g - SLOT_K) (g_S g) /\
  YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
  (forall R' m', (forall r, YK11.getr R' r = YK11.getr R r) -> mem_rel rsegs m' m0 -> P' R' m').

Definition RUN (g : ghost) (mem : word -> option byte) (regs : bvmap 5 word) (pc' : Z)
    (P' : bvmap 5 word -> (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists R pcw m0, ms = MState.MS R fp_regs pcw fp_csr None m0 (seg_rom rsegs) /\ RUNK g mem regs pc' P' R pcw m0.

Lemma fin_mem : forall g mem regs pc' P' R m0,
  Frame.munch (SWIN g) (normalize rsegs mem) m0 -> Frame.wmono rsegs (normalize rsegs mem) m0 ->
  Frame.stk rsegs m0 (g_S g - 65536) (g_S g) ->
  YK11.getr R 2 = YK11.getr regs 2 -> YK11.getr R 3 = YK11.getr regs 3 -> YK11.getr R 4 = YK11.getr regs 4 ->
  (forall R' m', (forall r, YK11.getr R' r = YK11.getr R r) -> mem_rel rsegs m' m0 -> P' R' m') ->
  Exec.evt rsegs (RUN g mem regs pc' P') (MState.MS R fp_regs (Z_to_bv 64 pc') fp_csr None m0 (seg_rom rsegs)).
Proof.
  intros g mem regs pc' P' R m0 HMU HWM HSTK E2 E3 E4 HP.
  apply Exec.evt_done. exists R, (Z_to_bv 64 pc'), m0. split; [reflexivity|].
  unfold RUNK. split; [reflexivity|]. split; [exact HMU|]. split; [exact HWM|]. split; [exact HSTK|].
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. exact HP.
Qed.

Lemma fin_nomem : forall g mem regs pc' P' R,
  Frame.stk rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) ->
  YK11.getr R 2 = YK11.getr regs 2 -> YK11.getr R 3 = YK11.getr regs 3 -> YK11.getr R 4 = YK11.getr regs 4 ->
  (forall R' m', (forall r, YK11.getr R' r = YK11.getr R r) -> mem_rel rsegs m' (normalize rsegs mem) -> P' R' m') ->
  Exec.evt rsegs (RUN g mem regs pc' P')
    (MState.MS R fp_regs (Z_to_bv 64 pc') fp_csr None (normalize rsegs mem) (seg_rom rsegs)).
Proof.
  intros. apply fin_mem; [apply Frame.munch_refl | apply Frame.wmono_refl | assumption ..].
Qed.

Lemma fin_l : forall g mem regs pc1 pc2 P1 P2 R m0,
  Frame.munch (SWIN g) (normalize rsegs mem) m0 -> Frame.wmono rsegs (normalize rsegs mem) m0 ->
  Frame.stk rsegs m0 (g_S g - 65536) (g_S g) ->
  YK11.getr R 2 = YK11.getr regs 2 -> YK11.getr R 3 = YK11.getr regs 3 -> YK11.getr R 4 = YK11.getr regs 4 ->
  (forall R' m', (forall r, YK11.getr R' r = YK11.getr R r) -> mem_rel rsegs m' m0 -> P1 R' m') ->
  Exec.evt rsegs (fun ms => RUN g mem regs pc1 P1 ms \/ RUN g mem regs pc2 P2 ms)
    (MState.MS R fp_regs (Z_to_bv 64 pc1) fp_csr None m0 (seg_rom rsegs)).
Proof.
  intros. eapply Exec.evt_mono; [apply fin_mem; eassumption|]. intros ms Hms. left. exact Hms.
Qed.

Lemma fin_r : forall g mem regs pc1 pc2 P1 P2 R m0,
  Frame.munch (SWIN g) (normalize rsegs mem) m0 -> Frame.wmono rsegs (normalize rsegs mem) m0 ->
  Frame.stk rsegs m0 (g_S g - 65536) (g_S g) ->
  YK11.getr R 2 = YK11.getr regs 2 -> YK11.getr R 3 = YK11.getr regs 3 -> YK11.getr R 4 = YK11.getr regs 4 ->
  (forall R' m', (forall r, YK11.getr R' r = YK11.getr R r) -> mem_rel rsegs m' m0 -> P2 R' m') ->
  Exec.evt rsegs (fun ms => RUN g mem regs pc1 P1 ms \/ RUN g mem regs pc2 P2 ms)
    (MState.MS R fp_regs (Z_to_bv 64 pc2) fp_csr None m0 (seg_rom rsegs)).
Proof.
  intros. eapply Exec.evt_mono; [apply fin_mem; eassumption|]. intros ms Hms. right. exact Hms.
Qed.

Lemma exit_ok : forall (X : ghost -> config -> Prop) g pc' km hb P' L A regs mem md R m' m0 regs',
  Hcut B APIf ra X ->
  (forall c', CUTST B APIf ra empty g pc' km hb P' c' -> X g c') ->
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  RUNK g mem regs pc' P' R (Z_to_bv 64 pc') m0 -> mem_rel rsegs m' m0 -> ro_same rsegs mem m' ->
  (forall r, YK11.getr regs' r = YK11.getr R r) ->
  Rz (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 pc') m' (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros X g pc' km hb P' L A regs mem md R m' m0 regs' HX HXi HFR HPM HK HREL HSAME HG.
  pose proof FF_segs as SEG.
  pose proof HFR as (HGV & _ & _ & _ & _ & HSTK & HMI & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & HS47 & _).
  pose proof alloc_ceiling_value as HAC.
  assert (HMI' : ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEG in HMI; exact HMI).
  destruct HK as (_ & HMU & HWM & HSTK0 & G2 & G3 & G4 & HP').
  apply HX. apply HXi. unfold CUTST.
  exists L, A, regs', m', md. split; [reflexivity|].
  split; [|split; [exact HPM|]].
  - apply (FR_frame g km hb L A regs mem md regs' m' HFR HPM).
    + rewrite HG. exact G2.
    + rewrite HG. exact G3.
    + rewrite HG. exact G4.
    + exact (munch_rel rsegs (SWIN g) mem (normalize rsegs mem) m' m0 (mem_rel_normalize rsegs mem HMI')
        HREL HSAME HMU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0 (mem_rel_normalize rsegs mem HMI') HREL HSAME HWM).
    + unfold SLOT_K, SLOT_STACK in *.
      apply (proj2 (stk_rel_sh2 m' m0 (g_S g - 65536) (g_S g) HREL ltac:(lia) ltac:(lia))). exact HSTK0.
    + exact (ro_agree_same rsegs mem m' HMI' HSAME).
  - apply HP'; [exact HG | exact HREL].
Qed.

Lemma seg_go2 : forall (X1 X2 : ghost -> config -> Prop) g pc pc1 pc2 km hb P P1 P2 c,
  Hcut B APIf ra X1 -> Hcut B APIf ra X2 ->
  (forall c', CUTST B APIf ra empty g pc1 km hb P1 c' -> X1 g c') ->
  (forall c', CUTST B APIf ra empty g pc2 km hb P2 c' -> X2 g c') ->
  CUTST B APIf ra empty g pc km hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     Exec.evt rsegs (fun ms => RUN g mem regs pc1 P1 ms \/ RUN g mem regs pc2 P2 ms)
       (MState.MS (rmk regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs))) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros X1 X2 g pc pc1 pc2 km hb P P1 P2 c HX1 HX2 HXi1 HXi2 (L & A & regs & mem & md & -> & HFR & HPM & HP) HRUN.
  pose proof FF_segs as SEG.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
  destruct (kb_md B (APIf rc) L A mem md HMR) as [Hh Hl].
  assert (HMI' : ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEG in HMI; exact HMI).
  apply (kb_run_rz B regs (Z_to_bv 64 pc) mem md
    (fun R pcw m' => exists m0, (RUNK g mem regs pc1 P1 R pcw m0 \/ RUNK g mem regs pc2 P2 R pcw m0) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs mem m')
    _ Hh Hl).
  - rewrite SEG. eapply Exec.evt_mono.
    + apply (evt_normalize rsegs); [exact wx_apart_rsegs | exact HMI' | exact (HRUN L A regs mem md HFR HPM HP)].
    + intros s (s0 & HK & HREL & HSAME).
      destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
      destruct HREL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
      cbn in E1, E2, E3, E4, E5, E6, E7, E8, HSAME.
      destruct HK as [(R & pcw & m0 & -> & HK) | (R & pcw & m0 & -> & HK)].
      * cbn in E1, E2, E3, E4, E5, E6, E7, E8. subst Rs Fs pcs svcs rvs fcs ros.
        exists R, pcw, ms. split; [reflexivity|]. exists m0. split; [left; exact HK|]. split; [exact E8 | exact HSAME].
      * cbn in E1, E2, E3, E4, E5, E6, E7, E8. subst Rs Fs pcs svcs rvs fcs ros.
        exists R, pcw, ms. split; [reflexivity|]. exists m0. split; [right; exact HK|]. split; [exact E8 | exact HSAME].
  - intros R pcw m' regs' (m0 & [HK|HK] & HREL & HSAME) HG.
    + pose proof HK as (Epc & _). subst pcw.
      exact (exit_ok X1 g pc1 km hb P1 L A regs mem md R m' m0 regs' HX1 HXi1 HFR HPM HK HREL HSAME HG).
    + pose proof HK as (Epc & _). subst pcw.
      exact (exit_ok X2 g pc2 km hb P2 L A regs mem md R m' m0 regs' HX2 HXi2 HFR HPM HK HREL HSAME HG).
Qed.

Lemma seg_go : forall (X : ghost -> config -> Prop) g pc pc' km hb P P' c,
  Hcut B APIf ra X ->
  (forall c', CUTST B APIf ra empty g pc' km hb P' c' -> X g c') ->
  CUTST B APIf ra empty g pc km hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     Exec.evt rsegs (RUN g mem regs pc' P')
       (MState.MS (rmk regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs))) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros X g pc pc' km hb P P' c HX HXi HC HRUN.
  apply (seg_go2 X X g pc pc' pc' km hb P P' P' c HX HX HXi HXi HC).
  intros L A regs mem md HFR HPM HP. eapply Exec.evt_mono; [exact (HRUN L A regs mem md HFR HPM HP)|].
  intros ms H. left. exact H.
Qed.

Lemma start_facts : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  ro_agree rsegs mem /\ YK11.getr regs 2 = Z_to_bv 64 (g_S g - 368) /\
  CEIL_MIN + 65536 <= g_S g /\ g_S g <= 2 ^ 47 /\ g_S g mod 16 = 0 /\
  Mem.mem_inv rsegs (normalize rsegs mem) /\
  Frame.stk rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) /\
  Mem.wr_at rsegs (normalize rsegs mem) (g_S g - 65536) 65536.
Proof.
  intros g km hb L A regs mem md HFR.
  pose proof FF_segs as SEG.
  destruct HFR as (HGV & H2 & _ & _ & _ & HSTK & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as HAC.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HRO : ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEG in HMI; exact HMI).
  split; [exact HRO|].
  split; [rewrite H2; unfold fsp, SLOT_FRAME; reflexivity|].
  split; [lia|]. split; [lia|]. split; [exact HS16|].
  split; [apply mem_inv_normalize|].
  split.
  { apply (proj1 (stk_rel_sh2 mem (normalize rsegs mem) (g_S g - 65536) (g_S g) (mem_rel_normalize rsegs mem HRO)
      ltac:(lia) ltac:(lia))).
    exact HSTK. }
  split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hro : Mem.ro_addr rsegs (wa (g_S g - 65536 + i)) = false)
    by (apply ro_hi_sh2; rewrite wa_unsigned by lia; lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem HRO) Hro).
  pose proof (HWIN (g_S g - 65536 + i) ltac:(lia)) as W. unfold writable_at in W. rewrite SEG in W. exact W.
Qed.

Lemma OUTS_keep : forall g km nm tk dp L A regs mem md m0 m',
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  Frame.munch (SWIN g) (normalize rsegs mem) m0 -> mem_rel rsegs m' m0 ->
  OUTS g nm tk dp mem -> OUTS g nm tk dp m'.
Proof.
  intros g km nm tk dp L A regs mem md m0 m' HFR HPM HMU HREL HO Hr.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & HS47 & _).
  pose proof alloc_ceiling_value as HAC.
  assert (HRO : ro_agree rsegs mem) by (unfold MI in HMI; rewrite FF_segs in HMI; exact HMI).
  destruct (nr0_fits (g_in g) Hr) as (Hw & H1 & H2 & H3).
  destruct (HO Hr) as (C1 & C2 & C3).
  assert (BL : forall a n, In (a, n) (NMB g nm tk dp) -> 0 <= a /\ a + n <= alloc_ceiling).
  { intros a n Hin.
    assert (Hin' : In (a, n) (blocks L A))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPM | apply in_or_app; left; exact Hin]).
    unfold blocks in Hin'. apply in_map_iff in Hin' as ([p n'] & Eq & Hq). cbn [fst snd] in Eq.
    injection Eq as <- <-.
    destruct (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ p n' HMR Hq). lia. }
  unfold NMB in BL.
  pose proof (BL nm _ ltac:(left; reflexivity)) as B1.
  pose proof (BL tk _ ltac:(right; left; reflexivity)) as B2.
  pose proof (BL dp _ ltac:(right; right; left; reflexivity)) as B3.
  unfold bsz in B1, B2, B3.
  pose proof (TK_len (g_in g)) as TL.
  unfold cstr in *.
  assert (KB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= alloc_ceiling ->
    bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs).
  { intros a bs Ha Hl Hb. apply (keep_bytes (SWIN g) mem m0 m' a bs HRO HMU HREL); [|exact Hb].
    unfold SWIN, SLOT_K, SLOT_STACK in *. cbn [disjoint_from]. split; [left; lia | exact I]. }
  unfold n_ln, n_ld, zlen in *.
  split; [|split]; apply KB; try assumption; rewrite ?length_app; cbn [length]; lia.
Qed.

End T.
