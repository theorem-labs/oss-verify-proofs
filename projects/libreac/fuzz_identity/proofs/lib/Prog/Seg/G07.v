From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge Cells Arr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv
  disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Definition sdZ (inp : list byte) : list Z := if n_said inp then map bz (name_str (idT inp)) else [].

Lemma g7_zb_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma g7_bb : forall l, bn_bytes (map bz l) = l.
Proof.
  intros l. unfold bn_bytes. rewrite map_map. rewrite (map_ext _ (fun x => x)) by (intros; apply g7_zb_bz).
  apply map_id.
Qed.

Lemma g7_bb_app0 : forall l, bn_bytes (map bz l ++ [0]) = l ++ [z8].
Proof. intros l. unfold bn_bytes. rewrite map_app. fold (bn_bytes (map bz l)). rewrite g7_bb. reflexivity. Qed.

Lemma g7_leq_eq : forall a b, bn_leq a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [bn_leq] in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.

Lemma g7_leq_map : forall a b, bn_leq (map bz a) (map bz b) = bytes_eqb a b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [map bn_leq bytes_eqb]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma g7_skipn_map : forall (f : byte -> Z) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma g7_dec : forall x, 0 <= x <= 40 -> bn_dec x 1 = map bz (DEC x 1) /\ bn_dec x 2 = map bz (DEC x 2).
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => bn_leq (bn_dec x 1) (map bz (DEC x 1)) && bn_leq (bn_dec x 2) (map bz (DEC x 2)))
    (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply g7_leq_eq; assumption.
Qed.

Lemma g7_STEM : forall f, bn_STEM f = map bz (stem_img f).
Proof.
  intros f. unfold bn_STEM, stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma g7_stem : forall inp, bn_stem (n_fam inp) (sdZ inp) = map bz (n_stem inp).
Proof.
  intros inp. unfold sdZ, n_stem, n_use_said. destruct (n_said inp); cbn [andb].
  - unfold name_str. destruct (model_name (idT inp)) as [|b r].
    + cbn [first_zero firstn map bn_stem]. assert (E : negb (bz (nthb [] 0) =? 0) = false) by reflexivity.
      rewrite E. apply g7_STEM.
    + cbn [first_zero]. unfold nthb. cbn [nth]. destruct (bz b =? 0).
      * cbn [firstn map bn_stem negb]. apply g7_STEM.
      * cbn [firstn map bn_stem negb]. reflexivity.
  - cbn [bn_stem]. apply g7_STEM.
Qed.

Lemma g7_NM : forall inp, n_wok inp = true ->
  bn_NM (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) = map bz (n_EXP_NM inp).
Proof.
  intros inp W. destruct (wok_chans inp W) as [Hi Ho].
  unfold bn_NM. rewrite g7_stem. unfold bn_w4.
  destruct (g7_dec _ Hi) as [_ Di]. destruct (g7_dec _ Ho) as [_ Do]. rewrite Di, Do, <- map_app.
  change (DEC (t_in inp) 2 ++ DEC (t_out inp) 2) with (n_W4 inp). cbv zeta.
  rewrite length_map, g7_skipn_map, g7_leq_map.
  unfold n_EXP_NM, n_ends_w4.
  rewrite (firstn_all2 (n := 4%nat) (n_W4 inp))
    by (unfold n_W4; rewrite length_app, (DEC2_len _ Hi), (DEC2_len _ Ho); lia).
  assert (E4 : (4 <=? Z.of_nat (length (n_stem inp))) = (4 <=? length (n_stem inp))%nat).
  { destruct (Z.leb_spec 4 (Z.of_nat (length (n_stem inp)))); destruct (Nat.leb_spec 4 (length (n_stem inp)));
      reflexivity || lia. }
  rewrite E4.
  destruct (_ && _); [reflexivity|]. rewrite !map_app. reflexivity.
Qed.

Lemma g7_lower : forall b, bz (lower b) = if (65 <=? bz b) && (bz b <=? 90) then bz b + 32 else bz b.
Proof.
  intro b. unfold lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
  unfold zb, bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. unfold bz in *. lia.
Qed.

Lemma g7_tk : forall l d, bn_tk d (map bz l) = map bz (tok_go d l).
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|]. cbn [map bn_tk tok_go].
  rewrite andb_comm. destruct (negb d && (bz b =? 45)); [apply IH|].
  cbn [map]. rewrite g7_lower, IH. reflexivity.
Qed.

Lemma g7_DP : forall inp, n_wok inp = true ->
  bn_DP (map bz (n_EXP_NM inp)) (t_in inp) (t_out inp) = map bz (n_EXP_DP inp).
Proof.
  intros inp W. destruct (wok_chans inp W) as [Hi Ho].
  destruct (g7_dec _ Hi) as [Di _]. destruct (g7_dec _ Ho) as [Do _].
  unfold bn_DP, n_EXP_DP. rewrite Di, Do. rewrite !map_app. reflexivity.
Qed.

Lemma g7_has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.

Lemma g7_tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|].
  assert (HD : has_dash (b :: r) = (bz b =? 45) || has_dash r) by reflexivity. rewrite HD. destruct d.
  - cbn [tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
  - destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb Datatypes.length]; rewrite E; cbn [andb orb].
    + rewrite IH. cbn [negb andb]. lia.
    + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
      pose proof (g7_has_dash_len r D). lia.
Qed.

Lemma g7_tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite g7_tok_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (g7_has_dash_len _ D). lia.
Qed.

Lemma g7_n_r : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.

Lemma g7_n_r0 : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.

Lemma g7_accept : forall inp nm tk dp, nm <> 0 -> tk <> 0 -> dp <> 0 ->
  bn_accept (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) nm (t_cap_name inp) tk (t_cap_tok inp) dp (t_cap_disp inp) =
  (n_r inp =? 0).
Proof.
  intros inp nm tk dp Hn Ht Hd.
  unfold bn_accept, bn_args_ok, n_r. change bn_ok with okw.
  rewrite (proj2 (Z.eqb_neq nm 0) Hn), (proj2 (Z.eqb_neq tk 0) Ht), (proj2 (Z.eqb_neq dp 0) Hd).
  cbn [negb andb].
  destruct (n_wok inp) eqn:W.
  - pose proof W as W'. unfold n_wok in W'. apply andb_true_iff in W' as [W1 W3]. apply andb_true_iff in W1 as [W1 W2].
    rewrite W1, W2, W3.
    assert (R0 : bn_ret (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) = 0).
    { unfold bn_ret. change bn_ok with okw. rewrite W1, W2, W3, (g7_NM inp W), length_map.
      pose proof (n_ln_le inp W) as HL.
      unfold n_ln in HL. destruct (Z.leb_spec (Z.of_nat (length (n_EXP_NM inp))) 23); [reflexivity | lia]. }
    rewrite R0. rewrite (g7_NM inp W). unfold bn_TK. rewrite g7_tk. rewrite (g7_DP inp W). rewrite !length_map.
    change (tok_go false (n_EXP_NM inp)) with (n_TK inp).
    change (Z.of_nat (length (n_EXP_NM inp))) with (n_ln inp).
    change (Z.of_nat (length (n_EXP_DP inp))) with (n_ld inp). rewrite g7_tk_len.
    pose proof (n_ln_le inp W) as HL.
    assert (HT : 0 <= n_lt inp) by (pose proof (g7_tk_len inp); lia).
    assert (HD : 0 <= n_ld inp) by (unfold n_ld; lia).
    unfold n_fits. cbn [andb].
    destruct (Z.eqb_spec (t_cap_name inp) 0); destruct (Z.eqb_spec (t_cap_tok inp) 0);
      destruct (Z.eqb_spec (t_cap_disp inp) 0);
      destruct (Z.ltb_spec (n_ln inp) (t_cap_name inp)); destruct (Z.ltb_spec (n_lt inp) (t_cap_tok inp));
      destruct (Z.ltb_spec (n_ld inp) (t_cap_disp inp)); cbn; try reflexivity; lia.
  - revert W. unfold n_wok.
    destruct (okw (t_in inp)); destruct (okw (t_out inp)); destruct (negb ((t_in inp =? 0) && (t_out inp =? 0)));
      cbn [andb]; intros W; try discriminate W; rewrite ?andb_false_r; cbn [andb]; reflexivity.
Qed.

Lemma g7_acc_len : forall f sd i o nm nl tk tl dp dl, bn_accept f sd i o nm nl tk tl dp dl = true ->
  Z.of_nat (length (bn_NM f sd i o)) < nl /\ Z.of_nat (length (bn_TK (bn_NM f sd i o))) < tl /\
  Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) < dl.
Proof.
  intros f sd i o nm nl tk tl dp dl H. unfold bn_accept in H.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [_ H3].
  apply Z.ltb_lt in H3, H4, H5. split; [exact H3|]. split; [exact H4 | exact H5].
Qed.

Lemma g7_model_name_len : forall idb, length idb = ID_SIZE -> length (model_name idb) = 17%nat.
Proof.
  intros idb H. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite length_firstn, length_skipn.
  unfold ID_SIZE in H. lia.
Qed.

Lemma g7_firstn_S_nth : forall (l : list byte) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H; cbn [Datatypes.length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma g7_bytes_fs : forall m a l k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n (H1 & H2 & H) Hkn.
  assert (Hlen : length (firstn n (skipn k l)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. rewrite Hlen in Hi.
  rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite H by lia.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma g7_first_zero_nth : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
  induction l as [|x l IH]; cbn [first_zero Datatypes.length]; intros H; [lia|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.

Lemma g7_name_nz : forall l b, In b (firstn (first_zero l) l) -> bz b <> 0.
Proof.
  induction l as [|x l IH]; intros b H; [destruct H|]. cbn [first_zero] in H.
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [destruct H|].
  cbn [firstn In] in H. destruct H as [<-|H]; [exact E | exact (IH b H)].
Qed.

Lemma g7_name_cstr : forall m a idb, bytes_at rsegs m a idb -> length idb = ID_SIZE -> bz (nthb idb 19) = 0 ->
  cstr m (a + 3) (name_str idb).
Proof.
  intros m a idb H Hl H19. pose proof (g7_model_name_len idb Hl) as Lm.
  assert (Hm : nth 16 (model_name idb) (zb 0) = nth 19 idb (zb 0)).
  { unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
    rewrite (nth_skip0 (skipn 3 idb)), skipn_skipn, <- nth_skip0. reflexivity. }
  assert (Hf : (first_zero (model_name idb) <= 16)%nat).
  { apply first_zero_le; [lia|]. rewrite Hm. exact H19. }
  assert (Hz : nth (first_zero (model_name idb)) (model_name idb) (zb 0) = z8).
  { pose proof (g7_first_zero_nth (model_name idb) ltac:(lia)) as E.
    rewrite <- (g7_zb_bz (nth _ (model_name idb) (zb 0))). rewrite E. reflexivity. }
  unfold cstr, name_str. rewrite <- Hz. rewrite <- g7_firstn_S_nth by lia.
  unfold model_name, get, OFF_NAME, NAME_CAP. rewrite firstn_firstn.
  replace (Nat.min (S (first_zero (firstn 17 (skipn 3 idb)))) 17) with (S (first_zero (firstn 17 (skipn 3 idb))))
    by (unfold model_name, get, OFF_NAME, NAME_CAP in Hf; lia).
  change 3 with (Z.of_nat 3). apply g7_bytes_fs; [exact H|].
  unfold model_name, get, OFF_NAME, NAME_CAP in Hf. unfold ID_SIZE in Hl. lia.
Qed.

Lemma g7_rw : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (a + i) /\ wview rsegs m (wa (a + i)) <> None /\
     Mem.ro_addr rsegs (wa (a + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) a [Cells.CB n (sf_rd_list m a n)].
Proof.
  intros m a n Ha Hn H.
  rewrite <- (sf_rd_list_len m n a) at 1. apply rw_cells_of_u8arr. split.
  - split; [exact Ha|]. split; [rewrite sf_rd_list_len; exact Hn|]. intros i Hi. rewrite sf_rd_list_len in Hi.
    rewrite sf_rd_list_nth by exact Hi. destruct (H (Z.of_nat i) ltac:(lia)) as ((b & Hb) & _ & Hro).
    unfold mrd, normalize. rewrite Hro. unfold wa. rewrite Hb. reflexivity.
  - split; [exact Ha|]. split; [rewrite sf_rd_list_len; exact Hn|]. intros i Hi. rewrite sf_rd_list_len in Hi.
    destruct (H i ltac:(lia)) as (_ & Hw & Hro). unfold wview, normalize. rewrite Hro. exact Hw.
Qed.

Section KA.
Context {fx : YK11.FPState}.

Lemma G07_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp f said i o nm nl tk tl dp dl lo : Z) (sd : list Z),
  reac_box_name_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 (-1) -> x26 = Z_to_bv 64 f -> x25 = Z_to_bv 64 said ->
  x9 = Z_to_bv 64 i -> x18 = Z_to_bv 64 o -> x20 = Z_to_bv 64 nm -> x24 = Z_to_bv 64 nl ->
  x21 = Z_to_bv 64 tk -> x23 = Z_to_bv 64 tl -> x22 = Z_to_bv 64 dp -> x27 = Z_to_bv 64 dl ->
  0 <= f < 128 -> 0 <= i < 256 -> 0 <= o < 256 -> 0 <= said < 2 ^ 64 -> 0 <= nm < 2 ^ 64 -> 0 <= nl < 2 ^ 64 ->
  0 <= tk < 2 ^ 64 -> 0 <= tl < 2 ^ 64 -> 0 <= dp < 2 ^ 64 -> 0 <= dl < 2 ^ 64 ->
  IMG_HI <= lo -> lo + 288 <= sp -> sp + 368 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> wr_at rsegs m sp 368 ->
  bytes_at rsegs m BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)) ->
  (forall m2, (forall x, ~ (sp <= bv_unsigned x < sp + 16) -> m2 x = m x) -> wmono rsegs m m2 -> ro_agree rsegs m2 ->
     bn_said (normalize rsegs m2) (sp - 288) sp said sd /\
     bn_bufs (normalize rsegs m2) (sp - 288) sp nm nl tk tl dp dl) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x137c0) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 x19
                x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 /\
          exists m2, munch [(sp, sp + 16)] m m2 /\ wmono rsegs m m2 /\
            bytes_at rsegs m2 sp (le8 (Z_to_bv 64 dp)) /\ bytes_at rsegs m2 (sp + 8) (le8 (Z_to_bv 64 dl)) /\
            wmono rsegs m2 m' /\
            (if bn_accept f sd i o nm nl tk tl dp dl
             then r = Z_to_bv 64 0 /\
                  munch [(sp - 288, sp);
                         (nm, nm + Z.of_nat (length (bn_NM f sd i o)) + 1);
                         (tk, tk + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1);
                         (dp, dp + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1)] m2 m' /\
                  bytes_at rsegs m' nm (bn_bytes (bn_NM f sd i o ++ [0])) /\
                  bytes_at rsegs m' tk (bn_bytes (bn_TK (bn_NM f sd i o) ++ [0])) /\
                  bytes_at rsegs m' dp (bn_bytes (bn_DP (bn_NM f sd i o) i o ++ [0]))
             else r = Z_to_bv 64 (-1) /\ munch [(sp - 288, sp)] m2 m')) /\
       pc' = Z_to_bv 64 0x137c0 /\ ro_agree rsegs m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x1378c) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp f said i o nm nl tk tl dp dl lo sd BN HRO E2 E10 E26 E25 E9 E18 E20 E24 E21 E23 E22 E27
    Hf Hi Ho Hsd Hnm Hnl Htk Htl Hdp Hdl HLO HL Hsp Hal ST WR HT PRE.
  subst x2 x10 x26 x25 x9 x18 x20 x24 x21 x23 x22 x27.
  unfold IMG_HI in HLO.
  step. step.
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; vm_compute; reflexivity); cbv iota
  end.
  pose proof (wr_at_store_ok rsegs m sp 368 0 8 WR ltac:(lia) ltac:(lia)) as HS. rewrite Z.add_0_r in HS.
  step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa _) _) =>
    replace aa with (Z_to_bv 64 sp) by (first [reflexivity | f_equal; lia])
  end.
  remember (write_to_mem m (Z_to_bv 64 sp) (le8 (Z_to_bv 64 dp))) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 368) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 sp (le8 (Z_to_bv 64 dp)))
    by (rewrite Em1; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (R1 : ro_agree rsegs m1).
  { rewrite Em1. apply sf_ro_write; [exact HRO | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S1 : stk rsegs m1 lo sp) by (rewrite Em1; apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (M1 : munch [(sp, sp + 16)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  assert (T1 : bytes_at rsegs m1 BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3))).
  { rewrite Em1. apply bytes_at_write_other; [exact HT | lia | rewrite length_le8; lia |].
    rewrite !length_app, !length_le8. unfold BN_TS. lia. }
  clear Em1.
  pose proof (wr_at_store_ok rsegs m1 sp 368 8 8 W1 ltac:(lia) ltac:(lia)) as HS2.
  step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa _) _) =>
    replace aa with (Z_to_bv 64 (sp + 8)) by (first [reflexivity | f_equal; lia])
  end.
  remember (write_to_mem m1 (Z_to_bv 64 (sp + 8)) (le8 (Z_to_bv 64 dl))) as m2 eqn:Em2.
  assert (B2 : bytes_at rsegs m2 (sp + 8) (le8 (Z_to_bv 64 dl)))
    by (rewrite Em2; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (B1' : bytes_at rsegs m2 sp (le8 (Z_to_bv 64 dp))).
  { rewrite Em2. apply bytes_at_write_other; [exact B1 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (R2 : ro_agree rsegs m2).
  { rewrite Em2. apply sf_ro_write; [exact R1 | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S2 : stk rsegs m2 lo sp) by (rewrite Em2; apply stk_write; [exact S1 | lia | rewrite length_le8; lia]).
  assert (M2 : munch [(sp, sp + 16)] m m2).
  { rewrite Em2. apply munch_write; [exact M1 | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM2 : wmono rsegs m m2) by (rewrite Em2; apply wmono_write; exact WM1).
  assert (T2 : bytes_at rsegs m2 BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3))).
  { rewrite Em2. apply bytes_at_write_other; [exact T1 | lia | rewrite length_le8; lia |].
    rewrite !length_app, !length_le8. unfold BN_TS. lia. }
  clear Em2.
  assert (EQ2 : forall x, ~ (sp <= bv_unsigned x < sp + 16) -> m2 x = m x).
  { intros x Hx. apply M2. cbn [outside]. split; [exact Hx | exact I]. }
  destruct (PRE m2 EQ2 WM2 R2) as [PS PB].
  step. step. step. step. step. step. step. step. step.
  eapply (sf_box_name_call BN) with (lo := lo) (f := f) (i := i) (o := o) (display := Z_to_bv 64 dp)
    (display_len := Z_to_bv 64 dl) (sd := sd).
  - exact R2.
  - reflexivity.
  - lia.
  - reflexivity.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (unsigned_lit sp) by lia. apply bytes_at_app. split; [exact B1'|].
    rewrite length_le8. replace (sp + Z.of_nat 8) with (sp + 8) by lia. exact B2.
  - rewrite (unsigned_lit sp) by lia. exact S2.
  - rewrite (unsigned_lit sp) by lia. unfold BN_K. lia.
  - rewrite (unsigned_lit sp) by lia. exact Hal.
  - unfold IMG_HI. lia.
  - exact T2.
  - intros _. rewrite !unsigned_lit by lia. unfold BN_K. split; [exact PS | exact PB].
  - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' WM RO HIF.
    rewrite !unsigned_lit in HIF by lia. unfold BN_K in HIF.
    rewrite sf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split.
    { do 15 eexists. split; [reflexivity|]. exists m2.
      split; [exact M2|]. split; [exact WM2|]. split; [exact B1'|]. split; [exact B2|].
      split; [exact WM | exact HIF]. }
    split; [reflexivity | exact RO].
Qed.

End KA.

Section G07.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BN : reac_box_name_contract.

Lemma g7_blk : forall g km nm tk dp L A regs mem md a k,
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) -> In (a, k) (NMB g nm tk dp) ->
  4096 <= a /\ a + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> present mem (a + i) /\ wview rsegs mem (wa (a + i)) <> None /\
     Mem.ro_addr rsegs (wa (a + i)) = false).
Proof.
  intros g km nm tk dp L A regs mem md a k HF HP Hin.
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md a k HF HP Hin) as (HBW & H1 & H2 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  split; [exact H1|]. split; [exact H2|]. intros i Hi. destruct (HBW i Hi) as (W & P & N).
  split; [exact P|]. split; [rewrite SEG in W; exact W|].
  destruct (Mem.ro_addr rsegs (wa (a + i))) eqn:E; [|reflexivity].
  exfalso. apply N. pose proof (sf_ro_img B APIf ra empty FF _ E) as Hi'. rewrite wa_unsigned in Hi' by lia. exact Hi'.
Qed.

Lemma g7_disj : forall g km nm tk dp L A regs mem md,
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  ranges_disjoint (nm, bsz (t_cap_name (g_in g))) (tk, bsz (t_cap_tok (g_in g))) /\
  ranges_disjoint (nm, bsz (t_cap_name (g_in g))) (dp, bsz (t_cap_disp (g_in g))) /\
  ranges_disjoint (tk, bsz (t_cap_tok (g_in g))) (dp, bsz (t_cap_disp (g_in g))).
Proof.
  intros g km nm tk dp L A regs mem md HF HP.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws (APIf rc)) L A mem md HMR) as PW.
  assert (Hs : forall a b, ranges_disjoint a b -> ranges_disjoint b a) by (intros a b H; unfold ranges_disjoint in *; lia).
  pose proof (sf_pw_perm _ Hs _ _ HP PW) as PW'. unfold NMB in PW'. cbn [app pairwise] in PW'.
  destruct PW' as (P1 & P2 & _).
  split; [apply P1; left; reflexivity|]. split; [apply P1; right; left; reflexivity|]. apply P2. left. reflexivity.
Qed.

Lemma g7_pre : forall g km nm tk dp L A regs mem md,
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) -> TID g mem ->
  forall m2, (forall x, ~ (fsp g <= bv_unsigned x < fsp g + 16) -> m2 x = mem x) -> wmono rsegs mem m2 ->
  ro_agree rsegs m2 ->
  bn_said (normalize rsegs m2) (fsp g - 288) (fsp g) (said_v g) (sdZ (g_in g)) /\
  bn_bufs (normalize rsegs m2) (fsp g - 288) (fsp g) nm (t_cap_name (g_in g)) tk (t_cap_tok (g_in g))
          dp (t_cap_disp (g_in g)).
Proof.
  intros g km nm tk dp L A regs mem md HF HP HTID m2 EQ WM R2.
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. unfold IMG_HI in HI.
  assert (BT : forall a bs, bytes_at rsegs mem a bs -> (a + Z.of_nat (length bs) <= fsp g \/ fsp g + 16 <= a) ->
                 bytes_at rsegs m2 a bs).
  { intros a bs H Hd. pose proof H as (H1 & H2 & _). apply (sf_bytes_same rsegs mem m2 a bs); [|exact H].
    intros i Hi. apply EQ. rewrite unsigned_lit by lia. lia. }
  split.
  - unfold said_v, sdZ. destruct (n_said (g_in g)) eqn:NS.
    + right. split; [unfold spk; lia|].
      set (idb := idT (g_in g)).
      pose proof HTID as (_ & HID). unfold IDb in HID. change (rec_id (g_in g) (NRn g)) with idb in HID.
      assert (Lid : length idb = ID_SIZE) by apply rec_id_length.
      pose proof (rec_id_b19 (g_in g) (NRn g)) as H19. change (rec_id (g_in g) (NRn g)) with idb in H19.
      assert (HID2 : bytes_at rsegs m2 (spk g 130) idb).
      { apply BT; [exact HID | unfold spk; lia]. }
      pose proof (name_str_len (g_in g) (NRn g)) as Hlen. change (rec_id (g_in g) (NRn g)) with idb in Hlen.
      set (len := length (name_str idb)) in *.
      set (k := Z.to_nat ((- (spk g 133 + Z.of_nat len + 1)) mod 8)).
      pose proof (Z.mod_pos_bound (- (spk g 133 + Z.of_nat len + 1)) 8 ltac:(lia)) as HM.
      assert (Hk : (k <= 7)%nat) by (unfold k; lia).
      split.
      { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
        pose proof (bz_range b). unfold name_str in Hb. pose proof (g7_name_nz _ _ Hb). lia. }
      exists (firstn k (skipn (4 + len) idb)).
      split.
      { rewrite g7_bb. replace (name_str idb ++ Z_to_bv 8 0 :: firstn k (skipn (4 + len) idb))
          with ((name_str idb ++ [z8]) ++ firstn k (skipn (4 + len) idb)) by (rewrite <- app_assoc; reflexivity).
        apply bytes_at_normalize; [exact R2|]. apply bytes_at_app. split.
        - pose proof (g7_name_cstr m2 _ idb HID2 Lid H19) as C. unfold cstr, spk in C |- *.
          replace (fsp g + 133) with (fsp g + 130 + 3) by lia. exact C.
        - rewrite length_app. cbn [Datatypes.length]. fold len.
          pose proof (g7_bytes_fs m2 _ idb (4 + len) k HID2 ltac:(unfold ID_SIZE in Lid; lia)) as F.
          unfold spk in F |- *. replace (fsp g + 133 + Z.of_nat (len + 1)) with (fsp g + 130 + Z.of_nat (4 + len))
            by lia. exact F. }
      rewrite length_map. fold len. rewrite length_firstn, length_skipn.
      split.
      { unfold ID_SIZE in Lid. rewrite Lid. replace (Nat.min k (38 - (4 + len))) with k by lia. unfold k.
        rewrite Z2Nat.id by lia. unfold spk. lia. }
      cbn [disjoint_from]. split; [right; unfold spk; lia | exact I].
    + left. split; reflexivity.
  - destruct (g7_disj g km nm tk dp L A regs mem md HF HP) as (D1 & D2 & D3).
    unfold ranges_disjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3.
    destruct (g7_blk g km nm tk dp L A regs mem md nm _ HF HP ltac:(left; reflexivity)) as (N1 & N2 & NB).
    destruct (g7_blk g km nm tk dp L A regs mem md tk _ HF HP ltac:(right; left; reflexivity)) as (K1 & K2 & KB).
    destruct (g7_blk g km nm tk dp L A regs mem md dp _ HF HP ltac:(right; right; left; reflexivity))
      as (P1 & P2 & PB).
    assert (Cn : 0 <= t_cap_name (g_in g) < 40) by (unfold t_cap_name; apply Z.mod_pos_bound; lia).
    assert (Ct : 0 <= t_cap_tok (g_in g) < 40) by (unfold t_cap_tok; apply Z.mod_pos_bound; lia).
    assert (Cd : 0 <= t_cap_disp (g_in g) < 64) by (unfold t_cap_disp; apply Z.mod_pos_bound; lia).
    assert (TR : forall a k, 4096 <= a -> a + k <= alloc_ceiling ->
              (forall i, 0 <= i < k -> present mem (a + i) /\ wview rsegs mem (wa (a + i)) <> None /\
                 Mem.ro_addr rsegs (wa (a + i)) = false) ->
              forall n, (n <= k)%Z -> 0 <= n ->
              exists j, rw_cells rsegs (normalize rsegs m2) a [Cells.CB (Z.to_nat n) j]).
    { intros a k Ha1 Ha2 HB n Hn Hn0. exists (sf_rd_list m2 a (Z.to_nat n)).
      apply g7_rw; [lia | rewrite Z2Nat.id by lia; lia |]. intros i Hi. rewrite Z2Nat.id in Hi by lia.
      destruct (HB i ltac:(lia)) as ((b & Hb) & Hw & Hro). split; [|split; [|exact Hro]].
      - exists b. rewrite EQ; [exact Hb|]. rewrite unsigned_lit by lia. lia.
      - apply WM. exact Hw. }
    unfold bn_bufs, bsz in *.
    split; [apply (TR nm _ N1 N2 NB); lia|].
    split; [apply (TR tk _ K1 K2 KB); lia|].
    split; [apply (TR dp _ P1 P2 PB); lia|].
    cbn [disjoint_from].
    split; [repeat split; lia|]. split; [repeat split; lia|]. repeat split; lia.
Qed.

Lemma seg_G07 : Hcut B APIf ra (Inv_K137c0 B APIf ra empty) -> Hcut B APIf ra (Inv_K1378c B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & L & A & regs & mem & md & -> & HF & HP & (HG & H10)).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HG as (HTID & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H40 & HQ0 & HQ8).
  set (inp := g_in g) in *.
  destruct (g7_blk g _ nm tk dp L A regs mem md nm _ HF HP ltac:(left; reflexivity)) as (N1 & N2 & _).
  destruct (g7_blk g _ nm tk dp L A regs mem md tk _ HF HP ltac:(right; left; reflexivity)) as (K1 & K2 & _).
  destruct (g7_blk g _ nm tk dp L A regs mem md dp _ HF HP ltac:(right; right; left; reflexivity)) as (P1 & P2 & _).
  assert (Cn : 0 <= t_cap_name inp < 40) by (unfold t_cap_name; apply Z.mod_pos_bound; lia).
  assert (Ct : 0 <= t_cap_tok inp < 40) by (unfold t_cap_tok; apply Z.mod_pos_bound; lia).
  assert (Cd : 0 <= t_cap_disp inp < 64) by (unfold t_cap_disp; apply Z.mod_pos_bound; lia).
  pose proof (sf_nfam_range inp) as Hfam.
  pose proof (inb_range inp (cT inp + 1)) as Hin. pose proof (inb_range inp (cT inp + 2)) as Hout.
  change (inb inp (cT inp + 1)) with (t_in inp) in Hin. change (inb inp (cT inp + 2)) with (t_out inp) in Hout.
  assert (Hsd : 0 <= said_v g < 2 ^ 64) by (unfold said_v, spk, IMG_HI in *; destruct (n_said (g_in g)); lia).
  assert (WR : wr_at rsegs mem (fsp g) 368).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  pose proof (sf_bn_ts B APIf ra empty FF mem Hrel) as HT.
  unfold bsz in N2, K2, P2.
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x1378c) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (G07_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (n_fam inp) (said_v g)
             (t_in inp) (t_out inp) nm (t_cap_name inp) tk (t_cap_tok inp) dp (t_cap_disp inp) (g_S g - SLOT_K)
             (sdZ inp) BN).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (sf_getr_reg regs 26) by reflexivity. exact H26.
    - rewrite <- (sf_getr_reg regs 25) by reflexivity. exact H25.
    - rewrite <- (sf_getr_reg regs 9) by reflexivity. exact H9.
    - rewrite <- (sf_getr_reg regs 18) by reflexivity. exact H18.
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (sf_getr_reg regs 24) by reflexivity. exact H24.
    - rewrite <- (sf_getr_reg regs 21) by reflexivity. exact H21.
    - rewrite <- (sf_getr_reg regs 23) by reflexivity. exact H23.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - rewrite <- (sf_getr_reg regs 27) by reflexivity. exact H27.
    - lia.
    - lia.
    - lia.
    - exact Hsd.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HI.
    - lia.
    - lia.
    - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - exact ST.
    - exact WR.
    - exact HT.
    - intros m2 EQ WM2 R2. exact (g7_pre g _ nm tk dp L A regs mem md HF HP HTID m2 EQ WM2 R2). }
  intros R pc' m' regs1 (Hreg & -> & RO) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> &
    m2 & M2 & WM2 & BQ0 & BQ8 & WM & HIF).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  assert (G10 : getr regs1 10 = r) by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  rewrite (g7_accept inp nm tk dp ltac:(lia) ltac:(lia) ltac:(lia)) in HIF.
  set (W := [(fsp g - 288, fsp g + 16); (nm, nm + bsz (t_cap_name inp)); (tk, tk + bsz (t_cap_tok inp));
             (dp, dp + bsz (t_cap_disp inp))]).
  assert (HWin : forall lo hi y, In (lo, hi) W -> lo <= y < hi ->
            (fsp g - 288 <= y < fsp g + 16) \/ in_hb (NMB g nm tk dp) y).
  { intros lo hi y Hy Hr. unfold W in Hy. destruct Hy as [Hy|[Hy|[Hy|[Hy|[]]]]]; injection Hy as <- <-;
      [left; lia | right | right | right].
    - exists nm, (bsz (t_cap_name inp)). split; [left; reflexivity | lia].
    - exists tk, (bsz (t_cap_tok inp)). split; [right; left; reflexivity | lia].
    - exists dp, (bsz (t_cap_disp inp)). split; [right; right; left; reflexivity | lia]. }
  assert (HWb : forall lo hi y, In (lo, hi) W -> lo <= y < hi -> y < fsp g + 16).
  { intros lo hi y Hy Hr. destruct (HWin lo hi y Hy Hr) as [H|(a & k & Hk & Ha)]; [lia|].
    unfold NMB in Hk. unfold bsz in *. destruct Hk as [Hk|[Hk|[Hk|[]]]]; injection Hk as <- <-; lia. }
  set (W' := [(fsp g - 288, fsp g); (nm, nm + bsz (t_cap_name inp)); (tk, tk + bsz (t_cap_tok inp));
              (dp, dp + bsz (t_cap_disp inp))]).
  assert (MU' : munch W' m2 m' /\ (n_r inp = 0 ->
            cstr m' nm (n_EXP_NM inp) /\ cstr m' tk (n_TK inp) /\ cstr m' dp (n_EXP_DP inp)) /\ r = Z_to_bv 64 (n_r inp)).
  { revert HIF. destruct (Z.eqb_spec (n_r inp) 0) as [R0|R0]; intros HIF.
    - destruct (g7_n_r0 inp R0) as [Wk Ft].
      unfold n_fits in Ft. apply andb_true_iff in Ft as [Ft F3]. apply andb_true_iff in Ft as [F1 F2].
      apply Z.ltb_lt in F1, F2, F3.
      destruct HIF as (Er & MU & BN1 & BT1 & BD1).
      rewrite (g7_NM inp Wk) in MU, BN1, BT1, BD1. unfold bn_TK in MU, BT1. rewrite g7_tk in MU, BT1.
      rewrite (g7_DP inp Wk) in MU, BD1. rewrite !length_map in MU.
      change (tok_go false (n_EXP_NM inp)) with (n_TK inp) in MU, BT1.
      rewrite g7_tk_len in MU. change (Z.of_nat (length (n_EXP_NM inp))) with (n_ln inp) in MU.
      change (Z.of_nat (length (n_EXP_DP inp))) with (n_ld inp) in MU.
      rewrite !g7_bb_app0 in BN1, BT1, BD1.
      split.
      { eapply munch_weaken; [|exact MU]. unfold W', bsz. sf_subfp. }
      split; [intros _; split; [exact BN1 | split; [exact BT1 | exact BD1]]|].
      rewrite R0. exact Er.
    - destruct HIF as (Er & MU).
      split.
      { eapply munch_weaken; [|exact MU]. unfold W', bsz. sf_subfp. }
      split; [intros E; exfalso; exact (R0 E)|].
      destruct (g7_n_r inp) as [E|E]; [exfalso; exact (R0 E)|]. rewrite E. exact Er. }
  destruct MU' as (MU' & OUT0 & Er).
  assert (MU : munch W mem m').
  { apply (munch_trans _ mem m2 m'); eapply munch_weaken; [|exact M2| |exact MU']; unfold W, W', bsz; sf_subfp. }
  assert (OUT : FRout g W).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr) as Hw. unfold spk.
    destruct Hw as [Hw|(a & k & Hk & Ha)]; [lia|].
    unfold NMB in Hk. unfold bsz in *. destruct Hk as [Hk|[Hk|[Hk|[]]]]; injection Hk as <- <-; lia. }
  assert (BS : forall a bs, bytes_at rsegs mem a bs -> fsp g + 16 <= a -> bytes_at rsegs m' a bs).
  { intros a bs H Ha. apply (sf_bytes_munchP (fun y => y < fsp g + 16) W mem m' a bs MU HWb); [|exact H].
    intros i Hi. lia. }
  apply HX. exists nm, tk, dp, L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' W HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU (wmono_trans _ _ _ _ WM2 WM)).
    intros lo hi y Hy Hr. destruct (HWin lo hi y Hy Hr) as [H|H]; [left; lia | right; exact H]. }
  split; [exact HP|].
  split; [|split; [rewrite G10; exact Er | intros R0; exact (OUT0 R0)]].
  split; [exact (sf_TID_munch g W mem m' MU OUT HTID)|].
  split; [sf_k KP1 8; exact H8|]. split; [sf_k KP1 9; exact H9|]. split; [sf_k KP1 18; exact H18|].
  split; [sf_k KP1 19; exact H19|]. split; [sf_k KP1 20; exact H20|]. split; [sf_k KP1 21; exact H21|].
  split; [sf_k KP1 22; exact H22|]. split; [sf_k KP1 23; exact H23|]. split; [sf_k KP1 24; exact H24|].
  split; [sf_k KP1 25; exact H25|]. split; [sf_k KP1 26; exact H26|]. split; [sf_k KP1 27; exact H27|].
  split; [unfold q64 in *; apply BS; [exact H40 | unfold spk; lia]|].
  assert (MW : forall a bs, bytes_at rsegs m2 a bs -> fsp g <= a -> bytes_at rsegs m' a bs).
  { intros a bs H Ha.
    apply (sf_bytes_munchP (fun y => y < fsp g) W' m2 m' a bs MU'); [| intros i Hi; lia | exact H].
    intros lo hi y Hy Hr. unfold W' in Hy. unfold bsz in *.
    destruct Hy as [Hy|[Hy|[Hy|[Hy|[]]]]]; injection Hy as <- <-; lia. }
  split.
  - unfold q64, spk. rewrite Z.add_0_r. apply MW; [exact BQ0 | lia].
  - unfold q64, spk. apply MW; [exact BQ8 | lia].
Qed.

End G07.
