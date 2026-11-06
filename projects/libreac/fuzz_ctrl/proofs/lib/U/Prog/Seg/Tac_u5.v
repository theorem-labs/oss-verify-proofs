(* Helpers for the segment lemmas of batch u5 (I01, I02, I03, G01-G05, G07) of fuzz_ctrl LLVMFuzzerTestOneInput
   (ubsan): the reply- and fragment-arm model facts (the plain Tac_b5 / Tac_b6 lemmas of two working branches on
   the U model), byte reads, the RPS and GF transport at the libreac v1.9.0 ubsan slots (reply outputs
   sp+1728/1736/1750, frag sp+120, before sp+192, `first` sp+36 .. 76, ID sp+76, OUR sp+114), SR (plan-ubsan 7) and
   the branch tactics. The frame-loop facts, FB / IFS transport and u4_mid are Tac_u4's. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcReply RcIdentModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists and bytes ---- *)

Lemma u5_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d H.
  - destruct n; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma u5_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma u5_bat_range : forall l i, 0 <= bat l i < 256.
Proof. intros l i. unfold bat. apply RcLib.byte_range. Qed.

Lemma u5_bsl_len : forall l k n, 0 <= k -> 0 <= n -> Z.of_nat (length l) >= k + n ->
  length (bsl l k n) = Z.to_nat n.
Proof. intros l k n Hk Hn H. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

(* fg_clear: byte 6 becomes 0, every other byte is kept. *)
Lemma u5_clear : forall x, (7 <= length x)%nat ->
  length (fg_clear x) = length x /\ bat (fg_clear x) 6 = 0 /\
  (forall k d, k <> 6%nat -> nth k (fg_clear x) d = nth k x d) /\
  (forall k, (7 <= k)%nat -> skipn k (fg_clear x) = skipn k x).
Proof.
  intros x Hx.
  destruct x as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 x']]]]]]]; cbn [length] in Hx; try lia.
  unfold fg_clear, bat. change (Z.to_nat 6) with 6%nat. cbn [firstn skipn app length].
  split; [reflexivity|]. split; [reflexivity|]. split.
  - intros k d Hk. do 6 (destruct k as [|k]; [reflexivity|]). destruct k as [|k]; [lia|]. reflexivity.
  - intros k Hk. do 7 (destruct k as [|k]; [lia|]). reflexivity.
Qed.

Lemma u5_first1 : forall (l : list byte) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d H; [cbn in H; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in H. lia.
Qed.

Lemma u5_ba_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* The bytes bsl bs k n at a + k, for k, n given as Z. *)
Lemma u5_ba_bsl : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (bsl bs k n).
Proof.
  intros m a bs k n H Hk Hn Hl. unfold bsl.
  pose proof (u5_ba_sub m a bs (Z.to_nat k) (Z.to_nat n) H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma u5_byte_read : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  rewrite (bytes_at_read rsegs m a bs (Z.of_nat i) 1 H ltac:(lia) ltac:(rewrite Nat2Z.id; lia)).
  rewrite Nat2Z.id. f_equal. apply u5_first1. exact Hi.
Qed.

Lemma u5_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma u5_q64_read : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (u5_ovr m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma u5_u16_read : forall m a v, u16 m a v -> ov_read_bytes rsegs m (wa a) 2 = Some (le2 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold u16 in H. pose proof (u5_ovr m a _ H) as R. rewrite length_le2 in R. exact R. Qed.

Lemma u5_norm : forall mem a bs, ro_agree rsegs mem -> bytes_at rsegs mem a bs ->
  bytes_at rsegs (normalize rsegs mem) a bs.
Proof.
  intros mem a bs HMI H.
  exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H).
Qed.

Lemma u5_q64_norm : forall mem a v, ro_agree rsegs mem -> q64 mem a v -> q64 (normalize rsegs mem) a v.
Proof. intros mem a v HMI H. unfold q64 in *. exact (u5_norm mem a _ HMI H). Qed.

Lemma u5_u16_norm : forall mem a v, ro_agree rsegs mem -> u16 mem a v -> u16 (normalize rsegs mem) a v.
Proof. intros mem a v HMI H. unfold u16 in *. exact (u5_norm mem a _ HMI H). Qed.

Lemma u5_rw_ba : forall m a n junk bs, Step.rw_cells rsegs m a [Cells.CB n junk] -> bytes_at rsegs m a bs ->
  length bs = n -> Step.rw_cells rsegs m a [Cells.CB n bs].
Proof.
  intros m a n junk bs (_ & Hw) Hb L. split; [|exact Hw].
  split; [cbn; split; [exact L | exact I]|]. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma u5_wr_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + n <= hi ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H3) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H3 (a + i) ltac:(lia))).
Qed.

Lemma u5_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma u5_lor8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor (y * 256) x = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.lor_comm.
  replace (y * 256) with (Z.shiftl y 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  apply Bytes.lor_shiftl8_add; lia.
Qed.

(* ---- one turn of the frame state ---- *)

Lemma u5_tID_S : forall inp j,
  t_ID inp (S j) = fg_id (t_IDr inp j) (t_len inp j) (t_FG inp j) (t_g inp j).
Proof.
  intros inp j. unfold t_ID, t_IDr, t_FG. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma u5_tFG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

(* The fragment arm's class with all five pointers non-zero. *)
Lemma u5_or0 : ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) = false.
Proof. reflexivity. Qed.

Lemma u5_close : forall len st g, fg_rf len st g = 1 ->
  fcls len st g = FgClose /\ fg_fr len g = true /\ bat g 19 <> 1 /\ fg_keep st g = true /\
  fg_close st g = true.
Proof.
  intros len st g H. unfold fg_rf, fcls, fg_class in *. rewrite u5_or0 in *.
  destruct (fg_fr len g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate H|].
  destruct (fg_keep st g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (fg_close st g); cbn [negb] in *; [|cbn in H; discriminate H].
  apply Z.eqb_neq in E19. auto.
Qed.

Lemma u5_rf01 : forall len st g, fg_rf len st g = 0 \/ fg_rf len st g = 1.
Proof.
  intros len st g. unfold fg_rf, fcls, fg_class. rewrite u5_or0.
  destruct (fg_fr len g); cbn [negb]; [|left; reflexivity].
  destruct (bat g 19 =? 1); [left; reflexivity|].
  destruct (fg_keep st g); cbn [negb]; [|left; reflexivity].
  destruct (fg_close st g); cbn [negb]; [right | left]; reflexivity.
Qed.

Lemma u5_fr_n : forall len g, fg_fr len g = true -> 50 <= len /\ 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H.
  repeat match type of H with
  | andb _ _ = true => apply andb_prop in H as [H ?]
  end.
  repeat match goal with
  | X : (_ <=? _) = true |- _ => apply Z.leb_le in X
  end.
  lia.
Qed.

(* fg_first: the state FIRST leaves. *)
Lemma u5_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat /\ bat (fg_first st g) 6 = 1 /\ bat (fg_first st g) 7 = fg_n g.
Proof.
  intros st g Hst Hg Hn.
  assert (L6 : length (bsl g 6 6) = 6%nat) by (apply u5_bsl_len; lia).
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply u5_bsl_len; lia).
  assert (E : fg_first st g = bsl g 6 6 ++ Z_to_bv 8 1 :: nth 26 g (Z_to_bv 8 0) :: fg_body g ++
                skipn (Z.to_nat (8 + fg_n g)) st) by reflexivity.
  assert (B6 : bat (fg_first st g) 6 = 1).
  { unfold bat. change (Z.to_nat 6) with 6%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  assert (B7 : bat (fg_first st g) 7 = fg_n g).
  { unfold fg_n, bat. change (Z.to_nat 7) with 7%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  split; [|split; [exact B6 | exact B7]].
  rewrite E, length_app. cbn [length]. rewrite length_app, LB, length_skipn, L6, Hst. lia.
Qed.

(* fg_join under KEEP, from a state with frag_ok. *)
Lemma u5_join : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  1 <= fg_lf st <= 22 -> fg_T st g <= 64 ->
  length (fg_join st g) = 72%nat /\
  (11 <= fg_lf st -> bat (fg_join st g) 17 = bat st 17 /\ bat (fg_join st g) 18 = bat st 18).
Proof.
  intros st g Hst Hg Hn Hl HT. unfold fg_T in HT.
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply u5_bsl_len; lia).
  unfold fg_join, fg_T.
  split; [rewrite !length_app, length_firstn, LB, length_skipn; lia|].
  intros H11. unfold bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
  rewrite !app_nth1 by (rewrite length_firstn; lia). rewrite !u5_nth_firstn by lia. split; reflexivity.
Qed.

(* One turn keeps the frag's length and frag_ok (struct.reac_identity_frag F2). *)
Lemma u5_fg_st_inv : forall len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  length (fg_st len st g) = 72%nat /\ frag_ok (fg_st len st g).
Proof.
  intros len st g Hst Hg (HF1 & HF2).
  unfold fg_st, fcls, fg_class. rewrite u5_or0.
  destruct (fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|split; [exact Hst | split; assumption]].
  destruct (u5_fr_n len g Efr) as (_ & Hn).
  destruct (bat g 19 =? 1); cbn [fg_next].
  { destruct (u5_first st g Hst Hg Hn) as (L & B6 & B7).
    split; [exact L|]. unfold frag_ok. rewrite B6, B7. split; [right; reflexivity|]. intros _. exact Hn. }
  destruct (fg_keep st g) eqn:Ek; cbn [negb fg_next].
  2:{ destruct (u5_clear st ltac:(lia)) as (L & B6 & _). split; [lia|]. unfold frag_ok. rewrite B6.
      split; [left; reflexivity | intros X; discriminate X]. }
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat st 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  destruct (u5_join st g Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (u5_clear (fg_join st g) ltac:(lia)) as (L & B6 & _).
  destruct (fg_close st g); cbn [negb fg_next];
    (split; [lia|]; unfold frag_ok; rewrite B6; split; [left; reflexivity | intros X; discriminate X]).
Qed.

Lemma u5_inv : forall inp j,
  length (t_ID inp j) = 38%nat /\ length (t_FG inp j) = 72%nat /\ frag_ok (t_FG inp j).
Proof.
  intros inp j. induction j as [|j (IH1 & IH2 & IH3)].
  - split; [reflexivity|]. split; [reflexivity|].
    assert (E : bat z72 6 = 0) by (vm_compute; reflexivity).
    unfold t_FG; cbn [fst_at fs_fg fs0]. unfold frag_ok. rewrite E.
    split; [left; reflexivity | intros X; discriminate X].
  - rewrite u5_tID_S, u5_tFG_S.
    destruct (u5_fg_st_inv (t_len inp j) (t_FG inp j) (t_g inp j) IH2 (u4_tg_len inp j) IH3) as (L & F).
    split; [|split; [exact L | exact F]].
    unfold fg_id, t_IDr, rp_id.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      repeat apply RcIdentModel.ING_length; exact IH1.
Qed.

Lemma u5_lens : forall inp j,
  length (t_IDr inp j) = 38%nat /\ length (t_FGf inp j) = 72%nat /\ frag_ok (t_FGf inp j).
Proof.
  intros inp j. rewrite <- u5_tFG_S. destruct (u5_inv inp (S j)) as (_ & L & F).
  split; [|split; [exact L | exact F]].
  destruct (u5_inv inp j) as (L1 & _).
  unfold t_IDr, rp_id. destruct (RcReply.ir (t_len inp j) (t_g inp j)); [apply RcIdentModel.ING_length|]; exact L1.
Qed.

(* ---- the fragment arm (rf = 1 is CLOSE) ---- *)
Lemma u5_close_facts : forall inp j, t_rf inp j = 1 ->
  14 <= fg_T (t_FG inp j) (t_g inp j) <= 64 /\ bat (t_FG inp j) 6 = 1 /\ 1 <= fg_lf (t_FG inp j) <= 22 /\
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)) /\ length (t_FGf inp j) = 72%nat /\
  recsum (bsl (t_FGf inp j) 15 (fg_T (t_FG inp j) (t_g inp j) - 8)) = 0.
Proof.
  intros inp j H. unfold t_rf in H.
  destruct (u5_close _ _ _ H) as (Ec & Efr & _ & Ek & Ecl).
  destruct (u5_inv inp j) as (_ & Hst & (HF1 & HF2)).
  pose proof (u4_tg_len inp j) as Hg.
  destruct (u5_fr_n _ _ Efr) as (_ & Hn).
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat (t_FG inp j) 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  assert (EF : t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j))).
  { unfold t_FGf, fg_st. rewrite Ec. reflexivity. }
  destruct (u5_join (t_FG inp j) (t_g inp j) Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (u5_clear (fg_join (t_FG inp j) (t_g inp j)) ltac:(lia)) as (L & _ & _ & SK).
  unfold fg_close in Ecl.
  repeat match type of Ecl with
  | andb _ _ = true => apply andb_prop in Ecl as [Ecl ?]
  end.
  match goal with X : (recsum _ =? 0) = true |- _ => apply Z.eqb_eq in X; rename X into HR end.
  apply Z.leb_le in Ecl.
  split; [lia|]. split; [exact H1|]. split; [unfold fg_lf; lia|]. split; [exact EF|].
  split; [rewrite EF, L; exact LJ|].
  rewrite EF. unfold bsl in *. rewrite SK by lia. exact HR.
Qed.

(* first_frag F3 (P4l, plan-ubsan 6.4 item 11), libreac v1.9.0: at CLOSE, FI(FG_j, FS_j) gives have = 1, and the
   address v1.9 rebuilds from joined_byte(&first, block, 9) and (.., 10) (0x13b20, 0x13b38) is addr_f
   (SlotModel.fg_addr_joined: CLOSE has an open record and 14 <= fg_T, Φ's first 50 bytes hold 27 + fg_n). *)
Lemma u5_P4l : forall inp j, t_rf inp j = 1 -> FI (t_FG inp j) (fst_at inp j) ->
  fs_have (fst_at inp j) = 1 /\
  fg_addr (t_FG inp j) (t_g inp j) =
    256 * joined_byte (fst_at inp j) (t_g inp j) 9 + joined_byte (fst_at inp j) (t_g inp j) 10.
Proof.
  intros inp j H HFI.
  destruct (u5_close_facts inp j H) as (HT & H6 & _).
  destruct (u5_inv inp j) as (_ & Hst & Hok).
  pose proof (u4_tg_len inp j) as Hg.
  unfold t_rf in H. destruct (u5_close _ _ _ H) as (_ & Efr & _).
  destruct (u5_fr_n _ _ Efr) as (_ & Hn).
  split; [exact (proj1 (proj1 HFI H6))|].
  apply fg_addr_joined; [exact Hst | exact Hok | exact HFI | exact H6 | rewrite Hg; lia | lia].
Qed.

Lemma u5_jb_range : forall s g i, 0 <= joined_byte s g i < 256.
Proof. intros s g i. unfold joined_byte. destruct (i <? fs_nb s); apply u5_bat_range. Qed.

Lemma u5_tID_S0 : forall inp j, t_rf inp j <> 1 -> t_ID inp (S j) = t_IDr inp j.
Proof.
  intros inp j H. rewrite u5_tID_S. unfold fg_id. unfold t_rf in H.
  replace (fg_rf (t_len inp j) (t_FG inp j) (t_g inp j) =? 1) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma u5_tID_S1 : forall inp j, t_rf inp j = 1 ->
  t_ID inp (S j) = snd (RcIdentModel.ING (t_IDr inp j) (fg_addr (t_FG inp j) (t_g inp j))
                                          (f_pl (t_len inp j) (t_FG inp j) (t_g inp j))).
Proof.
  intros inp j H. rewrite u5_tID_S. unfold fg_id. unfold t_rf in H. rewrite H. reflexivity.
Qed.

(* The frame loop's fragment class has nonzero pointers: never a refusal. *)
Lemma u5_nref : forall len st g, fcls len st g <> FgRefuse.
Proof.
  intros len st g. unfold fcls, fg_class. cbn [Z.eqb orb].
  destruct (negb (fg_fr len g)); [discriminate|].
  destruct (bat g 19 =? 1); [discriminate|].
  destruct (negb (fg_keep st g)); [discriminate|].
  destruct (negb (fg_close st g)); discriminate.
Qed.

(* Not sum_ok: FR(Φ, len) fails (fg_fr tests len >= 50 and the block sum), so the fragment state is kept. *)
Lemma u5_nosum : forall inp j, t_sum_ok inp j = false -> t_FGf inp j = t_FG inp j.
Proof.
  intros inp j H. unfold t_sum_ok, t_big in H.
  assert (E : fg_fr (t_len inp j) (t_g inp j) = false).
  { unfold fg_fr. revert H.
    destruct (50 <=? t_len inp j); [|intros _; reflexivity].
    destruct (blocksum (skipn 18 (t_g inp j)) =? 0); [cbn; intros X; discriminate X|].
    intros _. rewrite !andb_false_r. reflexivity. }
  unfold t_FGf, fg_st, fcls, fg_class. rewrite u5_or0, E. reflexivity.
Qed.

(* ---- the reply arm ---- *)

(* IR(Φ, len): len >= 50, sum_ok, pll in 1 .. 10, r = 1, and the record sums to 0; not IR: r = 0, ID kept. *)
Lemma u5_ir_facts : forall inp j, t_ir inp j = true ->
  50 <= t_len inp j /\ t_big inp j = true /\ t_sum_ok inp j = true /\ 1 <= r_pll (t_g inp j) <= 10 /\
  t_r inp j = 1.
Proof.
  intros inp j H. unfold t_ir in H.
  destruct (RcReply.ir_bytes _ _ H) as (H50 & _).
  destruct (RcReply.ir_true _ _ H) as (_ & _ & _ & _ & Hs & _ & _ & Hbs & _).
  assert (Hbig : t_big inp j = true) by (unfold t_big; apply Z.leb_le; exact H50).
  split; [exact H50|]. split; [exact Hbig|]. split.
  - unfold t_sum_ok. rewrite Hbig. unfold RcReply.ir_blk in Hbs. rewrite Hbs. reflexivity.
  - split; [unfold r_pll; lia|]. unfold t_r, rp_r. rewrite H. reflexivity.
Qed.

Lemma u5_ir_false : forall inp j, t_ir inp j = false -> t_r inp j = 0 /\ t_IDr inp j = t_ID inp j.
Proof. intros inp j H. unfold t_ir in H. unfold t_r, rp_r, t_IDr, rp_id. rewrite H. split; reflexivity. Qed.

(* record_sum_closes(blk + 16, pll + 5) reads IR's record bytes Φ[34 .. 39 + pll). *)
Lemma u5_irrec : forall g, bsl g 34 (r_pll g + 5) = RcReply.ir_rec g.
Proof.
  intros g. unfold bsl, RcReply.ir_rec, r_pll. replace (RcReply.ir_s g - 13 + 5) with (RcReply.ir_s g - 8) by lia.
  reflexivity.
Qed.

(* The reply's address slot (sp+1750) as a u16. *)
Lemma u5_raddr : forall g, RcReply.reply_addr g = le2 (Z_to_bv 64 (r_addr g)).
Proof.
  intros g. unfold RcReply.reply_addr, r_addr, le2.
  pose proof (RcReply.cp_v_range' g 36) as R6. pose proof (RcReply.cp_v_range' g 37) as R7.
  rewrite MState.unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia.
  unfold RcParse.cp_v in *.
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; change (bv_wrap 8 ?x) with (x mod 2 ^ 8);
    change (2 ^ 8) with 256; lia.
Qed.

Lemma u5_raddr_range : forall g, 0 <= r_addr g < 65536.
Proof.
  intros g. unfold r_addr. pose proof (RcReply.cp_v_range' g 36). pose proof (RcReply.cp_v_range' g 37). lia.
Qed.

(* ---- transport across a run that keeps s0-s11 and writes only in W ---- *)

Lemma u5_RPS_keep : forall g j phi mem m' W, RPS g j phi mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 1728) 24 -> RPS g j phi m'.
Proof.
  intros g j phi mem m' W HR MU D. unfold RPS, u16, q64, spk in *. destruct HR as (H1 & H0). split.
  - intros Hi. destruct (H1 Hi) as (A1 & A2 & A3). split; [|split].
    + apply (u4_ba W mem); [exact A1 | exact MU|]. apply (u4_dj_sub W _ _ _ _ D);
        unfold RcReply.reply_addr; cbn [length]; lia.
    + apply (u4_ba W mem); [exact A2 | exact MU|]. rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D); lia.
    + apply (u4_ba W mem); [exact A3 | exact MU|]. rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D); lia.
  - intros Hi. destruct (H0 Hi) as (A1 & A2 & A3). split; [|split].
    + apply (u4_ba W mem); [exact A1 | exact MU|]. rewrite length_le2. apply (u4_dj_sub W _ _ _ _ D); lia.
    + apply (u4_ba W mem); [exact A2 | exact MU|]. rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D); lia.
    + apply (u4_ba W mem); [exact A3 | exact MU|]. rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D); lia.
Qed.

Lemma u5_GF_keep : forall g j phi regs regs' mem m' W,
  GF g j phi regs mem -> SKP regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 8 -> disjoint_from W (spk g 36) 40 ->
  disjoint_from W (spk g 16) 16 -> disjoint_from W (spk g 114) 6 -> disjoint_from W (spk g 120) 72 ->
  disjoint_from W (spk g 76) 38 -> disjoint_from W (spk g 192) 72 -> disjoint_from W (spk g 1728) 24 ->
  disjoint_from W (spk g 1752) 36 ->
  GF g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HB & HI & HG & HS & H192 & Hrf) K MU Dp D8 D36 D16 D114 D120 D76 D192
    D1728 D1752.
  split; [exact (u4_FB_keep g j phi regs regs' mem m' W HB K MU Dp D8 D16 D114 D1752)|].
  split; [exact (u4_IDb_keep g _ mem m' W (u4_tIDr_len _ _) HI MU D76)|].
  split; [exact (u4_FGb_keep g _ mem m' W (u4_tFGf_len _ _) HG MU D120)|].
  split; [exact (u4_FSj_keep g j mem m' W HS MU D36)|].
  split; [apply (u4_ba W mem m' _ _ H192 MU); rewrite u4_tFG_len; exact D192|].
  intros Hr. destruct (Hrf Hr) as (A1 & A2 & A3). unfold u16, q64, spk in *.
  split; [|split].
  - apply (u4_ba W mem m' _ _ A1 MU). rewrite length_le2. apply (u4_dj_sub W _ _ _ _ D1728); lia.
  - apply (u4_ba W mem m' _ _ A2 MU). rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D1728); lia.
  - apply (u4_ba W mem m' _ _ A3 MU). rewrite length_le8. apply (u4_dj_sub W _ _ _ _ D1728); lia.
Qed.

Lemma u5_SKP_refl : forall regs, SKP regs regs.
Proof. intros regs. repeat split. Qed.

(* FB reads no register that seg_G03 / seg_G07 write: rf is s10 = x26 in v1.9 (v1.8 s9 = x25), and Tac_u4's SKP
   leaves x26 out. *)
Lemma u5_FB_regs : forall g j phi regs regs' m, FB g j phi regs m -> SKP regs regs' -> FB g j phi regs' m.
Proof.
  intros g j phi regs regs' m (HFT & (H25 & H19 & H27 & H20 & (H24 & H16 & HB)))
    (E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E27).
  split.
  - apply (u4_FT_keep g j phi regs regs' m m [] HFT);
      [unfold FTK; repeat split; assumption | apply munch_refl | exact I | exact I | exact I | exact I].
  - split; [exact (u4_rg _ _ _ _ E25 H25)|]. split; [exact (u4_rg _ _ _ _ E19 H19)|].
    split; [exact (u4_rg _ _ _ _ E27 H27)|]. split; [exact (u4_rg _ _ _ _ E20 H20)|].
    split; [exact (u4_rg _ _ _ _ E24 H24)|]. split; [exact H16 | exact HB].
Qed.

Lemma u5_GF_regs : forall g j phi regs regs' m, GF g j phi regs m -> SKP regs regs' -> GF g j phi regs' m.
Proof.
  intros g j phi regs regs' m (HB & HR) K. split; [exact (u5_FB_regs g j phi regs regs' m HB K) | exact HR].
Qed.

(* The callees' ro_agree premise on the normalized memory a segment runs on. *)
Lemma u5_ro_norm : forall m, MemNorm.ro_agree rsegs (MemNorm.normalize rsegs m).
Proof. intros m a Ha. unfold Mem.mrd, MemNorm.normalize. rewrite Ha. reflexivity. Qed.

Lemma u5_mcmp_refl : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* ---- branch conditions over literals and linear Z terms ---- *)
Ltac u5_ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) by lia end.
Ltac u5_cond_base := first
  [ reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac u5_cond := first
  [ reflexivity
  | unfold bv_eqb, bv_ltu, zxb; Step.fold_lit_ux; u5_ul;
    lazymatch goal with
    | |- negb _ = true => apply negb_true_iff; u5_cond_base
    | |- negb _ = false => apply negb_false_iff; u5_cond_base
    | _ => u5_cond_base
    end ].
Ltac u5_br b :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; u5_cond); cbv iota
  end.

(* A word equation Z_to_bv 64 x = Z_to_bv 64 y with x, y linear in the context's bounded terms. *)
Ltac u5_weq := f_equal; unfold zxb; u5_ul; lia.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* SR (plan-ubsan 7: stack range): S < 2^63 with the window [S - K, S) above the image, so every frame slot
   sp+N (N <= 1936) and frag->buf + 64 = sp+192 (v1.9: buf = sp+128) lie in [0, 2^63). *)
Lemma u5_SR : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  SL_TOP + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  (forall N, 0 <= N <= SLOT_FRAME -> 0 < spk g N /\ spk g N + 64 < 2 ^ 63).
Proof.
  intros g hb L A regs mem md HFR.
  destruct (sl_fr_bnd B APIf ra empty FF g hb L A regs mem md HFR) as (_ & _ & HSK & HS47 & _).
  split; [exact HSK|]. split; [exact HS47|].
  intros N HN. unfold spk, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK, SL_TOP in *. lia.
Qed.

End S.
