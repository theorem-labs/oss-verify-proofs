(* Helpers for the segment lemmas of batch u6 (G06, E01-E04) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac
   v1.9.0): the frame-loop model facts (cursor range, Φ's bytes, the frame-state invariants, first_frag F2: FI kept,
   u6_FI_S), the is_8819 facts (struct P5.2-P5.4), the transport of the cut bundles across a run that writes one
   interval (v1.9 layout: M7 sp+8, TF sp+16, left - h sp+24, `first` sp+36, id sp+76, our sp+114, frag sp+120),
   u6_mid (sl_mid with the write set's munch over the unnormalized memory), the store and body facts of G06's
   `first`, AF11 (E04's inline record sum) and branch tactics. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcParse RcLib RcLeaf RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists ---- *)
Lemma u6_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d H.
  - destruct n; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma u6_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma u6_bat_range : forall l i, 0 <= bat l i < 256.
Proof. intros l i. unfold bat. apply RcLib.byte_range. Qed.

Lemma u6_bsl_len : forall l k n, 0 <= k -> 0 <= n -> Z.of_nat (length l) >= k + n ->
  length (bsl l k n) = Z.to_nat n.
Proof. intros l k n Hk Hn H. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

(* fg_clear: byte 6 becomes 0, every other byte is kept. *)
Lemma u6_clear : forall x, (7 <= length x)%nat ->
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

(* ---- the frame cursor ---- *)
Lemma u6_inb : forall inp k, 0 <= inb inp k < 256.
Proof. intros inp k. unfold inb, RcIdentModel.bz. apply RcLib.byte_range. Qed.

Lemma u6_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - pose proof (u6_inb inp (fc inp j)). pose proof (u6_inb inp (fc inp j + 1)).
    unfold f_next, f_body, f_len, f_L, f_h, f_left.
    destruct (2 <=? nlen inp - fc inp j); cbv beta iota; lia.
Qed.

Lemma u6_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (u6_fc_range inp j) as R.
  pose proof (u6_inb inp (fc inp j)). pose proof (u6_inb inp (fc inp j + 1)).
  unfold t_len, t_body, f_len, f_body, f_L, f_h, f_left.
  destruct (2 <=? nlen inp - fc inp j); cbv beta iota; lia.
Qed.

Lemma u6_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (u6_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi, t_len, t_body, nlen in *. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma u6_g_eq : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. unfold t_g, fr50. rewrite firstn_app.
  rewrite u6_phi_len. replace (50 - Z.to_nat (t_len inp j))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma u6_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

(* ---- one turn of the frame state ---- *)
Lemma u6_tID_S : forall inp j,
  t_ID inp (S j) = fg_id (t_IDr inp j) (t_len inp j) (t_FG inp j) (t_g inp j).
Proof.
  intros inp j. unfold t_ID, t_IDr, t_FG. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma u6_tFG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma u6_fs_S : forall inp j,
  fst_at inp (S j) =
  if f_opens (t_len inp j) (t_g inp j)
  then FSt (t_ID inp (S j)) (t_FGf inp j) 1 (bat (t_g inp j) 26) (fg_body (t_g inp j))
  else FSt (t_ID inp (S j)) (t_FGf inp j) (fs_have (fst_at inp j)) (fs_nb (fst_at inp j))
         (fs_body (fst_at inp j)).
Proof.
  intros inp j. rewrite u6_tID_S. unfold t_FGf, t_IDr, t_FG, t_ID. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

(* n (the FIRST body's length) is a byte at every turn. *)
Lemma u6_fs_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 255.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_nb]. lia.
  - rewrite u6_fs_S. destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_nb];
      [pose proof (u6_bat_range (t_g inp j) 26); lia | exact IH].
Qed.

(* The fragment arm's class with all five pointers non-zero. *)
Lemma u6_or0 : ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) = false.
Proof. reflexivity. Qed.

Lemma u6_close : forall len st g, fg_rf len st g = 1 ->
  fcls len st g = FgClose /\ fg_fr len g = true /\ bat g 19 <> 1 /\ fg_keep st g = true /\
  fg_close st g = true.
Proof.
  intros len st g H. unfold fg_rf, fcls, fg_class in *. rewrite u6_or0 in *.
  destruct (fg_fr len g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate H|].
  destruct (fg_keep st g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (fg_close st g); cbn [negb] in *; [|cbn in H; discriminate H].
  apply Z.eqb_neq in E19. auto.
Qed.

Lemma u6_rf01 : forall len st g, fg_rf len st g = 0 \/ fg_rf len st g = 1.
Proof.
  intros len st g. unfold fg_rf, fcls, fg_class. rewrite u6_or0.
  destruct (fg_fr len g); cbn [negb]; [|left; reflexivity].
  destruct (bat g 19 =? 1); [left; reflexivity|].
  destruct (fg_keep st g); cbn [negb]; [|left; reflexivity].
  destruct (fg_close st g); cbn [negb]; [right | left]; reflexivity.
Qed.

Lemma u6_fr_n : forall len g, fg_fr len g = true -> 50 <= len /\ 1 <= fg_n g <= 22.
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

(* fg_first: the state FIRST leaves (its body bytes 8 .. 8 + n are Φ[27 .. 27 + n), the body `first` keeps). *)
Lemma u6_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat /\ bat (fg_first st g) 6 = 1 /\ bat (fg_first st g) 7 = fg_n g /\
  bsl (fg_first st g) 8 (fg_n g) = fg_body g.
Proof.
  intros st g Hst Hg Hn.
  assert (L6 : length (bsl g 6 6) = 6%nat) by (apply u6_bsl_len; lia).
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply u6_bsl_len; lia).
  assert (E : fg_first st g = bsl g 6 6 ++ Z_to_bv 8 1 :: nth 26 g (Z_to_bv 8 0) :: fg_body g ++
                skipn (Z.to_nat (8 + fg_n g)) st) by reflexivity.
  assert (N : forall i, (i < Z.to_nat (fg_n g))%nat ->
    nth (8 + i) (fg_first st g) (Z_to_bv 8 0) = nth (27 + i) g (Z_to_bv 8 0)).
  { intros i Hi. rewrite E, app_nth2 by lia. rewrite L6. replace (8 + i - 6)%nat with (S (S i)) by lia.
    cbn [nth]. rewrite app_nth1 by lia. unfold fg_body, bsl. rewrite u6_nth_firstn by lia.
    rewrite u6_nth_skipn. reflexivity. }
  assert (B6 : bat (fg_first st g) 6 = 1).
  { unfold bat. change (Z.to_nat 6) with 6%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  assert (B7 : bat (fg_first st g) 7 = fg_n g).
  { unfold fg_n, bat. change (Z.to_nat 7) with 7%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  assert (L72 : length (fg_first st g) = 72%nat).
  { rewrite E, length_app. cbn [length]. rewrite length_app, LB, length_skipn, L6, Hst. lia. }
  split; [exact L72|]. split; [exact B6|]. split; [exact B7|].
  assert (LBB : length (bsl (fg_first st g) 8 (fg_n g)) = Z.to_nat (fg_n g)).
  { unfold bsl. rewrite length_firstn, length_skipn, L72. lia. }
  apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0); [rewrite LBB, LB; reflexivity|].
  intros i Hi. rewrite LBB in Hi.
  unfold bsl at 1. change (Z.to_nat 8) with 8%nat.
  rewrite u6_nth_firstn by lia. rewrite u6_nth_skipn. rewrite (N i Hi).
  unfold fg_body, bsl. change (Z.to_nat 27) with 27%nat.
  rewrite u6_nth_firstn by lia. rewrite u6_nth_skipn. reflexivity.
Qed.

(* fg_join under KEEP, from a state with frag_ok. *)
Lemma u6_join : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  1 <= fg_lf st <= 22 -> fg_T st g <= 64 ->
  length (fg_join st g) = 72%nat /\
  (11 <= fg_lf st -> bat (fg_join st g) 17 = bat st 17 /\ bat (fg_join st g) 18 = bat st 18).
Proof.
  intros st g Hst Hg Hn Hl HT. unfold fg_T in HT.
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply u6_bsl_len; lia).
  unfold fg_join, fg_T.
  split; [rewrite !length_app, length_firstn, LB, length_skipn; lia|].
  intros H11. unfold bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
  rewrite !app_nth1 by (rewrite length_firstn; lia). rewrite !u6_nth_firstn by lia. split; reflexivity.
Qed.

(* One turn keeps the frag's length and frag_ok (struct.reac_identity_frag F2). *)
Lemma u6_fg_st_inv : forall len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  length (fg_st len st g) = 72%nat /\ frag_ok (fg_st len st g).
Proof.
  intros len st g Hst Hg (HF1 & HF2).
  unfold fg_st, fcls, fg_class. rewrite u6_or0.
  destruct (fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|split; [exact Hst | split; assumption]].
  destruct (u6_fr_n len g Efr) as (_ & Hn).
  destruct (bat g 19 =? 1); cbn [fg_next].
  { destruct (u6_first st g Hst Hg Hn) as (L & B6 & B7 & _).
    split; [exact L|]. unfold frag_ok. rewrite B6, B7. split; [right; reflexivity|]. intros _. exact Hn. }
  destruct (fg_keep st g) eqn:Ek; cbn [negb fg_next].
  2:{ destruct (u6_clear st ltac:(lia)) as (L & B6 & _). split; [lia|]. unfold frag_ok. rewrite B6.
      split; [left; reflexivity | intros X; discriminate X]. }
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat st 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  destruct (u6_join st g Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (u6_clear (fg_join st g) ltac:(lia)) as (L & B6 & _).
  destruct (fg_close st g); cbn [negb fg_next];
    (split; [lia|]; unfold frag_ok; rewrite B6; split; [left; reflexivity | intros X; discriminate X]).
Qed.

Lemma u6_inv : forall inp j,
  length (t_ID inp j) = 38%nat /\ length (t_FG inp j) = 72%nat /\ frag_ok (t_FG inp j).
Proof.
  intros inp j. induction j as [|j (IH1 & IH2 & IH3)].
  - split; [reflexivity|]. split; [reflexivity|].
    assert (E : bat z72 6 = 0) by (vm_compute; reflexivity).
    unfold t_FG; cbn [fst_at fs_fg fs0]. unfold frag_ok. rewrite E.
    split; [left; reflexivity | intros X; discriminate X].
  - rewrite u6_tID_S, u6_tFG_S.
    destruct (u6_fg_st_inv (t_len inp j) (t_FG inp j) (t_g inp j) IH2 (u6_g_len inp j) IH3) as (L & F).
    split; [|split; [exact L | exact F]].
    unfold fg_id, t_IDr, rp_id.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      repeat apply RcIdentModel.ING_length; exact IH1.
Qed.

(* ---- the fragment arm (rf = 1 is CLOSE) ---- *)
Lemma u6_close_facts : forall inp j, t_rf inp j = 1 ->
  14 <= fg_T (t_FG inp j) (t_g inp j) <= 64 /\ bat (t_FG inp j) 6 = 1 /\ 1 <= fg_lf (t_FG inp j) <= 22 /\
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)) /\ length (t_FGf inp j) = 72%nat /\
  recsum (bsl (t_FGf inp j) 15 (fg_T (t_FG inp j) (t_g inp j) - 8)) = 0.
Proof.
  intros inp j H. unfold t_rf in H.
  destruct (u6_close _ _ _ H) as (Ec & Efr & _ & Ek & Ecl).
  destruct (u6_inv inp j) as (_ & Hst & (HF1 & HF2)).
  pose proof (u6_g_len inp j) as Hg.
  destruct (u6_fr_n _ _ Efr) as (_ & Hn).
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat (t_FG inp j) 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  assert (EF : t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j))).
  { unfold t_FGf, fg_st. rewrite Ec. reflexivity. }
  destruct (u6_join (t_FG inp j) (t_g inp j) Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (u6_clear (fg_join (t_FG inp j) (t_g inp j)) ltac:(lia)) as (L & _ & _ & SK).
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

(* first_frag F2 (FI kept): one turn keeps FI between the frag and the frame state. *)
Lemma u6_FI_S : forall inp j, FI (t_FG inp j) (fst_at inp j) -> FI (t_FG inp (S j)) (fst_at inp (S j)).
Proof.
  intros inp j HFI. rewrite u6_fs_S, u6_tFG_S.
  destruct (u6_inv inp j) as (_ & Hst & _). pose proof (u6_g_len inp j) as Hg.
  unfold t_FGf, fg_st, fcls, fg_class. rewrite u6_or0.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo.
  - unfold f_opens in Eo. apply andb_prop in Eo as (Efr & E19).
    rewrite Efr, E19. cbn [negb fg_next].
    destruct (u6_fr_n _ _ Efr) as (_ & Hn).
    destruct (u6_first (t_FG inp j) (t_g inp j) Hst Hg Hn) as (_ & B6 & B7 & BB).
    unfold FI. cbn [fs_have fs_nb fs_body]. rewrite B7.
    split; [intros _; split; [reflexivity | unfold fg_n; reflexivity]|].
    intros _. unfold fg_n in BB. exact (eq_sym BB).
  - unfold f_opens in Eo.
    destruct (fg_fr (t_len inp j) (t_g inp j)) eqn:Efr; cbn [negb fg_next]; [|exact HFI].
    cbn [andb] in Eo. rewrite Eo.
    destruct (u6_inv inp j) as (_ & _ & (HF1 & HF2)).
    destruct (fg_keep (t_FG inp j) (t_g inp j)) eqn:Ek; cbn [negb fg_next].
    2:{ destruct (u6_clear (t_FG inp j) ltac:(lia)) as (_ & B6 & _).
        unfold FI. rewrite B6. split; intros X; discriminate X. }
    destruct (u6_fr_n _ _ Efr) as (_ & Hn).
    unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
    apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
    assert (H1 : bat (t_FG inp j) 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
    specialize (HF2 H1).
    destruct (u6_join (t_FG inp j) (t_g inp j) Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
    destruct (u6_clear (fg_join (t_FG inp j) (t_g inp j)) ltac:(lia)) as (_ & B6 & _).
    destruct (fg_close (t_FG inp j) (t_g inp j)); cbn [negb fg_next];
      unfold FI; rewrite B6; split; intros X; discriminate X.
Qed.

(* opens_record (struct.first_frag Names) as the code tests it: len >= 50 and sum_ok, then the bytes. *)
Lemma u6_opens_eq : forall len g,
  f_opens len g = (50 <=? len) && (blocksum (skipn 18 g) =? 0) &&
    ((bat g 16 =? 205) && (bat g 17 =? 234) && (bat g 18 =? 4) && (bat g 19 =? 1) && (bat g 22 =? 0) &&
     (bat g 23 =? 2) && (bat g 24 =? 0) && (bat g 25 =? 254) && (1 <=? bat g 26) && (bat g 26 <=? 22)).
Proof.
  intros len g. unfold f_opens, fg_fr, fg_n.
  destruct (50 <=? len), (blocksum (skipn 18 g) =? 0), (bat g 16 =? 205), (bat g 17 =? 234), (bat g 18 =? 4),
    (bat g 19 =? 1), (bat g 19 =? 2), (bat g 22 =? 0), (bat g 23 =? 2), (bat g 24 =? 0), (bat g 25 =? 254),
    (1 <=? bat g 26), (bat g 26 <=? 22); reflexivity.
Qed.

Lemma u6_lens : forall inp j,
  length (t_IDr inp j) = 38%nat /\ length (t_FGf inp j) = 72%nat /\ frag_ok (t_FGf inp j).
Proof.
  intros inp j. rewrite <- u6_tFG_S. destruct (u6_inv inp (S j)) as (_ & L & F).
  split; [|split; [exact L | exact F]].
  destruct (u6_inv inp j) as (L1 & _).
  unfold t_IDr, rp_id. destruct (RcReply.ir (t_len inp j) (t_g inp j)); [apply RcIdentModel.ING_length|]; exact L1.
Qed.

(* ---- memory: Φ's bytes, sub-ranges ---- *)
Lemma u6_ba_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma u6_ba_g : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H Hl. rewrite (u6_g_eq inp j Hl).
  rewrite <- (firstn_skipn 50 (t_phi inp j)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* ---- machine-level helpers ---- *)
Lemma u6_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma u6_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma u6_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma u6_q64_ovr : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (u6_ovr m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma u6_norm : forall mem a bs, ro_agree rsegs mem -> bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs.
Proof. intros mem a bs HMI H. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H). Qed.

Lemma u6_q64_norm : forall mem a v, ro_agree rsegs mem -> q64 mem a v -> q64 (normalize rsegs mem) a v.
Proof. intros mem a v HMI H. unfold q64 in *. exact (u6_norm mem a _ HMI H). Qed.

Lemma u6_tID_S0 : forall inp j, t_rf inp j <> 1 -> t_ID inp (S j) = t_IDr inp j.
Proof.
  intros inp j H. rewrite u6_tID_S. unfold fg_id. unfold t_rf in H.
  replace (fg_rf (t_len inp j) (t_FG inp j) (t_g inp j) =? 1) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma u6_tID_S1 : forall inp j, t_rf inp j = 1 ->
  t_ID inp (S j) = snd (RcIdentModel.ING (t_IDr inp j) (fg_addr (t_FG inp j) (t_g inp j))
                                          (f_pl (t_len inp j) (t_FG inp j) (t_g inp j))).
Proof.
  intros inp j H. rewrite u6_tID_S. unfold fg_id. unfold t_rf in H. rewrite H. reflexivity.
Qed.

(* ---- transport of the cut bundles across a run that writes only [lo, hi) (slot-plan-ubsan 3.1 layout) ---- *)
Definition u6_out (lo hi a n : Z) : Prop := a + n <= lo \/ hi <= a.

(* The registers FT, V7, V2 and VC read: s0, s1, s2, s4-s9 (E04 overwrites s3 and s11). *)
Definition u6_kT (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
  getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25.

(* The ranges FT and VC read: Φ, M7 (sp+8), TF (sp+16), left - h (sp+24), our (sp+114), B (sp+1752); OVF is the
   register s0 in v1.9. *)
Definition u6_av (g : ghost) (phi len lo hi : Z) : Prop :=
  u6_out lo hi phi len /\ u6_out lo hi (spk g 8) 8 /\ u6_out lo hi (spk g 16) 8 /\ u6_out lo hi (spk g 24) 8 /\
  u6_out lo hi (spk g 114) 6 /\ u6_out lo hi (spk g 1752) 36.

(* The ranges IFS reads: id (sp+76), frag (sp+120) and `first` (sp+36 .. 297: have, n, body of at most 255 bytes). *)
Definition u6_ai (g : ghost) (lo hi : Z) : Prop :=
  u6_out lo hi (spk g 76) 38 /\ u6_out lo hi (spk g 120) 72 /\ u6_out lo hi (spk g 36) 261.

Lemma u6_munch0 : forall m m', munch [] m m' -> munch [(0, 0)] m m'.
Proof. intros m m' H. apply (munch_weaken [] [(0, 0)] m m'); [intros x _; exact I | exact H]. Qed.

Lemma u6_av0 : forall g phi len, 0 <= phi -> 0 <= fsp g -> u6_av g phi len 0 0.
Proof. intros g phi len H1 H2. unfold u6_av, u6_out, spk. lia. Qed.

Lemma u6_ai0 : forall g, 0 <= fsp g -> u6_ai g 0 0.
Proof. intros g H. unfold u6_ai, u6_out, spk. lia. Qed.

Lemma u6_ba_keep : forall m m' lo hi a bs, munch [(lo, hi)] m m' -> bytes_at rsegs m a bs ->
  u6_out lo hi a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU H D. apply (bytes_at_transport rsegs [(lo, hi)] m m' a bs H MU).
  cbn [disjoint_from]. unfold u6_out in D. split; [exact D | exact I].
Qed.

Lemma u6_q64_keep : forall m m' lo hi a v, munch [(lo, hi)] m m' -> q64 m a v -> u6_out lo hi a 8 -> q64 m' a v.
Proof.
  intros m m' lo hi a v MU H D. unfold q64 in *. apply (u6_ba_keep m m' lo hi a _ MU H).
  rewrite length_le8. exact D.
Qed.

Lemma u6_FT_keep : forall g j phi regs regs' m m' lo hi,
  FT g j phi regs m -> u6_kT regs regs' -> munch [(lo, hi)] m m' -> u6_av g phi (t_len (g_in g) j) lo hi ->
  FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi ((Hj & H9 & HOUR & HM7 & HOVF & HS2) & (H24 & H21 & H22) & H23 & HPhi & H18)
    (E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25) MU (D1 & D8 & D16 & D24 & D114 & D1752).
  unfold FT, LK, FC, S2, OURb, M7, OVF, rg in *. rewrite E8, E9, E18, E21, E22, E23.
  refine (conj (conj Hj (conj H9 (conj _ (conj (u6_q64_keep m m' lo hi _ _ MU HM7 D8) (conj HOVF HS2)))))
         (conj (conj (u6_q64_keep m m' lo hi _ _ MU H24 D24) (conj H21 H22)) (conj H23 (conj _ H18)))).
  - apply (u6_ba_keep m m' lo hi _ _ MU HOUR). rewrite OUR_length. exact D114.
  - apply (u6_ba_keep m m' lo hi _ _ MU HPhi). rewrite u6_phi_len.
    pose proof (u6_len_range (g_in g) j). unfold u6_out in *. lia.
Qed.

Lemma u6_VC_keep : forall g j phi regs regs' m m' lo hi,
  VC g j phi regs m -> u6_kT regs regs' -> munch [(lo, hi)] m m' -> u6_av g phi (t_len (g_in g) j) lo hi ->
  VC g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (H24 & H16 & HB) (E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25) MU
    (_ & _ & D16 & _ & _ & D1752).
  unfold VC, rg in *. rewrite E24.
  refine (conj H24 (conj (u6_q64_keep m m' lo hi _ _ MU H16 D16) _)).
  apply (u6_ba_keep m m' lo hi _ _ MU HB). unfold t_B. rewrite RcParse.ctrlparse_length. exact D1752.
Qed.

Lemma u6_FV_keep : forall g j phi regs regs' m m' lo hi,
  FV g j phi regs m -> u6_kT regs regs' -> getr regs' 19 = getr regs 19 -> getr regs' 27 = getr regs 27 ->
  munch [(lo, hi)] m m' -> u6_av g phi (t_len (g_in g) j) lo hi -> FV g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (H7 & H1 & H0 & H2 & HC) K E19 E27 MU D.
  pose proof K as (E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25).
  refine (conj _ (conj _ (conj _ (conj _ (u6_VC_keep g j phi regs regs' m m' lo hi HC K MU D))))).
  - unfold V7, rg in *. rewrite E25. exact H7.
  - unfold V1, rg in *. rewrite E19. exact H1.
  - unfold V0, rg in *. rewrite E27. exact H0.
  - unfold V2, rg in *. rewrite E20. exact H2.
Qed.

Lemma u6_FB_keep : forall g j phi regs regs' m m' lo hi,
  FB g j phi regs m -> u6_kT regs regs' -> getr regs' 19 = getr regs 19 -> getr regs' 27 = getr regs 27 ->
  munch [(lo, hi)] m m' -> u6_av g phi (t_len (g_in g) j) lo hi -> FB g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (HT & HV) K E19 E27 MU D.
  exact (conj (u6_FT_keep g j phi regs regs' m m' lo hi HT K MU D)
              (u6_FV_keep g j phi regs regs' m m' lo hi HV K E19 E27 MU D)).
Qed.

Lemma u6_IDb_keep : forall g idb m m' lo hi, IDb g idb m -> length idb = 38%nat -> munch [(lo, hi)] m m' ->
  u6_out lo hi (spk g 76) 38 -> IDb g idb m'.
Proof.
  intros g idb m m' lo hi (H & Hok) L MU D. split; [|exact Hok].
  unfold IDB in *. apply (u6_ba_keep m m' lo hi _ _ MU H). rewrite L. exact D.
Qed.

Lemma u6_FGb_keep : forall g st m m' lo hi, FGb g st m -> length st = 72%nat -> munch [(lo, hi)] m m' ->
  u6_out lo hi (spk g 120) 72 -> FGb g st m'.
Proof.
  intros g st m m' lo hi (H & Hok) L MU D. split; [|exact Hok].
  unfold FGB in *. apply (u6_ba_keep m m' lo hi _ _ MU H). rewrite L. exact D.
Qed.

(* FSb reads `first` [sp+36, sp+41 + n) only (n <= 255): a byte map that keeps [sp+36, sp+297) keeps FSb, for any
   frag st' that FI relates to the same state. *)
Lemma u6_FSb_mem : forall g s st st' m m',
  (forall a bs, spk g 36 <= a -> a + Z.of_nat (length bs) <= spk g 297 -> bytes_at rsegs m a bs ->
     bytes_at rsegs m' a bs) ->
  0 <= fs_nb s <= 255 -> FSb g s st m -> FI st' s -> FSb g s st' m'.
Proof.
  intros g s st st' m m' T Hn H HFI. unfold FSb, u32, b8 in *.
  destruct H as (H36 & H40 & HB & HL & _).
  refine (conj _ (conj _ (conj _ (conj HL HFI)))).
  - apply T; [unfold spk; lia | rewrite length_le4; unfold spk; lia | exact H36].
  - apply T; [unfold spk; lia | cbn [length]; unfold spk; lia | exact H40].
  - apply T; [unfold spk; lia | rewrite HL; unfold spk; lia | exact HB].
Qed.

Lemma u6_FSb_keep : forall g s st m m' lo hi, FSb g s st m -> 0 <= fs_nb s <= 255 ->
  munch [(lo, hi)] m m' -> u6_out lo hi (spk g 36) 261 -> FSb g s st m'.
Proof.
  intros g s st m m' lo hi H Hn MU D.
  apply (u6_FSb_mem g s st st m m'); [| exact Hn | exact H | unfold FSb in H; tauto].
  intros a bs H1 H2 Hb. apply (u6_ba_keep m m' lo hi a bs MU Hb). unfold u6_out, spk in *. lia.
Qed.

Lemma u6_IFS_keep : forall g j m m' lo hi, IFS g j m -> munch [(lo, hi)] m m' -> u6_ai g lo hi -> IFS g j m'.
Proof.
  intros g j m m' lo hi (HI & HG & HS) MU (D76 & D120 & D36).
  destruct (u6_inv (g_in g) j) as (L1 & L2 & _).
  pose proof (u6_fs_nb_range (g_in g) j) as Hnb.
  exact (conj (u6_IDb_keep g _ m m' lo hi HI L1 MU D76)
              (conj (u6_FGb_keep g _ m m' lo hi HG L2 MU D120)
                    (u6_FSb_keep g _ _ m m' lo hi HS Hnb MU D36))).
Qed.

Lemma u6_EA_keep : forall g j phi regs regs' m m' lo hi,
  EA g j phi regs m -> u6_kT regs regs' -> getr regs' 19 = getr regs 19 -> getr regs' 27 = getr regs 27 ->
  munch [(lo, hi)] m m' -> u6_av g phi (t_len (g_in g) j) lo hi -> u6_ai g lo hi -> EA g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (HB & HI) K E19 E27 MU D DI.
  exact (conj (u6_FB_keep g j phi regs regs' m m' lo hi HB K E19 E27 MU D) (u6_IFS_keep g (S j) m m' lo hi HI MU DI)).
Qed.

(* EQ (U13dac, v1.9 pc 0x13da0) from EA and is_8819: s3 and s11 are not read. *)
Lemma u6_EQ_keep : forall g j phi regs regs' m m' lo hi,
  EA g j phi regs m -> t_8819 (g_in g) j = true -> u6_kT regs regs' -> munch [(lo, hi)] m m' ->
  u6_av g phi (t_len (g_in g) j) lo hi -> u6_ai g lo hi -> EQ g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi ((HT & H7 & _ & _ & H2 & HC) & HI) H88 K MU D DI.
  pose proof K as (E8 & E9 & E18 & E20 & E21 & E22 & E23 & E24 & E25).
  refine (conj (u6_FT_keep g j phi regs regs' m m' lo hi HT K MU D) (conj _ (conj _
    (conj (u6_VC_keep g j phi regs regs' m m' lo hi HC K MU D) (conj (u6_IFS_keep g (S j) m m' lo hi HI MU DI) H88))))).
  - unfold V7, rg in *. rewrite E25. exact H7.
  - unfold V2, rg in *. rewrite E20. exact H2.
Qed.


Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the continuation. *)
Lemma u6_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP).
    + exact MU'.
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* Φ, the frame turn's harness block, lies in the heap: [4096, alloc_ceiling). *)
Lemma u6_phi_rng : forall g phi n L A regs mem md,
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  4096 <= phi /\ phi + n <= alloc_ceiling.
Proof.
  intros g phi n L A regs mem md HFR HP.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (phi, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity. }
  apply blocks_In in Hin as (p & Ep & Hin).
  destruct (mr_blocks_range B _ (aa_laws (APIf rc)) L A mem md p n HM Hin) as (H1 & H2).
  subst phi. lia.
Qed.

Lemma u6_S_bnd : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  alloc_ceiling + 65536 <= g_S g /\ g_S g <= 2 ^ 47 /\ g_S g mod 16 = 0 /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ ro_agree rsegs mem.
Proof.
  intros g hb L A regs mem md HFR.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  destruct (sl_fr_bnd B APIf ra empty FF g hb L A regs mem md HFR) as (E2 & _ & _ & _ & HMI).
  unfold SLOT_K, SLOT_STACK in HSK.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact E2 | exact HMI].
Qed.

End S.


(* ---- G06: opens_record as the ubsan code tests it, its branches, v1.9's store into `first` (first_frag F2) ---- *)
(* Φ[26] in 1 .. 22 as the code tests it: beqz (v1.9 0x13c14), then 22 <u Φ[26] (v1.9 0x13c24). *)
Definition u6_opn (so : bool) (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) : bool :=
  so && ((bv_unsigned b16 =? 205) && (bv_unsigned b17 =? 234) && (bv_unsigned b18 =? 4) && (bv_unsigned b19 =? 1) &&
         (bv_unsigned b22 =? 0) && (bv_unsigned b23 =? 2) && (bv_unsigned b24 =? 0) && (bv_unsigned b25 =? 254) &&
         (negb (bv_unsigned b26 =? 0) && negb (22 <? bv_unsigned b26))).

Lemma u6_r26 : forall P x, 0 <= x -> P && (1 <=? x) && (x <=? 22) = P && (negb (x =? 0) && negb (22 <? x)).
Proof.
  intros P x Hx. destruct P; [|reflexivity].
  destruct (Z.leb_spec 1 x), (Z.leb_spec x 22), (Z.eqb_spec x 0), (Z.ltb_spec 22 x); cbn [andb negb];
    first [reflexivity | exfalso; lia].
Qed.

Lemma u6_opn_eq : forall inp j,
  u6_opn (t_sum_ok inp j) (nth 16 (t_g inp j) (Z_to_bv 8 0)) (nth 17 (t_g inp j) (Z_to_bv 8 0))
    (nth 18 (t_g inp j) (Z_to_bv 8 0)) (nth 19 (t_g inp j) (Z_to_bv 8 0)) (nth 22 (t_g inp j) (Z_to_bv 8 0))
    (nth 23 (t_g inp j) (Z_to_bv 8 0)) (nth 24 (t_g inp j) (Z_to_bv 8 0)) (nth 25 (t_g inp j) (Z_to_bv 8 0))
    (nth 26 (t_g inp j) (Z_to_bv 8 0)) = f_opens (t_len inp j) (t_g inp j).
Proof.
  intros inp j. rewrite u6_opens_eq, u6_r26 by apply u6_bat_range. reflexivity.
Qed.

Lemma u6_eqz : forall (b : byte) k, 0 <= k < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 k) = (bv_unsigned b =? k).
Proof. intros b k Hk. unfold zxb. pose proof (RcLib.byte_range b). apply u6_eqb; lia. Qed.

Lemma u6_ltz : forall (b : byte) k, 0 <= k < 2 ^ 64 -> bv_ltu (Z_to_bv 64 k) (zxb b) = (k <? bv_unsigned b).
Proof. intros b k Hk. unfold zxb. pose proof (RcLib.byte_range b). apply u6_ltu; lia. Qed.

(* The cells a `sw` and a `sb` leave (G06's first->have, first->n). *)
Lemma u6_c4 : forall m A v, Step.rw_cells rsegs m A [Cells.C4 v] -> bytes_at rsegs m A (le4 v).
Proof.
  intros m A v H. pose proof (sl_cells_bytes m A _ H) as X.
  cbn [Cells.cells_bytes Cells.cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma u6_c1 : forall m A b, Step.rw_cells rsegs m A [Cells.C1 b] -> bytes_at rsegs m A [b].
Proof.
  intros m A b H. pose proof (sl_cells_bytes m A _ H) as X.
  cbn [Cells.cells_bytes Cells.cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma u6_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma u6_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma u6_ba_byte : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite <- (u6_firstn1 bs k (Z_to_bv 8 0) Hk). apply u6_ba_sub; [exact H | lia].
Qed.

(* `first`'s body after the copy of Φ[27 .. 27 + n) to a: fg_body Φ, of length n (n <= 22). *)
Lemma u6_fgbody_len : forall g, length g = 50%nat -> fg_n g <= 22 ->
  length (fg_body g) = Z.to_nat (fg_n g).
Proof.
  intros g Hg Hn. pose proof (u6_bat_range g 26) as R. unfold fg_body, fg_n in *.
  apply u6_bsl_len; lia.
Qed.

Lemma u6_ba_fgbody : forall m a g, bytes_at rsegs m a g -> length g = 50%nat -> fg_n g <= 22 ->
  bytes_at rsegs m (a + 27) (fg_body g).
Proof.
  intros m a g H Hg Hn. pose proof (u6_bat_range g 26) as R.
  pose proof (u6_ba_sub m a g 27 (Z.to_nat (fg_n g)) H ltac:(unfold fg_n in *; lia)) as X.
  unfold fg_body, bsl. change (Z.to_nat 27) with 27%nat.
  change (Z.of_nat 27) with 27 in X. exact X.
Qed.

(* ---- E01-E03: is_8819 gives p.dst = Φ[0 .. 6) and p.src = Φ[6 .. 12) in B (struct P5.2); memcmp of equal bytes ---- *)
Lemma u6_8819 : forall inp j, t_8819 inp j = true ->
  50 <= t_len inp j /\ firstn 6 (skipn 10 (t_B inp j)) = firstn 6 (skipn 0 (t_g inp j)) /\
  firstn 6 (skipn 4 (t_B inp j)) = firstn 6 (skipn 6 (t_g inp j)).
Proof.
  intros inp j H.
  assert (Hh : RcParse.cp_hdr (t_len inp j) (t_g inp j) = true) by exact H.
  destruct (proj1 (RcParse.cp_hdr_spec _ _) Hh) as (Hn & _ & _).
  assert (Hk : fst (RcParse.ctrlparse (t_len inp j) (t_g inp j)) <> 0).
  { unfold RcParse.ctrlparse. rewrite Hh. cbn [fst]. pose proof (RcParse.cp_kind_range (t_g inp j)). lia. }
  pose proof (RcParse.ctrlparse_fields _ _ Hk) as X. cbv zeta in X. destruct X as (HS & HD & _).
  pose proof (RcParse.ctrlparse_length (t_len inp j) (t_g inp j)) as LB.
  pose proof (u6_g_len inp j) as LG.
  split; [exact Hn|]. unfold t_B.
  split; (apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0);
          [rewrite !length_firstn, !length_skipn, LB, LG; reflexivity|];
          intros i Hi; rewrite length_firstn, length_skipn, LB in Hi;
          rewrite !u6_nth_firstn by lia; rewrite !u6_nth_skipn; change (Z_to_bv 8 0) with RcParse.cp_z).
  - rewrite (HD i ltac:(lia)). reflexivity.
  - rewrite (HS i ltac:(lia)). reflexivity.
Qed.

Lemma u6_mcmp_refl : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* ---- E03: p.counter = B[20 .. 22) = Φ[14], Φ[15] (struct P5.2); k = 1 exactly when Φ[16] = Φ[17] = 0 (P5.3);
   sum_ok is the block sum of Φ[18 .. 50) on the is_8819 path; the code's 16-bit compare ---- *)
Lemma u6_firstn2 : forall (l : list byte) k d, (S k < length l)%nat ->
  firstn 2 (skipn k l) = [nth k l d; nth (S k) l d].
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k].
  - destruct l as [|y l]; [cbn in H; lia | reflexivity].
  - cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma u6_cnt : forall inp j, t_8819 inp j = true ->
  firstn 2 (skipn 20 (t_B inp j)) = [nth 14 (t_g inp j) (Z_to_bv 8 0); nth 15 (t_g inp j) (Z_to_bv 8 0)].
Proof.
  intros inp j H.
  assert (Hh : RcParse.cp_hdr (t_len inp j) (t_g inp j) = true) by exact H.
  assert (Hk : fst (RcParse.ctrlparse (t_len inp j) (t_g inp j)) <> 0).
  { unfold RcParse.ctrlparse. rewrite Hh. cbn [fst]. pose proof (RcParse.cp_kind_range (t_g inp j)). lia. }
  pose proof (RcParse.ctrlparse_fields _ _ Hk) as X. cbv zeta in X.
  destruct X as (_ & _ & _ & H20 & H21 & _).
  unfold t_B. rewrite (u6_firstn2 _ 20 (Z_to_bv 8 0)) by (rewrite RcParse.ctrlparse_length; lia).
  change (Z_to_bv 8 0) with RcParse.cp_z. rewrite H20, H21. reflexivity.
Qed.

Lemma u6_filler : forall inp j, t_8819 inp j = true ->
  (t_k inp j = 1 <-> bv_unsigned (nth 16 (t_g inp j) (Z_to_bv 8 0)) = 0 /\
                     bv_unsigned (nth 17 (t_g inp j) (Z_to_bv 8 0)) = 0).
Proof.
  intros inp j H. unfold t_k. rewrite RcParse.ctrlparse_filler.
  assert (Hh : RcParse.cp_hdr (t_len inp j) (t_g inp j) = true) by exact H.
  rewrite Hh. unfold RcParse.cp_v, RcParse.cp_b, RcParse.cp_z. tauto.
Qed.

Lemma u6_sum8819 : forall inp j, t_8819 inp j = true ->
  t_sum_ok inp j = (blocksum (firstn 32 (skipn 18 (t_g inp j))) =? 0).
Proof.
  intros inp j H. unfold t_sum_ok.
  assert (Hb : t_big inp j = true).
  { unfold t_8819 in H. apply andb_prop in H as (H & _). apply andb_prop in H as (H & _). exact H. }
  rewrite Hb. cbn [andb]. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn, u6_g_len. lia.
Qed.

Lemma u6_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
Proof.
  intros x y Hx Hy.
  assert (Lg : Z.log2 y < 8).
  { destruct (Z.eq_dec y 0) as [->|Hy0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (L : Z.land (Z.shiftl x 8) y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 y i) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* E03's v1.9 0x13cac-0x13cb0: (hi << 8) | lo. *)
Lemma u6_orshl : forall hi lo : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo)) =
  256 * bv_unsigned hi + bv_unsigned lo.
Proof.
  intros hi lo. pose proof (RcLib.byte_range hi). pose proof (RcLib.byte_range lo).
  assert (Eh : bv_unsigned (zxb hi) = bv_unsigned hi) by (unfold zxb; apply MState.unsigned_lit; lia).
  assert (El : bv_unsigned (zxb lo) = bv_unsigned lo) by (unfold zxb; apply MState.unsigned_lit; lia).
  rewrite Eh, El.
  rewrite (MState.unsigned_lit (Z.shiftl (bv_unsigned hi) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite u6_lor_shl8 by lia. lia.
Qed.

Lemma u6_le2 : forall hi lo : byte, le2 (Z_to_bv 64 (256 * bv_unsigned hi + bv_unsigned lo)) = [lo; hi].
Proof.
  intros hi lo. pose proof (RcLib.byte_range hi). pose proof (RcLib.byte_range lo).
  unfold le2. rewrite MState.unsigned_lit by lia. cbn [Z_to_le_bytes]. f_equal; [|f_equal].
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    Z.div_mod_to_equations. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma u6_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* E03's v1.9 0x13cdc and 0x13ce0-0x13ce4: seqz of a loaded byte, and seqz (k - 1). *)
Lemma u6_sltb : forall b : byte, PropExec.v_sltiu (zxb b) 1 = Z_to_bv 64 (b2z (bv_unsigned b =? 0)).
Proof.
  intros b. pose proof (RcLib.byte_range b). unfold PropExec.v_sltiu, zxb. rewrite MState.unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.ltb_spec (bv_unsigned b) 1); destruct (Z.eqb_spec (bv_unsigned b) 0); cbn [b2z];
    first [reflexivity | exfalso; lia].
Qed.

Lemma u6_sltk : forall k, 0 <= k <= 13 -> PropExec.v_sltiu (Z_to_bv 64 (k + -1)) 1 = Z_to_bv 64 (b2z (k =? 1)).
Proof.
  intros k Hk. unfold PropExec.v_sltiu. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.ltb_spec ((k + -1) mod 18446744073709551616) 1);
    destruct (Z.eqb_spec k 1); cbn [b2z];
    first [reflexivity | exfalso; Z.div_mod_to_equations; lia].
Qed.

(* ---- E04: the head-amp record (struct P5.4), the bytes one nth each, AF11 (the inline record sum) ---- *)
(* One byte of a bytes_at as the read the step tactic consumes. *)
Lemma u6_rd1 : forall m a bs k d, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [nth k bs d].
Proof.
  intros m a bs k d H Hk. pose proof (bytes_at_read rsegs m a bs (Z.of_nat k) 1 H ltac:(lia) ltac:(lia)) as R.
  rewrite Nat2Z.id in R. rewrite (u6_firstn1 bs k d Hk) in R. exact R.
Qed.

(* The n bytes from index k of a list, one nth each (default 0). *)
Fixpoint u6_nths (bs : list byte) (k n : nat) : list byte :=
  match n with
  | O => []
  | S n' => nth k bs (Z_to_bv 8 0) :: u6_nths bs (S k) n'
  end.

Lemma u6_skipn_cons : forall (bs : list byte) k d, (k < length bs)%nat -> skipn k bs = nth k bs d :: skipn (S k) bs.
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma u6_firstn_nths : forall n bs k, (k + n <= length bs)%nat -> firstn n (skipn k bs) = u6_nths bs k n.
Proof.
  induction n as [|n IH]; intros bs k H; [reflexivity|].
  rewrite (u6_skipn_cons bs k (Z_to_bv 8 0)) by lia. cbn [firstn u6_nths]. f_equal. apply IH. lia.
Qed.

Lemma u6_bytes_nths : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (u6_nths bs k n).
Proof. intros m a bs k n H Hk. rewrite <- u6_firstn_nths by exact Hk. exact (u6_ba_sub m a bs k n H Hk). Qed.

Lemma u6_bsl_nths : forall bs k n, 0 <= k -> 0 <= n -> (Z.to_nat k + Z.to_nat n <= length bs)%nat ->
  bsl bs k n = u6_nths bs (Z.to_nat k) (Z.to_nat n).
Proof. intros bs k n Hk Hn H. unfold bsl. apply u6_firstn_nths. exact H. Qed.

(* struct P5.4: kind 6 needs Φ[18] = 4 and Φ[19] = 3. *)
Lemma u6_k6 : forall inp j, t_k inp j = 6 ->
  RcParse.cp_v (t_g inp j) 18 = 4 /\ RcParse.cp_v (t_g inp j) 19 = 3.
Proof.
  intros inp j H. unfold t_k in H. apply RcParse.ctrlparse_headamp in H as (_ & R & _).
  unfold RcParse.cp_rec in R. rewrite !andb_true_iff in R. destruct R as ((_ & R18) & R19).
  apply Z.eqb_eq in R18. apply Z.eqb_eq in R19. split; assumption.
Qed.

Lemma u6_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof. intros inp j. apply RcParse.ctrlparse_kind_range. Qed.

Lemma u6_big_8819 : forall inp j, t_8819 inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_8819, t_big in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Z.leb_le. exact H.
Qed.

Lemma u6_eqb_wrap : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 =? y mod 2 ^ 64).
Proof. intros x y. unfold bv_eqb. rewrite !MState.unsigned_lit_wrap. reflexivity. Qed.

Lemma u6_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* AF11: not (Φ + 34) = 2^64 - 1 - (Φ + 34), so `bltu a3,a1` (v1.9 0x13d74) is not taken while Φ + 34 + i does not
   wrap. *)
Lemma u6_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = Z.ones 64 - x.
Proof.
  intros x Hx.
  assert (Hb : forall i, 64 <= i -> Z.testbit x i = false).
  { intros i Hi. destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  assert (D : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. cbn [negb]. apply andb_false_r.
    - rewrite (Hb i) by lia. reflexivity. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x D).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (Hb i) by lia. reflexivity.
Qed.

Lemma u6_af11 : forall x c i, c = Z.ones 64 -> 0 <= x -> x + 64 <= 2 ^ 64 -> 0 <= i < 64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) c)) (Z_to_bv 64 i) = false.
Proof.
  intros x c i -> H0 H1 Hi. unfold bv_ltu. rewrite (MState.unsigned_lit x) by lia.
  rewrite u6_lxor_ones by lia. rewrite !MState.unsigned_lit by (rewrite ?Z.ones_equiv; lia).
  apply Z.ltb_ge. rewrite Z.ones_equiv. lia.
Qed.

(* andi 127; seqz; addi -1 of the record sum S (v1.9 0x13d8c-0x13d94). *)
Lemma u6_wv : forall S, 0 <= S < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 127)) 1) + -1) =
  Z_to_bv 64 (if S mod 128 =? 0 then 0 else -1).
Proof.
  intros S HS. rewrite (MState.unsigned_lit S) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound S 128 ltac:(lia)) as HM.
  unfold PropExec.v_sltiu. rewrite (MState.unsigned_lit (S mod 128)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (S mod 128) 1); destruct (Z.eqb_spec (S mod 128) 0); try lia;
    rewrite MState.unsigned_lit by lia; f_equal; lia.
Qed.

(* ---- branch tactics ---- *)
(* Replace the condition of the branch at the head of the goal by its value. *)
Ltac u6_br v pf :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (symmetry; pf); cbv iota
  end.

Ltac u6_zdec :=
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  end; cbn [negb andb orb]; first [reflexivity | exfalso; lia].

(* The unsigned value of every word literal folded, of every other Z_to_bv 64 x rewritten to x (range by lia). *)
Ltac u6_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
      first [ Step.is_Zlit x; let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 x)) in
                change (bv_unsigned (Z_to_bv 64 x)) with v
            | rewrite (MState.unsigned_lit x) by lia ]
  end.

(* A branch decided by the bounds in context (the UBSan checks): v is its value. *)
Ltac u6_nt v :=
  u6_br v ltac:(unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; u6_ux; u6_zdec).
