(* Helpers for the segment lemmas of batch b6 (G04-G06, E01-E03) of fuzz_ctrl LLVMFuzzerTestOneInput (plain):
   the frame-loop model facts (cursor range, Φ's bytes, the frame-state invariants, the fragment arm's CLOSE facts,
   first_frag F2 (FI kept) and F3 (P4l)), the transport of the cut bundles across a run that writes one interval,
   and b6_mid (sl_mid with the write set's munch over the unnormalized memory).
   libreac v1.9.0 (SlotInv.v header): the frame objects 16 bytes higher (our sp+76, frag sp+82, id sp+154, the frag
   copy sp+192, the parsed block sp+1752, the fragment outputs sp+1728 .. sp+1752), type_filler at sp+24 and the
   record's body pointer at sp+32 (one 16-byte item of b6_av), sum_ok in s1 and is_8819 in s0 (V0 / VC); the
   frame state is v1.9's `first` (SlotModel fstate (have, nb, body), FSb: have [sp+16], nb in s3, the nb body bytes
   at sp+40): b6_fs_S / b6_first / b6_FI_S carry the body, b6_P4l states the address through SlotModel.joined_byte
   (fuzz/fuzz_ctrl.c v1.9.0:251-254), and the FSb transport reads [sp+16, sp+76) and s3. rule 24: no function
   proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcParse RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists ---- *)
Lemma b6_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d H.
  - destruct n; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma b6_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma b6_bat_range : forall l i, 0 <= bat l i < 256.
Proof. intros l i. unfold bat. apply RcLib.byte_range. Qed.

Lemma b6_bsl_len : forall l k n, 0 <= k -> 0 <= n -> Z.of_nat (length l) >= k + n ->
  length (bsl l k n) = Z.to_nat n.
Proof. intros l k n Hk Hn H. unfold bsl. rewrite length_firstn, length_skipn. lia. Qed.

(* fg_clear: byte 6 becomes 0, every other byte is kept. *)
Lemma b6_clear : forall x, (7 <= length x)%nat ->
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
Lemma b6_inb : forall inp k, 0 <= inb inp k < 256.
Proof. intros inp k. unfold inb, RcIdentModel.bz. apply RcLib.byte_range. Qed.

Lemma b6_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH]; cbn [fc].
  - unfold c0, nlen. lia.
  - pose proof (b6_inb inp (fc inp j)). pose proof (b6_inb inp (fc inp j + 1)).
    unfold f_next, f_body, f_len, f_L, f_h, f_left.
    destruct (2 <=? nlen inp - fc inp j); cbv beta iota; lia.
Qed.

Lemma b6_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (b6_fc_range inp j) as R.
  pose proof (b6_inb inp (fc inp j)). pose proof (b6_inb inp (fc inp j + 1)).
  unfold t_len, t_body, f_len, f_body, f_L, f_h, f_left.
  destruct (2 <=? nlen inp - fc inp j); cbv beta iota; lia.
Qed.

Lemma b6_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (b6_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi, t_len, t_body, nlen in *. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma b6_g_eq : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j H. unfold t_g, fr50. rewrite firstn_app.
  rewrite b6_phi_len. replace (50 - Z.to_nat (t_len inp j))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma b6_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

(* ---- one turn of the frame state ---- *)
Lemma b6_tID_S : forall inp j,
  t_ID inp (S j) = fg_id (t_IDr inp j) (t_len inp j) (t_FG inp j) (t_g inp j).
Proof.
  intros inp j. unfold t_ID, t_IDr, t_FG. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma b6_tFG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma b6_fs_S : forall inp j,
  fst_at inp (S j) =
  if f_opens (t_len inp j) (t_g inp j)
  then FSt (t_ID inp (S j)) (t_FGf inp j) 1 (bat (t_g inp j) 26) (fg_body (t_g inp j))
  else FSt (t_ID inp (S j)) (t_FGf inp j) (fs_have (fst_at inp j)) (fs_nb (fst_at inp j))
         (fs_body (fst_at inp j)).
Proof.
  intros inp j. rewrite b6_tID_S. unfold t_FGf, t_IDr, t_FG, t_ID. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

(* The fragment arm's class with all five pointers non-zero. *)
Lemma b6_or0 : ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) = false.
Proof. reflexivity. Qed.

Lemma b6_close : forall len st g, fg_rf len st g = 1 ->
  fcls len st g = FgClose /\ fg_fr len g = true /\ bat g 19 <> 1 /\ fg_keep st g = true /\
  fg_close st g = true.
Proof.
  intros len st g H. unfold fg_rf, fcls, fg_class in *. rewrite b6_or0 in *.
  destruct (fg_fr len g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate H|].
  destruct (fg_keep st g); cbn [negb] in *; [|cbn in H; discriminate H].
  destruct (fg_close st g); cbn [negb] in *; [|cbn in H; discriminate H].
  apply Z.eqb_neq in E19. auto.
Qed.

Lemma b6_rf01 : forall len st g, fg_rf len st g = 0 \/ fg_rf len st g = 1.
Proof.
  intros len st g. unfold fg_rf, fcls, fg_class. rewrite b6_or0.
  destruct (fg_fr len g); cbn [negb]; [|left; reflexivity].
  destruct (bat g 19 =? 1); [left; reflexivity|].
  destruct (fg_keep st g); cbn [negb]; [|left; reflexivity].
  destruct (fg_close st g); cbn [negb]; [right | left]; reflexivity.
Qed.

Lemma b6_fr_n : forall len g, fg_fr len g = true -> 50 <= len /\ 1 <= fg_n g <= 22.
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

(* fg_first: the state FIRST leaves; its bytes 8 .. 8 + n are the FIRST body (`first`'s body). *)
Lemma b6_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat /\ bat (fg_first st g) 6 = 1 /\ bat (fg_first st g) 7 = fg_n g /\
  bsl (fg_first st g) 8 (fg_n g) = fg_body g.
Proof.
  intros st g Hst Hg Hn.
  assert (L6 : length (bsl g 6 6) = 6%nat) by (apply b6_bsl_len; lia).
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply b6_bsl_len; lia).
  assert (E : fg_first st g = bsl g 6 6 ++ Z_to_bv 8 1 :: nth 26 g (Z_to_bv 8 0) :: fg_body g ++
                skipn (Z.to_nat (8 + fg_n g)) st) by reflexivity.
  assert (B6 : bat (fg_first st g) 6 = 1).
  { unfold bat. change (Z.to_nat 6) with 6%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  assert (B7 : bat (fg_first st g) 7 = fg_n g).
  { unfold fg_n, bat. change (Z.to_nat 7) with 7%nat. rewrite E, app_nth2 by lia. rewrite L6. reflexivity. }
  split; [|split; [exact B6|]; split; [exact B7|]].
  - rewrite E, length_app. cbn [length]. rewrite length_app, LB, length_skipn, L6, Hst. lia.
  - assert (K1 : forall (X Y : list byte) n, length X = n -> skipn n (X ++ Y) = Y).
    { intros X Y n <-. induction X as [|x X IH]; cbn; [reflexivity | exact IH]. }
    assert (K2 : forall (X Y : list byte) n, length X = n -> firstn n (X ++ Y) = X).
    { intros X Y n <-. induction X as [|x X IH]; cbn; [reflexivity | f_equal; exact IH]. }
    assert (E2 : fg_first st g = (bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)]) ++
                   (fg_body g ++ skipn (Z.to_nat (8 + fg_n g)) st)) by (rewrite <- app_assoc; exact E).
    unfold bsl at 1. change (Z.to_nat 8) with 8%nat.
    rewrite E2, K1 by (rewrite length_app, L6; reflexivity).
    apply K2. exact LB.
Qed.

(* fg_join under KEEP, from a state with frag_ok. *)
Lemma b6_join : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  1 <= fg_lf st <= 22 -> fg_T st g <= 64 ->
  length (fg_join st g) = 72%nat /\
  (11 <= fg_lf st -> bat (fg_join st g) 17 = bat st 17 /\ bat (fg_join st g) 18 = bat st 18).
Proof.
  intros st g Hst Hg Hn Hl HT. unfold fg_T in HT.
  assert (LB : length (fg_body g) = Z.to_nat (fg_n g)) by (unfold fg_body; apply b6_bsl_len; lia).
  unfold fg_join, fg_T.
  split; [rewrite !length_app, length_firstn, LB, length_skipn; lia|].
  intros H11. unfold bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
  rewrite !app_nth1 by (rewrite length_firstn; lia). rewrite !b6_nth_firstn by lia. split; reflexivity.
Qed.

(* One turn keeps the frag's length and frag_ok (struct.reac_identity_frag F2). *)
Lemma b6_fg_st_inv : forall len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  length (fg_st len st g) = 72%nat /\ frag_ok (fg_st len st g).
Proof.
  intros len st g Hst Hg (HF1 & HF2).
  unfold fg_st, fcls, fg_class. rewrite b6_or0.
  destruct (fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|split; [exact Hst | split; assumption]].
  destruct (b6_fr_n len g Efr) as (_ & Hn).
  destruct (bat g 19 =? 1); cbn [fg_next].
  { destruct (b6_first st g Hst Hg Hn) as (L & B6 & B7 & _).
    split; [exact L|]. unfold frag_ok. rewrite B6, B7. split; [right; reflexivity|]. intros _. exact Hn. }
  destruct (fg_keep st g) eqn:Ek; cbn [negb fg_next].
  2:{ destruct (b6_clear st ltac:(lia)) as (L & B6 & _). split; [lia|]. unfold frag_ok. rewrite B6.
      split; [left; reflexivity | intros X; discriminate X]. }
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat st 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  destruct (b6_join st g Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (b6_clear (fg_join st g) ltac:(lia)) as (L & B6 & _).
  destruct (fg_close st g); cbn [negb fg_next];
    (split; [lia|]; unfold frag_ok; rewrite B6; split; [left; reflexivity | intros X; discriminate X]).
Qed.

Lemma b6_inv : forall inp j,
  length (t_ID inp j) = 38%nat /\ length (t_FG inp j) = 72%nat /\ frag_ok (t_FG inp j).
Proof.
  intros inp j. induction j as [|j (IH1 & IH2 & IH3)].
  - split; [reflexivity|]. split; [reflexivity|].
    assert (E : bat z72 6 = 0) by (vm_compute; reflexivity).
    unfold t_FG; cbn [fst_at fs_fg fs0]. unfold frag_ok. rewrite E.
    split; [left; reflexivity | intros X; discriminate X].
  - rewrite b6_tID_S, b6_tFG_S.
    destruct (b6_fg_st_inv (t_len inp j) (t_FG inp j) (t_g inp j) IH2 (b6_g_len inp j) IH3) as (L & F).
    split; [|split; [exact L | exact F]].
    unfold fg_id, t_IDr, rp_id.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      repeat apply RcIdentModel.ING_length; exact IH1.
Qed.

(* ---- the fragment arm (rf = 1 is CLOSE) ---- *)
Lemma b6_close_facts : forall inp j, t_rf inp j = 1 ->
  14 <= fg_T (t_FG inp j) (t_g inp j) <= 64 /\ bat (t_FG inp j) 6 = 1 /\ 1 <= fg_lf (t_FG inp j) <= 22 /\
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)) /\ length (t_FGf inp j) = 72%nat /\
  recsum (bsl (t_FGf inp j) 15 (fg_T (t_FG inp j) (t_g inp j) - 8)) = 0.
Proof.
  intros inp j H. unfold t_rf in H.
  destruct (b6_close _ _ _ H) as (Ec & Efr & _ & Ek & Ecl).
  destruct (b6_inv inp j) as (_ & Hst & (HF1 & HF2)).
  pose proof (b6_g_len inp j) as Hg.
  destruct (b6_fr_n _ _ Efr) as (_ & Hn).
  unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
  apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
  assert (H1 : bat (t_FG inp j) 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
  specialize (HF2 H1).
  assert (EF : t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j))).
  { unfold t_FGf, fg_st. rewrite Ec. reflexivity. }
  destruct (b6_join (t_FG inp j) (t_g inp j) Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
  destruct (b6_clear (fg_join (t_FG inp j) (t_g inp j)) ltac:(lia)) as (L & _ & _ & SK).
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

(* `first`'s length nb is 0 before the first FIRST and Φ[26] in 1 .. 22 after one (fuzz/fuzz_ctrl.c v1.9.0:407-411). *)
Lemma b6_nb_range : forall inp j, 0 <= fs_nb (fst_at inp j) <= 22.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:E; cbn [fs_nb]; [|exact IH].
  unfold f_opens in E. apply andb_prop in E as [E _].
  destruct (b6_fr_n _ _ E) as (_ & Hn). unfold fg_n in Hn. lia.
Qed.

(* first_frag F3 (P4l, slot plan 6.4 item 11), v1.9.0: at CLOSE, FI(FG_j, FS_j) gives have = 1 and nb in 1 .. 22,
   and the address that the inlined joined_byte(&first, block, 9 / 10) rebuilds (fuzz/fuzz_ctrl.c v1.9.0:251-254,
   0x13984-0x139c8: body[i] when i < nb, else block[9 + i - nb]) is addr_f (SlotModel.fg_addr_joined). *)
Lemma b6_P4l : forall inp j, t_rf inp j = 1 -> FI (t_FG inp j) (fst_at inp j) ->
  fs_have (fst_at inp j) = 1 /\ 1 <= fs_nb (fst_at inp j) <= 22 /\
  fg_addr (t_FG inp j) (t_g inp j) =
    256 * joined_byte (fst_at inp j) (t_g inp j) 9 + joined_byte (fst_at inp j) (t_g inp j) 10.
Proof.
  intros inp j H HFI. pose proof HFI as (FI1 & _).
  destruct (b6_close_facts inp j H) as (HT & H6 & Hl & _).
  destruct (FI1 H6) as (Hh & Hnb).
  destruct (b6_inv inp j) as (_ & Hst & Hok).
  pose proof (b6_g_len inp j) as Hg.
  unfold t_rf in H. destruct (b6_close _ _ _ H) as (_ & Efr & _).
  destruct (b6_fr_n _ _ Efr) as (_ & Hn).
  unfold fg_lf in Hl.
  split; [exact Hh|]. split; [lia|].
  apply fg_addr_joined; [exact Hst | exact Hok | exact HFI | exact H6 | | lia].
  rewrite Hg. change (Z.of_nat 50) with 50. lia.
Qed.

(* first_frag F2 (FI kept): one turn keeps FI between the frag and `first` (have, nb, body). *)
Lemma b6_FI_S : forall inp j, FI (t_FG inp j) (fst_at inp j) -> FI (t_FG inp (S j)) (fst_at inp (S j)).
Proof.
  intros inp j HFI. rewrite b6_fs_S, b6_tFG_S.
  destruct (b6_inv inp j) as (_ & Hst & _). pose proof (b6_g_len inp j) as Hg.
  unfold t_FGf, fg_st, fcls, fg_class. rewrite b6_or0.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo.
  - unfold f_opens in Eo. apply andb_prop in Eo as (Efr & E19).
    rewrite Efr, E19. cbn [negb fg_next].
    destruct (b6_fr_n _ _ Efr) as (_ & Hn).
    destruct (b6_first (t_FG inp j) (t_g inp j) Hst Hg Hn) as (_ & B6 & B7 & B8).
    unfold FI. cbn [fs_have fs_nb fs_body]. rewrite B7. unfold fg_n in B8.
    split; [intros _; split; [reflexivity | unfold fg_n; reflexivity]|].
    intros _. symmetry. exact B8.
  - unfold f_opens in Eo.
    destruct (fg_fr (t_len inp j) (t_g inp j)) eqn:Efr; cbn [negb fg_next]; [|exact HFI].
    cbn [andb] in Eo. rewrite Eo.
    destruct (b6_inv inp j) as (_ & _ & (HF1 & HF2)).
    destruct (fg_keep (t_FG inp j) (t_g inp j)) eqn:Ek; cbn [negb fg_next].
    2:{ destruct (b6_clear (t_FG inp j) ltac:(lia)) as (_ & B6 & _).
        unfold FI. rewrite B6. split; intros X; discriminate X. }
    destruct (b6_fr_n _ _ Efr) as (_ & Hn).
    unfold fg_keep, fg_hf in Ek. apply andb_prop in Ek as (Ek & HT). apply andb_prop in Ek as (Hh & _).
    apply Z.leb_le in HT. apply negb_true_iff, Z.eqb_neq in Hh.
    assert (H1 : bat (t_FG inp j) 6 = 1) by (destruct HF1 as [X|X]; [contradiction | exact X]).
    specialize (HF2 H1).
    destruct (b6_join (t_FG inp j) (t_g inp j) Hst Hg Hn ltac:(unfold fg_lf; lia) HT) as (LJ & _).
    destruct (b6_clear (fg_join (t_FG inp j) (t_g inp j)) ltac:(lia)) as (_ & B6 & _).
    destruct (fg_close (t_FG inp j) (t_g inp j)); cbn [negb fg_next];
      unfold FI; rewrite B6; split; intros X; discriminate X.
Qed.

(* opens_record (struct.first_frag Names) as the code tests it: len >= 50 and sum_ok, then the bytes. *)
Lemma b6_opens_eq : forall len g,
  f_opens len g = (50 <=? len) && (blocksum (skipn 18 g) =? 0) &&
    ((bat g 16 =? 205) && (bat g 17 =? 234) && (bat g 18 =? 4) && (bat g 19 =? 1) && (bat g 22 =? 0) &&
     (bat g 23 =? 2) && (bat g 24 =? 0) && (bat g 25 =? 254) && (1 <=? bat g 26) && (bat g 26 <=? 22)).
Proof.
  intros len g. unfold f_opens, fg_fr, fg_n.
  destruct (50 <=? len), (blocksum (skipn 18 g) =? 0), (bat g 16 =? 205), (bat g 17 =? 234), (bat g 18 =? 4),
    (bat g 19 =? 1), (bat g 19 =? 2), (bat g 22 =? 0), (bat g 23 =? 2), (bat g 24 =? 0), (bat g 25 =? 254),
    (1 <=? bat g 26), (bat g 26 <=? 22); reflexivity.
Qed.

Lemma b6_lens : forall inp j,
  length (t_IDr inp j) = 38%nat /\ length (t_FGf inp j) = 72%nat /\ frag_ok (t_FGf inp j).
Proof.
  intros inp j. rewrite <- b6_tFG_S. destruct (b6_inv inp (S j)) as (_ & L & F).
  split; [|split; [exact L | exact F]].
  destruct (b6_inv inp j) as (L1 & _).
  unfold t_IDr, rp_id. destruct (RcReply.ir (t_len inp j) (t_g inp j)); [apply RcIdentModel.ING_length|]; exact L1.
Qed.

(* ---- memory: Φ's bytes, sub-ranges ---- *)
Lemma b6_ba_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma b6_ba_g : forall m phi inp j, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H Hl. rewrite (b6_g_eq inp j Hl).
  rewrite <- (firstn_skipn 50 (t_phi inp j)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* ---- transport of the cut bundles across a run that writes only [lo, hi) ---- *)
Definition b6_out (lo hi a n : Z) : Prop := a + n <= lo \/ hi <= a.

(* s0, s1, s3-s11 kept (s2 apart: G06 sets it to -7). *)
Definition b6_kS (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = getr regs 19 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
  getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\
  getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

(* The ranges the bundles of G04-E03 read, apart from id (sp+154) and `first` ([sp+16, sp+76)): Φ, our, M7,
   type_filler + the body pointer (sp+24 .. 40), the parsed block, frag, the frag copy, the fragment outputs. *)
Definition b6_av (g : ghost) (phi len lo hi : Z) : Prop :=
  b6_out lo hi phi len /\ b6_out lo hi (spk g 76) 6 /\ b6_out lo hi (spk g 8) 8 /\
  b6_out lo hi (spk g 24) 16 /\ b6_out lo hi (spk g 1752) 36 /\ b6_out lo hi (spk g 82) 72 /\
  b6_out lo hi (spk g 192) 72 /\ b6_out lo hi (spk g 1728) 24.

Lemma b6_munch0 : forall m m', munch [] m m' -> munch [(0, 0)] m m'.
Proof. intros m m' H. apply (munch_weaken [] [(0, 0)] m m'); [intros x _; exact I | exact H]. Qed.

Lemma b6_av0 : forall g phi len, 0 <= phi -> 0 <= fsp g -> b6_av g phi len 0 0.
Proof. intros g phi len H1 H2. unfold b6_av, b6_out, spk. lia. Qed.

Lemma b6_out0 : forall a n, 0 <= a -> b6_out 0 0 a n.
Proof. intros a n H. unfold b6_out. lia. Qed.

Lemma b6_ba_keep : forall m m' lo hi a bs, munch [(lo, hi)] m m' -> bytes_at rsegs m a bs ->
  b6_out lo hi a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU H D. apply (bytes_at_transport rsegs [(lo, hi)] m m' a bs H MU).
  cbn [disjoint_from]. unfold b6_out in D. split; [exact D | exact I].
Qed.

Lemma b6_q64_keep : forall m m' lo hi a v, munch [(lo, hi)] m m' -> q64 m a v -> b6_out lo hi a 8 -> q64 m' a v.
Proof.
  intros m m' lo hi a v MU H D. unfold q64 in *. apply (b6_ba_keep m m' lo hi a _ MU H).
  rewrite length_le8. exact D.
Qed.

Lemma b6_u16_keep : forall m m' lo hi a v, munch [(lo, hi)] m m' -> u16 m a v -> b6_out lo hi a 2 -> u16 m' a v.
Proof.
  intros m m' lo hi a v MU H D. unfold u16 in *. apply (b6_ba_keep m m' lo hi a _ MU H).
  rewrite length_le2. exact D.
Qed.

Lemma b6_FT_keep : forall g j phi regs regs' m m' lo hi,
  FT g j phi regs m -> b6_kS regs regs' -> munch [(lo, hi)] m m' -> b6_av g phi (t_len (g_in g) j) lo hi ->
  FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (Hj & H26 & (H27 & H32 & H20) & H21 & HPhi & HOUR & HM7)
    (E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) MU (D1 & D2 & D3 & D4 & _).
  unfold FT, FC, rg in *. rewrite E26, E27, E20, E21.
  split; [exact Hj|]. split; [exact H26|].
  split; [split; [exact H27|]; split; [|exact H20]|].
  { apply (b6_q64_keep m m' lo hi _ _ MU H32). unfold b6_out, spk in *. lia. }
  split; [exact H21|]. split.
  - apply (b6_ba_keep m m' lo hi _ _ MU HPhi). rewrite b6_phi_len.
    pose proof (b6_len_range (g_in g) j). unfold b6_out in *. lia.
  - split.
    + unfold OURb in *. apply (b6_ba_keep m m' lo hi _ _ MU HOUR). rewrite OUR_length. exact D2.
    + exact (b6_q64_keep m m' lo hi _ _ MU HM7 D3).
Qed.

Lemma b6_VC_keep : forall g j phi regs regs' m m' lo hi,
  VC g j phi regs m -> b6_kS regs regs' -> munch [(lo, hi)] m m' -> b6_av g phi (t_len (g_in g) j) lo hi ->
  VC g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (H8 & H22 & HTF & HB)
    (E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) MU (_ & _ & _ & D4 & D5 & _).
  unfold VC, rg in *. rewrite E8, E22.
  split; [exact H8|]. split; [exact H22|].
  split; [apply (b6_q64_keep m m' lo hi _ _ MU HTF); unfold b6_out, spk in *; lia|].
  apply (b6_ba_keep m m' lo hi _ _ MU HB). unfold t_B. rewrite RcParse.ctrlparse_length. exact D5.
Qed.

Lemma b6_FB_keep : forall g j phi regs regs' m m' lo hi,
  FB g j phi regs m -> b6_kS regs regs' -> getr regs' 18 = getr regs 18 -> munch [(lo, hi)] m m' ->
  b6_av g phi (t_len (g_in g) j) lo hi -> FB g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (HT & H7 & H9 & H0 & H2 & HC) K E18 MU D.
  pose proof K as (E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  split; [exact (b6_FT_keep g j phi regs regs' m m' lo hi HT K MU D)|].
  unfold FV, V7, V9, V0, V2, rg in *. rewrite E23, E25, E9, E18.
  split; [exact H7|]. split; [exact H9|]. split; [exact H0|]. split; [exact H2|].
  exact (b6_VC_keep g j phi regs regs' m m' lo hi HC K MU D).
Qed.

Lemma b6_IDb_keep : forall g idb m m' lo hi, IDb g idb m -> length idb = 38%nat -> munch [(lo, hi)] m m' ->
  b6_out lo hi (spk g 154) 38 -> IDb g idb m'.
Proof.
  intros g idb m m' lo hi (H & Hok) L MU D. split; [|exact Hok].
  unfold IDB in *. apply (b6_ba_keep m m' lo hi _ _ MU H). rewrite L. exact D.
Qed.

Lemma b6_FGb_keep : forall g st m m' lo hi, FGb g st m -> length st = 72%nat -> munch [(lo, hi)] m m' ->
  b6_out lo hi (spk g 82) 72 -> FGb g st m'.
Proof.
  intros g st m m' lo hi (H & Hok) L MU D. split; [|exact Hok].
  unfold FGB in *. apply (b6_ba_keep m m' lo hi _ _ MU H). rewrite L. exact D.
Qed.

(* `first`: have [sp+16], nb in s3, the nb (<= 36) body bytes at sp+40, all inside [sp+16, sp+76). *)
Lemma b6_FSb_keep : forall g s st regs regs' m m' lo hi, FSb g s st regs m -> getr regs' 19 = getr regs 19 ->
  munch [(lo, hi)] m m' -> fs_nb s <= 36 -> b6_out lo hi (spk g 16) 60 -> FSb g s st regs' m'.
Proof.
  intros g s st regs regs' m m' lo hi (H16 & H19 & HB & HL & HFI) E19 MU Hnb D.
  split; [apply (b6_q64_keep m m' lo hi _ _ MU H16); unfold b6_out, spk in *; lia|].
  split; [unfold rg in *; rewrite E19; exact H19|].
  split; [apply (b6_ba_keep m m' lo hi _ _ MU HB); rewrite HL; unfold b6_out, spk in *; lia|].
  split; [exact HL | exact HFI].
Qed.

Lemma b6_GF_keep : forall g j phi regs regs' m m' lo hi,
  GF g j phi regs m -> b6_kS regs regs' -> getr regs' 18 = getr regs 18 -> munch [(lo, hi)] m m' ->
  b6_av g phi (t_len (g_in g) j) lo hi -> b6_out lo hi (spk g 154) 38 -> b6_out lo hi (spk g 16) 60 ->
  GF g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (HB & HI & HG & HS & Hbf & Hrf) K E18 MU D DI DS.
  pose proof D as (_ & _ & _ & _ & _ & D82 & D192 & D1728).
  pose proof K as (_ & _ & E19 & _).
  pose proof (b6_nb_range (g_in g) j) as Hnb.
  destruct (b6_inv (g_in g) j) as (_ & L2 & _). destruct (b6_lens (g_in g) j) as (L3 & L4 & _).
  split; [exact (b6_FB_keep g j phi regs regs' m m' lo hi HB K E18 MU D)|].
  split; [exact (b6_IDb_keep g _ m m' lo hi HI L3 MU DI)|].
  split; [exact (b6_FGb_keep g _ m m' lo hi HG L4 MU D82)|].
  split; [exact (b6_FSb_keep g _ _ regs regs' m m' lo hi HS E19 MU ltac:(lia) DS)|].
  split; [apply (b6_ba_keep m m' lo hi _ _ MU Hbf); rewrite L2; exact D192|].
  intros Hr. destruct (Hrf Hr) as (A & P & N).
  split; [apply (b6_u16_keep m m' lo hi _ _ MU A); unfold b6_out, spk in *; lia|].
  split; [apply (b6_q64_keep m m' lo hi _ _ MU P); unfold b6_out, spk in *; lia|].
  apply (b6_q64_keep m m' lo hi _ _ MU N); unfold b6_out, spk in *; lia.
Qed.

Lemma b6_EA_keep : forall g j phi regs regs' m m' lo hi,
  EA g j phi regs m -> b6_kS regs regs' -> getr regs' 18 = getr regs 18 -> munch [(lo, hi)] m m' ->
  b6_av g phi (t_len (g_in g) j) lo hi -> b6_out lo hi (spk g 154) 38 -> b6_out lo hi (spk g 16) 60 ->
  EA g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' lo hi (HT & H7 & H9 & H0 & H2 & HC & (HI & HG & HS)) K E18 MU D DI DS.
  pose proof K as (E8 & E9 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  pose proof D as (_ & _ & _ & _ & _ & D82 & _).
  pose proof (b6_nb_range (g_in g) (S j)) as Hnb.
  destruct (b6_inv (g_in g) (S j)) as (L1 & L2 & _).
  split; [exact (b6_FT_keep g j phi regs regs' m m' lo hi HT K MU D)|].
  unfold V7, V9, V0, V2m, rg in *. rewrite E23, E25, E9, E18.
  split; [exact H7|]. split; [exact H9|]. split; [exact H0|]. split; [exact H2|].
  split; [exact (b6_VC_keep g j phi regs regs' m m' lo hi HC K MU D)|].
  split; [exact (b6_IDb_keep g _ m m' lo hi HI L1 MU DI)|].
  split; [exact (b6_FGb_keep g _ m m' lo hi HG L2 MU D82)|].
  exact (b6_FSb_keep g _ _ regs regs' m m' lo hi HS E19 MU ltac:(lia) DS).
Qed.


(* ---- machine-level helpers ---- *)
Lemma b6_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b6_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b6_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma b6_q64_ovr : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (b6_ovr m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma b6_norm : forall mem a bs, ro_agree rsegs mem -> bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs.
Proof. intros mem a bs HMI H. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs (mem_rel_normalize rsegs mem HMI)) H). Qed.

Lemma b6_q64_norm : forall mem a v, ro_agree rsegs mem -> q64 mem a v -> q64 (normalize rsegs mem) a v.
Proof. intros mem a v HMI H. unfold q64 in *. exact (b6_norm mem a _ HMI H). Qed.

Lemma b6_tID_S0 : forall inp j, t_rf inp j <> 1 -> t_ID inp (S j) = t_IDr inp j.
Proof.
  intros inp j H. rewrite b6_tID_S. unfold fg_id. unfold t_rf in H.
  replace (fg_rf (t_len inp j) (t_FG inp j) (t_g inp j) =? 1) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma b6_tID_S1 : forall inp j, t_rf inp j = 1 ->
  t_ID inp (S j) = snd (RcIdentModel.ING (t_IDr inp j) (fg_addr (t_FG inp j) (t_g inp j))
                                          (f_pl (t_len inp j) (t_FG inp j) (t_g inp j))).
Proof.
  intros inp j H. rewrite b6_tID_S. unfold fg_id. unfold t_rf in H. rewrite H. reflexivity.
Qed.


Lemma b6_rw_of : forall m lo hi a bs, Frame.stk rsegs m lo hi -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  bytes_at rsegs m a bs -> Step.rw_cells rsegs m a [Cells.CB (length bs) bs].
Proof.
  intros m lo hi a bs ST H1 H2 HB.
  destruct (sl_rw_of_stk m lo hi a (length bs) ST H1 H2) as (bs' & (_ & W)).
  split; [split; [split; [reflexivity | exact I] | cbn [Cells.cells_bytes Cells.cbytes]; rewrite app_nil_r; exact HB]|].
  exact W.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* sl_mid with a fixed write set W whose munch over the unnormalized memory reaches the continuation. *)
Lemma b6_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
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

(* Φ, the frame turn's harness block, lies in the heap below [S - K, S). *)
Lemma b6_phi_rng : forall g phi n L A regs mem md,
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  4096 <= phi /\ phi + n <= g_S g - SLOT_K.
Proof.
  intros g phi n L A regs mem md HFR HP.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  assert (Hin : In (phi, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. left. reflexivity. }
  apply blocks_In in Hin as (p & Ep & Hin).
  destruct (mr_blocks_range B _ (aa_laws (APIf rc)) L A mem md p n HM Hin) as (H1 & H2).
  subst phi. lia.
Qed.

End S.

(* ---- G06: opens_record as the code tests it (first_frag F2's store), its branches, the stored slots ---- *)
Definition b6_opn (so : bool) (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) : bool :=
  so && ((bv_unsigned b16 =? 205) && (bv_unsigned b17 =? 234) && (bv_unsigned b18 =? 4) && (bv_unsigned b19 =? 1) &&
         (bv_unsigned b22 =? 0) && (bv_unsigned b23 =? 2) && (bv_unsigned b24 =? 0) && (bv_unsigned b25 =? 254) &&
         (1 <=? bv_unsigned b26) && (bv_unsigned b26 <=? 22)).

Lemma b6_opn_eq : forall inp j,
  b6_opn (t_sum_ok inp j) (nth 16 (t_g inp j) (Z_to_bv 8 0)) (nth 17 (t_g inp j) (Z_to_bv 8 0))
    (nth 18 (t_g inp j) (Z_to_bv 8 0)) (nth 19 (t_g inp j) (Z_to_bv 8 0)) (nth 22 (t_g inp j) (Z_to_bv 8 0))
    (nth 23 (t_g inp j) (Z_to_bv 8 0)) (nth 24 (t_g inp j) (Z_to_bv 8 0)) (nth 25 (t_g inp j) (Z_to_bv 8 0))
    (nth 26 (t_g inp j) (Z_to_bv 8 0)) = f_opens (t_len inp j) (t_g inp j).
Proof. intros inp j. rewrite b6_opens_eq. reflexivity. Qed.

Lemma b6_eqz : forall (b : byte) k, 0 <= k < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 k) = (bv_unsigned b =? k).
Proof. intros b k Hk. unfold zxb. pose proof (RcLib.byte_range b). apply b6_eqb; lia. Qed.

(* 0x13a50-0x13a58: Φ[26] - 23 <u -22 is Φ[26] outside 1 .. 22. *)
Lemma b6_c26 : forall b : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + -23)) (Z_to_bv 64 (-22)) =
  negb ((1 <=? bv_unsigned b) && (bv_unsigned b <=? 22)).
Proof.
  intros b. pose proof (RcLib.byte_range b) as Hb.
  assert (E : bv_unsigned (zxb b) = bv_unsigned b) by (unfold zxb; rewrite MState.unsigned_lit by lia; reflexivity).
  rewrite E. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.leb_spec 1 (bv_unsigned b)), (Z.leb_spec (bv_unsigned b) 22); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma b6_c8 : forall m A v, Step.rw_cells rsegs m A [Cells.C8 v] -> bytes_at rsegs m A (le8 v).
Proof.
  intros m A v H. pose proof (sl_cells_bytes m A _ H) as X.
  cbn [Cells.cells_bytes Cells.cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma b6_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma b6_ba_byte : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk. rewrite <- (b6_firstn1 bs k (Z_to_bv 8 0) Hk). apply b6_ba_sub; [exact H | lia].
Qed.

(* ---- E01-E03: is_8819 gives p.dst = Φ[0 .. 6) and p.src = Φ[6 .. 12) in B (struct P5.2); memcmp of equal bytes ---- *)
Lemma b6_8819 : forall inp j, t_8819 inp j = true ->
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
  pose proof (b6_g_len inp j) as LG.
  split; [exact Hn|]. unfold t_B.
  split; (apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0);
          [rewrite !length_firstn, !length_skipn, LB, LG; reflexivity|];
          intros i Hi; rewrite length_firstn, length_skipn, LB in Hi;
          rewrite !b6_nth_firstn by lia; rewrite !b6_nth_skipn; change (Z_to_bv 8 0) with RcParse.cp_z).
  - rewrite (HD i ltac:(lia)). reflexivity.
  - rewrite (HS i ltac:(lia)). reflexivity.
Qed.

Lemma b6_mcmp_refl : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|a l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* ---- E03: p.counter = B[20 .. 22) = Φ[14], Φ[15] (struct P5.2); k = 1 exactly when Φ[16] = Φ[17] = 0 (P5.3);
   sum_ok is the block sum of Φ[18 .. 50) on the is_8819 path; the code's 16-bit compare ---- *)
Lemma b6_firstn2 : forall (l : list byte) k d, (S k < length l)%nat ->
  firstn 2 (skipn k l) = [nth k l d; nth (S k) l d].
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k].
  - destruct l as [|y l]; [cbn in H; lia | reflexivity].
  - cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma b6_cnt : forall inp j, t_8819 inp j = true ->
  firstn 2 (skipn 20 (t_B inp j)) = [nth 14 (t_g inp j) (Z_to_bv 8 0); nth 15 (t_g inp j) (Z_to_bv 8 0)].
Proof.
  intros inp j H.
  assert (Hh : RcParse.cp_hdr (t_len inp j) (t_g inp j) = true) by exact H.
  assert (Hk : fst (RcParse.ctrlparse (t_len inp j) (t_g inp j)) <> 0).
  { unfold RcParse.ctrlparse. rewrite Hh. cbn [fst]. pose proof (RcParse.cp_kind_range (t_g inp j)). lia. }
  pose proof (RcParse.ctrlparse_fields _ _ Hk) as X. cbv zeta in X.
  destruct X as (_ & _ & _ & H20 & H21 & _).
  unfold t_B. rewrite (b6_firstn2 _ 20 (Z_to_bv 8 0)) by (rewrite RcParse.ctrlparse_length; lia).
  change (Z_to_bv 8 0) with RcParse.cp_z. rewrite H20, H21. reflexivity.
Qed.

Lemma b6_filler : forall inp j, t_8819 inp j = true ->
  (t_k inp j = 1 <-> bv_unsigned (nth 16 (t_g inp j) (Z_to_bv 8 0)) = 0 /\
                     bv_unsigned (nth 17 (t_g inp j) (Z_to_bv 8 0)) = 0).
Proof.
  intros inp j H. unfold t_k. rewrite RcParse.ctrlparse_filler.
  assert (Hh : RcParse.cp_hdr (t_len inp j) (t_g inp j) = true) by exact H.
  rewrite Hh. unfold RcParse.cp_v, RcParse.cp_b, RcParse.cp_z. tauto.
Qed.

Lemma b6_sum8819 : forall inp j, t_8819 inp j = true ->
  t_sum_ok inp j = (blocksum (firstn 32 (skipn 18 (t_g inp j))) =? 0).
Proof.
  intros inp j H. unfold t_sum_ok.
  assert (Hb : t_big inp j = true).
  { unfold t_8819 in H. apply andb_prop in H as (H & _). apply andb_prop in H as (H & _). exact H. }
  rewrite Hb. cbn [andb]. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn, b6_g_len. lia.
Qed.

Lemma b6_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
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

(* 0x13ab8-0x13abc: (hi << 8) | lo. *)
Lemma b6_orshl : forall hi lo : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo)) =
  256 * bv_unsigned hi + bv_unsigned lo.
Proof.
  intros hi lo. pose proof (RcLib.byte_range hi). pose proof (RcLib.byte_range lo).
  assert (Eh : bv_unsigned (zxb hi) = bv_unsigned hi) by (unfold zxb; apply MState.unsigned_lit; lia).
  assert (El : bv_unsigned (zxb lo) = bv_unsigned lo) by (unfold zxb; apply MState.unsigned_lit; lia).
  rewrite Eh, El.
  rewrite (MState.unsigned_lit (Z.shiftl (bv_unsigned hi) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite b6_lor_shl8 by lia. lia.
Qed.

Lemma b6_le2 : forall hi lo : byte, le2 (Z_to_bv 64 (256 * bv_unsigned hi + bv_unsigned lo)) = [lo; hi].
Proof.
  intros hi lo. pose proof (RcLib.byte_range hi). pose proof (RcLib.byte_range lo).
  unfold le2. rewrite MState.unsigned_lit by lia. cbn [Z_to_le_bytes]. f_equal; [|f_equal].
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    Z.div_mod_to_equations. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma b6_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* 0x13ad8 and 0x13adc-0x13ae0: seqz of a loaded byte, and seqz (k - 1). *)
Lemma b6_sltb : forall b : byte, PropExec.v_sltiu (zxb b) 1 = Z_to_bv 64 (b2z (bv_unsigned b =? 0)).
Proof.
  intros b. pose proof (RcLib.byte_range b). unfold PropExec.v_sltiu, zxb. rewrite MState.unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  destruct (Z.ltb_spec (bv_unsigned b) 1); destruct (Z.eqb_spec (bv_unsigned b) 0); cbn [b2z];
    first [reflexivity | exfalso; lia].
Qed.

Lemma b6_sltk : forall k, 0 <= k <= 13 -> PropExec.v_sltiu (Z_to_bv 64 (k + -1)) 1 = Z_to_bv 64 (b2z (k =? 1)).
Proof.
  intros k Hk. unfold PropExec.v_sltiu. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.ltb_spec ((k + -1) mod 18446744073709551616) 1);
    destruct (Z.eqb_spec k 1); cbn [b2z];
    first [reflexivity | exfalso; Z.div_mod_to_equations; lia].
Qed.
