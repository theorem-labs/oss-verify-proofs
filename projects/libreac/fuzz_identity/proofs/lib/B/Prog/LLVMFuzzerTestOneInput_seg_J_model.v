(* The plain-model lemmas of segment J of LLVMFuzzerTestOneInput's build-B walk: the shape, the length and
   the bytes of the expected box name `n_EXP_NM` and display `n_EXP_DP` that the segment builds in the entry's
   frame, and the meaning of `n_r` (SlotModel). Nothing here speaks of the program or of addresses. *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
Import ListNotations.
Open Scope Z_scope.


(* Pure model facts about the expected box name n_EXP_NM (segment J, build B). *)

Definition m1_nzb (l : list byte) : bool := forallb (fun b => negb (bz b =? 0)) l.

Lemma m1_nzb_spec : forall l, m1_nzb l = true -> forall b, In b l -> bz b <> 0.
Proof.
  intros l H b Hb. unfold m1_nzb in H. rewrite forallb_forall in H.
  specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma m1_nonul_of : forall l, (forall b, In b l -> bz b <> 0) -> ~ In (zb 0) l.
Proof. intros l H Hin. apply (H _ Hin). vm_compute. reflexivity. Qed.

Lemma m1_first_zero_nz : forall l b, In b (firstn (first_zero l) l) -> bz b <> 0.
Proof.
  induction l as [|x l IH]; intros b; cbn [first_zero].
  - cbn [firstn In]. intros [].
  - destruct (Z.eqb_spec (bz x) 0) as [E|E]; cbn [firstn In]; [intros []|].
    intros [<-|H]; [exact E|exact (IH b H)].
Qed.

Lemma m1_stem_nz : forall inp b, In b (n_stem inp) -> bz b <> 0.
Proof.
  intro inp. unfold n_stem. destruct (n_use_said inp).
  - unfold name_str. apply m1_first_zero_nz.
  - apply m1_nzb_spec. unfold stem_img.
    destruct (n_fam inp =? 1); [vm_compute; reflexivity|].
    destruct (n_fam inp =? 2); [vm_compute; reflexivity|].
    destruct (n_fam inp =? 3); vm_compute; reflexivity.
Qed.

Lemma m1_stem_nonul : forall inp, ~ In (zb 0) (n_stem inp).
Proof. intro inp. apply m1_nonul_of. apply m1_stem_nz. Qed.

Lemma m1_stem_len : forall inp, (length (n_stem inp) <= 16)%nat.
Proof. exact n_stem_len. Qed.

Lemma m1_W4_len : forall inp, n_wok inp = true -> length (n_W4 inp) = 4%nat.
Proof.
  intros inp Hw. destruct (wok_chans inp Hw) as [Hi Ho].
  unfold n_W4. rewrite length_app, (DEC2_len _ Hi), (DEC2_len _ Ho). reflexivity.
Qed.

Lemma m1_DEC2_nz : forall x, 0 <= x <= 40 -> m1_nzb (DEC x 2) = true.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => m1_nzb (DEC x 2)) (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x
    ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  exact H.
Qed.

Lemma m1_W4_nz : forall inp, n_wok inp = true -> forall b, In b (n_W4 inp) -> bz b <> 0.
Proof.
  intros inp Hw b Hb. destruct (wok_chans inp Hw) as [Hi Ho].
  unfold n_W4 in Hb. apply in_app_or in Hb as [Hb|Hb].
  - exact (m1_nzb_spec _ (m1_DEC2_nz _ Hi) b Hb).
  - exact (m1_nzb_spec _ (m1_DEC2_nz _ Ho) b Hb).
Qed.

Lemma m1_W4_nonul : forall inp, n_wok inp = true -> ~ In (zb 0) (n_W4 inp).
Proof. intros inp Hw. apply m1_nonul_of. exact (m1_W4_nz inp Hw). Qed.

Lemma m1_ends_w4_cases : forall inp,
  (n_ends_w4 inp = true /\ n_EXP_NM inp = n_stem inp) \/
  (n_ends_w4 inp = false /\ n_EXP_NM inp = n_stem inp ++ [dash] ++ n_W4 inp).
Proof.
  intro inp. unfold n_EXP_NM. destruct (n_ends_w4 inp); [left|right]; split; reflexivity.
Qed.

Lemma m1_ends_w4_short : forall inp, (length (n_stem inp) < 4)%nat -> n_ends_w4 inp = false.
Proof.
  intros inp H. unfold n_ends_w4.
  destruct (Nat.leb_spec 4 (length (n_stem inp))) as [E|E]; [clear - H E; lia|reflexivity].
Qed.

Lemma m1_ends_w4_long : forall inp, n_wok inp = true -> (4 <= length (n_stem inp))%nat ->
  n_ends_w4 inp = bytes_eqb (skipn (length (n_stem inp) - 4) (n_stem inp)) (n_W4 inp).
Proof.
  intros inp Hw H4.
  assert (E : firstn 4 (n_W4 inp) = n_W4 inp)
    by (apply firstn_all2; rewrite (m1_W4_len inp Hw); lia).
  unfold n_ends_w4. rewrite E, (proj2 (Nat.leb_le _ _) H4). reflexivity.
Qed.

Lemma m1_dash_nz : bz dash <> 0.
Proof. intro E. vm_compute in E. discriminate E. Qed.

Lemma m1_EXP_NM_nonul : forall inp, n_wok inp = true -> ~ In (zb 0) (n_EXP_NM inp).
Proof.
  intros inp Hw. apply m1_nonul_of. unfold n_EXP_NM. destruct (n_ends_w4 inp); intros b Hb.
  - exact (m1_stem_nz inp b Hb).
  - apply in_app_or in Hb as [Hb|Hb]; [exact (m1_stem_nz inp b Hb)|].
    apply in_app_or in Hb as [Hb|Hb]; [|exact (m1_W4_nz inp Hw b Hb)].
    destruct Hb as [<-|[]]. exact m1_dash_nz.
Qed.

Lemma m1_n_ln_ends : forall inp, n_wok inp = true -> n_ends_w4 inp = true ->
  n_ln inp = Z.of_nat (length (n_stem inp)).
Proof. intros inp _ H. unfold n_ln, n_EXP_NM. rewrite H. reflexivity. Qed.

Lemma m1_n_ln_dash : forall inp, n_wok inp = true -> n_ends_w4 inp = false ->
  n_ln inp = Z.of_nat (length (n_stem inp)) + 5.
Proof.
  intros inp Hw H. unfold n_ln, n_EXP_NM. rewrite H, !length_app, (m1_W4_len inp Hw).
  cbn [length]. lia.
Qed.

Lemma m1_n_ln_le : forall inp, n_wok inp = true -> 1 <= n_ln inp <= 21.
Proof. exact n_ln_le. Qed.

Lemma m1_dash_find_l : forall l : list byte, exists k,
  0 <= k <= Z.of_nat (length l) /\
  (forall i, 0 <= i < k -> bz (nth (Z.to_nat i) l (zb 0)) <> 45) /\
  (k < Z.of_nat (length l) -> bz (nth (Z.to_nat k) l (zb 0)) = 45) /\
  ((k <? Z.of_nat (length l)) = has_dash l).
Proof.
  induction l as [|x l IH].
  - exists 0. cbn [length]. split; [lia|]. split; [intros i Hi; lia|].
    split; [intro H; lia|]. reflexivity.
  - unfold has_dash in *. cbn [existsb length].
    destruct (Z.eqb_spec (bz x) 45) as [E|E].
    + exists 0. split; [lia|]. split; [intros i Hi; lia|].
      split; [intros _; exact E|]. cbn [orb]. apply Z.ltb_lt. lia.
    + destruct IH as (k & Hk & Hpre & Hat & Hd). exists (k + 1).
      split; [clear - Hk; lia|]. split; [|split].
      * intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [exact E|].
        replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by (clear - Hi Hne; lia).
        cbn [nth]. apply Hpre. clear - Hi Hne; lia.
      * intro H. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by (clear - Hk; lia).
        cbn [nth]. apply Hat. clear - H; lia.
      * cbn [orb]. rewrite <- Hd.
        destruct (Z.ltb_spec (k + 1) (Z.of_nat (S (length l)))) as [L1|L1];
          destruct (Z.ltb_spec k (Z.of_nat (length l))) as [L2|L2];
          try reflexivity; clear - L1 L2; lia.
Qed.

Lemma m1_dash_find : forall inp, exists k,
  0 <= k <= n_ln inp /\
  (forall i, 0 <= i < k -> bz (nth (Z.to_nat i) (n_EXP_NM inp) (zb 0)) <> 45) /\
  (k < n_ln inp -> bz (nth (Z.to_nat k) (n_EXP_NM inp) (zb 0)) = 45) /\
  ((k <? n_ln inp) = has_dash (n_EXP_NM inp)).
Proof. intro inp. unfold n_ln. exact (m1_dash_find_l (n_EXP_NM inp)). Qed.

Lemma m1_n_lt : forall inp, n_lt inp = n_ln inp - (if has_dash (n_EXP_NM inp) then 1 else 0).
Proof. intro inp. reflexivity. Qed.



(* Pure model facts about the expected display string n_EXP_DP (segment J, build B):
   the pieces the walk writes into the display buffer, their running lengths, and the
   facts the J cut needs about them (no NUL byte, digit counts, caps, the n_r cases). *)

Definition m2_d1 (inp : list byte) : Z := Z.of_nat (length (DEC (t_in inp) 1)).
Definition m2_d2 (inp : list byte) : Z := Z.of_nat (length (DEC (t_out inp) 1)).
Definition m2_L1 (inp : list byte) : Z := n_ln inp.
Definition m2_L2 (inp : list byte) : Z := m2_L1 inp + 2 + m2_d1 inp.
Definition m2_L3 (inp : list byte) : Z := m2_L2 inp + 6 + m2_d2 inp.
Definition m2_dp1 (inp : list byte) : list byte := n_EXP_NM inp.
Definition m2_dp2 (inp : list byte) : list byte := m2_dp1 inp ++ str_bytes " ("%string ++ DEC (t_in inp) 1.
Definition m2_dp3 (inp : list byte) : list byte := m2_dp2 inp ++ str_bytes " in / "%string ++ DEC (t_out inp) 1.

(* --- the display string and its running lengths --- *)

Lemma m2_dp_full : forall inp, m2_dp3 inp ++ str_bytes " out)"%string = n_EXP_DP inp.
Proof.
  intro inp. unfold m2_dp3, m2_dp2, m2_dp1, n_EXP_DP. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma m2_len1 : forall inp, Z.of_nat (length (m2_dp1 inp)) = m2_L1 inp.
Proof. intro inp. unfold m2_dp1, m2_L1, n_ln. reflexivity. Qed.

Lemma m2_len2 : forall inp, Z.of_nat (length (m2_dp2 inp)) = m2_L2 inp.
Proof.
  intro inp. unfold m2_dp2, m2_dp1, m2_L2, m2_L1, m2_d1, n_ln. rewrite !length_app.
  change (length (str_bytes " ("%string)) with 2%nat. lia.
Qed.

Lemma m2_len3 : forall inp, Z.of_nat (length (m2_dp3 inp)) = m2_L3 inp.
Proof.
  intro inp. pose proof (m2_len2 inp) as H2. unfold m2_dp3, m2_L3, m2_d2. rewrite !length_app.
  change (length (str_bytes " in / "%string)) with 6%nat. clear - H2. lia.
Qed.

Lemma m2_len_dp : forall inp, Z.of_nat (length (n_EXP_DP inp)) = m2_L3 inp + 5.
Proof.
  intro inp. pose proof (m2_len3 inp) as H3.
  rewrite <- (m2_dp_full inp), length_app.
  change (length (str_bytes " out)"%string)) with 5%nat. clear - H3. lia.
Qed.

Lemma m2_d_range : forall inp, n_wok inp = true -> 1 <= m2_d1 inp <= 2 /\ 1 <= m2_d2 inp <= 2.
Proof.
  intros inp Hw. destruct (wok_chans inp Hw) as [Hi Ho].
  pose proof (DEC1_len _ Hi) as D1. pose proof (DEC1_len _ Ho) as D2.
  unfold m2_d1, m2_d2. clear - D1 D2. lia.
Qed.

Lemma m2_n_ld_le : forall inp, n_wok inp = true -> 1 <= n_ld inp <= 38.
Proof.
  intros inp Hw. pose proof (n_ld_le inp Hw) as HU. pose proof (n_ln_le inp Hw) as HL.
  destruct (m2_d_range inp Hw) as [Hd1 Hd2]. pose proof (m2_len_dp inp) as HE.
  unfold n_ld in *. unfold m2_L3, m2_L2, m2_L1 in HE. clear - HU HL Hd1 Hd2 HE. lia.
Qed.

(* --- no NUL byte anywhere in the display string --- *)

Definition m2_NZ (l : list byte) : Prop := forall b, In b l -> bz b <> 0.

Lemma m2_NZ_app : forall l1 l2, m2_NZ l1 -> m2_NZ l2 -> m2_NZ (l1 ++ l2).
Proof. intros l1 l2 H1 H2 b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (H1 b Hb) | exact (H2 b Hb)]. Qed.

Lemma m2_NZ_b : forall l, forallb (fun b => negb (bz b =? 0)) l = true -> m2_NZ l.
Proof.
  intros l H b Hb. rewrite forallb_forall in H. specialize (H b Hb).
  apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma m2_NZ_notin : forall l, m2_NZ l -> ~ In (zb 0) l.
Proof. intros l H Hin. apply (H _ Hin). vm_compute. reflexivity. Qed.

Lemma m2_NZ_dg : forall y, m2_NZ [dg (y mod 10)].
Proof.
  intros y b [<-|[]]. unfold dg, bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. pose proof (Z.mod_pos_bound y 10 ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma m2_NZ_dec_digits : forall n x, m2_NZ (dec_digits n x).
Proof.
  induction n as [|n IH]; intros x; cbn [dec_digits]; [intros b []|].
  apply m2_NZ_app; [|apply m2_NZ_dg]. destruct (x <? 10); [intros b []| apply IH].
Qed.

Lemma m2_NZ_repeat0 : forall k, m2_NZ (repeat (dg 0) k).
Proof.
  intros k b Hb. apply repeat_spec in Hb. subst b.
  exact (m2_NZ_dg 0 (dg (0 mod 10)) (or_introl eq_refl)).
Qed.

Lemma m2_NZ_DEC : forall x m, m2_NZ (DEC x m).
Proof. intros x m. unfold DEC. apply m2_NZ_app; [apply m2_NZ_repeat0 | apply m2_NZ_dec_digits]. Qed.

Lemma m2_DEC_nonul : forall v m, 0 <= v -> ~ In (zb 0) (DEC v m).
Proof. intros v m _. apply m2_NZ_notin, m2_NZ_DEC. Qed.

Lemma m2_NZ_firstn_fz : forall l, m2_NZ (firstn (first_zero l) l).
Proof.
  induction l as [|x l IH]; cbn [first_zero]; [intros b Hb; destruct Hb|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [intros b []|].
  cbn [firstn]. intros b [<-|Hb]; [exact E | exact (IH b Hb)].
Qed.

Lemma m2_NZ_stem_img : forall f, m2_NZ (stem_img f).
Proof.
  intro f. apply m2_NZ_b. unfold stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma m2_NZ_stem : forall inp, m2_NZ (n_stem inp).
Proof.
  intro inp. unfold n_stem. destruct (n_use_said inp);
    [unfold name_str; apply m2_NZ_firstn_fz | apply m2_NZ_stem_img].
Qed.

Lemma m2_NZ_EXP_NM : forall inp, m2_NZ (n_EXP_NM inp).
Proof.
  intro inp. pose proof (m2_NZ_stem inp) as HS. unfold n_EXP_NM.
  destruct (n_ends_w4 inp); [exact HS|].
  apply m2_NZ_app; [exact HS|]. apply m2_NZ_app; [apply m2_NZ_b; vm_compute; reflexivity|].
  unfold n_W4. apply m2_NZ_app; apply m2_NZ_DEC.
Qed.

Lemma m2_NZ_EXP_DP : forall inp, m2_NZ (n_EXP_DP inp).
Proof.
  intro inp. unfold n_EXP_DP.
  apply m2_NZ_app; [apply m2_NZ_EXP_NM|].
  apply m2_NZ_app; [apply m2_NZ_b; vm_compute; reflexivity|].
  apply m2_NZ_app; [apply m2_NZ_DEC|].
  apply m2_NZ_app; [apply m2_NZ_b; vm_compute; reflexivity|].
  apply m2_NZ_app; [apply m2_NZ_DEC|]. apply m2_NZ_b; vm_compute; reflexivity.
Qed.

Lemma m2_EXP_DP_nonul : forall inp, n_wok inp = true -> ~ In (zb 0) (n_EXP_DP inp).
Proof. intros inp _. apply m2_NZ_notin, m2_NZ_EXP_DP. Qed.

(* --- the three literals the walk copies --- *)

Lemma m2_lit_paren : map bz (str_bytes " ("%string) = [32; 40].
Proof. vm_compute. reflexivity. Qed.

Lemma m2_lit_in : map bz (str_bytes " in / "%string) = [32; 105; 110; 32; 47; 32].
Proof. vm_compute. reflexivity. Qed.

Lemma m2_lit_out : map bz (str_bytes " out)"%string) = [32; 111; 117; 116; 41].
Proof. vm_compute. reflexivity. Qed.

(* --- the return value and the capacity checks --- *)

Lemma m2_fits_r0 : forall inp, n_r inp = 0 ->
  n_wok inp = true /\ n_ln inp < t_cap_name inp /\ n_lt inp < t_cap_tok inp /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_r in H.
  destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate H].
  apply andb_true_iff in E as [Ew Ef]. unfold n_fits in Ef.
  apply andb_true_iff in Ef as [Ef Ed]. apply andb_true_iff in Ef as [En Et].
  apply Z.ltb_lt in En. apply Z.ltb_lt in Et. apply Z.ltb_lt in Ed.
  split; [exact Ew|]. split; [exact En|]. split; [exact Et|]. exact Ed.
Qed.

Lemma m2_fits_rm1 : forall inp, n_wok inp = true -> n_r inp = -1 ->
  n_ln inp >= t_cap_name inp \/ n_lt inp >= t_cap_tok inp \/ n_ld inp >= t_cap_disp inp.
Proof.
  intros inp Hw H. unfold n_r in H. rewrite Hw in H. cbn [andb] in H.
  destruct (n_fits inp) eqn:Ef; [discriminate H|]. unfold n_fits in Ef.
  apply andb_false_iff in Ef as [Ef|Ed].
  - apply andb_false_iff in Ef as [En|Et].
    + left. apply Z.ltb_ge in En. lia.
    + right; left. apply Z.ltb_ge in Et. lia.
  - right; right. apply Z.ltb_ge in Ed. lia.
Qed.

Lemma m2_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intro inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left|right]; reflexivity. Qed.

Lemma m2_caps : forall inp, 0 <= t_cap_name inp < 40 /\ 0 <= t_cap_tok inp < 40 /\ 0 <= t_cap_disp inp < 64.
Proof.
  intro inp. unfold t_cap_name, t_cap_tok, t_cap_disp.
  pose proof (Z.mod_pos_bound (tb inp 5) 40 ltac:(lia)) as H5.
  pose proof (Z.mod_pos_bound (tb inp 6) 40 ltac:(lia)) as H6.
  pose proof (Z.mod_pos_bound (tb inp 7) 64 ltac:(lia)) as H7.
  clear - H5 H6 H7. lia.
Qed.

(* The width decision of segment J, in the four shapes its branches leave. *)
Lemma m2_okw_bounds : forall inp, 0 <= t_in inp < 256 /\ 0 <= t_out inp < 256.
Proof. intro inp. split; apply inb_range. Qed.
Lemma m2_okw_false : forall v, (v = 1 \/ 40 < v \/ (2 <= v <= 40 /\ Z.even v = false)) -> okw v = false.
Proof.
intros v [-> | [H | [H He]]]; unfold okw.
- reflexivity.
- assert (E0 : (v =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (E40 : (v <=? 40) = false) by (apply Z.leb_gt; lia).
  rewrite E0, E40. destruct (2 <=? v); destruct (Z.even v); reflexivity.
- assert (E0 : (v =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite E0, He. destruct (2 <=? v); destruct (v <=? 40); reflexivity.
Qed.
Lemma m2_okw_true : forall v, (v = 0 \/ (2 <= v <= 40 /\ Z.even v = true)) -> okw v = true.
Proof.
intros v [-> | [H He]]; unfold okw; [reflexivity|].
assert (A2 : (2 <=? v) = true) by (apply Z.leb_le; lia).
assert (A40 : (v <=? 40) = true) by (apply Z.leb_le; lia).
rewrite A2, A40, He. destruct (v =? 0); reflexivity.
Qed.
Lemma m2_wok_false_in : forall inp,
(t_in inp = 1 \/ 40 < t_in inp \/ (2 <= t_in inp <= 40 /\ Z.even (t_in inp) = false)) -> n_wok inp = false.
Proof.
intros inp H. unfold n_wok. rewrite (m2_okw_false _ H).
destruct (okw (t_out inp)); destruct (negb ((t_in inp =? 0) && (t_out inp =? 0))); reflexivity.
Qed.
Lemma m2_wok_false_out : forall inp,
(t_out inp = 1 \/ 40 < t_out inp \/ (2 <= t_out inp <= 40 /\ Z.even (t_out inp) = false)) -> n_wok inp = false.
Proof.
intros inp H. unfold n_wok. rewrite (m2_okw_false _ H).
destruct (okw (t_in inp)); destruct (negb ((t_in inp =? 0) && (t_out inp =? 0))); reflexivity.
Qed.
Lemma m2_wok_both0 : forall inp, t_in inp = 0 -> t_out inp = 0 -> n_wok inp = false.
Proof. intros inp H1 H2. unfold n_wok. rewrite H1, H2. reflexivity. Qed.
Lemma m2_wok_true : forall inp,
(t_in inp = 0 \/ (2 <= t_in inp <= 40 /\ Z.even (t_in inp) = true)) ->
(t_out inp = 0 \/ (2 <= t_out inp <= 40 /\ Z.even (t_out inp) = true)) ->
(t_in inp <> 0 \/ t_out inp <> 0) -> n_wok inp = true.
Proof.
intros inp Hi Ho Hne. unfold n_wok. rewrite (m2_okw_true _ Hi), (m2_okw_true _ Ho).
assert (Hf : ((t_in inp =? 0) && (t_out inp =? 0)) = false).
{ destruct Hne as [H | H].
  - assert (E : (t_in inp =? 0) = false) by (apply Z.eqb_neq; exact H). rewrite E. reflexivity.
  - assert (E : (t_out inp =? 0) = false) by (apply Z.eqb_neq; exact H).
    rewrite E, Bool.andb_false_r. reflexivity. }
rewrite Hf. reflexivity.
Qed.
