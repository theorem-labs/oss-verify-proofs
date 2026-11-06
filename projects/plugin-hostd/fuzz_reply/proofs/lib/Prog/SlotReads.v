From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept
  send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c
  gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c
  relay_remove_b_c SlotInv.
Import ListNotations.
Local Open Scope Z_scope.

Definition zrange (l : list Z) : Prop := Forall (fun z => 0 <= z < 256) l.

Definition rtexts (rs : list (Z * list byte)) : list (list Z) := map (fun r => bzs (snd r)) rs.

Definition wcost (st : lstate) : Z := if ls_k st then 0 else Z.of_nat (length (ls_w st)).

Lemma bz_range : forall b : byte, 0 <= bz b < 256.
Proof. intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma bz_inj : forall a b : byte, bz a = bz b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma bz_lit : forall z, 0 <= z < 256 -> bz (Z_to_bv 8 z) = z.
Proof. intros z Hz. unfold bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma bzs_inj : forall a b, bzs a = bzs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bz_inj; exact H1 | apply IH; exact H2].
Qed.

Lemma bzs_app : forall a b, bzs (a ++ b) = bzs a ++ bzs b.
Proof. intros a b. unfold bzs. apply map_app. Qed.

Lemma bzs_length : forall a, length (bzs a) = length a.
Proof. intros a. unfold bzs. apply length_map. Qed.

Lemma bzs_lits : forall l, zrange l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|z l IH]; intros H; [reflexivity|]. inversion H as [|? ? H1 H2]; subst.
  cbn [map]. unfold bzs. cbn [map]. fold (bzs (map (Z_to_bv 8) l)). rewrite bz_lit by exact H1. f_equal. apply IH. exact H2.
Qed.

Lemma zrange_bzs : forall l, zrange (bzs l).
Proof. intros l. unfold zrange, bzs. apply Forall_map. apply Forall_forall. intros b _. apply bz_range. Qed.

Lemma bzs_zero : bzs [Z_to_bv 8 0] = [0].
Proof. unfold bzs. cbn [map]. rewrite bz_lit by lia. reflexivity. Qed.

Lemma step_range : forall st b, zrange (ls_w st) -> 0 <= b < 256 ->
  zrange (ls_w (fst (step st b))) /\ (forall l, snd (step st b) = Some l -> zrange l).
Proof.
  intros [w k] b Hw Hb. unfold step; cbn [ls_w ls_k] in *.
  destruct (Z.eqb b 0).
  { cbn [fst snd ls_w]. split; [constructor|]. intros l E. destruct k; [discriminate|]. injection E as <-. exact Hw. }
  destruct k; [cbn [fst snd ls_w]; split; [exact Hw | discriminate]|].
  destruct (Nat.eqb (length w) LINE_LIMIT); cbn [fst snd ls_w]; [split; [exact Hw | discriminate]|].
  split; [|discriminate]. apply Forall_app. split; [exact Hw | constructor; [exact Hb | constructor]].
Qed.

Lemma lines_range : forall d st, zrange (ls_w st) -> zrange d ->
  Forall zrange (lines st d) /\ zrange (ls_w (feed st d)).
Proof.
  induction d as [|b d IH]; intros st Hw Hd.
  { rewrite lines_nil, feed_nil. split; [constructor | exact Hw]. }
  inversion Hd as [|? ? Hb Hd']; subst.
  destruct (step_range st b Hw Hb) as [H1 H2].
  rewrite lines_cons, feed_cons.
  destruct (IH (fst (step st b)) H1 Hd') as [IH1 IH2].
  split; [|exact IH2].
  destruct (snd (step st b)) as [l|] eqn:E; [constructor; [exact (H2 l eq_refl) | exact IH1] | exact IH1].
Qed.

Lemma lines_bytes : forall d st,
  Z.of_nat (length (with_nul (lines st d))) + wcost (feed st d) <= wcost st + Z.of_nat (length d).
Proof.
  induction d as [|b d IH]; intros st.
  { rewrite lines_nil, feed_nil. cbn [with_nul map concat length]. lia. }
  rewrite lines_cons, feed_cons. specialize (IH (fst (step st b))).
  assert (S1 : (match snd (step st b) with Some l => Z.of_nat (length l) + 1 | None => 0 end) +
               wcost (fst (step st b)) <= wcost st + 1).
  { destruct st as [w k]. unfold step, wcost; cbn [ls_w ls_k].
    destruct (Z.eqb b 0); [destruct k; cbn [fst snd ls_w ls_k length]; lia|].
    destruct k; [cbn [fst snd ls_w ls_k]; lia|].
    destruct (Nat.eqb (length w) LINE_LIMIT); cbn [fst snd ls_w ls_k]; [lia|]. rewrite length_app. cbn [length]. lia. }
  cbn [length]. destruct (snd (step st b)) as [l|].
  - unfold with_nul in *. cbn [map concat]. rewrite !length_app. cbn [length]. lia.
  - lia.
Qed.

Lemma last_space_lt : forall l i j, last_space_from i l = Some j -> (j < i + length l)%nat.
Proof.
  induction l as [|b l IH]; intros i j H; cbn [last_space_from] in H; [discriminate|].
  destruct (last_space_from (S i) l) eqn:E.
  - injection H as <-. specialize (IH _ _ E). cbn [length]. lia.
  - destruct (Z.eqb b SPACE); [injection H as <-; cbn [length]; lia | discriminate].
Qed.

Lemma gesture_begin_len : forall l x, gesture l = Some (GBegin, x) -> (20 <= length l)%nat.
Proof.
  intros l x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|] eqn:E; [|discriminate].
  destruct (Nat.ltb 13 j) eqn:J; [|discriminate]. apply Nat.ltb_lt in J.
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:W.
  - unfold list_eqb in W. destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Ew|]; [|discriminate].
    pose proof (f_equal (@length Z) Ew) as Lw. rewrite length_skipn in Lw. cbn in Lw.
    pose proof (last_space_lt l 0 j E). lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

Lemma count_begin_cons : forall l Ls, count_begin (l :: Ls) = (if is_begin l then S (count_begin Ls) else count_begin Ls).
Proof. intros l Ls. unfold count_begin. cbn. destruct (is_begin l); reflexivity. Qed.

Lemma want_of_cons : forall P r rs, want_of P (r :: rs) = (if prefixb P (snd r) then S (want_of P rs) else want_of P rs).
Proof. intros P r rs. unfold want_of. cbn. destruct (prefixb P (snd r)); reflexivity. Qed.

Lemma count_begin_bytes : forall Ls, (21 * count_begin Ls <= length (with_nul Ls))%nat.
Proof.
  induction Ls as [|l Ls IH]; [cbn; lia|].
  rewrite count_begin_cons. unfold with_nul in *. cbn [map concat]. rewrite length_app, length_app. cbn [length].
  destruct (is_begin l) eqn:B; [|lia].
  unfold is_begin in B. destruct (gesture l) as [[[|] x]|] eqn:G; try discriminate.
  pose proof (gesture_begin_len l x G). lia.
Qed.

Lemma lines_count : forall Ls, (length Ls <= length (with_nul Ls))%nat.
Proof.
  induction Ls as [|l Ls IH]; [cbn; lia|]. unfold with_nul in *. cbn [map concat]. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma keys_total_nonneg : forall ks, 0 <= keys_total ks.
Proof. unfold keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.

Lemma keys_total_count : forall ks, Forall (fun k => 14 <= Z.of_nat (length (key_text k))) ks ->
  19 * Z.of_nat (length ks) <= keys_total ks.
Proof.
  unfold keys_total. induction ks as [|k ks IH]; intros H; cbn [fold_right length]; [lia|].
  inversion H as [|? ? H1 H2]; subst. specialize (IH H2). lia.
Qed.

Lemma keys_out_length : forall ks, Z.of_nat (length (keys_out ks)) = keys_total ks.
Proof.
  unfold keys_out, keys_total. induction ks as [|k ks IH]; cbn [map concat fold_right]; [reflexivity|].
  rewrite !length_app. change (length END5) with 5%nat. lia.
Qed.

Lemma same_set_length : forall (A B : list (list Z)), NoDup A -> NoDup B -> same_set A B -> length A = length B.
Proof.
  intros A B NA NB S. apply NoDup_ListNoDup in NA, NB.
  apply Nat.le_antisymm; apply NoDup_incl_length; try assumption; intros y Hy; apply S; assumption.
Qed.

Lemma same_set_trans : forall A B C, same_set A B -> same_set B C -> same_set A C.
Proof. intros A B C H1 H2 y. rewrite (H1 y). apply H2. Qed.

Lemma same_set_sym : forall A B, same_set A B -> same_set B A.
Proof. intros A B H y. symmetry. apply H. Qed.

Lemma upd_same_set : forall A B l, same_set A B -> same_set (upd A l) (upd B l).
Proof.
  intros A B l S y. unfold upd. destruct (gesture l) as [[[|] x]|].
  - rewrite !upd_in_begin. rewrite (S y). tauto.
  - rewrite !upd_in_end. rewrite (S y). tauto.
  - apply S.
Qed.

Lemma upds_same_set : forall Ls A B, same_set A B -> same_set (upds A Ls) (upds B Ls).
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros A B S; cbn [fold_left]; [exact S|]. apply IH, upd_same_set, S.
Qed.

Lemma bstream_bzs : forall E Ls, map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  bzs (bstream E) = with_nul Ls.
Proof.
  intros E. unfold bstream. generalize (hl_recs E) as rs. clear E.
  induction rs as [|r rs IH]; intros [|l Ls] Em R; cbn [map] in Em; try discriminate; [reflexivity|].
  injection Em as E1 E2. inversion R as [|? ? R1 R2]; subst.
  cbn [map concat]. unfold with_nul. cbn [map concat]. fold (with_nul Ls).
  rewrite !bzs_app, E1, bzs_lits by exact R1. rewrite bzs_zero, (IH Ls E2 R2). reflexivity.
Qed.

Lemma texts_lines : forall E Ls, map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls -> texts E = Ls.
Proof.
  intros E. unfold texts. generalize (hl_recs E) as rs. clear E.
  induction rs as [|r rs IH]; intros [|l Ls] Em R; cbn [map] in *; try discriminate; [reflexivity|].
  injection Em as E1 E2. inversion R as [|? ? R1 R2]; subst. rewrite E1, bzs_lits by exact R1. f_equal. apply IH; assumption.
Qed.

Lemma split_nul_app : forall l d, ~ In (Z_to_bv 8 0) l -> split_nul (l ++ Z_to_bv 8 0 :: d) = Some (l, d).
Proof.
  induction l as [|b l IH]; intros d H.
  - cbn [app split_nul]. change (bv_unsigned (Z_to_bv 8 0)) with (bz (Z_to_bv 8 0)). rewrite bz_lit by lia. reflexivity.
  - cbn [app split_nul].
    assert (Hb : bv_unsigned b <> 0).
    { intro E. apply H. left. apply bz_inj. unfold bz at 1. rewrite E, bz_lit by lia. reflexivity. }
    rewrite (proj2 (Z.eqb_neq _ _) Hb). rewrite IH by (intro X; apply H; right; exact X). reflexivity.
Qed.

Lemma prefixb_nil : forall x, prefixb [] x = true.
Proof. intros x. reflexivity. Qed.

Lemma want_of_nil : forall rs, want_of [] rs = length rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. rewrite want_of_cons, prefixb_nil, IH. reflexivity.
Qed.

Lemma split_at : forall {X} (l : list X) i d, (i < length l)%nat -> l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros X l. induction l as [|a l IH]; intros [|i] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn skipn nth app]. f_equal. apply IH. lia.
Qed.

Lemma in_drop_split : forall {X} (l : list X) i d y, NoDup l -> (i < length l)%nat ->
  (In y (firstn i l ++ skipn (S i) l) <-> In y l /\ y <> nth i l d).
Proof.
  intros X l i d y ND Hi. apply NoDup_ListNoDup in ND. pose proof (split_at l i d Hi) as E.
  revert ND E. generalize (firstn i l) as A. generalize (skipn (S i) l) as B. generalize (nth i l d) as z.
  intros z B A ND E. rewrite E in ND. apply NoDup_remove in ND. destruct ND as [_ NZ].
  rewrite E. rewrite !in_app_iff. cbn [In]. split.
  - intros HY. split; [tauto|]. intros ->. apply NZ. apply in_app_iff. exact HY.
  - intros [[HA | [HZ | HB]] NE]; [left; exact HA | congruence | right; exact HB].
Qed.

Lemma find_text_some : forall x rs, In (bzs x) (rtexts rs) ->
  exists i, find_text x rs = Some i /\ (i < length rs)%nat /\ bzs (snd (nth i rs (0, []))) = bzs x.
Proof.
  intros x rs. induction rs as [|r rs IH]; intros H; [destruct H|].
  cbn [find_text]. destruct (list_eqb (bzs (snd r)) (bzs x)) eqn:E.
  - exists O. split; [reflexivity|]. split; [cbn [length]; lia|]. cbn [nth]. apply list_eqb_true. exact E.
  - destruct H as [H|H].
    + exfalso. rewrite H in E. rewrite list_eqb_refl in E. discriminate.
    + destruct (IH H) as (i & F & L & N). exists (S i). rewrite F. split; [reflexivity|].
      split; [cbn [length]; lia | exact N].
Qed.

Lemma rtexts_drop : forall i rs, rtexts (drop_nth i rs) = firstn i (rtexts rs) ++ skipn (S i) (rtexts rs).
Proof. intros i rs. unfold rtexts, drop_nth. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.

Lemma drop_nth_length : forall i (rs : list (Z * list byte)), (i < length rs)%nat ->
  length (drop_nth i rs) = (length rs - 1)%nat.
Proof.
  intros i rs Hi. unfold drop_nth. rewrite length_app, length_firstn, length_skipn. lia.
Qed.

Lemma skipn_len_app : forall {A} (x y : list A), skipn (length x) (x ++ y) = y.
Proof. intros A x y. induction x as [|a x IH]; [reflexivity|]. cbn [length app skipn]. exact IH. Qed.

Lemma firstn_len_app : forall {A} (x y : list A), firstn (length x) (x ++ y) = x.
Proof. intros A x y. induction x as [|a x IH]; [reflexivity|]. cbn [length app firstn]. f_equal. exact IH. Qed.

Lemma end_line_ok : forall x,
  (Nat.leb 4 (length (x ++ END4)) && list_eqb (bzs (skipn (length (x ++ END4) - 4) (x ++ END4))) (bzs END4) &&
   prefixb [] (x ++ END4)) = true /\
  firstn (length (x ++ END4) - 4) (x ++ END4) = x.
Proof.
  intros x. assert (L : (length (x ++ END4) - 4 = length x)%nat) by (rewrite length_app; change (length END4) with 4%nat; lia).
  rewrite L, skipn_len_app, firstn_len_app, list_eqb_refl, prefixb_nil.
  rewrite (proj2 (Nat.leb_le 4 (length (x ++ END4)))) by (rewrite length_app; change (length END4) with 4%nat; lia).
  split; reflexivity.
Qed.

Lemma nth_rtexts : forall rs i, (i < length rs)%nat -> nth i (rtexts rs) [] = bzs (snd (nth i rs (0, []))).
Proof.
  induction rs as [|r rs IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [rtexts map nth]. unfold rtexts in IH. apply IH. lia.
Qed.

Lemma ends_run_keys : forall ks rs d,
  NoDup (keys_texts ks) -> NoDup (rtexts rs) -> same_set (keys_texts ks) (rtexts rs) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (key_text k)) ks ->
  exists rs' ds, ends_run [] rs (keys_out ks ++ d) (length rs) = Some (rs', ds, Z.of_nat (length (keys_out ks))).
Proof.
  induction ks as [|k ks IH]; intros rs d NK NR SS NZ.
  { destruct rs as [|r rs].
    - exists [], []. reflexivity.
    - exfalso. apply (proj2 (SS (bzs (snd r)))). left. reflexivity. }
  inversion NZ as [|? ? NZ1 NZ2]; subst.
  apply NoDup_ListNoDup in NK. unfold keys_texts in NK. cbn [map] in NK.
  inversion NK as [|? ? NK1 NK2]; subst. fold (keys_texts ks) in NK1, NK2.
  assert (IK : In (bzs (key_text k)) (rtexts rs)) by (apply SS; left; reflexivity).
  destruct (find_text_some (key_text k) rs IK) as (i & F & Li & Ni).
  replace (length rs) with (S (length rs - 1)) by lia. cbn [ends_run].
  assert (KO : keys_out (k :: ks) ++ d = (key_text k ++ END4) ++ Z_to_bv 8 0 :: (keys_out ks ++ d)).
  { unfold keys_out. cbn [map concat]. fold (keys_out ks). unfold END5, END4. rewrite <- !app_assoc. reflexivity. }
  rewrite KO.
  assert (NZX : ~ In (Z_to_bv 8 0) (key_text k ++ END4)).
  { rewrite in_app_iff. intros [X | X]; [exact (NZ1 X)|].
    unfold END4 in X. cbn [In] in X.
    repeat (destruct X as [X | X]; [apply (f_equal bz) in X; rewrite !bz_lit in X by lia; discriminate|]).
    exact X. }
  rewrite (split_nul_app _ _ NZX). cbv beta iota zeta.
  destruct (end_line_ok (key_text k)) as [C1 C2]. rewrite C1, C2, F. cbv beta iota zeta.
  assert (LRi : (i < length (rtexts rs))%nat) by (unfold rtexts; rewrite length_map; exact Li).
  assert (NT : nth i (rtexts rs) [] = bzs (key_text k)) by (rewrite (nth_rtexts rs i Li); exact Ni).
  assert (SS' : same_set (keys_texts ks) (rtexts (drop_nth i rs))).
  { intros y. rewrite rtexts_drop. rewrite (in_drop_split (rtexts rs) i [] y NR LRi). rewrite NT.
    rewrite <- (SS y). unfold keys_texts at 2. cbn [map]. fold (keys_texts ks). split.
    - intros HY. split; [right; exact HY|]. intros ->. exact (NK1 HY).
    - intros [[HY | HY] NE]; [congruence | exact HY]. }
  assert (NR' : NoDup (rtexts (drop_nth i rs))).
  { apply NoDup_ListNoDup. rewrite rtexts_drop. pose proof (proj1 (NoDup_ListNoDup _) NR) as NR0.
    rewrite (split_at (rtexts rs) i [] LRi) in NR0. apply NoDup_remove_1 in NR0. exact NR0. }
  destruct (IH (drop_nth i rs) d (proj2 (NoDup_ListNoDup _) NK2) NR' SS' NZ2) as (rs' & ds & ER).
  rewrite (drop_nth_length i rs Li) in ER. rewrite ER.
  exists rs', (nth i rs (0, []) :: ds). f_equal. f_equal.
  unfold keys_out at 2. cbn [map concat]. fold (keys_out ks). rewrite !length_app.
  change (length END4) with 4%nat. change (length END5) with 5%nat. lia.
Qed.

Lemma remove_at_app_last : forall {X} (pre : list X) (last : X) i,
  remove_at i (pre ++ [last]) = if Nat.eqb i (length pre) then pre else firstn i pre ++ last :: skipn (S i) pre.
Proof. intros X pre last i. unfold remove_at. rewrite rev_app_distr. cbn [rev app]. rewrite rev_involutive. reflexivity. Qed.

Lemma remove_at_length : forall {X} (l : list X) i, (i < length l)%nat -> length (remove_at i l) = (length l - 1)%nat.
Proof.
  intros X l i Hi. destruct l as [|x p] using rev_ind; [cbn in Hi; lia|]. clear IHp.
  rewrite remove_at_app_last. rewrite length_app in *. cbn [length] in *.
  destruct (Nat.eqb_spec i (length p)); [lia|]. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma remove_at_perm : forall {X} (l : list X) i d, (i < length l)%nat -> Permutation l (nth i l d :: remove_at i l).
Proof.
  intros X l i d Hi. destruct l as [|x p] using rev_ind; [cbn in Hi; lia|]. clear IHp.
  rewrite remove_at_app_last. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.eqb_spec i (length p)) as [->|NE].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. apply Permutation_sym, Permutation_cons_append.
  - rewrite app_nth1 by lia. pose proof (split_at p i d ltac:(lia)) as Ep.
    rewrite Ep at 1. rewrite <- app_assoc. cbn [app].
    eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
    apply Permutation_app_head. apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma Forall2_firstn' : forall {X Y} (R : X -> Y -> Prop) n l1 l2, Forall2 R l1 l2 -> Forall2 R (firstn n l1) (firstn n l2).
Proof.
  intros X Y R n. induction n as [|n IH]; intros l1 l2 H; [constructor|].
  destruct H as [|a b l1 l2 Hab H]; [constructor|]. cbn [firstn]. constructor; [exact Hab | apply IH; exact H].
Qed.

Lemma Forall2_skipn' : forall {X Y} (R : X -> Y -> Prop) n l1 l2, Forall2 R l1 l2 -> Forall2 R (skipn n l1) (skipn n l2).
Proof.
  intros X Y R n. induction n as [|n IH]; intros l1 l2 H; [exact H|].
  destruct H as [|a b l1 l2 Hab H]; [constructor|]. cbn [skipn]. apply IH. exact H.
Qed.

Lemma Forall2_remove_at : forall {X Y} (R : X -> Y -> Prop) l1 l2 i,
  Forall2 R l1 l2 -> Forall2 R (remove_at i l1) (remove_at i l2).
Proof.
  intros X Y R l1 l2 i H. destruct l1 as [|x1 p1] using rev_ind.
  { inversion H; subst. constructor. }
  clear IHp1. apply Forall2_app_inv_l in H. destruct H as (p2 & t2 & Hp & Ht & ->).
  inversion Ht as [|? x2 ? ? Hx Hn]; subst. inversion Hn; subst.
  rewrite !remove_at_app_last. rewrite <- (Forall2_length Hp).
  destruct (Nat.eqb i (length p1)); [exact Hp|].
  apply Forall2_app; [apply Forall2_firstn'; exact Hp|]. constructor; [exact Hx | apply Forall2_skipn'; exact Hp].
Qed.

Lemma combine_firstn' : forall {X Y} n (l1 : list X) (l2 : list Y), combine (firstn n l1) (firstn n l2) = firstn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2; [reflexivity|].
  destruct l1 as [|a l1]; destruct l2 as [|b l2]; try reflexivity. cbn [firstn combine]. rewrite IH. reflexivity.
Qed.

Lemma combine_skipn' : forall {X Y} n (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  combine (skipn n l1) (skipn n l2) = skipn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2 L; [reflexivity|].
  destruct l1 as [|a l1]; destruct l2 as [|b l2]; cbn [length] in L; try discriminate; [reflexivity|].
  cbn [skipn combine]. apply IH. lia.
Qed.

Lemma combine_app' : forall {X Y} (a1 : list X) (a2 : list Y) b1 b2, length a1 = length a2 ->
  combine (a1 ++ b1) (a2 ++ b2) = combine a1 a2 ++ combine b1 b2.
Proof.
  intros X Y a1. induction a1 as [|x a1 IH]; intros [|y a2] b1 b2 L; cbn [length] in L; try discriminate; [reflexivity|].
  cbn [app combine]. f_equal. apply IH. lia.
Qed.

Lemma combine_remove_at : forall {X Y} (l1 : list X) (l2 : list Y) i, length l1 = length l2 ->
  combine (remove_at i l1) (remove_at i l2) = remove_at i (combine l1 l2).
Proof.
  intros X Y l1 l2 i L. destruct l1 as [|x1 p1] using rev_ind.
  { destruct l2; [reflexivity | cbn in L; discriminate]. }
  clear IHp1. destruct l2 as [|x2 p2] using rev_ind; [rewrite length_app in L; cbn in L; lia|]. clear IHp2.
  rewrite !length_app in L. cbn [length] in L.
  rewrite combine_app' by lia. cbn [combine].
  rewrite !remove_at_app_last. rewrite length_combine. replace (Nat.min (length p1) (length p2)) with (length p1) by lia.
  replace (length p2) with (length p1) by lia.
  destruct (Nat.eqb i (length p1)); [reflexivity|].
  rewrite combine_app' by (rewrite !length_firstn; lia). cbn [combine].
  rewrite combine_firstn', combine_skipn' by lia. reflexivity.
Qed.

Lemma sum_perm : forall (l l' : list Z), Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' P. induction P; cbn [fold_right]; lia. Qed.

Lemma pair_cost_nonneg : forall e p, 0 <= re_used e -> 0 <= pair_cost e p.
Proof. intros e p H. unfold pair_cost. pose proof (keys_total_nonneg (re_keys e)). destruct (re_skip e =? 0); lia. Qed.

Lemma sum_nonneg : forall {X} (f : X -> Z) l, Forall (fun y => 0 <= f y) l -> 0 <= fold_right Z.add 0 (map f l).
Proof. intros X f l H. induction H as [|y l Hy H IH]; cbn [map fold_right]; lia. Qed.

Lemma sum_ge_in : forall {X} (f : X -> Z) l x, In x l -> Forall (fun y => 0 <= f y) l ->
  f x <= fold_right Z.add 0 (map f l).
Proof.
  intros X f l x Hx H. induction H as [|y l Hy H IH]; [destruct Hx|]. cbn [map fold_right].
  destruct Hx as [<- | Hx]; [pose proof (sum_nonneg f l H); lia | specialize (IH Hx); lia].
Qed.

Lemma cost_pairs_nonneg : forall es hj, Forall (fun e => 0 <= re_used e) es ->
  Forall (fun q : rentry * (hsrc * nat) => 0 <= pair_cost (fst q) (snd q)) (combine es hj).
Proof.
  intros es hj NN. apply Forall_forall. intros [e p] Hq. apply in_combine_l in Hq. cbn [fst snd].
  apply pair_cost_nonneg. rewrite Forall_forall in NN. exact (NN e Hq).
Qed.

Lemma pair_cost_le_slot : forall es hj e p, In (e, p) (combine es hj) -> Forall (fun e => 0 <= re_used e) es ->
  pair_cost e p <= slot_cost es hj.
Proof.
  intros es hj e p Hin NN. unfold slot_cost.
  exact (sum_ge_in (fun q : rentry * (hsrc * nat) => pair_cost (fst q) (snd q)) _ (e, p) Hin (cost_pairs_nonneg es hj NN)).
Qed.

Lemma slot_cost_remove_at : forall es hj i, length es = length hj -> (i < length es)%nat ->
  Forall (fun e => 0 <= re_used e) es ->
  slot_cost (remove_at i es) (remove_at i hj) <= slot_cost es hj.
Proof.
  intros es hj i L Hi NN. unfold slot_cost. rewrite combine_remove_at by exact L.
  pose proof (cost_pairs_nonneg es hj NN) as CN.
  assert (Hc : (i < length (combine es hj))%nat) by (rewrite length_combine; lia).
  destruct (combine es hj) as [|q0 cs'] eqn:EC; try rewrite EC in CN; try rewrite EC in Hc;
    [cbn [length] in Hc; lia|].
  pose proof (remove_at_perm (q0 :: cs') i q0 Hc) as P.
  apply (Permutation_map (fun q : rentry * (hsrc * nat) => pair_cost (fst q) (snd q))) in P.
  apply sum_perm in P. rewrite P. cbn [map fold_right].
  assert (Hin : In (nth i (q0 :: cs') q0) (q0 :: cs')) by (apply nth_In; exact Hc).
  rewrite Forall_forall in CN. pose proof (CN _ Hin) as N0. cbv beta in N0. lia.
Qed.

Lemma wcost_nonneg : forall st, 0 <= wcost st.
Proof. intros [w k]. unfold wcost. cbn [ls_k ls_w]. destruct k; lia. Qed.

Lemma hs_wcost : forall (e : rentry) (h : hsrc), re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (hs_overlong h = 0 \/ hs_overlong h = 1) -> Z.of_nat (length (re_U e)) = re_used e ->
  wcost (hs_state h) = (if re_skip e =? 0 then re_used e else 0).
Proof.
  intros e h E1 E2 Ho Hu. unfold wcost, hs_state. cbn [ls_k ls_w].
  destruct Ho as [Ho | Ho]; rewrite Ho; cbn [Z.eqb Pos.eqb]; rewrite E1, Ho; cbn [Z.eqb Pos.eqb]; [|reflexivity].
  rewrite <- Hu, <- (bzs_length (re_U e)), (E2 ltac:(rewrite E1; exact Ho)). reflexivity.
Qed.

Lemma reads_bound : forall (e : rentry) (h : hsrc), re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (hs_overlong h = 0 \/ hs_overlong h = 1) -> Z.of_nat (length (re_U e)) = re_used e ->
  Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) <=
    (if re_skip e =? 0 then re_used e else 0) + Z.of_nat (length (pending_stream h)).
Proof.
  intros e h E1 E2 Ho Hu. pose proof (lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB.
  rewrite (hs_wcost e h E1 E2 Ho Hu), bzs_length in LB. pose proof (wcost_nonneg (feed (hs_state h) (bzs (pending_stream h)))).
  lia.
Qed.
