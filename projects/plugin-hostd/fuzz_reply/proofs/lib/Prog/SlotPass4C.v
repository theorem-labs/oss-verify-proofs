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
  relay_remove_b_c SlotInv SlotReads HarnessTr.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p4_texts_length : forall l, Z.of_nat (length (texts l)) = hl_n l.
Proof. intros l. unfold texts, hl_n. rewrite length_map. reflexivity. Qed.

Lemma p4_lines_zr : forall h P, Forall zrange (lines (hs_state h) (bzs P)).
Proof.
  intros h P. apply (lines_range (bzs P) (hs_state h)); [unfold hs_state; cbn [ls_w]|]; apply zrange_bzs.
Qed.

Lemma p4_bstream : forall E Ls LB, map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  bzs LB = with_nul Ls -> bstream E = LB.
Proof. intros E Ls LB H1 H2 H3. apply bzs_inj. rewrite (bstream_bzs E Ls H1 H2). symmetry. exact H3. Qed.

Lemma p4_held_len : forall ks H, NoDup (texts H) -> same_set (keys_texts ks) (texts H) ->
  (length (texts H) <= length ks)%nat.
Proof.
  intros ks H ND S. apply NoDup_ListNoDup in ND.
  replace (length ks) with (length (keys_texts ks)) by (unfold keys_texts; apply length_map).
  apply NoDup_incl_length; [exact ND|]. intros y Hy. apply S. exact Hy.
Qed.

Lemma p4_cnl_bound : forall (e : rentry) (h : hsrc) (i : nat) (H : hlist) (Ls : list (list Z)) es hj k,
  In (e, (h, i)) (combine es hj) -> Forall (fun e => 0 <= re_used e) es -> slot_cost es hj <= k -> k < 2 ^ 26 ->
  Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e) ->
  (length (texts H) <= length (re_keys e))%nat ->
  Z.of_nat (length (with_nul Ls)) <= (if re_skip e =? 0 then re_used e else 0) + Z.of_nat (length (pending_stream h)) ->
  hl_n H + Z.of_nat (count_begin Ls) < 2 ^ 22 /\ Z.of_nat (length Ls) < 2 ^ 26.
Proof.
  intros e h i H Ls es hj k Hin NN HC Hk KL HL WB.
  pose proof (pair_cost_le_slot es hj e (h, i) Hin NN) as PC. unfold pair_cost in PC. cbn [fst] in PC.
  pose proof (keys_total_count (re_keys e) KL) as KT.
  pose proof (count_begin_bytes Ls) as CB. pose proof (lines_count Ls) as LC.
  pose proof (p4_texts_length H) as TL.
  assert (U : 0 <= re_used e) by (rewrite Forall_forall in NN; apply NN; exact (in_combine_l _ _ _ _ Hin)).
  assert (S0 : 0 <= (if re_skip e =? 0 then re_used e else 0)) by (destruct (re_skip e =? 0); lia).
  split; lia.
Qed.

Lemma p4_nozero : forall ks (rs : list (Z * list byte)), Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  (forall y, In y (keys_texts ks) -> In y (rtexts rs)) -> Forall (fun k => ~ In (Z_to_bv 8 0) (key_text k)) ks.
Proof.
  intros ks rs HR HS. apply Forall_forall. intros k Hk HZ.
  assert (Hy : In (bzs (key_text k)) (keys_texts ks))
    by (unfold keys_texts; apply (in_map (fun k => bzs (key_text k))); exact Hk).
  apply HS in Hy. unfold rtexts in Hy. apply in_map_iff in Hy. destruct Hy as (r & Er & Hr).
  apply bzs_inj in Er. rewrite Forall_forall in HR. apply (HR r Hr). rewrite Er. exact HZ.
Qed.

Lemma p4_held_set : forall ks ks' H Ls, same_set (keys_texts ks) (texts H) ->
  same_set (keys_texts ks') (upds (keys_texts ks) Ls) -> same_set (keys_texts ks') (upds (texts H) Ls).
Proof. intros ks ks' H Ls S1 S2. eapply same_set_trans; [exact S2|]. apply upds_same_set. exact S1. Qed.

Lemma p4_ends_some : forall ks rs d, NoDup (keys_texts ks) -> NoDup (rtexts rs) -> same_set (keys_texts ks) (rtexts rs) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (key_text k)) ks ->
  exists rs' ds, ends_run [] rs (keys_out ks ++ d) (want_of [] rs) = Some (rs', ds, Z.of_nat (length (keys_out ks))).
Proof. intros ks rs d N1 N2 S Z0. rewrite want_of_nil. apply ends_run_keys; assumption. Qed.

Lemma p4_at_total : forall LB Ls ks, bzs LB = with_nul Ls ->
  Z.of_nat (length LB) + Z.of_nat (length (keys_out ks)) = Z.of_nat (length (with_nul Ls)) + keys_total ks.
Proof. intros LB Ls ks H. rewrite keys_out_length, <- (bzs_length LB), H. reflexivity. Qed.

Lemma p4_keys_nil : forall ks, keys_total ks = 0 -> Forall (fun x => 14 <= Z.of_nat (length (key_text x))) ks -> ks = [].
Proof.
  intros ks H F. pose proof (keys_total_count ks F). destruct ks as [|k ks]; [reflexivity|]. cbn [length] in *. lia.
Qed.

Lemma p4_with_nul_nil : forall Ls, Z.of_nat (length (with_nul Ls)) = 0 -> Ls = [].
Proof. intros Ls H. pose proof (lines_count Ls). destruct Ls; [reflexivity|]. cbn [length] in *. lia. Qed.

Lemma p4_in_remove_at : forall {X} (l : list X) i x, (i < length l)%nat -> In x (remove_at i l) -> In x l.
Proof.
  intros X l i x Hi H. destruct l as [|d l']; [cbn in Hi; lia|].
  apply (Permutation_in x (Permutation_sym (remove_at_perm (d :: l') i d Hi))). right. exact H.
Qed.

Lemma p4_map_remove_at : forall {X Y} (f : X -> Y) (l : list X) i d, (i < length l)%nat ->
  Permutation (map f l) (f (nth i l d) :: map f (remove_at i l)).
Proof.
  intros X Y f l i d Hi. change (f (nth i l d) :: map f (remove_at i l)) with (map f (nth i l d :: remove_at i l)).
  apply Permutation_map. apply remove_at_perm. exact Hi.
Qed.

Lemma p4_nodup_map_remove_at : forall {X Y} (f : X -> Y) (l : list X) i d, (i < length l)%nat ->
  NoDup (map f l) -> NoDup (map f (remove_at i l)) /\ ~ In (f (nth i l d)) (map f (remove_at i l)).
Proof.
  intros X Y f l i d Hi ND. apply NoDup_ListNoDup in ND.
  pose proof (Permutation_NoDup (p4_map_remove_at f l i d Hi) ND) as N1. inversion N1 as [|? ? N2 N3]; subst.
  split; [apply NoDup_ListNoDup; exact N3 | exact N2].
Qed.

Lemma p4_in_map_remove_at : forall {X Y} (f : X -> Y) (l : list X) i d y, (i < length l)%nat ->
  In y (map f l) -> y <> f (nth i l d) -> In y (map f (remove_at i l)).
Proof.
  intros X Y f l i d y Hi Hy Ne. apply (Permutation_in y (p4_map_remove_at f l i d Hi)) in Hy.
  destruct Hy as [Hy|Hy]; [congruence | exact Hy].
Qed.

Lemma p4_perm_concat_map : forall {X Y} (f : X -> list Y) (l l' : list X), Permutation l l' ->
  Permutation (concat (map f l)) (concat (map f l')).
Proof.
  intros X Y f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [map concat].
  - constructor.
  - apply Permutation_app_head. exact IH.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma p4_perm_shuffle : forall {X} (g o : X) A A' a B B' b, Permutation A (a ++ A') -> Permutation B (b ++ B') ->
  Permutation (g :: o :: A ++ B) ((a ++ b) ++ (g :: o :: A' ++ B')).
Proof.
  intros X g o A A' a B B' b P1 P2.
  eapply Permutation_trans; [apply perm_skip, perm_skip, Permutation_app; [exact P1 | exact P2]|].
  change (g :: o :: (a ++ A') ++ b ++ B') with ([g; o] ++ (a ++ A') ++ b ++ B').
  change (g :: o :: A' ++ B') with ([g; o] ++ A' ++ B').
  rewrite <- !app_assoc.
  eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head.
  pose proof (Permutation_app_swap_app ([g; o] ++ A') b B') as S. rewrite <- !app_assoc in S. exact S.
Qed.

Lemma p4_target_remove_at : forall G OUT es hj i, (i < length es)%nat -> (i < length hj)%nat ->
  NoDup (target_addrs G OUT es hj) -> NoDup (target_addrs G OUT (remove_at i es) (remove_at i hj)).
Proof.
  intros G OUT es hj i He Hh ND. apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup. unfold target_addrs in *.
  destruct hj as [|p0 hj0] eqn:EH; [cbn in Hh; lia|]. rewrite <- EH in *.
  pose proof (p4_perm_concat_map entry_blocks _ _ (remove_at_perm es i no_entry He)) as P1.
  pose proof (p4_perm_concat_map (fun p : hsrc * nat => hs_blocks (fst p)) _ _ (remove_at_perm hj i p0 Hh)) as P2.
  change (concat (map entry_blocks (nth i es no_entry :: remove_at i es))) with
    (entry_blocks (nth i es no_entry) ++ concat (map entry_blocks (remove_at i es))) in P1.
  change (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (nth i hj p0 :: remove_at i hj))) with
    (hs_blocks (fst (nth i hj p0)) ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at i hj))) in P2.
  pose proof (Permutation_NoDup (p4_perm_shuffle G OUT _ _ _ _ _ _ P1 P2) ND) as N.
  apply NoDup_app_remove_l in N. exact N.
Qed.

Lemma p4_slot_open_remove_at : forall hj i d, (i < length hj)%nat -> NoDup (map snd hj) ->
  slot_open (remove_at i hj) (snd (nth i hj d)) = false /\
  (forall x, x <> snd (nth i hj d) -> slot_open (remove_at i hj) x = slot_open hj x).
Proof.
  intros hj i d Hi ND. destruct (p4_nodup_map_remove_at snd hj i d Hi ND) as [_ NI].
  unfold slot_open. split.
  - destruct (existsb (Nat.eqb (snd (nth i hj d))) (map snd (remove_at i hj))) eqn:EX; [|reflexivity].
    exfalso. apply existsb_exists in EX. destruct EX as (y & Hy & Ey). apply Nat.eqb_eq in Ey. subst y. exact (NI Hy).
  - intros x Nx.
    destruct (existsb (Nat.eqb x) (map snd hj)) eqn:E1; destruct (existsb (Nat.eqb x) (map snd (remove_at i hj))) eqn:E2;
      try reflexivity; exfalso.
    + apply not_true_iff_false in E2. apply E2. apply existsb_exists in E1. destruct E1 as (y & Hy & Ey).
      apply Nat.eqb_eq in Ey. subst y. apply existsb_exists. exists x. split; [|apply Nat.eqb_refl].
      exact (p4_in_map_remove_at snd hj i d x Hi Hy Nx).
    + apply not_true_iff_false in E1. apply E1. apply existsb_exists in E2. destruct E2 as (y & Hy & Ey).
      apply Nat.eqb_eq in Ey. subst y. apply existsb_exists. exists x. split; [|apply Nat.eqb_refl].
      apply in_map_iff in Hy. destruct Hy as (p & Ep & Hp). subst x. apply in_map. exact (p4_in_remove_at hj i p Hi Hp).
Qed.

Lemma p4_forall2_mem : forall {X Y} (R R' : X -> Y -> Prop) l1 l2, Forall2 R l1 l2 ->
  (forall x y, In (x, y) (combine l1 l2) -> R x y -> R' x y) -> Forall2 R' l1 l2.
Proof.
  intros X Y R R' l1 l2 H. induction H as [|x y l1 l2 Hxy H IH]; intros HI; constructor.
  - apply HI; [left; reflexivity | exact Hxy].
  - apply IH. intros a b Hab Rab. apply HI; [right; exact Hab | exact Rab].
Qed.
