From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayRunT RelayRunF RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c
  relay_finish_b_c
  RelayRep HarnessRep drain_b_c relay_remove_b_c relay_instance_gone_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition rig_dk : Z * list byte * list byte := (0, [], []).

Lemma rigl_set_nth_len : forall {A} n (y : A) l, length (set_nth n y l) = length l.
Proof. intros A n y l. revert n. induction l as [|h t IH]; intros [|n]; cbn; try reflexivity; f_equal; apply IH. Qed.

Lemma rigl_len_swap : forall {A} (d : A) n l, length (swap_remove d n l) = (length l - 1)%nat.
Proof. intros A d n l. unfold swap_remove. rewrite firstn_length, rigl_set_nth_len. lia. Qed.

Lemma rigl_map_set_nth : forall {A B} (f : A -> B) n y l, map f (set_nth n y l) = set_nth n (f y) (map f l).
Proof. intros A B f n y l. revert n. induction l as [|h t IH]; intros [|n]; cbn; try reflexivity; f_equal; apply IH. Qed.

Lemma rigl_last_map : forall {A B} (f : A -> B) d l, f (last l d) = last (map f l) (f d).
Proof. intros A B f d l. induction l as [|a l IH]; [reflexivity|]. destruct l as [|b l]; [reflexivity|]. exact IH. Qed.

Lemma rigl_map_firstn : forall {A B} (f : A -> B) k l, map f (firstn k l) = firstn k (map f l).
Proof. intros A B f k. induction k as [|k IH]; intros [|a l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma rigl_nth_set_nth : forall {A} n (y : A) l j d, (n < length l)%nat ->
  nth j (set_nth n y l) d = if Nat.eqb j n then y else nth j l d.
Proof.
  intros A n y l. revert n. induction l as [|h t IH]; intros n j d Hn; cbn in Hn; [lia|].
  destruct n as [|n], j as [|j]; cbn; try reflexivity. apply IH. lia.
Qed.

Lemma rigl_nth_firstn : forall {A} k (l : list A) j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  intros A k. induction k as [|k IH]; intros l j d Hj; [lia|].
  destruct l as [|a l]; [destruct j; reflexivity|]. destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma rigl_last_nth : forall {A} (l : list A) d, last l d = nth (length l - 1) l d.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|]. destruct l as [|b l]; [reflexivity|].
  change (last (b :: l) d = nth (length (a :: b :: l) - 1) (a :: b :: l) d).
  rewrite IH. cbn [length]. replace (S (S (length l)) - 1)%nat with (S (S (length l) - 1)) by lia. reflexivity.
Qed.

Lemma rigl_in_firstn : forall {A} k (l : list A) x, In x (firstn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

Lemma rigl_in_set_nth : forall {A} n (y : A) l x, In x (set_nth n y l) -> In x l \/ x = y.
Proof.
  intros A n y l. revert n. induction l as [|h t IH]; intros [|n] x Hx; cbn in Hx; try contradiction.
  - destruct Hx as [<-|Hx]; [right; reflexivity| left; right; exact Hx].
  - destruct Hx as [<-|Hx]; [left; left; reflexivity|].
    destruct (IH n x Hx) as [H|H]; [left; right; exact H| right; exact H].
Qed.

Lemma rigl_swap_perm : forall {A} (d : A) n l, (n < length l)%nat ->
  Permutation l (nth n l d :: swap_remove d n l).
Proof.
  intros A d n l Hn. destruct (nth_split l d Hn) as (a & b & E & La).
  set (x := nth n l d) in *. clearbody x. subst l n.
  apply swap_remove_perm.
Qed.

Lemma rigl_kp_cons : forall k K, key_ptrs (k :: K) = le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs K.
Proof. reflexivity. Qed.

Lemma rigl_firstn_le8 : forall v (rest : list byte), firstn 8 (le8 v ++ rest) = le8 v.
Proof.
  intros v rest. rewrite firstn_app, length_le8. replace (8 - 8)%nat with 0%nat by lia.
  rewrite firstn_all2 by (rewrite length_le8; lia). cbn [firstn]. apply app_nil_r.
Qed.

Lemma rigl_skipn_le8 : forall v (rest : list byte) j, skipn (8 + j) (le8 v ++ rest) = skipn j rest.
Proof.
  intros v rest j. rewrite skipn_app, length_le8. rewrite skipn_all2 by (rewrite length_le8; lia).
  replace (8 + j - 8)%nat with j by lia. reflexivity.
Qed.

Lemma rigl_with_nul_cons : forall l L, length (with_nul (l :: L)) = (length l + 1 + length (with_nul L))%nat.
Proof. intros l L. unfold with_nul. cbn [map concat]. rewrite !length_app. cbn [length]. lia. Qed.

Lemma rigl_step_pot : forall st b,
  (length (ls_w (fst (step st b))) + match snd (step st b) with Some l => length l + 1 | None => 0 end
     <= length (ls_w st) + 1)%nat.
Proof.
  intros [w k] b. unfold step. cbn [ls_w ls_k].
  destruct (b =? 0); [destruct k; cbn; lia|].
  destruct k; [cbn; lia|]. destruct (Nat.eqb (length w) LINE_LIMIT); cbn; [lia|]. rewrite length_app. cbn. lia.
Qed.

Lemma rigl_wn_inv : forall d st,
  (length (with_nul (lines st d)) + length (ls_w (feed st d)) <= length (ls_w st) + length d)%nat.
Proof.
  induction d as [|b d IH]; intros st.
  - cbn. lia.
  - unfold lines, feed in *. rewrite feed_lines_cons. cbn [fst snd length].
    specialize (IH (fst (step st b))).
    pose proof (rigl_step_pot st b) as P. revert P.
    destruct (snd (step st b)) as [l|]; intros P.
    + rewrite rigl_with_nul_cons. lia.
    + lia.
Qed.

Lemma rigl_filter_len : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [|a l IH]; [cbn; lia|]. cbn [List.filter]. destruct (f a); cbn [length]; lia. Qed.

Lemma rigl_upd_len : forall G l, (length (upd G l) <= length G + 1)%nat.
Proof.
  intros G l. unfold upd. destruct (gesture l) as [[[|] x]|]; cbv beta iota.
  - destruct (existsb (list_eqb x) G); [lia|]. rewrite length_app. cbn [length]. lia.
  - pose proof (rigl_filter_len (fun y => negb (list_eqb x y)) G). lia.
  - lia.
Qed.

Lemma rigl_fold_add_acc : forall (l : list Z) a, fold_right Z.add a l = fold_right Z.add 0 l + a.
Proof. induction l as [|x l IH]; intros a; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma rigl_firstn_app_exact : forall {A} (X Y : list A) n, length X = n -> firstn n (X ++ Y) = X.
Proof. intros A X Y n <-. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. Qed.

Lemma rigl_concat_len : forall (l : list rentry), Forall (fun e => length (entry_bytes e) = 56%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
  induction l as [|e l IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H. destruct H as [He Hl].
  cbn [map concat length]. rewrite length_app, He, (IH Hl). lia.
Qed.

Lemma rigl_in_nth_concat : forall (Xs : list (list Z)) j x, In x (nth j Xs []) -> In x (concat Xs).
Proof.
  intros Xs j x H. destruct (Nat.lt_ge_cases j (length Xs)) as [Hj|Hj].
  - apply in_concat. exists (nth j Xs []). split; [apply nth_In; exact Hj| exact H].
  - rewrite nth_overflow in H by exact Hj. destruct H.
Qed.

Lemma rigl_concat_split : forall (Xs : list (list Z)) i, (i < length Xs)%nat ->
  concat Xs = concat (firstn i Xs) ++ nth i Xs [] ++ concat (skipn (S i) Xs).
Proof.
  intros Xs i Hi. destruct (nth_split Xs [] Hi) as (a & b & E & La).
  set (x := nth i Xs []) in *. clearbody x. subst Xs i.
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  replace (skipn (S (length a)) (a ++ x :: b)) with b.
  2: { rewrite skipn_app, skipn_all2 by lia. replace (S (length a) - length a)%nat with 1%nat by lia. reflexivity. }
  rewrite concat_app. reflexivity.
Qed.

Lemma rigl_nodup_mid : forall (l1 l2 l3 : list Z), List.NoDup (l1 ++ l2 ++ l3) -> List.NoDup (l1 ++ l3).
Proof.
  induction l1 as [|a l1 IH]; intros l2 l3 H.
  - exact (NoDup_app_remove_l l2 l3 H).
  - cbn [app] in *. apply NoDup_cons_iff in H. destruct H as [Hn H]. constructor.
    + intros Hin. apply Hn. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin|Hin]; [left; exact Hin|right; apply in_or_app; right; exact Hin].
    + exact (IH l2 l3 H).
Qed.

Lemma rigl_mod_mod : forall a, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
  intros a. rewrite (Z.div_mod a (2 ^ 64)) at 2 by lia.
  replace (2 ^ 64 * (a / 2 ^ 64)) with ((2 ^ 32 * (a / 2 ^ 64)) * 2 ^ 32) by lia.
  rewrite Z.add_comm, Z.mod_add by lia; reflexivity.
Qed.

Lemma rigl_nth_error_ext : forall {A} (l l' : list A), (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  intros A l. induction l as [|a l IH]; intros [|b l'] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma rig_gei_end : forall f pre n H, (length H <= n)%nat -> gei_loop f pre n H = ([], H).
Proof.
  intros f pre n H Hn. destruct f as [|f]; [reflexivity|]. cbn [gei_loop].
  replace (Nat.ltb n (length H)) with false by (symmetry; apply Nat.ltb_ge; exact Hn). reflexivity.
Qed.

Lemma rig_gei_match : forall f pre n H, (n < length H)%nat -> has_prefix pre (nth n H []) = true ->
  gei_loop (S f) pre n H =
    (nth n H [] :: fst (gei_loop f pre n (swap_remove [] n H)), snd (gei_loop f pre n (swap_remove [] n H))).
Proof.
  intros f pre n H Hn Hp. cbn [gei_loop].
  replace (Nat.ltb n (length H)) with true by (symmetry; apply Nat.ltb_lt; exact Hn). rewrite Hp.
  destruct (gei_loop f pre n (swap_remove [] n H)); reflexivity.
Qed.

Lemma rig_gei_skip : forall f pre n H, (n < length H)%nat -> has_prefix pre (nth n H []) = false ->
  gei_loop (S f) pre n H = gei_loop f pre (S n) H.
Proof.
  intros f pre n H Hn Hp. cbn [gei_loop].
  replace (Nat.ltb n (length H)) with true by (symmetry; apply Nat.ltb_lt; exact Hn). rewrite Hp. reflexivity.
Qed.

Lemma rig_gei_fuel : forall f1 f2 pre n H, (length H - n <= f1)%nat -> (length H - n <= f2)%nat ->
  gei_loop f1 pre n H = gei_loop f2 pre n H.
Proof.
  induction f1 as [|f1 IH]; intros f2 pre n H H1 H2.
  - rewrite (rig_gei_end f2 pre n H) by lia. reflexivity.
  - destruct (Nat.lt_ge_cases n (length H)) as [Hn|Hn].
    + destruct f2 as [|f2]; [lia|].
      destruct (has_prefix pre (nth n H [])) eqn:Ep.
      * rewrite (rig_gei_match f1 pre n H Hn Ep), (rig_gei_match f2 pre n H Hn Ep).
        rewrite (IH f2 pre n (swap_remove [] n H)); [reflexivity | rewrite rigl_len_swap; lia | rewrite rigl_len_swap; lia].
      * rewrite (rig_gei_skip f1 pre n H Hn Ep), (rig_gei_skip f2 pre n H Hn Ep).
        apply IH; lia.
    + rewrite (rig_gei_end (S f1) pre n H Hn), (rig_gei_end f2 pre n H Hn). reflexivity.
Qed.

Lemma rig_len_swap : forall {A} (d : A) n l, (n < length l)%nat -> length (swap_remove d n l) = (length l - 1)%nat.
Proof. intros A d n l _. unfold swap_remove. rewrite firstn_length, rigl_set_nth_len. lia. Qed.

Lemma rig_swap_map : forall {A B} (f : A -> B) d n l, (n < length l)%nat ->
  map f (swap_remove d n l) = swap_remove (f d) n (map f l).
Proof.
  intros A B f d n l _. unfold swap_remove.
  rewrite rigl_map_firstn, rigl_map_set_nth, length_map, (rigl_last_map f d l). reflexivity.
Qed.

Lemma rig_nth_swap : forall {A} (d : A) n l j, (n < length l)%nat -> (j < length l - 1)%nat ->
  nth j (swap_remove d n l) d = if Nat.eqb j n then nth (length l - 1) l d else nth j l d.
Proof.
  intros A d n l j Hn Hj. unfold swap_remove.
  rewrite rigl_nth_firstn by exact Hj. rewrite rigl_nth_set_nth by exact Hn. rewrite rigl_last_nth. reflexivity.
Qed.

Lemma rig_swap_incl : forall {A} (d : A) n l x, In x (swap_remove d n l) -> In x l.
Proof.
  intros A d n l x H. unfold swap_remove in H. apply rigl_in_firstn in H.
  destruct (rigl_in_set_nth _ _ _ _ H) as [H1|H1]; [exact H1|]. subst x.
  destruct l as [|a l]; [destruct n; cbn in H; contradiction|].
  rewrite rigl_last_nth. apply nth_In. cbn [length]. lia.
Qed.

Lemma rig_swap_nodup : forall {A} (d : A) n l, (n < length l)%nat -> List.NoDup l -> List.NoDup (swap_remove d n l).
Proof.
  intros A d n l Hn Hnd. pose proof (Permutation_NoDup (rigl_swap_perm d n l Hn) Hnd) as H.
  apply NoDup_cons_iff in H. exact (proj2 H).
Qed.

Lemma rig_swap_removed : forall {A} (d : A) n l, (n < length l)%nat -> List.NoDup l ->
  ~ In (nth n l d) (swap_remove d n l).
Proof.
  intros A d n l Hn Hnd. pose proof (Permutation_NoDup (rigl_swap_perm d n l Hn) Hnd) as H.
  apply NoDup_cons_iff in H. exact (proj1 H).
Qed.

Lemma rig_swap_keep : forall {A} (d : A) n l x, (n < length l)%nat -> In x l -> x <> nth n l d -> In x (swap_remove d n l).
Proof.
  intros A d n l x Hn Hx Hne. pose proof (Permutation_in x (rigl_swap_perm d n l Hn) Hx) as H.
  destruct H as [H|H]; [congruence|exact H].
Qed.

Lemma rig_key_ptrs_nth : forall K j, (j < length K)%nat ->
  firstn 8 (skipn (8 * j) (key_ptrs K)) = le8 (Z_to_bv 64 (key_addr (nth j K rig_dk))).
Proof.
  induction K as [|k K IH]; intros j Hj; cbn [length] in Hj; [lia|].
  rewrite rigl_kp_cons. destruct j as [|j].
  - cbn [Nat.mul skipn nth]. apply rigl_firstn_le8.
  - replace (8 * S j)%nat with (8 + 8 * j)%nat by lia. rewrite rigl_skipn_le8. cbn [nth]. apply IH. lia.
Qed.

Lemma rig_key_ptrs_bytes : forall segs m hp K, 0 <= hp -> hp + 8 * Z.of_nat (length K) <= 2 ^ 64 ->
  (forall j, (j < length K)%nat -> bytes_at segs m (hp + 8 * Z.of_nat j) (le8 (Z_to_bv 64 (key_addr (nth j K rig_dk))))) ->
  bytes_at segs m hp (key_ptrs K).
Proof.
  intros segs m hp K. revert hp. induction K as [|k K IH]; intros hp H0 H1 H.
  - unfold bytes_at. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - rewrite rigl_kp_cons. apply bytes_at_app. split.
    + specialize (H 0%nat ltac:(cbn [length]; lia)). cbn [nth Z.of_nat] in H. rewrite Z.mul_0_r, Z.add_0_r in H. exact H.
    + rewrite length_le8. apply IH.
      * lia.
      * cbn [length] in H1. lia.
      * intros j Hj. specialize (H (S j) ltac:(cbn [length]; lia)). cbn [nth] in H.
        replace (hp + Z.of_nat 8 + 8 * Z.of_nat j) with (hp + 8 * Z.of_nat (S j)) by lia. exact H.
Qed.

Lemma rig_key_ptrs_slot : forall segs m hp K j, bytes_at segs m hp (key_ptrs K) -> (j < length K)%nat ->
  bytes_at segs m (hp + 8 * Z.of_nat j) (le8 (Z_to_bv 64 (key_addr (nth j K rig_dk)))).
Proof.
  intros segs m hp K. revert hp. induction K as [|k K IH]; intros hp j H Hj; cbn [length] in Hj; [lia|].
  rewrite rigl_kp_cons in H. apply bytes_at_app in H. destruct H as [H0 H1]. rewrite length_le8 in H1.
  destruct j as [|j].
  - cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact H0.
  - cbn [nth]. replace (hp + 8 * Z.of_nat (S j)) with (hp + Z.of_nat 8 + 8 * Z.of_nat j) by lia.
    apply IH; [exact H1| lia].
Qed.

Lemma rig_lines_len : forall st d, (length (lines st d) <= length d)%nat.
Proof.
  intros st d. revert st. induction d as [|b d IH]; intros st; [cbn; lia|].
  unfold lines in *. rewrite feed_lines_cons. cbn [snd length].
  specialize (IH (fst (step st b))).
  destruct (snd (step st b)); cbn [length]; lia.
Qed.

Lemma rig_with_nul_len : forall st d,
  (length (with_nul (lines st d)) <= length (ls_w st) + length d)%nat.
Proof. intros st d. pose proof (rigl_wn_inv d st). lia. Qed.

Lemma rig_upds_len : forall G ls, (length (upds G ls) <= length G + length ls)%nat.
Proof.
  intros G ls. revert G. induction ls as [|l ls IH]; intros G; [cbn; lia|].
  unfold upds in *. cbn [fold_left length]. specialize (IH (upd G l)). pose proof (rigl_upd_len G l). lia.
Qed.

Lemma rig_nodup_incl_len : forall (ks G : list (list Z)), List.NoDup ks -> (forall y, In y ks -> In y G) ->
  (length ks <= length G)%nat.
Proof. intros ks G H1 H2. apply NoDup_incl_length; [exact H1| exact H2]. Qed.

Lemma rig_fold_seq_S : forall (g : nat -> Z) i, fold_right Z.add 0 (map g (seq 0 (S i))) = fold_right Z.add 0 (map g (seq 0 i)) + g i.
Proof.
  intros g i. rewrite seq_S, map_app, fold_right_app. cbn [map fold_right]. change (0 + i)%nat with i.
  rewrite (rigl_fold_add_acc (map g (seq 0 i)) (g i + 0)). lia.
Qed.

Lemma rig_fold_seq_le : forall (g : nat -> Z) i j, (i <= j)%nat -> (forall k, 0 <= g k) ->
  fold_right Z.add 0 (map g (seq 0 i)) <= fold_right Z.add 0 (map g (seq 0 j)).
Proof.
  intros g i j Hij Hg. induction Hij as [|j Hij IH]; [lia|].
  rewrite rig_fold_seq_S. specialize (Hg j). lia.
Qed.

Lemma rig_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat -> length (entry_bytes e) = 56%nat.
Proof. intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity. Qed.

Lemma rig_entry_split : forall e, length (re_pad1 e) = 4%nat ->
  entry_bytes e = firstn 40 (entry_bytes e) ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e /\
  firstn 8 (entry_bytes e) = le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)).
Proof.
  intros e H1.
  assert (E : entry_bytes e = (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++
     re_pad1 e ++ le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e))) ++
     (le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e))
    by (unfold entry_bytes; rewrite <- !app_assoc; reflexivity).
  assert (E2 : entry_bytes e = (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e))) ++
     (le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++ le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++
      le8 (Z_to_bv 64 (re_cap e)) ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e))
    by (unfold entry_bytes; rewrite <- !app_assoc; reflexivity).
  split.
  - rewrite E at 2. rewrite rigl_firstn_app_exact by (rewrite !length_app, !length_le4, !length_le8, H1; reflexivity).
    exact E.
  - rewrite E2. apply rigl_firstn_app_exact. rewrite length_app, !length_le4. reflexivity.
Qed.

Lemma rig_concat_nth : forall (es : list rentry) i, (i < length es)%nat ->
  Forall (fun e => length (entry_bytes e) = 56%nat) es ->
  concat (map entry_bytes es) =
    concat (map entry_bytes (firstn i es)) ++ entry_bytes (nth i es no_entry) ++ concat (map entry_bytes (skipn (S i) es)) /\
  length (concat (map entry_bytes (firstn i es))) = (56 * i)%nat.
Proof.
  intros es i Hi HF. destruct (nth_split es no_entry Hi) as (a & b & E & La).
  set (x := nth i es no_entry) in *. clearbody x. subst es i.
  apply Forall_app in HF. destruct HF as [Ha _].
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  replace (skipn (S (length a)) (a ++ x :: b)) with b.
  2: { rewrite skipn_app, skipn_all2 by lia. replace (S (length a) - length a)%nat with 1%nat by lia. reflexivity. }
  split; [rewrite map_app, concat_app; reflexivity | exact (rigl_concat_len a Ha)].
Qed.

Lemma rig_nodup_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x. induction l1 as [|a l1 IH]; intros H H1 H2; [destruct H1|].
  cbn [app] in H. apply NoDup_cons_iff in H. destruct H as [Hn H].
  destruct H1 as [<-|H1]; [apply Hn, in_or_app; right; exact H2| exact (IH H H1 H2)].
Qed.

Lemma rig_nodup_concat_disj : forall (Xs : list (list Z)) i j x, List.NoDup (concat Xs) ->
  In x (nth i Xs []) -> In x (nth j Xs []) -> i = j.
Proof.
  intros Xs. induction Xs as [|X Xs IH]; intros i j x H Hi Hj.
  - destruct i; cbn in Hi; destruct Hi.
  - cbn [concat] in H. destruct i as [|i], j as [|j]; cbn [nth] in Hi, Hj.
    + reflexivity.
    + exfalso. exact (rig_nodup_app_disj X (concat Xs) x H Hi (rigl_in_nth_concat Xs j x Hj)).
    + exfalso. exact (rig_nodup_app_disj X (concat Xs) x H Hj (rigl_in_nth_concat Xs i x Hi)).
    + f_equal. exact (IH i j x (NoDup_app_remove_l _ _ H) Hi Hj).
Qed.

Lemma rig_nodup_pick : forall (a b : Z) (Xs Ys : list (list Z)) i, (i < length Xs)%nat -> length Ys = length Xs ->
  List.NoDup (a :: b :: concat Xs ++ concat Ys) -> List.NoDup (a :: b :: nth i Xs [] ++ nth i Ys []).
Proof.
  intros a b Xs Ys i Hi HL H.
  rewrite (rigl_concat_split Xs i Hi), (rigl_concat_split Ys i ltac:(lia)) in H.
  set (P1 := concat (firstn i Xs)) in *. set (S1 := concat (skipn (S i) Xs)) in *.
  set (P2 := concat (firstn i Ys)) in *. set (S2 := concat (skipn (S i) Ys)) in *.
  set (X := nth i Xs []) in *. set (Y := nth i Ys []) in *.
  clearbody P1 S1 P2 S2 X Y.
  assert (H1 : List.NoDup ([a; b] ++ X ++ S1 ++ P2 ++ Y ++ S2)).
  { apply (rigl_nodup_mid _ P1). revert H. cbn [app]. rewrite <- !app_assoc. exact (fun h => h). }
  assert (H2 : List.NoDup ((a :: b :: X) ++ Y ++ S2)).
  { apply (rigl_nodup_mid _ (S1 ++ P2)). revert H1. cbn [app]. rewrite <- !app_assoc. exact (fun h => h). }
  apply (NoDup_app_remove_r _ S2). revert H2. cbn [app]. rewrite <- !app_assoc. exact (fun h => h).
Qed.

Lemma rig_le4_inj : forall a b, le4 (Z_to_bv 64 a) = le4 (Z_to_bv 64 b) -> a mod 2 ^ 32 = b mod 2 ^ 32.
Proof.
  intros a b H. apply (f_equal bytes_le_to_Z) in H. rewrite !bytes_le_to_Z_le4, !unsigned_lit_wrap in H.
  rewrite !rigl_mod_mod in H. exact H.
Qed.

Lemma rig_bytes_uniq : forall segs m A bs1 bs2, bytes_at segs m A bs1 -> bytes_at segs m A bs2 ->
  length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros segs m A bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply rigl_nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (length bs1)) as [Hn|Hn].
  - rewrite <- H1 by exact Hn. apply H2. lia.
  - rewrite (proj2 (nth_error_None bs1 n) Hn), (proj2 (nth_error_None bs2 n) ltac:(lia)). reflexivity.
Qed.

Lemma rig_live_step : forall cl br dd T LEN, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T -> 0 <= LEN ->
  let br1 := if send_off cl br T then br else dd in
  (send_live cl br dd T = true -> br1 = 0 /\ send_live cl br1 dd LEN = negb (LEN =? 0) /\ send_live cl br dd (T + LEN) = true) /\
  (send_live cl br dd T = false ->
     send_live cl br1 dd LEN = send_live cl br dd (T + LEN) /\ (send_live cl br dd (T + LEN) = true -> T = 0)).
Proof.
  intros cl br dd T LEN Hcl Hbr Hdd HT HL. cbv zeta. unfold send_live, send_off.
  destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->];
  destruct (Z.eqb_spec T 0) as [ET|ET]; destruct (Z.eqb_spec LEN 0) as [EL|EL];
  destruct (Z.eqb_spec (T + LEN) 0) as [ES|ES];
  cbn; try (exfalso; lia); intuition (try discriminate; try lia).
Qed.

Lemma rig_off_step : forall cl br dd ei T LEN, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T -> 0 <= LEN ->
  let br1 := if send_off cl br T then br else dd in
  let ei1 := if send_off cl br T then ei else 0 in
  (if send_off cl br1 LEN then br1 else dd) = (if send_off cl br (T + LEN) then br else dd) /\
  (if send_off cl br1 LEN then ei1 else 0) = (if send_off cl br (T + LEN) then ei else 0) /\
  (br1 = 0 \/ br1 = 1) /\ ((ei = 0 \/ ei = 1) -> ei1 = 0 \/ ei1 = 1).
Proof.
  intros cl br dd ei T LEN Hcl Hbr Hdd HT HL. cbv zeta. unfold send_off.
  destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->];
  destruct (Z.eqb_spec T 0) as [ET|ET]; destruct (Z.eqb_spec LEN 0) as [EL|EL];
  destruct (Z.eqb_spec (T + LEN) 0) as [ES|ES];
  cbn; try (exfalso; lia); intuition (try discriminate; try lia).
Qed.

Lemma rig_live1 : forall cl br dd T X, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> 0 < X ->
  send_live cl (if send_off cl br T then br else dd) dd X = send_live cl br dd 1.
Proof.
  intros cl br dd T X Hcl Hbr Hdd HX. unfold send_live, send_off.
  destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->];
    destruct (Z.eqb_spec T 0); destruct (Z.eqb_spec X 0); cbn; try lia; reflexivity.
Qed.

Lemma rig_live_pos : forall cl br dd T, 0 < T -> send_live cl br dd T = send_live cl br dd 1.
Proof. intros cl br dd T HT. unfold send_live, send_off. destruct (Z.eqb_spec T 0); [lia|]. reflexivity. Qed.

Lemma rig_live_0 : forall cl br dd, send_live cl br dd 0 = false.
Proof. intros cl br dd. unfold send_live, send_off. destruct (cl <? 0), (br =? 1); reflexivity. Qed.

Lemma rig_wn_app : forall A B, length (with_nul (A ++ B)) = (length (with_nul A) + length (with_nul B))%nat.
Proof. intros A B. unfold with_nul. rewrite map_app, concat_app, length_app. reflexivity. Qed.

Lemma rig_wn_nil : forall L, length (with_nul L) = 0%nat -> L = [].
Proof. intros [|l L] H; [reflexivity|]. rewrite rigl_with_nul_cons in H. lia. Qed.

Lemma rig_skipn_combine : forall {X Y} (l1 : list X) (l2 : list Y) i d1 d2, (i < length l1)%nat ->
  length l2 = length l1 -> skipn i (combine l1 l2) = (nth i l1 d1, nth i l2 d2) :: skipn (S i) (combine l1 l2).
Proof.
  intros X Y l1. induction l1 as [|a l1 IH]; intros [|b l2] i d1 d2 Hi Hl; cbn [length] in Hi, Hl; try lia.
  destruct i as [|i]; [reflexivity|]. cbn [skipn combine nth]. apply IH; lia.
Qed.

(* drain's model (drain_b_c.drain_run): a dead run does not read g_nout and keeps g_capout; the lines it relays are
   the reference lines of the pending stream, so g_nout grows by their bytes, and a run that relays no line does not
   depend on the liveness of its sends. *)
Definition set_no (n : Z) (s : dstate) : dstate :=
  DS (ds_cap s) (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) (ds_eintr s) (ds_pend s) (ds_off s) (ds_ref s) (ds_en s)
     (ds_ecap s) n (ds_ocap s).

Definition dr_rest_of (pd : list (list Z)) (off : Z) : list Z :=
  match pd with [] => [] | r0 :: rs => skipn (Z.to_nat off) r0 ++ concat rs end.

Definition dr_rest (s : dstate) : list Z := dr_rest_of (ds_pend s) (ds_off s).

Definition dr_pend_ok (pd : list (list Z)) (off : Z) : Prop :=
  match pd with
  | [] => True
  | r0 :: rs => 0 <= off < Z.of_nat (length r0) /\ Forall (fun r => (1 <= length r)%nat) rs
  end.

Definition dr_inv (s : dstate) : Prop :=
  J1 (ds_u s) (ds_skip s) (ds_ref s) /\ (ds_cap s = 0 \/ 8192 <= ds_cap s) /\ dr_pend_ok (ds_pend s) (ds_off s).

Lemma rig_ll_val : Z.of_nat LINE_LIMIT = 6000.
Proof. reflexivity. Qed.

Lemma rig_ll_z : forall n, (n <= LINE_LIMIT)%nat -> Z.of_nat n <= 6000.
Proof. intros n H. apply Nat2Z.inj_le in H. rewrite rig_ll_val in H. exact H. Qed.

Lemma rig_ll_nat : forall n, Z.of_nat n <= 6000 -> (n <= LINE_LIMIT)%nat.
Proof. intros n H. apply Nat2Z.inj_le. rewrite rig_ll_val. exact H. Qed.

Lemma rig_lr_false : forall mx ls no cap no' cap' H ka j o ha ks,
  fst (fst (lines_run false mx no cap H ka ls j o ha ks)) = fst (fst (lines_run false mx no' cap' H ka ls j o ha ks)) /\
  snd (snd (fst (lines_run false mx no cap H ka ls j o ha ks))) =
    snd (snd (fst (lines_run false mx no' cap' H ka ls j o ha ks))) /\
  snd (fst (snd (fst (lines_run false mx no cap H ka ls j o ha ks)))) =
    snd (fst (snd (fst (lines_run false mx no' cap' H ka ls j o ha ks)))) /\
  snd (lines_run false mx no cap H ka ls j o ha ks) = snd (lines_run false mx no' cap' H ka ls j o ha ks) /\
  fst (fst (snd (fst (lines_run false mx no cap H ka ls j o ha ks)))) = cap.
Proof.
  intros mx ls. induction ls as [|l r IH]; intros no cap no' cap' H ka j o ha ks; [cbn; repeat split; reflexivity|].
  cbn [lines_run]. unfold send_line_tr, send_line_out, send_line_cap. cbn [fst snd app].
  match goal with |- context [lines_run false mx (no + ?len) cap ?H1 ?ka1 r ?j1 o ?ha1 ?ks1] =>
    destruct (IH (no + len) cap (no' + len) cap' H1 ka1 j1 o ha1 ks1) as (E1 & E2 & E3 & E4 & E5) end.
  rewrite E1. split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4 | exact E5].
Qed.

Lemma rig_grow : forall c used j b, (c = 0 \/ 8192 <= c) -> 0 <= used <= 6000 ->
  8192 <= fst (snd (grow_tr c used j b)) /\ 0 < fst (snd (grow_tr c used j b)) - used.
Proof.
  intros c used j b Hc Hu. unfold grow_tr.
  destruct (Z.ltb_spec (c - used) 4096); cbn [fst snd]; [destruct (Z.eqb_spec c 0)|]; lia.
Qed.

Section DM.

Lemma rig_dr_false : forall f mx s n j a,
  fst (drain_run f false mx (set_no n s) j a) = fst (drain_run f false mx s j a) /\
  set_no 0 (fst (snd (drain_run f false mx (set_no n s) j a))) = set_no 0 (fst (snd (drain_run f false mx s j a))) /\
  snd (snd (drain_run f false mx (set_no n s) j a)) = snd (snd (drain_run f false mx s j a)) /\
  ds_ocap (fst (snd (drain_run f false mx s j a))) = ds_ocap s.
Proof.
  induction f as [|f IH]; intros mx [c u sk H ka ei pd off rf en ec no oc] n j a; [repeat split; reflexivity|].
  unfold set_no.
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap].
  destruct ei.
  - match goal with |- context [drain_run f false mx (DS ?a1 ?b1 ?c1 ?d1 ?e1 ?g1 ?h1 ?i1 ?k1 ?l1 ?m1 n ?o1) ?jj ?aa] =>
      destruct (IH mx (DS a1 b1 c1 d1 e1 g1 h1 i1 k1 l1 m1 no o1) n jj aa) as (E1 & E2 & E3 & E4) end.
    unfold set_no in E1, E2, E3.
    cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap] in E1, E2, E3, E4.
    cbn [fst snd]. rewrite E1. split; [reflexivity|]. split; [exact E2|]. split; [exact E3 | exact E4].
  - destruct pd as [|r0 rs]; [repeat split; reflexivity|].
    match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end;
      [repeat split; reflexivity|].
    match goal with |- context [chunk u sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false mx n oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
      pose proof (rig_lr_false mx rl n oc no oc H ka j3 o3 h3 k3) as (L1 & L2 & L3 & L4 & L5);
      pose proof (rig_lr_false mx rl no oc no oc H ka j3 o3 h3 k3) as (_ & _ & _ & _ & L6);
      destruct (lines_run false mx n oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] eqn:ELR1;
      destruct (lines_run false mx no oc H ka rl j3 o3 h3 k3) as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]] eqn:ELR2
    end.
    cbn [fst snd] in L1, L2, L3, L4, L5, L6. injection L4 as <- <- <-.
    subst t1 H1 ka1 oc1 oc2. cbn [fst snd].
    match goal with |- context [drain_run f false mx (DS ?a1 ?b1 ?c1 ?d1 ?e1 ?g1 ?h1 ?i1 ?k1 ?l1 ?m1 (n + ?mm) ?o1) ?jj ?aa] =>
      destruct (IH mx (DS a1 b1 c1 d1 e1 g1 h1 i1 k1 l1 m1 (no + mm) o1) (n + mm) jj aa) as (E1 & E2 & E3 & E4) end.
    unfold set_no in E1, E2, E3.
    cbn [ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap] in E1, E2, E3, E4.
    rewrite E1. split; [reflexivity|]. split; [exact E2|]. split; [exact E3 | exact E4].
Qed.

Lemma rig_dr_lines : forall f live mx s j a, dr_inv s ->
  (length (dr_rest s) + (if ds_eintr s then 2 else 1) <= f)%nat ->
  ds_no (fst (snd (drain_run f live mx s j a))) =
    ds_no s + Z.of_nat (length (with_nul (lines (ds_ref s) (dr_rest s)))) /\
  (lines (ds_ref s) (dr_rest s) = [] -> forall live', drain_run f live' mx s j a = drain_run f live mx s j a).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV FU;
    [destruct ei; cbn [ds_eintr] in FU; lia|].
  unfold dr_inv in INV. unfold dr_rest in FU |- *.
  cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off ds_eintr ds_no] in INV, FU |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by (clear - UL'; lia).
  pose proof (rig_grow c (Z.of_nat (length u)) j (da_buf a) HC UL'') as [G1 G2].
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap].
  set (cp := fst (snd (grow_tr c (Z.of_nat (length u)) j (da_buf a)))) in *.
  destruct ei; cbv beta iota in FU.
  - assert (IV : dr_inv (DS cp u sk H ka false pd off rf en ec no oc)).
    { unfold dr_inv. cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off]. split; [exact J|]. split; [lia | exact HP]. }
    assert (FU1 : (length (dr_rest (DS cp u sk H ka false pd off rf en ec no oc)) +
                   (if ds_eintr (DS cp u sk H ka false pd off rf en ec no oc) then 2 else 1) <= f)%nat).
    { unfold dr_rest. cbn [ds_pend ds_off ds_eintr]. lia. }
    match goal with |- context [drain_run f live mx (DS cp u sk H ka false pd off rf en ec no oc) ?jj ?aa] =>
      destruct (IH live mx _ jj aa IV FU1) as [E1 E2] end.
    unfold dr_rest in E1, E2. cbn [ds_pend ds_off ds_ref ds_no] in E1, E2. cbn [fst snd].
    split; [exact E1|]. intros Hl live'. rewrite (E2 Hl live'). reflexivity.
  - destruct pd as [|r0 rs].
    + cbn [dr_rest_of]. rewrite lines_nil. split; [cbn; lia | intros _ live'; reflexivity].
    + destruct HP as [HO HF].
      match goal with |- context [Z.min ?a ?b <=? 0] => remember (Z.min a b) as nn eqn:Enn end.
      assert (NP : 0 < nn) by (rewrite Enn; lia).
      assert (NL : nn <= Z.of_nat (length r0) - off) by (rewrite Enn; lia).
      destruct (Z.leb_spec nn 0) as [X|X]; [lia|]. clear X.
      set (d := firstn (Z.to_nat nn) (skipn (Z.to_nat off) r0)) in *.
      pose proof (chunk_ok u sk rf d J) as CK.
      destruct (chunk u sk d) as [[u' sk'] rl] eqn:ECH.
      destruct CK as [Erl J'].
      set (PEND := if off + nn =? Z.of_nat (length r0) then rs else r0 :: rs) in *.
      set (OFF := if off + nn =? Z.of_nat (length r0) then 0 else off + nn) in *.
      assert (RS : dr_rest_of (r0 :: rs) off = d ++ dr_rest_of PEND OFF /\ dr_pend_ok PEND OFF).
      { unfold PEND, OFF, d. cbn [dr_rest_of].
        destruct (Z.eqb_spec (off + nn) (Z.of_nat (length r0))) as [W|W].
        - split.
          + rewrite firstn_all2 by (rewrite length_skipn; lia). f_equal.
            destruct rs as [|r1 rs1]; reflexivity.
          + destruct rs as [|r1 rs1]; [exact I|]. inversion HF as [|? ? HF1 HF2]; subst. cbn [dr_pend_ok].
            split; [lia | exact HF2].
        - split.
          + cbn [dr_rest_of]. replace (Z.to_nat (off + nn)) with (Z.to_nat nn + Z.to_nat off)%nat by lia.
            rewrite <- skipn_skipn, app_assoc, firstn_skipn. reflexivity.
          + cbn [dr_pend_ok]. split; [lia | exact HF]. }
      destruct RS as [RS1 RS2].
      assert (DL : length d = Z.to_nat nn)
        by (unfold d; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
      assert (IVG : forall H' ka' en' ec' no' oc',
                 dr_inv (DS cp u' sk' H' ka' false PEND OFF (feed rf d) en' ec' no' oc')).
      { intros. unfold dr_inv. cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off].
        split; [exact J'|]. split; [lia | exact RS2]. }
      assert (FUG : forall H' ka' en' ec' no' oc',
                 (length (dr_rest (DS cp u' sk' H' ka' false PEND OFF (feed rf d) en' ec' no' oc')) +
                  (if ds_eintr (DS cp u' sk' H' ka' false PEND OFF (feed rf d) en' ec' no' oc') then 2 else 1)
                  <= f)%nat).
      { intros. unfold dr_rest. cbn [ds_pend ds_off ds_eintr]. rewrite RS1, length_app in FU. lia. }
      split.
      * match goal with |- context [lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
          destruct (lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
        cbn [fst snd].
        match goal with |- context [drain_run f live mx (DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
          destruct (IH live mx _ jj aa (IVG H1 ka1 en' ec' no' oc1) (FUG H1 ka1 en' ec' no' oc1)) as [E1 _] end.
        rewrite E1. unfold dr_rest. cbn [ds_no ds_pend ds_off ds_ref].
        rewrite RS1, lines_app, rig_wn_app, <- Erl. lia.
      * intros Hl live'. rewrite RS1, lines_app in Hl. apply app_eq_nil in Hl as [Hl1 Hl2].
        rewrite <- Erl in Hl1. clear Erl. subst rl. cbn [lines_run fst snd].
        match goal with |- context [drain_run f live mx (DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
          destruct (IH live mx _ jj aa (IVG H ka en' ec' no' oc) (FUG H ka en' ec' no' oc)) as [_ E2] end.
        rewrite (E2 Hl2 live'). reflexivity.
Qed.

Lemma rig_drain_model : forall live mx NO CAP e h,
  dr_inv (drain_init NO CAP e h) -> dr_rest (drain_init NO CAP e h) = bzs (pending_stream h) ->
  ds_no (drain_fin live mx NO CAP e h) =
    NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) /\
  (lines (hs_state h) (bzs (pending_stream h)) = [] -> forall live' j a,
     drain_go live' mx NO CAP e h j a = drain_go live mx NO CAP e h j a).
Proof.
  intros live mx NO CAP e h IV ER.
  assert (FU : (length (dr_rest (drain_init NO CAP e h)) + (if ds_eintr (drain_init NO CAP e h) then 2 else 1)
                <= S (S (length (pending_stream h))))%nat).
  { rewrite ER. unfold bzs. rewrite length_map. destruct (ds_eintr _); lia. }
  split.
  - destruct (rig_dr_lines (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0 dadr0 IV FU)
      as [E1 _].
    rewrite ER in E1.
    change (ds_ref (drain_init NO CAP e h)) with (hs_state h) in E1.
    change (ds_no (drain_init NO CAP e h)) with NO in E1.
    unfold drain_fin, drain_go. exact E1.
  - intros Hl live' j a.
    destruct (rig_dr_lines (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) j a IV FU)
      as [_ E2].
    rewrite ER in E2. change (ds_ref (drain_init NO CAP e h)) with (hs_state h) in E2.
    unfold drain_go. exact (E2 Hl live').
Qed.

Lemma rig_drain_false : forall mx NO NO' CAP e h j a,
  drain_tr false mx NO' CAP e h j a = drain_tr false mx NO CAP e h j a /\
  set_no 0 (drain_fin false mx NO' CAP e h) = set_no 0 (drain_fin false mx NO CAP e h) /\
  drain_adr false mx NO' CAP e h j a = drain_adr false mx NO CAP e h j a /\
  ds_ocap (drain_fin false mx NO CAP e h) = CAP.
Proof.
  intros mx NO NO' CAP e h j a. unfold drain_tr, drain_fin, drain_adr, drain_go.
  destruct (rig_dr_false (S (S (length (pending_stream h)))) mx (drain_init NO CAP e h) NO' j a) as (E1 & _ & E3 & _).
  destruct (rig_dr_false (S (S (length (pending_stream h)))) mx (drain_init NO CAP e h) NO' 0 dadr0)
    as (_ & E2 & _ & E4).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3 | exact E4].
Qed.

Lemma rig_gone_run_cons : forall lv mx no cap pre e hj r nm j o,
  gone_run lv mx no cap pre ((e, hj) :: r) nm j o =
  let s := after_drain lv mx no cap e (fst hj) in
  let a0 := drain_start nm o e (fst hj) in
  let td := if re_eof e =? 0 then drain_tr lv mx no cap e (fst hj) j a0 else [] in
  let a := after_drain_adr lv mx no cap e (fst hj) j a0 in
  let gk := geia pre (combine (ds_H s) (da_keys a)) in
  let xks := map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst gk) in
  let k := keys_end_run lv mx (ds_no s) (ds_ocap s) xks (j + nretF td) (da_out a) in
  let r' := gone_run lv mx (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks)) (fst (snd k)) pre r nm
              (j + nretF td + nretF (fst k)) (snd (snd k)) in
  (td ++ fst k ++ fst (fst (fst r')), snd (fst (fst r')), s :: snd (fst r'),
   (fst (snd r'), DA (snd (snd k)) (da_buf a) (da_hp a) (map snd (snd gk)) (da_pend a) (da_ev a) (da_erecs a)
                    :: snd (snd r'))).
Proof.
  intros lv mx no cap pre e hj r nm j o. cbn [gone_run].
  match goal with |- context [gone_run ?a ?b ?c ?d ?g r nm ?jj ?oo] =>
    destruct (gone_run a b c d g r nm jj oo) as [[[t0 c0] ss] [o' das]] end.
  reflexivity.
Qed.
End DM.

Lemma rig_dinit : forall NO CAP e h,
  (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  Z.of_nat (length (re_U e)) <= 6000 -> ~ In (Z_to_bv 8 0) (re_U e) -> (re_cap e = 0 \/ 8192 <= re_cap e) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)) ->
  dr_inv (drain_init NO CAP e h) /\ dr_rest (drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
  intros NO CAP e h SK E SU UL UZ UC PD PF.
  unfold dr_inv, dr_rest, drain_init. cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off].
  split; [split; [|split]|].
  - unfold J1, hs_state. cbn [ls_k ls_w]. rewrite <- E.
    split; [reflexivity|]. split.
    + intros X. destruct SK as [S0|S1]; [exact (SU S0)|]. rewrite S1 in X. discriminate X.
    + split; [unfold bzs; rewrite length_map; exact (rig_ll_nat _ UL)|].
      unfold nozero, bzs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (x & <- & Hx).
      intros X. apply UZ. replace (Z_to_bv 8 0) with x; [exact Hx|].
      apply bv_eq. unfold bz in X. rewrite X. vm_compute. reflexivity.
  - exact UC.
  - destruct PD as [(E1 & E2)|(r & rs & E1 & E2)]; rewrite E1; cbn [map dr_pend_ok]; [exact I|].
    rewrite E1 in PF. inversion PF as [|? ? PF1 PF2]; subst.
    split; [unfold bzs; rewrite length_map; exact E2|].
    apply Forall_map. eapply Forall_impl; [|exact PF2]. intros x Hx. cbv beta. unfold bzs. rewrite length_map.
    exact Hx.
  - unfold pending_stream. destruct PD as [(E1 & E2)|(r & rs & E1 & E2)]; rewrite E1; cbn [map dr_rest_of];
      [reflexivity|].
    unfold bzs. rewrite map_app, skipn_map, concat_map, map_map. reflexivity.
Qed.
