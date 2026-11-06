From Stdlib Require Import ZArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandTac check_reply_c strcmp_c strcspn_c strncmp_c bcmp_c check_arity_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ca_hd_skipn_S : forall (l : list byte) k, (k < length l)%nat -> skipn k l = hd NUL (skipn k l) :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma ca_hd_skipn_end : forall (l : list byte) k, (length l <= k)%nat -> hd NUL (skipn k l) = NUL.
Proof. intros l k H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma ca_hd_nz_lt : forall (l : list byte) k, bv_unsigned (hd NUL (skipn k l)) <> 0 -> (k < length l)%nat.
Proof.
  intros l k H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  rewrite ca_hd_skipn_end in H by exact L. exfalso. apply H. reflexivity.
Qed.

Lemma ca_hd_in : forall (l : list byte) k, (k < length l)%nat -> In (hd NUL (skipn k l)) l.
Proof.
  induction l as [|x l IH]; intros [|k] H; cbn in *; try lia.
  - left. reflexivity.
  - right. apply IH. lia.
Qed.

Lemma ca_hd_z_end : forall (l : list byte) k, ~ In NUL l -> (k <= length l)%nat ->
  bv_unsigned (hd NUL (skipn k l)) = 0 -> k = length l.
Proof.
  intros l k Hn Hk H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [|lia].
  exfalso. apply Hn. replace NUL with (hd NUL (skipn k l)); [apply ca_hd_in; exact L|].
  apply bv_eq. rewrite H. reflexivity.
Qed.

Lemma ca_hd_nz : forall (l : list byte) k, ~ In NUL l -> (k < length l)%nat -> bv_unsigned (hd NUL (skipn k l)) <> 0.
Proof. intros l k Hn Hk H. pose proof (ca_hd_z_end l k Hn ltac:(lia) H). lia. Qed.

Lemma ca_rd_hd : forall m A (l : list byte) k, bytes_at rsegs m A (l ++ [NUL]) -> (k <= length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [hd NUL (skipn k l)].
Proof.
  intros m A l k H Hk.
  rewrite (bytes_at_read rsegs m A (l ++ [NUL]) (Z.of_nat k) 1 H) by (try rewrite Nat2Z.id; try rewrite length_app; cbn [length]; lia).
  rewrite Nat2Z.id, skipn_app. replace (k - length l)%nat with 0%nat by lia. cbn [skipn].
  destruct (skipn k l) as [|b t]; reflexivity.
Qed.

Lemma ca_skip_sp_at : forall (l : list byte) k, (k <= length l)%nat ->
  skip_sp (skipn k l) = if bz (hd NUL (skipn k l)) =? 32 then skip_sp (skipn (S k) l) else skipn k l.
Proof.
  intros l k Hk. destruct (Nat.lt_ge_cases k (length l)) as [L|L].
  - rewrite (ca_hd_skipn_S l k L). cbn [skip_sp hd]. reflexivity.
  - rewrite (skipn_all2 l L). reflexivity.
Qed.

Definition ca_dstep (d : Z) (b : byte) : Z :=
  if (bz b =? 60) || (bz b =? 91) then d + 1
  else if ((bz b =? 62) || (bz b =? 93)) && (0 <? d) then d - 1 else d.

Definition ilen (d : Z) (s : list byte) : nat := length (fst (item_scan d s)).

Lemma ilen_cons : forall d b s,
  ilen d (b :: s) = if (d =? 0) && (bz b =? 32) then 0%nat else S (ilen (ca_dstep d b) s).
Proof.
  intros d b s. unfold ilen, ca_dstep. cbn [item_scan].
  destruct ((d =? 0) && (bz b =? 32)); [reflexivity|].
  destruct (item_scan _ s); reflexivity.
Qed.

Lemma ilen_nil : forall d, ilen d [] = 0%nat.
Proof. reflexivity. Qed.

Lemma ca_item_scan_app : forall s d it rest, item_scan d s = (it, rest) -> it ++ rest = s.
Proof.
  induction s as [|b s IH]; intros d it rest H; cbn [item_scan] in H.
  - injection H as <- <-. reflexivity.
  - destruct ((d =? 0) && (bz b =? 32)).
    + injection H as <- <-. reflexivity.
    + destruct (item_scan _ s) as [it' rest'] eqn:E. injection H as <- <-. cbn [app]. f_equal. eapply IH. exact E.
Qed.

Lemma ca_item_scan_fst : forall d s, fst (item_scan d s) = firstn (ilen d s) s.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst].
  rewrite <- (ca_item_scan_app s d it rest E). rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma ca_item_scan_snd : forall d s, snd (item_scan d s) = skipn (ilen d s) s.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst snd].
  rewrite <- (ca_item_scan_app s d it rest E). rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity.
Qed.

Lemma ilen_le : forall d s, (ilen d s <= length s)%nat.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst].
  rewrite <- (ca_item_scan_app s d it rest E). rewrite length_app. lia.
Qed.

Lemma ilen_pos : forall s, bv_unsigned (hd NUL s) <> 32 -> s <> [] -> (1 <= ilen 0 s)%nat.
Proof.
  intros [|b s] H1 H2; [congruence|]. rewrite ilen_cons. cbn [hd] in H1. unfold bz.
  rewrite (proj2 (Z.eqb_neq _ 32) H1), andb_false_r. lia.
Qed.

Lemma ilen_end : forall s d, skipn (ilen d s) s = [] \/ bz (hd NUL (skipn (ilen d s) s)) = 32.
Proof.
  induction s as [|b s IH]; intros d; [left; reflexivity|].
  rewrite ilen_cons. destruct ((d =? 0) && (bz b =? 32)) eqn:E.
  - right. cbn [skipn hd]. apply andb_true_iff in E. destruct E as [_ E]. apply Z.eqb_eq in E. exact E.
  - cbn [skipn]. apply IH.
Qed.

Lemma items_f_nil : forall f s, skip_sp s = [] -> items_f f s = [].
Proof. intros [|f] s H; cbn [items_f]; [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma items_f_cons : forall f s s1, skip_sp s = s1 -> s1 <> [] ->
  items_f (S f) s = fst (item_scan 0 s1) :: items_f f (snd (item_scan 0 s1)).
Proof.
  intros f s s1 E N. cbn [items_f]. rewrite E. destruct s1 as [|b t]; [congruence|].
  cbn beta iota. destruct (item_scan 0 (b :: t)); reflexivity.
Qed.

Lemma items_f_step : forall f (l : list byte) k k1, skipn k1 l = skip_sp (skipn k l) -> (k1 < length l)%nat ->
  items_f (S f) (skipn k l) = firstn (ilen 0 (skipn k1 l)) (skipn k1 l) :: items_f f (skipn (k1 + ilen 0 (skipn k1 l)) l).
Proof.
  intros f l k k1 E L.
  rewrite (items_f_cons f (skipn k l) (skipn k1 l)).
  - rewrite ca_item_scan_fst, ca_item_scan_snd, skipn_skipn.
    replace (ilen 0 (skipn k1 l) + k1)%nat with (k1 + ilen 0 (skipn k1 l))%nat by lia. reflexivity.
  - symmetry. exact E.
  - intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia.
Qed.

Lemma ca_memcmp_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ (v = 0 <-> firstn n l = firstn n r).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; intros; reflexivity.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. cbn [memcmp_model firstn].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(lia) ltac:(lia)) as (v & Hv & Hv0). exists v. split; [exact Hv|].
      rewrite Hv0. replace b with a by (apply bv_eq; exact E).
      split; [intros ->; reflexivity | intros H; injection H as H; exact H].
    + eexists. split; [reflexivity|]. split; [intros H; lia | intros H; injection H as H1 _; subst; lia].
Qed.

Lemma ca_bytes_eqb_len : forall a b, length a <> length b -> bytes_eqb a b = false.
Proof.
  intros a b H. destruct (bytes_eqb a b) eqn:E; [|reflexivity].
  apply bytes_eqb_iff in E. subst. congruence.
Qed.

Lemma ca_swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. replace (bv_half_modulus 32) with (2^31) by reflexivity. lia. Qed.

Lemma ca_pos_false : forall d, (0 <? d) && (d <? 9223372036854775808) = false -> d < 9223372036854775808 -> d <= 0.
Proof.
  intros d H1 H2. destruct (Z.ltb_spec 0 d) as [L|L]; [|lia].
  destruct (Z.ltb_spec d 9223372036854775808); [discriminate | lia].
Qed.

Ltac pos_false_tac :=
  match goal with H : (0 <? _) && (_ <? 9223372036854775808) = false |- _ => apply ca_pos_false in H; [|lia] end.

Lemma dstep_open : forall d b, bv_unsigned b = 60 \/ bv_unsigned b = 91 -> ca_dstep d b = d + 1.
Proof. intros d b [H|H]; unfold ca_dstep, bz; rewrite H; reflexivity. Qed.

Lemma dstep_close : forall d b, bv_unsigned b = 62 \/ bv_unsigned b = 93 -> 0 < d -> bv_unsigned b <> 60 -> bv_unsigned b <> 91 ->
  ca_dstep d b = d - 1.
Proof.
  intros d b H Hd H60 H91. unfold ca_dstep, bz.
  rewrite (proj2 (Z.eqb_neq _ _) H60), (proj2 (Z.eqb_neq _ _) H91). cbn [orb].
  rewrite (proj2 (Z.ltb_lt _ _) Hd). destruct H as [H|H]; rewrite H; reflexivity.
Qed.

Lemma dstep_same : forall d b, bv_unsigned b <> 60 -> bv_unsigned b <> 91 ->
  (bv_unsigned b <> 62 /\ bv_unsigned b <> 93) \/ d <= 0 -> ca_dstep d b = d.
Proof.
  intros d b H60 H91 H. unfold ca_dstep, bz.
  rewrite (proj2 (Z.eqb_neq _ _) H60), (proj2 (Z.eqb_neq _ _) H91). cbn [orb].
  destruct H as [[H1 H2]|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) H), andb_false_r. reflexivity.
Qed.

Lemma ca_memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r vv Hm.
  - cbn in Hm. injection Hm as <-. lia.
  - destruct l as [|a l]; [cbn in Hm; discriminate|]. destruct r as [|b r]; [cbn in Hm; discriminate|].
    cbn [memcmp_model] in Hm.
    destruct (bv_unsigned a =? bv_unsigned b); [eapply IH; exact Hm|].
    injection Hm as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

Lemma rw_c8_cb : forall m Aa x cs, rw_cells rsegs m Aa (C8 x :: cs) -> rw_cells rsegs m Aa (CB 8 (le8 x) :: cs).
Proof.
  intros m Aa x cs H. pose proof (rw_cells_merge rsegs m Aa [] [C8 x] cs H) as M.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

Lemma bar_iff : forall (l : list byte) L, (1 <= L <= length l)%nat ->
  bytes_eqb (firstn L l) (str [124]) = Nat.eqb L 1 && (bz (hd NUL l) =? 124).
Proof.
  intros [|b l] L HL; cbn [length] in HL; [lia|].
  destruct L as [|[|L]]; [lia| |].
  - change (firstn 1 (b :: l)) with [b]. cbn [hd Nat.eqb andb]. unfold bytes_eqb, str, bz. cbn [map].
    change (bv_unsigned (Z_to_bv 8 124)) with 124.
    destruct (list_eq_dec Z.eq_dec [bv_unsigned b] [124]) as [E|E].
    + injection E as E. rewrite E. reflexivity.
    + destruct (Z.eqb_spec (bv_unsigned b) 124) as [E'|E']; [exfalso; apply E; rewrite E'; reflexivity | reflexivity].
  - rewrite ca_bytes_eqb_len; [reflexivity|]. rewrite length_firstn. unfold str. cbn [length map]. lia.
Qed.

Lemma last_firstn_hd : forall (l : list byte) L d, (1 <= L <= length l)%nat -> last (firstn L l) d = hd NUL (skipn (L - 1) l).
Proof.
  induction l as [|b l IH]; intros L d HL; cbn [length] in HL; [lia|].
  destruct L as [|[|L]]; [lia | reflexivity |].
  destruct l as [|c l']; [cbn [length] in HL; lia|].
  transitivity (last (firstn (S L) (c :: l')) d); [reflexivity|].
  rewrite IH by (cbn [length] in *; lia).
  replace (S (S L) - 1)%nat with (S L) by lia. replace (S L - 1)%nat with L by lia. reflexivity.
Qed.

Lemma bracketed_iff : forall (l : list byte) L, (1 <= L <= length l)%nat ->
  bracketed (firstn L l) = (bz (hd NUL l) =? 91) && (bz (hd NUL (skipn (L - 1) l)) =? 93).
Proof.
  intros [|b l] L HL; cbn [length] in HL; [lia|].
  destruct L as [|L]; [lia|].
  rewrite <- (last_firstn_hd (b :: l) (S L) b) by (cbn [length]; lia). reflexivity.
Qed.

Lemma has_dots_window : forall l, (3 <= length l)%nat ->
  has_dots l = bytes_eqb (firstn 3 l) (str [46; 46; 46]) || has_dots (tl l).
Proof.
  intros [|a [|b [|c r]]] H; cbn [length] in H; try lia.
  change (has_dots (a :: b :: c :: r)) with ((bz a =? 46) && (bz b =? 46) && (bz c =? 46) || has_dots (b :: c :: r)).
  change (firstn 3 (a :: b :: c :: r)) with [a; b; c]. change (tl (a :: b :: c :: r)) with (b :: c :: r).
  replace (bytes_eqb [a; b; c] (str [46; 46; 46])) with ((bz a =? 46) && (bz b =? 46) && (bz c =? 46)); [reflexivity|].
  unfold bytes_eqb, str, bz. cbn [map]. change (bv_unsigned (Z_to_bv 8 46)) with 46.
  destruct (list_eq_dec Z.eq_dec [bv_unsigned a; bv_unsigned b; bv_unsigned c] [46; 46; 46]) as [E|E].
  - injection E as E1 E2 E3. rewrite E1, E2, E3. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned a) 46), (Z.eqb_spec (bv_unsigned b) 46), (Z.eqb_spec (bv_unsigned c) 46);
      try reflexivity. exfalso. apply E. congruence.
Qed.

Lemma has_dots_short : forall l, (length l < 3)%nat -> has_dots l = false.
Proof. intros [|a [|b [|c r]]] H; cbn [length] in H; try lia; reflexivity. Qed.

Lemma skipn_S_tl : forall (l : list byte) i, skipn (S i) l = tl (skipn i l).
Proof. induction l as [|a l IH]; intros [|i]; cbn [skipn tl]; try reflexivity. apply IH. Qed.

Lemma win3 : forall (l : list byte) p i L, (i + 3 <= L)%nat -> (p + L <= length l)%nat ->
  firstn 3 (skipn i (firstn L (skipn p l))) = firstn 3 (skipn (p + i) (l ++ [NUL])) /\
  (3 <= length (skipn i (firstn L (skipn p l))))%nat.
Proof.
  intros l p i L H1 H2. rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  replace (i + p)%nat with (p + i)%nat by lia. split.
  - replace (Nat.min 3 (L - i)) with 3%nat by lia. rewrite skipn_app.
    replace (p + i - length l)%nat with 0%nat by lia. cbn [skipn]. rewrite firstn_app, length_skipn.
    replace (3 - (length l - (p + i)))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Ltac ainv_tac := refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); eassumption.

Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

Lemma ca_sx32_small : forall n, 0 <= n < 2^31 -> sx32 (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof.
  intros n Hn. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ca_signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2^63)); lia. Qed.

Section Syn.
  Variables (sp gp tp r1 : word) (F : bvmap 5 word) (fc : bv 32) (A : Z) (SS : list byte).
  Hypothesis HSn : ~ In NUL SS.
  Hypothesis LSS : Z.of_nat (length SS) <= 128.
  Hypothesis BA : 0 <= A /\ A + Z.of_nat (length SS) + 1 <= 2^63.

  Notation SB pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 32) r1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation SA pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m :=
    (SB pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 124) (Z_to_bv 64 3) (Z_to_bv 64 (-2147483648)) (Z_to_bv 64 2147483647)
        xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m).
  Notation SG pc xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 xs0 r1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma skipA : forall n k m xra xt0 xt1 xt2 xa1 xa2 xa3 xs2 xs3 xs4 xs10 xs11 xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = SA 0x14704 xra xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat k')) (zxb (hd NUL (skipn k' SS))) xa2 xa3
                          xs2 xs3 xs4 (Z_to_bv 64 (A + Z.of_nat k')) xs10 xs11 xt3 xt4 xt5 xt6 m)
      (SA 0x146f0 xra xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat k)) xa1 xa2 xa3 xs2 xs3 xs4 (Z_to_bv 64 (A + Z.of_nat k))
          xs10 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xt0 xt1 xt2 xa1 xa2 xa3 xs2 xs3 xs4 xs10 xs11 xt3 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof (ca_rd_hd m A SS k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS k ltac:(lia)) as LT.
      zstep. zstep. zstep.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma scanB : forall n q d m xra xt0 xt1 xt2 xa0 xa1 xs2 xs3 xs9 xs10 xs11 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya2 ya3, bv_unsigned ya2 = bz (hd NUL (skipn (q + ilen d (skipn q SS)) SS)) /\
                 ms' = SA 0x1475c xra xt0 xt1 xt2 xa0 xa1 ya2 ya3 xs2 xs3
                          (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)
      (SA 0x14714 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d) (zxb (hd NUL (skipn q SS))) xs2 xs3 (Z_to_bv 64 (A + Z.of_nat q))
          xs9 xs10 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xt0 xt1 xt2 xa0 xa1 xs2 xs3 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d', 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SA 0x14744 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d') (zxb (hd NUL (skipn q SS))) xs2 xs3
                          (Z_to_bv 64 (A + Z.of_nat q)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)).
    { intros d' HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya2 & ya3 & Hy & E). subst ms'. unfold POSTQ. exists ya2, ya3.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        split; [exact Hy | reflexivity].
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. zstep. apply evt_done. unfold POSTQ.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia.
        exists (Z_to_bv 64 0). eexists. rewrite IL.
        split; [rewrite (skipn_all2 SS (n := (q + 1)%nat)) by lia; reflexivity | reflexivity]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SA 0x1471c xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d) (zxb (hd NUL (skipn q SS))) xs2 xs3
                          (Z_to_bv 64 (A + Z.of_nat q)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. zstep. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. zstep. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. exists (Z_to_bv 64 32). eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. split; [unfold bz; rewrite Hc8; reflexivity | reflexivity].
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Lemma skipC : forall n k m xra xt0 xt1 xt2 xa0 xa2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k < length SS)%nat -> bz (hd NUL (skipn k SS)) = 32 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k < k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = SA 0x1477c xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (A + Z.of_nat k')) (zxb (hd NUL (skipn k' SS))) xa3
                          xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)
      (SA 0x14770 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (A + Z.of_nat k)) xa2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xt0 xt1 xt2 xa0 xa2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HN HK H32 HB; [lia|].
    pose proof (ca_rd_hd m A SS (S k) HB ltac:(lia)) as RD.
    pose proof (byte_range (hd NUL (skipn (S k) SS))) as BR.
    assert (SK : skip_sp (skipn k SS) = skip_sp (skipn (S k) SS)).
    { rewrite (ca_skip_sp_at SS k ltac:(lia)), (proj2 (Z.eqb_eq _ 32) H32). reflexivity. }
    zstep. zstep. zstep. if_cases C.
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS (S k) ltac:(lia)) as LT.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact C | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, SK. reflexivity.
      + split; [exact Hb | exact E].
    - zify_cond C. apply evt_done. exists (S k). split; [|split].
      + lia.
      + rewrite SK. destruct (Nat.lt_ge_cases (S k) (length SS)) as [L|L].
        * rewrite (ca_skip_sp_at SS (S k) ltac:(lia)), (proj2 (Z.eqb_neq (bz (hd NUL (skipn (S k) SS))) 32) C). reflexivity.
        * rewrite (skipn_all2 SS L). reflexivity.
      + split; [exact C|]. replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia. reflexivity.
  Qed.

  Lemma scanD : forall n q d m xra xt0 xt1 xt2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya0 ya1 ya2,
                 ms' = SA 0x146e8 xra xt0 xt1 xt2 ya0 ya1 ya2 xa3 xs2 xs3
                          (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)
      (SA 0x14784 xra xt0 xt1 xt2 (Z_to_bv 64 d) (Z_to_bv 64 (A + Z.of_nat q)) (zxb (hd NUL (skipn q SS))) xa3 xs2 xs3 xs4
          xs9 xs10 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xt0 xt1 xt2 xa3 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d', 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SA 0x147b8 xra xt0 xt1 xt2 (Z_to_bv 64 d') (Z_to_bv 64 (A + Z.of_nat q)) (zxb (hd NUL (skipn q SS)))
                          xa3 xs2 xs3 (Z_to_bv 64 (A + Z.of_nat q)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)).
    { intros d' HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya0 & ya1 & ya2 & E). subst ms'. unfold POSTQ. exists ya0, ya1, ya2.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SA 0x14790 xra xt0 xt1 xt2 (Z_to_bv 64 d) (Z_to_bv 64 (A + Z.of_nat q)) (zxb (hd NUL (skipn q SS)))
                          xa3 xs2 xs3 (Z_to_bv 64 (A + Z.of_nat q)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. zstep. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. zstep. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    zstep. zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Variables (m0 : word -> option byte) (lo : Z) (saved : list cell).
  Hypothesis AL : A + Z.of_nat (length SS) + 1 <= lo.
  Hypothesis LO : 0 <= lo /\ lo + 112 <= bv_unsigned sp.
  Hypothesis BC : bcmp_contract.

  Definition ainv (c0 : cell) (m : word -> option byte) : Prop :=
    mem_inv rsegs m /\ rw_cells rsegs m (bv_unsigned sp + -112) (c0 :: saved) /\ stk rsegs m lo (bv_unsigned sp + -112) /\
    munch [(lo, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\ bytes_at rsegs m A (SS ++ [NUL]).

  Definition dpost (hb : bool) (xs2 xs3 xs4 xs9 xs10 : word) (ms' : machine_state) : Prop :=
    exists m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      ainv (C8 (Z_to_bv 64 2147483647)) m' /\
      ((hb = true /\ ms' = SB 0x1484c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m') \/
       (hb = false /\ ms' = SB 0x14810 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m')).

  Lemma dots_loop : forall n i p L hb m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6,
    (L - i < n)%nat -> (i + 3 <= L)%nat -> (p + L <= length SS)%nat ->
    has_dots (skipn i (firstn L (skipn p SS))) = hb -> ainv (C8 (Z_to_bv 64 2147483647)) m ->
    evt rsegs (dpost hb xs2 xs3 xs4 (Z_to_bv 64 (A + Z.of_nat p)) (Z_to_bv 64 (Z.of_nat L)))
      (SB 0x147ec xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (A + Z.of_nat p))
          (Z_to_bv 64 (Z.of_nat L)) (Z_to_bv 64 (Z.of_nat i + 3)) xt3 xt4 xt5 xt6 m).
  Proof.
    pose proof BC as BC'. unfold bcmp_contract in BC'.
    induction n as [|n IH]; intros i p L hb m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6
      HN HI HP HH INV; [lia|].
    destruct INV as (MI & FR & ST & MU & WM & HB).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    destruct (win3 SS p i L HI HP) as [W3 L3].
    rewrite (has_dots_window _ L3), <- skipn_S_tl, W3 in HH.
    pose proof (lit_at m 67124 (str [46; 46; 46] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HD.
    destruct (ca_memcmp_eq 3 (skipn (p + i) (SS ++ [NUL])) (str [46; 46; 46] ++ [NUL])) as (vv & Hv & Hv0);
      [rewrite length_skipn, length_app; cbn [length]; lia | cbn; lia |].
    pose proof (ca_memcmp_range _ _ _ _ Hv) as VR.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply BC' with (ls := skipn (p + i) (SS ++ [NUL])) (rs := str [46; 46; 46] ++ [NUL]) (v := vv).
      - match goal with |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 ?e)) _ =>
          rewrite (unsigned_lit e) by lia; replace e with (A + Z.of_nat (p + i)) by lia end.
        apply bytes_at_skipn; [exact HB | rewrite length_app; cbn [length]; lia].
      - rewrite unsigned_lit by lia. exact HD.
      - exact Hv.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                E & MU1 & WM1 & MI1 & HB1 & HB2).
    subst ms'. clear HB1 HB2 HD.
    transport_after_call rsegs m m1 MU1 WM1.
    clear MU1 WM1 MI.
    fix_ret.
    zstep. if_cases Z1.
    - zify_cond Z1.
      assert (V0 : vv = 0) by (Z.div_mod_to_equations; lia).
      apply evt_done. unfold dpost. do 18 eexists. split; [ainv_tac|]. left. split; [|reflexivity].
      rewrite <- HH. apply Hv0 in V0. rewrite V0. reflexivity.
    - zify_cond Z1.
      assert (VN : vv <> 0) by (intros ->; apply Z1; reflexivity).
      assert (HH' : has_dots (skipn (S i) (firstn L (skipn p SS))) = hb).
      { rewrite <- HH. destruct (bytes_eqb (firstn 3 (skipn (p + i) (SS ++ [NUL]))) (str [46; 46; 46])) eqn:EB; [|reflexivity].
        exfalso. apply VN, Hv0. apply bytes_eqb_iff in EB. rewrite EB. reflexivity. }
      zstep. zstep. if_cases Z2.
      + zify_cond Z2. replace (Z.of_nat i + 4) with (Z.of_nat (S i) + 3) by lia.
        apply (IH (S i)); [lia | lia | lia | exact HH' | ainv_tac].
      + zify_cond Z2. apply evt_done. unfold dpost. do 18 eexists. split; [ainv_tac|]. right. split; [|reflexivity].
        rewrite <- HH'. apply has_dots_short. rewrite length_skipn, length_firstn, length_skipn. lia.
  Qed.

  Definition synpost (rmn rmx : Z) (ms' : machine_state) : Prop :=
    exists m' j' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6,
      ainv (CB 8 j') m' /\
      ms' = SA 0x14938 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 rmn) (Z_to_bv 64 rmx) xs4 xs9 xs10 xs11 xt3 xt4 xt5 xt6 m'.

  Lemma synloop : forall f k mn mx rmn rmx m j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xs9 xs10 xs11 xt3 xt4 xt5 xt6,
    (length SS - k <= f)%nat -> (k <= length SS)%nat -> 0 <= mn -> mn + Z.of_nat (length SS - k) <= 2^20 ->
    (mx = UNB \/ 0 <= mx /\ mx + Z.of_nat (length SS - k) <= 2^20) ->
    arity_items (items_f f (skipn k SS)) mn mx = (rmn, rmx) -> ainv (CB 8 j) m ->
    evt rsegs (synpost rmn rmx)
      (SA 0x146e8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 (A + Z.of_nat k))
          xs9 xs10 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    intros f. induction f as [f IH] using (well_founded_induction lt_wf).
    intros k mn mx rmn rmx m j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xs9 xs10 xs11 xt3 xt4 xt5 xt6 Hf Hk Hmn0 Hmn Hmx Hres INV.
    pose proof INV as (MI & FR & ST & MU & WM & HB).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    assert (Rmx : 0 <= mx <= 2147483647) by (unfold UNB in Hmx; lia).
    zstep. zstep.
    eapply evt_cut; [eapply (skipA (S (length SS - k)) k m); [lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      rewrite (items_f_nil f (skipn k SS)) in Hres by (rewrite <- Hsk, E1, skipn_all; reflexivity).
      cbn [arity_items] in Hres. injection Hres as <- <-.
      apply evt_done. unfold synpost. do 18 eexists. split; [exact INV | reflexivity].
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      destruct f as [|f']; [lia|].
      rewrite (items_f_step f' SS k k1 Hsk LT1) in Hres.
      zstep. zstep. zstep.
      eapply evt_cut; [eapply (scanB (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (ya2 & ya3 & Hya2 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      pose proof (ilen_end (skipn k1 SS) 0) as HE. rewrite skipn_skipn in HE.
      set (L := ilen 0 (skipn k1 SS)) in *.
      replace (L + k1)%nat with (k1 + L)%nat in HE by lia.
      cbn [arity_items] in Hres.
      rewrite (bar_iff (skipn k1 SS) L) in Hres by (rewrite length_skipn; lia).
      rewrite (bracketed_iff (skipn k1 SS) L) in Hres by (rewrite length_skipn; lia).
      rewrite skipn_skipn in Hres. replace (L - 1 + k1)%nat with (k1 + L - 1)%nat in Hres by lia.
      assert (REQ : forall xa0' xa3' xs10',
        arity_items (items_f f' (skipn (k1 + L) SS)) (mn + 1) (bump mx) = (rmn, rmx) ->
        evt rsegs (synpost rmn rmx)
          (SA 0x14820 xra xt0 xt1 xt2 xa0' (zxb (hd NUL (skipn k1 SS))) ya2 xa3' (Z_to_bv 64 mn) (Z_to_bv 64 mx)
              (Z_to_bv 64 (A + Z.of_nat (k1 + L))) (Z_to_bv 64 (A + Z.of_nat k1)) xs10' xs11 xt3 xt4 xt5 xt6 m)).
      { intros xa0' xa3' xs10' HR.
        zstep. zstep. if_cases C3.
        + zify_cond C3. zstep. zstep. zstep. rewrite ca_swrap32_id by lia.
          unfold bump in HR. rewrite (proj2 (Z.eqb_eq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) UNB rmn rmx m j); [lia | lia | lia | lia | left; reflexivity | | exact INV].
          cbv iota in HR. replace mx with UNB in HR by (unfold UNB; lia). exact HR.
        + zify_cond C3. zstep. zstep. zstep. zstep. rewrite !ca_swrap32_id by lia.
          unfold bump in HR. rewrite (proj2 (Z.eqb_neq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) (mx + 1) rmn rmx m j); [lia | lia | lia | lia | | exact HR | exact INV].
          right. unfold UNB in Hmx. lia. }
      assert (NFP : forall m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs9' xs10' xs11' xt3' xt4' xt5' xt6',
        ainv (C8 (Z_to_bv 64 2147483647)) m' ->
        arity_items (items_f f' (skipn (k1 + L) SS)) mn (bump mx) = (rmn, rmx) ->
        evt rsegs (synpost rmn rmx)
          (SB 0x14810 xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' (Z_to_bv 64 mn) (Z_to_bv 64 mx)
              (Z_to_bv 64 (A + Z.of_nat (k1 + L))) xs9' xs10' xs11' xt3' xt4' xt5' xt6' m')).
      { intros m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs9' xs10' xs11' xt3' xt4' xt5' xt6' INV' HR.
        destruct INV' as (MI' & FR' & ST' & MU' & WM' & HB').
        zstep. zstep. if_cases C.
        + zify_cond C. zstep. zstep. zstep. zstep. zstep. rewrite ca_swrap32_id by lia.
          apply rw_c8_cb in FR'.
          unfold bump in HR. rewrite (proj2 (Z.eqb_neq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat mn (mx + 1) rmn rmx m' (le8 (Z_to_bv 64 2147483647)));
            [lia | lia | lia | lia | | exact HR | ainv_tac].
          right. unfold UNB in Hmx. lia.
        + zify_cond C. zstep. zstep. zstep. zstep. zstep. zstep.
          apply rw_c8_cb in FR'.
          unfold bump in HR. rewrite (proj2 (Z.eqb_eq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat mn UNB rmn rmx m' (le8 (Z_to_bv 64 2147483647)));
            [lia | lia | lia | lia | left; reflexivity | | ainv_tac].
          cbv iota in HR. replace mx with UNB in HR by (unfold UNB; lia). exact HR. }
      assert (FOUND : forall m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs9' xs10' xs11' xt3' xt4' xt5' xt6',
        ainv (C8 (Z_to_bv 64 2147483647)) m' ->
        arity_items (items_f f' (skipn (k1 + L) SS)) mn UNB = (rmn, rmx) ->
        evt rsegs (synpost rmn rmx)
          (SB 0x1484c xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' (Z_to_bv 64 mn) (Z_to_bv 64 mx)
              (Z_to_bv 64 (A + Z.of_nat (k1 + L))) xs9' xs10' xs11' xt3' xt4' xt5' xt6' m')).
      { intros m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs9' xs10' xs11' xt3' xt4' xt5' xt6' INV' HR.
        destruct INV' as (MI' & FR' & ST' & MU' & WM' & HB').
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply rw_c8_cb in FR'.
        eapply (IH f' ltac:(lia) (k1 + L)%nat mn UNB rmn rmx m' (le8 (Z_to_bv 64 2147483647)));
          [lia | lia | lia | lia | left; reflexivity | exact HR | ainv_tac]. }
      assert (K147cc : forall xa3', Nat.eqb L 1 && (bz (hd NUL (skipn k1 SS)) =? 124) = false ->
        evt rsegs (synpost rmn rmx)
          (SA 0x147cc xra xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat k1)) (zxb (hd NUL (skipn k1 SS))) ya2 xa3'
              (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 (A + Z.of_nat (k1 + L))) (Z_to_bv 64 (A + Z.of_nat k1))
              xs10 xs11 xt3 xt4 xt5 xt6 m)).
      { intros xa3' HB0. rewrite HB0 in Hres.
        zstep. if_cases Y2.
        - zify_cond Y2. rewrite (proj2 (Z.eqb_neq (bz (hd NUL (skipn k1 SS))) 91) Y2) in Hres. cbn [andb] in Hres.
          apply REQ. exact Hres.
        - zify_cond Y2. rewrite (proj2 (Z.eqb_eq (bz (hd NUL (skipn k1 SS))) 91) Y2) in Hres. cbn [andb] in Hres.
          zstep.
          match goal with |- context [Z_to_bv 64 (?x - ?y)] => replace (x - y) with (Z.of_nat L) by lia end.
          zstep.
          pose proof (ca_rd_hd m A SS (k1 + L - 1) HB ltac:(lia)) as RDl.
          pose proof (byte_range (hd NUL (skipn (k1 + L - 1) SS))) as BRl.
          zstep. zstep. if_cases Y4.
          + zify_cond Y4. rewrite (proj2 (Z.eqb_neq (bz (hd NUL (skipn (k1 + L - 1) SS))) 93) Y4) in Hres.
            apply REQ. exact Hres.
          + zify_cond Y4. rewrite (proj2 (Z.eqb_eq (bz (hd NUL (skipn (k1 + L - 1) SS))) 93) Y4) in Hres.
            cbv iota in Hres. clear RDl.
            zstep. zstep. if_cases C5.
            * zify_cond C5.
              rewrite has_dots_short in Hres by (rewrite length_firstn, length_skipn; lia).
              eapply NFP; [ainv_tac | exact Hres].
            * zify_cond C5. zstep.
              eapply evt_cut.
              { eapply (dots_loop (S L) 0 k1 L (has_dots (firstn L (skipn k1 SS)))); [lia | lia | lia | reflexivity | ainv_tac]. }
              intros ms5 (m5 & xra5 & xt05 & xt15 & xt25 & xa05 & xa15 & xa25 & xa35 & xa45 & xa55 & xa65 & xa75 & xs115 &
                          xt35 & xt45 & xt55 & xt65 & INV5 & [[HT E5] | [HF E5]]); subst ms5.
              -- rewrite HT in Hres. eapply FOUND; [exact INV5 | exact Hres].
              -- rewrite HF in Hres. eapply NFP; [exact INV5 | exact Hres]. }
      zstep. if_cases Y1.
      + zify_cond Y1. apply K147cc.
        rewrite (proj2 (Z.eqb_neq (bz (hd NUL (skipn k1 SS))) 124) Y1), andb_false_r. reflexivity.
      + zify_cond Y1. zstep. zstep. if_cases C6.
        * zify_cond C6. apply K147cc. rewrite (proj2 (Nat.eqb_neq L 1)) by lia. reflexivity.
        * zify_cond C6.
          rewrite (proj2 (Nat.eqb_eq L 1)) in Hres by lia.
          rewrite (proj2 (Z.eqb_eq (bz (hd NUL (skipn k1 SS))) 124) Y1) in Hres. cbn [andb] in Hres.
          zstep. zstep. if_cases C7.
          -- zify_cond C7. rewrite Hya2 in C7.
             assert (R0 : skipn (k1 + L) SS = []) by (destruct HE as [HE|HE]; [exact HE | exfalso; exact (C7 HE)]).
             assert (KL : (k1 + L)%nat = length SS).
             { apply (f_equal (@length byte)) in R0. rewrite length_skipn in R0. cbn in R0. lia. }
             rewrite R0 in Hres, Hya2.
             rewrite (items_f_nil f' []) in Hres by reflexivity. cbv iota in Hres.
             zstep. if_cases Y8.
             ++ zify_cond Y8.
                eapply (IH f' ltac:(lia) (k1 + L)%nat mn mx rmn rmx m j); [lia | lia | lia | lia | destruct Hmx as [Hmx'|Hmx']; [left; exact Hmx' | right; lia] | | exact INV].
                rewrite R0, (items_f_nil f' []) by reflexivity. exact Hres.
             ++ zify_cond Y8. exfalso. apply Y8. rewrite Hya2. reflexivity.
          -- zify_cond C7. rewrite Hya2 in C7.
             assert (LT2 : (k1 + L < length SS)%nat).
             { destruct (Nat.lt_ge_cases (k1 + L) (length SS)) as [H|H]; [exact H|].
               exfalso. rewrite ca_hd_skipn_end in C7 by exact H. discriminate C7. }
             eapply evt_cut; [eapply (skipC (S (length SS - (k1 + L))) (k1 + L) m); [lia | lia | exact C7 | exact HB] |].
             intros ms3 (k2 & Hk2 & Hsk2 & Hsp2 & ->).
             zstep. if_cases C9.
             ++ zify_cond C9.
                pose proof (ca_hd_z_end SS k2 HSn ltac:(lia) C9) as E2.
                assert (NIL : items_f f' (skipn (k1 + L) SS) = []).
                { apply items_f_nil. rewrite <- Hsk2, E2, skipn_all. reflexivity. }
                rewrite NIL in Hres. cbv iota in Hres.
                eapply (IH f' ltac:(lia) (k1 + L)%nat mn mx rmn rmx m j); [lia | lia | lia | lia | destruct Hmx as [Hmx'|Hmx']; [left; exact Hmx' | right; lia] | | exact INV].
                rewrite NIL. exact Hres.
             ++ zify_cond C9.
                assert (LT3 : (k2 < length SS)%nat) by (apply (ca_hd_nz_lt SS k2); lia).
                zstep.
                eapply evt_cut; [eapply (scanD (S (length SS - k2)) k2 0 m); [lia | lia | lia | exact C9 | exact HB] |].
                intros ms4 (ya0 & ya1 & ya2' & ->).
                assert (NE2 : skipn k2 SS <> []).
                { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
                pose proof (ilen_pos (skipn k2 SS) Hsp2 NE2) as HL21.
                pose proof (ilen_le 0 (skipn k2 SS)) as HL22. rewrite length_skipn in HL22.
                set (L2 := ilen 0 (skipn k2 SS)) in *.
                destruct f' as [|f'']; [lia|].
                rewrite (items_f_step f'' SS (k1 + L) k2 Hsk2 LT3) in Hres. fold L2 in Hres. cbv iota in Hres.
                eapply (IH f'' ltac:(lia) (k2 + L2)%nat mn mx rmn rmx m j); [lia | lia | lia | lia | | exact Hres | exact INV].
                destruct Hmx as [Hmx|Hmx]; [left; exact Hmx | right; lia].
  Qed.

  Lemma fskipA : forall n k m xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7
                        xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = SG 0x1465c xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
                          (Z_to_bv 64 (A + Z.of_nat k')) (Z_to_bv 64 32) xa2 xa3 xa4 xa5 xa6 (zxb (hd NUL (skipn k' SS)))
                          xt3 xt4 xt5 xt6 m)
      (SG 0x1464c xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 32) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof (ca_rd_hd m A SS k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS k ltac:(lia)) as LT.
      zstep. zstep.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma fscanB : forall n q d m xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya0 ya1 ya7,
                 ms' = SG 0x14868 xra xs0 xs2 xs3 (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS)))) xs5 xs6 xs7 xs8
                          xs9 xs10 xs11 xt0 xt1 xt2 ya0 ya1 (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93)
                          (Z_to_bv 64 32) ya7 xt3 xt4 xt5 xt6 m)
      (SG 0x14678 xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat q)) (Z_to_bv 64 d)
          (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 32) (zxb (hd NUL (skipn q SS)))
          xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xt3 xt4 xt5 xt6
      HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d', 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x146a8 xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat q))
          (Z_to_bv 64 d') (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 32)
          (zxb (hd NUL (skipn q SS))) xt3 xt4 xt5 xt6 m)).
    { intros d' HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya0 & ya1 & ya7 & E). subst ms'. unfold POSTQ. exists ya0, ya1, ya7.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x14680 xra xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 (Z_to_bv 64 (A + Z.of_nat q))
          (Z_to_bv 64 d) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 32)
          (zxb (hd NUL (skipn q SS))) xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. zstep. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. zstep. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Lemma fskipC : forall n k m xra xs0 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7
                        xt3 xt4 xt5 xt6,
    (length SS - k < n)%nat -> (k <= length SS)%nat -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length SS)%nat /\ skipn k' SS = skip_sp (skipn k SS) /\
                 bz (hd NUL (skipn k' SS)) <> 32 /\
                 ms' = SG 0x148b4 xra xs0 xs2 xs3 xs4 (Z_to_bv 64 32) xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
                          (Z_to_bv 64 (A + Z.of_nat k')) (Z_to_bv 64 (A + Z.of_nat k' + 3)) xa2 xa3
                          (zxb (hd NUL (skipn k' SS))) xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)
      (SG 0x148a0 xra xs0 xs2 xs3 xs4 (Z_to_bv 64 32) xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
          (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 (A + Z.of_nat k + 3)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xs0 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 HN HK HB; [lia|].
    pose proof (ca_rd_hd m A SS k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k SS))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (ca_hd_nz_lt SS k ltac:(lia)) as LT.
      zstep. zstep. zstep.
      replace (A + Z.of_nat k + 4) with (A + Z.of_nat (S k) + 3) by lia.
      replace (A + Z.of_nat k + 1) with (A + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (ca_skip_sp_at SS k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k SS))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma fscanD : forall n q d m xra xs0 xs2 xs3 xs4 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (length SS - q < n)%nat -> (q <= length SS)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q SS)) <> 0 -> bytes_at rsegs m A (SS ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya2 ya3 ya4,
                 ms' = SG 0x14908 xra xs0 xs2 xs3 (Z_to_bv 64 (A + Z.of_nat (q + ilen d (skipn q SS))))
                          (Z_to_bv 64 32) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) xs10 xs11
                          xt0 xt1 xt2 xa0 xa1 ya2 ya3 ya4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)
      (SG 0x148c0 xra xs0 xs2 xs3 xs4 (Z_to_bv 64 32) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) xs10 xs11
          xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d) (Z_to_bv 64 (A + Z.of_nat q)) (zxb (hd NUL (skipn q SS))) xa5 xa6 xa7
          xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xs0 xs2 xs3 xs4 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa5 xa6 xa7 xt3 xt4 xt5 xt6
      HN HQ HD NZ HB; [lia|].
    pose proof (ca_hd_nz_lt SS q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q SS))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d', 0 <= d' <= Z.of_nat q + 1 -> d' = ca_dstep d (hd NUL (skipn q SS)) ->
      (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x148f0 xra xs0 xs2 xs3 xs4 (Z_to_bv 64 32) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) xs10 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d') (Z_to_bv 64 (A + Z.of_nat q))
          (zxb (hd NUL (skipn q SS))) xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)).
    { intros d' HD' Ed' NS.
      assert (IL : ilen d (skipn q SS) = S (ilen d' (skipn (S q) SS))).
      { rewrite (ca_hd_skipn_S SS q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (ca_rd_hd m A SS (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) SS))) as BR1.
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya2 & ya3 & ya4 & E). subst ms'. unfold POSTQ. exists ya2, ya3, ya4.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) SS)))%nat with (S q + ilen d' (skipn (S q) SS))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (ca_hd_z_end SS (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 SS (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (A + Z.of_nat q + 1) with (A + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q SS)) =? 32) = false ->
      evt rsegs POSTQ (SG 0x148c8 xra xs0 xs2 xs3 xs4 (Z_to_bv 64 32) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60)
          (Z_to_bv 64 93) xs10 xs11 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 d) (Z_to_bv 64 (A + Z.of_nat q))
          (zxb (hd NUL (skipn q SS))) xa5 xa6 xa7 xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. zstep. zstep. rewrite ca_swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. zstep. if_cases Hc4.
          * zify_cond Hc4. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc4. pos_false_tac. zstep.
            apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6. pos_false_tac.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. zstep. if_cases Hc7.
               ++ zify_cond Hc7.
                  apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
               ++ zify_cond Hc7. zstep. rewrite ca_swrap32_id by lia.
                  apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS].
          * zify_cond Hc5. zstep. zstep. rewrite ca_swrap32_id by lia.
            apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
    - zify_cond Hc1. pos_false_tac. zstep. if_cases Hc8.
      + zify_cond Hc8. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q SS) = 0%nat).
        { rewrite (ca_hd_skipn_S SS q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc8). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. unfold bz.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q SS))) 32)) by lia. rewrite andb_false_r. reflexivity.
  Qed.

  Definition endpost (rmn rmx : Z) (ms' : machine_state) : Prop :=
    exists m' j' xra xs0 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
      ainv (CB 8 j') m' /\
      ms' = SG 0x14938 xra xs0 (Z_to_bv 64 rmn) (Z_to_bv 64 rmx) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
              xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m'.

  Lemma fmtloop : forall f k mn mx rmn rmx m j xra xs3 xs11 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (length SS - k <= f)%nat -> (k <= length SS)%nat -> 0 <= mn -> mn + Z.of_nat (length SS - k) <= 2^20 ->
    (mx = UNB \/ 0 <= mx /\ mx + Z.of_nat (length SS - k) <= 2^20) ->
    format_arity_items (items_f f (skipn k SS)) mn mx = (rmn, rmx) -> ainv (CB 8 j) m ->
    evt rsegs (endpost rmn rmx)
      (SG 0x14894 xra (Z_to_bv 64 67124) (Z_to_bv 64 mn) xs3 (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 32) (Z_to_bv 64 91)
          (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 2147483647) xs11 xt0 xt1 xt2 xa0 (Z_to_bv 64 mx)
          xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).
  Proof.
    pose proof BC as BC'. unfold bcmp_contract in BC'.
    intros f. induction f as [f IH] using (well_founded_induction lt_wf).
    intros k mn mx rmn rmx m j xra xs3 xs11 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hf Hk Hmn0 Hmn Hmx Hres INV.
    pose proof INV as (MI & FR & ST & MU & WM & HB).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    assert (Rmx : 0 <= mx <= 2147483647) by (unfold UNB in Hmx; lia).
    zstep. zstep. zstep.
    eapply evt_cut; [eapply (fskipC (S (length SS - k)) k m); [lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      rewrite (items_f_nil f (skipn k SS)) in Hres by (rewrite <- Hsk, E1, skipn_all; reflexivity).
      cbn [format_arity_items] in Hres. injection Hres as <- <-.
      apply evt_done. unfold endpost. do 27 eexists. split; [exact INV | reflexivity].
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      destruct f as [|f']; [lia|].
      rewrite (items_f_step f' SS k k1 Hsk LT1) in Hres.
      zstep. zstep.
      eapply evt_cut; [eapply (fscanD (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (ya2 & ya3 & ya4 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      set (L := ilen 0 (skipn k1 SS)) in *.
      cbn [format_arity_items] in Hres.
      assert (CNT : forall m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6',
        ainv (CB 8 j) m' ->
        format_arity_items (items_f f' (skipn (k1 + L) SS)) (mn + 1) (bump mx) = (rmn, rmx) ->
        evt rsegs (endpost rmn rmx)
          (SG 0x14920 xra' (Z_to_bv 64 67124) (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 (A + Z.of_nat (k1 + L)))
              (Z_to_bv 64 32) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) (Z_to_bv 64 2147483647) xs11
              xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' m')).
      { intros m' xra' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' INV' HR.
        zstep. if_cases C3.
        + zify_cond C3. zstep. zstep. zstep. rewrite !ca_swrap32_id by lia.
          unfold bump in HR. rewrite (proj2 (Z.eqb_neq mx UNB)) in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) (mx + 1) rmn rmx m' j); [lia | lia | lia | lia | | exact HR | exact INV'].
          right. unfold UNB in Hmx. lia.
        + zify_cond C3. zstep. zstep. zstep. zstep. rewrite !ca_swrap32_id by lia.
          unfold bump in HR. rewrite (proj2 (Z.eqb_eq mx UNB)) in HR by (unfold UNB; lia). cbv iota in HR.
          replace mx with UNB in HR by (unfold UNB; lia).
          eapply (IH f' ltac:(lia) (k1 + L)%nat (mn + 1) UNB rmn rmx m' j);
            [lia | lia | lia | lia | left; reflexivity | exact HR | exact INV']. }
      zstep. if_cases Y1.
      + zify_cond Y1.
        rewrite (ca_bytes_eqb_len (firstn L (skipn k1 SS)) (str [46; 46; 46])) in Hres
          by (rewrite length_firstn, length_skipn; unfold str; cbn [length map]; lia).
        eapply CNT; [exact INV | exact Hres].
      + zify_cond Y1.
        assert (L3 : L = 3%nat) by lia.
        zstep. zstep. zstep.
        pose proof (lit_at m 67124 (str [46; 46; 46] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HD.
        destruct (ca_memcmp_eq 3 (skipn k1 (SS ++ [NUL])) (str [46; 46; 46] ++ [NUL])) as (vv & Hv & Hv0);
          [rewrite length_skipn, length_app; cbn [length]; lia | cbn; lia |].
        pose proof (ca_memcmp_range _ _ _ _ Hv) as VR.
        assert (FW : firstn 3 (skipn k1 (SS ++ [NUL])) = firstn L (skipn k1 SS)).
        { rewrite L3, skipn_app. replace (k1 - length SS)%nat with 0%nat by lia. cbn [skipn].
          rewrite firstn_app, length_skipn. replace (3 - (length SS - k1))%nat with 0%nat by lia.
          rewrite firstn_O, app_nil_r. reflexivity. }
        eapply evt_cut.
        { eapply BC' with (ls := skipn k1 (SS ++ [NUL])) (rs := str [46; 46; 46] ++ [NUL]) (v := vv).
          - rewrite unsigned_lit by lia. apply bytes_at_skipn; [exact HB | rewrite length_app; cbn [length]; lia].
          - rewrite unsigned_lit by lia. exact HD.
          - exact Hv.
          - exact MI. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MU1 & WM1 & MI1 & HB1 & HB2).
        subst ms'. clear HB1 HB2 HD INV.
        transport_after_call rsegs m m1 MU1 WM1.
        clear MU1 WM1 MI.
        fix_ret.
        zstep. zstep. if_cases Z2.
        * zify_cond Z2.
          assert (V0 : vv = 0) by (Z.div_mod_to_equations; lia).
          apply Hv0 in V0. rewrite FW in V0.
          assert (EB : bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46]) = true) by (apply bytes_eqb_iff; exact V0).
          rewrite EB in Hres.
          eapply (IH f' ltac:(lia) (k1 + L)%nat mn UNB rmn rmx m1 j);
            [lia | lia | lia | lia | left; reflexivity | exact Hres | ainv_tac].
        * zify_cond Z2.
          assert (VN : vv <> 0) by (intros ->; apply Z2; reflexivity).
          assert (EB : bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46]) = false).
          { destruct (bytes_eqb (firstn L (skipn k1 SS)) (str [46; 46; 46])) eqn:EB; [|reflexivity].
            exfalso. apply VN, Hv0. rewrite FW. apply bytes_eqb_iff in EB. rewrite EB. reflexivity. }
          rewrite EB in Hres.
          eapply CNT; [ainv_tac | exact Hres].
  Qed.

  Lemma fmt_path : forall m j rmn rmx xra xs0 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          xt3 xt4 xt5 xt6,
    ainv (CB 8 j) m -> row_arity SS 1 = (rmn, rmx) ->
    evt rsegs (endpost rmn rmx)
      (SG 0x14644 xra xs0 xs2 xs3 (Z_to_bv 64 A) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          xt3 xt4 xt5 xt6 m).
  Proof.
    intros m j rmn rmx xra xs0 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 INV HR.
    pose proof INV as (MI & FR & ST & MU & WM & HB).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    unfold row_arity in HR. cbn [Z.eqb] in HR.
    zstep. zstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
    eapply evt_cut; [eapply (fskipA (S (length SS)) 0 m); [lia | lia | exact HB] |].
    intros ms1 (k1 & Hk1 & Hsk & Hsp & ->).
    zstep. if_cases Z1.
    - zify_cond Z1.
      pose proof (ca_hd_z_end SS k1 HSn ltac:(lia) Z1) as E1.
      assert (NIL : shape_items SS = []).
      { unfold shape_items. apply items_f_nil. change SS with (skipn 0 SS) at 1. rewrite <- Hsk, E1, skipn_all. reflexivity. }
      rewrite NIL in HR. injection HR as <- <-.
      do 11 zstep.
      eapply (fmtloop (length SS) 0 0 0 0 0 m j); [lia | lia | lia | lia | right; lia | | exact INV].
      change (items_f (length SS) (skipn 0 SS)) with (shape_items SS). rewrite NIL. reflexivity.
    - zify_cond Z1.
      assert (LT1 : (k1 < length SS)%nat) by (apply (ca_hd_nz_lt SS k1); lia).
      pose proof (items_f_step (length SS - 1) SS 0 k1 Hsk LT1) as IS.
      change (skipn 0 SS) with SS in IS. replace (S (length SS - 1)) with (length SS) in IS by lia.
      unfold shape_items in HR. rewrite IS in HR. cbv iota in HR.
      do 6 zstep.
      eapply evt_cut; [eapply (fscanB (S (length SS - k1)) k1 0 m); [lia | lia | lia | exact Z1 | exact HB] |].
      intros ms2 (ya0 & ya1 & ya7 & ->).
      assert (NE1 : skipn k1 SS <> []).
      { intros H. apply (f_equal (@length byte)) in H. rewrite length_skipn in H. cbn in H. lia. }
      pose proof (ilen_pos (skipn k1 SS) Hsp NE1) as HL1.
      pose proof (ilen_le 0 (skipn k1 SS)) as HL2. rewrite length_skipn in HL2.
      set (L := ilen 0 (skipn k1 SS)) in *.
      do 11 zstep.
      eapply (fmtloop (length SS - 1) (k1 + L) 0 0 rmn rmx m j); [lia | lia | lia | lia | right; lia | exact HR | exact INV].
  Qed.

  Lemma syn_path : forall m j rmn rmx xra xs0 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          xt3 xt4 xt5 xt6,
    ainv (CB 8 j) m -> row_arity SS 0 = (rmn, rmx) ->
    evt rsegs (endpost rmn rmx)
      (SG 0x146bc xra xs0 xs2 xs3 (Z_to_bv 64 A) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          xt3 xt4 xt5 xt6 m).
  Proof.
    intros m j rmn rmx xra xs0 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 INV HR.
    unfold row_arity in HR. cbn [Z.eqb] in HR.
    do 11 zstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
    eapply evt_mono; [eapply (synloop (length SS) 0 0 0 rmn rmx m j); [lia | lia | lia | lia | right; lia | exact HR | exact INV] |].
    intros ms' (m' & j' & xra' & xt0' & xt1' & xt2' & xa0' & xa1' & xa2' & xa3' & xs4' & xs9' & xs10' & xs11' &
                xt3' & xt4' & xt5' & xt6' & INV' & ->).
    unfold endpost. do 27 eexists. split; [exact INV' | reflexivity].
  Qed.
End Syn.

Definition row_bytes (r : Z * Z * Z) : list byte :=
  match r with (na, sy, fm) => le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 sy) ++ le4 (Z_to_bv 64 fm) ++ [NUL; NUL; NUL; NUL] end.

Definition lit_ok (A : Z) : bool :=
  ro_bytes_b rsegs A (img_str A ++ [NUL]) && (Z.of_nat (length (img_str A)) <? 128) &&
  forallb (fun z => negb (z =? 0)) (map bv_unsigned (img_str A)) && (0 <=? A) && (A + 129 <=? 347320).

Definition rowchk (r : Z * Z * Z) : bool :=
  match r with (na, sy, fm) =>
    lit_ok na && lit_ok sy && ((fm =? 0) || (fm =? 1)) &&
    (0 <=? fst (row_arity (img_str sy) fm)) && (snd (row_arity (img_str sy) fm) <=? UNB)
  end.

Lemma rows_ok : forallb rowchk parsed_rows = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lit_facts : forall m A, mem_inv rsegs m -> lit_ok A = true ->
  cstr_at m A (img_str A) /\ Z.of_nat (length (img_str A)) < 128 /\ 0 <= A /\ A + 129 <= 347320.
Proof.
  intros m A HI H. unfold lit_ok in H. repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.ltb_lt in H2. apply Z.leb_le in H4. apply Z.leb_le in H5.
  split; [split|].
  - apply lit_at; [exact HI | exact H1 | lia | rewrite length_app; cbn [length]; lia].
  - apply notin_nul_lit. exact H3.
  - lia.
Qed.

Lemma read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(cbn [Z.to_nat]; lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma row_reads : forall m B na sy fm, bytes_at rsegs m B (row_bytes (na, sy, fm)) ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (Z_to_bv 64 na)) /\
  ov_read_bytes rsegs m (wa (B + 8)) 8 = Some (le8 (Z_to_bv 64 sy)) /\
  ov_read_bytes rsegs m (wa (B + 16)) 4 = Some (le4 (Z_to_bv 64 fm)).
Proof.
  intros m B na sy fm H. unfold row_bytes in H.
  apply bytes_at_app in H as [H1 H]. apply bytes_at_app in H as [H2 H]. apply bytes_at_app in H as [H3 _].
  pose proof (read_all _ _ _ H1) as R1. pose proof (read_all _ _ _ H2) as R2. pose proof (read_all _ _ _ H3) as R3.
  rewrite length_le8 in R1. rewrite !length_le8 in R2. rewrite !length_le8, length_le4 in R3.
  change (Z.of_nat 8) with 8 in R2, R3. replace (B + 8 + 8) with (B + 16) in R3 by lia.
  split; [exact R1 | split; [exact R2 | exact R3]].
Qed.

Definition acond (t : Z) (o : option (Z * Z)) : Prop :=
  match o with None => True | Some (mn, mx) => mn <= Z.min t 64 - 1 <= mx end.

Lemma arity_cont : forall t v q nc fn0, arity_ok t v q nc fn0 -> t <> 0 -> ~ (q = 0 /\ nc = 0) ->
  ~ (0 < nc /\ fn0 = REC_BROADCAST /\ passed_on_m v = true) -> acond t (row_find v parsed_rows).
Proof. intros t v q nc fn0 [H|[H|[H|H]]] H1 H2 H3; [contradiction | contradiction | contradiction | exact H]. Qed.

Lemma cspn_len_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [cspn_len length]; [lia|]. destruct (existsb _ _); lia. Qed.

Lemma vp_len : forall v f, cspn_len (str [32; 9]) v <> length f -> verb_prefix v f = false.
Proof. intros v f H. unfold verb_prefix. rewrite (proj2 (Nat.eqb_neq _ _) H). reflexivity. Qed.

Lemma vp_pre : forall v f, prefixb v f = false -> verb_prefix v f = false.
Proof. intros v f H. unfold verb_prefix. rewrite H, andb_false_r. reflexivity. Qed.

Lemma passed_on_false : forall v, bytes_eqb v (img_str 0x1067c) = false -> bytes_eqb v (img_str 0x104e2) = false ->
  verb_prefix v (str [99; 111; 110; 110; 101; 99; 116]) = false ->
  verb_prefix v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false -> passed_on_m v = false.
Proof. intros v H1 H2 H3 H4. unfold passed_on_m. rewrite H1, H2, H3, H4. reflexivity. Qed.

Lemma ca_sx32_zero : forall q, 0 <= q < 2^32 -> (bv_unsigned (sx32 (Z_to_bv 64 q)) = 0 <-> q = 0).
Proof.
  intros q Hq. unfold sx32. rewrite (unsigned_lit q) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  split; intros H.
  - Z.div_mod_to_equations. lia.
  - subst q. reflexivity.
Qed.

Lemma ca_walk_prefix : forall k s rest, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_walk (s ++ [NUL]) (k ++ rest) (length k - 1) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  induction k as [|c k IH]; intros s rest Hs Hk Hne; [congruence|].
  destruct (notin_nul_cons c k Hk) as [Hc Hk'].
  destruct s as [|a s'].
  - cbn [app strncmp_walk]. unfold NUL. rewrite Z_to_bv_unsigned. cbn [bv_wrap].
    eexists. split; [reflexivity|]. split; [intros E; exfalso; change (bv_wrap 8 0) with 0 in E; lia | intros E; discriminate].
  - destruct (notin_nul_cons a s' Hs) as [Ha Hs'].
    cbn [app length].
    destruct k as [|c2 k2].
    + cbn [app strncmp_walk Nat.sub Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb]. replace (0 - 0)%nat with 0%nat by reflexivity.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * eexists. split; [reflexivity|]. split; [intros _; cbn; f_equal; apply bv_eq; exact E | intros _; lia].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E; subst; lia].
    + replace (S (length (c2 :: k2)) - 1)%nat with (S (length (c2 :: k2) - 1)) by (cbn; lia).
      cbn [strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb Nat.eqb].
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * destruct (IH s' rest Hs' Hk' ltac:(discriminate)) as (v & Hw & Hv).
        exists v. split; [exact Hw|]. rewrite Hv. cbn [firstn length].
        replace a with c by (apply bv_eq; symmetry; exact E).
        split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E1 _; subst; lia].
Qed.

Lemma ca_strncmp_prefix : forall s k rest, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_model (s ++ [NUL]) (k ++ rest) (Z.of_nat (length k)) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  intros s k rest Hs Hk Hne. unfold strncmp_model.
  destruct k as [|c k']; [congruence|].
  replace (Z.of_nat (length (c :: k')) =? 0) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
  replace (Z.to_nat (Z.of_nat (length (c :: k')) - 1)) with (length (c :: k') - 1)%nat by lia.
  apply ca_walk_prefix; assumption.
Qed.

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z).
  Hypothesis LO : lo + 208 <= bv_unsigned sp.
  Hypothesis IE : 347320 <= lo.

  Definition fsaved : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation POST := (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Lemma ret_ok : forall j m' xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -112) (CB 8 j :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -112) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    evt rsegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x14940) fc None m' (seg_rom rsegs)).
  Proof.
    intros j m' xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 MI FR ST MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
    unfold fsaved in FR.
    do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  Qed.

  Variables (t : Z) (p0 : word) (v : list byte) (j0 : list byte).
  Hypothesis HT : 1 <= t <= 4096.
  Hypothesis SC : strcmp_contract.
  Hypothesis BC : bcmp_contract.

  Lemma tail_ok : forall j m' rmn rmx xra xs0 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -112) (CB 8 j :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -112) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    0 <= rmn <= Z.min t 64 - 1 -> Z.min t 64 - 1 <= rmx <= UNB ->
    evt rsegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 (Z.min t 64 - 1))
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 rmn) (Z_to_bv 64 rmx) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
               xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x14938) fc None m' (seg_rom rsegs)).
  Proof.
    intros j m' rmn rmx xra xs0 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
      xt3 xt4 xt5 xt6 MI FR ST MU WM R1 R2.
    unfold UNB in R2.
    zstep. if_cases B1; [exfalso; zify_cond B1; rewrite ?ca_signed_small in B1 by lia; lia|].
    zstep. if_cases B2; [exfalso; zify_cond B2; rewrite ?ca_signed_small in B2 by lia; lia|].
    eapply ret_ok; eassumption.
  Qed.

  Lemma rows_loop : forall rows i m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (i + length rows = 22)%nat -> rows <> [] -> forallb rowchk rows = true ->
    bytes_at rsegs m' (140472 + 24 * Z.of_nat i) (concat (map row_bytes rows)) ->
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -112) (CB 8 j0 :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -112) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    bytes_at rsegs m' (bv_unsigned p0) (v ++ [NUL]) -> ~ In NUL v ->
    acond t (row_find v rows) ->
    evt rsegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 p0 (Z_to_bv 64 (Z.min t 64 - 1))
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (140480 + 24 * Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat (length rows))) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x14618) fc None m' (seg_rom rsegs)).
  Proof.
    pose proof SC as SC'. unfold strcmp_contract in SC'.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    induction rows as [|[[na sy] fm] rows IH];
      intros i m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hi Hne Hok HG MI FR ST MU WM HV HVn AC;
      [congruence|].
    cbn [forallb] in Hok. apply andb_prop in Hok as [Hrow Hok].
    unfold rowchk in Hrow. repeat rewrite andb_true_iff in Hrow.
    destruct Hrow as [[[[Hna Hsy] Hfm] Hmn] Hmx].
    apply Z.leb_le in Hmn. apply Z.leb_le in Hmx.
    cbn [map concat] in HG. apply bytes_at_app in HG as [HR0 HG'].
    replace (Z.of_nat (length (row_bytes (na, sy, fm)))) with 24 in HG'
      by (unfold row_bytes; rewrite !length_app, !length_le8, length_le4; reflexivity).
    destruct (row_reads m' _ na sy fm HR0) as (RNA & RSY & RFM). clear HR0.
    destruct (lit_facts m' na MI Hna) as ([HNA HNAn] & LNA & NA0 & NAE).
    destruct (lit_facts m' sy MI Hsy) as ([HSY HSYn] & LSY & SY0 & SYE).
    assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
    change (length ((na, sy, fm) :: rows)) with (S (length rows)) in *.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC' with (sx := v) (sy := img_str na).
      - exact HV.
      - exact HVn.
      - rewrite unsigned_lit by lia. exact HNA.
      - exact HNAn. }
    intros ms' (r0 & x11 & x12 & x13 & E & Hr). subst ms'.
    fix_ret.
    revert AC. cbn [row_find]. destruct (bytes_eqb (img_str na) v) eqn:EQ; intros AC.
    - apply bytes_eqb_iff in EQ.
      assert (R0 : r0 = Z_to_bv 64 0) by (apply Hr; symmetry; exact EQ). subst r0.
      zstep. if_cases B1; [|exfalso; vm_compute in B1; discriminate B1].
      apply orb_true_iff in Hfm as [Hfm|Hfm]; apply Z.eqb_eq in Hfm; subst fm;
        destruct (row_arity (img_str sy) _) as [rmn rmx] eqn:RA; cbn [fst snd] in Hmn, Hmx; cbn [acond] in AC.
      + zstep. zstep. zstep. if_cases B2; [|exfalso; vm_compute in B2; discriminate B2].
        eapply evt_cut.
        { eapply syn_path with (SS := img_str sy) (m0 := m) (lo := lo) (saved := fsaved) (j := j0) (rmn := rmn) (rmx := rmx);
            first [exact BC | exact HSYn | exact RA | ainv_tac | (split; lia) | lia]. }
        intros ms' (m2 & j2 & xra' & xs0' & xs4' & xs5' & xs6' & xs7' & xs8' & xs9' & xs10' & xs11' & xt0' & xt1' & xt2' &
                    xa0' & xa1' & xa2' & xa3' & xa4' & xa5' & xa6' & xa7' & xt3' & xt4' & xt5' & xt6' & INV2 & ->).
        destruct INV2 as (MI2 & FR2 & ST2 & MU2 & WM2 & _).
        eapply tail_ok; [exact MI2 | exact FR2 | exact ST2 | exact MU2 | exact WM2 | lia | lia].
      + zstep. zstep. zstep. if_cases B2; [exfalso; vm_compute in B2; discriminate B2|].
        eapply evt_cut.
        { eapply fmt_path with (SS := img_str sy) (m0 := m) (lo := lo) (saved := fsaved) (j := j0) (rmn := rmn) (rmx := rmx);
            first [exact BC | exact HSYn | exact RA | ainv_tac | (split; lia) | lia]. }
        intros ms' (m2 & j2 & xra' & xs0' & xs4' & xs5' & xs6' & xs7' & xs8' & xs9' & xs10' & xs11' & xt0' & xt1' & xt2' &
                    xa0' & xa1' & xa2' & xa3' & xa4' & xa5' & xa6' & xa7' & xt3' & xt4' & xt5' & xt6' & INV2 & ->).
        destruct INV2 as (MI2 & FR2 & ST2 & MU2 & WM2 & _).
        eapply tail_ok; [exact MI2 | exact FR2 | exact ST2 | exact MU2 | exact WM2 | lia | lia].
    - assert (RN : bv_unsigned r0 <> 0).
      { intros H. apply bv0_iff, Hr in H. rewrite H in EQ.
        rewrite (proj2 (bytes_eqb_iff _ _) eq_refl) in EQ. discriminate EQ. }
      zstep. if_cases B1; [exfalso; zify_cond B1; lia|].
      zstep. zstep. zstep. if_cases B3.
      + eapply ret_ok; eassumption.
      + zify_cond B3. zstep.
        destruct rows as [|r' rows']; [exfalso; cbn [length] in B3; Z.div_mod_to_equations; lia|].
        match goal with |- context [Z_to_bv 64 (140480 + 24 * Z.of_nat i + ?c)] =>
          replace (140480 + 24 * Z.of_nat i + c) with (140480 + 24 * Z.of_nat (S i)) by lia end.
        match goal with |- context [Z_to_bv 64 (Z.of_nat (S (length (r' :: rows'))) + ?c)] =>
          replace (Z.of_nat (S (length (r' :: rows'))) + c) with (Z.of_nat (length (r' :: rows'))) by lia end.
        replace (140472 + 24 * Z.of_nat i + 24) with (140472 + 24 * Z.of_nat (S i)) in HG' by lia.
        eapply (IH (S i)); [lia | discriminate | exact Hok | exact HG' | exact MI | exact FR | exact ST | exact MU |
                            exact WM | exact HV | exact HVn | exact AC].
  Qed.

  Lemma cont_ok : forall m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    mem_inv rsegs m' -> rw_cells rsegs m' (bv_unsigned sp + -112) (CB 8 j0 :: fsaved) ->
    stk rsegs m' lo (bv_unsigned sp + -112) -> munch [(lo, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
    bytes_at rsegs m' 140472 g_parsed_bytes ->
    bytes_at rsegs m' (bv_unsigned p0) (v ++ [NUL]) -> ~ In NUL v ->
    acond t (row_find v parsed_rows) ->
    evt rsegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 p0 (Z_to_bv 64 t)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x145fc) fc None m' (seg_rom rsegs)).
  Proof.
    intros m' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 MI FR ST MU WM GP HV HVn AC.
    assert (TL : forall xa0', evt rsegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 p0 (Z_to_bv 64 (Z.min t 64 - 1))
               xa0' xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x1460c) fc None m' (seg_rom rsegs))).
    { intros xa0'. zstep. zstep. zstep.
      change (Z_to_bv 64 140480) with (Z_to_bv 64 (140480 + 24 * Z.of_nat 0)).
      change (Z_to_bv 64 22) with (Z_to_bv 64 (Z.of_nat (length parsed_rows))).
      eapply (rows_loop parsed_rows 0); [reflexivity | discriminate | exact rows_ok | exact GP | exact MI | exact FR |
                                         exact ST | exact MU | exact WM | exact HV | exact HVn | exact AC]. }
    zstep. zstep. if_cases B1.
    - zify_cond B1. rewrite ?ca_signed_small in B1 by lia.
      zstep. rewrite ?ca_swrap32_id by lia.
      first [ match goal with |- context [Z_to_bv 64 (t + ?c)] => replace (t + c) with (Z.min t 64 - 1) by lia end
            | match goal with |- context [Z_to_bv 64 (t - 1)] => replace (t - 1) with (Z.min t 64 - 1) by lia end ].
      apply TL.
    - zify_cond B1. rewrite ?ca_signed_small in B1 by lia.
      zstep. zstep.
      replace (Z_to_bv 64 63) with (Z_to_bv 64 (Z.min t 64 - 1)) by (f_equal; lia).
      apply TL.
  Qed.
End Main.

Theorem check_arity_holds : strcmp_contract -> strcspn_contract -> strncmp_contract -> bcmp_contract -> check_arity_contract.
Proof.
  intros SC SCS SNC BC.
  pose proof SC as SC'. unfold strcmp_contract in SC'. unfold strcspn_contract in SCS. unfold strncmp_contract in SNC.
  unfold check_arity_contract, CHECK_ARITY, CHECK_ARITY_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros t q nc fn0 ww p0 v can MI ST LO IE GG GU GPB GGR HNC HNCB HFN GGQ HQ HQB HT HTB HTD HWW HWWD HWS AOK.
  unfold outside_stack, disjoint_from, WORDS_N, WORDS_W, GOT_GREC, G_REC, GOT_GQUIT, G_QUIT, REC_NCALLS,
    REC_CALLS, CALL_FN, IMG_END, G_PARSED, GOT_GUARD, GUARD in *.
  change (212296 + 8) with 212304 in HNCB. change (212296 + 16 + 0) with 212312 in HFN.
  apply bytes_ro4 in HTB. apply bytes_ro8 in HWW. apply bytes_ro8 in GGR. apply bytes_ro8 in GGQ.
  apply bytes_ro4 in HNCB. apply bytes_ro4 in HQB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  assert (LGP : Z.of_nat (length g_parsed_bytes) = 528) by (vm_compute; reflexivity).
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 112%nat ST.
  do 14 zstep.
  match type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (j0 := j) in FR; clearbody j0 end.
  match type of MI with mem_inv _ ?mm => rename mm into m0 end.
  assert (HFN' : 0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 212312 (le4 (Z_to_bv 64 fn0))).
  { intros N. destruct (HFN N) as [F1 F2]. split; [exact F1|].
    eapply bytes_at_transport; [exact F2 | exact MU | cbn [disjoint_from]; simpl_sizes; slia]. }
  clear HFN.
  zstep. rewrite ca_sx32_small by lia.
  zstep. if_cases B0.
  { zify_cond B0. eapply ret_ok; eassumption. }
  zify_cond B0. assert (HT1 : 1 <= t <= 4096) by lia.
  destruct (HWS ltac:(lia)) as (HW1 & HW2 & [HW3 HW4] & HW5). clear HWS.
  unfold outside_stack, disjoint_from in HW2, HW5.
  apply (bytes_at_transport rsegs [(lo, bv_unsigned sp)] m m0) in HW1; [| exact MU | cbn [disjoint_from]; simpl_sizes; slia].
  apply (bytes_at_transport rsegs [(lo, bv_unsigned sp)] m m0) in HW3; [| exact MU | cbn [disjoint_from]; simpl_sizes; slia].
  apply bytes_ro8 in HW1.
  pose proof (bytes_at_bound _ _ _ _ HW3) as BV. rewrite length_app in BV. cbn [length] in BV.
  do 6 zstep.
  rewrite (ca_sx32_small nc) by lia.
  match goal with |- evt ?segs ?Q (MS ?R ?F0 _ ?fc0 ?rv ?mm ?ro) =>
    assert (K : q <> 0 \/ 0 < nc -> evt segs Q (MS R F0 (Z_to_bv 64 0x14574) fc0 rv mm ro)) end.
  { intros ACT.
    zstep. zstep.
    zstep. if_cases B2.
    - zify_cond B2. pos_false_tac.
      assert (AC : acond t (row_find v parsed_rows)).
      { apply (arity_cont t v q nc fn0 AOK); [lia | lia | intros (N & _); lia]. }
      eapply cont_ok; eassumption.
    - zify_cond B2.
      destruct (HFN' ltac:(lia)) as [HFR HFB]. apply bytes_ro4 in HFB.
      zstep. rewrite (ca_sx32_small fn0) by lia.
      zstep. zstep. if_cases Br3.
      + zify_cond Br3.
        assert (AC : acond t (row_find v parsed_rows)).
        { apply (arity_cont t v q nc fn0 AOK); [lia | lia | unfold REC_BROADCAST; intros (_ & N & _); lia]. }
        eapply cont_ok; eassumption.
      + zify_cond Br3.
        pose proof (lit_facts m0 0x1067c MI ltac:(vm_compute; reflexivity)) as ([HL1 HL1n] & _ & _ & _).
        pose proof (lit_facts m0 0x104e2 MI ltac:(vm_compute; reflexivity)) as ([HL2 HL2n] & _ & _ & _).
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply SC' with (sx := v) (sy := img_str 0x1067c).
          - exact HW3.
          - exact HW4.
          - rewrite unsigned_lit by lia. exact HL1.
          - exact HL1n. }
        intros ms' (r1 & x11 & x12 & x13 & E & Hr1). subst ms'. fix_ret.
        zstep. if_cases Br4.
        { eapply ret_ok; eassumption. }
        zify_cond Br4.
        assert (EQ1 : bytes_eqb v (img_str 0x1067c) = false).
        { destruct (bytes_eqb v (img_str 0x1067c)) eqn:E1; [|reflexivity].
          exfalso. apply Br4, bv0_iff, Hr1, bytes_eqb_iff, E1. }
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply SC' with (sx := v) (sy := img_str 0x104e2).
          - exact HW3.
          - exact HW4.
          - rewrite unsigned_lit by lia. exact HL2.
          - exact HL2n. }
        intros ms' (r2 & y11 & y12 & y13 & E & Hr2). subst ms'. fix_ret.
        zstep. if_cases Br5.
        { eapply ret_ok; eassumption. }
        zify_cond Br5.
        assert (EQ2 : bytes_eqb v (img_str 0x104e2) = false).
        { destruct (bytes_eqb v (img_str 0x104e2)) eqn:E2; [|reflexivity].
          exfalso. apply Br5, bv0_iff, Hr2, bytes_eqb_iff, E2. }
        pose proof (lit_at m0 67148 (str [32; 9] ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HSP.
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply SCS with (str := v) (slack := []) (set := str [32; 9]) (lo := lo) (can := can).
          - exact HW3.
          - exact HW4.
          - intros Hl. cbn in Hl. lia.
          - rewrite unsigned_lit by lia. exact HSP.
          - apply notin_nul_lit. vm_compute. reflexivity.
          - exact GG.
          - exact GU.
          - rewrite unsigned_lit by lia. exact ST.
          - rewrite unsigned_lit by lia. lia.
          - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
          - rewrite unsigned_lit by lia. left. cbn. lia.
          - unfold CSPN_SSP_GOT. left. lia.
          - unfold CSPN_SSP_GUARD. left. lia.
          - exact MI. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MU2 & WM2 & MI2 & ST2).
        subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. clear HSP.
        transport_after_call rsegs m0 m2 MU2 WM2.
        clear MU2 WM2 MI.
        fix_ret.
        pose proof (cspn_len_le (str [32; 9]) v) as CL.
        assert (AC2 : prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false \/
                      cspn_len (str [32; 9]) v <> 10%nat -> prefixb v (str [99; 111; 110; 110; 101; 99; 116]) = false \/
                      cspn_len (str [32; 9]) v <> 7%nat -> acond t (row_find v parsed_rows)).
        { intros P10 P7. apply (arity_cont t v q nc fn0 AOK); [lia | lia |].
          intros (_ & _ & PO). rewrite passed_on_false in PO; [discriminate PO | exact EQ1 | exact EQ2 | |].
          - destruct P7 as [P7|P7]; [apply vp_pre; exact P7 | apply vp_len; unfold str; cbn [map length]; exact P7].
          - destruct P10 as [P10|P10]; [apply vp_pre; exact P10 | apply vp_len; unfold str; cbn [map length]; exact P10]. }
        zstep. zstep. if_cases Br6.
        * zify_cond Br6. try rewrite Z.mod_small in Br6 by lia.
          zstep. zstep. zstep. zstep. zstep.
          pose proof (lit_at m2 66953 (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL])
                        MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HK.
          destruct (ca_strncmp_prefix v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) (str [32; 37; 115; 32; 37; 115] ++ [NUL])
                      HW4 ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate)) as (vv & Hv & Hv0).
          eapply evt_cut.
          { eapply SNC with (ls := v ++ [NUL])
              (rs := str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL]) (v := vv).
            - exact HW3.
            - rewrite unsigned_lit by lia. exact HK.
            - replace (bv_unsigned (Z_to_bv 64 10)) with (Z.of_nat (length (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116])))
                by reflexivity. exact Hv.
            - exact MI2. }
          intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MU3 & WM3 & MI3 & HB1 & HB2).
          subst ms'. clear HB1 HB2 HK.
          transport_after_call rsegs m2 m3 MU3 WM3.
          clear MU3 WM3 MI2.
          fix_ret.
          pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
          zstep. if_cases Br7.
          { eapply ret_ok; eassumption. }
          zify_cond Br7.
          assert (VN : vv <> 0) by (intros ->; apply Br7; reflexivity).
          assert (PF : prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116]) = false).
          { destruct (prefixb v (str [100; 105; 115; 99; 111; 110; 110; 101; 99; 116])) eqn:P; [|reflexivity].
            exfalso. apply VN, Hv0, prefixb_iff, P. }
          assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [left; exact PF | right; lia]).
          eapply cont_ok; eassumption.
        * zify_cond Br6. try rewrite Z.mod_small in Br6 by lia.
          zstep. zstep. if_cases Br8.
          -- zify_cond Br8. try rewrite Z.mod_small in Br8 by lia.
             assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [right; lia | right; lia]).
             eapply cont_ok; eassumption.
          -- zify_cond Br8. try rewrite Z.mod_small in Br8 by lia.
             zstep. zstep. zstep. zstep. zstep. zstep.
             pose proof (lit_at m2 67069 (str [99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL])
                           MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HK.
             destruct (ca_strncmp_prefix v (str [99; 111; 110; 110; 101; 99; 116]) (str [32; 37; 115; 32; 37; 115] ++ [NUL])
                         HW4 ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate)) as (vv & Hv & Hv0).
             eapply evt_cut.
             { eapply SNC with (ls := v ++ [NUL])
                 (rs := str [99; 111; 110; 110; 101; 99; 116] ++ str [32; 37; 115; 32; 37; 115] ++ [NUL]) (v := vv).
               - exact HW3.
               - rewrite unsigned_lit by lia. exact HK.
               - replace (bv_unsigned (Z_to_bv 64 7)) with (Z.of_nat (length (str [99; 111; 110; 110; 101; 99; 116])))
                   by reflexivity. exact Hv.
               - exact MI2. }
             intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & E & MU3 & WM3 & MI3 & HB1 & HB2).
             subst ms'. clear HB1 HB2 HK.
             transport_after_call rsegs m2 m3 MU3 WM3.
             clear MU3 WM3 MI2.
             fix_ret.
             pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
             zstep. if_cases Br7.
             { eapply ret_ok; eassumption. }
             zify_cond Br7.
             assert (VN : vv <> 0) by (intros ->; apply Br7; reflexivity).
             assert (PF : prefixb v (str [99; 111; 110; 110; 101; 99; 116]) = false).
             { destruct (prefixb v (str [99; 111; 110; 110; 101; 99; 116])) eqn:P; [|reflexivity].
               exfalso. apply VN, Hv0, prefixb_iff, P. }
             assert (AC : acond t (row_find v parsed_rows)) by (apply AC2; [right; lia | left; exact PF]).
             eapply cont_ok; eassumption. }
  zstep. if_cases B1.
  - zify_cond B1. apply K. left. intros Q0. apply B1. apply ca_sx32_zero; [lia | exact Q0].
  - zify_cond B1. apply ca_sx32_zero in B1; [|lia].
    zstep. if_cases B2.
    + zify_cond B2. pos_false_tac. eapply ret_ok; eassumption.
    + zify_cond B2. apply K. right. lia.
Qed.
