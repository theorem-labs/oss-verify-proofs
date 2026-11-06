From Stdlib Require Import ZArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandTac check_reply_c strcmp_c strcspn_c strncmp_c bcmp_c check_arity_c.
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

Notation SGU sp gp tp F fc pc xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m :=
  (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition uinv (sp : word) (m0 : word -> option byte) (lo : Z) (saved : list cell) (A : Z) (SS : list byte)
    (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ (exists j, rw_cells rsegs m (bv_unsigned sp + -144) (CB 40 j :: saved)) /\
  stk rsegs m lo (bv_unsigned sp + -144) /\ munch [(lo, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m A (SS ++ [NUL]).

Definition upost (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z)
    (saved : list cell) (A : Z) (SS : list byte) (rmn rmx : Z) (xs2 : word) (ms' : machine_state) : Prop :=
  exists m' xra xs0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6,
    uinv sp m0 lo saved A SS m' /\
    ms' = SGU sp gp tp F fc 0x14b54 xra xs0 (Z_to_bv 64 rmx) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt0 xt1 xt2
            xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 rmn) xa7 xt3 xt4 xt5 xt6 m'.

Definition path_spec (fm pc : Z) : Prop :=
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (A : Z) (SS : list byte) (m0 : word -> option byte) (lo : Z)
         (saved : list cell),
    ~ In NUL SS -> Z.of_nat (length SS) <= 128 -> 0 < A -> A + Z.of_nat (length SS) + 1 <= lo ->
    0 <= lo -> lo + 144 <= bv_unsigned sp ->
    forall m rmn rmx xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xt3 xt4 xt5 xt6,
      uinv sp m0 lo saved A SS m -> row_arity SS fm = (rmn, rmx) ->
      evt rsegs (upost sp gp tp F fc m0 lo saved A SS rmn rmx xs2)
        (SGU sp gp tp F fc pc xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 A) xt0 xt1 xt2
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m).

Definition syn_path_spec : Prop := path_spec 0 0x14804.
Definition fmt_path_spec : Prop := path_spec 1 0x14770.
