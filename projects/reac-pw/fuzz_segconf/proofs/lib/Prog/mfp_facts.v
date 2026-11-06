(** m_file's model, split the way the compiled loops compute it (build-independent: SegModel and
    Prog/mfu_facts.v only, so the UBSan twin's walk uses the same lemmas). Index forms of the inline loops: the
    blank test (the shift mask 0x100002200 of 0x140c8), the strip (forward then backward over [s, e)), the comment
    cut (0x140e0-0x14118), the fold (0x14328 / 0x14508), the quotes (0x142b8-0x142ec); SegModel.memchr; and the case
    equations of m_line, m_header (= mfu_facts.mh_find after its checks) and m_key (= mfu_facts.mk_disp). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import mfu_facts.
Import ListNotations.
Open Scope Z_scope.

(** ** Bytes and lists *)
Lemma blank_gt32 : forall c, 32 < c -> blank c = false.
Proof.
  intros c H. unfold blank.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
Lemma blank_mask : forall c, 0 <= c <= 32 -> blank c = (Z.land (Z.shiftr 0x100002200 c) 1 =? 1).
Proof.
  intros c Hc.
  assert (E : exists n, c = Z.of_nat n /\ (n <= 32)%nat) by (exists (Z.to_nat c); split; lia).
  destruct E as [n [-> Hn]]. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
Lemma hd0_skipn : forall (l : list Z) i, hd0 (skipn i l) = nth i l 0.
Proof.
  intros l; induction l as [|x r IH]; intros [|i]; cbn [skipn nth hd0]; try reflexivity. apply IH.
Qed.
Lemma slice_slice : forall (l : list Z) i j a b, (a <= b)%nat -> (b <= j - i)%nat ->
  slice a b (slice i j l) = slice (i + a) (i + b) l.
Proof.
  intros l i j a b Hab Hb. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite (Nat.min_l (b - a) (j - i - a)) by lia.
  replace (i + b - (i + a))%nat with (b - a)%nat by lia. rewrite (Nat.add_comm a i). reflexivity.
Qed.
Lemma slice_nth : forall (l : list Z) i j k, (k < j - i)%nat -> (j <= length l)%nat ->
  nth k (slice i j l) 0 = nth (i + k) l 0.
Proof.
  intros l i j k Hk Hj. unfold slice. rewrite nth_firstn, nth_skipn.
  destruct (Nat.ltb_spec k (j - i)); [reflexivity|lia].
Qed.
Lemma slice_length : forall (l : list Z) i j, (i <= j <= length l)%nat -> length (slice i j l) = (j - i)%nat.
Proof.
  intros l i j H. unfold slice. rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.
(** The line is a prefix of the text left. *)
Lemma mff_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma mf_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (mff_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [rewrite <- E; reflexivity|]. apply app_nth1. exact Hi.
Qed.
Lemma mf_line_firstn : forall rest o k, (o + k <= length (mf_line rest))%nat ->
  firstn k (skipn o rest) = slice o (o + k) (mf_line rest).
Proof.
  intros rest o k H. destruct (mff_line_split rest) as [R E].
  transitivity (firstn k (skipn o (mf_line rest ++ R))); [rewrite <- E; reflexivity|].
  unfold slice. replace (o + k - o)%nat with k by lia.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (k - (length (mf_line rest) - o))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.
Lemma mf_line_nulfree : forall rest, ~ In 0 rest -> ~ In 0 (mf_line rest) /\ ~ In 0 (mf_rest rest).
Proof.
  intros rest H. destruct (mf_line_rest rest) as [[E _]|[E [ER _]]].
  - split; intros Hin; apply H; rewrite E; apply in_or_app.
    + left. exact Hin.
    + right. right. exact Hin.
  - split; [intros Hin; apply H; rewrite E; exact Hin|rewrite ER; intros []].
Qed.

(** memchr: the first index of c, or none. *)
Lemma memchr_some : forall (l : list Z) c i, memchr l c = Some i ->
  (i < length l)%nat /\ nth i l 0 = c /\ (forall k, (k < i)%nat -> nth k l 0 <> c).
Proof.
  induction l as [|b r IH]; intros c i E; cbn [memchr] in E; [discriminate|].
  destruct (Z.eqb_spec b c) as [Hb|Hb].
  - injection E as <-. split; [cbn [length]; lia|]. split; [exact Hb|]. intros k Hk. lia.
  - destruct (memchr r c) as [i'|] eqn:Er; cbn [option_map] in E; [|discriminate].
    injection E as <-. destruct (IH c i' Er) as (H1 & H2 & H3).
    split; [cbn [length]; lia|]. split; [exact H2|].
    intros [|k] Hk; [exact Hb|exact (H3 k ltac:(lia))].
Qed.
Lemma memchr_none : forall (l : list Z) c, memchr l c = None -> forall k, (k < length l)%nat -> nth k l 0 <> c.
Proof.
  induction l as [|b r IH]; intros c E k Hk; cbn [length] in Hk; [lia|].
  cbn [memchr] in E. destruct (Z.eqb_spec b c) as [Hb|Hb]; [discriminate|].
  destruct (memchr r c) eqn:Er; cbn [option_map] in E; [discriminate|].
  destruct k as [|k]; [exact Hb|exact (IH c Er k ltac:(lia))].
Qed.
Lemma memchr_idx : forall (l : list Z) c i, (i < length l)%nat -> nth i l 0 = c ->
  (forall k, (k < i)%nat -> nth k l 0 <> c) -> memchr l c = Some i.
Proof.
  induction l as [|b r IH]; intros c i Hi Hc Hk; cbn [length] in Hi; [lia|].
  cbn [memchr]. destruct i as [|i].
  - change (b = c) in Hc. subst c. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (Hk 0%nat); [lia|exact Hb]|].
    rewrite (IH c i); [reflexivity|lia|exact Hc|].
    intros k Hk' Ek. apply (Hk (S k)); [lia|exact Ek].
Qed.
Lemma memchr_none_idx : forall (l : list Z) c, (forall k, (k < length l)%nat -> nth k l 0 <> c) -> memchr l c = None.
Proof.
  induction l as [|b r IH]; intros c H; [reflexivity|]. cbn [memchr].
  destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (H 0%nat); [cbn [length]; lia|exact Hb]|].
  rewrite IH; [reflexivity|]. intros k Hk Ek. apply (H (S k)); [cbn [length]; lia|exact Ek].
Qed.

(** ** Strip: the forward loop stops at the first non-blank i, the backward loop at j (u[j - 1] not blank, or
    j = i). *)
Definition all_blank (u : list Z) (a b : nat) : Prop := forall k, (a <= k < b)%nat -> blank (nth k u 0) = true.

Lemma dropwhile_blank_idx : forall u i, (i <= length u)%nat -> all_blank u 0 i ->
  (i = length u \/ blank (nth i u 0) = false) -> dropwhile blank u = skipn i u.
Proof.
  unfold all_blank.
  induction u as [|x r IH]; intros i Hi Hb Hs; [destruct i; reflexivity|].
  cbn [dropwhile]. destruct i as [|i].
  - destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate|].
    change (blank x = false) in Hs. rewrite Hs. reflexivity.
  - assert (Hx : blank x = true) by exact (Hb 0%nat ltac:(lia)). rewrite Hx. cbn [skipn].
    cbn [length] in Hi. apply IH; [lia| |].
    + intros k Hk. exact (Hb (S k) ltac:(lia)).
    + destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right; exact Hs].
Qed.
Lemma h_strip_idx : forall u i j, (i <= j <= length u)%nat -> all_blank u 0 i ->
  (i = length u \/ blank (nth i u 0) = false) -> all_blank u j (length u) ->
  (j = i \/ blank (nth (j - 1) u 0) = false) ->
  h_strip u = slice i j u.
Proof.
  unfold all_blank. intros u i j [Hij Hj] Hb0 Hs Hb1 He. unfold h_strip.
  rewrite (dropwhile_blank_idx u i) by first [lia | assumption].
  assert (Lw : length (rev (skipn i u)) = (length u - i)%nat) by (rewrite length_rev, length_skipn; reflexivity).
  rewrite (dropwhile_blank_idx (rev (skipn i u)) (length u - j)).
  - rewrite skipn_rev, rev_involutive, length_skipn. unfold slice. f_equal. lia.
  - rewrite Lw. lia.
  - intros k Hk. rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    apply Hb1. lia.
  - destruct (Nat.eq_dec j i) as [->|Hne]; [left; rewrite Lw; reflexivity|right].
    destruct He as [He|He]; [lia|].
    rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    replace (i + (length u - i - S (length u - j)))%nat with (j - 1)%nat by lia. exact He.
Qed.
(** The stripped bytes are nonempty iff the forward loop stopped inside; then the first and last are not blank. *)
Lemma mff_dw_hd : forall l, match dropwhile blank l with [] => True | x :: _ => blank x = false end.
Proof.
  induction l as [|x r IH]; [exact I|]. cbn [dropwhile]. destruct (blank x) eqn:E; [exact IH|exact E].
Qed.
Lemma mff_dw_suffix : forall l, exists p, l = p ++ dropwhile blank l.
Proof.
  induction l as [|x r [p IH]]; [exists []; reflexivity|]. cbn [dropwhile].
  destruct (blank x); [exists (x :: p); cbn [app]; rewrite <- IH; reflexivity|exists []; reflexivity].
Qed.
Lemma h_strip_ends : forall u b r, h_strip u = b :: r -> blank b = false /\ blank (last (b :: r) 0) = false.
Proof.
  intros u b r H. unfold h_strip in H.
  pose proof (mff_dw_hd u) as HE.
  pose proof (mff_dw_hd (rev (dropwhile blank u))) as HD.
  destruct (mff_dw_suffix (rev (dropwhile blank u))) as [p Hp].
  set (D := dropwhile blank (rev (dropwhile blank u))) in *. clearbody D.
  set (E := dropwhile blank u) in *. clearbody E.
  destruct D as [|x D']; [cbn [rev] in H; discriminate|].
  split.
  - assert (EE : E = b :: (r ++ rev p)).
    { rewrite <- (rev_involutive E), Hp, rev_app_distr, H. reflexivity. }
    rewrite EE in HE. exact HE.
  - rewrite <- H. cbn [rev]. rewrite last_last. exact HD.
Qed.

(** ** The comment cut: the first q with a mark at q and q = 0 or a space or tab at q - 1. *)
Definition cut_at (l : list Z) (q : nat) : bool :=
  is_mark (nth q l 0) && ((q =? 0)%nat || sp_tab (nth (q - 1) l 0)).
(** h_cut_go with its accumulator: the test at position k given the flag first and the byte prev before l. *)
Definition mff_cut_at (first : bool) (prev : Z) (l : list Z) (k : nat) : bool :=
  is_mark (nth k l 0) && match k with O => first || sp_tab prev | S k' => sp_tab (nth k' l 0) end.
Lemma mff_cut_go : forall l first prev q, (q <= length l)%nat ->
  (forall k, (k < q)%nat -> mff_cut_at first prev l k = false) ->
  (q = length l \/ mff_cut_at first prev l q = true) -> h_cut_go first prev l = firstn q l.
Proof.
  induction l as [|x r IH]; intros first prev q Hq Hk Hs; [destruct q; reflexivity|].
  cbn [h_cut_go]. destruct q as [|q].
  - destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate|].
    change (is_mark x && (first || sp_tab prev) = true) in Hs. rewrite Hs. reflexivity.
  - pose proof (Hk 0%nat ltac:(lia)) as H0. change (is_mark x && (first || sp_tab prev) = false) in H0.
    rewrite H0. cbn [firstn]. f_equal. cbn [length] in Hq. apply IH; [lia| |].
    + intros k Hk'. specialize (Hk (S k) ltac:(lia)). unfold mff_cut_at in Hk |- *.
      destruct k; exact Hk.
    + destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right].
      unfold mff_cut_at in Hs |- *. destruct q; exact Hs.
Qed.
Lemma h_cut_idx : forall l q, (q <= length l)%nat -> (forall k, (k < q)%nat -> cut_at l k = false) ->
  (q = length l \/ cut_at l q = true) -> h_cut_comment l = firstn q l.
Proof.
  intros l q Hq Hk Hs. unfold h_cut_comment. apply mff_cut_go; [exact Hq| |].
  - intros k Hk'. specialize (Hk k Hk'). unfold cut_at, mff_cut_at in *.
    destruct k as [|k]; [exact Hk|]. replace (S k - 1)%nat with k in Hk by lia. exact Hk.
  - destruct Hs as [Hs|Hs]; [left; exact Hs|right]. unfold cut_at, mff_cut_at in *.
    destruct q as [|q]; [exact Hs|]. replace (S q - 1)%nat with q in Hs by lia. exact Hs.
Qed.

(** ** The fold: lower of each of the first min(n, cap - 1) bytes. *)
Lemma lower_byte : forall c, 0 <= c < 256 -> 0 <= lower c < 256 /\ (lower c = 0 <-> c = 0).
Proof.
  intros c Hc. unfold lower.
  destruct (Z.leb_spec 65 c), (Z.leb_spec c 90); cbn [andb]; split; try lia; split; intros; lia.
Qed.
(** lower as the code computes it: c + 32 when (c - 'A') is below 26 as a 64-bit unsigned value. *)
Lemma lower_bin : forall c, 0 <= c < 256 -> lower c = c + (if (c - 65) mod 2 ^ 64 <? 26 then 32 else 0).
Proof.
  intros c Hc. unfold lower. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.leb_spec 65 c) as [H1|H1].
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec c 90), (Z.ltb_spec (c - 65) 26); cbn [andb]; lia.
  - rewrite <- (Z_mod_plus_full (c - 65) 1 18446744073709551616). rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (c - 65 + 1 * 18446744073709551616) 26); cbn [andb]; lia.
Qed.
Lemma h_fold_length : forall v cap, length (h_fold v cap) = Nat.min (length v) (cap - 1).
Proof.
  intros v cap. unfold h_fold. rewrite length_map, length_firstn. apply Nat.min_comm.
Qed.
Lemma h_fold_nth : forall v cap k, (k < length (h_fold v cap))%nat -> nth k (h_fold v cap) 0 = lower (nth k v 0).
Proof.
  intros v cap k Hk. unfold h_fold in *.
  rewrite (@nth_indep Z (map lower (firstn (cap - 1) v)) k 0 (lower 0)) by exact Hk. rewrite map_nth. f_equal.
  rewrite length_map, length_firstn in Hk. pose proof (Nat.le_min_l (cap - 1) (length v)).
  rewrite nth_firstn. destruct (Nat.ltb_spec k (cap - 1)); [reflexivity|lia].
Qed.
Lemma h_fold_props : forall v cap, ~ In 0 v -> Forall (fun x => 0 <= x < 256) v ->
  ~ In 0 (h_fold v cap) /\ Forall (fun x => 0 <= x < 256) (h_fold v cap).
Proof.
  intros v cap H0 HF. unfold h_fold. rewrite Forall_forall in HF.
  assert (Hin : forall x, In x (firstn (cap - 1) v) -> In x v).
  { intros x Hx. rewrite <- (firstn_skipn (cap - 1) v). apply in_or_app. left. exact Hx. }
  split.
  - intros Hm. apply in_map_iff in Hm. destruct Hm as [x [Hx Hxin]].
    apply Hin in Hxin. destruct (lower_byte x (HF x Hxin)) as [_ Hl].
    assert (x = 0) as -> by (apply Hl; exact Hx). exact (H0 Hxin).
  - apply Forall_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- Hxin]].
    apply Hin in Hxin. exact (proj1 (lower_byte x (HF x Hxin))).
Qed.

(** ** The role words (the table m_key.words) *)
Lemma leqb_eq : forall a b, leqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [leqb]; split; intros H; try reflexivity; try discriminate.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as -> ->. rewrite Z.eqb_refl. cbn [andb]. apply IH. reflexivity.
Qed.
Lemma h_role_word_eq : forall low,
  h_role_word low =
  if (length S_auto =? length low)%nat && leqb (firstn (length low) S_auto) low then Some 0 else
  if (length S_master =? length low)%nat && leqb (firstn (length low) S_master) low then Some 1 else
  if (length S_slave =? length low)%nat && leqb (firstn (length low) S_slave) low then Some 2 else
  if (length S_tap =? length low)%nat && leqb (firstn (length low) S_tap) low then Some 3 else
  if (length S_box =? length low)%nat && leqb (firstn (length low) S_box) low then Some 4 else None.
Proof. intros low. reflexivity. Qed.

(** ** The quotes: one matching pair, first and last byte. *)
Lemma mff_last_nth : forall (v : list Z) d, last v d = nth (pred (length v)) v d.
Proof. induction v as [|x r IH]; intros d; [reflexivity|]. destruct r as [|y r]; [reflexivity|]. exact (IH d). Qed.
Lemma mff_rl_tl : forall (v : list Z), removelast (tl v) = slice 1 (length v - 1) v.
Proof.
  intros [|x r]; [reflexivity|]. unfold slice. rewrite removelast_firstn_len. cbn [tl skipn length].
  f_equal. lia.
Qed.
Lemma h_unquote_idx : forall v,
  h_unquote v =
  if (2 <=? length v)%nat && ((nth 0 v 0 =? DQ) || (nth 0 v 0 =? SQ)) && (nth (length v - 1) v 0 =? nth 0 v 0)
  then slice 1 (length v - 1) v else v.
Proof.
  intros v. unfold h_unquote.
  assert (E1 : hd0 v = nth 0 v 0) by (destruct v; reflexivity).
  rewrite (mff_last_nth v 0), E1, mff_rl_tl.
  replace (pred (length v)) with (length v - 1)%nat by lia. reflexivity.
Qed.

(** ** The case equations *)
Lemma m_line_long : forall c cur n l, (512 <= length l)%nat ->
  m_line (c, cur) n l = (m_refuse c n false, if hd0 (dropwhile blank l) =? LBR then None else cur).
Proof.
  intros c cur n l H. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
Qed.
Lemma m_line_empty : forall c cur n l, (length l < 512)%nat -> h_strip (h_cut_comment l) = [] ->
  m_line (c, cur) n l = (c, cur).
Proof.
  intros c cur n l H1 H2. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1), H2. reflexivity.
Qed.
Lemma m_line_hdr : forall c cur n l, (length l < 512)%nat -> hd0 (h_strip (h_cut_comment l)) = LBR ->
  m_line (c, cur) n l = m_header c (h_strip (h_cut_comment l)) n.
Proof.
  intros c cur n l H1 H2. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1).
  revert H2. destruct (h_strip (h_cut_comment l)) as [|b s]; cbn [hd0]; intros H2; [discriminate|].
  subst b. reflexivity.
Qed.
Lemma m_line_key : forall c cur n l, (length l < 512)%nat -> h_strip (h_cut_comment l) <> [] ->
  hd0 (h_strip (h_cut_comment l)) <> LBR ->
  m_line (c, cur) n l = (m_key c cur (h_strip (h_cut_comment l)) n, cur).
Proof.
  intros c cur n l H1 H2 H3. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1).
  revert H2 H3. destruct (h_strip (h_cut_comment l)) as [|b s]; intros H2 H3; [congruence|].
  cbn [hd0] in H3. rewrite (proj2 (Z.eqb_neq b LBR) H3). reflexivity.
Qed.

(** m_header after its checks is mh_find; every failed check refuses with cur = NULL. *)
Lemma m_header_find : forall c l line ci,
  memchr l RBR = Some ci -> S ci = length l ->
  (8 <= length (h_strip (slice 1 ci l)))%nat ->
  ieq (firstn 7 (h_strip (slice 1 ci l))) S_segment = true ->
  sp_tab (nth 7 (h_strip (slice 1 ci l)) 0) = true ->
  (0 < length (h_strip (skipn 7 (h_strip (slice 1 ci l)))) < 16)%nat ->
  m_header c l line = mh_find c (h_strip (skipn 7 (h_strip (slice 1 ci l)))) line.
Proof.
  intros c l line ci H1 H2 H3 H4 H5 H6. unfold m_header. rewrite H1. cbv beta iota zeta.
  assert (E2 : (S ci =? length l)%nat = true) by (apply Nat.eqb_eq; exact H2). rewrite E2.
  rewrite (proj2 (Nat.ltb_ge _ _) H3), H4, H5.
  assert (E6 : (length (h_strip (skipn 7 (h_strip (slice 1 ci l)))) =? 0)%nat = false)
    by (apply Nat.eqb_neq; lia).
  assert (E7 : (16 <=? length (h_strip (skipn 7 (h_strip (slice 1 ci l)))))%nat = false)
    by (apply Nat.leb_gt; lia).
  rewrite E6, E7. reflexivity.
Qed.
Lemma m_header_refuse : forall c l line,
  (forall ci, memchr l RBR = Some ci -> S ci = length l ->
     (8 <= length (h_strip (slice 1 ci l)))%nat ->
     ieq (firstn 7 (h_strip (slice 1 ci l))) S_segment = true ->
     sp_tab (nth 7 (h_strip (slice 1 ci l)) 0) = true ->
     length (h_strip (skipn 7 (h_strip (slice 1 ci l)))) = 0%nat \/
     (16 <= length (h_strip (skipn 7 (h_strip (slice 1 ci l)))))%nat) ->
  m_header c l line = (m_refuse c line false, None).
Proof.
  intros c l line H. unfold m_header.
  destruct (memchr l RBR) as [ci|] eqn:E1; [|reflexivity]. cbv beta iota zeta.
  destruct (S ci =? length l)%nat eqn:E2; [|reflexivity].
  destruct (length (h_strip (slice 1 ci l)) <? 8)%nat eqn:E3; [reflexivity|].
  destruct (ieq (firstn 7 (h_strip (slice 1 ci l))) S_segment) eqn:E4; [|reflexivity].
  destruct (sp_tab (nth 7 (h_strip (slice 1 ci l)) 0)) eqn:E5; [|reflexivity].
  apply Nat.ltb_ge in E3. apply Nat.eqb_eq in E2.
  destruct (H ci eq_refl E2 E3 E4 E5) as [H6|H6].
  - rewrite H6. reflexivity.
  - rewrite (proj2 (Nat.leb_le _ _) H6), orb_true_r. reflexivity.
Qed.

(** m_key with a cursor and an '=' is mk_disp of the stripped key and the unquoted stripped value; else it
    refuses. *)
Lemma m_key_disp : forall c gi l line ei, memchr l EQ = Some ei ->
  m_key c (Some gi) l line = mk_disp c gi (h_strip (firstn ei l)) (h_unquote (h_strip (skipn (S ei) l))) line.
Proof.
  intros c gi l line ei H. unfold m_key. rewrite H. reflexivity.
Qed.
Lemma m_key_refuse : forall c g l line, (memchr l EQ = None \/ g = None) -> m_key c g l line = m_refuse c line false.
Proof.
  intros c g l line H. unfold m_key.
  destruct H as [H|H]; [rewrite H; reflexivity|subst g; destruct (memchr l EQ); reflexivity].
Qed.
