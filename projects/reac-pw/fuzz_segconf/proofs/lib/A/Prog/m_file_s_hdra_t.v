(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA (HDR 0x862cc -> HFIND 0x86abc or TAIL 0x86cf8): the
   model facts its walk uses. Gallina only; no instruction is executed here. The HDRA segment lane of the G2 walk owner's G2.

   What the code computes, in index form over the stripped line sl = slice i j (mf_line rest), s = p + i, e = p + j
   (the G2 walk owner's guide/MF-CUTS-A.md section 4, S_MF_HDRA; listing m_file.fuzz_segconf.asan.s):
   - memchr(s, ']', e - s) 0x862d4: the index k of the first ']' of sl, or none;
   - close + 1 = e 0x862e4: S k = length sl;
   - the strip of [s + 1, close) 0x862e8-0x8648c: the forward loop (head 0x862fc) stops at the first non-blank q of
     [1, k) or at k, the backward loop (head 0x863ec) at r, sl[r - 1] not blank or r = q: the header bytes hb are
     slice q r sl (hda_strip_slice);
   - be - b >= 8 0x8649c, ieq(b, 7, "segment") 0x864b0, b[7] = '\t' or ' ' 0x864cc-0x864d8;
   - the strip of [b + 7, be) 0x864dc-0x86aa8 (heads 0x864ec, 0x86a64): the name nm = slice a z sl;
   - 0 < |nm| < 16 0x86aac / 0x86ab8.
   Each refusal is m_header's refusal (the hda_hdr_refuse_ lemmas), and the passed checks make m_header m_file_m.v's
   mh_find
   of the name (hda_hdr_find).

   Restated, statements and proofs, from the plain / image-B owner's plain lib/Prog/mfp_facts.v at dec616e11c2f (blank_gt32 :13,
   blank_mask :18, slice_slice :29, slice_nth :37, slice_length :43, mff_line_split :48, mf_line_nth :54,
   mf_line_firstn :59, memchr_some :78, memchr_none :89, memchr_idx :96, memchr_none_idx :106, all_blank :115,
   dropwhile_blank_idx :117, h_strip_idx :130, m_header_find :313, m_header_refuse :330) and lib/Prog/mfu_facts.v
   at dec616e11c2f (break_nl_spec :17, mf_line_rest :282); that tree's files Require the plain integration, so
   they are copied here with an hda_ prefix (the brief's rule: copy a plain lemma, cite its line). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_m.
Import ListNotations.
Open Scope Z_scope.

(* ============================== bytes and lists (mfp_facts.v) ============================== *)
Lemma hda_blank_gt32 : forall c, 32 < c -> blank c = false.
Proof.
  intros c H. unfold blank.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
(* the blank test of the loops: `bltu s3, x` (s3 = 32) then bit x of the mask s9 = 0x100002200 *)
Lemma hda_blank_mask : forall c, 0 <= c <= 32 -> blank c = (Z.land (Z.shiftr 0x100002200 c) 1 =? 1).
Proof.
  intros c Hc.
  assert (E : exists n, c = Z.of_nat n /\ (n <= 32)%nat) by (exists (Z.to_nat c); split; lia).
  destruct E as [n [-> Hn]]. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
Lemma hda_slice_slice : forall (l : list Z) i j a b, (a <= b)%nat -> (b <= j - i)%nat ->
  slice a b (slice i j l) = slice (i + a) (i + b) l.
Proof.
  intros l i j a b Hab Hb. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite (Nat.min_l (b - a) (j - i - a)) by lia.
  replace (i + b - (i + a))%nat with (b - a)%nat by lia. rewrite (Nat.add_comm a i). reflexivity.
Qed.
Lemma hda_slice_nth : forall (l : list Z) i j k, (k < j - i)%nat -> (j <= length l)%nat ->
  nth k (slice i j l) 0 = nth (i + k) l 0.
Proof.
  intros l i j k Hk Hj. unfold slice. rewrite nth_firstn, nth_skipn.
  destruct (Nat.ltb_spec k (j - i)); [reflexivity|lia].
Qed.
Lemma hda_slice_length : forall (l : list Z) i j, (i <= j <= length l)%nat -> length (slice i j l) = (j - i)%nat.
Proof.
  intros l i j H. unfold slice. rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.
Lemma hda_skipn_slice : forall (l : list Z) i j k, (k <= j - i)%nat ->
  skipn k (slice i j l) = slice (i + k) j l.
Proof.
  intros l i j k Hk. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (j - (i + k))%nat with (j - i - k)%nat by lia. rewrite (Nat.add_comm k i). reflexivity.
Qed.
Lemma hda_firstn_slice : forall (l : list Z) i j k, (k <= j - i)%nat ->
  firstn k (slice i j l) = slice i (i + k) l.
Proof.
  intros l i j k Hk. unfold slice. rewrite firstn_firstn.
  replace (i + k - i)%nat with k by lia. rewrite Nat.min_l by lia. reflexivity.
Qed.

(* ============================== the line (mfu_facts.v, mfp_facts.v) ============================== *)
Lemma hda_break_nl_spec : forall s l q, break_nl s = (l, q) ->
  ~ In NL l /\ (s = l ++ NL :: q \/ (s = l /\ q = [])).
Proof.
  induction s as [|b r IH]; intros l q E; cbn [break_nl] in E.
  - injection E as <- <-. split; [intros []|right; split; reflexivity].
  - destruct (Z.eqb_spec b NL) as [Hb|Hb].
    + injection E as <- <-. split; [intros []|left; subst b; reflexivity].
    + revert E. destruct (break_nl r) as [l1 q1] eqn:E1. intros E. injection E as <- <-.
      destruct (IH l1 q1 eq_refl) as [N1 [S1|[S1 Q1]]].
      * split; [intros [H|H]; [lia|exact (N1 H)]|left; rewrite S1; reflexivity].
      * split; [intros [H|H]; [lia|exact (N1 H)]|right; split; [rewrite S1; reflexivity|exact Q1]].
Qed.
Lemma hda_mf_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (hda_break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.
Lemma hda_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (hda_mf_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma hda_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (hda_line_split rest) as [R E].
  transitivity (length (mf_line rest ++ R)); [rewrite length_app; lia | rewrite <- E; lia].
Qed.
Lemma hda_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (hda_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [rewrite <- E; reflexivity|]. apply app_nth1. exact Hi.
Qed.
Lemma hda_line_firstn : forall rest o k, (o + k <= length (mf_line rest))%nat ->
  firstn k (skipn o rest) = slice o (o + k) (mf_line rest).
Proof.
  intros rest o k H. destruct (hda_line_split rest) as [R E].
  transitivity (firstn k (skipn o (mf_line rest ++ R))); [rewrite <- E; reflexivity|].
  unfold slice. replace (o + k - o)%nat with k by lia.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (k - (length (mf_line rest) - o))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.
(* the byte x of the stripped line sl = slice i j (mf_line rest) is the byte i + x of the text left *)
Lemma hda_sl_nth : forall rest i j x, (j <= length (mf_line rest))%nat -> (x < j - i)%nat ->
  nth x (slice i j (mf_line rest)) 0 = nth (i + x) rest 0.
Proof.
  intros rest i j x Hj Hx. rewrite hda_slice_nth by lia. symmetry. apply hda_line_nth. lia.
Qed.
(* a slice of the stripped line is a run of the text left, inside the line *)
Lemma hda_sl_run : forall rest i j a z, (i <= j <= length (mf_line rest))%nat -> (a <= z <= j - i)%nat ->
  slice a z (slice i j (mf_line rest)) = firstn (z - a) (skipn (i + a) rest) /\
  (i + a + (z - a) <= length (mf_line rest))%nat.
Proof.
  intros rest i j a z Hj Haz. split; [|lia].
  rewrite hda_slice_slice by lia. rewrite hda_line_firstn by lia. f_equal. lia.
Qed.

(* ============================== memchr (mfp_facts.v) ============================== *)
Lemma hda_memchr_some : forall (l : list Z) c i, memchr l c = Some i ->
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
Lemma hda_memchr_idx : forall (l : list Z) c i, (i < length l)%nat -> nth i l 0 = c ->
  (forall k, (k < i)%nat -> nth k l 0 <> c) -> memchr l c = Some i.
Proof.
  induction l as [|b r IH]; intros c i Hi Hc Hk; cbn [length] in Hi; [lia|].
  cbn [memchr]. destruct i as [|i].
  - change (b = c) in Hc. subst c. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (Hk 0%nat); [lia|exact Hb]|].
    rewrite (IH c i); [reflexivity|lia|exact Hc|].
    intros k Hk' Ek. apply (Hk (S k)); [lia|exact Ek].
Qed.
Lemma hda_memchr_none_idx : forall (l : list Z) c, (forall k, (k < length l)%nat -> nth k l 0 <> c) ->
  memchr l c = None.
Proof.
  induction l as [|b r IH]; intros c H; [reflexivity|]. cbn [memchr].
  destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (H 0%nat); [cbn [length]; lia|exact Hb]|].
  rewrite IH; [reflexivity|]. intros k Hk Ek. apply (H (S k)); [cbn [length]; lia|exact Ek].
Qed.
(* memchr's answer k (the first c, or k = length l when there is none), the wrapper's first_byte, as the model's *)
Lemma hda_memchr_of_first : forall (l : list Z) c k, (k <= length l)%nat ->
  (forall x, (x < k)%nat -> nth x l 0 <> c) -> ((k < length l)%nat -> nth k l 0 = c) ->
  memchr l c = if (k <? length l)%nat then Some k else None.
Proof.
  intros l c k Hk Hb Hc. destruct (Nat.ltb_spec k (length l)) as [Hlt|Hge].
  - apply hda_memchr_idx; [exact Hlt | exact (Hc Hlt) | exact Hb].
  - apply hda_memchr_none_idx. intros x Hx. apply Hb. lia.
Qed.

(* ============================== the strip (mfp_facts.v) ============================== *)
Definition hda_all_blank (u : list Z) (a b : nat) : Prop := forall k, (a <= k < b)%nat -> blank (nth k u 0) = true.

Lemma hda_dropwhile_blank_idx : forall u i, (i <= length u)%nat -> hda_all_blank u 0 i ->
  (i = length u \/ blank (nth i u 0) = false) -> dropwhile blank u = skipn i u.
Proof.
  unfold hda_all_blank.
  induction u as [|x r IH]; intros i Hi Hb Hs; [destruct i; reflexivity|].
  cbn [dropwhile]. destruct i as [|i].
  - destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate|].
    change (blank x = false) in Hs. rewrite Hs. reflexivity.
  - assert (Hx : blank x = true) by exact (Hb 0%nat ltac:(lia)). rewrite Hx. cbn [skipn].
    cbn [length] in Hi. apply IH; [lia| |].
    + intros k Hk. exact (Hb (S k) ltac:(lia)).
    + destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right; exact Hs].
Qed.
Lemma hda_h_strip_idx : forall u i j, (i <= j <= length u)%nat -> hda_all_blank u 0 i ->
  (i = length u \/ blank (nth i u 0) = false) -> hda_all_blank u j (length u) ->
  (j = i \/ blank (nth (j - 1) u 0) = false) ->
  h_strip u = slice i j u.
Proof.
  unfold hda_all_blank. intros u i j [Hij Hj] Hb0 Hs Hb1 He. unfold h_strip.
  rewrite (hda_dropwhile_blank_idx u i) by first [lia | assumption].
  assert (Lw : length (rev (skipn i u)) = (length u - i)%nat) by (rewrite length_rev, length_skipn; reflexivity).
  rewrite (hda_dropwhile_blank_idx (rev (skipn i u)) (length u - j)).
  - rewrite skipn_rev, rev_involutive, length_skipn. unfold slice. f_equal. lia.
  - rewrite Lw. lia.
  - intros k Hk. rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    apply Hb1. lia.
  - destruct (Nat.eq_dec j i) as [->|Hne]; [left; rewrite Lw; reflexivity|right].
    destruct He as [He|He]; [lia|].
    rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    replace (i + (length u - i - S (length u - j)))%nat with (j - 1)%nat by lia. exact He.
Qed.
(* what the two strip loops leave over the bytes [lo, hi) of u: the forward one at a (blanks before it, and a = hi
   or u[a] not blank), the backward one at z (blanks from it, and z = a or u[z - 1] not blank) *)
Definition hda_strip (u : list Z) (lo hi a z : nat) : Prop :=
  (lo <= a <= z)%nat /\ (z <= hi <= length u)%nat /\
  hda_all_blank u lo a /\ (a = hi \/ blank (nth a u 0) = false) /\
  hda_all_blank u z hi /\ (z = a \/ blank (nth (z - 1) u 0) = false).
Lemma hda_strip_slice : forall u lo hi a z, hda_strip u lo hi a z -> h_strip (slice lo hi u) = slice a z u.
Proof.
  intros u lo hi a z (H1 & H2 & H3 & H4 & H5 & H6).
  assert (L : length (slice lo hi u) = (hi - lo)%nat) by (apply hda_slice_length; lia).
  rewrite (hda_h_strip_idx (slice lo hi u) (a - lo) (z - lo)).
  - rewrite hda_slice_slice by lia. f_equal; lia.
  - rewrite L. lia.
  - intros k Hk. rewrite hda_slice_nth by lia. apply H3. lia.
  - destruct (Nat.eq_dec a hi) as [E|Hne]; [left; rewrite L; lia|].
    destruct H4 as [H4|H4]; [lia|]. right. rewrite hda_slice_nth by lia.
    replace (lo + (a - lo))%nat with a by lia. exact H4.
  - intros k Hk. rewrite L in Hk. rewrite hda_slice_nth by lia. apply H5. lia.
  - destruct (Nat.eq_dec z a) as [E|Hne]; [left; lia|].
    destruct H6 as [H6|H6]; [lia|]. right. rewrite hda_slice_nth by lia.
    replace (lo + (z - lo - 1))%nat with (z - 1)%nat by lia. exact H6.
Qed.
(* the forward loop's step and exits, the backward loop's step and exits, as the walk meets them *)
Lemma hda_all_blank_nil : forall u a, hda_all_blank u a a.
Proof. intros u a k Hk. lia. Qed.
Lemma hda_all_blank_snoc : forall u a b, hda_all_blank u a b -> blank (nth b u 0) = true -> hda_all_blank u a (S b).
Proof. intros u a b H Hb k Hk. destruct (Nat.eq_dec k b) as [->|Hne]; [exact Hb | apply H; lia]. Qed.
Lemma hda_all_blank_cons : forall u a b, hda_all_blank u (S a) b -> blank (nth a u 0) = true -> (a < b)%nat ->
  hda_all_blank u a b.
Proof. intros u a b H Ha _ k Hk. destruct (Nat.eq_dec k a) as [->|Hne]; [exact Ha | apply H; lia]. Qed.

(* ============================== m_header (mfp_facts.v) ============================== *)
Lemma hda_m_header_find : forall c l line ci,
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
Lemma hda_m_header_refuse : forall c l line,
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

(* ============================== m_header in the walk's index form ============================== *)
(* the header bytes hb = slice q r sl and the name nm = slice a z sl, from the two strips *)
Lemma hda_hb : forall sl k q r, hda_strip sl 1 k q r -> h_strip (slice 1 k sl) = slice q r sl.
Proof. intros sl k q r H. exact (hda_strip_slice sl 1 k q r H). Qed.
Lemma hda_hb_len : forall sl k q r, hda_strip sl 1 k q r -> length (slice q r sl) = (r - q)%nat.
Proof. intros sl k q r (H1 & H2 & _). apply hda_slice_length. lia. Qed.
Lemma hda_hb_7 : forall sl q r, (q + 8 <= r <= length sl)%nat ->
  firstn 7 (slice q r sl) = slice q (q + 7) sl /\ nth 7 (slice q r sl) 0 = nth (q + 7) sl 0 /\
  skipn 7 (slice q r sl) = slice (q + 7) r sl.
Proof.
  intros sl q r H. split; [apply hda_firstn_slice; lia|].
  split; [rewrite hda_slice_nth by lia; reflexivity | apply hda_skipn_slice; lia].
Qed.
(* the name passed its checks: m_header is mh_find of the name *)
Lemma hda_hdr_find : forall c sl line k q r a z,
  memchr sl RBR = Some k -> S k = length sl ->
  hda_strip sl 1 k q r -> (q + 8 <= r)%nat ->
  ieq (slice q (q + 7) sl) S_segment = true -> sp_tab (nth (q + 7) sl 0) = true ->
  hda_strip sl (q + 7) r a z -> (0 < z - a < 16)%nat ->
  m_header c sl line = mh_find c (slice a z sl) line.
Proof.
  intros c sl line k q r a z H1 H2 H3 H4 H5 H6 H7 H8.
  pose proof H3 as (_ & (_ & Hk) & _). pose proof H7 as ((Ha & Haz) & (Hzr & Hr) & _).
  rewrite (hda_m_header_find c sl line k H1 H2); rewrite (hda_hb sl k q r H3).
  - destruct (hda_hb_7 sl q r ltac:(lia)) as (_ & _ & E3). rewrite E3, (hda_strip_slice sl (q + 7) r a z H7).
    reflexivity.
  - rewrite (hda_hb_len sl k q r H3). lia.
  - destruct (hda_hb_7 sl q r ltac:(lia)) as (E1 & _). rewrite E1. exact H5.
  - destruct (hda_hb_7 sl q r ltac:(lia)) as (_ & E2 & _). rewrite E2. exact H6.
  - destruct (hda_hb_7 sl q r ltac:(lia)) as (_ & _ & E3). rewrite E3, (hda_strip_slice sl (q + 7) r a z H7).
    rewrite hda_slice_length by lia. lia.
Qed.
(* the six refusals of the walk: each is m_header's refusal *)
Lemma hda_hdr_refuse_nf : forall c sl line, memchr sl RBR = None -> m_header c sl line = (m_refuse c line false, None).
Proof. intros c sl line H. apply hda_m_header_refuse. intros ci E. congruence. Qed.
Lemma hda_hdr_refuse_end : forall c sl line k, memchr sl RBR = Some k -> S k <> length sl ->
  m_header c sl line = (m_refuse c line false, None).
Proof. intros c sl line k H1 H2. apply hda_m_header_refuse. intros ci E HS. exfalso. congruence. Qed.
Lemma hda_hdr_refuse_short : forall c sl line k q r, memchr sl RBR = Some k -> hda_strip sl 1 k q r ->
  (r < q + 8)%nat -> m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k q r H1 H2 H3. apply hda_m_header_refuse. intros ci E _ HL. exfalso.
  rewrite H1 in E. injection E as <-. rewrite (hda_hb sl k q r H2), (hda_hb_len sl k q r H2) in HL. lia.
Qed.
Lemma hda_hdr_refuse_ieq : forall c sl line k q r, memchr sl RBR = Some k -> hda_strip sl 1 k q r ->
  (q + 8 <= r)%nat -> ieq (slice q (q + 7) sl) S_segment = false -> m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k q r H1 H2 H3 H4. pose proof H2 as (_ & (Hrk & Hk) & _).
  apply hda_m_header_refuse. intros ci E _ _ HI. exfalso.
  rewrite H1 in E. injection E as <-. rewrite (hda_hb sl k q r H2) in HI.
  destruct (hda_hb_7 sl q r ltac:(lia)) as (E1 & _). rewrite E1 in HI. congruence.
Qed.
Lemma hda_hdr_refuse_sp : forall c sl line k q r, memchr sl RBR = Some k -> hda_strip sl 1 k q r ->
  (q + 8 <= r)%nat -> sp_tab (nth (q + 7) sl 0) = false -> m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k q r H1 H2 H3 H4. pose proof H2 as (_ & (Hrk & Hk) & _).
  apply hda_m_header_refuse. intros ci E _ _ _ HS. exfalso.
  rewrite H1 in E. injection E as <-. rewrite (hda_hb sl k q r H2) in HS.
  destruct (hda_hb_7 sl q r ltac:(lia)) as (_ & E2 & _). rewrite E2 in HS. congruence.
Qed.
Lemma hda_hdr_refuse_name : forall c sl line k q r a z, memchr sl RBR = Some k -> hda_strip sl 1 k q r ->
  (q + 8 <= r)%nat -> hda_strip sl (q + 7) r a z -> (z - a = 0 \/ 16 <= z - a)%nat ->
  m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k q r a z H1 H2 H3 H4 H5. pose proof H2 as (_ & (Hrk & Hk) & _).
  pose proof H4 as ((Ha & Haz) & (Hzr & Hr) & _).
  apply hda_m_header_refuse. intros ci E _ _ _ _. rewrite H1 in E. injection E as <-.
  rewrite (hda_hb sl k q r H2).
  destruct (hda_hb_7 sl q r ltac:(lia)) as (_ & _ & E3). rewrite E3, (hda_strip_slice sl (q + 7) r a z H4).
  rewrite hda_slice_length by lia. exact H5.
Qed.
