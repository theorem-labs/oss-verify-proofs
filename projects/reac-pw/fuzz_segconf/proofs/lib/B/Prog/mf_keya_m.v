(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA (KEY 0x8661c -> KDISP 0x86714 or
   TAIL): the model facts of the segment, build-independent (SegModel, image B's lib/B/Prog/m_file_m.v line terms and
   strip_c.v's strip_lead / strip_trail / strip_mid / strip_le only). Index forms of what the code computes: memchr's
   result as SegModel.memchr, the two strip calls (0x86658 key, 0x86664 value) as slices of the line, the quotes
   (0x86668-0x866d8), and m_key's two cases (mk_disp, or the refusal).
   Copied from image A's lane (the image-A m_file-family lane, commit ddef332b859f,
   lib/A/Prog/m_file_s_keya_m.v, whose lemmas are the segconf porter's plain proofs at commit dec616e11c2f
   lib/Prog/mfp_facts.v:13-362 and lib/Prog/mfu_facts.v:17-28, 279-290), statements and proofs unchanged, each name
   prefixed kb_ so that no other m_file file's names are shadowed. New for image B (strip is a call there, not
   image A's four inline loops): kb_strip_slice, kb_key_strip, kb_val_strip (strip's post, s0 + strip_lead and
   e0 - strip_trail, as the slice SegModel.h_strip gives). A walk lane of the image-B m_file-family owner's G2B. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_m strip_c.
Import ListNotations.
Open Scope Z_scope.

(* ============================== bytes and lists (mfp_facts.v:13-75) ============================== *)
Lemma kb_slice_slice : forall (l : list Z) i j a b, (a <= b)%nat -> (b <= j - i)%nat ->
  slice a b (slice i j l) = slice (i + a) (i + b) l.
Proof.
  intros l i j a b Hab Hb. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite (Nat.min_l (b - a) (j - i - a)) by lia.
  replace (i + b - (i + a))%nat with (b - a)%nat by lia. rewrite (Nat.add_comm a i). reflexivity.
Qed.
Lemma kb_slice_nth : forall (l : list Z) i j k, (k < j - i)%nat -> (j <= length l)%nat ->
  nth k (slice i j l) 0 = nth (i + k) l 0.
Proof.
  intros l i j k Hk Hj. unfold slice. rewrite nth_firstn, nth_skipn.
  destruct (Nat.ltb_spec k (j - i)); [reflexivity|lia].
Qed.
Lemma kb_slice_length : forall (l : list Z) i j, (i <= j <= length l)%nat -> length (slice i j l) = (j - i)%nat.
Proof.
  intros l i j H. unfold slice. rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.

(* ============================== the line (mfu_facts.v:17-28, 279-290) ============================== *)
Lemma kb_break_nl_spec : forall s l q, break_nl s = (l, q) ->
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
Lemma kb_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (kb_break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.
Lemma kb_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof.
  intros rest Hr. destruct (kb_line_rest rest) as [[E _]|[E1 [E2 _]]].
  - rewrite E at 2. rewrite length_app. cbn [length]. lia.
  - rewrite E2. destruct rest; [congruence|]. cbn [length]. lia.
Qed.
Lemma kb_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (kb_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma kb_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (kb_line_split rest) as [R E]. rewrite E at 2. rewrite length_app. lia.
Qed.
Lemma kb_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (kb_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [rewrite <- E; reflexivity|]. apply app_nth1. exact Hi.
Qed.
Lemma kb_line_firstn : forall rest o k, (o + k <= length (mf_line rest))%nat ->
  firstn k (skipn o rest) = slice o (o + k) (mf_line rest).
Proof.
  intros rest o k H. destruct (kb_line_split rest) as [R E].
  transitivity (firstn k (skipn o (mf_line rest ++ R))); [rewrite <- E; reflexivity|].
  unfold slice. replace (o + k - o)%nat with k by lia.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (k - (length (mf_line rest) - o))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

(* ============================== memchr (mfp_facts.v:78-111) ============================== *)
Lemma kb_memchr_some : forall (l : list Z) c i, memchr l c = Some i ->
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
Lemma kb_memchr_none : forall (l : list Z) c, memchr l c = None -> forall k, (k < length l)%nat -> nth k l 0 <> c.
Proof.
  induction l as [|b r IH]; intros c E k Hk; cbn [length] in Hk; [lia|].
  cbn [memchr] in E. destruct (Z.eqb_spec b c) as [Hb|Hb]; [discriminate|].
  destruct (memchr r c) eqn:Er; cbn [option_map] in E; [discriminate|].
  destruct k as [|k]; [exact Hb|exact (IH c Er k ltac:(lia))].
Qed.
Lemma kb_memchr_idx : forall (l : list Z) c i, (i < length l)%nat -> nth i l 0 = c ->
  (forall k, (k < i)%nat -> nth k l 0 <> c) -> memchr l c = Some i.
Proof.
  induction l as [|b r IH]; intros c i Hi Hc Hk; cbn [length] in Hi; [lia|].
  cbn [memchr]. destruct i as [|i].
  - change (b = c) in Hc. subst c. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (Hk 0%nat); [lia|exact Hb]|].
    rewrite (IH c i); [reflexivity|lia|exact Hc|].
    intros k Hk' Ek. apply (Hk (S k)); [lia|exact Ek].
Qed.
Lemma kb_memchr_none_idx : forall (l : list Z) c, (forall k, (k < length l)%nat -> nth k l 0 <> c) -> memchr l c = None.
Proof.
  induction l as [|b r IH]; intros c H; [reflexivity|]. cbn [memchr].
  destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (H 0%nat); [cbn [length]; lia|exact Hb]|].
  rewrite IH; [reflexivity|]. intros k Hk Ek. apply (H (S k)); [cbn [length]; lia|exact Ek].
Qed.

(* ============================== the quotes (mfp_facts.v:263-279) ============================== *)
Lemma kb_last_nth : forall (v : list Z) d, last v d = nth (pred (length v)) v d.
Proof. induction v as [|x r IH]; intros d; [reflexivity|]. destruct r as [|y r]; [reflexivity|]. exact (IH d). Qed.
Lemma kb_rl_tl : forall (v : list Z), removelast (tl v) = slice 1 (length v - 1) v.
Proof.
  intros [|x r]; [reflexivity|]. unfold slice. rewrite removelast_firstn_len. cbn [tl skipn length].
  f_equal. lia.
Qed.
Lemma kb_h_unquote_idx : forall v,
  h_unquote v =
  if (2 <=? length v)%nat && ((nth 0 v 0 =? DQ) || (nth 0 v 0 =? SQ)) && (nth (length v - 1) v 0 =? nth 0 v 0)
  then slice 1 (length v - 1) v else v.
Proof.
  intros v. unfold h_unquote.
  assert (E1 : hd0 v = nth 0 v 0) by (destruct v; reflexivity).
  rewrite (kb_last_nth v 0), E1, kb_rl_tl.
  replace (pred (length v)) with (length v - 1)%nat by lia. reflexivity.
Qed.

(* ============================== m_key's cases (mfp_facts.v:353-362) ============================== *)
Lemma kb_m_key_disp : forall c gi l line ei, memchr l EQ = Some ei ->
  m_key c (Some gi) l line = mk_disp c gi (h_strip (firstn ei l)) (h_unquote (h_strip (skipn (S ei) l))) line.
Proof.
  intros c gi l line ei H. unfold m_key. rewrite H. reflexivity.
Qed.
Lemma kb_m_key_refuse : forall c g l line, (memchr l EQ = None \/ g = None) -> m_key c g l line = m_refuse c line false.
Proof.
  intros c g l line H. unfold m_key.
  destruct H as [H|H]; [rewrite H; reflexivity|subst g; destruct (memchr l EQ); reflexivity].
Qed.

(* ============================== KEYA's index forms ============================== *)
(* the stripped line sl = slice i j L of the line L, its '=' at ei: the key region is [i, i + ei) of L, the value
   region [i + ei + 1, j) (image A's ka_firstn_slice / ka_skipn_slice) *)
Lemma kb_firstn_slice : forall (L : list Z) i j ei, (ei <= j - i)%nat ->
  firstn ei (slice i j L) = slice i (i + ei) L.
Proof.
  intros L i j ei H. unfold slice. rewrite firstn_firstn. f_equal; lia.
Qed.
Lemma kb_skipn_slice : forall (L : list Z) i j ei, (S ei <= j - i)%nat ->
  skipn (S ei) (slice i j L) = slice (i + S ei) j L.
Proof.
  intros L i j ei H. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (S ei + i)%nat with (i + S ei)%nat by lia. f_equal. lia.
Qed.

(* IMAGE B: strip's post as a slice. strip of the bytes [lo, hi) of L leaves the cells at lo + strip_lead and
   hi - strip_trail of those bytes (strip_c.v's post), and SegModel.h_strip of them is the slice between
   (strip_c.v's strip_mid, strip_le) *)
Lemma kb_strip_slice : forall (L : list Z) lo hi, (lo <= hi <= length L)%nat ->
  (strip_lead (slice lo hi L) + strip_trail (slice lo hi L) <= hi - lo)%nat /\
  h_strip (slice lo hi L) =
  slice (lo + strip_lead (slice lo hi L)) (hi - strip_trail (slice lo hi L)) L.
Proof.
  intros L lo hi H.
  pose proof (kb_slice_length L lo hi H) as Hlen.
  pose proof (strip_le (slice lo hi L)) as Hle. rewrite Hlen in Hle.
  split; [exact Hle|].
  rewrite <- (strip_mid (slice lo hi L)). rewrite Hlen.
  set (a := strip_lead (slice lo hi L)) in *. set (b := strip_trail (slice lo hi L)) in *.
  unfold slice. rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  replace (a + lo)%nat with (lo + a)%nat by lia.
  f_equal; lia.
Qed.
(* the key: h_strip of the bytes before the '=' *)
Lemma kb_key_strip : forall (L : list Z) i j ei, (i < j <= length L)%nat -> (ei < j - i)%nat ->
  (strip_lead (slice i (i + ei) L) + strip_trail (slice i (i + ei) L) <= ei)%nat /\
  h_strip (firstn ei (slice i j L)) =
  slice (i + strip_lead (slice i (i + ei) L)) (i + ei - strip_trail (slice i (i + ei) L)) L.
Proof.
  intros L i j ei Hij Hei. rewrite kb_firstn_slice by lia.
  destruct (kb_strip_slice L i (i + ei) ltac:(lia)) as (H1 & H2).
  split; [lia | exact H2].
Qed.
(* the value: h_strip of the bytes after the '=' *)
Lemma kb_val_strip : forall (L : list Z) i j ei, (i < j <= length L)%nat -> (ei < j - i)%nat ->
  (strip_lead (slice (i + S ei) j L) + strip_trail (slice (i + S ei) j L) <= j - (i + S ei))%nat /\
  h_strip (skipn (S ei) (slice i j L)) =
  slice (i + S ei + strip_lead (slice (i + S ei) j L)) (j - strip_trail (slice (i + S ei) j L)) L.
Proof.
  intros L i j ei Hij Hei. rewrite kb_skipn_slice by lia.
  exact (kb_strip_slice L (i + S ei) j ltac:(lia)).
Qed.

(* the quotes on the stripped value slice c d L: a matching pair at its ends goes (image A's ka_q) *)
Definition kb_q (L : list Z) (c d : nat) : bool :=
  (2 <=? d - c)%nat && ((nth c L 0 =? DQ) || (nth c L 0 =? SQ)) && (nth (d - 1) L 0 =? nth c L 0).
Lemma kb_unquote_idx : forall (L : list Z) c d, (c <= d <= length L)%nat ->
  h_unquote (slice c d L) = if kb_q L c d then slice (S c) (d - 1) L else slice c d L.
Proof.
  intros L c d H. rewrite kb_h_unquote_idx. rewrite kb_slice_length by lia. unfold kb_q.
  destruct (Nat.leb_spec 2 (d - c)) as [H2|H2]; cbn [andb]; [|reflexivity].
  rewrite (kb_slice_nth L c d 0) by lia. rewrite (kb_slice_nth L c d (d - c - 1)) by lia.
  replace (c + 0)%nat with c by lia. replace (c + (d - c - 1))%nat with (d - 1)%nat by lia.
  destruct ((nth c L 0 =? DQ) || (nth c L 0 =? SQ)); cbn [andb]; [|reflexivity].
  destruct (nth (d - 1) L 0 =? nth c L 0); [|reflexivity].
  rewrite kb_slice_slice by lia. f_equal; lia.
Qed.

(* the key and the value inside the line of the text left, as KDISP's mk_kv states them *)
Lemma kb_mk_kv : forall rest a b c' d', (a <= b <= length (mf_line rest))%nat -> (c' <= d' <= length (mf_line rest))%nat ->
  mk_kv rest a (b - a) c' (d' - c') (slice a b (mf_line rest)) (slice c' d' (mf_line rest)).
Proof.
  intros rest a b c' d' H1 H2. unfold mk_kv.
  split; [lia|]. split; [lia|].
  split; rewrite kb_line_firstn by lia; f_equal; lia.
Qed.

(* the model at KDISP from the model at KEY: cur = Some gi and an '=' in the stripped line *)
Lemma kb_model_disp : forall mcc gi sl line rest ei fin,
  memchr sl EQ = Some ei ->
  mf_fin (m_key mcc (Some gi) sl (line + 1), Some gi) line rest = fin ->
  mf_fin (mk_disp mcc gi (h_strip (firstn ei sl)) (h_unquote (h_strip (skipn (S ei) sl))) (line + 1), Some gi) line rest = fin.
Proof. intros mcc gi sl line rest ei fin Hm H. rewrite <- (kb_m_key_disp mcc gi sl (line + 1) ei Hm). exact H. Qed.
(* the model at the refusal (cur = NULL or no '='), the step to the next line *)
Lemma kb_model_refuse : forall mcc cur sl line rest fin, (memchr sl EQ = None \/ cur = None) ->
  mf_fin (m_key mcc cur sl (line + 1), cur) line rest = fin ->
  fst (m_lines (m_refuse mcc (line + 1) false, cur) (line + 1) (lines (mf_rest rest))) = fin.
Proof.
  intros mcc cur sl line rest fin Hm H. unfold mf_fin in H.
  rewrite (kb_m_key_refuse mcc cur sl (line + 1) Hm) in H. exact H.
Qed.

(* memchr's first_byte over the bytes of sl: found at k < |sl| is SegModel.memchr's Some k, else None *)
Lemma kb_memchr_found : forall (sl : list Z) (rd : Z -> option Z) x c k,
  (forall i', (i' < length sl)%nat -> rd (x + Z.of_nat i') = Some (nth i' sl 0)) ->
  0 <= k < Z.of_nat (length sl) ->
  (forall i', 0 <= i' < k -> exists b, rd (x + i') = Some b /\ b <> c) ->
  rd (x + k) = Some c ->
  memchr sl c = Some (Z.to_nat k).
Proof.
  intros sl rd x c k Hb Hk Hpre Hat. apply kb_memchr_idx; [lia| |].
  - pose proof (Hb (Z.to_nat k) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite Hat in E.
    injection E as E. symmetry. exact E.
  - intros k' Hk'. destruct (Hpre (Z.of_nat k') ltac:(lia)) as (b & Hrb & Hne).
    pose proof (Hb k' ltac:(lia)) as E. rewrite Hrb in E. injection E as E. rewrite <- E. exact Hne.
Qed.
Lemma kb_memchr_nf : forall (sl : list Z) (rd : Z -> option Z) x c,
  (forall i', (i' < length sl)%nat -> rd (x + Z.of_nat i') = Some (nth i' sl 0)) ->
  (forall i', 0 <= i' < Z.of_nat (length sl) -> exists b, rd (x + i') = Some b /\ b <> c) ->
  memchr sl c = None.
Proof.
  intros sl rd x c Hb Hpre. apply kb_memchr_none_idx. intros k' Hk'.
  destruct (Hpre (Z.of_nat k') ltac:(lia)) as (b & Hrb & Hne).
  pose proof (Hb k' ltac:(lia)) as E. rewrite Hrb in E. injection E as E. rewrite <- E. exact Hne.
Qed.

(* the stripped line's bytes from the text left's: byte k of slice i j (mf_line rest) is byte i + k of rest *)
Lemma kb_sl_byte : forall rest i j k, (i <= j <= length (mf_line rest))%nat -> (k < j - i)%nat ->
  nth k (slice i j (mf_line rest)) 0 = nth (i + k) rest 0.
Proof.
  intros rest i j k Hij Hk. rewrite kb_slice_nth by lia. symmetry. apply kb_line_nth. lia.
Qed.
