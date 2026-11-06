(* m_file on fuzz_segconf.asan (image A), segment S_MF_KEYA (KEY 0x8633c -> KDISP 0x86684 or TAIL): the model
   facts of the segment, build-independent (SegModel and m_file_m.v's line terms only). Index forms of what the
   compiled loops compute: memchr's result as SegModel.memchr, the key strip (0x86354-0x86488, 0x8654c), the value
   strip (0x86550-0x865ec), the quotes (0x865f0-0x86654), and m_key's two cases (mk_disp, or the refusal).
   Copied lemmas, each from the plain / image-B owner's plain proof at commit dec616e11c2f (a file outside this
   tree; m_file_m.v restates the line terms they use): blank_gt32, blank_mask, slice_slice, slice_nth,
   slice_length, mff_line_split, mf_line_nth, mf_line_firstn, memchr_some, memchr_none, memchr_idx,
   memchr_none_idx, all_blank, dropwhile_blank_idx, h_strip_idx, mff_last_nth, mff_rl_tl, h_unquote_idx,
   m_key_disp, m_key_refuse (lib/Prog/mfp_facts.v:13-362); break_nl_spec, mf_line_rest, mf_rest_lt
   (lib/Prog/mfu_facts.v:17-28, 279-290). The ka_* lemmas are this lane's. The KEYA segment lane of the G2 walk owner's G2. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_m.
Import ListNotations.
Open Scope Z_scope.

(* ============================== bytes and lists (mfp_facts.v:13-75) ============================== *)
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

(* ============================== the line (mfu_facts.v:17-28, 279-290) ============================== *)
Lemma break_nl_spec : forall s l q, break_nl s = (l, q) ->
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
Lemma mf_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.
Lemma mf_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof.
  intros rest Hr. destruct (mf_line_rest rest) as [[E _]|[E1 [E2 _]]].
  - rewrite E at 2. rewrite length_app. cbn [length]. lia.
  - rewrite E2. destruct rest; [congruence|]. cbn [length]. lia.
Qed.
Lemma mff_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma mf_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mff_line_split rest) as [R E]. rewrite E at 2. rewrite length_app. lia.
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

(* ============================== memchr (mfp_facts.v:78-111) ============================== *)
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

(* ============================== the strip (mfp_facts.v:115-147) ============================== *)
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

(* ============================== the quotes (mfp_facts.v:263-279) ============================== *)
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

(* ============================== m_key's cases (mfp_facts.v:353-362) ============================== *)
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

(* ============================== KEYA's index forms (this lane) ============================== *)
(* the stripped line sl = slice i j L of the line L, its '=' at ei: the key region is [i, i + ei) of L, the value
   region [i + ei + 1, j) *)
Lemma ka_firstn_slice : forall (L : list Z) i j ei, (ei <= j - i)%nat ->
  firstn ei (slice i j L) = slice i (i + ei) L.
Proof.
  intros L i j ei H. unfold slice. rewrite firstn_firstn. f_equal; lia.
Qed.
Lemma ka_skipn_slice : forall (L : list Z) i j ei, (S ei <= j - i)%nat ->
  skipn (S ei) (slice i j L) = slice (i + S ei) j L.
Proof.
  intros L i j ei H. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (S ei + i)%nat with (i + S ei)%nat by lia. f_equal. lia.
Qed.

(* the strip of the bytes [lo, hi) of L in L's indices: the forward loop stopped at a, the backward loop at b *)
Lemma ka_strip_slice : forall (L : list Z) lo hi a b, (lo <= a <= b)%nat -> (b <= hi <= length L)%nat ->
  all_blank L lo a -> (a = hi \/ blank (nth a L 0) = false) ->
  all_blank L b hi -> (b = a \/ blank (nth (b - 1) L 0) = false) ->
  h_strip (slice lo hi L) = slice a b L.
Proof.
  intros L lo hi a b Hab Hbh Hb0 Hs Hb1 He.
  assert (Lu : length (slice lo hi L) = (hi - lo)%nat) by (apply slice_length; lia).
  assert (Nu : forall k, (k < hi - lo)%nat -> nth k (slice lo hi L) 0 = nth (lo + k) L 0)
    by (intros k Hk; apply slice_nth; lia).
  rewrite (h_strip_idx (slice lo hi L) (a - lo) (b - lo)).
  - rewrite slice_slice by lia. f_equal; lia.
  - rewrite Lu. lia.
  - intros k Hk. rewrite Nu by lia. apply Hb0. lia.
  - rewrite Lu. destruct Hs as [Hs|Hs]; [left; lia|].
    destruct (Nat.eq_dec a hi) as [E|E]; [left; lia|right]. rewrite Nu by lia.
    replace (lo + (a - lo))%nat with a by lia. exact Hs.
  - intros k Hk. rewrite Lu in Hk. rewrite Nu by lia. apply Hb1. lia.
  - destruct He as [He|He]; [left; lia|].
    destruct (Nat.eq_dec b a) as [E|E]; [left; lia|right]. rewrite Nu by lia.
    replace (lo + (b - lo - 1))%nat with (b - 1)%nat by lia. exact He.
Qed.

(* the key and the stripped value from the loops' stops *)
Lemma ka_key_idx : forall (L : list Z) i j ei a b, (ei < j - i)%nat -> (j <= length L)%nat ->
  (i <= a <= b)%nat -> (b <= i + ei)%nat ->
  all_blank L i a -> (a = (i + ei)%nat \/ blank (nth a L 0) = false) ->
  all_blank L b (i + ei) -> (b = a \/ blank (nth (b - 1) L 0) = false) ->
  h_strip (firstn ei (slice i j L)) = slice a b L.
Proof.
  intros L i j ei a b Hei Hj Hab Hb H1 H2 H3 H4. rewrite ka_firstn_slice by lia.
  apply ka_strip_slice; first [lia | assumption].
Qed.
Lemma ka_val_idx : forall (L : list Z) i j ei c d, (ei < j - i)%nat -> (j <= length L)%nat ->
  (i + S ei <= c <= d)%nat -> (d <= j)%nat ->
  all_blank L (i + S ei) c -> (c = j \/ blank (nth c L 0) = false) ->
  all_blank L d j -> (d = c \/ blank (nth (d - 1) L 0) = false) ->
  h_strip (skipn (S ei) (slice i j L)) = slice c d L.
Proof.
  intros L i j ei c d Hei Hj Hcd Hd H1 H2 H3 H4. rewrite ka_skipn_slice by lia.
  apply ka_strip_slice; first [lia | assumption].
Qed.

(* the quotes on the stripped value slice c d L: a matching pair at its ends goes *)
Definition ka_q (L : list Z) (c d : nat) : bool :=
  (2 <=? d - c)%nat && ((nth c L 0 =? DQ) || (nth c L 0 =? SQ)) && (nth (d - 1) L 0 =? nth c L 0).
Lemma ka_unquote_idx : forall (L : list Z) c d, (c <= d <= length L)%nat ->
  h_unquote (slice c d L) = if ka_q L c d then slice (S c) (d - 1) L else slice c d L.
Proof.
  intros L c d H. rewrite h_unquote_idx. rewrite slice_length by lia. unfold ka_q.
  destruct (Nat.leb_spec 2 (d - c)) as [H2|H2]; cbn [andb]; [|reflexivity].
  rewrite (slice_nth L c d 0) by lia. rewrite (slice_nth L c d (d - c - 1)) by lia.
  replace (c + 0)%nat with c by lia. replace (c + (d - c - 1))%nat with (d - 1)%nat by lia.
  destruct ((nth c L 0 =? DQ) || (nth c L 0 =? SQ)); cbn [andb]; [|reflexivity].
  destruct (nth (d - 1) L 0 =? nth c L 0); [|reflexivity].
  rewrite slice_slice by lia. f_equal; lia.
Qed.

(* the key and the value inside the line of the text left, as KDISP's mk_kv states them *)
Lemma ka_mk_kv : forall rest a b c' d', (a <= b <= length (mf_line rest))%nat -> (c' <= d' <= length (mf_line rest))%nat ->
  mk_kv rest a (b - a) c' (d' - c') (slice a b (mf_line rest)) (slice c' d' (mf_line rest)).
Proof.
  intros rest a b c' d' H1 H2. unfold mk_kv.
  split; [lia|]. split; [lia|].
  split; rewrite mf_line_firstn by lia; f_equal; lia.
Qed.

(* the model at KDISP from the model at KEY: cur = Some gi and an '=' in the stripped line *)
Lemma ka_model_disp : forall mcc gi sl line rest ei fin,
  memchr sl EQ = Some ei ->
  mf_fin (m_key mcc (Some gi) sl (line + 1), Some gi) line rest = fin ->
  mf_fin (mk_disp mcc gi (h_strip (firstn ei sl)) (h_unquote (h_strip (skipn (S ei) sl))) (line + 1), Some gi) line rest = fin.
Proof. intros mcc gi sl line rest ei fin Hm H. rewrite <- (m_key_disp mcc gi sl (line + 1) ei Hm). exact H. Qed.
(* the model at the refusal (cur = NULL or no '='), the step to the next line *)
Lemma ka_model_refuse : forall mcc cur sl line rest fin, (memchr sl EQ = None \/ cur = None) ->
  mf_fin (m_key mcc cur sl (line + 1), cur) line rest = fin ->
  fst (m_lines (m_refuse mcc (line + 1) false, cur) (line + 1) (lines (mf_rest rest))) = fin.
Proof.
  intros mcc cur sl line rest fin Hm H. unfold mf_fin in H.
  rewrite (m_key_refuse mcc cur sl (line + 1) Hm) in H. exact H.
Qed.

(* memchr's first_byte over the bytes of sl: found at k < |sl| is SegModel.memchr's Some k, else None *)
Lemma ka_memchr_found : forall (sl : list Z) (rd : Z -> option Z) x c k,
  (forall i', (i' < length sl)%nat -> rd (x + Z.of_nat i') = Some (nth i' sl 0)) ->
  0 <= k < Z.of_nat (length sl) ->
  (forall i', 0 <= i' < k -> exists b, rd (x + i') = Some b /\ b <> c) ->
  rd (x + k) = Some c ->
  memchr sl c = Some (Z.to_nat k).
Proof.
  intros sl rd x c k Hb Hk Hpre Hat. apply memchr_idx; [lia| |].
  - pose proof (Hb (Z.to_nat k) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite Hat in E.
    injection E as E. symmetry. exact E.
  - intros k' Hk'. destruct (Hpre (Z.of_nat k') ltac:(lia)) as (b & Hrb & Hne).
    pose proof (Hb k' ltac:(lia)) as E. rewrite Hrb in E. injection E as E. rewrite <- E. exact Hne.
Qed.
Lemma ka_memchr_nf : forall (sl : list Z) (rd : Z -> option Z) x c,
  (forall i', (i' < length sl)%nat -> rd (x + Z.of_nat i') = Some (nth i' sl 0)) ->
  (forall i', 0 <= i' < Z.of_nat (length sl) -> exists b, rd (x + i') = Some b /\ b <> c) ->
  memchr sl c = None.
Proof.
  intros sl rd x c Hb Hpre. apply memchr_none_idx. intros k' Hk'.
  destruct (Hpre (Z.of_nat k') ltac:(lia)) as (b & Hrb & Hne).
  pose proof (Hb k' ltac:(lia)) as E. rewrite Hrb in E. injection E as E. rewrite <- E. exact Hne.
Qed.

(* the stripped line's bytes from the text left's: byte k of slice i j (mf_line rest) is byte i + k of rest *)
Lemma ka_sl_byte : forall rest i j k, (i <= j <= length (mf_line rest))%nat -> (k < j - i)%nat ->
  nth k (slice i j (mf_line rest)) 0 = nth (i + k) rest 0.
Proof.
  intros rest i j k Hij Hk. rewrite slice_nth by lia. symmetry. apply mf_line_nth. lia.
Qed.
