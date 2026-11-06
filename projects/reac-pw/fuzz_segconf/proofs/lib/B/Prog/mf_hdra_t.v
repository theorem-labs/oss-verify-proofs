(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_HDRA (HDR 0x864f4 -> HFIND 0x865c0 or
   TAIL 0x86820): the model facts its walk uses. Gallina only; no instruction is executed here. A walk lane of
   the image-B m_file-family owner's G2B.

   What the code computes, in index form over the text left rest at p and the stripped line
   sl = slice i j (mf_line rest) at s = p + i, e = p + j (the image-B m_file cut map section 4, S_MF_HDRA; listing
   the neutral listing of m_file in image B, lines 239-289, 418-428, 642-646):
   - memchr(s, ']', e - s) 0x864fc: the index k of sl's first ']', or none (NULL refuses, 0x86500);
   - close + 1 = e 0x86510: k = j - i - 1;
   - strip(&b, &be) 0x86530 over [s + 1, close) = the text's [i + 1, j - 1): b = p + q1, be = p + r1 with
     q1 = i + 1 + strip_lead, r1 = j - 1 - strip_trail of that slice (strip_c.v's post), so the header bytes
     h_strip (slice 1 k sl) are slice q1 r1 rest (hd_strip_slice);
   - be - b < 8 0x86544, ieq(b, 7, "segment") 0x86554, b[7] = '\t' or ' ' 0x86580-0x86588;
   - strip(&nm, &ne) 0x865a0 over [b + 7, be) = [q1 + 7, r1): nm = p + q2, ne = p + r2;
   - n = ne - nm = 0 0x865b0 or n >= 16 0x865bc refuses; else m_find (HFIND).
   Each refusal is m_header's refusal (the hd_hdr_refuse lemmas), and the passed checks make m_header m_file_m.v's mh_find of
   the name slice q2 r2 rest (hd_hdr_find).
   The list lemmas hd_slice_* / hd_line_* / hd_memchr_* are the image-A m_file-family lane's image-A lib/A/Prog/m_file_s_hdra_t.v
   (commit 88d61b26fa90: hda_slice_slice, hda_slice_nth, hda_slice_length, hda_skipn_slice,
   hda_firstn_slice, hda_break_nl_spec, hda_mf_line_rest, hda_line_split, hda_line_le, hda_line_nth,
   hda_memchr_some, hda_memchr_idx, hda_memchr_none_idx, hda_memchr_of_first), statements and proofs, renamed hd_;
   that file Requires image A's m_file_m.v, so they are copied. The strip and m_header lemmas are new: image A
   inlines strip (its header strip is an index relation, hda_strip); image B calls it, and strip_c.v's post gives
   the two ends through strip_lead / strip_trail. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_m strip_c.
Import ListNotations.
Open Scope Z_scope.

(* ============================== slices (the image-A m_file-family lane's image-A file) ============================== *)
Lemma hd_slice_slice : forall (l : list Z) i j a b, (a <= b)%nat -> (b <= j - i)%nat ->
  slice a b (slice i j l) = slice (i + a) (i + b) l.
Proof.
  intros l i j a b Hab Hb. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite (Nat.min_l (b - a) (j - i - a)) by lia.
  replace (i + b - (i + a))%nat with (b - a)%nat by lia. rewrite (Nat.add_comm a i). reflexivity.
Qed.
Lemma hd_slice_nth : forall (l : list Z) i j k, (k < j - i)%nat -> (j <= length l)%nat ->
  nth k (slice i j l) 0 = nth (i + k) l 0.
Proof.
  intros l i j k Hk Hj. unfold slice. rewrite nth_firstn, nth_skipn.
  destruct (Nat.ltb_spec k (j - i)); [reflexivity|lia].
Qed.
Lemma hd_slice_length : forall (l : list Z) i j, (i <= j <= length l)%nat -> length (slice i j l) = (j - i)%nat.
Proof.
  intros l i j H. unfold slice. rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.
Lemma hd_skipn_slice : forall (l : list Z) i j k, (k <= j - i)%nat ->
  skipn k (slice i j l) = slice (i + k) j l.
Proof.
  intros l i j k Hk. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (j - (i + k))%nat with (j - i - k)%nat by lia. rewrite (Nat.add_comm k i). reflexivity.
Qed.
Lemma hd_firstn_slice : forall (l : list Z) i j k, (k <= j - i)%nat ->
  firstn k (slice i j l) = slice i (i + k) l.
Proof.
  intros l i j k Hk. unfold slice. rewrite firstn_firstn.
  replace (i + k - i)%nat with k by lia. rewrite Nat.min_l by lia. reflexivity.
Qed.

(* ============================== the line (the image-A m_file-family lane's image-A file) ============================== *)
Lemma hd_break_nl_spec : forall s l q, break_nl s = (l, q) ->
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
Lemma hd_mf_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (hd_break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.
Lemma hd_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (hd_mf_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma hd_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (hd_line_split rest) as [R E].
  transitivity (length (mf_line rest ++ R)); [rewrite length_app; lia | rewrite <- E; lia].
Qed.
Lemma hd_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (hd_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [rewrite <- E; reflexivity|]. apply app_nth1. exact Hi.
Qed.
(* a slice of the line is the same slice of the text left *)
Lemma hd_line_slice : forall rest a b, (b <= length (mf_line rest))%nat ->
  slice a b (mf_line rest) = slice a b rest.
Proof.
  intros rest a b Hb. destruct (hd_line_split rest) as [R E].
  transitivity (slice a b (mf_line rest)); [reflexivity|].
  rewrite E at 2. unfold slice. destruct (Nat.le_gt_cases a (length (mf_line rest))) as [Ha|Ha].
  - rewrite skipn_app. replace (a - length (mf_line rest))%nat with 0%nat by lia. cbn [skipn].
    rewrite firstn_app, length_skipn.
    destruct (Nat.le_gt_cases (b - a) (length (mf_line rest) - a)) as [H1|H1].
    + replace (b - a - (length (mf_line rest) - a))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
    + lia.
  - replace (b - a)%nat with 0%nat by lia. reflexivity.
Qed.

(* ============================== memchr (the image-A m_file-family lane's image-A file) ============================== *)
Lemma hd_memchr_some : forall (l : list Z) c i, memchr l c = Some i ->
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
Lemma hd_memchr_idx : forall (l : list Z) c i, (i < length l)%nat -> nth i l 0 = c ->
  (forall k, (k < i)%nat -> nth k l 0 <> c) -> memchr l c = Some i.
Proof.
  induction l as [|b r IH]; intros c i Hi Hc Hk; cbn [length] in Hi; [lia|].
  cbn [memchr]. destruct i as [|i].
  - change (b = c) in Hc. subst c. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (Hk 0%nat); [lia|exact Hb]|].
    rewrite (IH c i); [reflexivity|lia|exact Hc|].
    intros k Hk' Ek. apply (Hk (S k)); [lia|exact Ek].
Qed.
Lemma hd_memchr_none_idx : forall (l : list Z) c, (forall k, (k < length l)%nat -> nth k l 0 <> c) ->
  memchr l c = None.
Proof.
  induction l as [|b r IH]; intros c H; [reflexivity|]. cbn [memchr].
  destruct (Z.eqb_spec b c) as [Hb|Hb]; [exfalso; apply (H 0%nat); [cbn [length]; lia|exact Hb]|].
  rewrite IH; [reflexivity|]. intros k Hk Ek. apply (H (S k)); [cbn [length]; lia|exact Ek].
Qed.
Lemma hd_memchr_of_first : forall (l : list Z) c k, (k <= length l)%nat ->
  (forall x, (x < k)%nat -> nth x l 0 <> c) -> ((k < length l)%nat -> nth k l 0 = c) ->
  memchr l c = if (k <? length l)%nat then Some k else None.
Proof.
  intros l c k Hk Hb Hc. destruct (Nat.ltb_spec k (length l)) as [Hlt|Hge].
  - apply hd_memchr_idx; [exact Hlt | exact (Hc Hlt) | exact Hb].
  - apply hd_memchr_none_idx. intros x Hx. apply Hb. lia.
Qed.

(* ============================== strip (image B: strip_c.v's post) ============================== *)
(* the two ends strip returns, over the bytes [a, b) of l: h_strip of the slice is the slice between them *)
Lemma hd_strip_le : forall (l : list Z) a b, (a <= b <= length l)%nat ->
  (a + strip_lead (slice a b l) + strip_trail (slice a b l) <= b)%nat.
Proof.
  intros l a b H. pose proof (strip_le (slice a b l)) as S. rewrite hd_slice_length in S by lia. lia.
Qed.
Lemma hd_strip_slice : forall (l : list Z) a b, (a <= b <= length l)%nat ->
  h_strip (slice a b l) = slice (a + strip_lead (slice a b l)) (b - strip_trail (slice a b l)) l.
Proof.
  intros l a b H. pose proof (hd_strip_le l a b H) as Le.
  rewrite <- strip_mid. rewrite hd_slice_length by lia.
  rewrite hd_skipn_slice by lia. rewrite hd_firstn_slice by lia. f_equal. lia.
Qed.

(* ============================== the header's indices ============================== *)
(* the stripped line, sl = slice i j (mf_line rest) *)
Definition hda_sl (rest : list Z) (i j : nat) : list Z := slice i j (mf_line rest).
(* the header bytes' ends after strip 0x86530 over [i + 1, j - 1): b = p + q1, be = p + r1 *)
Definition hda_q1 (rest : list Z) (i j : nat) : nat := (i + 1 + strip_lead (slice (i + 1) (j - 1) rest))%nat.
Definition hda_r1 (rest : list Z) (i j : nat) : nat := (j - 1 - strip_trail (slice (i + 1) (j - 1) rest))%nat.
(* the name's ends after strip 0x865a0 over [q1 + 7, r1): nm = p + q2, ne = p + r2 *)
Definition hda_q2 (rest : list Z) (i j : nat) : nat :=
  (hda_q1 rest i j + 7 + strip_lead (slice (hda_q1 rest i j + 7) (hda_r1 rest i j) rest))%nat.
Definition hda_r2 (rest : list Z) (i j : nat) : nat :=
  (hda_r1 rest i j - strip_trail (slice (hda_q1 rest i j + 7) (hda_r1 rest i j) rest))%nat.
(* memchr's answer: ']' first at k = j - i - 1, the last byte of sl, after the '[' at 0 *)
Definition hda_close (rest : list Z) (i j : nat) : Prop :=
  memchr (hda_sl rest i j) RBR = Some (j - i - 1)%nat /\ (2 <= j - i)%nat.

Lemma hd_q1r1 : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  (i + 1 <= hda_q1 rest i j <= hda_r1 rest i j)%nat /\ (hda_r1 rest i j <= j - 1)%nat.
Proof.
  intros rest i j Hij H2. pose proof (hd_line_le rest) as HL.
  pose proof (hd_strip_le rest (i + 1) (j - 1) ltac:(lia)) as Le. unfold hda_q1, hda_r1. lia.
Qed.
Lemma hd_q2r2 : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  (hda_q1 rest i j + 7 <= hda_r1 rest i j)%nat ->
  (hda_q1 rest i j + 7 <= hda_q2 rest i j <= hda_r2 rest i j)%nat /\ (hda_r2 rest i j <= hda_r1 rest i j)%nat.
Proof.
  intros rest i j Hij H2 H7. pose proof (hd_line_le rest) as HL. pose proof (hd_q1r1 rest i j Hij H2) as (A & B).
  pose proof (hd_strip_le rest (hda_q1 rest i j + 7) (hda_r1 rest i j) ltac:(lia)) as Le. unfold hda_q2, hda_r2. lia.
Qed.

(* memchr's found answer is at least 1: sl starts with '[' *)
Lemma hd_close_pos : forall rest i j k, (i < j <= length (mf_line rest))%nat -> nth i (mf_line rest) 0 = LBR ->
  memchr (hda_sl rest i j) RBR = Some k -> (1 <= k)%nat.
Proof.
  intros rest i j k Hij HLB HM. destruct (hd_memchr_some _ _ _ HM) as (_ & Hk & _).
  destruct k as [|k]; [|lia]. exfalso. unfold hda_sl in Hk. rewrite hd_slice_nth in Hk by lia.
  rewrite Nat.add_0_r, HLB in Hk. lia.
Qed.

(* the header bytes are the strip of [1, k) of sl, the text's [q1, r1) *)
Lemma hd_hb : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  h_strip (slice 1 (j - i - 1) (hda_sl rest i j)) = slice (hda_q1 rest i j) (hda_r1 rest i j) rest.
Proof.
  intros rest i j Hij H2. pose proof (hd_line_le rest) as HL. unfold hda_sl.
  rewrite hd_slice_slice by lia. rewrite hd_line_slice by lia.
  replace (i + 1)%nat with (i + 1)%nat by reflexivity. replace (i + (j - i - 1))%nat with (j - 1)%nat by lia.
  rewrite hd_strip_slice by lia. reflexivity.
Qed.
Lemma hd_hb_len : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  length (slice (hda_q1 rest i j) (hda_r1 rest i j) rest) = (hda_r1 rest i j - hda_q1 rest i j)%nat.
Proof.
  intros rest i j Hij H2. pose proof (hd_line_le rest) as HL. pose proof (hd_q1r1 rest i j Hij H2).
  apply hd_slice_length. lia.
Qed.
(* the name is the strip of the header bytes after their first 7, the text's [q2, r2) *)
Lemma hd_nm : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  (hda_q1 rest i j + 7 <= hda_r1 rest i j)%nat ->
  h_strip (skipn 7 (slice (hda_q1 rest i j) (hda_r1 rest i j) rest)) = slice (hda_q2 rest i j) (hda_r2 rest i j) rest.
Proof.
  intros rest i j Hij H2 H7. pose proof (hd_line_le rest) as HL. pose proof (hd_q1r1 rest i j Hij H2) as (A & B).
  rewrite hd_skipn_slice by lia. rewrite hd_strip_slice by lia. reflexivity.
Qed.

(* ============================== m_header ============================== *)
Lemma hd_hdr_refuse_nf : forall c sl line, memchr sl RBR = None -> m_header c sl line = (m_refuse c line false, None).
Proof. intros c sl line H. unfold m_header. rewrite H. reflexivity. Qed.
Lemma hd_hdr_refuse_end : forall c sl line k, memchr sl RBR = Some k -> S k <> length sl ->
  m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k H Hk. unfold m_header. rewrite H.
  destruct (Nat.eqb_spec (S k) (length sl)) as [E|E]; [lia | reflexivity].
Qed.
Lemma hd_hdr_refuse_short : forall c sl line k, memchr sl RBR = Some k -> S k = length sl ->
  (length (h_strip (slice 1 k sl)) < 8)%nat -> m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k H Hk Hs. unfold m_header. rewrite H.
  rewrite (proj2 (Nat.eqb_eq _ _) Hk). cbn [negb]. cbv zeta.
  rewrite (proj2 (Nat.ltb_lt _ _) Hs). reflexivity.
Qed.
Lemma hd_hdr_refuse_ieq : forall c sl line k, memchr sl RBR = Some k -> S k = length sl ->
  (8 <= length (h_strip (slice 1 k sl)))%nat -> ieq (firstn 7 (h_strip (slice 1 k sl))) S_segment = false ->
  m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k H Hk Hs Hi. unfold m_header. rewrite H.
  rewrite (proj2 (Nat.eqb_eq _ _) Hk). cbn [negb]. cbv zeta.
  rewrite (proj2 (Nat.ltb_ge _ _) Hs), Hi. reflexivity.
Qed.
Lemma hd_hdr_refuse_sp : forall c sl line k, memchr sl RBR = Some k -> S k = length sl ->
  (8 <= length (h_strip (slice 1 k sl)))%nat -> ieq (firstn 7 (h_strip (slice 1 k sl))) S_segment = true ->
  sp_tab (nth 7 (h_strip (slice 1 k sl)) 0) = false ->
  m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k H Hk Hs Hi Hsp. unfold m_header. rewrite H.
  rewrite (proj2 (Nat.eqb_eq _ _) Hk). cbn [negb]. cbv zeta.
  rewrite (proj2 (Nat.ltb_ge _ _) Hs), Hi, Hsp. reflexivity.
Qed.
Lemma hd_hdr_refuse_name : forall c sl line k, memchr sl RBR = Some k -> S k = length sl ->
  (8 <= length (h_strip (slice 1 k sl)))%nat -> ieq (firstn 7 (h_strip (slice 1 k sl))) S_segment = true ->
  sp_tab (nth 7 (h_strip (slice 1 k sl)) 0) = true ->
  (length (h_strip (skipn 7 (h_strip (slice 1 k sl)))) = 0 \/ 16 <= length (h_strip (skipn 7 (h_strip (slice 1 k sl)))))%nat ->
  m_header c sl line = (m_refuse c line false, None).
Proof.
  intros c sl line k H Hk Hs Hi Hsp Hn. unfold m_header. rewrite H.
  rewrite (proj2 (Nat.eqb_eq _ _) Hk). cbn [negb]. cbv zeta.
  rewrite (proj2 (Nat.ltb_ge _ _) Hs), Hi, Hsp. cbn [negb orb].
  destruct Hn as [Hn|Hn].
  - rewrite Hn. reflexivity.
  - rewrite (proj2 (Nat.leb_le _ _) Hn), Bool.orb_true_r. reflexivity.
Qed.
Lemma hd_hdr_find : forall c sl line k, memchr sl RBR = Some k -> S k = length sl ->
  (8 <= length (h_strip (slice 1 k sl)))%nat -> ieq (firstn 7 (h_strip (slice 1 k sl))) S_segment = true ->
  sp_tab (nth 7 (h_strip (slice 1 k sl)) 0) = true ->
  (0 < length (h_strip (skipn 7 (h_strip (slice 1 k sl)))) < 16)%nat ->
  m_header c sl line = mh_find c (h_strip (skipn 7 (h_strip (slice 1 k sl)))) line.
Proof.
  intros c sl line k H Hk Hs Hi Hsp Hn. unfold m_header. rewrite H.
  rewrite (proj2 (Nat.eqb_eq _ _) Hk). cbn [negb]. cbv zeta.
  rewrite (proj2 (Nat.ltb_ge _ _) Hs), Hi, Hsp. cbn [negb orb].
  set (nm := h_strip (skipn 7 (h_strip (slice 1 k sl)))) in *.
  destruct (Nat.eqb_spec (length nm) 0) as [E|E]; [lia|].
  destruct (Nat.leb_spec 16 (length nm)) as [E2|E2]; [lia|].
  cbn [orb]. reflexivity.
Qed.

(* ============================== the same, in the text's indices ============================== *)
(* the facts every lemma below takes: i < j inside the line, '[' at i, the close at j - i - 1 *)
Section ix.
Variables (rest : list Z) (i j : nat).
Hypothesis Hij : (i < j <= length (mf_line rest))%nat.
Hypothesis HC : hda_close rest i j.

Let Lsl : length (hda_sl rest i j) = (j - i)%nat.
Proof. unfold hda_sl. apply hd_slice_length. lia. Qed.
Let Hk : S (j - i - 1) = length (hda_sl rest i j).
Proof. destruct HC as (_ & H2). rewrite Lsl. lia. Qed.

Lemma hd_ix_short : forall c line, (hda_r1 rest i j < hda_q1 rest i j + 8)%nat ->
  m_header c (hda_sl rest i j) line = (m_refuse c line false, None).
Proof.
  intros c line Hs. destruct HC as (HM & H2). apply (hd_hdr_refuse_short c _ line (j - i - 1) HM Hk).
  rewrite hd_hb by lia. rewrite hd_hb_len by lia. lia.
Qed.
Lemma hd_ix_ieq : forall c line, (hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
  ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = false ->
  m_header c (hda_sl rest i j) line = (m_refuse c line false, None).
Proof.
  intros c line Hs Hi. destruct HC as (HM & H2). apply (hd_hdr_refuse_ieq c _ line (j - i - 1) HM Hk).
  - rewrite hd_hb by lia. rewrite hd_hb_len by lia. lia.
  - rewrite hd_hb by lia. rewrite hd_firstn_slice by lia. exact Hi.
Qed.
Lemma hd_ix_sp : forall c line, (hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
  ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = true ->
  sp_tab (nth (hda_q1 rest i j + 7) rest 0) = false ->
  m_header c (hda_sl rest i j) line = (m_refuse c line false, None).
Proof.
  intros c line Hs Hi Hsp. destruct HC as (HM & H2). pose proof (hd_line_le rest) as HL.
  apply (hd_hdr_refuse_sp c _ line (j - i - 1) HM Hk).
  - rewrite hd_hb by lia. rewrite hd_hb_len by lia. lia.
  - rewrite hd_hb by lia. rewrite hd_firstn_slice by lia. exact Hi.
  - rewrite hd_hb by lia. rewrite hd_slice_nth by (pose proof (hd_q1r1 rest i j Hij H2); lia). exact Hsp.
Qed.
Lemma hd_ix_name : forall c line, (hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
  ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = true ->
  sp_tab (nth (hda_q1 rest i j + 7) rest 0) = true ->
  (hda_r2 rest i j = hda_q2 rest i j \/ 16 <= hda_r2 rest i j - hda_q2 rest i j)%nat ->
  m_header c (hda_sl rest i j) line = (m_refuse c line false, None).
Proof.
  intros c line Hs Hi Hsp Hn. destruct HC as (HM & H2). pose proof (hd_line_le rest) as HL.
  pose proof (hd_q1r1 rest i j Hij H2) as Q1. pose proof (hd_q2r2 rest i j Hij H2 ltac:(lia)) as Q2.
  apply (hd_hdr_refuse_name c _ line (j - i - 1) HM Hk).
  - rewrite hd_hb by lia. rewrite hd_hb_len by lia. lia.
  - rewrite hd_hb by lia. rewrite hd_firstn_slice by lia. exact Hi.
  - rewrite hd_hb by lia. rewrite hd_slice_nth by lia. exact Hsp.
  - rewrite hd_hb by lia. rewrite hd_nm by lia. rewrite hd_slice_length by lia. lia.
Qed.
Lemma hd_ix_find : forall c line, (hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
  ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = true ->
  sp_tab (nth (hda_q1 rest i j + 7) rest 0) = true ->
  (hda_q2 rest i j < hda_r2 rest i j < hda_q2 rest i j + 16)%nat ->
  m_header c (hda_sl rest i j) line = mh_find c (slice (hda_q2 rest i j) (hda_r2 rest i j) rest) line.
Proof.
  intros c line Hs Hi Hsp Hn. destruct HC as (HM & H2). pose proof (hd_line_le rest) as HL.
  pose proof (hd_q1r1 rest i j Hij H2) as Q1. pose proof (hd_q2r2 rest i j Hij H2 ltac:(lia)) as Q2.
  rewrite <- (hd_nm rest i j Hij H2 ltac:(lia)). rewrite <- (hd_hb rest i j Hij H2).
  apply (hd_hdr_find c _ line (j - i - 1) HM Hk).
  - rewrite hd_hb by lia. rewrite hd_hb_len by lia. lia.
  - rewrite hd_hb by lia. rewrite hd_firstn_slice by lia. exact Hi.
  - rewrite hd_hb by lia. rewrite hd_slice_nth by lia. exact Hsp.
  - rewrite hd_hb by lia. rewrite hd_nm by lia. rewrite hd_slice_length by lia. lia.
Qed.
End ix.

(* the found name is m_find's argument at HFIND: o = q2, |nm| = r2 - q2, inside the line *)
Lemma hd_name_run : forall rest i j, (i < j <= length (mf_line rest))%nat -> (2 <= j - i)%nat ->
  (hda_q1 rest i j + 7 <= hda_r1 rest i j)%nat ->
  length (slice (hda_q2 rest i j) (hda_r2 rest i j) rest) = (hda_r2 rest i j - hda_q2 rest i j)%nat /\
  (hda_q2 rest i j + length (slice (hda_q2 rest i j) (hda_r2 rest i j) rest) <= length (mf_line rest))%nat /\
  firstn (length (slice (hda_q2 rest i j) (hda_r2 rest i j) rest)) (skipn (hda_q2 rest i j) rest) =
    slice (hda_q2 rest i j) (hda_r2 rest i j) rest.
Proof.
  intros rest i j Hij H2 H7. pose proof (hd_line_le rest) as HL.
  pose proof (hd_q1r1 rest i j Hij H2) as Q1. pose proof (hd_q2r2 rest i j Hij H2 H7) as Q2.
  assert (E : length (slice (hda_q2 rest i j) (hda_r2 rest i j) rest) = (hda_r2 rest i j - hda_q2 rest i j)%nat)
    by (apply hd_slice_length; lia).
  split; [exact E|]. split; [rewrite E; lia|]. rewrite E. reflexivity.
Qed.
