(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT (HEAD 0x860d0 -> LONG / HDR / KEY / TAIL): the model
   facts the segment's walk needs, over SegModel and m_file_m.v's line terms (mf_line, mf_rest, mf_next, mf_fin).
   Pure list facts; no instruction is executed here. The FRONT segment lane of the G2 walk owner's G2.

   COPIED, with their proofs, from the plain / image-B owner's plain model files at dec616e11c2f (those
   files are not in this tree and Require the plain integration, so they are copied, with the prefix fr_):
     lib/Prog/mfu_facts.v:17-66 (break_nl_spec .. m_lines_step), :274-290 (mf_fin_head, mf_rest_lt, mf_line_rest);
     lib/Prog/mfp_facts.v:13-24 (blank_gt32, blank_mask), :43-58 (slice_length, mff_line_split, mf_line_nth),
     :115-147 (all_blank, dropwhile_blank_idx, h_strip_idx), :175-203 (cut_at, mff_cut_at, mff_cut_go, h_cut_idx),
     :282-310 (m_line_long, m_line_empty, m_line_hdr, m_line_key).
   NEW here: the strchr answer as the line split (fr_break_first .. fr_next_nonl, fr_nl), the comment cut and the
   strip at the indices the code stops at (fr_cut_at_first, fr_cut_all, fr_slice_firstn, fr_nth_firstn), and the
   model equation of each exit of the segment from the head's (fr_eq_long, fr_eq_empty, fr_eq_hdr, fr_eq_key). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_m.
Import ListNotations.
Local Open Scope Z_scope.

(* ======================================== the lines ======================================== *)
(* mfu_facts.v:17-28 *)
Lemma fr_break_nl_spec : forall s l q, break_nl s = (l, q) ->
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

(* mfu_facts.v:30-33 *)
Lemma fr_break_nl_rest_lt : forall s, s <> [] -> (length (snd (break_nl s)) < length s)%nat.
Proof.
  intros [|b r] H; [congruence|]. pose proof (break_nl_len_cons b r) as L. cbn [length]. lia.
Qed.

(* mfu_facts.v:35-47 *)
Lemma fr_lines_go_S_cons : forall f b r,
  lines_go (S f) (b :: r) = let (l, q) := break_nl (b :: r) in l :: lines_go f q.
Proof. reflexivity. Qed.

Lemma fr_lines_go_fuel : forall f g p, (length p < f)%nat -> (length p < g)%nat -> lines_go f p = lines_go g p.
Proof.
  induction f as [|f IH]; intros g p Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  destruct p as [|b r]; [reflexivity|]. rewrite !fr_lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E.
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  cbn [length] in Hf, Hg. f_equal. apply IH; lia.
Qed.

(* mfu_facts.v:50-57 *)
Lemma fr_lines_cons : forall s, s <> [] -> lines s = fst (break_nl s) :: lines (snd (break_nl s)).
Proof.
  intros [|b r] Hs; [congruence|]. unfold lines at 1. cbn [length]. rewrite fr_lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E. cbn [fst snd].
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  f_equal. unfold lines. apply fr_lines_go_fuel; lia.
Qed.

(* mfu_facts.v:64-66 *)
Lemma fr_m_lines_step : forall st n s, s <> [] ->
  m_lines st n (lines s) = m_lines (m_line st (n + 1) (fst (break_nl s))) (n + 1) (lines (snd (break_nl s))).
Proof. intros st n s Hs. rewrite (fr_lines_cons s Hs). reflexivity. Qed.

(* mfu_facts.v:274-276 *)
Lemma fr_mf_fin_head : forall st line rest, rest <> [] ->
  fst (m_lines st line (lines rest)) = mf_fin (m_line st (line + 1) (mf_line rest)) line rest.
Proof.
  intros st line rest Hr. unfold mf_fin, mf_line, mf_rest. rewrite (fr_m_lines_step st line rest Hr). reflexivity.
Qed.

(* mfu_facts.v:279-280 *)
Lemma fr_mf_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof. intros rest Hr. apply fr_break_nl_rest_lt. exact Hr. Qed.

(* mfu_facts.v:282-290 *)
Lemma fr_mf_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (fr_break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.

(* ===================================== bytes and lists ===================================== *)
(* mfp_facts.v:13-24 *)
Lemma fr_blank_gt32 : forall c, 32 < c -> blank c = false.
Proof.
  intros c H. unfold blank.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
Lemma fr_blank_mask : forall c, 0 <= c <= 32 -> blank c = (Z.land (Z.shiftr 0x100002200 c) 1 =? 1).
Proof.
  intros c Hc.
  assert (E : exists n, c = Z.of_nat n /\ (n <= 32)%nat) by (exists (Z.to_nat c); split; lia).
  destruct E as [n [-> Hn]]. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(* mfp_facts.v:43-46 *)
Lemma fr_slice_length : forall (l : list Z) i j, (i <= j <= length l)%nat -> length (slice i j l) = (j - i)%nat.
Proof.
  intros l i j H. unfold slice. rewrite length_firstn, length_skipn. apply Nat.min_l. lia.
Qed.
(* mfp_facts.v:48-58 *)
Lemma fr_line_split : forall rest, exists R, rest = mf_line rest ++ R.
Proof.
  intros rest. destruct (fr_mf_line_rest rest) as [[E _]|[E _]].
  - exists (NL :: mf_rest rest). exact E.
  - exists []. rewrite app_nil_r. exact E.
Qed.
Lemma fr_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (fr_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [rewrite <- E; reflexivity|]. apply app_nth1. exact Hi.
Qed.
Lemma fr_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (fr_line_split rest) as [R E].
  assert (H : length rest = length (mf_line rest ++ R)) by (rewrite <- E; reflexivity).
  rewrite length_app in H. lia.
Qed.

(* ======================================== the strip ======================================== *)
(* mfp_facts.v:115-147 *)
Definition all_blank (u : list Z) (a b : nat) : Prop := forall k, (a <= k < b)%nat -> blank (nth k u 0) = true.

Lemma fr_dropwhile_blank_idx : forall u i, (i <= length u)%nat -> all_blank u 0 i ->
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
Lemma fr_h_strip_idx : forall u i j, (i <= j <= length u)%nat -> all_blank u 0 i ->
  (i = length u \/ blank (nth i u 0) = false) -> all_blank u j (length u) ->
  (j = i \/ blank (nth (j - 1) u 0) = false) ->
  h_strip u = slice i j u.
Proof.
  unfold all_blank. intros u i j [Hij Hj] Hb0 Hs Hb1 He. unfold h_strip.
  rewrite (fr_dropwhile_blank_idx u i) by first [lia | assumption].
  assert (Lw : length (rev (skipn i u)) = (length u - i)%nat) by (rewrite length_rev, length_skipn; reflexivity).
  rewrite (fr_dropwhile_blank_idx (rev (skipn i u)) (length u - j)).
  - rewrite skipn_rev, rev_involutive, length_skipn. unfold slice. f_equal. lia.
  - rewrite Lw. lia.
  - intros k Hk. rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    apply Hb1. lia.
  - destruct (Nat.eq_dec j i) as [->|Hne]; [left; rewrite Lw; reflexivity|right].
    destruct He as [He|He]; [lia|].
    rewrite rev_nth by (rewrite length_skipn; lia). rewrite length_skipn, nth_skipn.
    replace (i + (length u - i - S (length u - j)))%nat with (j - 1)%nat by lia. exact He.
Qed.

(* ===================================== the comment cut ===================================== *)
(* mfp_facts.v:175-203 *)
Definition cut_at (l : list Z) (q : nat) : bool :=
  is_mark (nth q l 0) && ((q =? 0)%nat || sp_tab (nth (q - 1) l 0)).
Definition fr_cut_at_go (first : bool) (prev : Z) (l : list Z) (k : nat) : bool :=
  is_mark (nth k l 0) && match k with O => first || sp_tab prev | S k' => sp_tab (nth k' l 0) end.
Lemma fr_cut_go : forall l first prev q, (q <= length l)%nat ->
  (forall k, (k < q)%nat -> fr_cut_at_go first prev l k = false) ->
  (q = length l \/ fr_cut_at_go first prev l q = true) -> h_cut_go first prev l = firstn q l.
Proof.
  induction l as [|x r IH]; intros first prev q Hq Hk Hs; [destruct q; reflexivity|].
  cbn [h_cut_go]. destruct q as [|q].
  - destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate|].
    change (is_mark x && (first || sp_tab prev) = true) in Hs. rewrite Hs. reflexivity.
  - pose proof (Hk 0%nat ltac:(lia)) as H0. change (is_mark x && (first || sp_tab prev) = false) in H0.
    rewrite H0. cbn [firstn]. f_equal. cbn [length] in Hq. apply IH; [lia| |].
    + intros k Hk'. specialize (Hk (S k) ltac:(lia)). unfold fr_cut_at_go in Hk |- *.
      destruct k; exact Hk.
    + destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right].
      unfold fr_cut_at_go in Hs |- *. destruct q; exact Hs.
Qed.
Lemma fr_h_cut_idx : forall l q, (q <= length l)%nat -> (forall k, (k < q)%nat -> cut_at l k = false) ->
  (q = length l \/ cut_at l q = true) -> h_cut_comment l = firstn q l.
Proof.
  intros l q Hq Hk Hs. unfold h_cut_comment. apply fr_cut_go; [exact Hq| |].
  - intros k Hk'. specialize (Hk k Hk'). unfold cut_at, fr_cut_at_go in *.
    destruct k as [|k]; [exact Hk|]. replace (S k - 1)%nat with k in Hk by lia. exact Hk.
  - destruct Hs as [Hs|Hs]; [left; exact Hs|right]. unfold cut_at, fr_cut_at_go in *.
    destruct q as [|q]; [exact Hs|]. replace (S q - 1)%nat with q in Hs by lia. exact Hs.
Qed.
(* the cut as the comment loop finds it: the first index q with a mark at q and q = 0 or a space or a tab before
   it, else the whole line *)
Lemma fr_cut_at_first : forall l q, (q < length l)%nat -> (forall k, (k < q)%nat -> cut_at l k = false) ->
  cut_at l q = true -> h_cut_comment l = firstn q l /\ length (h_cut_comment l) = q.
Proof.
  intros l q Hq Hk Hc. rewrite (fr_h_cut_idx l q) by first [lia | assumption | right; exact Hc].
  split; [reflexivity|]. rewrite length_firstn. lia.
Qed.
Lemma fr_cut_all : forall l, (forall k, (k < length l)%nat -> cut_at l k = false) ->
  h_cut_comment l = l /\ length (h_cut_comment l) = length l.
Proof.
  intros l Hk. rewrite (fr_h_cut_idx l (length l)) by first [lia | assumption | left; reflexivity].
  rewrite firstn_all. split; reflexivity.
Qed.
Lemma fr_cut_len : forall l, (length (h_cut_comment l) <= length l)%nat /\ exists q, h_cut_comment l = firstn q l.
Proof.
  intros l. unfold h_cut_comment. generalize true, 0. induction l as [|x r IH]; intros f pv; cbn [h_cut_go].
  - split; [cbn; lia|]. exists 0%nat. reflexivity.
  - destruct (is_mark x && (f || sp_tab pv)).
    + split; [cbn; lia|]. exists 0%nat. reflexivity.
    + destruct (IH false x) as [IH1 [q Hq]]. cbn [length]. split; [lia|]. exists (S q). rewrite Hq. reflexivity.
Qed.
(* the cut's bytes are the line's *)
Lemma fr_nth_firstn : forall (l : list Z) c k, (k < c)%nat -> nth k (firstn c l) 0 = nth k l 0.
Proof.
  intros l c k Hk. rewrite nth_firstn. destruct (Nat.ltb_spec k c); [reflexivity|lia].
Qed.
Lemma fr_slice_firstn : forall (l : list Z) c i j, (j <= c)%nat -> slice i j (firstn c l) = slice i j l.
Proof.
  intros l c i j Hj. unfold slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.
Lemma fr_cut_nth : forall l k, (k < length (h_cut_comment l))%nat -> nth k (h_cut_comment l) 0 = nth k l 0.
Proof.
  intros l k Hk. destruct (fr_cut_len l) as [_ [q Hq]]. rewrite Hq in *. rewrite length_firstn in Hk.
  apply fr_nth_firstn. lia.
Qed.
Lemma fr_cut_slice : forall l i j, (j <= length (h_cut_comment l))%nat ->
  slice i j (h_cut_comment l) = slice i j l.
Proof.
  intros l i j Hj. destruct (fr_cut_len l) as [_ [q Hq]]. rewrite Hq in *. rewrite length_firstn in Hj.
  apply fr_slice_firstn. lia.
Qed.

(* ===================================== strchr's answer ===================================== *)
(* the first '\n' at j: the line is the j bytes before it, the text after it starts at j + 1 *)
Lemma fr_break_first : forall rest j, (j < length rest)%nat -> nth j rest 0 = NL -> ~ In NL (firstn j rest) ->
  break_nl rest = (firstn j rest, skipn (S j) rest).
Proof.
  induction rest as [|b r IH]; intros j Hj Hn Hf; cbn [length] in Hj; [lia|].
  cbn [break_nl]. destruct j as [|j].
  - cbn [nth] in Hn. subst b. rewrite Z.eqb_refl. reflexivity.
  - cbn [firstn In] in Hf. destruct (Z.eqb_spec b NL) as [Hb|Hb]; [exfalso; apply Hf; left; exact Hb|].
    cbn [nth] in Hn. rewrite (IH j); [reflexivity|lia|exact Hn|intros Hi; apply Hf; right; exact Hi].
Qed.
(* the value a0 holds after `strchr(p, '\n')` (0 when there is no '\n') *)
Definition fr_nl (p : Z) (rest : list Z) : Z :=
  if existsb (fun b => b =? NL) rest then p + Z.of_nat (length (mf_line rest)) else 0.
Lemma fr_firstNL : forall rest j, (j < length rest)%nat -> nth j rest 0 = NL -> ~ In NL (firstn j rest) ->
  mf_line rest = firstn j rest /\ mf_rest rest = skipn (S j) rest /\ length (mf_line rest) = j /\
  existsb (fun b => b =? NL) rest = true.
Proof.
  intros rest j Hj Hn Hf. unfold mf_line, mf_rest. rewrite (fr_break_first rest j Hj Hn Hf). cbn [fst snd].
  split; [reflexivity|]. split; [reflexivity|]. split; [rewrite length_firstn; lia|].
  apply existsb_exists. exists (nth j rest 0). split; [apply nth_In; exact Hj|]. rewrite Hn. apply Z.eqb_refl.
Qed.
Lemma fr_noNL : forall rest, ~ In NL rest ->
  mf_line rest = rest /\ mf_rest rest = [] /\ existsb (fun b => b =? NL) rest = false.
Proof.
  intros rest H. destruct (fr_mf_line_rest rest) as [[E _]|[E1 [E2 _]]].
  - exfalso. apply H. rewrite E. apply in_or_app. right. left. reflexivity.
  - split; [symmetry; exact E1|]. split; [exact E2|].
    apply not_true_iff_false. intros Hx. apply existsb_exists in Hx as [x [Hx Hb]].
    apply Z.eqb_eq in Hb. subst x. exact (H Hx).
Qed.
Lemma fr_next_nl : forall p rest j, (j < length rest)%nat -> nth j rest 0 = NL -> ~ In NL (firstn j rest) ->
  mf_next p rest = p + Z.of_nat j + 1.
Proof.
  intros p rest j Hj Hn Hf. unfold mf_next. destruct (fr_firstNL rest j Hj Hn Hf) as (_ & E & _).
  rewrite E, length_skipn. lia.
Qed.
Lemma fr_next_nonl : forall p rest, ~ In NL rest -> mf_next p rest = p + Z.of_nat (length rest).
Proof.
  intros p rest H. unfold mf_next. destruct (fr_noNL rest H) as (_ & E & _). rewrite E. cbn [length]. lia.
Qed.
(* the next line's address from the head: the '\n' + 1 when there is one, else the NUL *)
Lemma fr_next_cases : forall p rest,
  (existsb (fun b => b =? NL) rest = true /\ mf_next p rest = p + Z.of_nat (length (mf_line rest)) + 1) \/
  (existsb (fun b => b =? NL) rest = false /\ mf_next p rest = p + Z.of_nat (length (mf_line rest)) /\
   mf_line rest = rest).
Proof.
  intros p rest. unfold mf_next. destruct (fr_mf_line_rest rest) as [[E L]|[E1 [E2 L]]].
  - left. split; [|rewrite L; lia].
    apply existsb_exists. exists NL. split; [|apply Z.eqb_refl].
    rewrite E. apply in_or_app. right. left. reflexivity.
  - right. split; [|split; [rewrite L; lia | symmetry; exact E1]].
    apply not_true_iff_false. intros Hx. apply existsb_exists in Hx as [x [Hx Hb]].
    apply Z.eqb_eq in Hb. subst x. rewrite E1 in Hx.
    destruct (fr_break_nl_spec rest (mf_line rest) (mf_rest rest)) as [N _];
      [unfold mf_line, mf_rest; destruct (break_nl rest); reflexivity|].
    exact (N Hx).
Qed.

(* ==================================== the line's step ==================================== *)
(* mfp_facts.v:282-310 *)
Lemma fr_m_line_long : forall c cur n l, (512 <= length l)%nat ->
  m_line (c, cur) n l = (m_refuse c n false, if hd0 (dropwhile blank l) =? LBR then None else cur).
Proof.
  intros c cur n l H. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
Qed.
Lemma fr_m_line_empty : forall c cur n l, (length l < 512)%nat -> h_strip (h_cut_comment l) = [] ->
  m_line (c, cur) n l = (c, cur).
Proof.
  intros c cur n l H1 H2. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1), H2. reflexivity.
Qed.
Lemma fr_m_line_hdr : forall c cur n l, (length l < 512)%nat -> hd0 (h_strip (h_cut_comment l)) = LBR ->
  m_line (c, cur) n l = m_header c (h_strip (h_cut_comment l)) n.
Proof.
  intros c cur n l H1 H2. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1).
  revert H2. destruct (h_strip (h_cut_comment l)) as [|b s]; cbn [hd0]; intros H2; [discriminate|].
  subst b. reflexivity.
Qed.
Lemma fr_m_line_key : forall c cur n l, (length l < 512)%nat -> h_strip (h_cut_comment l) <> [] ->
  hd0 (h_strip (h_cut_comment l)) <> LBR ->
  m_line (c, cur) n l = (m_key c cur (h_strip (h_cut_comment l)) n, cur).
Proof.
  intros c cur n l H1 H2 H3. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_gt _ _) H1).
  revert H2 H3. destruct (h_strip (h_cut_comment l)) as [|b s]; intros H2 H3; [congruence|].
  cbn [hd0] in H3. rewrite (proj2 (Z.eqb_neq b LBR) H3). reflexivity.
Qed.

(* the model equation of each exit, from the head's *)
Lemma fr_eq_long : forall st line rest F, rest <> [] -> fst (m_lines st line (lines rest)) = F ->
  mf_fin (m_line st (line + 1) (mf_line rest)) line rest = F.
Proof. intros st line rest F Hr H. rewrite <- H. symmetry. apply fr_mf_fin_head. exact Hr. Qed.
Lemma fr_eq_empty : forall mcc cur line rest F, rest <> [] -> fst (m_lines (mcc, cur) line (lines rest)) = F ->
  (length (mf_line rest) < 512)%nat -> h_strip (h_cut_comment (mf_line rest)) = [] ->
  fst (m_lines (mcc, cur) (line + 1) (lines (mf_rest rest))) = F.
Proof.
  intros mcc cur line rest F Hr H HL HS. rewrite (fr_mf_fin_head (mcc, cur) line rest Hr) in H.
  rewrite (fr_m_line_empty mcc cur (line + 1) (mf_line rest) HL HS) in H. exact H.
Qed.
Lemma fr_eq_hdr : forall mcc cur line rest F, rest <> [] -> fst (m_lines (mcc, cur) line (lines rest)) = F ->
  (length (mf_line rest) < 512)%nat -> hd0 (h_strip (h_cut_comment (mf_line rest))) = LBR ->
  mf_fin (m_header mcc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest = F.
Proof.
  intros mcc cur line rest F Hr H HL HS. rewrite (fr_mf_fin_head (mcc, cur) line rest Hr) in H.
  rewrite (fr_m_line_hdr mcc cur (line + 1) (mf_line rest) HL HS) in H. exact H.
Qed.
Lemma fr_eq_key : forall mcc cur line rest F, rest <> [] -> fst (m_lines (mcc, cur) line (lines rest)) = F ->
  (length (mf_line rest) < 512)%nat -> h_strip (h_cut_comment (mf_line rest)) <> [] ->
  hd0 (h_strip (h_cut_comment (mf_line rest))) <> LBR ->
  mf_fin (m_key mcc cur (h_strip (h_cut_comment (mf_line rest))) (line + 1), cur) line rest = F.
Proof.
  intros mcc cur line rest F Hr H HL HS HB. rewrite (fr_mf_fin_head (mcc, cur) line rest Hr) in H.
  rewrite (fr_m_line_key mcc cur (line + 1) (mf_line rest) HL HS HB) in H. exact H.
Qed.
