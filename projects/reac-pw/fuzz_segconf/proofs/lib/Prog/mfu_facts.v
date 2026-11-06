(** reac-pw/fuzz_segconf, the walks of m_file (both builds use it): facts of the spine's m_file
    model (Spec/SegModel.v) that the pieces S_MF_* and their composition need. Build-independent: it loads only the
    spine, so the plain and the UBSan walks can both import it.
    - the lines: [lines s] for a nonempty text is its first line (break_nl) and the lines of the rest, and the rest is
      shorter than the text;
    - one line (m_line) and the lines (m_lines) add at most one refusal and one overflow per line, keep gen, and
      never shrink seg or kept (so the footprint of a line fits the footprint of the final state), and keep the
      cursor inside seg (cur_ok of the contracts, here [mf_cur_ok]). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Open Scope Z_scope.

(** ** The lines *)

(** break_nl cuts the text at its first newline, or takes the whole text when it has none. *)
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

Lemma break_nl_rest_lt : forall s, s <> [] -> (length (snd (break_nl s)) < length s)%nat.
Proof.
  intros [|b r] H; [congruence|]. pose proof (break_nl_len_cons b r) as L. cbn [length]. lia.
Qed.

Lemma lines_go_S_cons : forall f b r,
  lines_go (S f) (b :: r) = let (l, q) := break_nl (b :: r) in l :: lines_go f q.
Proof. reflexivity. Qed.

Lemma lines_go_fuel : forall f g p, (length p < f)%nat -> (length p < g)%nat -> lines_go f p = lines_go g p.
Proof.
  induction f as [|f IH]; intros g p Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  destruct p as [|b r]; [reflexivity|]. rewrite !lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E.
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  cbn [length] in Hf, Hg. f_equal. apply IH; lia.
Qed.

(** A nonempty text: its first line, then the lines of what follows it. *)
Lemma lines_cons : forall s, s <> [] -> lines s = fst (break_nl s) :: lines (snd (break_nl s)).
Proof.
  intros [|b r] Hs; [congruence|]. unfold lines at 1. cbn [length]. rewrite lines_go_S_cons.
  destruct (break_nl (b :: r)) as [l q] eqn:E. cbn [fst snd].
  assert (HL : (length q <= length r)%nat)
    by (pose proof (break_nl_len_cons b r) as H; rewrite E in H; exact H).
  f_equal. unfold lines. apply lines_go_fuel; lia.
Qed.

Lemma lines_nil : lines [] = [].
Proof. reflexivity. Qed.

(** One more step of the loop: the model state after the head's text is the state after its first line, run over
    the rest (the head's and the tail's posts are the same final state). *)
Lemma m_lines_step : forall st n s, s <> [] ->
  m_lines st n (lines s) = m_lines (m_line st (n + 1) (fst (break_nl s))) (n + 1) (lines (snd (break_nl s))).
Proof. intros st n s Hs. rewrite (lines_cons s Hs). reflexivity. Qed.

(** ** Counters (the plain contract file's m_header_cnt .. m_lines_cnt, restated here so that this file loads
    no image) *)
Lemma mfu_m_header_cnt m l n :
  mc_gen (fst (m_header m l n)) = mc_gen m /\
  mc_refused m <= mc_refused (fst (m_header m l n)) <= mc_refused m + 1 /\
  mc_overflow m <= mc_overflow (fst (m_header m l n)) <= mc_overflow m + 1.
Proof.
  unfold m_header. cbv zeta. destruct (memchr l RBR) as [ci|]; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [m_find ?a ?b] => destruct (m_find a b)
         end; cbn; lia.
Qed.

Lemma mfu_m_key_cnt m g l n :
  mc_gen (m_key m g l n) = mc_gen m /\
  mc_refused m <= mc_refused (m_key m g l n) <= mc_refused m + 1 /\
  mc_overflow (m_key m g l n) = mc_overflow m.
Proof.
  unfold m_key. cbv zeta. destruct (memchr l EQ); [|cbn; lia]. destruct g; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; cbn; lia.
Qed.

Lemma mfu_m_line_cnt st n l :
  mc_gen (fst (m_line st n l)) = mc_gen (fst st) /\
  mc_refused (fst st) <= mc_refused (fst (m_line st n l)) <= mc_refused (fst st) + 1 /\
  mc_overflow (fst st) <= mc_overflow (fst (m_line st n l)) <= mc_overflow (fst st) + 1.
Proof.
  destruct st as [m cur]. unfold m_line. destruct (512 <=? length l)%nat; [cbn; lia|].
  destruct (h_strip (h_cut_comment l)) as [|b s]; [cbn; lia|].
  destruct (b =? LBR); cbn [fst]; [apply mfu_m_header_cnt|].
  pose proof (mfu_m_key_cnt m cur (b :: s) n) as H. lia.
Qed.

(** ** Sizes and the cursor *)

(** The cursor of the loop names an entry of seg (the contracts' cur_ok, with the same text). *)
Definition mf_cur_ok (mc : mconf) (cur : option nat) : Prop :=
  match cur with Some i => (i < length (mc_seg mc))%nat | None => True end.

Lemma upd_nth_length {A} : forall (f : A -> A) l i, length (upd_nth i f l) = length l.
Proof. intros f. induction l as [|x r IH]; intros [|i]; cbn; auto. Qed.

Lemma m_find_go_lt : forall segs name i j, m_find_go segs name i = Some j -> (i <= j < i + length segs)%nat.
Proof.
  induction segs as [|g r IH]; intros name i j E; cbn [m_find_go] in E; [discriminate|].
  destruct ((strlen (ms_name g) =? length name)%nat && leqb (firstn (length name) (ms_name g)) name);
    [injection E as <-; cbn [length]; lia|].
  apply IH in E. cbn [length]. lia.
Qed.

Lemma m_find_lt : forall c name i, m_find c name = Some i -> (i < length (mc_seg c))%nat.
Proof. intros c name i E. apply m_find_go_lt in E. lia. Qed.

Lemma m_refuse_sizes : forall c l k,
  mc_seg (m_refuse c l k) = mc_seg c /\
  (length (mc_kept c) <= length (mc_kept (m_refuse c l k)) <= S (length (mc_kept c)))%nat.
Proof.
  intros c l k. unfold m_refuse. cbv zeta. cbn [mc_seg mc_kept]. split; [reflexivity|].
  destruct (Z.of_nat (length (mc_kept c)) <? 8); [rewrite length_app; cbn [length]|]; lia.
Qed.

(** The sizes a model step leaves: (seg, kept) never shrink, and the cursor stays inside seg. *)
Definition mf_grows (mc mc' : mconf) : Prop :=
  (length (mc_seg mc) <= length (mc_seg mc') /\ length (mc_kept mc) <= length (mc_kept mc'))%nat.

Lemma mf_grows_refl mc : mf_grows mc mc.
Proof. split; lia. Qed.

Lemma mf_grows_trans a b c : mf_grows a b -> mf_grows b c -> mf_grows a c.
Proof. unfold mf_grows. lia. Qed.

Lemma m_refuse_grows c l k : mf_grows c (m_refuse c l k).
Proof. destruct (m_refuse_sizes c l k) as [E L]. unfold mf_grows. rewrite E. lia. Qed.

Lemma m_upd_sizes c i f : mc_seg (m_upd c i f) = upd_nth i f (mc_seg c) /\ mc_kept (m_upd c i f) = mc_kept c.
Proof. split; reflexivity. Qed.

Lemma m_upd_grows c i f : mf_grows c (m_upd c i f).
Proof. unfold mf_grows, m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite upd_nth_length. lia. Qed.

Lemma m_header_ok c l n :
  mf_grows c (fst (m_header c l n)) /\ mf_cur_ok (fst (m_header c l n)) (snd (m_header c l n)).
Proof.
  unfold m_header. cbv zeta. destruct (memchr l RBR) as [ci|];
    [|split; [apply m_refuse_grows|exact I]].
  do 3 (match goal with |- context [if ?b then _ else _] => destruct b end;
        [split; [apply m_refuse_grows|exact I]|]).
  match goal with |- context [m_find c ?nm] => destruct (m_find c nm) as [i|] eqn:Ef end.
  - pose proof (m_find_lt _ _ _ Ef) as Hi. cbn [fst snd].
    destruct (ms_gen (nth i (mc_seg c) mseg_d) =? mc_gen c).
    + pose proof (m_refuse_sizes c n false) as [E _].
      split; [eapply mf_grows_trans; [apply m_refuse_grows|apply m_upd_grows]|].
      unfold mf_cur_ok, m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length, E. exact Hi.
    + split; [apply m_upd_grows|].
      unfold mf_cur_ok, m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact Hi.
  - destruct (32 <=? length (mc_seg c))%nat.
    + split; [|exact I]. cbn [fst].
      eapply mf_grows_trans; [|apply m_refuse_grows]. unfold mf_grows. cbn [mc_seg mc_kept]. lia.
    + cbn [fst snd]. unfold mf_grows, mf_cur_ok, m_set_segs. cbn [mc_seg mc_kept].
      rewrite length_app. cbn [length]. lia.
Qed.

Lemma m_key_grows c g l n : mf_grows c (m_key c g l n).
Proof.
  unfold m_key. cbv zeta. destruct (memchr l EQ); [|apply m_refuse_grows]. destruct g; [|apply m_refuse_grows].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; first [apply m_refuse_grows | apply m_upd_grows].
Qed.

Lemma m_key_seg_len c g l n : length (mc_seg (m_key c g l n)) = length (mc_seg c).
Proof.
  unfold m_key. cbv zeta.
  assert (R : forall ln k, length (mc_seg (m_refuse c ln k)) = length (mc_seg c))
    by (intros ln k; destruct (m_refuse_sizes c ln k) as [E _]; rewrite E; reflexivity).
  assert (U : forall i f, length (mc_seg (m_upd c i f)) = length (mc_seg c))
    by (intros i f; unfold m_upd, m_set_segs; cbn [mc_seg]; apply upd_nth_length).
  destruct (memchr l EQ); [|apply R]. destruct g; [|apply R].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; first [apply R | apply U].
Qed.

Lemma m_line_ok : forall st n l, mf_cur_ok (fst st) (snd st) ->
  mf_grows (fst st) (fst (m_line st n l)) /\ mf_cur_ok (fst (m_line st n l)) (snd (m_line st n l)).
Proof.
  intros [c cur] n l Hc. cbn [fst snd] in Hc. unfold m_line. cbv beta iota zeta.
  destruct (512 <=? length l)%nat.
  - cbn [fst snd]. split; [apply m_refuse_grows|].
    destruct (hd0 (dropwhile blank l) =? LBR); [exact I|].
    destruct cur as [i|]; [|exact I]. unfold mf_cur_ok in *.
    destruct (m_refuse_sizes c n false) as [E _]. rewrite E. exact Hc.
  - destruct (h_strip (h_cut_comment l)) as [|b s]; [split; [apply mf_grows_refl|exact Hc]|].
    destruct (b =? LBR); [apply m_header_ok|].
    cbn [fst snd]. split; [apply m_key_grows|].
    destruct cur as [i|]; [|exact I]. unfold mf_cur_ok in *. rewrite m_key_seg_len. exact Hc.
Qed.

Lemma m_lines_ok : forall ls st n, mf_cur_ok (fst st) (snd st) ->
  mf_grows (fst st) (fst (m_lines st n ls)) /\ mf_cur_ok (fst (m_lines st n ls)) (snd (m_lines st n ls)).
Proof.
  induction ls as [|l r IH]; intros st n Hc; cbn [m_lines]; [split; [apply mf_grows_refl|exact Hc]|].
  destruct (m_line_ok st (n + 1) l Hc) as [G1 C1].
  destruct (IH (m_line st (n + 1) l) (n + 1) C1) as [G2 C2].
  split; [eapply mf_grows_trans; eassumption|exact C2].
Qed.

(** ** The line and the model steps the cuts of S_MF_LINE name (both builds' lib/{,U/}Prog cut files use these)

    At the head the text left is [rest] at p; the line is the bytes before its first '\n' (or all of rest), the text
    after it is [mf_rest rest], at [mf_next p rest] (nl + 1, or the NUL when there is no '\n'). *)
Definition mf_line (rest : list Z) : list Z := fst (break_nl rest).
Definition mf_rest (rest : list Z) : list Z := snd (break_nl rest).
Definition mf_next (p : Z) (rest : list Z) : Z := p + Z.of_nat (length rest - length (mf_rest rest)).

(** The final model from a state st after the line numbered line + 1 (st = m_line (mc, cur) (line + 1) l, or a piece
    of it a cut has reduced it to). *)
Definition mf_fin (st : mconf * option nat) (line : Z) (rest : list Z) : mconf :=
  fst (m_lines st (line + 1) (lines (mf_rest rest))).

(** The tail of m_header after its name checks (SegModel.m_header from `match m_find c nm`, word for word). *)
Definition mh_find (c : mconf) (nm : list Z) (line : Z) : mconf * option nat :=
  match m_find c nm with
  | None =>
      if (32 <=? length (mc_seg c))%nat then
        (m_refuse (MConf (mc_seg c) (mc_overflow c + 1) (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c))
                  line false, None)
      else (m_set_segs c (mc_seg c ++ [ms_with_gen (mc_gen c) (mseg0 nm)]), Some (length (mc_seg c)))
  | Some i =>
      let c1 := if ms_gen (nth i (mc_seg c) mseg_d) =? mc_gen c then m_refuse c line false else c in
      (m_upd c1 i (ms_with_gen (mc_gen c)), Some i)
  end.

(** The tail of m_key after the key k and the value v are cut (SegModel.m_key's `Some ei, Some gi` branch from
    `if ieq k S_role`, word for word). *)
Definition mk_disp (c : mconf) (gi : nat) (k v : list Z) (line : Z) : mconf :=
  if ieq k S_role then
    match h_role_word (h_fold v 64) with
    | Some r => m_upd c gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading c)]))
    | None => m_refuse c line false
    end
  else if ieq k S_model then
    let low := h_fold v 24 in
    match cat_row low with
    | None => m_refuse c line false
    | Some _ => m_upd c gi (ms_with_model low)
    end
  else if ieq k S_ignore then
    if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then
      m_upd c gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading c)]))
    else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then
      m_upd c gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading c)]))
    else m_refuse c line false
  else if ieq k S_knock then m_refuse c line true
  else m_refuse c line false.

(** The head's post and a line's: the final model after the head's text is the one after its first line. *)
Lemma mf_fin_head : forall st line rest, rest <> [] ->
  fst (m_lines st line (lines rest)) = mf_fin (m_line st (line + 1) (mf_line rest)) line rest.
Proof. intros st line rest Hr. unfold mf_fin, mf_line, mf_rest. rewrite (m_lines_step st line rest Hr). reflexivity. Qed.

(** The text left after the line: shorter, and where mf_next points. *)
Lemma mf_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof. intros rest Hr. apply break_nl_rest_lt. exact Hr. Qed.

Lemma mf_line_rest : forall rest,
  (rest = mf_line rest ++ NL :: mf_rest rest /\ (length rest - length (mf_rest rest) = S (length (mf_line rest)))%nat) \/
  (rest = mf_line rest /\ mf_rest rest = [] /\ (length rest - length (mf_rest rest) = length (mf_line rest))%nat).
Proof.
  intros rest. unfold mf_line, mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [fst snd].
  destruct (break_nl_spec rest l q E) as [_ [H|[H1 H2]]].
  - left. split; [exact H|]. rewrite H, length_app. cbn [length]. lia.
  - right. subst q. split; [exact H1|]. split; [reflexivity|]. rewrite H1. cbn [length]. lia.
Qed.
