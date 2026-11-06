(** reac-pw/fuzz_segconf: the pure facts that the pieces P1, P2, P3 of reac_segconf_parse_file use.
    One file for both builds: it Requires only build-independent text (Prog/pf_pieces_spec.v, Spec/SegModel.v,
    Prog/seg_spec.v, Lib/). It proves the pure Props stated in Prog/pf_pieces_spec.v that P1-P3 use, each as
    [<Prop>_holds], and the list helpers the piece walks need. No function of the binary is walked here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** List helpers *)

Lemma pfa_len_skipn {A} (n : nat) (l : list A) : length (skipn n l) = (length l - n)%nat.
Proof. revert l; induction n as [|n IH]; intros [|x l]; cbn; try lia. apply IH. Qed.

Lemma pfa_skipn_suffix {A} (a q : list A) : skipn (length a) (a ++ q) = q.
Proof. induction a as [|x a IH]; cbn; [reflexivity|exact IH]. Qed.

Lemma pfa_skipn_sub_suffix {A} (s a q : list A) : s = a ++ q -> skipn (length s - length q) s = q.
Proof.
  intros ->. rewrite length_app. replace (length a + length q - length q)%nat with (length a) by lia.
  apply pfa_skipn_suffix.
Qed.

Lemma pfa_firstn_app_len {A} (a q : list A) : firstn (length a) (a ++ q) = a.
Proof. induction a as [|x a IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma pfa_firstn_len_firstn {A} (n : nat) (l : list A) : firstn (length (firstn n l)) l = firstn n l.
Proof. revert l; induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma pfa_skipn_map {A B} (f : A -> B) (n : nat) (l : list A) : skipn n (map f l) = map f (skipn n l).
Proof. revert l; induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma pfa_tw_dw (P : Z -> bool) (l : list Z) : takewhile P l ++ dropwhile P l = l.
Proof. induction l as [|a l IH]; cbn; [reflexivity|]. destruct (P a); cbn; [rewrite IH|]; reflexivity. Qed.

(** ** break_nl and lines *)

(** The line ends at a '\n' (which break_nl drops), or it is the whole rest. *)
Lemma break_nl_cases (p : list Z) :
  (p = fst (break_nl p) ++ NL :: snd (break_nl p) /\ ~ In NL (fst (break_nl p))) \/
  (fst (break_nl p) = p /\ snd (break_nl p) = [] /\ ~ In NL p).
Proof.
  induction p as [|b r IH]; cbn [break_nl].
  - right. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. intros [].
  - destruct (Z.eqb_spec b NL) as [E|E].
    + left. subst b. cbn [fst snd app]. split; [reflexivity|]. intros [].
    + revert IH. destruct (break_nl r) as [l q]. cbn [fst snd]. intros IH.
      destruct IH as [[H1 H2]|[H1 [H2 H3]]].
      * left. split; [rewrite H1 at 1; reflexivity|]. intros [H|H]; [congruence|exact (H2 H)].
      * right. subst l q. split; [reflexivity|]. split; [reflexivity|]. intros [H|H]; [congruence|exact (H3 H)].
Qed.

Lemma break_nl_fst_len (p : list Z) : (length (fst (break_nl p)) <= length p)%nat.
Proof.
  destruct (break_nl_cases p) as [[H _]|[H _]].
  - pose proof (f_equal (@length Z) H) as L. rewrite length_app in L. cbn [length] in L. lia.
  - rewrite H. lia.
Qed.

Lemma lines_go_fuel_eq (f1 : nat) : forall (f2 : nat) (p : list Z),
  (length p < f1)%nat -> (length p < f2)%nat -> lines_go f1 p = lines_go f2 p.
Proof.
  induction f1 as [|f1 IH]; intros f2 p H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|]. destruct p as [|b r]; [reflexivity|].
  cbn [lines_go]. pose proof (break_nl_len_cons b r) as L.
  revert L. destruct (break_nl (b :: r)) as [l q]. cbn [snd]. intros L.
  cbn [length] in H1, H2. f_equal. apply IH; lia.
Qed.

Lemma lines_go_cons (f : nat) (b : Z) (r : list Z) :
  lines_go (S f) (b :: r) = fst (break_nl (b :: r)) :: lines_go f (snd (break_nl (b :: r))).
Proof. cbn [lines_go]. destruct (break_nl (b :: r)) as [l q]. reflexivity. Qed.

(** ** The pure Props of pf_pieces_spec.v *)

Lemma L_lines_step_holds : L_lines_step.
Proof.
  unfold L_lines_step. intros p Hp. destruct p as [|b r]; [congruence|].
  change (lines (b :: r)) with (lines_go (S (S (length r))) (b :: r)). rewrite lines_go_cons.
  pose proof (break_nl_len_cons b r) as L.
  f_equal. unfold lines. apply lines_go_fuel_eq; lia.
Qed.

Lemma L_break_nl_holds : L_break_nl.
Proof.
  unfold L_break_nl. induction p as [|b r IH]; intros Hn.
  - right. cbn. split; [reflexivity|]. split; reflexivity.
  - change (nulfree (b :: r)) in Hn. apply nulfree_cons in Hn as [Hb Hr].
    cbn [strchr break_nl].
    destruct (Z.eqb_spec b NL) as [E|E].
    + left. subst b. cbn [fst snd app length]. split; reflexivity.
    + destruct (Z.eqb_spec b 0) as [E0|E0]; [contradiction|].
      specialize (IH Hr). revert IH. destruct (break_nl r) as [l q]. cbn [fst snd]. intros IH.
      destruct IH as [[H1 H2]|[H1 [H2 H3]]].
      * left. rewrite H1. cbn [option_map length app]. split; [reflexivity|]. rewrite H2 at 1. reflexivity.
      * right. rewrite H1. cbn [option_map]. subst l q. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma L_next_holds : L_next.
Proof.
  unfold L_next, pf_next, pf_line. intros s o Ho.
  pose proof (firstn_skipn o s) as Hs.
  pose proof (break_nl_cases (skipn o s)) as C.
  revert Hs C. generalize (skipn o s) as p. intros p Hs C.
  revert C. destruct (break_nl p) as [l q]. cbn [fst snd]. intros C.
  assert (Lf : length (firstn o s) = o) by (rewrite length_firstn; lia).
  pose proof (f_equal (@length Z) Hs) as Ls. rewrite length_app, Lf in Ls.
  destruct C as [[H1 _]|[H1 [H2 _]]].
  - rewrite H1, length_app in Ls. cbn [length] in Ls.
    split; [|split; [|split]].
    + apply (pfa_skipn_sub_suffix s (firstn o s ++ l ++ [NL]) q).
      transitivity (firstn o s ++ p); [symmetry; exact Hs|]. rewrite H1, <- !app_assoc. reflexivity.
    + lia.
    + lia.
    + destruct (Nat.ltb_spec (o + length l) (length s)); lia.
  - subst l q. cbn [length].
    split; [|split; [|split]].
    + apply (pfa_skipn_sub_suffix s s []). rewrite app_nil_r. reflexivity.
    + lia.
    + lia.
    + destruct (Nat.ltb_spec (o + length p) (length s)); lia.
Qed.

Lemma L_line_bytes_holds : L_line_bytes.
Proof.
  unfold L_line_bytes, pf_line. intros s o Hn.
  pose proof (nulfree_skipn o s Hn) as Hp.
  revert Hp. generalize (skipn o s) as p. intros p Hp.
  pose proof (break_nl_nulfree _ Hp) as [Hl _].
  pose proof (break_nl_cases p) as C.
  revert Hl C. destruct (break_nl p) as [l q]. cbn [fst snd]. intros Hl C.
  destruct C as [[H1 H2]|[H1 [H2 H3]]].
  - split; [|split; [exact Hl|exact H2]]. rewrite H1, pfa_firstn_app_len. reflexivity.
  - split; [|split; [exact Hl|rewrite H1; exact H3]]. rewrite H1, firstn_all. reflexivity.
Qed.

Lemma first_at_spec (P : nat -> bool) (fuel : nat) : forall i : nat,
  match first_at P i fuel with
  | Some k => (i <= k < i + fuel)%nat /\ P k = true /\ (forall j, (i <= j < k)%nat -> P j = false)
  | None => forall j, (i <= j < i + fuel)%nat -> P j = false
  end.
Proof.
  induction fuel as [|f IH]; intros i; cbn [first_at].
  - intros j Hj. lia.
  - destruct (P i) eqn:E; cbv beta iota.
    + split; [lia|]. split; [exact E|]. intros j Hj; lia.
    + specialize (IH (S i)). revert IH. destruct (first_at P (S i) f) as [k|]; intros IH.
      * destruct IH as [H1 [H2 H3]]. split; [lia|]. split; [exact H2|].
        intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact E|]. apply H3; lia.
      * intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact E|]. apply IH; lia.
Qed.

Lemma L_strip_holds : L_strip.
Proof.
  unfold L_strip, r_strip_comment. intros l Hn. rewrite (cut_nul_id l Hn). cbv zeta.
  pose proof (first_at_spec (r_comment_at l) (length l) 0) as F.
  revert F. destruct (first_at (r_comment_at l) 0 (length l)) as [k|]; intros F.
  - destruct F as [[_ H1] [H2 H3]]. exists k. split; [lia|]. split; [reflexivity|]. split.
    + intros j Hj. apply H3. lia.
    + intros _. exact H2.
  - exists (length l). split; [lia|]. split; [symmetry; apply firstn_all|]. split.
    + intros j Hj. apply F. lia.
    + intros H. lia.
Qed.

Lemma L_trim_holds : L_trim.
Proof.
  unfold L_trim, r_trim, trim_lead. intros l Hn. rewrite (cut_nul_id l Hn). cbv zeta.
  pose proof (pfa_tw_dw blank l) as E.
  revert E. generalize (takewhile blank l) as tw. intros tw E.
  assert (Hd : skipn (length tw) l = dropwhile blank l).
  { rewrite <- E at 1. apply pfa_skipn_suffix. }
  rewrite Hd. split; [|split].
  - pose proof (f_equal (@length Z) E) as L. rewrite length_app in L. rewrite length_firstn. lia.
  - symmetry. apply pfa_firstn_len_firstn.
  - exact (nulfree_firstn _ _ (nulfree_dropwhile _ _ Hn)).
Qed.

Lemma L_cstr_skipn_holds : L_cstr_skipn.
Proof.
  unfold L_cstr_skipn, cstr_at. intros segs m t s o (bs & slack & Hb & Hz & Hn & Hm) Ho.
  assert (Lb : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  assert (Lf : length (firstn o bs) = o) by (rewrite length_firstn; lia).
  exists (skipn o bs), slack.
  rewrite <- (firstn_skipn o bs), <- app_assoc in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite Lf in Hb.
  split; [exact Hb|]. split; [|split].
  - rewrite <- Hz. unfold zs. symmetry. apply pfa_skipn_map.
  - exact (nulfree_skipn o s Hn).
  - rewrite pfa_len_skipn.
    replace (t + Z.of_nat o + Z.of_nat (length s - o) + 1) with (t + Z.of_nat (length s) + 1) by lia.
    exact Hm.
Qed.

Lemma L_r_lines_app_holds : L_r_lines_app.
Proof.
  unfold L_r_lines_app. intros st n d. revert st n.
  induction d as [|l d IH]; intros st n e.
  - cbn [app r_lines length]. f_equal; lia.
  - destruct st as [[c cur] nm]. cbn [app r_lines length]. rewrite IH. f_equal; lia.
Qed.

Lemma L_parse_start_holds : L_parse_start.
Proof.
  unfold L_parse_start. intros rc0 s lab.
  set (R := r_lines (pf_start rc0 lab, None, []) 0 (lines s)).
  assert (E : r_parse_file rc0 s lab = let '(c2, _, _) := R in (c2, Z.of_nat (length (rc_seg c2))))
    by reflexivity.
  rewrite E. clearbody R. destruct R as [[c2 x] y]. reflexivity.
Qed.

Lemma pfa_tw_break (p : list Z) : takewhile blank p = takewhile blank (fst (break_nl p)).
Proof.
  induction p as [|b r IH]; [reflexivity|]. cbn [break_nl].
  destruct (Z.eqb_spec b NL) as [E|E].
  - subst b. reflexivity.
  - revert IH. destruct (break_nl r) as [l q]. cbn [fst]. intros IH.
    cbn [takewhile]. destruct (blank b); [rewrite IH|]; reflexivity.
Qed.

Lemma O2_strspn_rest_holds : O2_strspn_rest.
Proof.
  unfold O2_strspn_rest. intros rest Hn.
  pose proof (break_nl_nulfree rest Hn) as [Hl _].
  split.
  - destruct (break_nl_cases rest) as [[H1 _]|[H1 _]].
    + left. revert H1. generalize (snd (break_nl rest)) as q. generalize (fst (break_nl rest)) as l.
      intros l q H1. rewrite H1, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    + right. rewrite H1. reflexivity.
  - unfold strspn_blank. rewrite (cut_nul_id rest Hn), (cut_nul_id _ Hl), (pfa_tw_break rest). reflexivity.
Qed.

(** ** Helpers for the piece walks *)

(** The end of the text: no line is left. *)
Lemma lines_skipn_end : forall (s : list Z) (o : nat), (length s <= o)%nat -> lines (skipn o s) = [].
Proof.
  intros s o H. destruct (skipn o s) as [|x r] eqn:E; [reflexivity|].
  pose proof (pfa_len_skipn o s) as L. rewrite E in L. cbn [length] in L. lia.
Qed.

Lemma pfa_skipn_ne : forall (s : list Z) (o : nat), (o < length s)%nat -> skipn o s <> [].
Proof. intros s o H E. pose proof (pfa_len_skipn o s) as L. rewrite E in L. cbn [length] in L. lia. Qed.

(** The next line's offset. *)
Lemma pf_next_le : forall (s : list Z) (o : nat), (o < length s)%nat -> (pf_next s o <= length s)%nat.
Proof. intros s o H. destruct (L_next_holds s o H) as (_ & _ & H3 & _). exact H3. Qed.

Lemma pf_next_gt : forall (s : list Z) (o : nat), (o < length s)%nat -> (o < pf_next s o)%nat.
Proof. intros s o H. destruct (L_next_holds s o H) as (_ & H2 & _). exact H2. Qed.

Lemma pf_next_skipn_lt : forall (s : list Z) (o : nat), (o < length s)%nat ->
  (length (skipn (pf_next s o) s) < length (skipn o s))%nat.
Proof.
  intros s o H. pose proof (pf_next_le s o H). pose proof (pf_next_gt s o H).
  rewrite !pfa_len_skipn. lia.
Qed.

(** One line consumed: the account moves to the next line's offset. *)
Lemma pf_lctx_next : forall s o ln d, ~ In 0 s -> pf_lctx s o ln d -> (o < length s)%nat ->
  pf_lctx s (pf_next s o) (ln + 1) (d ++ [pf_line s o]).
Proof.
  intros s o ln d _ (Ho & Hl & Hln & Hle) Hlt.
  destruct (L_next_holds s o Hlt) as (Hsk & Hgt & Hle' & _).
  unfold pf_lctx. split; [exact Hle'|]. split; [|split].
  - rewrite Hl, <- app_assoc. f_equal. cbn [app].
    rewrite (L_lines_step_holds (skipn o s) (pfa_skipn_ne s o Hlt)), Hsk. reflexivity.
  - rewrite length_app. cbn [length]. lia.
  - lia.
Qed.

(** The account at the start (P1) and at the end of the text (the tail's exit to DONE). *)
Lemma pf_lctx_start : forall s, pf_lctx s 0 0 [].
Proof.
  intros s. unfold pf_lctx. cbn [skipn length app]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|lia].
Qed.

Lemma pf_lctx_done : forall s o ln d, pf_lctx s o ln d -> (length s <= o)%nat -> lines s = d.
Proof. intros s o ln d (_ & Hl & _) H. rewrite Hl, (lines_skipn_end s o H), app_nil_r. reflexivity. Qed.

(** One pass of the loop in the spine: the lines left at o are the line at o, then the lines left at pf_next s o. *)
Lemma r_lines_skipn_step : forall s o st ln, (o < length s)%nat ->
  r_lines st ln (lines (skipn o s)) =
  r_lines (let '(c, cur, nm) := st in r_line c cur nm (ln + 1) (pf_line s o)) (ln + 1)
          (lines (skipn (pf_next s o) s)).
Proof.
  intros s o st ln Hlt. destruct (L_next_holds s o Hlt) as (Hsk & _).
  rewrite (L_lines_step_holds (skipn o s) (pfa_skipn_ne s o Hlt)), Hsk.
  destruct st as [[c cur] nm]. cbn [r_lines]. reflexivity.
Qed.

(** The spine's state after one more line. *)
Lemma pf_spine_snoc : forall rc0 lab d l,
  pf_spine rc0 lab (d ++ [l]) =
  (let '(c, cur, nm) := pf_spine rc0 lab d in r_line c cur nm (Z.of_nat (length d) + 1) l).
Proof.
  intros rc0 lab d l. unfold pf_spine. rewrite L_r_lines_app_holds.
  destruct (r_lines (pf_start rc0 lab, None, []) 0 d) as [[c cur] nm]. cbn [r_lines].
  rewrite Z.add_0_l. reflexivity.
Qed.

(** The counters' room. *)
Lemma pf_cnt_mono : forall rc k k', (k' <= k)%nat -> pf_cnt rc k -> pf_cnt rc k'.
Proof. unfold pf_cnt. intros rc k k' H [H1 H2]. split; lia. Qed.

Lemma pfa_refuse_refused : forall c l f a, rc_refused (refuse c l f a) = rc_refused c + 1.
Proof. intros c l f a. unfold refuse. cbv zeta. destruct (8 <=? _); [reflexivity|]. destruct (_ || _); reflexivity. Qed.

(** A refusal takes one unit of c->refused's room; the line it refuses took at least one byte. *)
Lemma pf_cnt_refuse : forall rc ln f a k k', (k' < k)%nat -> pf_cnt rc k -> pf_cnt (refuse rc ln f a) k'.
Proof.
  unfold pf_cnt. intros rc ln f a k k' Hk [H1 H2].
  rewrite pfa_refuse_refused. destruct (refuse_proj rc ln f a) as (_ & Ho & _). rewrite Ho. split; lia.
Qed.

(** The line's bytes. *)
Lemma pf_line_len_le : forall s o, (length (pf_line s o) <= length (skipn o s))%nat.
Proof. intros s o. unfold pf_line. apply break_nl_fst_len. Qed.

Lemma pf_tline_nul : forall s o, ~ In 0 s -> ~ In 0 (pf_tline s o).
Proof.
  intros s o _. unfold pf_tline, r_trim. cbv zeta.
  exact (nulfree_firstn _ _ (nulfree_dropwhile _ _ (cut_nul_nulfree _))).
Qed.

(** r_line on the line at o, unfolded: the long branch (P3) and the short one (P2's dispatch). *)
Lemma r_line_long : forall rc cur nm ln s o, (512 <= length (pf_line s o))%nat ->
  r_line rc cur nm ln (pf_line s o) =
  (refuse rc ln F_long [AI 511],
   (if (strspn_blank (pf_line s o) <? length (pf_line s o))%nat &&
       (nth (strspn_blank (pf_line s o)) (pf_line s o) 0 =? LBR) then None else cur),
   nm).
Proof.
  intros rc cur nm ln s o H. unfold r_line. cbv zeta.
  destruct (Nat.leb_spec 512 (length (pf_line s o))) as [_|C]; [reflexivity|lia].
Qed.

Lemma r_line_short : forall rc cur nm ln s o, (length (pf_line s o) < 512)%nat ->
  r_line rc cur nm ln (pf_line s o) =
  (if hd0 (pf_tline s o) =? 0 then (rc, cur, nm)
   else if hd0 (pf_tline s o) =? LBR then r_header rc nm ln (pf_tline s o)
   else r_key rc cur nm ln (pf_tline s o)).
Proof.
  intros rc cur nm ln s o H. unfold r_line. cbv zeta.
  destruct (Nat.leb_spec 512 (length (pf_line s o))) as [C|_]; [lia|reflexivity].
Qed.

Lemma pfa_takewhile_len (P : Z -> bool) (l : list Z) : (length (takewhile P l) <= length l)%nat.
Proof. induction l as [|a l IH]; cbn; [lia|]. destruct (P a); cbn; lia. Qed.

(** The long branch's choice of cur, read as the binary reads it (P3, 0x14e10 .. 0x14e2c): strspn over the rest of
    the text from the line's start, then at[lead] == '['. *)
Lemma pfa_long_pick (p : list Z) (cur : option nat) : ~ In 0 p ->
  (if (strspn_blank (fst (break_nl p)) <? length (fst (break_nl p)))%nat &&
      (nth (strspn_blank (fst (break_nl p))) (fst (break_nl p)) 0 =? LBR) then None else cur) =
  (if nth (strspn_blank p) p 0 =? LBR then None else cur).
Proof.
  intros Hn. destruct (O2_strspn_rest_holds p Hn) as [_ Hsp].
  assert (Hle : (strspn_blank p <= length (fst (break_nl p)))%nat).
  { rewrite Hsp. unfold strspn_blank.
    pose proof (cut_nul_len (fst (break_nl p))) as A.
    pose proof (pfa_takewhile_len blank (cut_nul (fst (break_nl p)))) as B. lia. }
  rewrite <- Hsp. pose proof (break_nl_cases p) as C.
  revert Hle C. generalize (strspn_blank p) as k. intros k Hle C.
  revert Hle C. generalize (snd (break_nl p)) as q. generalize (fst (break_nl p)) as l. intros l q Hle C.
  destruct C as [[H1 _]|[H1 _]].
  - destruct (Nat.ltb_spec k (length l)) as [Hlt|Hge]; cbn [andb].
    + rewrite H1, app_nth1 by exact Hlt. reflexivity.
    + replace k with (length l) by lia. rewrite H1, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - subst l. destruct (Nat.ltb_spec k (length p)) as [Hlt|Hge]; cbn [andb].
    + reflexivity.
    + rewrite nth_overflow by exact Hge. reflexivity.
Qed.

Lemma r_line_long_rest : forall rc cur nm ln s o, ~ In 0 s -> (512 <= length (pf_line s o))%nat ->
  r_line rc cur nm ln (pf_line s o) =
  (refuse rc ln F_long [AI 511], (if nth (strspn_blank (skipn o s)) (skipn o s) 0 =? LBR then None else cur), nm).
Proof.
  intros rc cur nm ln s o Hn Hlen. rewrite (r_line_long rc cur nm ln s o Hlen). unfold pf_line.
  rewrite (pfa_long_pick (skipn o s) cur (nulfree_skipn o s Hn)). reflexivity.
Qed.

(** The counters' room at the loop head of P1: reader_pre's bounds and the text's 65535 bytes. *)
Lemma pf_cnt_start : forall rc0 lab (k : nat),
  rc_refused rc0 + 2 ^ 17 < 2 ^ 32 -> rc_overflow rc0 + 2 ^ 17 < 2 ^ 32 -> (k <= 65535)%nat ->
  pf_cnt (pf_start rc0 lab) k.
Proof.
  intros rc0 lab k H1 H2 Hk.
  assert (Hz : Z.of_nat k <= 65535).
  { apply Nat2Z.inj_le in Hk. assert (E : Z.of_nat 65535%nat = 65535) by reflexivity. rewrite E in Hk. exact Hk. }
  clear Hk. unfold pf_cnt, pf_start. cbn [rc_refused rc_overflow]. split; lia.
Qed.

(** The line count at a line start: 0 <= ln <= o <= length s (UBSan's lineno++ check). *)
Lemma pf_lctx_ln : forall s o ln d, pf_lctx s o ln d -> 0 <= ln <= Z.of_nat o /\ (o <= length s)%nat.
Proof. intros s o ln d (Ho & _ & Hln & Hle). lia. Qed.

(** The comment cut the strip loop finds (P2, 0x14e68): the first k with a comment start at k, or the end of the
    line, is where r_strip_comment cuts. *)
Lemma r_strip_comment_at : forall (l : list Z) (k : nat), ~ In 0 l -> (k <= length l)%nat ->
  (forall j, (j < k)%nat -> r_comment_at l j = false) -> ((k < length l)%nat -> r_comment_at l k = true) ->
  r_strip_comment l = firstn k l.
Proof.
  intros l k Hn Hk Hb He.
  destruct (L_strip_holds l Hn) as (k0 & Hk0 & E & Hb0 & He0). rewrite E.
  destruct (Nat.lt_trichotomy k k0) as [Hlt|[->|Hgt]].
  - assert (T : r_comment_at l k = true) by (apply He; lia). rewrite (Hb0 k Hlt) in T. discriminate.
  - reflexivity.
  - assert (T : r_comment_at l k0 = true) by (apply He0; lia). rewrite (Hb k0 Hgt) in T. discriminate.
Qed.

(** Lengths of the trimmed line (buf bounds). *)
Lemma pfa_dropwhile_len (P : Z -> bool) (l : list Z) : (length (dropwhile P l) <= length l)%nat.
Proof. induction l as [|a l IH]; cbn; [lia|]. destruct (P a); cbn; lia. Qed.

Lemma r_trim_len_le : forall l, (length (r_trim l) <= length l)%nat.
Proof.
  intros l. unfold r_trim. cbv zeta. rewrite length_firstn.
  pose proof (pfa_dropwhile_len blank (cut_nul l)). pose proof (cut_nul_len l). lia.
Qed.

Lemma r_strip_comment_len_le : forall l, (length (r_strip_comment l) <= length l)%nat.
Proof.
  intros l. unfold r_strip_comment. cbv zeta. pose proof (cut_nul_len l).
  destruct (first_at _ _ _); [rewrite length_firstn|]; lia.
Qed.

Lemma pf_tline_len_le : forall s o, (length (pf_tline s o) <= length (pf_line s o))%nat.
Proof.
  intros s o. unfold pf_tline.
  pose proof (r_trim_len_le (r_strip_comment (pf_line s o))). pose proof (r_strip_comment_len_le (pf_line s o)). lia.
Qed.
