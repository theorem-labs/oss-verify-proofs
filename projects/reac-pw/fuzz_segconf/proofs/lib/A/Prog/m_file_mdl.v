(* m_file on fuzz_segconf.asan (image A): the model's sizes along the line loop, shared by the m_file segment lanes
   (the m_file cut-statement lane's ruling): one model step never shrinks seg or kept and keeps the cursor inside seg, and so the
   kept list of any state on the way is no longer than the final model's, the premise of the shared m_refuse step
   (lib/A/Prog/m_file_rf.v mf_refuse_step). Build-independent: SegModel and m_file_m.v's model terms only.
   Restated from the plain / image-B owner's plain proof lib/Prog/mfu_facts.v:112-222 at commit dec616e11c2f (a
   file outside this tree): upd_nth_length, m_find_go_lt, m_find_lt, m_refuse_sizes, mf_grows (+ refl / trans),
   m_refuse_grows, m_upd_sizes, m_upd_grows, m_header_ok, m_key_grows, m_key_seg_len, m_line_ok, m_lines_ok;
   mf_cur_ok is m_file_m.v's (the same text as mfu_facts.v:109-110). mf_cur_ok_refuse, mf_kept_le_final and
   mf_kept_le_refuse are this lane's. The KEYA segment lane of the G2 walk owner's G2. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_m.
Import ListNotations.
Open Scope Z_scope.

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

(* the sizes a model step leaves: (seg, kept) never shrink *)
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

(* ======================================= this lane's ======================================= *)
(* a refusal keeps the cursor inside seg *)
Lemma mf_cur_ok_refuse : forall mc cur l k, mf_cur_ok mc cur -> mf_cur_ok (m_refuse mc l k) cur.
Proof.
  intros mc [i|] l k H; [|exact I]. unfold mf_cur_ok in *.
  destruct (m_refuse_sizes mc l k) as [E _]. rewrite E. exact H.
Qed.
(* the kept list of a state on the way is no longer than the final model's *)
Lemma mf_kept_le_final : forall (mc : mconf) cur n ls fin, mf_cur_ok mc cur ->
  fst (m_lines (mc, cur) n ls) = fin -> (length (mc_kept mc) <= length (mc_kept fin))%nat.
Proof.
  intros mc cur n ls fin Hc E. destruct (m_lines_ok ls (mc, cur) n Hc) as [[_ G] _].
  rewrite E in G. exact G.
Qed.
(* mf_refuse_step's premise at a refusal that goes on to the next lines with the cursor cur' *)
Lemma mf_kept_le_refuse : forall (mc : mconf) l k cur' n ls fin, mf_cur_ok (m_refuse mc l k) cur' ->
  fst (m_lines (m_refuse mc l k, cur') n ls) = fin ->
  (length (mc_kept (m_refuse mc l k)) <= length (mc_kept fin))%nat.
Proof. intros mc l k cur' n ls fin Hc E. exact (mf_kept_le_final _ cur' n ls fin Hc E). Qed.
