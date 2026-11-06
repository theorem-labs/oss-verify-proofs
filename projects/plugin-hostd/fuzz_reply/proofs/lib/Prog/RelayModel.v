From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Definition LINE_LIMIT : nat := 6000.

Definition nozero (l : list Z) : Prop := Forall (fun b => b <> 0) l.

Record lstate := LS { ls_w : list Z; ls_k : bool }.

Definition step (st : lstate) (b : Z) : lstate * option (list Z) :=
  if Z.eqb b 0 then (LS [] false, if ls_k st then None else Some (ls_w st))
  else if ls_k st then (st, None)
  else if Nat.eqb (length (ls_w st)) LINE_LIMIT then (LS (ls_w st) true, None)
  else (LS (ls_w st ++ [b]) false, None).

Fixpoint feed_lines (st : lstate) (d : list Z) : lstate * list (list Z) :=
  match d with
  | [] => (st, [])
  | b :: d' =>
      let (st1, o) := step st b in
      let (st2, ls) := feed_lines st1 d' in
      (st2, match o with Some l => l :: ls | None => ls end)
  end.

Definition feed (st : lstate) (d : list Z) : lstate := fst (feed_lines st d).
Definition lines (st : lstate) (d : list Z) : list (list Z) := snd (feed_lines st d).

Lemma step_zero : forall st, step st 0 = (LS [] false, if ls_k st then None else Some (ls_w st)).
Proof. reflexivity. Qed.

Lemma step_nz_k : forall st b, b <> 0 -> ls_k st = true -> step st b = (st, None).
Proof. intros st b Hb Hk. unfold step. rewrite (proj2 (Z.eqb_neq b 0) Hb), Hk. reflexivity. Qed.

Lemma step_nz_full : forall st b, b <> 0 -> ls_k st = false -> length (ls_w st) = LINE_LIMIT ->
  step st b = (LS (ls_w st) true, None).
Proof.
  intros st b Hb Hk He. unfold step.
  rewrite (proj2 (Z.eqb_neq b 0) Hb), Hk, (proj2 (Nat.eqb_eq _ _) He). reflexivity.
Qed.

Lemma step_nz_add : forall st b, b <> 0 -> ls_k st = false -> length (ls_w st) <> LINE_LIMIT ->
  step st b = (LS (ls_w st ++ [b]) false, None).
Proof.
  intros st b Hb Hk He. unfold step.
  rewrite (proj2 (Z.eqb_neq b 0) Hb), Hk, (proj2 (Nat.eqb_neq _ _) He). reflexivity.
Qed.

Lemma feed_lines_cons : forall st b d,
  feed_lines st (b :: d) =
  (fst (feed_lines (fst (step st b)) d),
   match snd (step st b) with
   | Some l => l :: snd (feed_lines (fst (step st b)) d)
   | None => snd (feed_lines (fst (step st b)) d)
   end).
Proof.
  intros st b d. cbn [feed_lines].
  destruct (step st b) as [st1 o]. cbn [fst snd].
  destruct (feed_lines st1 d). reflexivity.
Qed.

Lemma feed_nil : forall st, feed st [] = st.
Proof. reflexivity. Qed.

Lemma lines_nil : forall st, lines st [] = [].
Proof. reflexivity. Qed.

Lemma feed_cons : forall st b d, feed st (b :: d) = feed (fst (step st b)) d.
Proof. intros. unfold feed at 1. rewrite feed_lines_cons. reflexivity. Qed.

Lemma lines_cons : forall st b d,
  lines st (b :: d) =
  match snd (step st b) with
  | Some l => l :: lines (fst (step st b)) d
  | None => lines (fst (step st b)) d
  end.
Proof.
  intros. unfold lines at 1. rewrite feed_lines_cons. cbn [snd].
  destruct (snd (step st b)); reflexivity.
Qed.

Lemma feed_lines_app : forall d1 d2 st,
  feed st (d1 ++ d2) = feed (feed st d1) d2 /\
  lines st (d1 ++ d2) = lines st d1 ++ lines (feed st d1) d2.
Proof.
  induction d1 as [|b d1 IH]; intros d2 st.
  - split; reflexivity.
  - cbn [app]. rewrite !feed_cons, !lines_cons.
    destruct (IH d2 (fst (step st b))) as [H1 H2].
    split; [exact H1|].
    rewrite H2. destruct (snd (step st b)); reflexivity.
Qed.

Lemma feed_app : forall st d1 d2, feed st (d1 ++ d2) = feed (feed st d1) d2.
Proof. intros. apply feed_lines_app. Qed.

Lemma lines_app : forall st d1 d2, lines st (d1 ++ d2) = lines st d1 ++ lines (feed st d1) d2.
Proof. intros. apply feed_lines_app. Qed.

Fixpoint scan (skip : bool) (acc : list Z) (d : list Z) : bool * list Z * list (list Z) :=
  match d with
  | [] => (skip, acc, [])
  | b :: d' =>
      if Z.eqb b 0 then
        let '(sk, r, ls) := scan false [] d' in
        (sk, r, if skip || Nat.ltb LINE_LIMIT (length acc) then ls else acc :: ls)
      else scan skip (acc ++ [b]) d'
  end.

Lemma scan_zero : forall skip acc d,
  scan skip acc (0 :: d) =
  let '(sk, r, ls) := scan false [] d in
  (sk, r, if skip || Nat.ltb LINE_LIMIT (length acc) then ls else acc :: ls).
Proof. reflexivity. Qed.

Lemma scan_nz : forall skip acc b d, b <> 0 -> scan skip acc (b :: d) = scan skip (acc ++ [b]) d.
Proof. intros skip acc b d Hb. cbn [scan]. rewrite (proj2 (Z.eqb_neq b 0) Hb). reflexivity. Qed.

Definition chunk (u : list Z) (skip : bool) (d : list Z) : list Z * bool * list (list Z) :=
  let '(sk, r, ls) := scan skip u d in
  if Nat.ltb LINE_LIMIT (length r) then ([], true, ls) else (r, sk, ls).

Definition J1 (u : list Z) (skip : bool) (st : lstate) : Prop :=
  skip = ls_k st /\ (skip = false -> u = ls_w st) /\ (length u <= LINE_LIMIT)%nat /\ nozero u.

Definition rel (skip : bool) (acc : list Z) (st : lstate) : Prop :=
  (skip = false /\ ls_k st = false /\ acc = ls_w st /\ (length acc <= LINE_LIMIT)%nat)
  \/ (skip = false /\ ls_k st = true /\ (LINE_LIMIT < length acc)%nat)
  \/ (skip = true /\ ls_k st = true).

Lemma rel_empty : rel false [] (LS [] false).
Proof. left. cbn. unfold LINE_LIMIT. repeat split; lia. Qed.

Lemma scan_ok : forall d skip acc st,
  rel skip acc st -> nozero acc ->
  let '(sk, r, ls) := scan skip acc d in
  ls = lines st d /\ rel sk r (feed st d) /\ nozero r.
Proof.
  induction d as [|b d IH]; intros skip acc st Hr Hz.
  - cbn [scan]. rewrite lines_nil, feed_nil. split; [reflexivity|split; assumption].
  - destruct (Z.eq_dec b 0) as [Hb|Hb].
    + subst b. rewrite scan_zero, feed_cons, lines_cons, step_zero. cbn [fst snd].
      pose proof (IH false [] (LS [] false) rel_empty (Forall_nil _)) as IH0.
      destruct (scan false [] d) as [[sk r] ls].
      destruct IH0 as (IH1 & IH2 & IH3).
      cbv beta iota.
      split; [|split; assumption].
      rewrite IH1.
      destruct Hr as [(Hs & Hk & Ha & Hl)|[(Hs & Hk & Hl)|(Hs & Hk)]]; subst skip; rewrite Hk.
      * subst acc. replace (Nat.ltb LINE_LIMIT (length (ls_w st))) with false; [reflexivity|].
        symmetry. apply Nat.ltb_ge. exact Hl.
      * replace (Nat.ltb LINE_LIMIT (length acc)) with true; [reflexivity|].
        symmetry. apply Nat.ltb_lt. exact Hl.
      * reflexivity.
    + rewrite (scan_nz skip acc b d Hb), feed_cons, lines_cons.
      assert (Hz' : nozero (acc ++ [b])) by (apply Forall_app; split; [exact Hz|constructor; auto]).
      destruct Hr as [(Hs & Hk & Ha & Hl)|[(Hs & Hk & Hl)|(Hs & Hk)]]; subst skip.
      * subst acc.
        destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He|He].
        -- rewrite (step_nz_full st b Hb Hk He). cbn [fst snd].
           apply IH; [|exact Hz'].
           right; left. cbn [ls_k]. rewrite length_app, He. cbn [length].
           split; [reflexivity|]. split; [reflexivity|]. unfold LINE_LIMIT. lia.
        -- rewrite (step_nz_add st b Hb Hk He). cbn [fst snd].
           apply IH; [|exact Hz'].
           left. cbn [ls_k ls_w]. rewrite length_app. cbn [length].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           unfold LINE_LIMIT in *. lia.
      * rewrite (step_nz_k st b Hb Hk). cbn [fst snd].
        apply IH; [|exact Hz'].
        right; left. rewrite length_app. cbn [length].
        split; [reflexivity|]. split; [exact Hk|]. lia.
      * rewrite (step_nz_k st b Hb Hk). cbn [fst snd].
        apply IH; [|exact Hz'].
        right; right. split; [reflexivity|exact Hk].
Qed.

Theorem chunk_ok : forall u skip st d,
  J1 u skip st ->
  let '(u', skip', ls) := chunk u skip d in
  ls = lines st d /\ J1 u' skip' (feed st d).
Proof.
  intros u skip st d (Hk & Hu & Hl & Hz).
  assert (Hr : rel skip u st).
  { destruct skip.
    - right; right. split; [reflexivity|symmetry; exact Hk].
    - left. split; [reflexivity|]. split; [symmetry; exact Hk|]. split; [apply Hu; reflexivity|exact Hl]. }
  pose proof (scan_ok d skip u st Hr Hz) as H.
  unfold chunk.
  destruct (scan skip u d) as [[sk r] ls].
  cbv beta iota in H.
  destruct H as (Hls & Hr' & Hz').
  destruct (Nat.ltb_spec LINE_LIMIT (length r)) as [Hlt|Hge]; cbv beta iota.
  - split; [exact Hls|].
    destruct Hr' as [(_ & _ & _ & Hle)|[(_ & Hk' & _)|(_ & Hk')]].
    + exfalso. lia.
    + unfold J1. rewrite Hk'. cbn [length]. unfold LINE_LIMIT.
      split; [reflexivity|]. split; [intro Hc; discriminate Hc|]. split; [lia|constructor].
    + unfold J1. rewrite Hk'. cbn [length]. unfold LINE_LIMIT.
      split; [reflexivity|]. split; [intro Hc; discriminate Hc|]. split; [lia|constructor].
  - split; [exact Hls|].
    destruct Hr' as [(Hs & Hk' & Ha & Hle)|[(Hs & Hk' & Hgt)|(Hs & Hk')]]; subst sk.
    + unfold J1. rewrite Hk'.
      split; [reflexivity|]. split; [intros _; exact Ha|]. split; [exact Hge|exact Hz'].
    + exfalso. lia.
    + unfold J1. rewrite Hk'.
      split; [reflexivity|]. split; [intro Hc; discriminate Hc|]. split; [exact Hge|exact Hz'].
Qed.

Fixpoint chunks (u : list Z) (skip : bool) (ds : list (list Z)) : list Z * bool * list (list Z) :=
  match ds with
  | [] => (u, skip, [])
  | d :: ds' =>
      let '(u1, s1, ls1) := chunk u skip d in
      let '(u2, s2, ls2) := chunks u1 s1 ds' in
      (u2, s2, ls1 ++ ls2)
  end.

Theorem chunks_ok : forall ds u skip st,
  J1 u skip st ->
  let '(u', skip', ls) := chunks u skip ds in
  ls = lines st (concat ds) /\ J1 u' skip' (feed st (concat ds)).
Proof.
  induction ds as [|d ds IH]; intros u skip st HJ.
  - cbn [chunks concat]. rewrite lines_nil, feed_nil. split; [reflexivity|exact HJ].
  - cbn [chunks concat].
    pose proof (chunk_ok u skip st d HJ) as H1.
    destruct (chunk u skip d) as [[u1 s1] ls1].
    cbv beta iota in H1.
    destruct H1 as [Hl1 HJ1].
    pose proof (IH u1 s1 (feed st d) HJ1) as H2.
    destruct (chunks u1 s1 ds) as [[u2 s2] ls2].
    cbv beta iota in H2.
    destruct H2 as [Hl2 HJ2].
    cbv beta iota.
    rewrite lines_app, feed_app, Hl1, Hl2. split; [reflexivity|exact HJ2].
Qed.

Definition K_GESTURE : list Z := [112; 97; 114; 97; 109; 95; 103; 101; 115; 116; 117; 114; 101].
Definition W_BEGIN : list Z := [98; 101; 103; 105; 110].
Definition W_END : list Z := [101; 110; 100].
Definition SPACE : Z := 32.

Fixpoint last_space_from (i : nat) (l : list Z) : option nat :=
  match l with
  | [] => None
  | b :: l' =>
      match last_space_from (S i) l' with
      | Some j => Some j
      | None => if Z.eqb b SPACE then Some i else None
      end
  end.

Inductive gkind := GBegin | GEnd.

Definition list_eqb (a b : list Z) : bool := if list_eq_dec Z.eq_dec a b then true else false.

Definition gesture (l : list Z) : option (gkind * list Z) :=
  if list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l) then
    match last_space_from 0 l with
    | Some j =>
        if Nat.ltb 13 j then
          let w := skipn (S j) l in
          if list_eqb w W_BEGIN then Some (GBegin, firstn j l)
          else if list_eqb w W_END then Some (GEnd, firstn j l)
          else None
        else None
    | None => None
    end
  else None.

Definition upd (G : list (list Z)) (l : list Z) : list (list Z) :=
  match gesture l with
  | Some (GBegin, x) => if existsb (list_eqb x) G then G else G ++ [x]
  | Some (GEnd, x) => filter (fun y => negb (list_eqb x y)) G
  | None => G
  end.

Definition upds (G : list (list Z)) (ls : list (list Z)) : list (list Z) := fold_left upd ls G.

Definition with_nul (ls : list (list Z)) : list Z := concat (map (fun l => l ++ [0]) ls).
