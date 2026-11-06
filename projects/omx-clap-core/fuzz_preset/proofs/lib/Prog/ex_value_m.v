From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ex_value_c.
Import ListNotations.
Open Scope Z_scope.

Definition run0 {A : Type} (c : M A) : option A := fst (fst (c [])).

Definition ex_cap (n cap : nat) : nat := if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

Definition ex_L (dn : nat) (o : bool) (n cap : nat) (acc : list (list Z * jv)) (y : list Z) : option (jv * list Z) :=
  run0 (jrl ex_sm (2 * length y + 2) dn o n cap acc y).

Definition ex_name (o : bool) (y : list Z) : option (list Z * list Z) :=
  if o then
    match skip y with
    | b :: z =>
      if b =? 34 then
        match run0 (jr_string z) with
        | Some (nm, r) => match skip r with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end
        | None => None
        end
      else None
    | [] => None
    end
  else Some ([], y).

Lemma run0_bind : forall A B (m : M A) (k : A -> M B), agrees m ->
  run0 (jbind m k) = match run0 m with Some a => run0 (k a) | None => None end.
Proof.
  intros A B m k H. unfold run0, jbind.
  destruct (m []) as [[r t] o] eqn:E.
  pose proof (agrees_nil A m H) as N. rewrite E in N. cbn [fst snd] in N.
  inversion N; subst; clear N.
  destruct r as [a|]; cbn [fst snd]; [|reflexivity].
  destruct (k a []) as [[r1 t1] o1]; reflexivity.
Qed.

Lemma run0_ret : forall A (a : A), run0 (jret a) = Some a.
Proof. reflexivity. Qed.

Lemma run0_alloc : forall A n (k : unit -> M A), run0 (jbind (jalloc n) k) = run0 (k tt).
Proof.
  intros A n k. unfold run0, jbind, jalloc, take. cbv beta iota zeta.
  destruct (k tt []) as [[r t] o]. reflexivity.
Qed.

Lemma run0_grow : forall o n cap, run0 (grow o n cap) = Some (ex_cap n cap).
Proof.
  intros o n cap. unfold grow, ex_cap.
  destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity.
Qed.

Lemma run0_jr_string : forall y, run0 (jr_string y) = decode y.
Proof.
  intros y. unfold jr_string.
  destruct (scan y) as [q|] eqn:Es.
  - destruct (decode y) as [sr|]; reflexivity.
  - destruct (decode y) as [[s r]|] eqn:Ed; [|reflexivity].
    destruct (decode_stop y s r Ed) as (q & Hq & _). congruence.
Qed.

Lemma run0_jr_name : forall o y, run0 (jr_name o y) = ex_name o y.
Proof.
  intros [|] y; [|reflexivity].
  unfold jr_name, ex_name. cbv beta iota.
  destruct (skip y) as [|b z]; cbv beta iota; [reflexivity|].
  destruct (b =? 34); cbv beta iota; [|reflexivity].
  rewrite run0_bind by apply agrees_jr_string.
  destruct (run0 (jr_string z)) as [[nm r]|]; cbv beta iota; [|reflexivity].
  destruct (skip r) as [|c r1]; cbv beta iota; [reflexivity|].
  destruct (c =? 58); reflexivity.
Qed.

Lemma ex_V_unfold : forall d x, ex_V d x = run0 (jrv ex_sm (S (2 * length x)) (Z.to_nat d) x).
Proof. reflexivity. Qed.

Lemma skip_nws : forall b y, ws b = false -> skip (b :: y) = b :: y.
Proof. intros b y H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma skip_ws : forall b y, ws b = true -> skip (b :: y) = skip y.
Proof. intros b y H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma ex_V_cons : forall d b y, ws b = false -> ex_V d (b :: y) = run0 (
  if b =? 123 then jr_cont (jrl ex_sm (2 * length (b :: y))) (Z.to_nat d) true (b :: y)
  else if b =? 91 then jr_cont (jrl ex_sm (2 * length (b :: y))) (Z.to_nat d) false (b :: y)
  else if b =? 34 then jbind (jr_string y) (fun '(s, r) => jret (JStr s, r))
  else if b =? 116 then lit w_true JTrue (b :: y)
  else if b =? 102 then lit w_false JFalse (b :: y)
  else if b =? 110 then lit w_null JNull (b :: y)
  else jr_number ex_sm (b :: y)).
Proof.
  intros d b y H. unfold ex_V, jr_value, run0. cbn [jrv].
  rewrite (skip_nws b y H). reflexivity.
Qed.

Lemma ex_V_brace : forall d b y, (b = 123 \/ b = 91) ->
  ex_V d (b :: y) = run0 (jr_cont (jrl ex_sm (2 * length (b :: y))) (Z.to_nat d) (b =? 123) (b :: y)).
Proof. intros d b y [-> | ->]; rewrite ex_V_cons by reflexivity; reflexivity. Qed.

Lemma ltb_maxd : forall d, 0 <= d -> Nat.ltb MAXD (S (Z.to_nat d)) = (32 <? d + 1).
Proof.
  intros d Hd. unfold MAXD.
  destruct (Nat.ltb 32%nat (S (Z.to_nat d))) eqn:E1; destruct (32 <? d + 1) eqn:E2; try reflexivity.
  - apply Nat.ltb_lt in E1. apply Z.ltb_ge in E2. lia.
  - apply Nat.ltb_ge in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma jrl_nil : forall f d o n cap acc, run0 (jrl ex_sm f d o n cap acc []) = None.
Proof.
  intros [|f] d o n cap acc; [reflexivity|]. cbn [jrl].
  rewrite run0_bind by apply agrees_grow. rewrite run0_grow. cbv beta iota.
  destruct o; [reflexivity|]. destruct f; reflexivity.
Qed.

Definition suf (r x : list Z) : Prop := exists k, r = skipn k x.

Lemma skipn_skipn_z : forall (x : list Z) a b, skipn a (skipn b x) = skipn (b + a) x.
Proof.
  induction x as [|c x IH]; intros a b; [rewrite !skipn_nil; reflexivity|].
  destruct b as [|b]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.

Lemma suf_refl : forall x, suf x x.
Proof. intros x. exists 0%nat. reflexivity. Qed.

Lemma suf_trans : forall a b c, suf a b -> suf b c -> suf a c.
Proof. intros a b c [k1 ->] [k2 ->]. exists (k2 + k1)%nat. apply skipn_skipn_z. Qed.

Lemma suf_cons : forall r b y, suf r y -> suf r (b :: y).
Proof. intros r b y [k ->]. exists (S k). reflexivity. Qed.

Lemma suf_skipn : forall k x, suf (skipn k x) x.
Proof. intros k x. exists k. reflexivity. Qed.

Lemma suf_tail : forall c r x, suf (c :: r) x -> suf r x.
Proof. intros c r x H. apply (suf_trans r (c :: r) x); [|exact H]. exists 1%nat. reflexivity. Qed.

Lemma suf_app : forall (a r : list Z), suf r (a ++ r).
Proof. intros a r. exists (length a). induction a as [|c a IH]; [reflexivity|exact IH]. Qed.

Lemma suf_skip : forall x, suf (skip x) x.
Proof.
  induction x as [|b x IH]; [apply suf_refl|]. cbn [skip].
  destruct (ws b); [apply suf_cons; exact IH|apply suf_refl].
Qed.

Lemma suf_len : forall r x, suf r x -> (length r <= length x)%nat.
Proof. intros r x [k ->]. rewrite length_skipn. lia. Qed.

Lemma ex_name_suf : forall o y nm y1, ex_name o y = Some (nm, y1) -> suf y1 y.
Proof.
  intros [|] y nm y1; unfold ex_name; cbv beta iota.
  - destruct (skip y) as [|b z] eqn:Ey; cbv beta iota; [intro H; discriminate H|].
    destruct (b =? 34); cbv beta iota; [|intro H; discriminate H].
    rewrite run0_jr_string.
    destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    destruct (c =? 58); cbv beta iota; [|intro H; discriminate H].
    intro H. injection H as _ <-.
    destruct (decode_stop z s r Ed) as (q & _ & Hr & _).
    apply (suf_trans _ r y).
    { apply (suf_tail c). rewrite <- Er. apply suf_skip. }
    apply (suf_trans r z y).
    { rewrite Hr. apply suf_skipn. }
    apply (suf_trans z (b :: z) y); [apply suf_cons, suf_refl|rewrite <- Ey; apply suf_skip].
  - intro H. injection H as _ <-. apply suf_refl.
Qed.

Lemma suf_cont : forall f d o b y v r,
  (forall d o n cap acc y v r, run0 (jrl ex_sm f d o n cap acc y) = Some (v, r) -> suf r y) ->
  run0 (jr_cont (jrl ex_sm f) d o (b :: y)) = Some (v, r) -> suf r (b :: y).
Proof.
  intros f d o b y v r IH. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota zeta; [intro H; discriminate H|].
  cbn [tl]. intro H. apply suf_cons. revert H.
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota.
  - intro H. pose proof (suf_skip y) as Sy. rewrite Ey in Sy.
    exact (suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
  - pose proof (suf_skip y) as Sy. rewrite Ey in Sy.
    destruct (c =? closer o); cbv beta iota; intro H.
    + rewrite run0_ret in H. injection H as _ <-. exact (suf_tail c _ y Sy).
    + exact (suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
Qed.

Lemma suf_lit : forall w u x v r, run0 (lit w u x) = Some (v, r) -> suf r x.
Proof.
  intros w u x v r. unfold lit.
  destruct (prefixb w x); intro H; [|discriminate H].
  rewrite run0_ret in H. injection H as _ <-. apply suf_skipn.
Qed.

Lemma suf_number : forall x v r, run0 (jr_number ex_sm x) = Some (v, r) -> suf r x.
Proof.
  intros x v r. unfold jr_number. cbv beta iota zeta.
  match goal with |- context [skipn ?j x] => set (J := j) end.
  destruct (skipn J x) as [|c z] eqn:Ez; cbv beta iota; [intro H; discriminate H|].
  pose proof (suf_skipn J x) as SJ. rewrite Ez in SJ.
  destruct (negb (digit c)); cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c =? 48) && ?m then _ else _] => destruct ((c =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  destruct (span numch z) as [a r0] eqn:Es; cbv beta iota zeta.
  rewrite run0_alloc.
  match goal with |- context [whole ex_sm ?t] => destruct (whole ex_sm t) end;
    cbv beta iota; intro H; [|discriminate H].
  rewrite run0_ret in H. injection H as _ <-.
  apply (suf_trans _ z x); [|exact (suf_tail c z x SJ)].
  rewrite (span_app _ _ _ _ Es). apply suf_app.
Qed.

Lemma suf_fuel : forall f,
  (forall d x v r, run0 (jrv ex_sm f d x) = Some (v, r) -> suf r x) /\
  (forall d o n cap acc y v r, run0 (jrl ex_sm f d o n cap acc y) = Some (v, r) -> suf r y).
Proof.
  induction f as [|f [IHv IHl]]; [split; intros; discriminate|].
  split.
  - intros d x v r. cbn [jrv].
    destruct (skip x) as [|b y] eqn:Ex; cbv beta iota; [intro H; discriminate H|].
    pose proof (suf_skip x) as Sx. rewrite Ex in Sx.
    intro H. apply (suf_trans r (b :: y) x); [|exact Sx]. revert H.
    destruct (b =? 123); cbv beta iota; [exact (suf_cont f d true b y v r IHl)|].
    destruct (b =? 91); cbv beta iota; [exact (suf_cont f d false b y v r IHl)|].
    destruct (b =? 34); cbv beta iota.
    + rewrite run0_bind by apply agrees_jr_string. rewrite run0_jr_string.
      destruct (decode y) as [[s r0]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
      intro H. rewrite run0_ret in H. injection H as _ <-.
      destruct (decode_stop y s r0 Ed) as (q & _ & Hr & _).
      apply suf_cons. rewrite Hr. apply suf_skipn.
    + destruct (b =? 116); cbv beta iota; [intro H; exact (suf_lit _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota; [intro H; exact (suf_lit _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota; [intro H; exact (suf_lit _ _ _ _ _ H)|].
      intro H. exact (suf_number _ _ _ H).
  - intros d o n cap acc y v r. cbn [jrl].
    rewrite run0_bind by apply agrees_grow. rewrite run0_grow. cbv beta iota.
    rewrite run0_bind by apply agrees_jr_name. rewrite run0_jr_name.
    destruct (ex_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|intro H; discriminate H].
    pose proof (ex_name_suf o y nm y1 En) as S1.
    rewrite run0_bind by apply (proj1 (agrees_fuel ex_sm f)).
    destruct (run0 (jrv ex_sm f d y1)) as [[u r0]|] eqn:Ev; cbv beta iota; [|intro H; discriminate H].
    pose proof (IHv d y1 u r0 Ev) as S2.
    destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    pose proof (suf_skip r0) as S3. rewrite Er in S3.
    assert (S4 : suf r1 y).
    { apply (suf_trans r1 r0 y); [exact (suf_tail c r1 r0 S3)|exact (suf_trans r0 y1 y S2 S1)]. }
    destruct (c =? 44); cbv beta iota.
    + intro H. exact (suf_trans _ _ _ (IHl _ _ _ _ _ _ _ _ H) S4).
    + destruct (c =? closer o); cbv beta iota; intro H; [|discriminate H].
      rewrite run0_ret in H. injection H as _ <-. exact S4.
Qed.

Lemma ex_V_len : forall d y u r, ex_V d y = Some (u, r) -> (length r < length y)%nat.
Proof.
  intros d y u r. unfold ex_V.
  destruct (jr_value ex_sm (Z.to_nat d) y []) as [[res tr] ok'] eqn:E. cbn [fst]. intro H. subst res.
  exact (jr_value_rest ex_sm _ _ _ _ _ _ _ E).
Qed.

Lemma ex_V_nil : forall d, ex_V d [] = None.
Proof. reflexivity. Qed.

Lemma ex_V_ws : forall d b y, ws b = true -> ex_V d (b :: y) = ex_V d y.
Proof.
  intros d b y H. unfold ex_V.
  rewrite <- (jr_value_fuel ex_sm (S (2 * length (b :: y))) (Z.to_nat d) y []) by (cbn [length]; lia).
  unfold jr_value. cbn [jrv]. rewrite (skip_ws b y H). reflexivity.
Qed.

Lemma ex_V_open : forall d b y, 0 <= d -> (b = 123 \/ b = 91) ->
  ex_V d (b :: y) =
    if 32 <? d + 1 then None
    else match skip y with
         | c :: r => if c =? closer (b =? 123) then Some (mk (b =? 123) [], r)
                     else ex_L (S (Z.to_nat d)) (b =? 123) 0 0 [] (c :: r)
         | [] => None
         end.
Proof.
  intros d b y Hd Hb. rewrite (ex_V_brace d b y Hb).
  set (o := b =? 123).
  unfold jr_cont. rewrite (ltb_maxd d Hd).
  destruct (32 <? d + 1); cbv beta iota zeta; [reflexivity|].
  cbn [tl].
  destruct (skip y) as [|c r] eqn:Ey; cbv beta iota.
  - apply jrl_nil.
  - pose proof (skip_len y) as Ly. rewrite Ey in Ly.
    destruct (c =? closer o); cbv beta iota; [reflexivity|].
    unfold ex_L, run0.
    rewrite (proj2 (fuel_mono ex_sm (2 * length (c :: r) + 2)) (S (Z.to_nat d)) o 0%nat 0%nat [] (c :: r)
      (2 * length (b :: y))%nat []) by (cbn [length] in *; lia).
    reflexivity.
Qed.

Lemma ex_V_str : forall d y,
  ex_V d (34 :: y) = match run0 (jr_string y) with Some (s, r) => Some (JStr s, r) | None => None end.
Proof.
  intros d y. rewrite ex_V_cons by reflexivity.
  transitivity (run0 (jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)))); [reflexivity|].
  rewrite run0_bind by apply agrees_jr_string.
  destruct (run0 (jr_string y)) as [[s r]|]; reflexivity.
Qed.

Lemma ex_V_true : forall d y,
  ex_V d (116 :: y) = if prefixb w_true (116 :: y) then Some (JTrue, skipn 4 (116 :: y)) else None.
Proof.
  intros d y. rewrite ex_V_cons by reflexivity.
  transitivity (run0 (lit w_true JTrue (116 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_true (116 :: y)); reflexivity.
Qed.

Lemma ex_V_false : forall d y,
  ex_V d (102 :: y) = if prefixb w_false (102 :: y) then Some (JFalse, skipn 5 (102 :: y)) else None.
Proof.
  intros d y. rewrite ex_V_cons by reflexivity.
  transitivity (run0 (lit w_false JFalse (102 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_false (102 :: y)); reflexivity.
Qed.

Lemma ex_V_null : forall d y,
  ex_V d (110 :: y) = if prefixb w_null (110 :: y) then Some (JNull, skipn 4 (110 :: y)) else None.
Proof.
  intros d y. rewrite ex_V_cons by reflexivity.
  transitivity (run0 (lit w_null JNull (110 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_null (110 :: y)); reflexivity.
Qed.

Lemma ex_V_num : forall d b y, ws b = false -> b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  ex_V d (b :: y) =
    let j := if b =? 45 then 1%nat else 0%nat in
    match skipn j (b :: y) with
    | [] => None
    | c :: z =>
      if negb (digit c) then None
      else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
      else let (a, r) := span numch z in
           let txt := firstn j (b :: y) ++ c :: a in
           if whole ex_sm txt then Some (JNum txt (snd (ex_sm txt)), r) else None
    end.
Proof.
  intros d b y Hw H1 H2 H3 H4 H5 H6.
  rewrite ex_V_cons by exact Hw.
  rewrite (proj2 (Z.eqb_neq b 123) H1), (proj2 (Z.eqb_neq b 91) H2), (proj2 (Z.eqb_neq b 34) H3),
    (proj2 (Z.eqb_neq b 116) H4), (proj2 (Z.eqb_neq b 102) H5), (proj2 (Z.eqb_neq b 110) H6).
  unfold jr_number. cbv beta iota zeta.
  destruct (skipn (if b =? 45 then 1%nat else 0%nat) (b :: y)) as [|c z]; cbv beta iota; [reflexivity|].
  destruct (negb (digit c)); cbv beta iota; [reflexivity|].
  match goal with |- context [if (c =? 48) && ?m then _ else _] => destruct ((c =? 48) && m) end;
    cbv beta iota; [reflexivity|].
  destruct (span numch z) as [a r]; cbv beta iota zeta.
  rewrite run0_alloc. cbv beta iota.
  match goal with |- context [whole ex_sm ?t] => destruct (whole ex_sm t) end; reflexivity.
Qed.

Lemma ex_span : forall (z : list Z) k, (k <= length z)%nat ->
  (forall i, (i < k)%nat -> numch (nth i z 0) = true) -> (k = length z \/ numch (nth k z 0) = false) ->
  span numch z = (firstn k z, skipn k z).
Proof.
  induction z as [|b z IH]; intros k Hk Hi Hs.
  - cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. reflexivity.
  - destruct k as [|k].
    + destruct Hs as [Hs|Hs]; [cbn [length] in Hs; lia|].
      cbn [nth] in Hs. cbn [span]. rewrite Hs. reflexivity.
    + pose proof (Hi 0%nat ltac:(lia)) as H0. cbn [nth] in H0. cbn [span]. rewrite H0.
      cbn [length] in Hk.
      rewrite (IH k ltac:(lia)).
      * reflexivity.
      * intros i Hik. exact (Hi (S i) ltac:(lia)).
      * destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right; exact Hs].
Qed.

Lemma ex_L_step : forall dn o n cap acc y,
  ex_L dn o n cap acc y =
    match ex_name o y with
    | None => None
    | Some (nm, y1) =>
      match ex_V (Z.of_nat dn) y1 with
      | None => None
      | Some (u, r) =>
        match skip r with
        | c :: r1 => if c =? 44 then ex_L dn o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
                     else if c =? closer o then Some (mk o (rev ((nm, u) :: acc)), r1) else None
        | [] => None
        end
      end
    end.
Proof.
  intros dn o n cap acc y.
  unfold ex_L at 1.
  replace (2 * length y + 2)%nat with (S (2 * length y + 1)) by lia.
  cbn [jrl].
  rewrite run0_bind by apply agrees_grow. rewrite run0_grow. cbv beta iota.
  rewrite run0_bind by apply agrees_jr_name. rewrite run0_jr_name.
  destruct (ex_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|reflexivity].
  pose proof (suf_len _ _ (ex_name_suf o y nm y1 En)) as L1.
  rewrite run0_bind by apply (proj1 (agrees_fuel ex_sm _)).
  assert (EV : run0 (jrv ex_sm (2 * length y + 1) dn y1) = ex_V (Z.of_nat dn) y1).
  { rewrite ex_V_unfold, Nat2Z.id. unfold run0.
    rewrite (jr_value_fuel ex_sm (2 * length y + 1) dn y1 []) by lia. reflexivity. }
  rewrite EV.
  destruct (ex_V (Z.of_nat dn) y1) as [[u r]|] eqn:Ev; cbv beta iota; [|reflexivity].
  pose proof (ex_V_len _ _ _ _ Ev) as L2.
  destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [reflexivity|].
  pose proof (skip_len r) as L3. rewrite Er in L3. cbn [length] in L3.
  destruct (c =? 44); cbv beta iota; [|destruct (c =? closer o); reflexivity].
  unfold ex_L, run0.
  rewrite (proj2 (fuel_mono ex_sm (2 * length r1 + 2)) dn o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
    (2 * length y + 1)%nat []) by lia.
  reflexivity.
Qed.

Lemma ex_V_rest : forall d y u r, ex_V d y = Some (u, r) -> (length r < length y)%nat /\ exists k, r = skipn k y.
Proof.
  intros d y u r H. split; [exact (ex_V_len d y u r H)|].
  rewrite ex_V_unfold in H. exact (proj1 (suf_fuel _) _ _ _ _ H).
Qed.

Lemma ex_string_rest : forall y s r, run0 (jr_string y) = Some (s, r) ->
  exists c, scan y = Some c /\ r = skipn (S c) y /\ (c < length y)%nat /\ (length s <= c)%nat /\
    (Forall (fun b => 0 <= b < 256) y -> Forall (fun b => 0 < b < 256) s).
Proof.
  intros y s r H. rewrite run0_jr_string in H.
  destruct (decode_stop y s r H) as (q & Hs & Hr & Hl & _ & _).
  exists q. pose proof (scan_quote y q Hs) as [Hq _].
  split; [exact Hs|]. split; [exact Hr|]. split; [exact Hq|]. split; [exact Hl|].
  intros Hb. exact (G1_4_bytes y s r Hb H).
Qed.

Lemma ex_exp : forall bits, fp_exp_field fmt_double (bits mod 2 ^ 64) = Z.land (Z.shiftr bits 52) 2047.
Proof.
  intros bits. unfold fp_exp_field.
  change (fp_mw fmt_double) with 52. change (Z.ones (fp_ew fmt_double)) with 2047.
  apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 11) as [H|H].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - change 2047 with (Z.ones 11). rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma ex_class : forall bits : Z,
  Z.land (fp_class fmt_double (bits mod 2 ^ 64)) 897 = 0 <-> finite bits = true.
Proof.
  intros bits. unfold fp_class. cbv zeta.
  change (Z.ones (fp_ew fmt_double)) with 2047.
  rewrite ex_exp. unfold finite.
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 2047);
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 0);
  destruct (fp_man_field fmt_double (bits mod 2 ^ 64) =? 0);
  destruct (fp_sign_bit fmt_double (bits mod 2 ^ 64));
  destruct (fp_is_snan fmt_double (bits mod 2 ^ 64));
  vm_compute; split; intro H; first [reflexivity | discriminate H].
Qed.

Lemma jv_eq_dec : forall a b : jv, {a = b} + {a <> b}.
Proof.
  fix F 1. intros a b.
  destruct a as [| | |t1 c1|s1|l1|m1]; destruct b as [| | |t2 c2|s2|l2|m2];
    try (left; reflexivity); try (right; discriminate).
  - destruct (list_eq_dec Z.eq_dec t1 t2) as [<-|N]; [|right; congruence].
    destruct (Z.eq_dec c1 c2) as [<-|N]; [left; reflexivity|right; congruence].
  - destruct (list_eq_dec Z.eq_dec s1 s2) as [<-|N]; [left; reflexivity|right; congruence].
  - revert l2. revert l1. fix G 1.
    intros [|x l1] [|y l2]; [left; reflexivity|right; discriminate|right; discriminate|].
    destruct (F x y) as [<-|N]; [|right; congruence].
    destruct (G l1 l2) as [E|N]; [left; congruence|right; congruence].
  - revert m2. revert m1. fix G 1.
    intros [|[n1 u1] m1] [|[n2 u2] m2]; [left; reflexivity|right; discriminate|right; discriminate|].
    destruct (list_eq_dec Z.eq_dec n1 n2) as [<-|N]; [|right; congruence].
    destruct (F u1 u2) as [<-|N]; [|right; congruence].
    destruct (G m1 m2) as [E|N]; [left; congruence|right; congruence].
Qed.

Lemma list_neq_split : forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b}) (d : A) (l1 l2 : list A),
  l1 <> l2 -> length l1 <> length l2 \/
  exists j, (j < length l1)%nat /\ (j < length l2)%nat /\ nth j l1 d <> nth j l2 d.
Proof.
  intros A dec d l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - exfalso. apply H. reflexivity.
  - left. cbn [length]. lia.
  - left. cbn [length]. lia.
  - destruct (dec x y) as [<-|Nxy].
    + assert (Hl : l1 <> l2) by congruence.
      destruct (IH l2 Hl) as [L|(j & J1 & J2 & J3)].
      * left. cbn [length]. lia.
      * right. exists (S j). cbn [length nth]. split; [lia|]. split; [lia|]. exact J3.
    + right. exists 0%nat. cbn [length nth]. split; [lia|]. split; [lia|]. exact Nxy.
Qed.

Lemma ex_arr_neq : forall ts us,
  JArr ts <> JArr us <->
  length ts <> length us \/
  exists j, (j < length ts)%nat /\ (j < length us)%nat /\ nth j ts JNull <> nth j us JNull.
Proof.
  intros ts us. split.
  - intros H. apply (list_neq_split jv jv_eq_dec JNull). congruence.
  - intros H E. injection E as E. subst us.
    destruct H as [L|(j & J1 & J2 & J3)]; [exact (L eq_refl)|exact (J3 eq_refl)].
Qed.

Lemma ex_obj_neq : forall ms ns,
  JObj ms <> JObj ns <->
  length ms <> length ns \/
  exists j, (j < length ms)%nat /\ (j < length ns)%nat /\
    (fst (nth j ms ([], JNull)) <> fst (nth j ns ([], JNull)) \/
     snd (nth j ms ([], JNull)) <> snd (nth j ns ([], JNull))).
Proof.
  intros ms ns.
  assert (dec : forall a b : list Z * jv, {a = b} + {a <> b}).
  { intros [n1 u1] [n2 u2].
    destruct (list_eq_dec Z.eq_dec n1 n2) as [<-|N]; [|right; congruence].
    destruct (jv_eq_dec u1 u2) as [<-|N]; [left; reflexivity|right; congruence]. }
  split.
  - intros H. assert (Hl : ms <> ns) by congruence.
    destruct (list_neq_split _ dec ([], JNull) ms ns Hl) as [L|(j & J1 & J2 & J3)]; [left; exact L|right].
    exists j. split; [exact J1|]. split; [exact J2|].
    revert J3. destruct (nth j ms ([], JNull)) as [a u], (nth j ns ([], JNull)) as [b w].
    cbn [fst snd]. intro J3.
    destruct (list_eq_dec Z.eq_dec a b) as [<-|N]; [right; congruence|left; exact N].
  - intros H E. injection E as E. subst ns.
    destruct H as [L|(j & J1 & J2 & [J3|J3])]; [exact (L eq_refl)|exact (J3 eq_refl)|exact (J3 eq_refl)].
Qed.

Definition smr_ok (z : Z) : Prop := Z.shiftr z 64 = 0.

Lemma smr_ok_iff : forall z, smr_ok z <-> 0 <= z < 2 ^ 64.
Proof.
  intro z. unfold smr_ok. rewrite Z.shiftr_div_pow2 by lia. split.
  - intro H. pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as E.
    pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) as B.
    rewrite H in E. set (r := z mod 2 ^ 64) in *. lia.
  - intro H. apply Z.div_small. exact H.
Qed.

Lemma smr_lor : forall a b, smr_ok a -> smr_ok b -> smr_ok (Z.lor a b).
Proof. unfold smr_ok. intros a b Ha Hb. rewrite Z.shiftr_lor, Ha, Hb. reflexivity. Qed.

Lemma smr_land : forall a b, smr_ok a -> smr_ok b -> smr_ok (Z.land a b).
Proof. unfold smr_ok. intros a b Ha Hb. rewrite Z.shiftr_land, Ha, Hb. reflexivity. Qed.

Lemma smr_lxor : forall a b, smr_ok a -> smr_ok b -> smr_ok (Z.lxor a b).
Proof. unfold smr_ok. intros a b Ha Hb. rewrite Z.shiftr_lxor, Ha, Hb. reflexivity. Qed.

Lemma smr_shr : forall x n, smr_ok x -> smr_ok n -> smr_ok (Z.shiftr x n).
Proof.
  intros x n Hx Hn. apply smr_ok_iff in Hn. unfold smr_ok in *.
  rewrite Z.shiftr_shiftr by lia. rewrite Z.add_comm. rewrite <- Z.shiftr_shiftr by lia.
  rewrite Hx. apply Z.shiftr_0_l.
Qed.

Lemma smr_wrap : forall x, smr_ok (SoftFloat.wrap64 x).
Proof. intro x. apply smr_ok_iff. apply SoftFloat.wrap64_range. Qed.

Lemma smr_if : forall (c : bool) a b, smr_ok a -> smr_ok b -> smr_ok (if c then a else b).
Proof. intros [|] a b Ha Hb; assumption. Qed.

Lemma smr_snd_if : forall (c : bool) (p q : Z * Z),
  smr_ok (snd p) -> smr_ok (snd q) -> smr_ok (snd (if c then p else q)).
Proof. intros [|] p q Hp Hq; assumption. Qed.

Lemma smr_snd_pair : forall x y : Z, smr_ok y -> smr_ok (snd (x, y)).
Proof. intros x y H. exact H. Qed.

Lemma smr_trunc : forall s r, smr_ok s -> smr_ok (SoftFloat.trunc_round s r).
Proof.
  intros s r Hs. unfold SoftFloat.trunc_round, SoftFloat.add64.
  destruct (negb _); [apply smr_wrap|].
  destruct (negb (negb _)); [apply smr_wrap|exact Hs].
Qed.

Ltac smr_go :=
  repeat match goal with
  | |- smr_ok (snd (if _ then _ else _)) => apply smr_snd_if
  | |- smr_ok (snd (_, _)) => apply smr_snd_pair
  | |- smr_ok (if _ then _ else _) => apply smr_if
  | |- smr_ok (Z.lor _ _) => apply smr_lor
  | |- smr_ok (Z.land _ _) => apply smr_land
  | |- smr_ok (Z.lxor _ _) => apply smr_lxor
  | |- smr_ok (Z.shiftr _ _) => apply smr_shr
  | |- smr_ok (SoftFloat.wrap64 _) => apply smr_wrap
  | |- smr_ok (SoftFloat.trunc_round _ _) => apply smr_trunc
  | |- smr_ok (Zpos _) => reflexivity
  | |- smr_ok Z0 => reflexivity
  | H : smr_ok ?z |- smr_ok ?z => exact H
  end.

Lemma smr_to_d : forall a, 0 <= SoftFloat.f128_to_d a < 2 ^ 64.
Proof.
  intro a. apply smr_ok_iff.
  cbv beta zeta delta [SoftFloat.f128_to_d SoftFloat.lo64 SoftFloat.hi64 SoftFloat.shl64
    SoftFloat.add64 SoftFloat.sub64 SoftFloat.eqz64 SoftFloat.nez64 SoftFloat.sext32
    SoftFloat.zext32 SoftFloat.sra63 SoftFloat.not64 SoftFloat.b2z SoftFloat.DQUIET
    SoftFloat.M32 SoftFloat.ONES64].
  match goal with |- smr_ok (match ?p with _ => _ end) =>
    assert (H : smr_ok (snd p)) by smr_go; revert H; destruct p as [e s] end.
  cbv beta iota delta [snd]. intro H. smr_go.
Qed.

Lemma ex_sm_range : forall txt, 0 <= snd (ex_sm txt) < 2 ^ 64.
Proof.
  intro txt. unfold ex_sm, strtod_c.strtod_model, FloatScan.scan_strtod. cbv zeta.
  destruct (FloatScan.floatscan _ _ _ _) as [[f y]|]; cbn [snd]; [apply smr_to_d|lia].
Qed.
