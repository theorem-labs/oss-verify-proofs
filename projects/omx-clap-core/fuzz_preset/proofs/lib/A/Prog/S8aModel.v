(* fuzz_preset, slice S8a EX-VALUE: the PURE model lemmas of the walk of ex_value (image A' asan #102, A' 0x832a4) against
   the text tex_value_specX (lib/A/PRH_FnEx.v). No machine state, no mkst, no memory: the grammar's reading prhex_V
   (PRH_FnEx.v:62-63, PjGrammar.jr_value over ReaderRes.jr_strtod), the reader loop ev_L (S8aIface.v:54-56), the
   differs bookkeeping ev_dl (S8aIface.v:82-86) and the whitespace mask EV_WSMASK (S8aIface.v:43).
   COPIED, NOT CITED: the model lemmas are preset's released plain lib/Prog/ex_value_m.v (run0, ex_cap, ex_name,
   ex_V_*, ex_L_step, suf_*, ex_V_rest, ex_string_rest, jv_eq_dec, list_neq_split, ex_arr_neq, ex_obj_neq) and
   lib/Prog/ex_value_b.v:30-43 (ev_ws_mask, ev_ws_big), restated here over prhex_V / ev_L / ev_run0 (the plain ex_sm
   and ReaderRes.jr_strtod are the same function of strtod_c.strtod_model). No plain or UBSan file is Required and no
   plain lemma is cited; the grammar facts used (agrees_*, fuel_mono, jr_value_fuel, jr_value_rest, skip_len,
   decode_stop, scan_quote, span_app) are lib/Spec/PjGrammar.v's.
   NUMERALS: 123 '{', 91 '[', 125 / 93 the closers, 34 the double quote, 44 ',', 58 ':', 116 't', 102 'f', 110 'n',
   45 '-', 48 '0', 32 the largest blank byte: WORD (byte values of the grammar). 6 / 5: WORD (PjTree.tag of an
   object / an array). 4 / 5 in skipn 4 / skipn 5: LENGTH (the words true / null, false). 8, 2 in ex_cap,
   2 * length y + 2,
   S (2 * length x): DERIVED (PjGrammar's grow and fuel). 33, 256, 64: LENGTH (the byte ranges enumerated, the
   shift-amount modulus of srl). 0 / 1: WORD (NULL, the differs flag). No ADDRESS literal. *)
From Stdlib Require Import ZArith List Lia Bool Arith Setoid.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
Import ListNotations.
Local Open Scope Z_scope.

(* ======== the reader's monad at the all-succeed oracle (plain ex_value_m.v:9-80) ======== *)

(* the capacity after item n (PjGrammar.grow's result) *)
Definition ex_cap (n cap : nat) : nat :=
  if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

(* an object member's name and the text after its ':' (an array item has the name []) *)
Definition ex_name (o : bool) (y : list Z) : option (list Z * list Z) :=
  if o then
    match skip y with
    | b :: z =>
      if b =? 34 then
        match ev_run0 (jr_string z) with
        | Some (nm, r) => match skip r with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end
        | None => None
        end
      else None
    | [] => None
    end
  else Some ([], y).

Lemma ex_name_arr : forall y, ex_name false y = Some ([], y).
Proof. reflexivity. Qed.

Lemma evm_run0_bind : forall A B (m : M A) (k : A -> M B), agrees m ->
  ev_run0 (jbind m k) = match ev_run0 m with Some a => ev_run0 (k a) | None => None end.
Proof.
  intros A B m k H. unfold ev_run0, jbind.
  destruct (m []) as [[r t] o] eqn:E.
  pose proof (agrees_nil A m H) as N. rewrite E in N. cbn [fst snd] in N.
  inversion N; subst; clear N.
  destruct r as [a|]; cbn [fst snd]; [|reflexivity].
  destruct (k a []) as [[r1 t1] o1]; reflexivity.
Qed.

Lemma evm_run0_ret : forall A (a : A), ev_run0 (jret a) = Some a.
Proof. reflexivity. Qed.

Lemma evm_run0_alloc : forall A n (k : unit -> M A), ev_run0 (jbind (jalloc n) k) = ev_run0 (k tt).
Proof.
  intros A n k. unfold ev_run0, jbind, jalloc, take. cbv beta iota zeta.
  destruct (k tt []) as [[r t] o]. reflexivity.
Qed.

Lemma evm_run0_grow : forall o n cap, ev_run0 (grow o n cap) = Some (ex_cap n cap).
Proof.
  intros o n cap. unfold grow, ex_cap.
  destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity.
Qed.

Lemma evm_run0_jr_string : forall y, ev_run0 (jr_string y) = decode y.
Proof.
  intros y. unfold jr_string.
  destruct (scan y) as [q|] eqn:Es.
  - destruct (decode y) as [sr|]; reflexivity.
  - destruct (decode y) as [[s r]|] eqn:Ed; [|reflexivity].
    destruct (decode_stop y s r Ed) as (q & Hq & _). congruence.
Qed.

Lemma evm_run0_jr_name : forall o y, ev_run0 (jr_name o y) = ex_name o y.
Proof.
  intros [|] y; [|reflexivity].
  unfold jr_name, ex_name. cbv beta iota.
  destruct (skip y) as [|b z]; cbv beta iota; [reflexivity|].
  destruct (b =? 34); cbv beta iota; [|reflexivity].
  rewrite evm_run0_bind by apply agrees_jr_string.
  destruct (ev_run0 (jr_string z)) as [[nm r]|]; cbv beta iota; [|reflexivity].
  destruct (skip r) as [|c r1]; cbv beta iota; [reflexivity|].
  destruct (c =? 58); reflexivity.
Qed.

Lemma prhex_V_unfold : forall d x,
  prhex_V d x = ev_run0 (jrv ReaderRes.jr_strtod (S (2 * length x)) (Z.to_nat d) x).
Proof. reflexivity. Qed.

Lemma evm_skip_nws : forall b y, ws b = false -> skip (b :: y) = b :: y.
Proof. intros b y H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma evm_skip_ws : forall b y, ws b = true -> skip (b :: y) = skip y.
Proof. intros b y H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma prhex_V_cons : forall d b y, ws b = false -> prhex_V d (b :: y) = ev_run0 (
  if b =? 123 then jr_cont (jrl ReaderRes.jr_strtod (2 * length (b :: y))) (Z.to_nat d) true (b :: y)
  else if b =? 91 then jr_cont (jrl ReaderRes.jr_strtod (2 * length (b :: y))) (Z.to_nat d) false (b :: y)
  else if b =? 34 then jbind (jr_string y) (fun '(s, r) => jret (JStr s, r))
  else if b =? 116 then lit w_true JTrue (b :: y)
  else if b =? 102 then lit w_false JFalse (b :: y)
  else if b =? 110 then lit w_null JNull (b :: y)
  else jr_number ReaderRes.jr_strtod (b :: y)).
Proof.
  intros d b y H. unfold prhex_V, jr_value, ev_run0. cbn [jrv].
  rewrite (evm_skip_nws b y H). reflexivity.
Qed.

Lemma prhex_V_brace : forall d b y, (b = 123 \/ b = 91) ->
  prhex_V d (b :: y) =
    ev_run0 (jr_cont (jrl ReaderRes.jr_strtod (2 * length (b :: y))) (Z.to_nat d) (b =? 123) (b :: y)).
Proof. intros d b y [-> | ->]; rewrite prhex_V_cons by reflexivity; reflexivity. Qed.

Lemma evm_ltb_maxd : forall d, 0 <= d -> Nat.ltb MAXD (S (Z.to_nat d)) = (32 <? d + 1).
Proof.
  intros d Hd. unfold MAXD.
  destruct (Nat.ltb 32%nat (S (Z.to_nat d))) eqn:E1; destruct (32 <? d + 1) eqn:E2; try reflexivity.
  - apply Nat.ltb_lt in E1. apply Z.ltb_ge in E2. lia.
  - apply Nat.ltb_ge in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma evm_jrl_nil : forall f d o n cap acc, ev_run0 (jrl ReaderRes.jr_strtod f d o n cap acc []) = None.
Proof.
  intros [|f] d o n cap acc; [reflexivity|]. cbn [jrl].
  rewrite evm_run0_bind by apply agrees_grow. rewrite evm_run0_grow. cbv beta iota.
  destruct o; [reflexivity|]. destruct f; reflexivity.
Qed.

Lemma ev_L_nil : forall dn o n cap acc, ev_L dn o n cap acc [] = None.
Proof. intros dn o n cap acc. apply evm_jrl_nil. Qed.

(* ======== suffixes (plain ex_value_m.v:110-238) ======== *)

Definition evm_suf (r x : list Z) : Prop := exists k, r = skipn k x.

Lemma evm_skipn_skipn_z : forall (x : list Z) a b, skipn a (skipn b x) = skipn (b + a) x.
Proof.
  induction x as [|c x IH]; intros a b; [rewrite !skipn_nil; reflexivity|].
  destruct b as [|b]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.

Lemma evm_suf_refl : forall x, evm_suf x x.
Proof. intros x. exists 0%nat. reflexivity. Qed.

Lemma evm_suf_trans : forall a b c, evm_suf a b -> evm_suf b c -> evm_suf a c.
Proof. intros a b c [k1 ->] [k2 ->]. exists (k2 + k1)%nat. apply evm_skipn_skipn_z. Qed.

Lemma evm_suf_cons : forall r b y, evm_suf r y -> evm_suf r (b :: y).
Proof. intros r b y [k ->]. exists (S k). reflexivity. Qed.

Lemma evm_suf_skipn : forall k x, evm_suf (skipn k x) x.
Proof. intros k x. exists k. reflexivity. Qed.

Lemma evm_suf_tail : forall c r x, evm_suf (c :: r) x -> evm_suf r x.
Proof.
  intros c r x H. apply (evm_suf_trans r (c :: r) x); [|exact H]. exists 1%nat. reflexivity.
Qed.

Lemma evm_suf_app : forall (a r : list Z), evm_suf r (a ++ r).
Proof. intros a r. exists (length a). induction a as [|c a IH]; [reflexivity|exact IH]. Qed.

Lemma evm_suf_skip : forall x, evm_suf (skip x) x.
Proof.
  induction x as [|b x IH]; [apply evm_suf_refl|]. cbn [skip].
  destruct (ws b); [apply evm_suf_cons; exact IH|apply evm_suf_refl].
Qed.

Lemma evm_suf_len : forall r x, evm_suf r x -> (length r <= length x)%nat.
Proof. intros r x [k ->]. rewrite length_skipn. lia. Qed.

Lemma ex_name_suf : forall o y nm y1, ex_name o y = Some (nm, y1) -> evm_suf y1 y.
Proof.
  intros [|] y nm y1; unfold ex_name; cbv beta iota.
  - destruct (skip y) as [|b z] eqn:Ey; cbv beta iota; [intro H; discriminate H|].
    destruct (b =? 34); cbv beta iota; [|intro H; discriminate H].
    rewrite evm_run0_jr_string.
    destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    destruct (c =? 58); cbv beta iota; [|intro H; discriminate H].
    intro H. injection H as _ <-.
    destruct (decode_stop z s r Ed) as (q & _ & Hr & _).
    apply (evm_suf_trans _ r y).
    { apply (evm_suf_tail c). rewrite <- Er. apply evm_suf_skip. }
    apply (evm_suf_trans r z y).
    { rewrite Hr. apply evm_suf_skipn. }
    apply (evm_suf_trans z (b :: z) y); [apply evm_suf_cons, evm_suf_refl|rewrite <- Ey; apply evm_suf_skip].
  - intro H. injection H as _ <-. apply evm_suf_refl.
Qed.

Lemma evm_suf_cont : forall f d o b y v r,
  (forall d o n cap acc y v r, ev_run0 (jrl ReaderRes.jr_strtod f d o n cap acc y) = Some (v, r) -> evm_suf r y) ->
  ev_run0 (jr_cont (jrl ReaderRes.jr_strtod f) d o (b :: y)) = Some (v, r) -> evm_suf r (b :: y).
Proof.
  intros f d o b y v r IH. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota zeta; [intro H; discriminate H|].
  cbn [tl]. intro H. apply evm_suf_cons. revert H.
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota.
  - intro H. pose proof (evm_suf_skip y) as Sy. rewrite Ey in Sy.
    exact (evm_suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
  - pose proof (evm_suf_skip y) as Sy. rewrite Ey in Sy.
    destruct (c =? closer o); cbv beta iota; intro H.
    + rewrite evm_run0_ret in H. injection H as _ <-. exact (evm_suf_tail c _ y Sy).
    + exact (evm_suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
Qed.

Lemma evm_suf_lit : forall w u x v r, ev_run0 (lit w u x) = Some (v, r) -> evm_suf r x.
Proof.
  intros w u x v r. unfold lit.
  destruct (prefixb w x); intro H; [|discriminate H].
  rewrite evm_run0_ret in H. injection H as _ <-. apply evm_suf_skipn.
Qed.

Lemma evm_suf_number : forall x v r, ev_run0 (jr_number ReaderRes.jr_strtod x) = Some (v, r) -> evm_suf r x.
Proof.
  intros x v r. unfold jr_number. cbv beta iota zeta.
  match goal with |- context [skipn ?j x] => set (J := j) end.
  destruct (skipn J x) as [|c z] eqn:Ez; cbv beta iota; [intro H; discriminate H|].
  pose proof (evm_suf_skipn J x) as SJ. rewrite Ez in SJ.
  destruct (negb (digit c)); cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c =? 48) && ?m then _ else _] => destruct ((c =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  destruct (span numch z) as [a r0] eqn:Es; cbv beta iota zeta.
  rewrite evm_run0_alloc.
  match goal with |- context [whole ReaderRes.jr_strtod ?t] => destruct (whole ReaderRes.jr_strtod t) end;
    cbv beta iota; intro H; [|discriminate H].
  rewrite evm_run0_ret in H. injection H as _ <-.
  apply (evm_suf_trans _ z x); [|exact (evm_suf_tail c z x SJ)].
  rewrite (span_app _ _ _ _ Es). apply evm_suf_app.
Qed.

Lemma evm_suf_fuel : forall f,
  (forall d x v r, ev_run0 (jrv ReaderRes.jr_strtod f d x) = Some (v, r) -> evm_suf r x) /\
  (forall d o n cap acc y v r, ev_run0 (jrl ReaderRes.jr_strtod f d o n cap acc y) = Some (v, r) -> evm_suf r y).
Proof.
  induction f as [|f [IHv IHl]]; [split; intros; discriminate|].
  split.
  - intros d x v r. cbn [jrv].
    destruct (skip x) as [|b y] eqn:Ex; cbv beta iota; [intro H; discriminate H|].
    pose proof (evm_suf_skip x) as Sx. rewrite Ex in Sx.
    intro H. apply (evm_suf_trans r (b :: y) x); [|exact Sx]. revert H.
    destruct (b =? 123); cbv beta iota; [exact (evm_suf_cont f d true b y v r IHl)|].
    destruct (b =? 91); cbv beta iota; [exact (evm_suf_cont f d false b y v r IHl)|].
    destruct (b =? 34); cbv beta iota.
    + rewrite evm_run0_bind by apply agrees_jr_string. rewrite evm_run0_jr_string.
      destruct (decode y) as [[s r0]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
      intro H. rewrite evm_run0_ret in H. injection H as _ <-.
      destruct (decode_stop y s r0 Ed) as (q & _ & Hr & _).
      apply evm_suf_cons. rewrite Hr. apply evm_suf_skipn.
    + destruct (b =? 116); cbv beta iota; [intro H; exact (evm_suf_lit _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota; [intro H; exact (evm_suf_lit _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota; [intro H; exact (evm_suf_lit _ _ _ _ _ H)|].
      intro H. exact (evm_suf_number _ _ _ H).
  - intros d o n cap acc y v r. cbn [jrl].
    rewrite evm_run0_bind by apply agrees_grow. rewrite evm_run0_grow. cbv beta iota.
    rewrite evm_run0_bind by apply agrees_jr_name. rewrite evm_run0_jr_name.
    destruct (ex_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|intro H; discriminate H].
    pose proof (ex_name_suf o y nm y1 En) as S1.
    rewrite evm_run0_bind by apply (proj1 (agrees_fuel ReaderRes.jr_strtod f)).
    destruct (ev_run0 (jrv ReaderRes.jr_strtod f d y1)) as [[u r0]|] eqn:Ev; cbv beta iota;
      [|intro H; discriminate H].
    pose proof (IHv d y1 u r0 Ev) as S2.
    destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    pose proof (evm_suf_skip r0) as S3. rewrite Er in S3.
    assert (S4 : evm_suf r1 y).
    { apply (evm_suf_trans r1 r0 y); [exact (evm_suf_tail c r1 r0 S3)|exact (evm_suf_trans r0 y1 y S2 S1)]. }
    destruct (c =? 44); cbv beta iota.
    + intro H. exact (evm_suf_trans _ _ _ (IHl _ _ _ _ _ _ _ _ H) S4).
    + destruct (c =? closer o); cbv beta iota; intro H; [|discriminate H].
      rewrite evm_run0_ret in H. injection H as _ <-. exact S4.
Qed.

(* ======== ITEM 1: prhex_V at each first byte ======== *)

Lemma prhex_V_len : forall d y u r, prhex_V d y = Some (u, r) -> (length r < length y)%nat.
Proof.
  intros d y u r. unfold prhex_V.
  destruct (jr_value ReaderRes.jr_strtod (Z.to_nat d) y []) as [[res tr] ok'] eqn:E. cbn [fst]. intro H. subst res.
  exact (jr_value_rest ReaderRes.jr_strtod _ _ _ _ _ _ _ E).
Qed.

Lemma prhex_V_nil : forall d, prhex_V d [] = None.
Proof. reflexivity. Qed.

Lemma prhex_V_ws : forall d b y, ws b = true -> prhex_V d (b :: y) = prhex_V d y.
Proof.
  intros d b y H. unfold prhex_V.
  rewrite <- (jr_value_fuel ReaderRes.jr_strtod (S (2 * length (b :: y))) (Z.to_nat d) y [])
    by (cbn [length]; lia).
  unfold jr_value. cbn [jrv]. rewrite (evm_skip_ws b y H). reflexivity.
Qed.

Lemma prhex_V_skip : forall d xs, prhex_V d xs = prhex_V d (skip xs).
Proof.
  intros d xs. induction xs as [|b y IH]; [reflexivity|]. cbn [skip].
  destruct (ws b) eqn:Hb; [rewrite (prhex_V_ws d b y Hb); exact IH|reflexivity].
Qed.

Lemma prhex_V_str : forall d y,
  prhex_V d (34 :: y) =
    match fst (fst (jr_string y [])) with Some (s, r) => Some (JStr s, r) | None => None end.
Proof.
  intros d y. rewrite prhex_V_cons by reflexivity.
  transitivity (ev_run0 (jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)))); [reflexivity|].
  rewrite evm_run0_bind by apply agrees_jr_string.
  unfold ev_run0. destruct (fst (fst (jr_string y []))) as [[s r]|]; reflexivity.
Qed.

Lemma prhex_V_true : forall d y,
  prhex_V d (116 :: y) = if prefixb w_true (116 :: y) then Some (JTrue, skipn 4 (116 :: y)) else None.
Proof.
  intros d y. rewrite prhex_V_cons by reflexivity.
  transitivity (ev_run0 (lit w_true JTrue (116 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_true (116 :: y)); reflexivity.
Qed.

Lemma prhex_V_false : forall d y,
  prhex_V d (102 :: y) = if prefixb w_false (102 :: y) then Some (JFalse, skipn 5 (102 :: y)) else None.
Proof.
  intros d y. rewrite prhex_V_cons by reflexivity.
  transitivity (ev_run0 (lit w_false JFalse (102 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_false (102 :: y)); reflexivity.
Qed.

Lemma prhex_V_null : forall d y,
  prhex_V d (110 :: y) = if prefixb w_null (110 :: y) then Some (JNull, skipn 4 (110 :: y)) else None.
Proof.
  intros d y. rewrite prhex_V_cons by reflexivity.
  transitivity (ev_run0 (lit w_null JNull (110 :: y))); [reflexivity|].
  unfold lit. destruct (prefixb w_null (110 :: y)); reflexivity.
Qed.

Lemma prhex_V_num : forall d b y,
  ws b = false -> b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  prhex_V d (b :: y) =
    let j := if b =? 45 then 1%nat else 0%nat in
    match skipn j (b :: y) with
    | [] => None
    | c :: z =>
      if negb (digit c) then None
      else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
      else let (a, r) := span numch z in
           let txt := firstn j (b :: y) ++ c :: a in
           if whole ReaderRes.jr_strtod txt then Some (JNum txt (snd (ReaderRes.jr_strtod txt)), r) else None
    end.
Proof.
  intros d b y Hw H1 H2 H3 H4 H5 H6.
  rewrite prhex_V_cons by exact Hw.
  rewrite (proj2 (Z.eqb_neq b 123) H1), (proj2 (Z.eqb_neq b 91) H2), (proj2 (Z.eqb_neq b 34) H3),
    (proj2 (Z.eqb_neq b 116) H4), (proj2 (Z.eqb_neq b 102) H5), (proj2 (Z.eqb_neq b 110) H6).
  unfold jr_number. cbv beta iota zeta.
  destruct (skipn (if b =? 45 then 1%nat else 0%nat) (b :: y)) as [|c z]; cbv beta iota; [reflexivity|].
  destruct (negb (digit c)); cbv beta iota; [reflexivity|].
  match goal with |- context [if (c =? 48) && ?m then _ else _] => destruct ((c =? 48) && m) end;
    cbv beta iota; [reflexivity|].
  destruct (span numch z) as [a r]; cbv beta iota zeta.
  rewrite evm_run0_alloc. cbv beta iota.
  match goal with |- context [whole ReaderRes.jr_strtod ?t] => destruct (whole ReaderRes.jr_strtod t) end;
    reflexivity.
Qed.

Lemma prhex_V_rest : forall d y u r, prhex_V d y = Some (u, r) ->
  (length r < length y)%nat /\ exists k, r = skipn k y.
Proof.
  intros d y u r H. split; [exact (prhex_V_len d y u r H)|].
  rewrite prhex_V_unfold in H. exact (proj1 (evm_suf_fuel _) _ _ _ _ H).
Qed.

(* the dispatch's forms (pieces 2-4): the first non-blank byte of xs decides *)
Lemma ev_V_blank : forall d xs, skip xs = [] -> prhex_V d xs = None.
Proof. intros d xs Hs. rewrite prhex_V_skip, Hs. reflexivity. Qed.

Lemma ev_V_str : forall d xs y, skip xs = 34 :: y ->
  prhex_V d xs = match fst (fst (jr_string y [])) with None => None | Some (s, r) => Some (JStr s, r) end.
Proof. intros d xs y Hs. rewrite prhex_V_skip, Hs. exact (prhex_V_str d y). Qed.

Lemma ev_V_word : forall d xs y b wl v, skip xs = b :: y ->
  ((b = 116 /\ wl = w_true /\ v = JTrue) \/ (b = 102 /\ wl = w_false /\ v = JFalse) \/
   (b = 110 /\ wl = w_null /\ v = JNull)) ->
  prhex_V d xs = (if prefixb wl (b :: y) then Some (v, skipn (length wl) (b :: y)) else None).
Proof.
  intros d xs y b wl v Hs Hw. rewrite prhex_V_skip, Hs.
  destruct Hw as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
    [exact (prhex_V_true d y)|exact (prhex_V_false d y)|exact (prhex_V_null d y)].
Qed.

Lemma ev_prefixb_firstn : forall wl l, prefixb wl l = true <-> firstn (length wl) l = wl.
Proof.
  induction wl as [|a w IH]; intros [|b l]; cbn [prefixb length firstn].
  - split; intros; reflexivity.
  - split; intros; reflexivity.
  - split; intro H; discriminate H.
  - rewrite andb_true_iff, Z.eqb_eq, IH. split.
    + intros [-> E]. rewrite E. reflexivity.
    + intros E. injection E as E1 E2. split; [symmetry; exact E1|exact E2].
Qed.

(* the string reader's rest (plain ex_string_rest, in tex_string_specX's form) *)
Lemma ex_string_rest : forall y s r, fst (fst (jr_string y [])) = Some (s, r) ->
  exists c, scan y = Some c /\ r = skipn (S c) y /\ (c < length y)%nat /\ (length s <= c)%nat /\
    (Forall (fun b => 0 <= b < 256) y -> Forall (fun b => 0 < b < 256) s).
Proof.
  intros y s r H. change (ev_run0 (jr_string y) = Some (s, r)) in H. rewrite evm_run0_jr_string in H.
  destruct (decode_stop y s r H) as (q & Hs & Hr & Hl & _ & _).
  exists q. pose proof (scan_quote y q Hs) as [Hq _].
  split; [exact Hs|]. split; [exact Hr|]. split; [exact Hq|]. split; [exact Hl|].
  intros Hb. exact (G1_4_bytes y s r Hb H).
Qed.

(* ======== ITEM 2: a container's opener ======== *)

Lemma prhex_V_open : forall d b y, 0 <= d -> (b = 123 \/ b = 91) ->
  prhex_V d (b :: y) =
    if 32 <? d + 1 then None
    else match skip y with
         | c :: r => if c =? closer (b =? 123) then Some (mk (b =? 123) [], r)
                     else ev_L (S (Z.to_nat d)) (b =? 123) 0 0 [] (skip y)
         | [] => None
         end.
Proof.
  intros d b y Hd Hb. rewrite (prhex_V_brace d b y Hb).
  set (o := b =? 123).
  unfold jr_cont. rewrite (evm_ltb_maxd d Hd).
  destruct (32 <? d + 1); cbv beta iota zeta; [reflexivity|].
  cbn [tl].
  destruct (skip y) as [|c r] eqn:Ey; cbv beta iota.
  - apply evm_jrl_nil.
  - pose proof (skip_len y) as Ly. rewrite Ey in Ly.
    destruct (c =? closer o); cbv beta iota; [reflexivity|].
    unfold ev_L, ev_run0.
    rewrite (proj2 (fuel_mono ReaderRes.jr_strtod (2 * length (c :: r) + 2)) (S (Z.to_nat d)) o 0%nat 0%nat []
      (c :: r) (2 * length (b :: y))%nat []) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* ======== ITEM 3: one step of the reader loop ======== *)

Lemma ev_L_step : forall dn o n cap acc y,
  ev_L dn o n cap acc y =
    match ex_name o y with
    | None => None
    | Some (nm, y1) =>
      match prhex_V (Z.of_nat dn) y1 with
      | None => None
      | Some (u, r) =>
        match skip r with
        | c :: r1 => if c =? 44 then ev_L dn o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
                     else if c =? closer o then Some (mk o (rev ((nm, u) :: acc)), r1) else None
        | [] => None
        end
      end
    end.
Proof.
  intros dn o n cap acc y.
  unfold ev_L at 1.
  replace (2 * length y + 2)%nat with (S (2 * length y + 1)) by lia.
  cbn [jrl].
  rewrite evm_run0_bind by apply agrees_grow. rewrite evm_run0_grow. cbv beta iota.
  rewrite evm_run0_bind by apply agrees_jr_name. rewrite evm_run0_jr_name.
  destruct (ex_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|reflexivity].
  pose proof (evm_suf_len _ _ (ex_name_suf o y nm y1 En)) as L1.
  rewrite evm_run0_bind by apply (proj1 (agrees_fuel ReaderRes.jr_strtod _)).
  assert (EV : ev_run0 (jrv ReaderRes.jr_strtod (2 * length y + 1) dn y1) = prhex_V (Z.of_nat dn) y1).
  { rewrite prhex_V_unfold, Nat2Z.id. unfold ev_run0.
    rewrite (jr_value_fuel ReaderRes.jr_strtod (2 * length y + 1) dn y1 []) by lia. reflexivity. }
  rewrite EV.
  destruct (prhex_V (Z.of_nat dn) y1) as [[u r]|] eqn:Ev; cbv beta iota; [|reflexivity].
  pose proof (prhex_V_len _ _ _ _ Ev) as L2.
  destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [reflexivity|].
  pose proof (skip_len r) as L3. rewrite Er in L3. cbn [length] in L3.
  destruct (c =? 44); cbv beta iota; [|destruct (c =? closer o); reflexivity].
  unfold ev_L, ev_run0.
  rewrite (proj2 (fuel_mono ReaderRes.jr_strtod (2 * length r1 + 2)) dn o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
    (2 * length y + 1)%nat []) by lia.
  reflexivity.
Qed.

(* the same at the nesting S8aIface's P_STEP names (ev_L (S (Z.to_nat dep)) ...): the item is read at dep + 1 *)
Lemma ev_L_step_d : forall dep o n cap acc y, 0 <= dep ->
  ev_L (S (Z.to_nat dep)) o n cap acc y =
    match ex_name o y with
    | None => None
    | Some (nm, y1) =>
      match prhex_V (dep + 1) y1 with
      | None => None
      | Some (u, r) =>
        match skip r with
        | c :: r1 => if c =? 44 then ev_L (S (Z.to_nat dep)) o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
                     else if c =? closer o then Some (mk o (rev ((nm, u) :: acc)), r1) else None
        | [] => None
        end
      end
    end.
Proof.
  intros dep o n cap acc y Hd. rewrite ev_L_step.
  replace (Z.of_nat (S (Z.to_nat dep))) with (dep + 1) by lia. reflexivity.
Qed.

(* ======== ITEM 5: the whitespace mask (plain ex_value_b.v:30-43, over Z) ======== *)

Lemma evm_z_all : forall (P : Z -> bool) (n : nat) (m : Z), Z.of_nat n = m ->
  forallb P (map Z.of_nat (seq 0 n)) = true -> forall b, 0 <= b < m -> P b = true.
Proof.
  intros P n m Hm H b Hb. subst m. rewrite forallb_forall in H. rewrite <- (Z2Nat.id b) by lia. apply H.
  apply in_map. apply in_seq. lia.
Qed.

Lemma ev_ws_bit : forall b, 0 <= b < 256 -> ((b <= 32 /\ Z.testbit EV_WSMASK b = true) <-> ws b = true).
Proof.
  intros b Hb.
  pose proof (evm_z_all (fun z => Bool.eqb ((z <=? 32) && Z.testbit EV_WSMASK z) (ws z)) 256 256 eq_refl
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  cbv beta in H. apply Bool.eqb_prop in H. rewrite <- H. rewrite andb_true_iff, Z.leb_le. reflexivity.
Qed.

Lemma ev_ws_mask : forall b, 0 <= b <= 32 ->
  (Z.land (Z.shiftr EV_WSMASK (b mod 64)) 1 =? 0) = negb (ws b).
Proof.
  intros b Hb.
  pose proof (evm_z_all (fun z => Bool.eqb (Z.land (Z.shiftr EV_WSMASK (z mod 64)) 1 =? 0) (negb (ws z))) 33 33
    eq_refl ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  cbv beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma ev_ws_mask1 : forall b, 0 <= b <= 32 -> (Z.land (Z.shiftr EV_WSMASK b) 1 = 1 <-> ws b = true).
Proof.
  intros b Hb.
  pose proof (evm_z_all (fun z => Bool.eqb (Z.land (Z.shiftr EV_WSMASK z) 1 =? 1) (ws z)) 33 33 eq_refl
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  cbv beta in H. apply Bool.eqb_prop in H. rewrite <- H. symmetry. apply Z.eqb_eq.
Qed.

Lemma ev_ws_mask0 : forall b, 0 <= b <= 32 -> (Z.land (Z.shiftr EV_WSMASK b) 1 = 0 <-> ws b = false).
Proof.
  intros b Hb.
  pose proof (evm_z_all (fun z => Bool.eqb (Z.land (Z.shiftr EV_WSMASK z) 1 =? 0) (negb (ws z))) 33 33 eq_refl
    ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
  cbv beta in H. apply Bool.eqb_prop in H. rewrite <- Bool.negb_true_iff, <- H. symmetry. apply Z.eqb_eq.
Qed.

Lemma ev_ws_big : forall b, 32 < b -> ws b = false.
Proof.
  intros b Hb. unfold ws. repeat match goal with |- context [Z.eqb ?a ?c] => destruct (Z.eqb_spec a c) end;
  cbn [orb]; first [reflexivity | lia].
Qed.

(* ======== tree inequality (plain ex_value_m.v:450-520) ======== *)

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

(* ======== ITEM 4: the differs bookkeeping over S8aIface.ev_dl ======== *)

(* v's tree has another type than the container *)
Lemma ev_tv_false : forall v o t,
  ev_tv v o t = false <-> v <> 0 /\ tag t <> (if o then 6 else 5).
Proof. intros v o t. unfold ev_tv. rewrite orb_false_iff, !Z.eqb_neq. reflexivity. Qed.

(* the node the loop compares with is not NULL *)
Lemma ev_v'_nz : forall v o t,
  ev_v' v o t <> 0 <-> v <> 0 /\ tag t = (if o then 6 else 5).
Proof.
  intros v o t. unfold ev_v', ev_tv.
  destruct (Z.eqb_spec v 0) as [Hv|Hv]; destruct (Z.eqb_spec (tag t) (if o then 6 else 5)) as [Ht|Ht];
    cbn [orb].
  - split; [intro N; exfalso; exact (N Hv)|intros [N _]; exact N].
  - split; [intro N; exfalso; exact (N Hv)|intros [N _]; exact N].
  - split; [intro N; split; [exact N|exact Ht]|intros [N _]; exact N].
  - split; [intro N; exfalso; apply N; reflexivity|intros [_ E]; exfalso; exact (Ht E)].
Qed.

(* propositional glue for the differs chains (no tauto: these contexts are large) *)
Lemma evm_or_false : forall A B C F : Prop, ~ F -> (A \/ (B /\ (C \/ F)) <-> A \/ (B /\ C)).
Proof.
  intros A B C F NF. split.
  - intros [a|[b [c|f]]]; [left; exact a|right; split; [exact b|exact c]|contradiction].
  - intros [a|[b c]]; [left; exact a|right; split; [exact b|left; exact c]].
Qed.

Lemma evm_chain : forall dl dl1 dl2 dl3 (P1 P2 P3 : Prop),
  (dl1 = 1 <-> dl = 1 \/ P1) -> (dl2 = 1 <-> dl1 = 1 \/ P2) -> (dl3 = 1 <-> dl2 = 1 \/ P3) ->
  (dl3 = 1 <-> dl = 1 \/ (P1 \/ (P2 \/ P3))).
Proof.
  intros dl dl1 dl2 dl3 P1 P2 P3 H1 H2 H3. split.
  - intro E3. apply (proj1 H3) in E3. destruct E3 as [E2|p3]; [|right; right; right; exact p3].
    apply (proj1 H2) in E2. destruct E2 as [E1|p2]; [|right; right; left; exact p2].
    apply (proj1 H1) in E1. destruct E1 as [E|p1]; [left; exact E|right; left; exact p1].
  - intros [E|[p1|[p2|p3]]]; apply (proj2 H3).
    + left. apply (proj2 H2). left. apply (proj2 H1). left. exact E.
    + left. apply (proj2 H2). left. apply (proj2 H1). right. exact p1.
    + left. apply (proj2 H2). right. exact p2.
    + right. exact p3.
Qed.

Lemma evm_comb : forall (L D D0 X Q Y : Prop), (L <-> D \/ Q) -> (D <-> D0 \/ X) -> (X \/ Q <-> Y) ->
  (L <-> D0 \/ Y).
Proof.
  intros L D D0 X Q Y HL HD K. split; intro h.
  - apply (proj1 HL) in h. destruct h as [d|q].
    + apply (proj1 HD) in d. destruct d as [d0|x]; [left; exact d0|right; apply (proj1 K); left; exact x].
    + right. apply (proj1 K). right. exact q.
  - apply (proj2 HL). destruct h as [d0|y].
    + left. apply (proj2 HD). left. exact d0.
    + apply (proj2 K) in y. destruct y as [x|q]; [left; apply (proj2 HD); right; exact x|right; exact q].
Qed.

Lemma evm_tag_mk : forall o l, tag (mk o l) = (if o then 6 else 5).
Proof. intros [|] l; reflexivity. Qed.

Lemma evm_nth_map_pair : forall (ts : list jv) j,
  nth j (map (fun u => ([] : list Z, u)) ts) ([], JNull) = ([], nth j ts JNull).
Proof. induction ts as [|a ts IH]; intros [|j]; cbn; try reflexivity; apply IH. Qed.

Lemma evm_nth_map_snd : forall (l : list (list Z * jv)) j, nth j (map snd l) JNull = snd (nth j l ([], JNull)).
Proof. induction l as [|a l IH]; intros [|j]; cbn; try reflexivity; apply IH. Qed.

(* the items read so far, one more *)
Lemma evm_ex_snoc : forall o t acc nm u,
  (exists j, (j < length ((nm, u) :: acc))%nat /\ ev_bad o t j (nth j (rev ((nm, u) :: acc)) ([], JNull))) <->
  (exists j, (j < length acc)%nat /\ ev_bad o t j (nth j (rev acc) ([], JNull))) \/
  ev_bad o t (length acc) (nm, u).
Proof.
  intros o t acc nm u. cbn [length rev].
  assert (Lr : length (rev acc) = length acc) by apply length_rev.
  split.
  - intros (j & J & Bj). destruct (Nat.lt_ge_cases j (length acc)) as [Lt|Ge].
    + left. exists j. split; [exact Lt|]. rewrite app_nth1 in Bj by lia. exact Bj.
    + right. assert (j = length acc) by lia. subst j.
      rewrite app_nth2 in Bj by lia. rewrite Lr, Nat.sub_diag in Bj. cbn [nth] in Bj. exact Bj.
  - intros [(j & J & Bj)|Bj].
    + exists j. split; [lia|]. rewrite app_nth1 by lia. exact Bj.
    + exists (length acc). split; [lia|]. rewrite app_nth2 by lia. rewrite Lr, Nat.sub_diag. cbn [nth]. exact Bj.
Qed.

(* a tree of the container's type is not the container read iff some item differs or the counts differ *)
Lemma evm_neq_mk : forall (o : bool) (t : jv) (acc : list (list Z * jv)), tag t = (if o then 6 else 5) ->
  (t <> mk o (rev acc) <->
   (exists j, (j < length acc)%nat /\ ev_bad o t j (nth j (rev acc) ([], JNull))) \/
   length acc <> length (ev_kids t)).
Proof.
  intros o t acc Ht.
  assert (Lr : length (rev acc) = length acc) by apply length_rev.
  destruct o; destruct t as [| | |txt bits|s|ts|ms]; cbn [tag] in Ht; try discriminate Ht;
    unfold ev_bad; cbn [mk ev_kids].
  - rewrite ex_obj_neq, Lr. split.
    + intros [L|(j & J1 & J2 & D)].
      * right. lia.
      * left. exists j. split; [exact J2|]. right.
        destruct D as [D|D]; [left; split; [reflexivity|exact D]|right; exact D].
    + intros [(j & J & Bj)|L].
      * destruct (Nat.lt_ge_cases j (length ms)) as [Jm|Jm]; [|left; lia].
        right. exists j. split; [exact Jm|]. split; [exact J|].
        destruct Bj as [Bj|[[_ Bj]|Bj]]; [lia|left; exact Bj|right; exact Bj].
      * left. lia.
  - rewrite ex_arr_neq, !length_map, Lr. split.
    + intros [L|(j & J1 & J2 & D)].
      * right. lia.
      * left. exists j. split; [exact J2|]. right. right.
        rewrite evm_nth_map_pair. cbn [snd]. rewrite <- evm_nth_map_snd. exact D.
    + intros [(j & J & Bj)|L].
      * destruct (Nat.lt_ge_cases j (length ts)) as [Jm|Jm]; [|left; lia].
        right. exists j. split; [exact Jm|]. split; [exact J|].
        destruct Bj as [Bj|[[Bj _]|Bj]]; [lia|discriminate Bj|].
        rewrite evm_nth_map_pair in Bj. cbn [snd] in Bj. rewrite evm_nth_map_snd. exact Bj.
      * left. lia.
Qed.

(* at the container's first item (acc = []): the type check of C :247-251 *)
Lemma ev_dl_start : forall dl0 v o t dln,
  ev_dl dl0 v o t [] dln <->
  (dln = 0 \/ dln = 1) /\ (dln = 1 <-> dl0 = 1 \/ (v <> 0 /\ ev_tv v o t = false)).
Proof.
  intros dl0 v o t dln. unfold ev_dl. cbn [length rev].
  assert (N : ~ exists j, (j < 0)%nat /\ ev_bad o t j (nth j [] ([], JNull))) by (intros (j & J & _); lia).
  split; intros [H01 H]; (split; [exact H01|]); rewrite H; [|symmetry]; apply evm_or_false; exact N.
Qed.

(* one item (nm, u) read at index n = length acc (C :258-275 and the recursive call):
   kid is &v'->kids[n] or NULL (C :258), dl1 after `if (v' && !kid) in->differs = 1` (C :260-261), dl2 after the
   key comparison of an object (C :267-268; arrays: dl2 = dl1), dl3 the recursive call's post with the kid's tree tk
   (tex_value_specX's `dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> u)` at v = kid, t = tk) *)
Lemma ev_dl_step : forall dl0 v o t acc n nm u kid tk dl dl1 dl2 dl3,
  n = length acc ->
  ev_dl dl0 v o t acc dl ->
  (kid <> 0 <-> ev_v' v o t <> 0 /\ (n < length (ev_kids t))%nat) ->
  (kid <> 0 -> tk = snd (nth n (ev_kids t) ([], JNull))) ->
  (dl1 = 1 <-> dl = 1 \/ (ev_v' v o t <> 0 /\ kid = 0)) ->
  (dl2 = 1 <-> dl1 = 1 \/ (o = true /\ kid <> 0 /\ fst (nth n (ev_kids t) ([], JNull)) <> nm)) ->
  (dl3 = 1 <-> dl2 = 1 \/ (kid <> 0 /\ tk <> u)) ->
  (dl3 = 0 \/ dl3 = 1) ->
  ev_dl dl0 v o t ((nm, u) :: acc) dl3.
Proof.
  intros dl0 v o t acc n nm u kid tk dl dl1 dl2 dl3 Hn [_ Hdl] Hk Htk H1 H2 H3 H01. subst n.
  split; [exact H01|].
  apply (evm_comb _ _ _ _ _ _ (evm_chain _ _ _ _ _ _ _ H1 H2 H3) Hdl).
  pose proof (evm_ex_snoc o t acc nm u) as Ex.
  assert (Eb : ev_bad o t (length acc) (nm, u) <->
     (length (ev_kids t) <= length acc)%nat \/
     (o = true /\ fst (nth (length acc) (ev_kids t) ([], JNull)) <> nm) \/
     snd (nth (length acc) (ev_kids t) ([], JNull)) <> u) by (unfold ev_bad; cbn [fst snd]; apply iff_refl).
  destruct (Z.eq_dec v 0) as [Hv|Hv].
  - assert (V0 : ev_v' v o t = 0) by (subst v; reflexivity).
    assert (K0 : kid = 0)
      by (destruct (Z.eq_dec kid 0) as [K|K]; [exact K|exfalso; exact (proj1 (proj1 Hk K) V0)]).
    split.
    + intros [[N _]|[[N _]|[(_ & K & _)|[K _]]]]; exfalso; [exact (N Hv)|exact (N V0)|exact (K K0)|exact (K K0)].
    + intros [N _]. exfalso. exact (N Hv).
  - destruct (ev_tv v o t) eqn:Etv.
    + assert (V1 : ev_v' v o t = v) by (unfold ev_v'; rewrite Etv; reflexivity).
      assert (V1nz : ev_v' v o t <> 0) by (rewrite V1; exact Hv).
      assert (TF : true = false -> False) by (intro F; discriminate F).
      destruct (Z.eq_dec kid 0) as [K0|K1].
      * assert (L : (length (ev_kids t) <= length acc)%nat).
        { destruct (Nat.lt_ge_cases (length acc) (length (ev_kids t))) as [Lt|Ge]; [|exact Ge].
          exfalso. exact (proj2 Hk (conj V1nz Lt) K0). }
        split.
        -- intros _. split; [exact Hv|right; apply (proj2 Ex); right; apply (proj2 Eb); left; exact L].
        -- intros _. right. left. split; [exact V1nz|exact K0].
      * assert (Lt : (length acc < length (ev_kids t))%nat) by exact (proj2 (proj1 Hk K1)).
        assert (NL : ~ (length (ev_kids t) <= length acc)%nat) by lia.
        assert (Tk : tk = snd (nth (length acc) (ev_kids t) ([], JNull))) by exact (Htk K1).
        split.
        -- intros [[_ [F|Eo]]|[[_ K]|[(Ho & _ & Fn)|(_ & Fu)]]].
           ++ exfalso. exact (TF F).
           ++ split; [exact Hv|right; apply (proj2 Ex); left; exact Eo].
           ++ exfalso. exact (K1 K).
           ++ split; [exact Hv|right; apply (proj2 Ex); right; apply (proj2 Eb); right; left; split; [exact Ho|exact Fn]].
           ++ split; [exact Hv|right; apply (proj2 Ex); right; apply (proj2 Eb); right; right; rewrite <- Tk; exact Fu].
        -- intros [_ [F|En]].
           ++ exfalso. exact (TF F).
           ++ apply (proj1 Ex) in En. destruct En as [Eo|Bd].
              ** left. split; [exact Hv|right; exact Eo].
              ** apply (proj1 Eb) in Bd. destruct Bd as [Lk|[[Ho Fn]|Fu]].
                 --- exfalso. exact (NL Lk).
                 --- right. right. left. split; [exact Ho|split; [exact K1|exact Fn]].
                 --- right. right. right. split; [exact K1|rewrite Tk; exact Fu].
    + split.
      * intros _. split; [exact Hv|left; reflexivity].
      * intros _. left. split; [exact Hv|left; reflexivity].
Qed.

(* the container's end (C :289-290: `if (v' && n != v'->n) in->differs = 1` with n = length acc): the text's
   outcome for the tree read, mk o (rev acc) *)
Lemma ev_dl_final : forall dl0 v o t acc dl dlf,
  ev_dl dl0 v o t acc dl ->
  (dlf = 1 <-> dl = 1 \/ (ev_v' v o t <> 0 /\ length acc <> length (ev_kids t))) ->
  (dlf = 1 <-> dl0 = 1 \/ (v <> 0 /\ t <> mk o (rev acc))).
Proof.
  intros dl0 v o t acc dl dlf [_ Hdl] Hf.
  apply (evm_comb _ _ _ _ _ _ Hf Hdl).
  destruct (Z.eq_dec v 0) as [Hv|Hv].
  - assert (V0 : ev_v' v o t = 0) by (subst v; reflexivity).
    split.
    + intros [[N _]|[N _]]; exfalso; [exact (N Hv)|exact (N V0)].
    + intros [N _]. exfalso. exact (N Hv).
  - destruct (ev_tv v o t) eqn:Etv.
    + assert (V1 : ev_v' v o t = v) by (unfold ev_v'; rewrite Etv; reflexivity).
      assert (Ht : tag t = (if o then 6 else 5)).
      { unfold ev_tv in Etv. apply orb_true_iff in Etv.
        destruct Etv as [E0|E1]; [apply Z.eqb_eq in E0; contradiction|apply Z.eqb_eq; exact E1]. }
      pose proof (evm_neq_mk o t acc Ht) as N.
      assert (TF : true = false -> False) by (intro F; discriminate F).
      split.
      * intros [[_ [F|Eo]]|[_ Ln]].
        -- exfalso. exact (TF F).
        -- split; [exact Hv|apply (proj2 N); left; exact Eo].
        -- split; [exact Hv|apply (proj2 N); right; exact Ln].
      * intros [_ Nm]. apply (proj1 N) in Nm. destruct Nm as [Eo|Ln].
        -- left. split; [exact Hv|right; exact Eo].
        -- right. split; [rewrite V1; exact Hv|exact Ln].
    + assert (Nt : t <> mk o (rev acc)).
      { intro Eq. unfold ev_tv in Etv. apply orb_false_iff in Etv. destruct Etv as [_ E1].
        apply Z.eqb_neq in E1. apply E1. rewrite Eq. apply evm_tag_mk. }
      split.
      * intros _. split; [exact Hv|exact Nt].
      * intros _. left. split; [exact Hv|left; reflexivity].
Qed.
