(* fuzz_preset, parse_value's image-B walk (lane PValueB): the PURE grammar facts the walk reads off the reader model
   lib/Spec/PjGrammar.v (jr_value / jr_items / jr_string / lit / jr_number over a strtod model sm), each in the shape
   one arm of the machine code takes. No machine state, no image number. Numerals are the JSON bytes the code
   compares with (34 double quote, 45 '-', 48 '0', 91 '[', 102 'f', 110 'n', 116 't', 123 '{': WORD) and the plain bound
   constants 224 / 512 (LENGTH, PjGrammar vspec). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.

Section m.
Variable sm : list Z -> Z * Z.

(* the items branch of jrv at any fuel that covers the members after the opener *)
Lemma pvm_items_fuel : forall f d o b y ok, (2 * length y + 2 <= f)%nat ->
  jr_cont (jrl sm f) d o (b :: y) ok = jr_items sm d o (b :: y) ok.
Proof.
  intros f d o b y ok H. unfold jr_items.
  remember (2 * length (b :: y) + 2)%nat as F eqn:HF. cbn [length] in HF.
  unfold jr_cont. cbn [tl].
  destruct (Nat.ltb MAXD (S d)); [reflexivity|].
  pose proof (skip_len y) as Hs.
  destruct (skip y) as [|c r] eqn:Ey.
  - rewrite (proj2 (fuel_mono sm 2) (S d) o 0%nat 0%nat [] [] f ok) by (cbn [length]; lia).
    rewrite (proj2 (fuel_mono sm 2) (S d) o 0%nat 0%nat [] [] F ok) by (cbn [length]; lia).
    reflexivity.
  - destruct (c =? closer o); [reflexivity|].
    cbn [length] in Hs.
    rewrite (proj2 (fuel_mono sm (2 * length (c :: r) + 2)) (S d) o 0%nat 0%nat [] (c :: r) f ok)
      by (cbn [length]; lia).
    rewrite (proj2 (fuel_mono sm (2 * length (c :: r) + 2)) (S d) o 0%nat 0%nat [] (c :: r) F ok)
      by (cbn [length]; lia).
    reflexivity.
Qed.

(* jr_value by the first byte after the white space, the dispatch of the machine code *)
Lemma pvm_unfold : forall d x ok, jr_value sm d x ok =
  match skip x with
  | [] => (None, [], ok)
  | b :: y =>
    if b =? 123 then jr_items sm d true (b :: y) ok
    else if b =? 91 then jr_items sm d false (b :: y) ok
    else if b =? 34 then jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)) ok
    else if b =? 116 then lit w_true JTrue (b :: y) ok
    else if b =? 102 then lit w_false JFalse (b :: y) ok
    else if b =? 110 then lit w_null JNull (b :: y) ok
    else jr_number sm (b :: y) ok
  end.
Proof.
  intros d x ok. unfold jr_value. cbn [jrv].
  pose proof (skip_len x) as Hs.
  destruct (skip x) as [|b y] eqn:Ex; [reflexivity|].
  cbn [length] in Hs.
  destruct (b =? 123); [apply pvm_items_fuel; lia|].
  destruct (b =? 91); [apply pvm_items_fuel; lia|].
  destruct (b =? 34); [reflexivity|].
  destruct (b =? 116); [reflexivity|].
  destruct (b =? 102); [reflexivity|].
  destruct (b =? 110); reflexivity.
Qed.

(* the string arm's model outcome, by the first allocation outcome *)
Lemma pvm_string : forall y ok,
  jr_string y ok =
  match scan y with
  | None => (None, [], ok)
  | Some q =>
      let (b, ok1) := take ok in
      if b then
        match decode y with
        | Some sr => (Some sr, [EAlloc (S q)], ok1)
        | None => (None, [EAlloc (S q); EFree (S q)], ok1)
        end
      else (None, [EFail (S q)], ok1)
  end.
Proof.
  intros y ok. unfold jr_string.
  destruct (scan y) as [q|]; [|reflexivity].
  destruct ok as [|b ok]; [|destruct b]; destruct (decode y) as [sr|]; reflexivity.
Qed.

(* the number arm's model outcome, in the order the machine code tests: the optional minus, the first digit, a
   leading zero followed by a digit, the token (span numch), the allocation outcome, the strtod test *)
Lemma pvm_number : forall x ok, jr_number sm x ok =
  let j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end in
  match skipn j x with
  | [] => (None, [], ok)
  | c :: z =>
    if negb (digit c) then (None, [], ok)
    else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then (None, [], ok)
    else
      let (a, r) := span numch z in
      let txt := firstn j x ++ c :: a in
      let (bk, ok1) := take ok in
      if bk then
        (if whole sm txt then (Some (JNum txt (snd (sm txt)), r), [EAlloc (S (length txt))], ok1)
         else (None, [EAlloc (S (length txt))], ok1))
      else (None, [EFail (S (length txt))], ok1)
  end.
Proof.
  intros x ok. unfold jr_number. cbv beta zeta.
  match goal with |- context [skipn ?j x] => destruct (skipn j x) as [|c z] end; [reflexivity|].
  destruct (negb (digit c)); [reflexivity|].
  match goal with |- context [andb (c =? 48) ?m] => destruct (andb (c =? 48) m) end; [reflexivity|].
  destruct (span numch z) as [a r].
  match goal with |- context [whole sm ?t] => destruct (whole sm t) end;
    destruct ok as [|bk ok]; try destruct bk; reflexivity.
Qed.

(* what span numch leaves: the token bytes are number characters and the first byte after it is not *)
Lemma pvm_span : forall z a r, span numch z = (a, r) ->
  z = a ++ r /\ Forall (fun b => numch b = true) a /\
  (r = [] \/ exists b r', r = b :: r' /\ numch b = false).
Proof.
  intros z. induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- <-. split; [reflexivity|]. split; [constructor|]. left; reflexivity.
  - destruct (numch b) eqn:Eb.
    + destruct (span numch z) as [a1 r1] eqn:E. injection H as <- <-.
      destruct (IH a1 r1 eq_refl) as (H1 & H2 & H3). rewrite H1.
      split; [reflexivity|]. split; [constructor; [exact Eb | exact H2]|exact H3].
    + injection H as <- <-. split; [reflexivity|]. split; [constructor|].
      right. exists b, z. split; [reflexivity|exact Eb].
Qed.

(* the strtod test of the machine code: the byte at the end pointer (txt is NUL-terminated in its buffer) is NUL
   exactly when strtod consumed the whole token, and the value class test is PjGrammar.finite *)
Lemma pvm_whole : forall txt c bits, sm txt = (c, bits) -> 0 <= c <= Z.of_nat (length txt) ->
  Forall (fun b => numch b = true) txt ->
  (whole sm txt = true <-> nth (Z.to_nat c) (txt ++ [0]) 0 = 0 /\ finite bits = true).
Proof.
  intros txt c bits Hsm Hc Hf. unfold whole. rewrite Hsm. cbn [fst snd].
  split.
  - intros H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst c.
    split; [|exact H2]. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros [Hn Hb]. apply andb_true_iff. split; [|exact Hb]. apply Z.eqb_eq.
    destruct (Nat.lt_ge_cases (Z.to_nat c) (length txt)) as [Hlt|Hge].
    + exfalso. rewrite app_nth1 in Hn by exact Hlt.
      assert (Hin : In (nth (Z.to_nat c) txt 0) txt) by (apply nth_In; exact Hlt).
      rewrite Forall_forall in Hf. specialize (Hf _ Hin). rewrite Hn in Hf.
      vm_compute in Hf. discriminate Hf.
    + lia.
Qed.

End m.

(* skip leaves a suffix of its input *)
Lemma pvm_skip_suffix : forall x, skip x = skipn (length x - length (skip x)) x.
Proof.
  induction x as [|b r IH]; [reflexivity|].
  cbn [skip length]. destruct (ws b).
  - pose proof (skip_len r) as Hs.
    replace (S (length r) - length (skip r))%nat with (S (length r - length (skip r))) by lia.
    cbn [skipn]. exact IH.
  - cbn [length]. rewrite Nat.sub_diag. reflexivity.
Qed.

(* the cursor after skip_ws, in rest_atR form (the skip_ws text states it as text + len - |skip rest|) *)
Lemma pvm_skip_rest : forall (tb : list Z) text len p,
  Z.of_nat (length tb) = len -> text <= p <= text + len ->
  rest_atR tb text (text + len - Z.of_nat (length (skip (rest_atR tb text p)))) = skip (rest_atR tb text p) /\
  p <= text + len - Z.of_nat (length (skip (rest_atR tb text p))) <= text + len.
Proof.
  intros tb text len p Hlen Hp. unfold rest_atR.
  remember (Z.to_nat (p - text)) as k eqn:Ek.
  pose proof (skip_len (skipn k tb)) as Hs. rewrite length_skipn in Hs.
  split.
  - transitivity (skipn ((length (skipn k tb) - length (skip (skipn k tb))) + k) tb).
    + f_equal. rewrite length_skipn. lia.
    + rewrite <- skipn_skipn. symmetry. apply pvm_skip_suffix.
  - lia.
Qed.

(* a trace's peak held bytes is bounded by any bound on the held bytes of its prefixes *)
Lemma pvm_hpeak_prefix : forall (t : list ev) (Bd : Z), 0 <= Bd ->
  (forall p rest, t = p ++ rest -> held p <= Bd) -> hpeakR t <= Bd.
Proof.
  induction t as [|e r IH]; intros Bd HB H; cbn [hpeakR]; [exact HB|].
  assert (H1 : held_ev e <= Bd).
  { specialize (H [e] r eq_refl). cbn [held] in H. lia. }
  assert (H2 : hpeakR r <= Bd - held_ev e).
  { apply IH; [lia|]. intros p rest E.
    specialize (H (e :: p) rest (f_equal (cons e) E)). cbn [held] in H. lia. }
  lia.
Qed.

(* parse_value's peak bound of the post (plain parse_value_c.v:54), from PjGrammar.G10_2 *)
Lemma pvm_hpeak : forall sm d x ok,
  hpeakR (snd (fst (jr_value sm d x ok))) <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (MAXD - d).
Proof.
  intros sm d x ok. apply pvm_hpeak_prefix; [lia|].
  intros p rest E. exact (G10_2 sm d x ok p rest E).
Qed.
