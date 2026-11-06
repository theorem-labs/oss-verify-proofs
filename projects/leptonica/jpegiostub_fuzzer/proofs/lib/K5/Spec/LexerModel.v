(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import String Ascii ZArith Bool List Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint list_Zeqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => (x =? y) && list_Zeqb l1' l2'
  | _, _ => false
  end.

(* [comment removed for export] *)
Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition P11_MESSAGE_MAX : Z := 512.
Definition PEM_BEGIN : list Z := str "-----BEGIN ".          (* [comment removed for export] *)
Definition PEM_END_REST : list Z := str "-----END ".         (* [comment removed for export] *)
Definition FUZZ_INPUT : list Z := str "fuzz-input".         (* [comment removed for export] *)
Definition NULL_STR : list Z := str "(null)".               (* [comment removed for export] *)
Definition MSG_PEM : list Z := str "invalid pem block: no ending line".
Definition MSG_SECTION : list Z := str "invalid section header: missing braces".
Definition MSG_FIELD : list Z := str "invalid field line: no colon".
Definition FUNC_INIT : list Z := str "p11_lexer_init".
Definition FUNC_NEXT : list Z := str "p11_lexer_next".
Definition EXPR_FILENAME : list Z := str "lexer->filename != NULL".
Definition EXPR_SECTION : list Z := str "lexer->tok.section.name != NULL".
Definition EXPR_FIELD : list Z := str "lexer->tok.field.name != NULL".

(* [comment removed for export] *)
Definition precond_text (expr func : list Z) : list Z :=
  str "p11-kit: '" ++ expr ++ str "' not true at " ++ func ++ [10].
(* [comment removed for export] *)
Definition reached_text (func : list Z) : list Z :=
  str "p11-kit: shouldn't be reached at " ++ func ++ [10].

(* [comment removed for export] *)
Definition message_store_bytes (text : list Z) : list Z :=
  if zlength text <=? P11_MESSAGE_MAX - 2
  then text ++ [0]
  else ztake (P11_MESSAGE_MAX - 2) text ++ [0; 0].

(* [comment removed for export] *)
Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tevent : Type :=
| TMalloc (n : Z) (r : option nat)
| TFree (p : option nat)
| TStderr (bytes : list Z)
| TStdout (bytes : list Z)
| TMsgStore (bytes : list Z)
| TReturn (rc : Z)
| TUnreachable.

(* [comment removed for export] *)
Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;        (* [comment removed for export] *)
  lib_malloc : Z -> M (option ptr);          (* [comment removed for export] *)
  lib_free : option ptr -> M unit;           (* [comment removed for export] *)
  out_stderr : list Z -> M unit;             (* [comment removed for export] *)
  out_stdout : list Z -> M unit;             (* [comment removed for export] *)
  msg_store : list Z -> M unit               (* [comment removed for export] *)
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bytes.
Variable d : list Z.

(* [comment removed for export] *)
Fixpoint memchr_n (n : nat) (pos c : Z) : option Z :=
  match n with
  | O => None
  | S n' => if znth d pos =? c then Some pos else memchr_n n' (pos + 1) c
  end.
Definition memchr (pos c n : Z) : option Z := memchr_n (Z.to_nat n) pos c.

(* [comment removed for export] *)
Definition strncmp_lit (pos : Z) (lit : list Z) : bool :=
  list_Zeqb (ztake (zlength lit) (zdrop pos d)) lit.

(* [comment removed for export] *)
Fixpoint strnstr_n (fuel : nat) (s slen : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if slen <? 1 then None
      else let sc := znth d s in
           if sc =? 0 then None
           else if negb (sc =? 10) then strnstr_n f (s + 1) (slen - 1)
           else if slen - 1 <? zlength PEM_END_REST then None
           else if strncmp_lit (s + 1) PEM_END_REST then Some s
           else strnstr_n f (s + 1) (slen - 1)
  end.
Definition strnstr_end (s slen : Z) : option Z := strnstr_n (S (Z.to_nat slen)) s slen.

(* [comment removed for export] *)
Fixpoint skip_fwd_n (fuel : nat) (p e : Z) : Z :=
  match fuel with
  | O => p
  | S f => if negb (p =? e) && is_space (znth d p) then skip_fwd_n f (p + 1) e else p
  end.
Definition skip_fwd (p e : Z) : Z := skip_fwd_n (Z.to_nat (e - p)) p e.

(* [comment removed for export] *)
Fixpoint skip_back_n (fuel : nat) (p e : Z) : Z :=
  match fuel with
  | O => e
  | S f => if negb (p =? e) && is_space (znth d (e - 1)) then skip_back_n f p (e - 1) else e
  end.
Definition skip_back (p e : Z) : Z := skip_back_n (Z.to_nat (e - p)) p e.

(* [comment removed for export] *)
Fixpoint count_nl_n (fuel : nat) (pos e line : Z) : Z :=
  match fuel with
  | O => line
  | S f =>
      if pos <? e then
        match memchr pos 10 (e - pos) with
        | None => line
        | Some p => count_nl_n f (p + 1) e (line + 1)
        end
      else line
  end.
Definition count_nl (pos e line : Z) : Z := count_nl_n (Z.to_nat (e - pos)) pos e line.

(* [comment removed for export] *)
Fixpoint cstr (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: l' => if c =? 0 then [] else c :: cstr l'
  end.

(* [comment removed for export] *)
Definition strndup_bytes (p n : Z) : list Z :=
  let s := cstr (ztake n (zdrop p d)) in
  s ++ repeat 0 (Z.to_nat (n + 1 - zlength s)).

End Bytes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BytesFacts.
Variable d : list Z.

Lemma memchr_n_some : forall n pos c p,
  memchr_n d n pos c = Some p ->
  pos <= p < pos + Z.of_nat n /\ znth d p = c /\
  (forall q, pos <= q < p -> znth d q <> c).
Proof.
  induction n as [|n IH]; intros pos c p H; cbn [memchr_n] in H.
  - discriminate.
  - destruct (Z.eqb_spec (znth d pos) c) as [E|NE].
    + injection H as <-. split; [lia|]. split; [exact E|]. intros q Hq. lia.
    + specialize (IH _ _ _ H). destruct IH as (A & B & C).
      split; [lia|]. split; [assumption|].
      intros q Hq. destruct (Z.eq_dec q pos) as [->|]; [exact NE|]. apply C. lia.
Qed.

Lemma memchr_n_none : forall n pos c,
  memchr_n d n pos c = None -> forall q, pos <= q < pos + Z.of_nat n -> znth d q <> c.
Proof.
  induction n as [|n IH]; intros pos c H q Hq; cbn [memchr_n] in H.
  - lia.
  - destruct (Z.eqb_spec (znth d pos) c) as [E|NE]; [discriminate|].
    destruct (Z.eq_dec q pos) as [->|]; [exact NE|]. eapply IH; [exact H|]. lia.
Qed.

Lemma memchr_some : forall pos c n p, 0 <= n ->
  memchr d pos c n = Some p ->
  pos <= p < pos + n /\ znth d p = c /\ (forall q, pos <= q < p -> znth d q <> c).
Proof.
  intros pos c n p Hn H. unfold memchr in H. apply memchr_n_some in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma memchr_none : forall pos c n, 0 <= n ->
  memchr d pos c n = None -> forall q, pos <= q < pos + n -> znth d q <> c.
Proof.
  intros pos c n Hn H q Hq. unfold memchr in H. eapply memchr_n_none in H; [exact H|]. rewrite Z2Nat.id by lia. exact Hq.
Qed.

Lemma skip_fwd_n_bounds : forall f p e, p <= e -> p <= skip_fwd_n d f p e <= e.
Proof.
  induction f as [|f IH]; intros p e H; cbn [skip_fwd_n]; [lia|].
  destruct (Z.eqb_spec p e) as [->|NE]; cbn [negb andb]; [lia|].
  destruct (is_space (znth d p)); [|lia]. specialize (IH (p + 1) e). lia.
Qed.

Lemma skip_fwd_n_exit : forall f p e, p <= e -> Z.of_nat f = e - p ->
  let r := skip_fwd_n d f p e in
  (r = e \/ is_space (znth d r) = false) /\ (forall q, p <= q < r -> is_space (znth d q) = true).
Proof.
  induction f as [|f IH]; intros p e H Hf; cbn [skip_fwd_n].
  - split; [left; lia| intros; lia].
  - destruct (Z.eqb_spec p e) as [->|NE]; cbn [negb andb]; [split; [left; reflexivity| intros; lia]|].
    destruct (is_space (znth d p)) eqn:Hs.
    + destruct (IH (p + 1) e) as [A B]; [lia|lia|]. split; [exact A|].
      intros q Hq. destruct (Z.eq_dec q p) as [->|]; [exact Hs|]. apply B. lia.
    + split; [right; exact Hs| intros; lia].
Qed.

Lemma skip_fwd_bounds : forall p e, p <= e -> p <= skip_fwd d p e <= e.
Proof. intros. unfold skip_fwd. apply skip_fwd_n_bounds. lia. Qed.

Lemma skip_fwd_exit : forall p e, p <= e ->
  (skip_fwd d p e = e \/ is_space (znth d (skip_fwd d p e)) = false) /\
  (forall q, p <= q < skip_fwd d p e -> is_space (znth d q) = true).
Proof. intros p e H. unfold skip_fwd. apply (skip_fwd_n_exit (Z.to_nat (e - p)) p e H). lia. Qed.

Lemma skip_back_n_bounds : forall f p e, p <= e -> p <= skip_back_n d f p e <= e.
Proof.
  induction f as [|f IH]; intros p e H; cbn [skip_back_n]; [lia|].
  destruct (Z.eqb_spec p e) as [->|NE]; cbn [negb andb]; [lia|].
  destruct (is_space (znth d (e - 1))); [|lia]. specialize (IH p (e - 1)). lia.
Qed.

Lemma skip_back_n_exit : forall f p e, p <= e -> Z.of_nat f = e - p ->
  let r := skip_back_n d f p e in
  (r = p \/ is_space (znth d (r - 1)) = false) /\ (forall q, r <= q < e -> is_space (znth d q) = true).
Proof.
  induction f as [|f IH]; intros p e H Hf; cbn [skip_back_n].
  - split; [left; lia| intros; lia].
  - destruct (Z.eqb_spec p e) as [<-|NE]; cbn [negb andb]; [split; [left; reflexivity| intros; lia]|].
    destruct (is_space (znth d (e - 1))) eqn:Hs.
    + destruct (IH p (e - 1)) as [A B]; [lia|lia|]. split; [exact A|].
      intros q Hq. destruct (Z.eq_dec q (e - 1)) as [->|]; [exact Hs|]. apply B. lia.
    + split; [right; exact Hs| intros; lia].
Qed.

Lemma skip_back_bounds : forall p e, p <= e -> p <= skip_back d p e <= e.
Proof. intros. unfold skip_back. apply skip_back_n_bounds. lia. Qed.

Lemma skip_back_exit : forall p e, p <= e ->
  (skip_back d p e = p \/ is_space (znth d (skip_back d p e - 1)) = false) /\
  (forall q, skip_back d p e <= q < e -> is_space (znth d q) = true).
Proof. intros p e H. unfold skip_back. apply (skip_back_n_exit (Z.to_nat (e - p)) p e H). lia. Qed.

Lemma strnstr_n_some : forall f s slen p,
  strnstr_n d f s slen = Some p ->
  s <= p /\ p + 1 + zlength PEM_END_REST <= s + slen /\
  znth d p = 10 /\ strncmp_lit d (p + 1) PEM_END_REST = true /\
  (forall q, s <= q < p -> znth d q <> 0).
Proof.
  induction f as [|f IH]; intros s slen p H; cbn [strnstr_n] in H; [discriminate|].
  destruct (Z.ltb_spec slen 1); [discriminate|].
  destruct (Z.eqb_spec (znth d s) 0) as [E0|NE0]; [discriminate|].
  destruct (Z.eqb_spec (znth d s) 10) as [E10|NE10]; cbn [negb] in H.
  - destruct (Z.ltb_spec (slen - 1) (zlength PEM_END_REST)); [discriminate|].
    destruct (strncmp_lit d (s + 1) PEM_END_REST) eqn:Hc.
    + injection H as <-. repeat split; auto; try lia; try (intros q Hq; lia).
    + specialize (IH _ _ _ H). destruct IH as (A & B & C & D & E). repeat split; auto; try lia.
      intros q Hq. destruct (Z.eq_dec q s) as [->|]; [exact NE0|]. apply E. lia.
  - specialize (IH _ _ _ H). destruct IH as (A & B & C & D & E). repeat split; auto; try lia.
    intros q Hq. destruct (Z.eq_dec q s) as [->|]; [exact NE0|]. apply E. lia.
Qed.

Lemma strnstr_end_some : forall s slen p,
  strnstr_end d s slen = Some p ->
  s <= p /\ p + 10 <= s + slen /\ znth d p = 10 /\ strncmp_lit d (p + 1) PEM_END_REST = true.
Proof.
  intros s slen p H. unfold strnstr_end in H. apply strnstr_n_some in H.
  destruct H as (A & B & C & D & _). cbn [zlength PEM_END_REST length str map list_ascii_of_string Z.of_nat] in B.
  repeat split; auto. unfold zlength in B. cbn in B. lia.
Qed.

Lemma count_nl_n_bounds : forall f pos e line,
  pos <= e -> line <= count_nl_n d f pos e line <= line + (e - pos).
Proof.
  induction f as [|f IH]; intros pos e line H; cbn [count_nl_n]; [lia|].
  destruct (Z.ltb_spec pos e); [|lia].
  destruct (memchr d pos 10 (e - pos)) as [p|] eqn:Hm; [|lia].
  apply memchr_some in Hm; [|lia]. destruct Hm as (A & _ & _).
  specialize (IH (p + 1) e (line + 1)). lia.
Qed.

Lemma count_nl_bounds : forall pos e line, pos <= e -> line <= count_nl d pos e line <= line + (e - pos).
Proof. intros. unfold count_nl. apply count_nl_n_bounds. lia. Qed.

End BytesFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k))
  (at level 100, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k))
  (at level 100, right associativity).

(* [comment removed for export] *)
Inductive token : Type :=
| TokEOF                                   (* [comment removed for export] *)
| TokSection (name : ptr)                  (* [comment removed for export] *)
| TokField (name : ptr) (value : ptr)      (* [comment removed for export] *)
| TokPem (begin_ : Z) (len : Z).           (* [comment removed for export] *)

Record lexer : Type := mkLexer {
  lx_filename : option ptr;   (* [comment removed for export] *)
  lx_line : Z;                (* [comment removed for export] *)
  lx_at : Z;                  (* [comment removed for export] *)
  lx_remaining : Z;           (* [comment removed for export] *)
  lx_complained : bool;
  lx_tok : token
}.

Variable d : list Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition clear_state (lx : lexer) : M lexer :=
  match lx_tok lx with
  | TokField n v => lib_free ops (Some n) ;;; lib_free ops (Some v)
  | TokSection n => lib_free ops (Some n)
  | TokPem _ _ | TokEOF => ret ops tt
  end ;;;
  ret ops (mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) false TokEOF).

(* [comment removed for export] *)
Definition lexer_msg_text (lx : lexer) (msg : list Z) : list Z :=
  (match lx_filename lx with Some _ => FUZZ_INPUT | None => NULL_STR end)
    ++ [58] ++ Zdecimal (lx_line lx) ++ [58; 32] ++ msg.

Definition lexer_msg (lx : lexer) (msg : list Z) : M lexer :=
  if lx_complained lx then ret ops lx
  else match lx_tok lx with
       | TokEOF =>
           msg_store ops (message_store_bytes (lexer_msg_text lx msg)) ;;;
           ret ops (mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) true TokEOF)
       | _ => unreachable ops
       end.

(* [comment removed for export] *)
Definition next_result : Type := (bool * bool * lexer)%type.

Definition set_tok (lx : lexer) (t : token) : lexer :=
  mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) (lx_complained lx) t.

(* [comment removed for export] *)
Definition line_body (k : lexer -> M next_result) (lx : lexer) (end_ : Z) (lx2 : lexer) : M next_result :=
    let line := lx_at lx in
    (* [comment removed for export] *)
    let line1 := skip_fwd d line end_ in
    let end1 := skip_back d line1 end_ in
    (* [comment removed for export] *)
    if (line1 =? end1) || (znth d line1 =? 35) then k lx2
    else if znth d line1 =? 91 then
      (* [comment removed for export] *)
      if negb (znth d (end1 - 1) =? 93) then
        lx' <- lexer_msg lx2 MSG_SECTION ;;
        ret ops (false, true, lx')
      else
        (* [comment removed for export] *)
        r <- lib_malloc ops ((end1 - line1) - 2 + 1) ;;
        match r with
        | None => out_stderr ops (precond_text EXPR_SECTION FUNC_NEXT) ;;;
                  ret ops (false, false, lx2)
        | Some p => ret ops (true, false, set_tok lx2 (TokSection p))
        end
    else
      (* [comment removed for export] *)
      match memchr d line1 58 (end1 - line1) with
      | None =>
          lx' <- lexer_msg lx2 MSG_FIELD ;;
          ret ops (false, true, lx')
      | Some colon =>
          let value := skip_fwd d (colon + 1) end1 in
          let colon1 := skip_back d line1 colon in
          (* [comment removed for export] *)
          r1 <- lib_malloc ops ((colon1 - line1) + 1) ;;
          match r1 with
          | None => out_stderr ops (precond_text EXPR_FIELD FUNC_NEXT) ;;;
                    ret ops (false, false, lx2)
          | Some pn =>
              (* [comment removed for export] *)
              r2 <- lib_malloc ops ((end1 - value) + 1) ;;
              match r2 with
              | None => lib_free ops (Some pn) ;;;
                        out_stderr ops (reached_text FUNC_NEXT) ;;;
                        ret ops (false, false, lx2)
              | Some pv => ret ops (true, false, set_tok lx2 (TokField pn pv))
              end
          end
      end.

(* [comment removed for export] *)
Definition pem_body (lx : lexer) : M next_result :=
  let at_ := lx_at lx in
  let rem := lx_remaining lx in
    match strnstr_end d at_ rem with
    | None =>
        lx' <- lexer_msg lx MSG_PEM ;;
        ret ops (false, true, lx')
    | Some pos =>
        (* [comment removed for export] *)
        let end_ := match memchr d (pos + 1) 10 (rem - (pos - at_) - 1) with
                    | Some e => e + 1
                    | None => at_ + rem
                    end in
        let line' := count_nl d at_ end_ (lx_line lx) in
        ret ops (true, false,
                 mkLexer (lx_filename lx) line' end_ (rem - (end_ - at_)) (lx_complained lx)
                         (TokPem at_ (end_ - at_)))
    end.

(* [comment removed for export] *)
Definition split_line (lx : lexer) : Z * lexer :=
  let at_ := lx_at lx in
  let rem := lx_remaining lx in
      match memchr d at_ 10 rem with
      | None => (at_ + rem,
                 mkLexer (lx_filename lx) (lx_line lx) (at_ + rem) 0 (lx_complained lx) (lx_tok lx))
      | Some e => (e,
                   mkLexer (lx_filename lx) (lx_line lx + 1) (e + 1) (rem - (e - at_) - 1)
                           (lx_complained lx) (lx_tok lx))
      end.

(* [comment removed for export] *)
Fixpoint next_loop (fuel : nat) (lx : lexer) : M next_result :=
  match fuel with
  | O => unreachable ops
  | S fuel' =>
  if lx_remaining lx =? 0 then ret ops (false, false, lx)                 (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  if (11 <=? lx_remaining lx) && strncmp_lit d (lx_at lx) PEM_BEGIN then pem_body lx
  else
    let '(end_, lx2) := split_line lx in
    line_body (next_loop fuel') lx end_ lx2
  end.

(* [comment removed for export] *)
Definition lexer_next (lx : lexer) : M next_result :=
  lx1 <- clear_state lx ;;
  next_loop (S (Z.to_nat (lx_remaining lx1))) lx1.

(* [comment removed for export] *)
Definition lexer_init (len : Z) : M lexer :=
  r <- lib_malloc ops (zlength FUZZ_INPUT + 1) ;;
  match r with
  | None => out_stderr ops (precond_text EXPR_FILENAME FUNC_INIT)
  | Some _ => ret ops tt
  end ;;;
  ret ops (mkLexer r 0 0 len false TokEOF).

(* [comment removed for export] *)
Definition lexer_done (lx : lexer) : M unit :=
  lx1 <- clear_state lx ;;
  lib_free ops (lx_filename lx1).

(* [comment removed for export] *)
Fixpoint lex_all (fuel : nat) (lx : lexer) : M lexer :=
  match fuel with
  | O => unreachable ops
  | S fuel' =>
      r <- lexer_next lx ;;
      let '(ok, _, lx') := r in
      if ok then lex_all fuel' lx' else ret ops lx'
  end.

(* [comment removed for export] *)
Definition fuzz_one : M Z :=
  lx <- lexer_init (zlength d) ;;
  lx' <- lex_all (S (Z.to_nat (zlength d))) lx ;;
  lexer_done lx' ;;;
  ret ops 0.

(* [comment removed for export] *)
Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;       (* [comment removed for export] *)
      run_calls n' rc'
  end.

(* [comment removed for export] *)
Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in       (* [comment removed for export] *)
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  (* [comment removed for export] *)
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2                                          (* [comment removed for export] *)
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;                                   (* [comment removed for export] *)
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Arguments TokEOF {ptr}.
Arguments TokSection {ptr}.
Arguments TokField {ptr}.
Arguments TokPem {ptr}.
Arguments mkLexer {ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module LexRun.

(* [comment removed for export] *)
Inductive ttree (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TEv (e : tevent) (k : ttree A)
| TMallocQ (n : Z) (k : option nat -> ttree A).
Arguments TRet {A}.
Arguments TUnr {A}.
Arguments TEv {A}.
Arguments TMallocQ {A}.

Fixpoint tbind {A B} (m : ttree A) (f : A -> ttree B) : ttree B :=
  match m with
  | TRet a => f a
  | TUnr => TUnr
  | TEv e k => TEv e (tbind k f)
  | TMallocQ n k => TMallocQ n (fun r => tbind (k r) f)
  end.

Definition tree_ops : target_ops ttree nat :=
  mkOps (fun A (a : A) => TRet a)
        (fun A B m f => tbind m f)
        (fun A => TUnr)
        (fun n => TMallocQ n (fun r => TRet r))
        (fun p => TEv (TFree p) (TRet tt))
        (fun bs => TEv (TStderr bs) (TRet tt))
        (fun bs => TEv (TStdout bs) (TRet tt))
        (fun bs => TEv (TMsgStore bs) (TRet tt)).

Definition target_tree (cfg payload : list Z) : ttree Z :=
  target_run tree_ops payload cfg.

(* [comment removed for export] *)
Fixpoint run_tree {A} (t : ttree A) (oracle : list bool) (next : nat) (acc : list tevent)
  : list tevent * option A :=
  match t with
  | TRet a => (rev acc, Some a)
  | TUnr => (rev (TUnreachable :: acc), None)
  | TEv e k => run_tree k oracle next (e :: acc)
  | TMallocQ n k =>
      let '(ok, oracle') := match oracle with
                            | [] => (true, [])
                            | b :: o' => (b, o')
                            end in
      let r := if ok then Some next else None in
      run_tree (k r) oracle' (S next) (TMalloc n r :: acc)
  end.

Definition target_events (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := run_tree (target_tree cfg payload) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End LexRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module LexerModelTests.
Import LexRun.

(* [comment removed for export] *)
Example ex_basic :
  target_events [0] (str "[sec]" ++ [10] ++ str "key: value" ++ [10]) []
  = [TMalloc 17 (Some 0%nat);                       (* [comment removed for export] *)
     TMalloc 11 (Some 1%nat);                       (* [comment removed for export] *)
     TMalloc 4 (Some 2%nat);                        (* [comment removed for export] *)
     TFree (Some 2%nat);                            (* [comment removed for export] *)
     TMalloc 4 (Some 3%nat);                        (* [comment removed for export] *)
     TMalloc 6 (Some 4%nat);                        (* [comment removed for export] *)
     TFree (Some 3%nat); TFree (Some 4%nat);        (* [comment removed for export] *)
     TFree (Some 1%nat);                            (* [comment removed for export] *)
     TStdout [48; 10];                              (* [comment removed for export] *)
     TFree (Some 0%nat);                            (* [comment removed for export] *)
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Example ex_empty_fail :
  target_events [1] [] [false]
  = [TMalloc 11 None;
     TStderr (precond_text EXPR_FILENAME FUNC_INIT);
     TFree None;                                    (* [comment removed for export] *)
     TStdout [48; 10];
     TMalloc 11 (Some 1%nat);
     TFree (Some 1%nat);
     TStdout [48; 10];
     TFree None;                                    (* [comment removed for export] *)
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Example ex_msg_null :
  target_events [] (str "# c" ++ [10] ++ str " oops " ++ [10]) [true; false]
  = [TMalloc 11 (Some 0%nat);
     TMalloc 11 None;
     TStderr (precond_text EXPR_FILENAME FUNC_INIT);
     TMsgStore (str "(null):2: invalid field line: no colon" ++ [0]);
     TFree None;
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Example ex_copy_fail :
  target_events [3] [65] [false] = [TMalloc 1 None; TReturn 2].
Proof. vm_compute. reflexivity. Qed.

End LexerModelTests.
