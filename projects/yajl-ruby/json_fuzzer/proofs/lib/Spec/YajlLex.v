(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope yprog_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ytok : Type :=
| TK_bool | TK_colon | TK_comma | TK_eof | TK_error
| TK_left_brace      (* [comment removed for export] *)
| TK_left_bracket    (* [comment removed for export] *)
| TK_null
| TK_right_brace     (* [comment removed for export] *)
| TK_right_bracket   (* [comment removed for export] *)
| TK_integer | TK_double
| TK_string | TK_string_esc   (* [comment removed for export] *)
| TK_comment.

Definition tok_code (t : ytok) : Z :=
  match t with
  | TK_bool => 0 | TK_colon => 1 | TK_comma => 2 | TK_eof => 3 | TK_error => 4
  | TK_left_brace => 5 | TK_left_bracket => 6 | TK_null => 7 | TK_right_brace => 8
  | TK_right_bracket => 9 | TK_integer => 10 | TK_double => 11 | TK_string => 12
  | TK_string_esc => 13 | TK_comment => 14
  end.

Definition tok_eqb (a b : ytok) : bool := tok_code a =? tok_code b.

Inductive lex_error : Type :=
| LE_ok
| LE_string_invalid_utf8
| LE_string_invalid_escaped_char
| LE_string_invalid_json_char
| LE_string_invalid_hex_char
| LE_invalid_char
| LE_invalid_string
| LE_missing_integer_after_decimal
| LE_missing_integer_after_exponent
| LE_missing_integer_after_minus
| LE_unallowed_comment
| LE_alloc_failed.

Definition lex_error_code (e : lex_error) : Z :=
  match e with
  | LE_ok => 0 | LE_string_invalid_utf8 => 1 | LE_string_invalid_escaped_char => 2
  | LE_string_invalid_json_char => 3 | LE_string_invalid_hex_char => 4 | LE_invalid_char => 5
  | LE_invalid_string => 6 | LE_missing_integer_after_decimal => 7
  | LE_missing_integer_after_exponent => 8 | LE_missing_integer_after_minus => 9
  | LE_unallowed_comment => 10 | LE_alloc_failed => 11
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ylexer : Type := mkLexer {
  lx_lineOff : Z;
  lx_charOff : Z;
  lx_error : lex_error;
  lx_buf : ybuf;            (* [comment removed for export] *)
  lx_bufblk : yptr;         (* [comment removed for export] *)
  lx_bufOff : Z;
  lx_bufInUse : Z;
  lx_allowComments : Z;
  lx_validateUTF8 : Z
}.

Definition SIZEOF_YAJL_LEXER_T : Z := 48.

Definition lx_set_error (lx : ylexer) (e : lex_error) : ylexer :=
  mkLexer (lx_lineOff lx) (lx_charOff lx) e (lx_buf lx) (lx_bufblk lx)
          (lx_bufOff lx) (lx_bufInUse lx) (lx_allowComments lx) (lx_validateUTF8 lx).
Definition lx_set_error_opt (lx : ylexer) (e : option lex_error) : ylexer :=
  match e with Some e => lx_set_error lx e | None => lx end.
Definition lx_set_buf (lx : ylexer) (b : ybuf) (bufOff bufInUse : Z) : ylexer :=
  mkLexer (lx_lineOff lx) (lx_charOff lx) (lx_error lx) b (lx_bufblk lx)
          bufOff bufInUse (lx_allowComments lx) (lx_validateUTF8 lx).

(* [comment removed for export] *)
Definition ylex_alloc (allowComments validateUTF8 : Z) : yprog (option (yptr * ylexer)) :=
  r <- ymalloc SIZEOF_YAJL_LEXER_T ;;
  match r with
  | None => YRet None
  | Some blk =>
      rb <- ybuf_alloc ;;
      match rb with
      | None => yfree (Some blk) ;;; YRet None
      | Some bufblk =>
          YRet (Some (blk, mkLexer 0 0 LE_ok ybuf_zero bufblk 0 0 allowComments validateUTF8))
      end
  end.

(* [comment removed for export] *)
Definition ylex_free (blk : yptr) (lx : ylexer) : yprog unit :=
  ybuf_free (lx_bufblk lx) (lx_buf lx) ;;; yfree (Some blk).

(* [comment removed for export] *)
Definition ylex_realloc (lx : ylexer) : yprog ylexer :=
  b <- ybuf_clear (lx_buf lx) ;;
  YRet (mkLexer 0 0 LE_ok b (lx_bufblk lx) 0 0 (lx_allowComments lx) (lx_validateUTF8 lx)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition char_lookup_table : list Z :=
  [ 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2;
    2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2;
    0; 0; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1;
    4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 0; 0; 0; 0; 0; 0;
    0; 4; 4; 4; 4; 4; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 0; 0; 0;
    0; 4; 5; 4; 4; 4; 5; 0; 0; 0; 0; 0; 0; 0; 1; 0;
    0; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 ].

Definition clt (c : Z) : Z := znth char_lookup_table c.
(* [comment removed for export] *)
Definition is_vec (c : Z) : bool := Z.testbit (clt c) 0.
Definition is_ijc (c : Z) : bool := Z.testbit (clt c) 1.
Definition is_vhc (c : Z) : bool := Z.testbit (clt c) 2.

(* [comment removed for export] *)
Definition is_lex_ws (c : Z) : bool :=
  (c =? c_tab) || (c =? c_lf) || (c =? c_vt) || (c =? c_ff) || (c =? c_cr) || (c =? c_sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive u8res : Type := U8_ok (off : Z) | U8_eof (off : Z) | U8_error (off : Z).

(* [comment removed for export] *)
Definition is_utf8_cont (c : Z) : bool := Z.shiftr c 6 =? 2.

(* [comment removed for export] *)
Definition ylex_utf8_char (txt : list Z) (len off cur : Z) : u8res :=
  if cur <=? 127 then U8_ok off
  else if Z.shiftr cur 5 =? 6 then
    (* [comment removed for export] *)
    if len <=? off then U8_eof off else
    let c1 := znth txt off in let off := off + 1 in
    if is_utf8_cont c1 then U8_ok off else U8_error off
  else if Z.shiftr cur 4 =? 14 then
    (* [comment removed for export] *)
    if len <=? off then U8_eof off else
    let c1 := znth txt off in let off := off + 1 in
    if is_utf8_cont c1 then
      if len <=? off then U8_eof off else
      let c2 := znth txt off in let off := off + 1 in
      if is_utf8_cont c2 then U8_ok off else U8_error off
    else U8_error off
  else if Z.shiftr cur 3 =? 30 then
    (* [comment removed for export] *)
    if len <=? off then U8_eof off else
    let c1 := znth txt off in let off := off + 1 in
    if is_utf8_cont c1 then
      if len <=? off then U8_eof off else
      let c2 := znth txt off in let off := off + 1 in
      if is_utf8_cont c2 then
        if len <=? off then U8_eof off else
        let c3 := znth txt off in let off := off + 1 in
        if is_utf8_cont c3 then U8_ok off else U8_error off
      else U8_error off
    else U8_error off
  else U8_error off.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive hxres : Type := HX_ok (off : Z) | HX_eof (off : Z) | HX_bad (off : Z).

Fixpoint ylex_hex4 (n : nat) (txt : list Z) (len off : Z) : hxres :=
  match n with
  | O => HX_ok off
  | S n' =>
      if len <=? off then HX_eof off
      else if is_vhc (znth txt off) then ylex_hex4 n' txt len (off + 1)
      else HX_bad off   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint ylex_string_loop (fuel : nat) (validateUTF8 : Z) (txt : list Z) (len off : Z)
         (hasEsc : bool) : ytok * Z * option lex_error * bool :=
  match fuel with
  | O => (TK_eof, off, None, hasEsc)
  | S fuel' =>
      if len <=? off then (TK_eof, off, None, hasEsc)             (* [comment removed for export] *)
      else
        let c := znth txt off in
        let off1 := off + 1 in
        if c =? c_quote then (TK_string, off1, None, hasEsc)      (* [comment removed for export] *)
        else if c =? c_bslash then
          (* [comment removed for export] *)
          if len <=? off1 then (TK_eof, off1, None, true)
          else
            let c2 := znth txt off1 in
            let off2 := off1 + 1 in
            if c2 =? c_u then
              match ylex_hex4 4 txt len off2 with
              | HX_ok off3 => ylex_string_loop fuel' validateUTF8 txt len off3 true
              | HX_eof off3 => (TK_eof, off3, None, true)
              | HX_bad off3 => (TK_error, off3, Some LE_string_invalid_hex_char, true)
              end
            else if is_vec c2 then ylex_string_loop fuel' validateUTF8 txt len off2 true
            else (* [comment removed for export] *) (TK_error, off1, Some LE_string_invalid_escaped_char, true)
        else if is_ijc c then (* [comment removed for export] *) (TK_error, off, Some LE_string_invalid_json_char, hasEsc)
        else if negb (validateUTF8 =? 0) then
          match ylex_utf8_char txt len off1 c with
          | U8_ok off' => ylex_string_loop fuel' validateUTF8 txt len off' hasEsc
          | U8_eof off' => (TK_eof, off', None, hasEsc)
          | U8_error off' => (TK_error, off', Some LE_string_invalid_utf8, hasEsc)
          end
        else ylex_string_loop fuel' validateUTF8 txt len off1 hasEsc
  end.

Definition lex_fuel (len off : Z) : nat := S (Z.to_nat (len - off)).

Definition ylex_string (validateUTF8 : Z) (txt : list Z) (len off : Z)
  : ytok * Z * option lex_error :=
  let '(tok, off', err, hasEsc) := ylex_string_loop (lex_fuel len off) validateUTF8 txt len off false in
  let tok' := match tok with
              | TK_string => if hasEsc then TK_string_esc else TK_string
              | t => t
              end in
  (tok', off', err).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rdres : Type := RD_eof | RD_char (c : Z) (off : Z).   (* [comment removed for export] *)

Definition read1 (txt : list Z) (len off : Z) : rdres :=
  if len <=? off then RD_eof else RD_char (znth txt off) (off + 1).

(* [comment removed for export] *)
Fixpoint read_past_digits (fuel : nat) (txt : list Z) (len off : Z) : rdres :=
  match fuel with
  | O => RD_eof
  | S fuel' =>
      match read1 txt len off with
      | RD_eof => RD_eof
      | RD_char c off' => if is_digit c then read_past_digits fuel' txt len off' else RD_char c off'
      end
  end.

(* [comment removed for export] *)
Definition ylex_number (txt : list Z) (len off : Z) : ytok * Z * option lex_error :=
  match read1 txt len off with
  | RD_eof => (TK_eof, off, None)
  | RD_char c off =>
    (* [comment removed for export] *)
    let r := if c =? c_minus then read1 txt len off else RD_char c off in
    match r with
    | RD_eof => (TK_eof, len, None)
    | RD_char c off =>
      (* [comment removed for export] *)
      let r := if c =? c_0 then Some (read1 txt len off)
               else if (c_1 <=? c) && (c <=? c_9) then Some (read_past_digits (lex_fuel len off) txt len off)
               else None in
      match r with
      | None => (* [comment removed for export] *) (TK_error, off - 1, Some LE_missing_integer_after_minus)
      | Some RD_eof => (TK_eof, len, None)
      | Some (RD_char c off) =>
        (* [comment removed for export] *)
        let fr := if c =? c_dot then
                    match read1 txt len off with
                    | RD_eof => inr (TK_eof, len, @None lex_error)
                    | RD_char c off =>
                        if is_digit c then
                          match read_past_digits (lex_fuel len off) txt len off with
                          | RD_eof => inr (TK_eof, len, None)
                          | RD_char c off => inl (c, off, TK_double)
                          end
                        else (* [comment removed for export] *) inr (TK_error, off - 1, Some LE_missing_integer_after_decimal)
                    end
                  else inl (c, off, TK_integer) in
        match fr with
        | inr res => res
        | inl (c, off, tok) =>
          (* [comment removed for export] *)
          let ex := if (c =? c_e) || (c =? c_E) then
                      match read1 txt len off with
                      | RD_eof => inr (TK_eof, len, @None lex_error)
                      | RD_char c off =>
                          let r := if (c =? c_plus) || (c =? c_minus) then read1 txt len off else RD_char c off in
                          match r with
                          | RD_eof => inr (TK_eof, len, None)
                          | RD_char c off =>
                              if is_digit c then
                                match read_past_digits (lex_fuel len off) txt len off with
                                | RD_eof => inr (TK_eof, len, None)
                                | RD_char c off => inl (c, off, TK_double)
                                end
                              else (* [comment removed for export] *) inr (TK_error, off - 1, Some LE_missing_integer_after_exponent)
                          end
                      end
                    else inl (c, off, tok) in
          match ex with
          | inr res => res
          | inl (c, off, tok) => (* [comment removed for export] *) (tok, off - 1, None)
          end
        end
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint skip_line_comment (fuel : nat) (txt : list Z) (len off : Z) : rdres :=
  match fuel with
  | O => RD_eof
  | S fuel' =>
      match read1 txt len off with
      | RD_eof => RD_eof
      | RD_char c off' => if c =? c_lf then RD_char c off' else skip_line_comment fuel' txt len off'
      end
  end.

(* [comment removed for export] *)
Fixpoint skip_block_comment (fuel : nat) (txt : list Z) (len off : Z) : rdres :=
  match fuel with
  | O => RD_eof
  | S fuel' =>
      match read1 txt len off with
      | RD_eof => RD_eof
      | RD_char c off' =>
          if c =? c_star then
            match read1 txt len off' with
            | RD_eof => RD_eof
            | RD_char c2 off'' =>
                if c2 =? c_slash then RD_char c2 off''
                else (* [comment removed for export] *) skip_block_comment fuel' txt len off'
            end
          else skip_block_comment fuel' txt len off'
      end
  end.

Definition ylex_comment (txt : list Z) (len off : Z) : ytok * Z * option lex_error :=
  match read1 txt len off with
  | RD_eof => (TK_eof, off, None)
  | RD_char c off1 =>
      if c =? c_slash then
        match skip_line_comment (lex_fuel len off1) txt len off1 with
        | RD_eof => (TK_eof, len, None)
        | RD_char _ off2 => (TK_comment, off2, None)
        end
      else if c =? c_star then
        match skip_block_comment (lex_fuel len off1) txt len off1 with
        | RD_eof => (TK_eof, len, None)
        | RD_char _ off2 => (TK_comment, off2, None)
        end
      else (TK_error, off1, Some LE_invalid_char)   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive wres : Type := W_ok (off : Z) | W_eof (off : Z) | W_bad (off : Z).

Fixpoint ylex_want (want : list Z) (txt : list Z) (len off : Z) : wres :=
  match want with
  | [] => W_ok off
  | w :: rest =>
      if len <=? off then W_eof off
      else if znth txt off =? w then ylex_want rest txt len (off + 1)
      else W_bad off
  end.

Definition want_rue : list Z := [c_r; c_u; c_e].
Definition want_alse : list Z := [c_a; 108; 115; c_e].   (* [comment removed for export] *)
Definition want_ull : list Z := [c_u; 108; 108].          (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive outref : Type := OB_null | OB_text (i : Z) | OB_lexbuf (i : Z).

Definition outref_succ (r : outref) : outref :=
  match r with OB_null => OB_null | OB_text i => OB_text (i + 1) | OB_lexbuf i => OB_lexbuf (i + 1) end.

(* [comment removed for export] *)
Fixpoint ylex_loop (fuel : nat) (lx : ylexer) (txt : list Z) (len off start : Z)
  : yprog (ylexer * ytok * Z * Z) :=
  match fuel with
  | O => YAbort
  | S fuel' =>
      yassert (off <=? len) ;;;                                  (* [comment removed for export] *)
      if len <=? off then YRet (lx, TK_eof, off, start)
      else
        let c := znth txt off in
        let off1 := off + 1 in
        if c =? c_lbrace then YRet (lx, TK_left_bracket, off1, start)
        else if c =? c_rbrace then YRet (lx, TK_right_bracket, off1, start)
        else if c =? c_lbracket then YRet (lx, TK_left_brace, off1, start)
        else if c =? c_rbracket then YRet (lx, TK_right_brace, off1, start)
        else if c =? c_comma then YRet (lx, TK_comma, off1, start)
        else if c =? c_colon then YRet (lx, TK_colon, off1, start)
        else if is_lex_ws c then ylex_loop fuel' lx txt len off1 (start + 1)
        else if c =? c_t then
          match ylex_want want_rue txt len off1 with
          | W_ok o => YRet (lx, TK_bool, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_f then
          match ylex_want want_alse txt len off1 with
          | W_ok o => YRet (lx, TK_bool, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_n then
          match ylex_want want_ull txt len off1 with
          | W_ok o => YRet (lx, TK_null, o, start)
          | W_eof o => YRet (lx, TK_eof, o, start)
          | W_bad o => YRet (lx_set_error lx LE_invalid_string, TK_error, o, start)
          end
        else if c =? c_quote then
          let '(tok, o, err) := ylex_string (lx_validateUTF8 lx) txt len off1 in
          YRet (lx_set_error_opt lx err, tok, o, start)
        else if (c =? c_minus) || is_digit c then
          (* [comment removed for export] *)
          let '(tok, o, err) := ylex_number txt len off in
          YRet (lx_set_error_opt lx err, tok, o, start)
        else if c =? c_slash then
          if lx_allowComments lx =? 0 then
            (* [comment removed for export] *)
            YRet (lx_set_error lx LE_unallowed_comment, TK_error, off, start)
          else
            let '(tok, o, err) := ylex_comment txt len off1 in
            match tok with
            | TK_comment =>
                (* [comment removed for export] *)
                b' <- ybuf_clear (lx_buf lx) ;;
                ylex_loop fuel' (lx_set_buf lx b' (lx_bufOff lx) 0) txt len o o
            | _ => YRet (lx_set_error_opt lx err, tok, o, start)
            end
        else YRet (lx_set_error lx LE_invalid_char, TK_error, off1, start)
  end.

Definition is_string_tok (t : ytok) : bool :=
  match t with TK_string | TK_string_esc => true | _ => false end.

(* [comment removed for export] *)
Definition ylex_finish (lx : ylexer) (txt : list Z) (tok : ytok) (off start : Z)
  : yprog (ylexer * ytok * Z * outref * Z) :=
  if tok_eqb tok TK_eof || negb (lx_bufInUse lx =? 0) then
    b1 <- (if lx_bufInUse lx =? 0 then ybuf_clear (lx_buf lx) else YRet (lx_buf lx)) ;;
    b2 <- ybuf_append b1 (zslice txt start (off - start)) ;;
    let lx1 := lx_set_buf lx b2 0 1 in
    if ybuf_err b2 then YRet (lx_set_error lx1 LE_alloc_failed, TK_error, off, OB_null, 0)
    else if negb (tok_eqb tok TK_eof) then
      (* [comment removed for export] *)
      n <- ybuf_len_chk b2 ;;
      let lx2 := lx_set_buf lx b2 0 0 in
      if is_string_tok tok
      then (yassert (2 <=? n) ;;; YRet (lx2, tok, off, OB_lexbuf 1, n - 2))
      else YRet (lx2, tok, off, OB_lexbuf 0, n)
    else YRet (lx1, tok, off, OB_null, 0)
  else if negb (tok_eqb tok TK_error) then
    let n := off - start in
    if is_string_tok tok
    then (yassert (2 <=? n) ;;; YRet (lx, tok, off, OB_text (start + 1), n - 2))
    else YRet (lx, tok, off, OB_text start, n)
  else YRet (lx, tok, off, OB_null, 0).

(* [comment removed for export] *)
Definition ylex_lex (lx : ylexer) (txt : list Z) (len off : Z)
  : yprog (ylexer * ytok * Z * outref * Z) :=
  r <- ylex_loop (lex_fuel len off) lx txt len off off ;;
  let '(lx1, tok, off1, start) := r in
  ylex_finish lx1 txt tok off1 start.
