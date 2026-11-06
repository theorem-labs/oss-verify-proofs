(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope yprog_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ystate : Type :=
| ST_start | ST_parse_complete | ST_parse_error | ST_lexical_error
| ST_map_start | ST_map_sep | ST_map_need_val | ST_map_got_val | ST_map_need_key
| ST_array_start | ST_array_got_val | ST_array_need_val.

Definition state_code (s : ystate) : Z :=
  match s with
  | ST_start => 0 | ST_parse_complete => 1 | ST_parse_error => 2 | ST_lexical_error => 3
  | ST_map_start => 4 | ST_map_sep => 5 | ST_map_need_val => 6 | ST_map_got_val => 7
  | ST_map_need_key => 8 | ST_array_start => 9 | ST_array_got_val => 10 | ST_array_need_val => 11
  end.

Definition state_eqb (a b : ystate) : bool := state_code a =? state_code b.

Inductive ystatus : Type :=
| YS_ok | YS_client_canceled | YS_insufficient_data | YS_error | YS_alloc_failed.

Definition status_code (s : ystatus) : Z :=
  match s with
  | YS_ok => 0 | YS_client_canceled => 1 | YS_insufficient_data => 2 | YS_error => 3 | YS_alloc_failed => 4
  end.

(* [comment removed for export] *)
Inductive perr : Type :=
| PE_client_cancelled          (* [comment removed for export] *)
| PE_alloc_failed              (* [comment removed for export] *)
| PE_unallowed_token           (* [comment removed for export] *)
| PE_invalid_token_internal    (* [comment removed for export] *)
| PE_invalid_object_key        (* [comment removed for export] *)
| PE_expect_colon              (* [comment removed for export] *)
| PE_map_expect                (* [comment removed for export] *)
| PE_array_expect.             (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record yhandle : Type := mkHandle {
  h_blk : yptr;
  h_lexer_blk : yptr;
  h_lexer : ylexer;
  h_parseError : option perr;
  h_bytesConsumed : Z;
  h_decbuf_blk : yptr;
  h_decbuf : ybuf;
  h_stack : list ystate;        (* [comment removed for export] *)
  h_stack_size : Z;
  h_stack_blk : option yptr
}.

Definition SIZEOF_YAJL_HANDLE_T : Z := 104.
Definition YAJL_BS_INC : Z := 128.
Definition UINT_MAX : Z := 4294967295.

Definition h_set_lexer (h : yhandle) (lx : ylexer) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) lx (h_parseError h) (h_bytesConsumed h)
           (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h) (h_stack_blk h).
Definition h_set_lex_off (h : yhandle) (lx : ylexer) (off : Z) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) lx (h_parseError h) off
           (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h) (h_stack_blk h).
Definition h_set_off (h : yhandle) (off : Z) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) off
           (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h) (h_stack_blk h).
Definition h_set_perr (h : yhandle) (e : perr) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (Some e) (h_bytesConsumed h)
           (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h) (h_stack_blk h).
Definition h_set_decbuf (h : yhandle) (b : ybuf) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) (h_bytesConsumed h)
           (h_decbuf_blk h) b (h_stack h) (h_stack_size h) (h_stack_blk h).
Definition h_set_stack (h : yhandle) (st : list ystate) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) (h_bytesConsumed h)
           (h_decbuf_blk h) (h_decbuf h) st (h_stack_size h) (h_stack_blk h).
Definition h_set_stack3 (h : yhandle) (st : list ystate) (size : Z) (blk : option yptr) : yhandle :=
  mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) (h_bytesConsumed h)
           (h_decbuf_blk h) (h_decbuf h) st size blk.

Definition h_used (h : yhandle) : Z := zlength (h_stack h).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ybs_current (h : yhandle) : yprog ystate :=
  match h_stack h with
  | s :: _ => YRet s
  | [] => YAbort
  end.

(* [comment removed for export] *)
Definition ybs_set (h : yhandle) (s : ystate) : yprog yhandle :=
  match h_stack h with
  | _ :: rest => if h_used h <=? h_stack_size h then YRet (h_set_stack h (s :: rest)) else YAbort
  | [] => YAbort
  end.

(* [comment removed for export] *)
Definition ybs_pop (h : yhandle) : yprog yhandle :=
  match h_stack h with
  | _ :: rest => YRet (h_set_stack h rest)
  | [] => YAbort
  end.

(* [comment removed for export] *)
Definition ybs_push (h : yhandle) (s : ystate) : yprog (bool * yhandle) :=
  if h_stack_size h - h_used h =? 0 then
    if UINT_MAX - YAJL_BS_INC <? h_stack_size h then YRet (false, h)
    else
      let size' := h_stack_size h + YAJL_BS_INC in
      r <- yrealloc (h_stack_blk h) size' ;;
      match r with
      | None => YRet (false, h_set_stack3 h (h_stack h) size' None)
      | Some p => YRet (true, h_set_stack3 h (s :: h_stack h) size' (Some p))
      end
  else YRet (true, h_set_stack h (s :: h_stack h)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record yctx : Type := mkCtx { cx_arrayLevel : Z; cx_objectLevel : Z }.

(* [comment removed for export] *)
Record ycallbacks : Type := mkCallbacks {
  cb_null : yctx -> yprog yctx;
  cb_boolean : yctx -> Z -> yprog yctx;
  cb_number : yctx -> list Z -> Z -> yprog yctx;
  cb_string : yctx -> list Z -> Z -> yprog yctx;
  cb_start_map : yctx -> yprog yctx;
  cb_map_key : yctx -> list Z -> Z -> yprog yctx;
  cb_end_map : yctx -> yprog yctx;
  cb_start_array : yctx -> yprog yctx;
  cb_end_array : yctx -> yprog yctx
}.

(* [comment removed for export] *)
Definition jf_callbacks : ycallbacks :=
  mkCallbacks
    (fun cx => YRet cx)                                                    (* [comment removed for export] *)
    (fun cx _ => YRet cx)                                                  (* [comment removed for export] *)
    (fun cx _ l => yassert (0 <? l) ;;; YRet cx)                           (* [comment removed for export] *)
    (fun cx _ _ => YRet cx)                                                (* [comment removed for export] *)
    (fun cx => YRet (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)))   (* [comment removed for export] *)
    (fun cx _ _ => yassert (0 <? cx_objectLevel cx) ;;; YRet cx)          (* [comment removed for export] *)
    (fun cx => yassert (0 <? cx_objectLevel cx) ;;;                        (* [comment removed for export] *)
               YRet (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx - 1)))
    (fun cx => YRet (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)))   (* [comment removed for export] *)
    (fun cx => yassert (0 <? cx_arrayLevel cx) ;;;                         (* [comment removed for export] *)
               YRet (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx))).

(* [comment removed for export] *)
Definition out_bytes (txt : list Z) (lx : ylexer) (r : outref) (n : Z) : list Z :=
  match r with
  | OB_null => []
  | OB_text i => zslice txt i n
  | OB_lexbuf i => zslice (yb_bytes (lx_buf lx)) i n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive step_res : Type :=
| SR_done (st : ystatus) (h : yhandle) (cx : yctx)
| SR_again (h : yhandle) (cx : yctx).

(* [comment removed for export] *)
Definition yparse_error (h : yhandle) (cx : yctx) (e : perr) : yprog step_res :=
  h1 <- ybs_set h ST_parse_error ;;
  YRet (SR_again (h_set_perr h1 e) cx).

(* [comment removed for export] *)
Definition ybuf_chk_fail (h : yhandle) (cx : yctx) : yprog step_res :=
  h1 <- ybs_set h ST_parse_error ;;
  YRet (SR_done YS_alloc_failed (h_set_perr h1 PE_alloc_failed) cx).

(* [comment removed for export] *)
Definition ygot_value (h : yhandle) (cx : yctx) (push : option ystate) : yprog step_res :=
  s <- ybs_current h ;;
  h1 <- match s with
        | ST_start => lx <- ylex_realloc (h_lexer h) ;; YRet (h_set_lexer h lx)
        | ST_map_need_val => ybs_set h ST_map_got_val
        | _ => ybs_set h ST_array_got_val
        end ;;
  match push with
  | None => YRet (SR_again h1 cx)
  | Some st =>
      r <- ybs_push h1 st ;;
      let '(ok, h2) := r in
      if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx)
  end.

(* [comment removed for export] *)
Definition ydecode_tok (h : yhandle) (bytes : list Z) (n : Z) : yprog yhandle :=
  db <- ybuf_clear (h_decbuf h) ;;
  db1 <- ystring_decode db bytes n ;;
  YRet (h_set_decbuf h db1).

Section Parser.
Variable cb : ycallbacks.
Variable txt : list Z.      (* [comment removed for export] *)
Variable len : Z.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition yparse_step (h : yhandle) (cx : yctx) : yprog step_res :=
  cur <- ybs_current h ;;
  match cur with
  | ST_parse_complete => YRet (SR_done YS_ok h cx)
  | ST_lexical_error | ST_parse_error => YRet (SR_done YS_error h cx)

  | ST_start | ST_map_need_val | ST_array_need_val | ST_array_start =>
      r <- ylex_lex (h_lexer h) txt len (h_bytesConsumed h) ;;
      let '(lx, tok, off, ob, n) := r in
      let h := h_set_lex_off h lx off in
      let bytes := out_bytes txt lx ob n in
      match tok with
      | TK_eof => YRet (SR_done YS_insufficient_data h cx)
      | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
      | TK_string => cx1 <- cb_string cb cx bytes n ;; ygot_value h cx1 None
      | TK_string_esc =>
          h1 <- ydecode_tok h bytes n ;;
          if ybuf_err (h_decbuf h1) then ybuf_chk_fail h1 cx
          else
            _d <- ybuf_data_chk (h_decbuf h1) ;;
            m <- ybuf_len_chk (h_decbuf h1) ;;
            cx1 <- cb_string cb cx (yb_bytes (h_decbuf h1)) m ;;
            ygot_value h1 cx1 None
      | TK_bool => cx1 <- cb_boolean cb cx (if znth bytes 0 =? c_t then 1 else 0) ;; ygot_value h cx1 None
      | TK_null => cx1 <- cb_null cb cx ;; ygot_value h cx1 None
      | TK_left_bracket => cx1 <- cb_start_map cb cx ;; ygot_value h cx1 (Some ST_map_start)
      | TK_left_brace => cx1 <- cb_start_array cb cx ;; ygot_value h cx1 (Some ST_array_start)
      | TK_integer | TK_double => cx1 <- cb_number cb cx bytes n ;; ygot_value h cx1 None
      | TK_right_brace =>
          cur1 <- ybs_current h ;;
          if state_eqb cur1 ST_array_start then
            cx1 <- cb_end_array cb cx ;;
            h1 <- ybs_pop h ;;
            YRet (SR_again h1 cx1)
          else yparse_error h cx PE_unallowed_token          (* [comment removed for export] *)
      | TK_colon | TK_comma | TK_right_bracket => yparse_error h cx PE_unallowed_token
      | TK_comment => yparse_error h cx PE_invalid_token_internal
      end

  | ST_map_start | ST_map_need_key =>
      r <- ylex_lex (h_lexer h) txt len (h_bytesConsumed h) ;;
      let '(lx, tok, off, ob, n) := r in
      let h := h_set_lex_off h lx off in
      let bytes := out_bytes txt lx ob n in
      let on_key := fun (h : yhandle) (kbytes : list Z) (kn : Z) =>
                      cx1 <- cb_map_key cb cx kbytes kn ;;
                      h1 <- ybs_set h ST_map_sep ;;
                      YRet (SR_again h1 cx1) in
      match tok with
      | TK_eof => YRet (SR_done YS_insufficient_data h cx)
      | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
      | TK_string_esc =>
          h1 <- ydecode_tok h bytes n ;;
          if ybuf_err (h_decbuf h1) then ybuf_chk_fail h1 cx
          else
            _d <- ybuf_data_chk (h_decbuf h1) ;;
            m <- ybuf_len_chk (h_decbuf h1) ;;
            on_key h1 (yb_bytes (h_decbuf h1)) m
      | TK_string => on_key h bytes n
      | TK_right_bracket =>
          cur1 <- ybs_current h ;;
          if state_eqb cur1 ST_map_start then
            cx1 <- cb_end_map cb cx ;;
            h1 <- ybs_pop h ;;
            YRet (SR_again h1 cx1)
          else yparse_error h cx PE_invalid_object_key
      | _ => yparse_error h cx PE_invalid_object_key
      end

  | ST_map_sep =>
      r <- ylex_lex (h_lexer h) txt len (h_bytesConsumed h) ;;
      let '(lx, tok, off, ob, n) := r in
      let h := h_set_lex_off h lx off in
      match tok with
      | TK_colon => h1 <- ybs_set h ST_map_need_val ;; YRet (SR_again h1 cx)
      | TK_eof => YRet (SR_done YS_insufficient_data h cx)
      | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
      | _ => yparse_error h cx PE_expect_colon
      end

  | ST_map_got_val =>
      r <- ylex_lex (h_lexer h) txt len (h_bytesConsumed h) ;;
      let '(lx, tok, off, ob, n) := r in
      let h := h_set_lex_off h lx off in
      match tok with
      | TK_right_bracket =>
          cx1 <- cb_end_map cb cx ;;
          h1 <- ybs_pop h ;;
          YRet (SR_again h1 cx1)
      | TK_comma => h1 <- ybs_set h ST_map_need_key ;; YRet (SR_again h1 cx)
      | TK_eof => YRet (SR_done YS_insufficient_data h cx)
      | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
      | _ =>
          (* [comment removed for export] *)
          h1 <- ybs_set h ST_parse_error ;;
          let h2 := h_set_perr h1 PE_map_expect in
          let off' := if n <=? off then off - n else 0 in
          YRet (SR_again (h_set_off h2 off') cx)
      end

  | ST_array_got_val =>
      r <- ylex_lex (h_lexer h) txt len (h_bytesConsumed h) ;;
      let '(lx, tok, off, ob, n) := r in
      let h := h_set_lex_off h lx off in
      match tok with
      | TK_right_brace =>
          cx1 <- cb_end_array cb cx ;;
          h1 <- ybs_pop h ;;
          YRet (SR_again h1 cx1)
      | TK_comma => h1 <- ybs_set h ST_array_need_val ;; YRet (SR_again h1 cx)
      | TK_eof => YRet (SR_done YS_insufficient_data h cx)
      | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
      | _ => yparse_error h cx PE_array_expect
      end
  end.

(* [comment removed for export] *)
Fixpoint yparse_loop (fuel : nat) (h : yhandle) (cx : yctx) : yprog (ystatus * yhandle * yctx) :=
  match fuel with
  | O => YAbort
  | S fuel' =>
      r <- yparse_step h cx ;;
      match r with
      | SR_done st h1 cx1 => YRet (st, h1, cx1)
      | SR_again h1 cx1 => yparse_loop fuel' h1 cx1
      end
  end.

Definition parse_fuel : nat := S (S (Z.to_nat len)).

(* [comment removed for export] *)
Definition ydo_parse (h : yhandle) (cx : yctx) : yprog (ystatus * yhandle * yctx) :=
  yparse_loop parse_fuel (h_set_off h 0) cx.

End Parser.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yajl_alloc (allowComments validateUTF8 : Z) : yprog (option yhandle) :=
  r <- ymalloc SIZEOF_YAJL_HANDLE_T ;;
  match r with
  | None => YRet None
  | Some hb =>
      rl <- ylex_alloc allowComments validateUTF8 ;;
      match rl with
      | None => yfree (Some hb) ;;; YRet None
      | Some (lb, lx) =>
          rd <- ybuf_alloc ;;
          match rd with
          | None => ylex_free lb lx ;;; yfree (Some hb) ;;; YRet None
          | Some db =>
              let h0 := mkHandle hb lb lx None 0 db ybuf_zero [] 0 None in
              rp <- ybs_push h0 ST_start ;;
              let '(ok, h1) := rp in
              if ok then YRet (Some h1)
              else ybuf_free db ybuf_zero ;;; ylex_free lb lx ;;; yfree (Some hb) ;;; YRet None
          end
      end
  end.

(* [comment removed for export] *)
Definition yajl_free (h : yhandle) : yprog unit :=
  match h_stack_blk h with
  | Some p => yfree (Some p)
  | None => YRet tt
  end ;;;
  ybuf_free (h_decbuf_blk h) (h_decbuf h) ;;;
  ylex_free (h_lexer_blk h) (h_lexer h) ;;;
  yfree (Some (h_blk h)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yfuzz_one (cb : ycallbacks) (post : ystatus -> yhandle -> yctx -> yprog unit)
           (data : list Z) (size : Z) : yprog Z :=
  r <- yajl_alloc 1 1 ;;
  match r with
  | None => YRet 0
  | Some h =>
      pr <- ydo_parse cb data size h (mkCtx 0 0) ;;
      let '(st, h1, cx1) := pr in
      post st h1 cx1 ;;;
      yajl_free h1 ;;;
      YRet 0
  end.

Definition yLLVMFuzzerTestOneInput (data : list Z) (size : Z) : yprog Z :=
  yfuzz_one jf_callbacks (fun _ _ _ => YRet tt) data size.

(* [comment removed for export] *)
Fixpoint zdigits (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc else zdigits f (n / 10) (48 + n mod 10 :: acc)
  end.
Definition zdecimal (n : Z) : list Z :=
  if n <? 0 then 45 :: zdigits 20 (- n) [] else zdigits 20 n [].

(* [comment removed for export] *)
Section TargetRun.
(* [comment removed for export] *)
Variable one : list Z -> Z -> yprog Z.

Fixpoint yrun_calls (n : nat) (payload : list Z) (payload_len : Z) (rc : Z) : yprog Z :=
  match n with
  | O => YRet rc
  | S n' =>
      rc1 <- one payload payload_len ;;
      yemit (zdecimal rc1 ++ [c_lf]) ;;;
      yrun_calls n' payload payload_len rc1
  end.

Definition ytarget_run_with (config : list Z) (config_len : Z) (payload : list Z) (payload_len : Z)
  : yprog Z :=
  let c := if config_len =? 0 then 0 else znth config 0 in
  let calls := 1 + Z.land c 3 in
  owned <- (if payload_len =? 0 then YRet (Some None)
            else r <- ymalloc payload_len ;;
                 match r with
                 | None => YRet None
                 | Some p => YRet (Some (Some p))
                 end) ;;
  match owned with
  | None => YRet 2
  | Some own =>
      rc <- yrun_calls (Z.to_nat calls) payload payload_len 0 ;;
      yfree own ;;;
      YRet (if rc =? 0 then 0 else 1)
  end.
End TargetRun.

Definition ytarget_run : list Z -> Z -> list Z -> Z -> yprog Z :=
  ytarget_run_with yLLVMFuzzerTestOneInput.
