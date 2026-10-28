(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMR.
Import PML.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ST_N := 18. Definition ST_NU := 19. Definition ST_NUL := 20. Definition ST_T := 21. Definition ST_TR := 22. Definition ST_TRU := 23.
Definition ST_F := 24. Definition ST_FA := 25. Definition ST_FAL := 26. Definition ST_FALS := 27.
(* [comment removed for export] *)
Definition SS_TEXT := 0. Definition SS_ESC := 1. Definition SS_U1 := 2. Definition SS_U2 := 3. Definition SS_U3 := 4. Definition SS_U4 := 5.
Definition SS_SP1 := 6. Definition SS_SP2 := 7. Definition SS_U5 := 8. Definition SS_U6 := 9. Definition SS_U7 := 10. Definition SS_U8 := 11.
(* [comment removed for export] *)
Definition NS_MINUS := 0. Definition NS_ZERO := 1. Definition NS_INTEGER := 2. Definition NS_FRAC1 := 3. Definition NS_FRAC2 := 4.
Definition NS_EXP1 := 5. Definition NS_EXP2 := 6. Definition NS_EXP3 := 7.
(* [comment removed for export] *)
Definition E_EOF := 1. Definition E_SOURCE := 2. Definition E_SYNTAX := 3. Definition E_EXTRA_CHAR := 4. Definition E_DEPTH := 5.
Definition E_SQUOTE := 6. Definition E_CHAR_IN_STRING := 7. Definition E_EXTRA_COMMA := 8. Definition E_EXPECTED_KEY := 9.
Definition E_EXPECTED_VALUE := 10. Definition E_INVALID_VALUE := 11. Definition E_EXPECTED_COLON := 12. Definition E_ILLEGAL_CTL := 13.
Definition E_ILLEGAL_ESC := 14. Definition E_SURR_PAIR := 15. Definition E_INVALID_UESC := 17. Definition E_LEADING_ZERO := 18.
Definition E_INVALID_NUMBER := 19. Definition E_COMMA_OR_RBRACE := 20. Definition E_COMMA_OR_RBRACKET := 21. Definition E_UNEXP_RBRACKET := 22.
Definition E_UNEXP_RBRACE := 23. Definition E_ILLEGAL_COMMENT := 24. Definition E_BAD_CONT := 25. Definition E_OVERLONG := 26.
Definition E_ILLEGAL_CODEPOINT := 27. Definition E_ILLEGAL_SURR := 28. Definition E_UNPAIRED_SURR := 29. Definition E_ILLEGAL_UNICODE := 30.
Definition E_UNEXP_CHAR := 31.
(* [comment removed for export] *)
Definition E_STUCK := 99. Definition E_FUEL := 98.
Definition CHUNK : Z := 16384.

(* [comment removed for export] *)
Definition is_ctl (b : Z) : bool := ((0 <=? b) && (b <=? 8)) || (b =? 11) || (b =? 12) || ((14 <=? b) && (b <=? 31)).   (* [comment removed for export] *)
Definition is_ws (b : Z) : bool := (b =? 32) || (b =? 9) || (b =? 10) || (b =? 13).
Definition is_digit (b : Z) : bool := (48 <=? b) && (b <=? 57).
Definition is_nzdigit (b : Z) : bool := (49 <=? b) && (b <=? 57).
Definition is_exp (b : Z) : bool := (b =? 101) || (b =? 69).
(* [comment removed for export] *)
Definition hexval (b : Z) : option Z :=
  if is_digit b then Some (b - 48) else if (97 <=? b) && (b <=? 102) then Some (b - 87) else if (65 <=? b) && (b <=? 70) then Some (b - 55) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition trailing (b : Z) : Z := if b <? 192 then 0 else if b <? 224 then 1 else if b <? 240 then 2 else if b <? 248 then 3 else if b <? 252 then 4 else 5.
Definition is_cont (b : Z) : bool := (128 <=? b) && (b <=? 191).
(* [comment removed for export] *)
Definition legal (seq : list Z) : Z :=
  match seq with
  | [] => 0
  | lead :: rest =>
      if 4 <=? Z.of_nat (length rest) then 1
      else if negb (forallb is_cont rest) then 2
      else
        let chk1 := match rest with
                    | [] => 0
                    | b1 :: _ => if lead =? 224 then (if b1 <? 160 then 6 else 0)
                                 else if lead =? 237 then (if 159 <? b1 then 6 else 0)
                                 else if lead =? 240 then (if b1 <? 144 then 6 else 0)
                                 else if lead =? 244 then (if 143 <? b1 then 6 else 0)
                                 else if b1 <? 128 then 6 else 0
                    end in
        if negb (chk1 =? 0) then chk1
        else if (128 <=? lead) && (lead <=? 193) then 6
        else if 244 <? lead then 6 else 0
  end.
(* [comment removed for export] *)
Record u8v : Type := U8 { u_err : Z; u_pend : list Z; u_need : Z }.
Definition u8_init : u8v := U8 0 [] 0.
Definition u8_feed (v : u8v) (b : Z) : u8v :=
  if negb (u_err v =? 0) then v
  else match u_pend v with
       | [] => let t := trailing b in if t =? 0 then U8 (legal [b]) [] 0 else U8 0 [b] (t + 1)
       | p => let p' := p ++ [b] in if Z.of_nat (length p') =? u_need v then U8 (legal p') [] 0 else U8 0 p' (u_need v)
       end.
Fixpoint u8_feeds (v : u8v) (bs : list Z) : u8v := match bs with [] => v | b :: r => u8_feeds (u8_feed v b) r end.
(* [comment removed for export] *)
Definition u8_finish (v : u8v) : Z := if negb (u_err v =? 0) then u_err v else match u_pend v with [] => 0 | _ => 5 end.
(* [comment removed for export] *)
Definition b256 (bs : list Z) : list Z := map (fun b => b mod 256) bs.
Definition validate (txt : list Z) : Z := u8_finish (u8_feeds u8_init (b256 txt)).
(* [comment removed for export] *)
Definition conv_errc (u : Z) : Z :=
  if u =? 1 then E_OVERLONG else if u =? 2 then E_BAD_CONT else if u =? 3 then E_UNPAIRED_SURR else if u =? 4 then E_ILLEGAL_SURR else E_ILLEGAL_CODEPOINT.
(* [comment removed for export] *)
Definition is_high_surr (cp : Z) : bool := (55296 <=? cp) && (cp <=? 56319).
Definition is_surr (cp : Z) : bool := (55296 <=? cp) && (cp <=? 57343).
Definition utf8_of (cp : Z) : list Z :=
  if is_surr cp then []
  else if cp <? 128 then [cp]
  else if cp <? 2048 then [192 + Z.shiftr cp 6; 128 + Z.land cp 63]
  else if cp <? 65536 then [224 + Z.shiftr cp 12; 128 + Z.land (Z.shiftr cp 6) 63; 128 + Z.land cp 63]
  else if cp <=? 1114111 then [240 + Z.shiftr cp 18; 128 + Z.land (Z.shiftr cp 12) 63; 128 + Z.land (Z.shiftr cp 6) 63; 128 + Z.land cp 63]
  else [239; 191; 189].
(* [comment removed for export] *)
Definition pair_cp (cp cp2 : Z) : Z := 65536 + Z.shiftl (Z.land cp 1023) 10 + Z.land cp2 1023.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record ctrl : Type := CT {
  c_st : Z; c_sst : Z; c_nst : Z; c_more : bool; c_done : bool; c_level : Z;
  c_stack : list Z;      (* [comment removed for export] *)
  c_cp : Z; c_cp2 : Z;   (* [comment removed for export] *)
  c_dlen : Z;            (* [comment removed for export] *)
  c_u8 : u8v }.          (* [comment removed for export] *)
Definition set_st (c : ctrl) (x : Z) := CT x (c_sst c) (c_nst c) (c_more c) (c_done c) (c_level c) (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_sst (c : ctrl) (x : Z) := CT (c_st c) x (c_nst c) (c_more c) (c_done c) (c_level c) (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_nst (c : ctrl) (x : Z) := CT (c_st c) (c_sst c) x (c_more c) (c_done c) (c_level c) (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_more (c : ctrl) (x : bool) := CT (c_st c) (c_sst c) (c_nst c) x (c_done c) (c_level c) (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_done (c : ctrl) (x : bool) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) x (c_level c) (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_level (c : ctrl) (x : Z) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) (c_done c) x (c_stack c) (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_stack (c : ctrl) (x : list Z) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) (c_done c) (c_level c) x (c_cp c) (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_cp (c : ctrl) (x : Z) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) (c_done c) (c_level c) (c_stack c) x (c_cp2 c) (c_dlen c) (c_u8 c).
Definition set_cp2 (c : ctrl) (x : Z) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) (c_done c) (c_level c) (c_stack c) (c_cp c) x (c_dlen c) (c_u8 c).
Definition set_tok (c : ctrl) (d : Z) (v : u8v) := CT (c_st c) (c_sst c) (c_nst c) (c_more c) (c_done c) (c_level c) (c_stack c) (c_cp c) (c_cp2 c) d v.
(* [comment removed for export] *)
Definition push (c : ctrl) (s : Z) : ctrl := set_stack c (c_stack c ++ [s]).
Definition top (c : ctrl) : Z := last (c_stack c) (-1).
Definition pop (c : ctrl) : ctrl := set_stack c (removelast (c_stack c)).
(* [comment removed for export] *)
Definition tok1 (c : ctrl) (b : Z) : ctrl := set_tok c (c_dlen c + 1) (u8_feed (c_u8 c) b).
Definition tokn (c : ctrl) (bs : list Z) : ctrl := set_tok c (c_dlen c + Z.of_nat (length bs)) (u8_feeds (c_u8 c) bs).
Definition tok_clear (c : ctrl) : ctrl := set_tok c 0 u8_init.
(* [comment removed for export] *)
Definition ctrl0 : ctrl := CT ST_START SS_TEXT NS_MINUS true false 0 [ST_ROOT] 0 0 0 u8_init.
(* [comment removed for export] *)
Definition st_after (c : ctrl) : Z := if c_level c =? 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition evk := PMW.evk.
Record res : Type := RES { q_c : ctrl; q_w : list Z; q_evs : list evk; q_al : Z; q_code : Z }.
Definition ret (c : ctrl) (w : list Z) : res := RES c w [] 0 0.
Definition err (c : ctrl) (w : list Z) (code : Z) : res := RES (set_more c false) w [] 0 code.
(* [comment removed for export] *)
Definition AL_LIT : Z := 5.
Definition al_num (dlen : Z) : Z := 28 + dlen.
Definition al_str (dlen : Z) : Z := 6 * dlen.
(* [comment removed for export] *)
Definition bind (r : res) (k : ctrl -> list Z -> res) : res :=
  if negb (q_code r =? 0) then r
  else let r2 := k (q_c r) (q_w r) in RES (q_c r2) (q_w r2) (q_evs r ++ q_evs r2) (q_al r + q_al r2) (q_code r2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition after_value (c : ctrl) (w : list Z) : res :=
  let p := top c in
  if (p =? ST_ARRAY) || (p =? ST_OBJECT) then ret (set_st c ST_EXPECT_COMMA_OR_END) w
  else if p =? ST_ROOT then ret (set_st c ST_ACCEPT) w
  else err c w E_SYNTAX.
Definition begin_member (c : ctrl) (w : list Z) : res :=
  let p := top c in
  if p =? ST_OBJECT then ret (set_st c ST_EXPECT_MEMBER_NAME) w
  else if p =? ST_ARRAY then ret (set_st c ST_EXPECT_VALUE) w
  else if p =? ST_ROOT then ret c w
  else err c w E_SYNTAX.
(* [comment removed for export] *)
Definition end_number (c : ctrl) (w : list Z) : res :=
  bind (RES (set_more c true) w [PMW.EkNum] (al_num (c_dlen c)) 0) after_value.
(* [comment removed for export] *)
Definition begin_container (arr : bool) (c : ctrl) (w : list Z) : res :=
  let c1 := set_level c (c_level c + 1) in
  if 1024 <? c_level c1 then err c1 w E_DEPTH
  else RES (set_more (set_st (push c1 (if arr then ST_ARRAY else ST_OBJECT)) (if arr then ST_EXPECT_VALUE_OR_END else ST_EXPECT_MEMBER_NAME_OR_END)) true)
           w [PMW.EkBegin arr] 0 0.
(* [comment removed for export] *)
Definition end_container (arr : bool) (c : ctrl) (w : list Z) : res :=
  if c_level c <? 1 then err c w (if arr then E_UNEXP_RBRACKET else E_UNEXP_RBRACE)
  else let p := top c in let c1 := set_st (pop c) p in
    if p =? (if arr then ST_ARRAY else ST_OBJECT) then
      let c2 := set_level (set_more c1 true) (c_level c1 - 1) in
      RES (set_st c2 (st_after c2)) w [PMW.EkEnd] 0 0
    else if p =? (if arr then ST_OBJECT else ST_ARRAY) then err c1 w (if arr then E_COMMA_OR_RBRACE else E_COMMA_OR_RBRACKET)
    else err c1 w (if arr then E_UNEXP_RBRACKET else E_UNEXP_RBRACE).
(* [comment removed for export] *)
Fixpoint skip_space (c : ctrl) (w : list Z) : ctrl * list Z :=
  match w with
  | [] => (c, [])
  | b :: r =>
      if (b =? 32) || (b =? 9) || (b =? 10) then skip_space c r
      else if b =? 13 then match r with
                           | [] => (set_st (push c (c_st c)) ST_CR, [])
                           | b2 :: r2 => if b2 =? 10 then skip_space c r2 else skip_space c r
                           end
      else (c, w)
  end.
Definition skip_space_r (c : ctrl) (w : list Z) : res := let cw := skip_space c w in ret (fst cw) (snd cw).
(* [comment removed for export] *)
Definition lit_done (c : ctrl) (w : list Z) : res := let c1 := set_more c true in RES (set_st c1 (st_after c1)) w [PMW.EkLit] AL_LIT 0.
Definition parse_lit (tail : list Z) (short_st : Z) (c : ctrl) (w : list Z) : res :=
  let n := S (length tail) in
  if (n <=? length w)%nat then
    (if forallb (fun p => fst p =? snd p) (combine (tl (firstn n w)) tail) then lit_done c (skipn n w) else err c w E_INVALID_VALUE)
  else ret (set_st c short_st) (tl w).
Definition parse_null := parse_lit [117; 108; 108] ST_N.
Definition parse_true := parse_lit [114; 117; 101] ST_T.
Definition parse_false := parse_lit [97; 108; 115; 101] ST_F.
(* [comment removed for export] *)
Definition end_string (c : ctrl) (w : list Z) : res :=
  let u := u8_finish (c_u8 c) in
  if negb (u =? 0) then err c w (conv_errc u)
  else let p := top c in
    if p =? ST_MEMBER_NAME then RES (set_st (pop (set_more c true)) ST_EXPECT_COLON) (tl w) [PMW.EkKey] (al_str (c_dlen c)) 0
    else if (p =? ST_OBJECT) || (p =? ST_ARRAY) then RES (set_st (set_more c true) ST_EXPECT_COMMA_OR_END) (tl w) [PMW.EkStr true] (al_str (c_dlen c)) 0
    else if p =? ST_ROOT then RES (set_st (set_more c true) ST_ACCEPT) (tl w) [PMW.EkStr true] (al_str (c_dlen c)) 0
    else err c w E_SYNTAX.
(* [comment removed for export] *)
Definition hexstep (c : ctrl) (second : bool) (v : Z) : ctrl :=                                  (* [comment removed for export] *)
  if second then set_cp2 c ((c_cp2 c * 16 + v) mod 2 ^ 32) else set_cp c ((c_cp c * 16 + v) mod 2 ^ 32).
Fixpoint parse_string (c : ctrl) (w : list Z) : res :=
  match w with
  | [] => ret c []
  | b :: r =>
    let s := c_sst c in
    if s =? SS_TEXT then
      if is_ctl b then err (set_sst c SS_TEXT) w E_ILLEGAL_CTL
      else if (b =? 10) || (b =? 13) || (b =? 9) then err c w E_CHAR_IN_STRING
      else if b =? 92 then parse_string (set_sst c SS_ESC) r
      else if b =? 34 then end_string c w
      else parse_string (tok1 c b) r
    else if s =? SS_ESC then
      if (b =? 34) || (b =? 92) || (b =? 47) then parse_string (set_sst (tok1 c b) SS_TEXT) r
      else if b =? 98 then parse_string (set_sst (tok1 c 8) SS_TEXT) r
      else if b =? 102 then parse_string (set_sst (tok1 c 12) SS_TEXT) r
      else if b =? 110 then parse_string (set_sst (tok1 c 10) SS_TEXT) r
      else if b =? 114 then parse_string (set_sst (tok1 c 13) SS_TEXT) r
      else if b =? 116 then parse_string (set_sst (tok1 c 9) SS_TEXT) r
      else if b =? 117 then parse_string (set_sst (set_cp c 0) SS_U1) r
      else err (set_sst c SS_ESC) w E_ILLEGAL_ESC
    else if s =? SS_U1 then match hexval b with Some v => parse_string (set_sst (set_cp c v) SS_U2) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U2 then match hexval b with Some v => parse_string (set_sst (hexstep c false v) SS_U3) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U3 then match hexval b with Some v => parse_string (set_sst (hexstep c false v) SS_U4) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U4 then
      match hexval b with
      | Some v => let c1 := hexstep c false v in
                  if is_high_surr (c_cp c1) then parse_string (set_sst c1 SS_SP1) r
                  else ret (set_sst (tokn c1 (utf8_of (c_cp c1))) SS_TEXT) r
      | None => err c w E_INVALID_UESC end
    else if s =? SS_SP1 then (if b =? 92 then parse_string (set_sst (set_cp2 c 0) SS_SP2) r else err c w E_SURR_PAIR)
    else if s =? SS_SP2 then (if b =? 117 then parse_string (set_sst c SS_U5) r else err c w E_SURR_PAIR)
    else if s =? SS_U5 then match hexval b with Some v => parse_string (set_sst (set_cp2 c v) SS_U6) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U6 then match hexval b with Some v => parse_string (set_sst (hexstep c true v) SS_U7) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U7 then match hexval b with Some v => parse_string (set_sst (hexstep c true v) SS_U8) r | None => err c w E_INVALID_UESC end
    else if s =? SS_U8 then
      match hexval b with
      | Some v => let c1 := hexstep c true v in parse_string (set_sst (tokn c1 (utf8_of (pair_cp (c_cp c1) (c_cp2 c1)))) SS_TEXT) r
      | None => err c w E_INVALID_UESC end
    else err c w E_STUCK
  end.
(* [comment removed for export] *)
Fixpoint parse_number (c : ctrl) (w : list Z) : res :=
  match w with
  | [] => ret (if c_nst c =? NS_ZERO then set_nst c NS_INTEGER else c) []
  | b :: r =>
    let k := c_nst c in
    let go k' := parse_number (set_nst (tok1 c b) k') r in
    if k =? NS_MINUS then (if is_nzdigit b then go NS_INTEGER else if b =? 48 then go NS_ZERO else err c w E_INVALID_NUMBER)
    else if k =? NS_ZERO then (if b =? 46 then go NS_FRAC1 else if is_exp b then go NS_EXP1 else if is_digit b then err c w E_LEADING_ZERO else end_number c w)
    else if k =? NS_INTEGER then (if is_digit b then go NS_INTEGER else if b =? 46 then go NS_FRAC1 else if is_exp b then go NS_EXP1 else end_number c w)
    else if k =? NS_FRAC1 then (if is_digit b then go NS_FRAC2 else err c w E_INVALID_NUMBER)
    else if k =? NS_FRAC2 then (if is_digit b then go NS_FRAC2 else if is_exp b then go NS_EXP1 else end_number c w)
    else if k =? NS_EXP1 then (if (b =? 45) || (b =? 43) then go NS_EXP2 else if is_digit b then go NS_EXP3 else err c w E_INVALID_NUMBER)
    else if k =? NS_EXP2 then (if is_digit b then go NS_EXP3 else err c w E_INVALID_NUMBER)
    else if k =? NS_EXP3 then (if is_digit b then go NS_EXP3 else end_number c w)
    else err c w E_STUCK
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition start_string (key : bool) (c : ctrl) (r : list Z) : res :=
  parse_string (tok_clear (set_sst (set_st (if key then push c ST_MEMBER_NAME else c) ST_STRING) SS_TEXT)) r.
(* [comment removed for export] *)
Definition start_number (c : ctrl) (b : Z) (r : list Z) : res :=
  parse_number (set_nst (set_st (tok1 (tok_clear c) b) ST_NUMBER) (if b =? 45 then NS_MINUS else if b =? 48 then NS_ZERO else NS_INTEGER)) r.
(* [comment removed for export] *)
Inductive act : Type :=
  | AErr (code : Z) (consumed : bool)   (* [comment removed for export] *)
  | AAccept                            (* [comment removed for export] *)
  | ASkip                              (* [comment removed for export] *)
  | ASlash                             (* [comment removed for export] *)
  | ABegin (arr : bool)                (* [comment removed for export] *)
  | AEnd (arr : bool)                  (* [comment removed for export] *)
  | AString (key : bool)               (* [comment removed for export] *)
  | ANumber                            (* [comment removed for export] *)
  | ALit (which : Z)                   (* [comment removed for export] *)
  | AComma                             (* [comment removed for export] *)
  | AGoto (st' : Z) (consume : bool)   (* [comment removed for export] *)
  | APop (consume : bool)              (* [comment removed for export] *)
  | APushCr                            (* [comment removed for export] *)
  | ALitDone                           (* [comment removed for export] *)
  | AParseString                       (* [comment removed for export] *)
  | AParseNumber                       (* [comment removed for export] *)
  | AStuck.                            (* [comment removed for export] *)
Definition is_expect_st (st : Z) : bool :=
  (st =? ST_START) || (st =? ST_EXPECT_COMMA_OR_END) || (st =? ST_EXPECT_MEMBER_NAME_OR_END) || (st =? ST_EXPECT_MEMBER_NAME)
  || (st =? ST_EXPECT_COLON) || (st =? ST_EXPECT_VALUE_OR_END) || (st =? ST_EXPECT_VALUE).
(* [comment removed for export] *)
Definition value_act (b : Z) : option act :=
  if b =? 123 then Some (ABegin false) else if b =? 91 then Some (ABegin true) else if b =? 34 then Some (AString false)
  else if (b =? 45) || is_digit b then Some ANumber
  else if b =? 110 then Some (ALit 0) else if b =? 116 then Some (ALit 1) else if b =? 102 then Some (ALit 2) else None.
(* [comment removed for export] *)
Definition dispatch (st p b : Z) : act :=
  if st =? ST_ACCEPT then AAccept
  else if st =? ST_CR then APop (b =? 10)
  else if is_expect_st st then
    if is_ctl b then AErr E_ILLEGAL_CTL false
    else if is_ws b then ASkip
    else if b =? 47 then ASlash
    else if st =? ST_START then
      match value_act b with Some a => a | None =>
        if b =? 125 then AErr E_UNEXP_RBRACE false else if b =? 93 then AErr E_UNEXP_RBRACKET false else AErr E_SYNTAX false end
    else if st =? ST_EXPECT_COMMA_OR_END then
      if b =? 125 then AEnd false else if b =? 93 then AEnd true else if b =? 44 then AComma
      else AErr (if p =? ST_ARRAY then E_COMMA_OR_RBRACKET else if p =? ST_OBJECT then E_COMMA_OR_RBRACE else E_UNEXP_CHAR) false
    else if st =? ST_EXPECT_MEMBER_NAME_OR_END then
      if b =? 125 then AEnd false else if b =? 34 then AString true
      else if b =? 39 then AErr E_SQUOTE false else AErr E_EXPECTED_KEY false
    else if st =? ST_EXPECT_MEMBER_NAME then
      if b =? 34 then AString true else if b =? 125 then AErr E_EXTRA_COMMA true
      else if b =? 39 then AErr E_SQUOTE false else AErr E_EXPECTED_KEY false
    else if st =? ST_EXPECT_COLON then
      if b =? 58 then AGoto ST_EXPECT_VALUE true else AErr E_EXPECTED_COLON false
    else if st =? ST_EXPECT_VALUE then
      match value_act b with Some a => a | None =>
        if b =? 93 then AErr (if p =? ST_ARRAY then E_EXTRA_COMMA else E_EXPECTED_VALUE) true
        else if b =? 39 then AErr E_SQUOTE false else AErr E_EXPECTED_VALUE false end
    else (* [comment removed for export] *)
      match value_act b with Some a => a | None =>
        if b =? 93 then AEnd true else if b =? 39 then AErr E_SQUOTE false else AErr E_EXPECTED_VALUE false end
  else if st =? ST_STRING then AParseString
  else if st =? ST_NUMBER then AParseNumber
  else if st =? ST_T then (if b =? 114 then AGoto ST_TR true else AErr E_INVALID_VALUE false)
  else if st =? ST_TR then (if b =? 117 then AGoto ST_TRU true else AErr E_INVALID_VALUE false)
  else if st =? ST_TRU then (if b =? 101 then ALitDone else AErr E_INVALID_VALUE false)
  else if st =? ST_F then (if b =? 97 then AGoto ST_FA true else AErr E_INVALID_VALUE false)
  else if st =? ST_FA then (if b =? 108 then AGoto ST_FAL true else AErr E_INVALID_VALUE false)
  else if st =? ST_FAL then (if b =? 115 then AGoto ST_FALS true else AErr E_INVALID_VALUE false)
  else if st =? ST_FALS then (if b =? 101 then ALitDone else AErr E_INVALID_VALUE false)
  else if st =? ST_N then (if b =? 117 then AGoto ST_NU true else AErr E_INVALID_VALUE false)
  else if st =? ST_NU then (if b =? 108 then AGoto ST_NUL true else AErr E_INVALID_VALUE false)
  else if st =? ST_NUL then (if b =? 108 then ALitDone else AErr E_INVALID_VALUE false)
  else if st =? ST_SLASH then
    (* [comment removed for export] *)
    if b =? 42 then AGoto ST_SLASH_STAR true else if b =? 47 then AGoto ST_SLASH_SLASH true else AErr E_SYNTAX false
  else if st =? ST_SLASH_STAR then
    if b =? 13 then APushCr else if b =? 42 then AGoto ST_SLASH_STAR_STAR true else AGoto ST_SLASH_STAR true
  else if st =? ST_SLASH_SLASH then (if (b =? 13) || (b =? 10) then APop false else AGoto ST_SLASH_SLASH true)
  else if st =? ST_SLASH_STAR_STAR then (if b =? 47 then APop true else AGoto ST_SLASH_STAR true)
  else AStuck.
(* [comment removed for export] *)
Definition act_run (a : act) (c : ctrl) (b : Z) (r : list Z) : res :=
  let w := b :: r in
  match a with
  | AErr code consumed => err c (if consumed then r else w) code
  | AAccept => ret (set_more (set_st (set_done c true) ST_DONE) false) w
  | ASkip => skip_space_r c w
  | ASlash => ret (set_st (push c (c_st c)) ST_SLASH) r
  | ABegin arr => begin_container arr c r
  | AEnd arr => end_container arr c r
  | AString key => start_string key c r
  | ANumber => start_number c b r
  | ALit which => (if which =? 0 then parse_null else if which =? 1 then parse_true else parse_false) c w
  | AComma => bind (begin_member c w) (fun c1 _ => ret c1 r)
  | AGoto st' consumed => ret (set_st c st') (if consumed then r else w)
  | APop consumed => ret (set_st (pop c) (top c)) (if consumed then r else w)
  | APushCr => ret (set_st (push c (c_st c)) ST_CR) r
  | ALitDone => lit_done c r
  | AParseString => parse_string c w
  | AParseNumber => parse_number c w
  | AStuck => err c w E_STUCK
  end.
Definition iter (c : ctrl) (b : Z) (r : list Z) : res := act_run (dispatch (c_st c) (top c) b) c b r.
(* [comment removed for export] *)
Fixpoint loop (F : nat) (c : ctrl) (w : list Z) : res :=
  match w with
  | [] => ret c []
  | b :: r => if negb (c_more c) then ret c w
              else match F with
                   | O => err c w E_FUEL
                   | S F' => bind (iter c b r) (loop F')
                   end
  end.
Definition loop_fuel (w : list Z) : nat := S (S (S (length w + length w))).
(* [comment removed for export] *)
Definition prologue (c : ctrl) : res :=
  let st := c_st c in
  if st =? ST_NUMBER then
    let k := c_nst c in
    if (k =? NS_ZERO) || (k =? NS_INTEGER) || (k =? NS_FRAC2) || (k =? NS_EXP3) then end_number c [] else err c [] E_EOF
  else if st =? ST_ACCEPT then ret (set_more (set_st (set_done c true) ST_DONE) false) []
  else if st =? ST_START then err c [] E_EOF
  else if st =? ST_DONE then ret (set_more c false) []
  else if st =? ST_CR then ret (set_st (pop c) (top c)) []
  else err c [] E_EOF.
(* [comment removed for export] *)
Definition parse_some (c : ctrl) (w : list Z) : res :=
  if c_st c =? ST_ACCEPT then ret (set_more (set_st (set_done c true) ST_DONE) false) w
  else match w with
       | [] => if c_more c then prologue c else ret c []
       | _ => loop (loop_fuel w) c w
       end.
(* [comment removed for export] *)
Definition pcheck_done (c : ctrl) (w : list Z) : res := if forallb is_ws w then ret c [] else err c w E_EXTRA_CHAR.
Definition skip_whitespace (c : ctrl) (w : list Z) : ctrl * list Z :=
  match w with
  | [] => (c, [])
  | b :: r =>
      let cw := (if c_st c =? ST_CR then (set_st (pop c) (top c), if b =? 10 then r else w) else (c, w)) in
      match snd cw with
      | [] => cw
      | b1 :: _ => if is_ws b1 then skip_space (fst cw) (snd cw) else cw
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition r_of (w : list Z) (q : res) : PMW.cres ctrl :=
  PMW.CR (q_c q) (q_evs q) (Z.of_nat (length w) - Z.of_nat (length (q_w q))) (q_code q) (q_al q).
Definition r_of0 (q : res) : PMW.cres ctrl := PMW.CR (q_c q) (q_evs q) 0 (q_code q) (q_al q).
Definition of_text (c : ctrl) (txt : list Z) : ctrl := set_tok c (Z.of_nat (length txt)) (u8_feeds u8_init (b256 txt)).
Definition rstep (f : PMW.fname) (c : ctrl) (inp : list Z) : PMW.cres ctrl :=
  match f with
  | PMW.FSkipSpace => r_of inp (skip_space_r c inp)
  | PMW.FBeginMember => r_of inp (begin_member c inp)
  | PMW.FAfterValue => r_of inp (after_value c inp)
  | PMW.FBeginObject => r_of inp (begin_container false c inp)
  | PMW.FBeginArray => r_of inp (begin_container true c inp)
  | PMW.FEndObject => r_of inp (end_container false c inp)
  | PMW.FEndArray => r_of inp (end_container true c inp)
  | PMW.FParseTrue => r_of inp (parse_true c inp)
  | PMW.FParseFalse => r_of inp (parse_false c inp)
  | PMW.FParseNull => r_of inp (parse_null c inp)
  | PMW.FEndStringValue => r_of0 (end_string (of_text c inp) [])
  | PMW.FEndInt => r_of0 (end_number (of_text c inp) [])
  | PMW.FEndFrac => r_of0 (end_number (of_text c inp) [])
  | PMW.FParseString => r_of inp (parse_string c inp)
  | PMW.FParseNumber => r_of inp (parse_number c inp)
  | PMW.FParseSome => r_of inp (parse_some c inp)
  | PMW.FSkipWs => let cw := skip_whitespace c inp in r_of inp (ret (fst cw) (snd cw))
  | PMW.FCheckDone => r_of inp (pcheck_done c inp)
  end.
(* [comment removed for export] *)
Definition rm_core (c : ctrl) (ps : pstate) : Prop :=
  c_st c = ps_st ps /\ c_more c = ps_more ps /\ c_done c = ps_done ps /\ c_level c = ps_level ps /\ c_stack c = ps_stack ps.
Definition rm_stale (c : ctrl) (M : mem) (P : Z) (ps : pstate) : Prop := rm_core c ps.
Definition rm_match (c : ctrl) (M : mem) (P : Z) (ps : pstate) : Prop :=
  rm_core c ps /\
  (ps_st ps = ST_STRING ->
     c_sst c = ps_sst ps /\ c_dlen c = Z.of_nat (length (ps_buf ps)) /\ c_u8 c = u8_feeds u8_init (b256 (ps_buf ps)) /\
     (3 <= c_sst c <= 11 -> u32 M (P + 148) (c_cp c)) /\ (9 <= c_sst c <= 11 -> u32 M (P + 152) (c_cp2 c)) /\
     (exists t, u8 M (P + 220) t /\ 0 <= t <= 1)) /\                                                  (* [comment removed for export] *)
  (ps_st ps = ST_NUMBER -> c_nst c = ps_nst ps /\ c_dlen c = Z.of_nat (length (ps_buf ps))).
Lemma rm_match_stale : forall c M P ps, rm_match c M P ps -> rm_stale c M P ps.
Proof. intros c M P ps H. exact (proj1 H). Qed.
Definition the_rm : PMW.refmodel := PMW.RM ctrl rm_match rm_stale rstep validate.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pfx (l s : list Z) : bool := (length l <=? length s)%nat && forallb (fun p => fst p =? snd p) (combine l s).
Definition detect (s : list Z) : option nat :=
  if pfx [255; 254; 0; 0] s then None
  else if pfx [0; 0; 254; 255] s then None
  else if pfx [255; 254] s then None
  else if pfx [254; 255] s then None
  else if pfx [239; 187; 191] s then Some 3%nat
  else if (length s <? 4)%nat then Some 0%nat
  else match s with
       | b0 :: b1 :: b2 :: b3 :: _ =>
           if (b0 =? 0) && (b1 =? 0) && (b2 =? 0) then None
           else if (b0 =? 0) && (b2 =? 0) then None
           else if (b1 =? 0) && (b2 =? 0) && (b3 =? 0) then None
           else if (b1 =? 0) && (b3 =? 0) then None
           else Some 0%nat
       | _ => Some 0%nat
       end.
(* [comment removed for export] *)
Record rstate : Type := RS { r_c : ctrl; r_w : list Z; r_rest : list Z; r_bof : bool; r_eof : bool }.
(* [comment removed for export] *)
Definition refill (rs : rstate) : rstate * Z :=
  match r_w rs with
  | _ :: _ => (rs, 0)
  | [] =>
    if r_eof rs then (rs, 0)
    else let s := firstn (Z.to_nat CHUNK) (r_rest rs) in
         let rest := skipn (Z.to_nat CHUNK) (r_rest rs) in
         let eof := (length s <? Z.to_nat CHUNK)%nat in
         match s with
         | [] => (RS (r_c rs) [] rest (r_bof rs) eof, 0)
         | _ => if r_bof rs then
                  match detect s with
                  | None => (RS (r_c rs) [] rest (r_bof rs) eof, E_ILLEGAL_UNICODE)
                  | Some k => (RS (r_c rs) (skipn k s) rest false eof, 0)
                  end
                else (RS (r_c rs) s rest false eof, 0)
         end
  end.
(* [comment removed for export] *)
Fixpoint rloop (F : nat) (rs : rstate) : rstate * list evk * Z * Z :=
  match F with
  | O => (rs, [], 0, E_FUEL)
  | S F' =>
    if negb (c_more (r_c rs)) then (rs, [], 0, 0)
    else
      let p := refill rs in let rs1 := fst p in
      if negb (snd p =? 0) then (rs1, [], 0, snd p)
      else
        let eof := match r_w rs1 with [] => true | _ => false end in
        let q := parse_some (r_c rs1) (r_w rs1) in
        let rs2 := RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1) in
        if negb (q_code q =? 0) then (rs2, q_evs q, q_al q, q_code q)
        else if eof && (c_st (q_c q) =? ST_START) then (rs2, q_evs q, q_al q, 0)
        else if eof && negb ((c_st (q_c q) =? ST_ACCEPT) || c_done (q_c q)) then (rs2, q_evs q, q_al q, E_EOF)
        else let t := rloop F' rs2 in (fst (fst (fst t)), q_evs q ++ snd (fst (fst t)), q_al q + snd (fst t), snd t)
  end.
(* [comment removed for export] *)
Definition sw (rs : rstate) : rstate := let cw := skip_whitespace (r_c rs) (r_w rs) in RS (fst cw) (snd cw) (r_rest rs) (r_bof rs) (r_eof rs).
Fixpoint rtail (F : nat) (rs : rstate) : rstate * Z :=
  match F with
  | O => (rs, E_FUEL)
  | S F' =>
    if r_eof rs then (rs, 0)
    else let rs1 := sw rs in
         match r_w rs1 with
         | [] => let p := refill rs1 in if negb (snd p =? 0) then (fst p, snd p) else rtail F' (fst p)
         | _ => (rs1, 0)
         end
  end.
(* [comment removed for export] *)
Fixpoint rcheck (F : nat) (rs : rstate) : Z :=
  match F with
  | O => E_FUEL
  | S F' =>
    let p := refill rs in let rs1 := fst p in
    if negb (snd p =? 0) then snd p
    else let q := match r_w rs1 with [] => ret (r_c rs1) [] | _ => pcheck_done (r_c rs1) (r_w rs1) end in
         if negb (q_code q =? 0) then q_code q
         else let rs2 := RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1) in
              if r_eof rs2 then 0 else rcheck F' rs2
  end.
Definition read_check_done (F : nat) (rs : rstate) : Z :=
  if r_eof rs then q_code (pcheck_done (r_c rs) (r_w rs)) else rcheck F rs.
(* [comment removed for export] *)
Definition rfuel (p : list Z) : nat := (Nat.div (length p) (Z.to_nat CHUNK) + 4)%nat.
Definition READ (p : list Z) : list evk * Z * Z :=
  let F := rfuel p in
  let t := rloop F (RS ctrl0 [] p true false) in
  let rs := fst (fst (fst t)) in let evs := snd (fst (fst t)) in let al := snd (fst t) in let code := snd t in
  if negb (code =? 0) then (evs, al, code)
  else let u := rtail F (sw rs) in
       if negb (snd u =? 0) then (evs, al, snd u)
       else (evs, al, read_check_done F (fst u)).
(* [comment removed for export] *)
Definition K (p : list Z) : list evk := fst (fst (READ p)).
Definition IND (p : list Z) : Z := PMW.ind_run [] (K p).
Definition ALLOW (p : list Z) : Z := snd (fst (READ p)).
Definition CODE (p : list Z) : Z := snd (READ p).

(* [comment removed for export] *)
(* [comment removed for export] *)
Example ex_obj : READ [123; 34; 97; 34; 58; 91; 49; 44; 50; 93; 125] = ([PMW.EkBegin false; PMW.EkKey; PMW.EkBegin true; PMW.EkNum; PMW.EkNum; PMW.EkEnd; PMW.EkEnd], 6 + 29 + 29, 0).
Proof. vm_compute. reflexivity. Qed.
Example ex_ind : IND [123; 34; 97; 34; 58; 91; 49; 44; 50; 93; 125] = 1 + 9 + 1 + 9 + 11 + 6 + 2.
Proof. vm_compute. reflexivity. Qed.
Example ex_extra : CODE [49; 32; 50] = E_EXTRA_CHAR.
Proof. vm_compute. reflexivity. Qed.
Example ex_empty : CODE [] = E_EOF.
Proof. vm_compute. reflexivity. Qed.
End PMR.
