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
Fixpoint cstr (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: l' => if c =? 0 then [] else c :: cstr l'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hex_digit_adj (c : Z) : Z :=
  let c1 := if c_A <=? c then Z.land c 223 - 7 else c in
  (c1 - 48) mod 256.

(* [comment removed for export] *)
Fixpoint hex_loop (val : Z) (hs : list Z) : option Z :=
  match hs with
  | [] => Some val
  | h :: t =>
      let c := hex_digit_adj h in
      if Z.land c 240 =? 0 then hex_loop (Z.lor (Z.shiftl val 4) c) t else None
  end.

(* [comment removed for export] *)
Definition yhexToDigit (val : Z) (str : list Z) (i : Z) : option Z :=
  hex_loop val [znth str i; znth str (i + 1); znth str (i + 2); znth str (i + 3)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition yUtf32toUtf8 (cp : Z) : list Z :=
  if cp <? 128 then [cp]
  else if cp <? 2048 then
    [Z.lor (Z.shiftr cp 6) 192; Z.lor (Z.land cp 63) 128]
  else if cp <? 65536 then
    [Z.lor (Z.shiftr cp 12) 224; Z.lor (Z.land (Z.shiftr cp 6) 63) 128; Z.lor (Z.land cp 63) 128]
  else if cp <? 2097152 then
    [Z.lor (Z.shiftr cp 18) 240; Z.lor (Z.land (Z.shiftr cp 12) 63) 128;
     Z.lor (Z.land (Z.shiftr cp 6) 63) 128; Z.lor (Z.land cp 63) 128]
  else [63] (* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition combine_surrogate (cp sur : Z) : Z :=
  Z.lor (Z.lor (Z.shiftl (Z.land cp 63) 10)
               (Z.shiftl (Z.land (Z.shiftr cp 6) 15 + 1) 16))
        (Z.land sur 1023).

(* [comment removed for export] *)
Definition simple_escape (c : Z) : option Z :=
  if c =? c_r then Some 13
  else if c =? c_n then Some 10
  else if c =? c_bslash then Some 92
  else if c =? c_slash then Some 47
  else if c =? c_quote then Some 34
  else if c =? c_f then Some 12
  else if c =? c_b then Some 8
  else if c =? c_t then Some 9
  else None.

(* [comment removed for export] *)
Fixpoint ydecode_loop (fuel : nat) (b : ybuf) (str : list Z) (len beg end_ : Z)
  : yprog (ybuf * Z * Z) :=
  match fuel with
  | O => YAbort
  | S fuel' =>
    if end_ <? len then
      if znth str end_ =? c_bslash then
        b1 <- ybuf_append b (zslice str beg (end_ - beg)) ;;
        let e1 := end_ + 1 in
        let c := znth str e1 in
        match simple_escape c with
        | Some u =>
            b2 <- ybuf_append b1 [u] ;;
            ydecode_loop fuel' b2 str len (e1 + 1) (e1 + 1)
        | None =>
          if c =? c_u then
            let e2 := e1 + 1 in
            match yhexToDigit 0 str e2 with
            | None => YAbort
            | Some cp =>
              let e3 := e2 + 3 in
              let k := (* [comment removed for export] *)
                fun (cp' : Z) (e : Z) =>
                  b2 <- ybuf_append b1 (if cp' =? 0 then [0] else cstr (yUtf32toUtf8 cp')) ;;
                  ydecode_loop fuel' b2 str len (e + 1) (e + 1) in
              if Z.land cp 64512 =? 55296 then
                if (e3 + 2 <? len) && (znth str (e3 + 1) =? c_bslash) && (znth str (e3 + 2) =? c_u) then
                  let e4 := e3 + 1 in
                  match yhexToDigit 0 str (e4 + 2) with
                  | None => YAbort
                  | Some sur => k (combine_surrogate cp sur) (e4 + 5)
                  end
                else
                  (* [comment removed for export] *)
                  b2 <- ybuf_append b1 [63] ;;
                  ydecode_loop fuel' b2 str len (e3 + 1) (e3 + 1)
              else k cp e3
            end
          else YAbort (* [comment removed for export] *)
        end
      else ydecode_loop fuel' b str len beg (end_ + 1)
    else YRet (b, beg, end_)
  end.

Definition decode_fuel (len : Z) : nat := S (Z.to_nat len).

(* [comment removed for export] *)
Definition ystring_decode (b : ybuf) (str : list Z) (len : Z) : yprog ybuf :=
  r <- ydecode_loop (decode_fuel len) b str len 0 0 ;;
  let '(b1, beg, e) := r in
  ybuf_append b1 (zslice str beg (e - beg)).
