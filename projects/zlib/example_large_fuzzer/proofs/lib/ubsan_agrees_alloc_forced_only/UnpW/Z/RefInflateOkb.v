(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition distext_okb (s : inflate_state) : bool := is_extra s <=? 15.
Definition lenext_okb (s : inflate_state) : bool := is_extra s <=? 15.

Fixpoint dchk (k : nat) (c : icall) (index need : Z -> Z) (N : Z) (tab : Z -> Z) (r : iregs) : option iregs :=
  let i := index (ir_hold r) in
  let nd := need (tab i) in
  if (0 <=? i) && (i <? N) && (0 <=? nd) && (nd <=? 32) then
    if nd <=? ir_bits r then Some r
    else match k with
         | O => None
         | S k' => if ir_have r =? 0 then Some r else dchk k' c index need N tab (pullr c r)
         end
  else None.

Definition ctab_size (p : codeptr) : Z :=
  match p with CDyn ofs => 1444 - ofs | CLenfix => 512 | CDistfix => 32 end.

Definition dec_idx1 (n : Z) (h : Z) : Z := BITSv h n.
Definition dec_idx2 (last : Z) (h : Z) : Z :=
  code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last).
Definition dec_need2 (last : Z) (here : Z) : Z := wrap32 (code_bits last + code_bits here).

Definition decode_okb (two : Z -> bool) (s : inflate_state) (c : icall) (r : iregs) (p : codeptr) (n : Z) : bool :=
  let tab := code_at s p in
  (0 <=? n) && (n <=? 15) &&
  match dchk 8 c (dec_idx1 n) code_bits (ctab_size p) tab r with
  | None => false
  | Some r1 =>
      let last := tab (dec_idx1 n (ir_hold r1)) in
      if (code_bits last <=? ir_bits r1) && two (code_op last) then
        (code_bits last + code_op last <=? 31) &&
        match dchk 8 c (dec_idx2 last) (dec_need2 last) (ctab_size p) tab r1 with None => false | Some _ => true end
      else true
  end.

Definition dist_two (op : Z) : bool := Z.land op 240 =? 0.
Definition dist_okb (w : iw) : bool :=
  decode_okb dist_two (w_s w) (w_c w) (w_r w) (is_distcode (w_s w)) (is_distbits (w_s w)).

Definition match_okb (s : inflate_state) : bool := (1 <=? is_length s) && (1 <=? is_offset s).

Definition len_two (op : Z) : bool := negb (op =? 0) && (Z.land op 240 =? 0).

Definition lenfast_okb (w : iw) : bool :=
  let wR := RESTORE w in
  ff_ok (w_s wR) (w_c wR) (w_r wR) &&
  let c1 := w_c (inflate_fast wR) in
  (0 <=? ic_next_in c1) && (0 <=? ic_avail_in c1) && (ic_next_in c1 + ic_avail_in c1 =? arr_len (ic_input (w_c w)))
  && (0 <=? ic_next_out c1) && (0 <=? ic_avail_out c1) && (ic_next_out c1 + ic_avail_out c1 =? arr_len (ic_outbuf (w_c w))).

Definition len_okb (w : iw) : bool :=
  let s := w_s w in let r := w_r w in
  (0 <=? is_lenbits s) && (is_lenbits s <=? 15) && (0 <=? is_distbits s) && (is_distbits s <=? 15) &&
  (* zlib 1.4: the fast path also needs bits < 8 *)
  if (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8) then lenfast_okb w
  else decode_okb len_two s (w_c w) r (is_lencode s) (is_lenbits s).

Definition ddrop (r : iregs) (n : Z) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)).

Definition addback (s : inflate_state) (n : Z) : inflate_state := iset_back s (swrap32 (is_back s + n)).

Definition dx_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_back (iset_offset s (wrap32 (is_offset s + BITSv h (is_extra s)))) (swrap32 (is_back s + is_extra s)).
Definition dx_r (r : iregs) (e : Z) : iregs :=
  irset_bits (irset_hold r (Z.shiftr (ir_hold r) e)) (wrap32 (ir_bits r - e)).
Definition distext_next (w : iw) : option iw :=
  let s := w_s w in
  if is_extra s =? 0 then Some (mkW (iset_mode s MATCH) (w_c w) (w_r w))
  else match NEEDBITS (is_extra s) w with
       | ARun _ (mkW s1 c1 r1) => Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c1 (dx_r r1 (is_extra s)))
       | _ => None
       end.
Definition distext_chain (w : iw) : bool :=
  distext_okb (w_s w) && match distext_next w with Some w2 => match_okb (w_s w2) | None => true end.

Definition dt_s (s : inflate_state) (B val ext : Z) : inflate_state :=
  iset_mode (iset_extra (iset_offset (iset_back s B) val) ext) DISTEXT.
Definition dist_tailnext (s : inflate_state) (c : icall) (h : Z) (rt : iregs) (sb : inflate_state) : option iw :=
  if negb (Z.land (code_op h) 64 =? 0) then None
  else Some (mkW (dt_s s (swrap32 (is_back sb + code_bits h)) (code_val h) (Z.land (code_op h) 15)) c (ddrop rt (code_bits h))).
Definition dist_next (w : iw) : option iw :=
  let s := w_s w in let c := w_c w in
  match DECODE1 (is_distcode s) (is_distbits s) w with
  | ARun last (mkW _ _ r1) =>
      if dist_two (code_op last) then
        match DECODE2 (is_distcode s) last (mkW s c r1) with
        | ARun here (mkW _ _ r2) => dist_tailnext s c here (ddrop r2 (code_bits last)) (addback s (code_bits last))
        | _ => None
        end
      else dist_tailnext s c last r1 s
  | _ => None
  end.
Definition dist_chain (w : iw) : bool :=
  dist_okb w && match dist_next w with Some w2 => distext_chain w2 | None => true end.

Definition lx_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_back (iset_length s (wrap32 (is_length s + BITSv h (is_extra s)))) (swrap32 (is_back s + is_extra s)).
Definition lx_fin (s1 : inflate_state) : inflate_state := iset_mode (iset_was s1 (is_length s1)) DIST.
Definition lenext_next (w : iw) : option iw :=
  let s := w_s w in
  if is_extra s =? 0 then Some (mkW (lx_fin s) (w_c w) (w_r w))
  else match NEEDBITS (is_extra s) w with
       | ARun _ (mkW s1 c1 r1) => Some (mkW (lx_fin (lx_s s (ir_hold r1))) c1 (ddrop r1 (is_extra s)))
       | _ => None
       end.
Definition lenext_chain (w : iw) : bool :=
  lenext_okb (w_s w) && match lenext_next w with Some w2 => dist_chain w2 | None => true end.

Definition lt_s (s : inflate_state) (B val ext : Z) : inflate_state :=
  iset_mode (iset_extra (iset_length (iset_back s B) val) ext) LENEXT.
Definition len_tailnext (c : icall) (h : Z) (r : iregs) (sb : inflate_state) : option iw :=
  let op := code_op h in
  if (op =? 0) || negb (Z.land op 32 =? 0) || negb (Z.land op 64 =? 0) then None
  else Some (mkW (iset_mode (iset_extra (iset_length (addback sb (code_bits h)) (code_val h)) (Z.land op 15)) LENEXT) c (ddrop r (code_bits h))).
Definition len_next (w : iw) : option iw :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  if (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8) then None
  else
    let s0 := iset_back s 0 in
    match DECODE1 (is_lencode s) (is_lenbits s) (mkW s0 c r) with
    | ARun last (mkW _ _ r1) =>
        if len_two (code_op last) then
          match DECODE2 (is_lencode s) last (mkW s0 c r1) with
          | ARun here (mkW _ _ r2) => len_tailnext c here (ddrop r2 (code_bits last)) (addback s0 (code_bits last))
          | _ => None
          end
        else len_tailnext c last r1 s0
    | _ => None
    end.
Definition len_chain (w : iw) : bool :=
  len_okb w && match len_next w with Some w2 => lenext_chain w2 | None => true end.

Definition len__chain (w : iw) : bool := len_chain (mkW (iset_mode (w_s w) LEN) (w_c w) (w_r w)).

Definition tb_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_ncode (iset_ndist (iset_nlen s (h mod 2 ^ 5 + 257)) (h mod 2 ^ 10 / 2 ^ 5 + 1)) (h mod 2 ^ 14 / 2 ^ 10 + 4).
Definition tb_r (r : iregs) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) 14)) (ir_bits r - 14).
Definition tb_s2 (s : inflate_state) (h : Z) : inflate_state := iset_mode (iset_have (tb_s s h) 0) LENLENS.
Definition table_next (w : iw) : option iw :=
  match NEEDBITS 14 w with
  | ARun _ (mkW s1 c1 r1) =>
      if (286 <? is_nlen (tb_s s1 (ir_hold r1))) || (30 <? is_ndist (tb_s s1 (ir_hold r1))) then None
      else Some (mkW (tb_s2 s1 (ir_hold r1)) c1 (tb_r r1))
  | _ => None
  end.

