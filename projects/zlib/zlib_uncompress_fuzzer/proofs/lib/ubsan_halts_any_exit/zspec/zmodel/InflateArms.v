(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope am_scope.


Definition BITSv (hold n : Z) : Z := Z.land (wrap32 hold) (zmask n).

Definition PULLBYTE : AM unit := fun w =>
  let r := w_r w in
  if ir_have r =? 0 then ALeave w
  else
    let b := arr_get (ic_input (w_c w)) (ir_next r) in
    ARun tt (wset_r w
      (mkIR (ir_next r + 1) (wrap32 (ir_have r - 1)) (ir_put r) (ir_left r)
            (wrap64 (ir_hold r + shl64 b (ir_bits r))) (wrap32 (ir_bits r + 8))
            (ir_in r) (ir_out r) (ir_ret r))).

Fixpoint NEEDBITS_k (k : nat) (n : Z) : AM unit :=
  match k with
  | O => aret tt
  | S k' => do bits <- gr ir_bits ;
            if bits <? n then (PULLBYTE ;; NEEDBITS_k k' n) else aret tt
  end.
Definition NEEDBITS (n : Z) : AM unit := NEEDBITS_k 8 n.

Definition BITS (n : Z) : AM Z := gr (fun r => BITSv (ir_hold r) n).
Definition HOLD : AM Z := gr ir_hold.

Definition DROPBITS (n : Z) : AM unit :=
  ur (fun r => irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n))).

Definition INITBITS : AM unit := ur (fun r => irset_bits (irset_hold r 0) 0).

Definition BYTEBITS : AM unit :=
  ur (fun r => let k := Z.land (ir_bits r) 7 in
               irset_bits (irset_hold r (Z.shiftr (ir_hold r) k)) (wrap32 (ir_bits r - k))).

Definition set_mode (m : Z) : AM unit := us (fun s => iset_mode s m).
Definition set_msg (m : Z) : AM unit := uc (fun c => icset_msg c m).
Definition go_bad (m : Z) : AM unit := set_msg m ;; set_mode BAD.

Definition set_adler_check (v : Z) : AM unit :=
  us (fun s => iset_check s v) ;; uc (fun c => icset_adler c v).

Fixpoint DECODE_k (k : nat) (p : codeptr) (index : Z -> Z) (need : Z -> Z) : AM Z :=
  match k with
  | O => do hold <- HOLD ; gs (fun s => code_at s p (index hold))
  | S k' => do hold <- HOLD ;
            do bits <- gr ir_bits ;
            do here <- gs (fun s => code_at s p (index hold)) ;
            if need here <=? bits then aret here
            else (PULLBYTE ;; DECODE_k k' p index need)
  end.
Definition DECODE1 (p : codeptr) (nbits : Z) : AM Z :=
  DECODE_k 8 p (fun hold => BITSv hold nbits) code_bits.
Definition DECODE2 (p : codeptr) (last : Z) : AM Z :=
  DECODE_k 8 p
    (fun hold => code_val last + Z.shiftr (BITSv hold (code_bits last + code_op last)) (code_bits last))
    (fun here => wrap32 (code_bits last + code_bits here)).

Definition crc_input (copy : Z) : AM unit := fun w =>
  let r := w_r w in
  let bytes := arr_slice (ic_input (w_c w)) (ir_next r) copy in
  ARun tt (wset_s w (iset_check (w_s w) (icrc32_upd (is_check (w_s w)) bytes))).

Definition CRC2 (word : Z) : AM unit :=
  us (fun s => iset_check s (icrc32_upd (is_check s) [wrap8 word; wrap8 (Z.shiftr word 8)])).
Definition CRC4 (word : Z) : AM unit :=
  us (fun s => iset_check s (icrc32_upd (is_check s)
        [wrap8 word; wrap8 (Z.shiftr word 8); wrap8 (Z.shiftr word 16); wrap8 (Z.shiftr word 24)])).

Definition UPDATE_CHECK_bytes (s : inflate_state) (check : Z) (bytes : list Z) : Z :=
  if negb (is_flags s =? 0) then icrc32_upd check bytes else iadler32_upd check bytes.

Definition hcrc_on (s : inflate_state) : bool :=
  negb (Z.land (is_flags s) 512 =? 0) && negb (Z.land (is_wrap s) 4 =? 0).

Definition fixedtables (s : inflate_state) : inflate_state :=
  iset_distbits (iset_distcode (iset_lenbits (iset_lencode s CLenfix) 9) CDistfix) 5.


Section Arms.
  Variable iv : ivariant.
  Variable flush : Z.

  Definition aux (f : inflate_state -> inflate_state) : AM unit :=
    if iv_aux iv then us f else aret tt.
  Definition set_back (v : Z) : AM unit := aux (fun s => iset_back s v).
  Definition add_back (v : Z) : AM unit := aux (fun s => iset_back s (swrap32 (is_back s + v))).


  Definition arm_DONE : AM unit :=
    ur (fun r => irset_ret r Z_STREAM_END) ;; aleave.

  Definition arm_LENGTH : AM unit :=
    do s <- gs (fun s => s) ;
    do st <- (if negb (is_wrap s =? 0) && negb (is_flags s =? 0) then
                NEEDBITS 32 ;;
                do hold <- HOLD ;
                do s <- gs (fun s => s) ;
                if negb (Z.land (is_wrap s) 4 =? 0) && negb (hold =? Z.land (is_total s) 4294967295)
                then go_bad MSG_incorrect_length_check ;; aret false
                else INITBITS ;; aret true
              else aret true) ;
    if st then set_mode DONE ;; arm_DONE else aret tt.

  Definition arm_CHECK : AM unit :=
    do s <- gs (fun s => s) ;
    do ok <- (if negb (is_wrap s =? 0) then
                NEEDBITS 32 ;;
                do r <- gr (fun r => r) ;
                let out := wrap32 (ir_out r - ir_left r) in
                ur (fun r => irset_out r out) ;;
                uc (fun c => icset_total_out c (wrap64 (ic_total_out c + out))) ;;
                us (fun s => iset_total s (wrap64 (is_total s + out))) ;;
                do s <- gs (fun s => s) ;
                (if negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) then
                   do bytes <- (fun w => ARun (arr_slice (ic_outbuf (w_c w)) (ir_put (w_r w) - out) out) w) ;
                   set_adler_check (UPDATE_CHECK_bytes s (is_check s) bytes)
                 else aret tt) ;;
                ur (fun r => irset_out r (ir_left r)) ;;
                do hold <- HOLD ;
                do s <- gs (fun s => s) ;
                let v := if negb (is_flags s =? 0) then hold else ZSWAP32 hold in
                if negb (Z.land (is_wrap s) 4 =? 0) && negb (v =? is_check s)
                then go_bad MSG_incorrect_data_check ;; aret false
                else INITBITS ;; aret true
              else aret true) ;
    if ok then set_mode LENGTH ;; arm_LENGTH else aret tt.


  Definition arm_LIT : AM unit :=
    do r <- gr (fun r => r) ;
    if ir_left r =? 0 then aleave
    else
      do s <- gs (fun s => s) ;
      uc (fun c => icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) ;;
      ur (fun r => irset_left (irset_put r (ir_put r + 1)) (wrap32 (ir_left r - 1))) ;;
      set_mode LEN.

  Definition match_copy (win : arr) (st : arr * Z * fromptr * Z) : arr * Z * fromptr * Z :=
    loopZ (snd st)
      (fun st : arr * Z * fromptr * Z => let '(ob, put, from, copy) := st in
         let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
         let ob := arr_set ob put v in
         let copy := wrap32 (copy - 1) in
         (negb (copy =? 0), (ob, put + 1, from_succ from, copy))) st.

  Definition arm_MATCH : AM unit :=
    do r <- gr (fun r => r) ;
    if ir_left r =? 0 then aleave
    else
      do s <- gs (fun s => s) ;
      let copy := wrap32 (ir_out r - ir_left r) in
      do fc <- (if copy <? is_offset s then
                  let copy := wrap32 (is_offset s - copy) in
                  if (is_whave s <? copy) && (if iv_aux iv then negb (is_sane s =? 0) else true)
                  then go_bad MSG_invalid_distance_too_far_back ;; aret None
                  else
                    let '(copy, from) :=
                      if is_wnext s <? copy
                      then let copy := wrap32 (copy - is_wnext s) in (copy, FWin (is_wsize s - copy))
                      else (copy, FWin (is_wnext s - copy)) in
                    let copy := if is_length s <? copy then is_length s else copy in
                    aret (Some (from, copy))
                else
                  aret (Some (FOut (ir_put r - is_offset s), is_length s))) ;
      match fc with
      | None => aret tt
      | Some (from, copy) =>
          let copy := if ir_left r <? copy then ir_left r else copy in
          ur (fun r => irset_left r (wrap32 (ir_left r - copy))) ;;
          us (fun s => iset_length s (wrap32 (is_length s - copy))) ;;
          (fun w => let '(ob, put, _, _) :=
                      match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
                    ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))) ;;
          do s <- gs (fun s => s) ;
          if is_length s =? 0 then set_mode LEN else aret tt
      end.


  Definition arm_DISTEXT : AM unit :=
    do s <- gs (fun s => s) ;
    (if negb (is_extra s =? 0) then
       NEEDBITS (is_extra s) ;;
       do v <- BITS (is_extra s) ;
       us (fun s => iset_offset s (wrap32 (is_offset s + v))) ;;
       DROPBITS (is_extra s) ;;
       add_back (is_extra s)
     else aret tt) ;;
    set_mode MATCH ;; arm_MATCH.

  Definition arm_DIST : AM unit :=
    do s <- gs (fun s => s) ;
    do here <- DECODE1 (is_distcode s) (is_distbits s) ;
    do here <- (if Z.land (code_op here) 240 =? 0 then
                  let last := here in
                  do here <- DECODE2 (is_distcode s) last ;
                  DROPBITS (code_bits last) ;;
                  add_back (code_bits last) ;;
                  aret here
                else aret here) ;
    DROPBITS (code_bits here) ;;
    add_back (code_bits here) ;;
    if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
    else
      us (fun s => iset_extra (iset_offset s (code_val here)) (Z.land (code_op here) 15)) ;;
      set_mode DISTEXT ;; arm_DISTEXT.

  Definition arm_LENEXT : AM unit :=
    do s <- gs (fun s => s) ;
    (if negb (is_extra s =? 0) then
       NEEDBITS (is_extra s) ;;
       do v <- BITS (is_extra s) ;
       us (fun s => iset_length s (wrap32 (is_length s + v))) ;;
       DROPBITS (is_extra s) ;;
       add_back (is_extra s)
     else aret tt) ;;
    aux (fun s => iset_was s (is_length s)) ;;
    set_mode DIST ;; arm_DIST.

  Definition arm_LEN : AM unit :=
    do r <- gr (fun r => r) ;
    (* zlib 1.4 (inflate.c l.924): the fast path also needs bits < 8 *)
    if iv_fast iv && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8) then
      amodify (fun w => LOAD (inflate_fast (RESTORE w))) ;;
      do s <- gs (fun s => s) ;
      if is_mode s =? TYPE then set_back (-1) else aret tt
    else
      set_back 0 ;;
      do s <- gs (fun s => s) ;
      do here <- DECODE1 (is_lencode s) (is_lenbits s) ;
      do here <- (if negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0) then
                    let last := here in
                    do here <- DECODE2 (is_lencode s) last ;
                    DROPBITS (code_bits last) ;;
                    add_back (code_bits last) ;;
                    aret here
                  else aret here) ;
      DROPBITS (code_bits here) ;;
      add_back (code_bits here) ;;
      us (fun s => iset_length s (code_val here)) ;;
      if code_op here =? 0 then set_mode LIT
      else if negb (Z.land (code_op here) 32 =? 0) then set_back (-1) ;; set_mode TYPE
      else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
      else
        us (fun s => iset_extra s (Z.land (code_op here) 15)) ;;
        set_mode LENEXT ;; arm_LENEXT.

  Definition arm_LEN_ : AM unit := set_mode LEN ;; arm_LEN.


  Definition set_lens (i v : Z) : AM unit :=
    us (fun s => iset_lens s (arr_set (is_lens s) i (wrap16 v))).

  Definition lens_repeat (copy len : Z) : AM unit :=
    us (fun s =>
      let '(lens, have, _) :=
        loopZ copy
          (fun st : arr * Z * Z => let '(lens, have, copy) := st in
             if negb (copy =? 0) then
               (true, (arr_set lens have (wrap16 len), wrap32 (have + 1), wrap32 (copy - 1)))
             else (false, (lens, have, copy)))
          (is_lens s, is_have s, copy) in
      iset_have (iset_lens s lens) have).

  Definition codelens_body : AM bool :=
    do s <- gs (fun s => s) ;
    do here <- DECODE1 (is_lencode s) (is_lenbits s) ;
    if code_val here <? 16 then
      DROPBITS (code_bits here) ;;
      do s <- gs (fun s => s) ;
      set_lens (is_have s) (code_val here) ;;
      us (fun s => iset_have s (wrap32 (is_have s + 1))) ;;
      aret true
    else
      do lc <- (if code_val here =? 16 then
                  NEEDBITS (code_bits here + 2) ;;
                  DROPBITS (code_bits here) ;;
                  do s <- gs (fun s => s) ;
                  if is_have s =? 0 then go_bad MSG_invalid_bit_length_repeat ;; aret None
                  else
                    let len := arr_get (is_lens s) (is_have s - 1) in
                    do b <- BITS 2 ;
                    DROPBITS 2 ;;
                    aret (Some (len, 3 + b))
                else if code_val here =? 17 then
                  NEEDBITS (code_bits here + 3) ;;
                  DROPBITS (code_bits here) ;;
                  do b <- BITS 3 ;
                  DROPBITS 3 ;;
                  aret (Some (0, 3 + b))
                else
                  NEEDBITS (code_bits here + 7) ;;
                  DROPBITS (code_bits here) ;;
                  do b <- BITS 7 ;
                  DROPBITS 7 ;;
                  aret (Some (0, 11 + b))) ;
      match lc with
      | None => aret false
      | Some (len, copy) =>
          do s <- gs (fun s => s) ;
          if is_nlen s + is_ndist s <? is_have s + copy
          then go_bad MSG_invalid_bit_length_repeat ;; aret false
          else lens_repeat copy len ;; aret true
      end.

  Fixpoint codelens_while (k : nat) : AM unit :=
    match k with
    | O => aret tt
    | S k' => do s <- gs (fun s => s) ;
              if is_have s <? is_nlen s + is_ndist s then
                do c <- codelens_body ;
                if c then codelens_while k' else aret tt
              else aret tt
    end.

  Definition arm_CODELENS : AM unit :=
    codelens_while 321%nat ;;
    do s <- gs (fun s => s) ;
    if is_mode s =? BAD then aret tt
    else if arr_get (is_lens s) 256 =? 0 then go_bad MSG_invalid_code_missing_end_of_block
    else
      let '(ret, tbl, next, lenbits, work) :=
        inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
      us (fun s => iset_work (iset_lenbits (iset_next (iset_lencode (iset_codes s tbl) (CDyn 0)) next) lenbits) work) ;;
      ur (fun r => irset_ret r ret) ;;
      if negb (ret =? 0) then go_bad MSG_invalid_literal_lengths_set
      else
        do s <- gs (fun s => s) ;
        let '(ret, tbl, next, distbits, work) :=
          inflate_table DISTS (is_lens s) (is_nlen s) (is_ndist s) (is_codes s) (is_next s) 6 (is_work s) in
        us (fun s => iset_work (iset_distbits (iset_next (iset_distcode (iset_codes s tbl) (CDyn (is_next s))) next) distbits) work) ;;
        ur (fun r => irset_ret r ret) ;;
        if negb (ret =? 0) then go_bad MSG_invalid_distances_set
        else
          set_mode LEN_ ;;
          if iv_flush_exits iv && (flush =? Z_TREES) then aleave else arm_LEN_.

  Fixpoint lenlens_while1 (k : nat) : AM unit :=
    match k with
    | O => aret tt
    | S k' => do s <- gs (fun s => s) ;
              if is_have s <? is_ncode s then
                NEEDBITS 3 ;;
                do b <- BITS 3 ;
                do s <- gs (fun s => s) ;
                set_lens (arr_get order_a (is_have s)) b ;;
                us (fun s => iset_have s (wrap32 (is_have s + 1))) ;;
                DROPBITS 3 ;;
                lenlens_while1 k'
              else aret tt
    end.
  Fixpoint lenlens_while2 (k : nat) : AM unit :=
    match k with
    | O => aret tt
    | S k' => do s <- gs (fun s => s) ;
              if is_have s <? 19 then
                set_lens (arr_get order_a (is_have s)) 0 ;;
                us (fun s => iset_have s (wrap32 (is_have s + 1))) ;;
                lenlens_while2 k'
              else aret tt
    end.

  Definition arm_LENLENS : AM unit :=
    lenlens_while1 19%nat ;;
    lenlens_while2 19%nat ;;
    do s <- gs (fun s => s) ;
    let '(ret, tbl, next, lenbits, work) :=
      inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) in
    (* zlib 1.4 (inflate.c l.820): state->lencode = state->distcode = state->next, before inflate_table *)
    us (fun s => iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s tbl) (CDyn 0)) (CDyn 0)) next) lenbits) work) ;;
    ur (fun r => irset_ret r ret) ;;
    if negb (ret =? 0) then go_bad MSG_invalid_code_lengths_set
    else
      us (fun s => iset_have s 0) ;;
      set_mode CODELENS ;; arm_CODELENS.

  Definition arm_TABLE : AM unit :=
    NEEDBITS 14 ;;
    do v <- BITS 5 ; us (fun s => iset_nlen s (v + 257)) ;; DROPBITS 5 ;;
    do v <- BITS 5 ; us (fun s => iset_ndist s (v + 1)) ;; DROPBITS 5 ;;
    do v <- BITS 4 ; us (fun s => iset_ncode s (v + 4)) ;; DROPBITS 4 ;;
    do s <- gs (fun s => s) ;
    if (286 <? is_nlen s) || (30 <? is_ndist s) then go_bad MSG_too_many_length_or_distance_symbols
    else
      us (fun s => iset_have s 0) ;;
      set_mode LENLENS ;; arm_LENLENS.


  Definition arm_COPY : AM unit :=
    do s <- gs (fun s => s) ;
    let copy := is_length s in
    if negb (copy =? 0) then
      do r <- gr (fun r => r) ;
      let copy := if ir_have r <? copy then ir_have r else copy in
      let copy := if ir_left r <? copy then ir_left r else copy in
      if copy =? 0 then aleave
      else
        uc (fun c => icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) copy)) ;;
        ur (fun r => irset_put (irset_left (irset_next (irset_have r
                 (wrap32 (ir_have r - copy))) (ir_next r + copy)) (wrap32 (ir_left r - copy))) (ir_put r + copy)) ;;
        us (fun s => iset_length s (wrap32 (is_length s - copy)))
    else set_mode TYPE.

  Definition arm_COPY_ : AM unit := set_mode COPY ;; arm_COPY.

  Definition arm_STORED : AM unit :=
    BYTEBITS ;;
    NEEDBITS 32 ;;
    do hold <- HOLD ;
    if negb (Z.land hold 65535 =? Z.lxor (Z.shiftr hold 16) 65535)
    then go_bad MSG_invalid_stored_block_lengths
    else
      us (fun s => iset_length s (Z.land (wrap32 hold) 65535)) ;;
      INITBITS ;;
      set_mode COPY_ ;;
      if iv_flush_exits iv && (flush =? Z_TREES) then aleave else arm_COPY_.


  Definition arm_TYPEDO : AM unit :=
    do s <- gs (fun s => s) ;
    if negb (is_last s =? 0) then BYTEBITS ;; set_mode CHECK
    else
      NEEDBITS 3 ;;
      do v <- BITS 1 ; us (fun s => iset_last s v) ;;
      DROPBITS 1 ;;
      do t <- BITS 2 ;
      do goon <- (if t =? 0 then set_mode STORED ;; aret true
                  else if t =? 1 then
                    us fixedtables ;;
                    set_mode LEN_ ;;
                    if iv_flush_exits iv && (flush =? Z_TREES) then DROPBITS 2 ;; aleave
                    else aret true
                  else if t =? 2 then set_mode TABLE ;; aret true
                  else go_bad MSG_invalid_block_type ;; aret true) ;
      if goon then DROPBITS 2 else aret tt.

  Definition arm_TYPE : AM unit :=
    if iv_flush_exits iv && ((flush =? Z_BLOCK) || (flush =? Z_TREES)) then aleave
    else arm_TYPEDO.


  Definition arm_DICT : AM unit :=
    do s <- gs (fun s => s) ;
    (* zlib 1.4 (inflate.c l.709-712): strm->total_in += in - strm->avail_in before returning Z_NEED_DICT *)
    if is_havedict s =? 0 then
      amodify RESTORE ;;
      do r <- gr (fun r => r) ;
      uc (fun c => icset_total_in c (wrap64 (ic_total_in c + wrap32 (ir_in r - ic_avail_in c)))) ;;
      areturn Z_NEED_DICT
    else set_adler_check iadler32_init ;; set_mode TYPE ;; arm_TYPE.

  Definition arm_DICTID : AM unit :=
    NEEDBITS 32 ;;
    do hold <- HOLD ;
    set_adler_check (ZSWAP32 hold) ;;
    INITBITS ;;
    set_mode DICT ;; arm_DICT.


  Definition arm_HCRC : AM unit :=
    do s <- gs (fun s => s) ;
    do ok <- (if negb (Z.land (is_flags s) 512 =? 0) then
                NEEDBITS 16 ;;
                do hold <- HOLD ;
                do s <- gs (fun s => s) ;
                if negb (Z.land (is_wrap s) 4 =? 0) && negb (hold =? Z.land (is_check s) 65535)
                then go_bad MSG_header_crc_mismatch ;; aret false
                else INITBITS ;; aret true
              else aret true) ;
    if ok then
      set_adler_check icrc32_init ;;
      set_mode TYPE
    else aret tt.

  Definition scan_zero (input : arr) (next have : Z) : Z * Z :=
    loopZ have
      (fun cl : Z * Z => let '(copy, _) := cl in
         let len := arr_get input (next + copy) in
         let copy := wrap32 (copy + 1) in
         (negb (len =? 0) && (copy <? have), (copy, len)))
      (0, 0).

  Definition name_like (flag : Z) : AM bool :=
    do s <- gs (fun s => s) ;
    if negb (Z.land (is_flags s) flag =? 0) then
      do r <- gr (fun r => r) ;
      if ir_have r =? 0 then aret false
      else
        do w <- aget ;
        let '(copy, len) := scan_zero (ic_input (w_c w)) (ir_next r) (ir_have r) in
        (if hcrc_on s then crc_input copy else aret tt) ;;
        ur (fun r => irset_next (irset_have r (wrap32 (ir_have r - copy))) (ir_next r + copy)) ;;
        if negb (len =? 0) then aret false else aret true
    else aret true.

  Definition arm_COMMENT : AM unit :=
    do ok <- name_like 4096 ;
    if ok then set_mode HCRC ;; arm_HCRC else aleave.

  Definition arm_NAME : AM unit :=
    do ok <- name_like 2048 ;
    if ok then us (fun s => iset_length s 0) ;; set_mode COMMENT ;; arm_COMMENT else aleave.

  Definition arm_EXTRA : AM unit :=
    do s <- gs (fun s => s) ;
    do ok <- (if negb (Z.land (is_flags s) 1024 =? 0) then
                do r <- gr (fun r => r) ;
                let copy := is_length s in
                let copy := if ir_have r <? copy then ir_have r else copy in
                (if negb (copy =? 0) then
                   (if hcrc_on s then crc_input copy else aret tt) ;;
                   ur (fun r => irset_next (irset_have r (wrap32 (ir_have r - copy))) (ir_next r + copy)) ;;
                   us (fun s => iset_length s (wrap32 (is_length s - copy)))
                 else aret tt) ;;
                do s <- gs (fun s => s) ;
                if negb (is_length s =? 0) then aret false else aret true
              else aret true) ;
    if ok then us (fun s => iset_length s 0) ;; set_mode NAME ;; arm_NAME else aleave.

  Definition arm_EXLEN : AM unit :=
    do s <- gs (fun s => s) ;
    (if negb (Z.land (is_flags s) 1024 =? 0) then
       NEEDBITS 16 ;;
       do hold <- HOLD ;
       us (fun s => iset_length s (wrap32 hold)) ;;
       (if hcrc_on s then CRC2 hold else aret tt) ;;
       INITBITS
     else aret tt) ;;
    set_mode EXTRA ;; arm_EXTRA.

  Definition arm_OS : AM unit :=
    NEEDBITS 16 ;;
    do hold <- HOLD ;
    do s <- gs (fun s => s) ;
    (if hcrc_on s then CRC2 hold else aret tt) ;;
    INITBITS ;;
    set_mode EXLEN ;; arm_EXLEN.

  Definition arm_TIME : AM unit :=
    NEEDBITS 32 ;;
    do hold <- HOLD ;
    do s <- gs (fun s => s) ;
    (if hcrc_on s then CRC4 hold else aret tt) ;;
    INITBITS ;;
    set_mode OS ;; arm_OS.

  Definition arm_FLAGS : AM unit :=
    NEEDBITS 16 ;;
    do hold <- HOLD ;
    us (fun s => iset_flags s (swrap32 hold)) ;;
    do s <- gs (fun s => s) ;
    if negb (Z.land (is_flags s) 255 =? Z_DEFLATED) then go_bad MSG_unknown_compression_method
    else if negb (Z.land (is_flags s) 57344 =? 0) then go_bad MSG_unknown_header_flags_set
    else
      (if hcrc_on s then CRC2 hold else aret tt) ;;
      INITBITS ;;
      set_mode TIME ;; arm_TIME.


  Definition arm_HEAD : AM unit :=
    do s <- gs (fun s => s) ;
    if is_wrap s =? 0 then set_mode TYPEDO
    else
      NEEDBITS 16 ;;
      do hold <- HOLD ;
      if negb (Z.land (is_wrap s) 2 =? 0) && (hold =? 35615) then
        (if is_wbits s =? 0 then us (fun s => iset_wbits s 15) else aret tt) ;;
        us (fun s => iset_check s icrc32_init) ;;
        CRC2 hold ;;
        INITBITS ;;
        set_mode FLAGS
      else
        do b8 <- BITS 8 ;
        if (Z.land (is_wrap s) 1 =? 0) ||
           negb ((wrap64 (shl32 b8 8 + Z.shiftr hold 8)) mod 31 =? 0)
        then go_bad MSG_incorrect_header_check
        else
          do b4 <- BITS 4 ;
          if negb (b4 =? Z_DEFLATED) then go_bad MSG_unknown_compression_method
          else
            DROPBITS 4 ;;
            do b4 <- BITS 4 ;
            let len := b4 + 8 in
            (* zlib 1.4 (inflate.c l.548-554): the window-size check first, then wbits := len only if it is 0 *)
            do s <- gs (fun s => s) ;
            if (15 <? len) || (negb (is_wbits s =? 0) && (is_wbits s <? len)) then go_bad MSG_invalid_window_size
            else
              (if is_wbits s =? 0 then us (fun s => iset_wbits s len) else aret tt) ;;
              aux (fun s => iset_dmax s (shl32 1 len)) ;;
              us (fun s => iset_flags s 0) ;;
              set_adler_check iadler32_init ;;
              do hold <- HOLD ;
              set_mode (if negb (Z.land hold 512 =? 0) then DICTID else TYPE) ;;
              INITBITS.


  Definition arm_BAD : AM unit := ur (fun r => irset_ret r Z_DATA_ERROR) ;; aleave.
  Definition arm_MEM : AM unit := areturn Z_MEM_ERROR.
  Definition arm_SYNC : AM unit := areturn Z_STREAM_ERROR.


  Definition dispatch : AM unit :=
    do s <- gs (fun s => s) ;
    let m := is_mode s in
    if m =? HEAD then arm_HEAD
    else if m =? FLAGS then arm_FLAGS
    else if m =? TIME then arm_TIME
    else if m =? OS then arm_OS
    else if m =? EXLEN then arm_EXLEN
    else if m =? EXTRA then arm_EXTRA
    else if m =? NAME then arm_NAME
    else if m =? COMMENT then arm_COMMENT
    else if m =? HCRC then arm_HCRC
    else if m =? DICTID then arm_DICTID
    else if m =? DICT then arm_DICT
    else if m =? TYPE then arm_TYPE
    else if m =? TYPEDO then arm_TYPEDO
    else if m =? STORED then arm_STORED
    else if m =? COPY_ then arm_COPY_
    else if m =? COPY then arm_COPY
    else if m =? TABLE then arm_TABLE
    else if m =? LENLENS then arm_LENLENS
    else if m =? CODELENS then arm_CODELENS
    else if m =? LEN_ then arm_LEN_
    else if m =? LEN then arm_LEN
    else if m =? LENEXT then arm_LENEXT
    else if m =? DIST then arm_DIST
    else if m =? DISTEXT then arm_DISTEXT
    else if m =? MATCH then arm_MATCH
    else if m =? LIT then arm_LIT
    else if m =? CHECK then arm_CHECK
    else if m =? LENGTH then arm_LENGTH
    else if m =? DONE then arm_DONE
    else if m =? BAD then arm_BAD
    else if m =? MEM then arm_MEM
    else arm_SYNC.

  Inductive istop : Set := SLeave | SRet (rc : Z).

End Arms.
