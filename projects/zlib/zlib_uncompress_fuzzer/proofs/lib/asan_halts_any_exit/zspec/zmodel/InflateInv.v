(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition SRNGp (s : inflate_state) : Prop :=
  HEAD <= is_mode s <= SYNC
  /\ - 2 ^ 31 <= is_last s < 2 ^ 31 /\ 0 <= is_wrap s < 16 /\ - 2 ^ 31 <= is_havedict s < 2 ^ 31
  /\ - 2 ^ 31 <= is_flags s < 2 ^ 31 /\ 0 <= is_dmax s < 2 ^ 32 /\ 0 <= is_check s < 2 ^ 64 /\ 0 <= is_total s < 2 ^ 64
  /\ 8 <= is_wbits s <= 15 /\ 0 <= is_wsize s < 2 ^ 32 /\ 0 <= is_whave s < 2 ^ 32 /\ 0 <= is_wnext s < 2 ^ 32
  /\ 0 <= is_hold s < 2 ^ 64 /\ 0 <= is_bits s < 2 ^ 32
  /\ 0 <= is_length s < 2 ^ 32 /\ 0 <= is_offset s < 2 ^ 32 /\ 0 <= is_extra s < 2 ^ 32
  /\ match is_lencode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ match is_distcode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ 0 <= is_lenbits s < 2 ^ 32 /\ 0 <= is_distbits s < 2 ^ 32
  /\ 0 <= is_ncode s < 2 ^ 32 /\ 0 <= is_nlen s < 2 ^ 32 /\ 0 <= is_ndist s < 2 ^ 32 /\ 0 <= is_have s < 2 ^ 32
  /\ 0 <= is_next s <= 1444
  /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens s) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (is_work s) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes s) i < 2 ^ 32)
  /\ is_sane s = 1 /\ - 2 ^ 31 <= is_back s < 2 ^ 31 /\ 0 <= is_was s < 2 ^ 32 /\ is_head s = 0
  /\ (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256)
  /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s)
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s).

Section LRNGcopy.
  Variables (NI NO WN TOT0 : Z).
  Definition LRNGp (w : iw) : Prop :=
    let s := w_s w in let c := w_c w in let r := w_r w in
    SRNGp s
    /\ arr_len (ic_input c) = NI /\ arr_len (ic_outbuf c) = NO /\ arr_len (is_window s) = WN
    /\ (WN = 0 \/ WN = 2 ^ is_wbits s) /\ (WN = 0 <-> is_window_blk s = None) /\ (is_wsize s = 0 \/ is_wsize s = WN)
    /\ 0 <= ic_next_in c /\ 0 <= ic_avail_in c /\ ic_next_in c + ic_avail_in c = NI
    /\ 0 <= ic_next_out c /\ 0 <= ic_avail_out c /\ ic_next_out c + ic_avail_out c = NO
    /\ 0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r = NI
    /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r = NO
    /\ ir_in r = NI /\ ir_left r <= ir_out r <= NO /\ ir_out r - ir_left r <= ir_put r
    /\ 0 <= ir_bits r < 64 /\ 0 <= ir_hold r < 2 ^ ir_bits r
    /\ (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256)
    /\ (forall i, 0 <= i < NO -> 0 <= arr_get (ic_outbuf c) i < 256)
    /\ 0 <= ic_total_in c < 2 ^ 64 /\ 0 <= ic_total_out c < 2 ^ 64 /\ 0 <= ic_adler c < 2 ^ 64
    /\ - 2 ^ 31 <= ic_data_type c < 2 ^ 31
    /\ wrap64 (ic_total_out c + (ir_out r - ir_left r)) = wrap64 (TOT0 + ir_put r).
End LRNGcopy.

Definition ARRB (lens work codes : arr) : Prop :=
  (forall i, 0 <= i < 320 -> 0 <= arr_get lens i < 2 ^ 16)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get work i < 2 ^ 16)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get codes i < 2 ^ 32).

Definition SRNGq (s : inflate_state) : Prop :=
  HEAD <= is_mode s <= SYNC
  /\ - 2 ^ 31 <= is_last s < 2 ^ 31 /\ 0 <= is_wrap s < 16 /\ - 2 ^ 31 <= is_havedict s < 2 ^ 31
  /\ - 2 ^ 31 <= is_flags s < 2 ^ 31 /\ 0 <= is_dmax s < 2 ^ 32 /\ 0 <= is_check s < 2 ^ 64 /\ 0 <= is_total s < 2 ^ 64
  /\ 8 <= is_wbits s <= 15 /\ 0 <= is_wsize s < 2 ^ 32 /\ 0 <= is_whave s < 2 ^ 32 /\ 0 <= is_wnext s < 2 ^ 32
  /\ 0 <= is_hold s < 2 ^ 64 /\ 0 <= is_bits s < 2 ^ 32
  /\ 0 <= is_length s < 2 ^ 32 /\ 0 <= is_offset s < 2 ^ 32 /\ 0 <= is_extra s < 2 ^ 32
  /\ match is_lencode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ match is_distcode s with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ 0 <= is_lenbits s < 2 ^ 32 /\ 0 <= is_distbits s < 2 ^ 32
  /\ 0 <= is_ncode s < 2 ^ 32 /\ 0 <= is_nlen s < 2 ^ 32 /\ 0 <= is_ndist s < 2 ^ 32 /\ 0 <= is_have s < 2 ^ 32
  /\ 0 <= is_next s <= 1444
  /\ ARRB (is_lens s) (is_work s) (is_codes s)
  /\ is_sane s = 1 /\ - 2 ^ 31 <= is_back s < 2 ^ 31 /\ 0 <= is_was s < 2 ^ 32 /\ is_head s = 0
  /\ (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256)
  /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s)
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s).

Lemma ARRB_lens_set : forall lens work codes j v, ARRB lens work codes -> 0 <= v < 2 ^ 16 -> ARRB (arr_set lens j v) work codes.
Proof.
  intros lens work codes j v (A & B & C) Hv. split; [| split; [exact B | exact C]].
  intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Hv | exact (A i Hi)].
Qed.

Section LRNGmine.
  Variables (NI NO WN TOT0 : Z).
  Definition LRNGq (w : iw) : Prop :=
    let s := w_s w in let c := w_c w in let r := w_r w in
    SRNGq s
    /\ arr_len (ic_input c) = NI /\ arr_len (ic_outbuf c) = NO /\ arr_len (is_window s) = WN
    /\ (WN = 0 \/ WN = 2 ^ is_wbits s) /\ (WN = 0 <-> is_window_blk s = None) /\ (is_wsize s = 0 \/ is_wsize s = WN)
    /\ 0 <= ic_next_in c /\ 0 <= ic_avail_in c /\ ic_next_in c + ic_avail_in c = NI
    /\ 0 <= ic_next_out c /\ 0 <= ic_avail_out c /\ ic_next_out c + ic_avail_out c = NO
    /\ 0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r = NI
    /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r = NO
    /\ ir_in r = NI /\ ir_left r <= ir_out r <= NO /\ ir_out r - ir_left r <= ir_put r
    /\ 0 <= ir_bits r < 64 /\ 0 <= ir_hold r < 2 ^ ir_bits r
    /\ (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256)
    /\ (forall i, 0 <= i < NO -> 0 <= arr_get (ic_outbuf c) i < 256)
    /\ 0 <= ic_total_in c < 2 ^ 64 /\ 0 <= ic_total_out c < 2 ^ 64 /\ 0 <= ic_adler c < 2 ^ 64
    /\ - 2 ^ 31 <= ic_data_type c < 2 ^ 31
    /\ wrap64 (ic_total_out c + (ir_out r - ir_left r)) = wrap64 (TOT0 + ir_put r).
End LRNGmine.

Lemma SRNGq_of_p : forall s, SRNGp s -> SRNGq s.
Proof. intros s H. unfold SRNGp, SRNGq, ARRB in *. tauto. Qed.
Lemma LRNGq_of_p : forall NI NO WN TOT0 w, LRNGp NI NO WN TOT0 w -> LRNGq NI NO WN TOT0 w.
Proof. intros NI NO WN TOT0 w H. unfold LRNGp, LRNGq in *. destruct H as [S R]. split; [apply SRNGq_of_p; exact S | exact R]. Qed.

Section LRNGstruct.
  Variables (NI NO WN TOT0 : Z).
  Definition CINV (c : icall) : Prop :=
    arr_len (ic_input c) = NI /\ arr_len (ic_outbuf c) = NO
    /\ 0 <= ic_next_in c /\ 0 <= ic_avail_in c /\ ic_next_in c + ic_avail_in c = NI
    /\ 0 <= ic_next_out c /\ 0 <= ic_avail_out c /\ ic_next_out c + ic_avail_out c = NO
    /\ (forall i, 0 <= i < NI -> 0 <= arr_get (ic_input c) i < 256)
    /\ (forall i, 0 <= i < NO -> 0 <= arr_get (ic_outbuf c) i < 256)
    /\ 0 <= ic_total_in c < 2 ^ 64 /\ 0 <= ic_total_out c < 2 ^ 64 /\ 0 <= ic_adler c < 2 ^ 64
    /\ - 2 ^ 31 <= ic_data_type c < 2 ^ 31.
  Definition RINV (r : iregs) : Prop :=
    0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r = NI
    /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r = NO
    /\ ir_in r = NI /\ ir_left r <= ir_out r <= NO /\ ir_out r - ir_left r <= ir_put r
    /\ 0 <= ir_bits r < 64 /\ 0 <= ir_hold r < 2 ^ ir_bits r.
  Definition WINV (s : inflate_state) : Prop :=
    arr_len (is_window s) = WN
    /\ (WN = 0 \/ WN = 2 ^ is_wbits s) /\ (WN = 0 <-> is_window_blk s = None) /\ (is_wsize s = 0 \/ is_wsize s = WN).
  Definition CROSS (c : icall) (r : iregs) : Prop :=
    wrap64 (ic_total_out c + (ir_out r - ir_left r)) = wrap64 (TOT0 + ir_put r).

  Lemma LRNGq_iff : forall s c r,
    LRNGq NI NO WN TOT0 (mkW s c r) <-> SRNGq s /\ CINV c /\ RINV r /\ WINV s /\ CROSS c r.
  Proof.
    intros s c r. unfold LRNGq, CINV, RINV, WINV, CROSS. cbn [w_s w_c w_r]. tauto.
  Qed.
  Lemma LRNGq_mk : forall s c r, SRNGq s -> CINV c -> RINV r -> WINV s -> CROSS c r -> LRNGq NI NO WN TOT0 (mkW s c r).
  Proof. intros s c r A B C D E. apply LRNGq_iff. tauto. Qed.
  Lemma LRNGq_S : forall s c r, LRNGq NI NO WN TOT0 (mkW s c r) -> SRNGq s.
  Proof. intros s c r H. apply LRNGq_iff in H. tauto. Qed.
  Lemma LRNGq_C : forall s c r, LRNGq NI NO WN TOT0 (mkW s c r) -> CINV c.
  Proof. intros s c r H. apply LRNGq_iff in H. tauto. Qed.
  Lemma LRNGq_R : forall s c r, LRNGq NI NO WN TOT0 (mkW s c r) -> RINV r.
  Proof. intros s c r H. apply LRNGq_iff in H. tauto. Qed.
  Lemma LRNGq_W : forall s c r, LRNGq NI NO WN TOT0 (mkW s c r) -> WINV s.
  Proof. intros s c r H. apply LRNGq_iff in H. tauto. Qed.
  Lemma LRNGq_X : forall s c r, LRNGq NI NO WN TOT0 (mkW s c r) -> CROSS c r.
  Proof. intros s c r H. apply LRNGq_iff in H. tauto. Qed.

  Lemma LRNGq_set_s : forall s s' c r,
    LRNGq NI NO WN TOT0 (mkW s c r) -> SRNGq s' ->
    is_window s' = is_window s -> is_window_blk s' = is_window_blk s -> is_wbits s' = is_wbits s -> is_wsize s' = is_wsize s ->
    LRNGq NI NO WN TOT0 (mkW s' c r).
  Proof.
    intros s s' c r H HS E1 E2 E3 E4. apply LRNGq_iff in H. apply LRNGq_iff.
    destruct H as (A & B & C & D & E). split; [exact HS|]. split; [exact B|]. split; [exact C|]. split; [| exact E].
    unfold WINV in *. rewrite E1, E2, E3, E4. exact D.
  Qed.
  Lemma LRNGq_set_r : forall s c r r',
    LRNGq NI NO WN TOT0 (mkW s c r) -> RINV r' ->
    ir_out r' - ir_left r' = ir_out r - ir_left r -> ir_put r' = ir_put r ->
    LRNGq NI NO WN TOT0 (mkW s c r').
  Proof.
    intros s c r r' H HR E1 E2. apply LRNGq_iff in H. apply LRNGq_iff.
    destruct H as (A & B & C & D & E). unfold CROSS in *. rewrite E1, E2. tauto.
  Qed.
End LRNGstruct.




Definition term_ok (ty : codetype) (maxb : Z) (e : Z) : bool :=
  let op := code_op e in let b := code_bits e in let v := code_val e in
  (1 <=? b) && (b <=? maxb) &&
  match ty with
  | LENS => ((op =? 0) && (v <? 256))
            || ((16 <=? op) && (op <=? 21) && (3 <=? v) && (v + Z.shiftl 1 (op - 16) - 1 <=? 258))
            || (negb (Z.land op 64 =? 0) && (Z.land op 16 =? 0))
  | DISTS => ((16 <=? op) && (op <=? 29) && (1 <=? v) && (v + Z.shiftl 1 (op - 16) - 1 <=? 32768))
             || (negb (Z.land op 64 =? 0) && (Z.land op 16 =? 0) && (Z.land op 32 =? 0))
  | CODES => (op =? 0) || (op =? 64)
  end.

Definition is_linkop (op : Z) : bool := (1 <=? op) && (op <=? 15).

Definition root_ok (ty : codetype) (rd : Z -> Z) (root ext : Z) (e : Z) : bool :=
  let op := code_op e in
  if is_linkop op then
    (code_bits e =? root) && (op <=? 15 - root) && (Z.shiftl 1 root <=? code_val e) && (code_val e + Z.shiftl 1 op <=? ext)
    && forallb (fun j => let e' := rd (code_val e + j) in negb (is_linkop (code_op e')) && term_ok ty (15 - root) e')
               (zupto (Z.shiftl 1 op))
  else term_ok ty root e.

Definition tab_ok (ty : codetype) (rd : Z -> Z) (root ext : Z) : bool :=
  (1 <=? root) && (root <=? 15) && (Z.shiftl 1 root <=? ext) &&
  forallb (fun i => root_ok ty rd root ext (rd i)) (zupto (Z.shiftl 1 root)).

Lemma lenfix_ok : tab_ok LENS (arr_get lenfix_a) 9 512 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix_ok : tab_ok DISTS (arr_get distfix_a) 5 32 = true.
Proof. vm_compute. reflexivity. Qed.

Definition cat (codes : arr) (p : codeptr) (i : Z) : Z :=
  match p with
  | CDyn ofs => arr_get codes (ofs + i)
  | CLenfix => arr_get lenfix_a i
  | CDistfix => arr_get distfix_a i
  end.
Lemma code_at_cat : forall s p i, code_at s p i = cat (is_codes s) p i.
Proof. intros s [o| |] i; reflexivity. Qed.

Definition cext (p : codeptr) : Z :=
  match p with CDyn ofs => 1444 - ofs | CLenfix => 512 | CDistfix => 32 end.

Definition tables_okf (lc dc : codeptr) (lb db nx : Z) (codes : arr) : bool :=
  match lc, dc with
  | CLenfix, CDistfix => (lb =? 9) && (db =? 5)
  | CDyn o1, CDyn o2 =>
      (o1 =? 0) && (0 <=? o2) && (o2 <=? nx) && (nx <=? 1444)
      && tab_ok LENS (cat codes lc) lb o2 && tab_ok DISTS (cat codes dc) db (nx - o2)
  | _, _ => false
  end.
Definition tables_ok (s : inflate_state) : bool :=
  tables_okf (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_next s) (is_codes s).

Definition ctab_okf (lc : codeptr) (lb nx : Z) (codes : arr) : bool :=
  match lc with
  | CDyn 0 => tab_ok CODES (cat codes (CDyn 0)) lb nx && (nx <=? 1444)
  | _ => false
  end.
Definition ctab_ok (s : inflate_state) : bool := ctab_okf (is_lencode s) (is_lenbits s) (is_next s) (is_codes s).

Definition rep_ok (rd : Z -> Z) (root : Z) : Prop :=
  (forall x x', 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
     is_linkop (code_op (rd x)) = false ->
     x mod 2 ^ code_bits (rd x) = x' mod 2 ^ code_bits (rd x) -> rd x' = rd x)
  /\ (forall x, 0 <= x < 2 ^ root -> is_linkop (code_op (rd x)) = true ->
      forall i i', 0 <= i < 2 ^ code_op (rd x) -> 0 <= i' < 2 ^ code_op (rd x) ->
        i mod 2 ^ code_bits (rd (code_val (rd x) + i)) = i' mod 2 ^ code_bits (rd (code_val (rd x) + i)) ->
        rd (code_val (rd x) + i') = rd (code_val (rd x) + i)).

Definition rep_rootb (rd : Z -> Z) (root : Z) : bool :=
  forallb (fun x => let e := rd x in let m := Z.shiftl 1 (code_bits e) in
     is_linkop (code_op e) ||
     forallb (fun x' => negb (x mod m =? x' mod m) || (rd x' =? e)) (zupto (Z.shiftl 1 root)))
    (zupto (Z.shiftl 1 root)).
Definition no_linkb (rd : Z -> Z) (root : Z) : bool :=
  forallb (fun x => negb (is_linkop (code_op (rd x)))) (zupto (Z.shiftl 1 root)).

Lemma rep_ok_of_b : forall rd root, 0 <= root -> rep_rootb rd root = true -> no_linkb rd root = true -> rep_ok rd root.
Proof.
  intros rd root Hr R NL. unfold rep_rootb in R. unfold no_linkb in NL. rewrite Z.shiftl_1_l in R, NL. split.
  - intros x x' Hx Hx' L E.
    pose proof (forallb_zupto _ _ R x Hx) as Rx. cbv beta zeta in Rx. rewrite L in Rx. cbn [orb] in Rx.
    pose proof (forallb_zupto _ _ Rx x' Hx') as Rxx. cbv beta in Rxx.
    rewrite Z.shiftl_1_l in Rxx. rewrite E, Z.eqb_refl in Rxx. cbn [negb orb] in Rxx. apply Z.eqb_eq. exact Rxx.
  - intros x Hx L. pose proof (forallb_zupto _ _ NL x Hx) as N. cbv beta in N. rewrite L in N. discriminate N.
Qed.

Lemma lenfix_rep : rep_ok (arr_get lenfix_a) 9.
Proof. apply rep_ok_of_b; [lia | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
Lemma distfix_rep : rep_ok (arr_get distfix_a) 5.
Proof. apply rep_ok_of_b; [lia | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

Definition tables_rep (s : inflate_state) : Prop :=
  rep_ok (cat (is_codes s) (is_lencode s)) (is_lenbits s) /\ rep_ok (cat (is_codes s) (is_distcode s)) (is_distbits s).
Definition ctab_rep (s : inflate_state) : Prop := rep_ok (cat (is_codes s) (is_lencode s)) (is_lenbits s).


Definition lcons (s : inflate_state) (h : Z) : Z :=
  let e := code_at s (is_lencode s) (Z.land h (Z.ones (is_lenbits s))) in
  if is_linkop (code_op e)
  then code_bits e + code_bits (code_at s (is_lencode s) (code_val e + Z.land (Z.shiftr h (code_bits e)) (zmask (code_op e))))
  else code_bits e.
Definition dcons (s : inflate_state) (h : Z) : Z :=
  let e := code_at s (is_distcode s) (Z.land h (Z.ones (is_distbits s))) in
  if is_linkop (code_op e)
  then code_bits e + code_bits (code_at s (is_distcode s) (code_val e + Z.land (Z.shiftr h (code_bits e)) (zmask (code_op e))))
  else code_bits e.
Definition clx (v : Z) : Z := if v <? 16 then 0 else if v =? 16 then 2 else if v =? 17 then 3 else 7.
Definition ccons (s : inflate_state) (h : Z) : Z :=
  let e := code_at s (is_lencode s) (Z.land h (Z.ones (is_lenbits s))) in
  code_bits e + clx (code_val e).

Definition PEND (m : Z) (s : inflate_state) (h bits : Z) : Prop :=
  if m =? HEAD then is_wrap s <> 0
  else if (m =? FLAGS) || (m =? TIME) || (m =? OS) || (m =? DICTID) || (m =? STORED)
          || (m =? CHECK) || (m =? LENGTH) || (m =? DONE) || (m =? BAD) || (m =? MEM) || (m =? SYNC) then True
  else if m =? EXLEN then Z.land (is_flags s) 1024 <> 0
  else if m =? HCRC then Z.land (is_flags s) 512 <> 0
  else if m =? TABLE then bits < 14
  else if m =? CODELENS then bits < ccons s h /\ is_have s < is_nlen s + is_ndist s
  else if m =? LEN then bits < lcons s h
  else if m =? DIST then bits < dcons s h
  else if (m =? LENEXT) || (m =? DISTEXT) then bits < is_extra s
  else False.


Definition codes_live (m : Z) : bool :=
  (m =? LEN_) || (m =? LEN) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) || (m =? LIT).

Definition sinv (s : inflate_state) : Prop :=
  let m := is_mode s in
  0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ (arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444)
  /\ (codes_live m = true -> tables_ok s = true)
  /\ (m = LENLENS -> 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 4 <= is_ncode s <= 19 /\ 0 <= is_have s <= 19
                   /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a i) <= 7))
  /\ (m = CODELENS -> 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_nlen s + is_ndist s
                    /\ ctab_ok s = true
                    /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15))
  /\ (m = LENEXT -> 3 <= is_length s /\ 0 <= is_extra s <= 15 /\ is_length s + Z.shiftl 1 (is_extra s) - 1 <= 258)
  /\ (m = DIST -> 3 <= is_length s <= 258)
  /\ (m = DISTEXT -> 3 <= is_length s <= 258 /\ 1 <= is_offset s /\ 0 <= is_extra s <= 15
                   /\ is_offset s + Z.shiftl 1 (is_extra s) - 1 <= 32768)
  /\ (m = MATCH -> 1 <= is_length s <= 258 /\ 1 <= is_offset s <= 32768)
  /\ (m = COPY_ \/ m = COPY -> 0 <= is_length s <= 65535)
  /\ (codes_live m = true -> tables_rep s)
  /\ (m = CODELENS -> ctab_rep s).


Definition xinv (w : iw) : Prop :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  (ir_ret r = Z_OK \/ is_mode s = BAD)
  /\ ic_next_out c <= ir_put r
  /\ (ir_out r - ir_left r = ir_put r \/ (ir_out r = ir_left r /\ CHECK <= is_mode s)).

Definition DEBT (w : iw) : Prop :=
  let s := w_s w in let r := w_r w in
  forall h', 0 <= h' -> h' mod 2 ^ ir_bits r = ir_hold r -> lcons s h' + 8 * ir_next r + 7 >= ir_bits r.

Definition binv (w : iw) : Prop :=
  let s := w_s w in let r := w_r w in
  ir_bits r < 8 \/ PEND (is_mode s) s (ir_hold r) (ir_bits r).
Definition binv_saved (s : inflate_state) : Prop :=
  is_bits s < 8 \/ PEND (is_mode s) s (is_hold s) (is_bits s).

Definition ck_adl (v : Z) : Prop := v = 0 \/ v = 1 \/ exists a bs, v = adler32_model a bs.
Definition cks (s : inflate_state) : Prop :=
  TYPE <= is_mode s <= CHECK -> Z.land (is_wrap s) 4 <> 0 -> is_flags s = 0 -> ck_adl (is_check s).

Definition cinv (w : iw) : Prop :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  cks s
  /\ (is_mode s <= DICT -> ir_out r = ir_left r)
  /\ (MEM <= is_mode s -> ic_next_out c = ir_put r /\ is_hold s = ir_hold r /\ is_bits s = ir_bits r /\ ir_out r = ir_left r)
  /\ (ir_left r <> ir_out r -> Z.land (is_wrap s) 4 <> 0 -> is_flags s = 0 -> ck_adl (is_check s))
  /\ ir_have r <= ic_avail_in c /\ ir_left r <= ic_avail_out c.

Definition mrank (m : Z) : Z :=
  if m =? EXLEN then 7 else if m =? EXTRA then 6 else if m =? NAME then 5
  else if (m =? COMMENT) || (m =? COPY_) then 4
  else if (m =? HCRC) || (m =? HEAD) || (m =? DICT) || (m =? COPY) || (m =? LENLENS) then 3
  else if (m =? TYPE) || (m =? TYPEDO) || (m =? CODELENS) || (m =? DISTEXT) then 2
  else if (m =? CHECK) || (m =? LENGTH) || (m =? FLAGS) || (m =? STORED) || (m =? LEN_) || (m =? LENEXT) || (m =? MATCH) then 1
  else 0.
Definition PHI (w : iw) : Z :=
  let r := w_r w in 8 * (8 * ir_have r + ir_bits r + ir_left r) + mrank (is_mode (w_s w)).

Section PINV.
  Variables (NI NO WN TOT0 : Z).
  Definition pinv (w : iw) : Prop :=
    (0 <= NI < 2 ^ 32 /\ 0 <= NO < 2 ^ 32) /\ LRNGq NI NO WN TOT0 w /\ sinv (w_s w) /\ xinv w /\ binv w /\ cinv w.
  Definition pinv0 (w : iw) : Prop :=
    (0 <= NI < 2 ^ 32 /\ 0 <= NO < 2 ^ 32) /\ LRNGq NI NO WN TOT0 w /\ sinv (w_s w) /\ xinv w /\ cinv w.
  Lemma pinv_0 : forall w, pinv w -> pinv0 w.
  Proof. intros w (A & B & C & D & _ & F). exact (conj A (conj B (conj C (conj D F)))). Qed.
End PINV.


Lemma shiftl_1 : forall n, 0 <= n -> Z.shiftl 1 n = 2 ^ n.
Proof. intros n Hn. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma tab_ok_root : forall ty rd root ext, tab_ok ty rd root ext = true ->
  1 <= root <= 15 /\ 2 ^ root <= ext /\
  forall i, 0 <= i < 2 ^ root -> root_ok ty rd root ext (rd i) = true.
Proof.
  intros ty rd root ext H. unfold tab_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. rewrite shiftl_1 in H3 by lia.
  split; [lia|]. split; [exact H3|]. intros i Hi. apply (forallb_zupto _ _ H4). rewrite shiftl_1 by lia. exact Hi.
Qed.

Lemma root_ok_cases : forall ty rd root ext e, 0 <= root -> root_ok ty rd root ext e = true ->
  (is_linkop (code_op e) = false /\ term_ok ty root e = true)
  \/ (is_linkop (code_op e) = true /\ code_bits e = root /\ code_op e <= 15 - root /\ 2 ^ root <= code_val e
      /\ code_val e + 2 ^ code_op e <= ext
      /\ forall j, 0 <= j < 2 ^ code_op e ->
           is_linkop (code_op (rd (code_val e + j))) = false /\ term_ok ty (15 - root) (rd (code_val e + j)) = true).
Proof.
  intros ty rd root ext e Hr H. unfold root_ok in H.
  destruct (is_linkop (code_op e)) eqn:L.
  - right. unfold is_linkop in L. apply andb_prop in L as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 H5].
    apply Z.eqb_eq in H1. apply Z.leb_le in H5. apply Z.leb_le in H2. apply Z.leb_le in H3. rewrite !shiftl_1 in H2, H3 by lia.
    split; [reflexivity|]. split; [exact H1|]. split; [exact H5|]. split; [exact H2|]. split; [exact H3|].
    intros j Hj. pose proof (forallb_zupto _ _ H4 j ltac:(rewrite shiftl_1 by lia; exact Hj)) as Hx. cbv beta in Hx.
    apply andb_prop in Hx as [X1 X2]. split; [| exact X2]. destruct (is_linkop _); [discriminate X1 | reflexivity].
  - left. split; [reflexivity | exact H].
Qed.

Lemma term_ok_bits : forall ty maxb e, term_ok ty maxb e = true -> 1 <= code_bits e <= maxb.
Proof.
  intros ty maxb e H. unfold term_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
