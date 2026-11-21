(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.

Module RefInflateA_MATCH1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition mc_src (win ob : arr) (put0 : Z) (from : fromptr) (k : Z) : Z :=
  match from with
  | FWin i => arr_get win (i + k)
  | FOut i => arr_get ob (i + k mod (put0 - i))
  end.

Fixpoint mc_obn (win ob : arr) (put0 : Z) (from : fromptr) (j : nat) : arr :=
  match j with
  | O => ob
  | S j' => arr_set (mc_obn win ob put0 from j') (put0 + Z.of_nat j') (mc_src win ob put0 from (Z.of_nat j'))
  end.

Fixpoint from_add (f : fromptr) (j : nat) : fromptr :=
  match j with O => f | S j' => from_succ (from_add f j') end.

Lemma from_add_Win : forall i j, from_add (FWin i) j = FWin (i + Z.of_nat j).
Proof. intros i j. induction j as [|j IH]; [cbn; f_equal; lia|]. cbn [from_add]. rewrite IH. cbn. f_equal. lia. Qed.
Lemma from_add_Out : forall i j, from_add (FOut i) j = FOut (i + Z.of_nat j).
Proof. intros i j. induction j as [|j IH]; [cbn; f_equal; lia|]. cbn [from_add]. rewrite IH. cbn. f_equal. lia. Qed.

Lemma mc_obn_len : forall win ob put0 from j, arr_len (mc_obn win ob put0 from j) = arr_len ob.
Proof. intros. induction j as [|j IH]; [reflexivity|]. cbn [mc_obn]. rewrite arr_len_set. exact IH. Qed.

Lemma mc_obn_get : forall win ob put0 from j p,
  0 <= put0 -> put0 + Z.of_nat j <= arr_len ob ->
  arr_get (mc_obn win ob put0 from j) p
  = if (put0 <=? p) && (p <? put0 + Z.of_nat j) then mc_src win ob put0 from (p - put0) else arr_get ob p.
Proof.
  intros win ob put0 from j p Hp0. induction j as [|j IH]; intros Hj.
  - cbn [mc_obn]. destruct (Z.leb_spec put0 p); [| reflexivity]. destruct (Z.ltb_spec p (put0 + Z.of_nat 0)); [exfalso; lia | reflexivity].
  - cbn [mc_obn]. rewrite arr_get_set. unfold arr_inb. rewrite mc_obn_len.
    destruct (Z.eqb_spec (put0 + Z.of_nat j) p) as [E|NE].
    + subst p. replace ((0 <=? put0 + Z.of_nat j) && (put0 + Z.of_nat j <? arr_len ob)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. destruct (Z.leb_spec put0 (put0 + Z.of_nat j)); [| exfalso; lia].
      destruct (Z.ltb_spec (put0 + Z.of_nat j) (put0 + Z.of_nat (S j))); [| exfalso; lia]. cbn [andb]. f_equal. lia.
    + cbn [andb]. rewrite IH by lia.
      destruct (Z.leb_spec put0 p); [| reflexivity]. cbn [andb].
      destruct (Z.ltb_spec p (put0 + Z.of_nat j)); destruct (Z.ltb_spec p (put0 + Z.of_nat (S j))); try reflexivity; exfalso; lia.
Qed.

Lemma mc_read : forall win ob put0 from j,
  0 <= put0 -> put0 + Z.of_nat j <= arr_len ob ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  match from_add from j with
  | FWin i => arr_get win i
  | FOut i => arr_get (mc_obn win ob put0 from j) i
  end = mc_src win ob put0 from (Z.of_nat j).
Proof.
  intros win ob put0 from j Hp0 Hj Hfrom. destruct from as [i|i].
  - rewrite from_add_Win. reflexivity.
  - rewrite from_add_Out. rewrite mc_obn_get by lia. cbn [mc_src].
    set (d := put0 - i). assert (Hd : 0 < d) by lia.
    destruct (Z_lt_le_dec (Z.of_nat j) d) as [Hlt|Hge].
    + replace ((put0 <=? i + Z.of_nat j) && (i + Z.of_nat j <? put0 + Z.of_nat j)) with false
        by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
      rewrite Z.mod_small by lia. reflexivity.
    + replace ((put0 <=? i + Z.of_nat j) && (i + Z.of_nat j <? put0 + Z.of_nat j)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      f_equal. replace (i + Z.of_nat j - put0) with (Z.of_nat j - d) by lia.
      rewrite <- (Z.mod_add _ 1 d) by lia. f_equal. f_equal. lia.
Qed.

Local Definition mc_body (win : arr) :=
  (fun st : arr * Z * fromptr * Z => let '(ob, put, from, copy) := st in
     let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
     let ob := arr_set ob put v in
     let copy := wrap32 (copy - 1) in
     (negb (copy =? 0), (ob, put + 1, from_succ from, copy))).

Lemma mc_loop : forall win ob put0 from n (k j : nat),
  0 <= put0 -> put0 + n <= arr_len ob -> n < 2 ^ 32 ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  (Z.of_nat j + Z.of_nat k = n)%Z -> (0 < k)%nat ->
  loopZ (Z.of_nat k) (mc_body win) (mc_obn win ob put0 from j, put0 + Z.of_nat j, from_add from j, n - Z.of_nat j)
  = (mc_obn win ob put0 from (Z.to_nat n), put0 + n, from_add from (Z.to_nat n), 0).
Proof.
  intros win ob put0 from n k. induction k as [|k IH]; intros j Hp0 Hn Hn32 Hfrom Hjk Hk; [lia|].
  rewrite loopZ_step by lia. unfold mc_body at 1.
  rewrite (mc_read win ob put0 from j Hp0 ltac:(lia) Hfrom).
  rewrite (wrap32_id (n - Z.of_nat j - 1)) by lia.
  destruct (Z.eqb_spec (n - Z.of_nat j - 1) 0) as [E|NE]; cbn [negb].
  - assert (Ej : Z.to_nat n = S j) by lia. rewrite Ej. cbn [mc_obn from_add]. apply f_equal2; [apply f_equal2; [apply f_equal2; [reflexivity | lia] | reflexivity] | lia].
  - replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    specialize (IH (S j) Hp0 Hn Hn32 Hfrom ltac:(lia) ltac:(lia)).
    cbn [mc_obn from_add] in IH. rewrite <- IH. f_equal. apply f_equal2; [apply f_equal2; [apply f_equal2; [reflexivity | lia] | reflexivity] | lia].
Qed.

Lemma match_copy_eq : forall win ob put0 from n,
  0 <= put0 -> put0 + n <= arr_len ob -> 0 < n < 2 ^ 32 ->
  match from with FOut i => i < put0 | FWin _ => True end ->
  match_copy win (ob, put0, from, n) = (mc_obn win ob put0 from (Z.to_nat n), put0 + n, from_add from (Z.to_nat n), 0).
Proof.
  intros win ob put0 from n Hp0 Hn Hn1 Hfrom. unfold match_copy. cbn [snd].
  pose proof (mc_loop win ob put0 from n (Z.to_nat n) 0 Hp0 Hn ltac:(lia) Hfrom ltac:(lia) ltac:(lia)) as H.
  cbn [mc_obn from_add Z.of_nat] in H. rewrite Z.add_0_r, Z.sub_0_r, Z2Nat.id in H by lia. exact H.
Qed.


Definition mt_plan (s : inflate_state) (r : iregs) : option (fromptr * Z) :=
  let copy := wrap32 (ir_out r - ir_left r) in
  if copy <? is_offset s then
    let copy := wrap32 (is_offset s - copy) in
    if is_whave s <? copy then None
    else
      let cf := if is_wnext s <? copy
                then (wrap32 (copy - is_wnext s), FWin (is_wsize s - wrap32 (copy - is_wnext s)))
                else (copy, FWin (is_wnext s - copy)) in
      Some (snd cf, if is_length s <? fst cf then is_length s else fst cf)
  else Some (FOut (ir_put r - is_offset s), is_length s).

Definition mt_clamp (r : iregs) (copy : Z) : Z := if ir_left r <? copy then ir_left r else copy.

Lemma arm_MATCH_eq : forall s c r, is_sane s = 1 ->
  arm_MATCH ivar_ref (mkW s c r) =
    if ir_left r =? 0 then ALeave (mkW s c r)
    else match mt_plan s r with
         | None => ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_distance_too_far_back) r)
         | Some (from, copy0) =>
             let copy := mt_clamp r copy0 in
             let r1 := irset_left r (wrap32 (ir_left r - copy)) in
             let s1 := iset_length s (wrap32 (is_length s - copy)) in
             let '(ob, put, _, _) := match_copy (is_window s) (ic_outbuf c, ir_put r, from, copy) in
             if wrap32 (is_length s - copy) =? 0
             then ARun tt (mkW (iset_mode s1 LEN) (icset_outbuf c ob) (irset_put r1 put))
             else ARun tt (mkW s1 (icset_outbuf c ob) (irset_put r1 put))
         end.
Proof.
  intros s c r Hsane. unfold arm_MATCH. mstep1 (@gr_eq iregs).
  destruct (ir_left r =? 0); [reflexivity|].
  mstep1 (@gs_eq inflate_state). unfold mt_plan.
  destruct (wrap32 (ir_out r - ir_left r) <? is_offset s).
  - cbn [iv_aux ivar_ref]. rewrite Hsane. cbn [Z.eqb negb andb].
    destruct (is_whave s <? wrap32 (is_offset s - wrap32 (ir_out r - ir_left r))).
    + cbn [andb]. rewrite abind_run. rewrite abind_run. rewrite go_bad_eq. cbv beta iota. rewrite aret_eq. cbv beta iota. rewrite aret_eq. reflexivity.
    + cbn [andb]. destruct (is_wnext s <? wrap32 (is_offset s - wrap32 (ir_out r - ir_left r))); cbn [fst snd];
        mstep1 (@aret_eq (option (fromptr * Z))); unfold mt_clamp; mstep1 ur_eq; mstep1 us_eq; rewrite abind_run;
        cbn [w_s w_c w_r is_window iset_length ir_put irset_left];
        (destruct (match_copy _ _) as [[[ob put] fr] cp]); unfold wset_r, wset_c; cbn [w_s w_c w_r]; mstep1 (@gs_eq inflate_state);
        cbn [is_length iset_length]; (destruct (_ =? 0); [rewrite set_mode_eq | rewrite aret_eq]; reflexivity).
  - mstep1 (@aret_eq (option (fromptr * Z))). unfold mt_clamp. mstep1 ur_eq. mstep1 us_eq. rewrite abind_run.
    cbn [w_s w_c w_r is_window iset_length ir_put irset_left].
    destruct (match_copy _ _) as [[[ob put] fr] cp]. unfold wset_r, wset_c. cbn [w_s w_c w_r]. mstep1 (@gs_eq inflate_state).
    cbn [is_length iset_length]. destruct (_ =? 0); [rewrite set_mode_eq | rewrite aret_eq]; reflexivity.
Qed.
End RefInflateA_MATCH1.

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
