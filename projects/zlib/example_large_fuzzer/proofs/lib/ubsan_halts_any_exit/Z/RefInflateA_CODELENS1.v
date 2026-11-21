(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Definition cl_lit (s : inflate_state) (val : Z) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (is_have s) (wrap16 val))) (wrap32 (is_have s + 1)).

Fixpoint lrep (n : nat) (lens : arr) (have copy len : Z) : arr * Z * Z :=
  match n with
  | O => (lens, have, copy)
  | S n' => if negb (copy =? 0) then lrep n' (arr_set lens have (wrap16 len)) (wrap32 (have + 1)) (wrap32 (copy - 1)) len
            else (lens, have, copy)
  end.
Definition cl_rep (s : inflate_state) (copy len : Z) : inflate_state :=
  let '(lens, have, _) := lrep (Z.to_nat copy) (is_lens s) (is_have s) copy len in
  iset_have (iset_lens s lens) have.

Lemma loopZ_lrep : forall n len lens have cp,
  loopZ (Z.of_nat n)
    (fun st : arr * Z * Z => let '(lens, have, copy) := st in
       if negb (copy =? 0) then (true, (arr_set lens have (wrap16 len), wrap32 (have + 1), wrap32 (copy - 1)))
       else (false, (lens, have, copy)))
    (lens, have, cp) = lrep n lens have cp len.
Proof.
  induction n as [|n IH]; intros len lens have cp.
  - cbn [lrep Z.of_nat]. rewrite loopZ_le0 by lia. reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite loopZ_step by lia. cbn [lrep].
    destruct (negb (cp =? 0)); [| reflexivity].
    replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia. apply IH.
Qed.

Lemma lens_repeat_eq : forall copy len s c r, 0 <= copy ->
  lens_repeat copy len (mkW s c r) = ARun tt (mkW (cl_rep s copy len) c r).
Proof.
  intros copy len s c r Hc. unfold lens_repeat. rewrite us_eq. f_equal. f_equal. unfold cl_rep.
  rewrite <- (Z2Nat.id copy) at 1 by exact Hc. rewrite loopZ_lrep. reflexivity.
Qed.

Fixpoint fill (n : nat) (lens : arr) (i v : Z) : arr :=
  match n with O => lens | S n' => fill n' (arr_set lens i v) (i + 1) v end.

Lemma lrep_fill : forall n lens have len,
  0 <= have -> have + Z.of_nat n < 2 ^ 32 ->
  lrep n lens have (Z.of_nat n) len = (fill n lens have (wrap16 len), have + Z.of_nat n, 0).
Proof.
  induction n as [|n IH]; intros lens have len Hh Hn.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [lrep fill]. rewrite Nat2Z.inj_succ in Hn |- *.
    replace (negb (Z.succ (Z.of_nat n) =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    rewrite (wrap32_id (have + 1)) by lia. replace (wrap32 (Z.succ (Z.of_nat n) - 1)) with (Z.of_nat n) by (rewrite wrap32_id by lia; lia).
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma cl_rep_fill : forall s copy len, 0 <= is_have s -> 0 <= copy -> is_have s + copy < 2 ^ 32 ->
  cl_rep s copy len = iset_have (iset_lens s (fill (Z.to_nat copy) (is_lens s) (is_have s) (wrap16 len))) (is_have s + copy).
Proof.
  intros s copy len Hh Hc Hhc. unfold cl_rep.
  rewrite <- (Z2Nat.id copy) at 2 by exact Hc. rewrite lrep_fill by lia. rewrite Z2Nat.id by exact Hc. reflexivity.
Qed.

Lemma BITSv_nonneg : forall h n, 0 <= BITSv h n.
Proof. intros h n. unfold BITSv, wrap32. apply (proj2 (Z.land_nonneg _ _)). left. apply (proj2 (Z.land_nonneg _ _)). right. lia. Qed.

Definition cl_nb (val : Z) : Z := if val =? 16 then 2 else if val =? 17 then 3 else 7.
Definition cl_base (val : Z) : Z := if val =? 16 then 3 else if val =? 17 then 3 else 11.

Definition cl_bad (s : inflate_state) (c : icall) (r : iregs) : iw :=
  mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) r.

Definition cl_after (s : inflate_state) (c : icall) (here : Z) (r2 : iregs) : ares bool :=
  let val := code_val here in
  let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  if (val =? 16) && (is_have s =? 0) then ARun false (cl_bad s c r3)
  else
    let len := if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0 in
    let copy := cl_base val + BITSv (ir_hold r3) nb in
    let r4 := ddrop r3 nb in
    if is_nlen s + is_ndist s <? is_have s + copy then ARun false (cl_bad s c r4)
    else ARun true (mkW (cl_rep s copy len) c r4).

Lemma codelens_body_eq : forall s c r,
  codelens_body (mkW s c r) =
  match DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r) with
  | ARun here (mkW s1 c1 r1) =>
      if code_val here <? 16 then ARun true (mkW (cl_lit s1 (code_val here)) c1 (ddrop r1 (code_bits here)))
      else match NEEDBITS (code_bits here + cl_nb (code_val here)) (mkW s1 c1 r1) with
           | ARun _ (mkW s2 c2 r2) => cl_after s2 c2 here r2
           | ALeave w => ALeave w
           | ARet rc w => ARet rc w
           end
  | ALeave w => ALeave w
  | ARet rc w => ARet rc w
  end.
Proof.
  intros s c r. unfold codelens_body. rewrite abind_run, gs_eq. rewrite abind_run.
  destruct (DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r)) as [here [s1 c1 r1] | w | rc w]; [| reflexivity | reflexivity].
  destruct (code_val here <? 16) eqn:Hv.
  { mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state). unfold set_lens. mstep1 us_eq. mstep1 us_eq. rewrite aret_eq. reflexivity. }
  rewrite abind_run.
  unfold cl_after, cl_nb, cl_base.
  destruct (code_val here =? 16) eqn:H16.
  - rewrite abind_run.
    destruct (NEEDBITS (code_bits here + 2) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
    mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state). cbn [andb].
    destruct (is_have s2 =? 0).
    + rewrite abind_run, go_bad_eq, aret_eq. rewrite aret_eq. reflexivity.
    + mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens iset_mode].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
  - cbn [andb].
    destruct (code_val here =? 17) eqn:H17.
    + rewrite abind_run.
      destruct (NEEDBITS (code_bits here + 3) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
      mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
    + rewrite abind_run.
      destruct (NEEDBITS (code_bits here + 7) (mkW s1 c1 r1)) as [[] [s2 c2 r2] | w | rc w]; [| reflexivity | reflexivity].
      mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. mstep1 (@gs_eq inflate_state). cbv zeta.
      cbn [is_nlen is_ndist is_have is_lens].
      destruct (is_nlen s2 + is_ndist s2 <? _).
      * rewrite abind_run, go_bad_eq, aret_eq. reflexivity.
      * rewrite abind_run, lens_repeat_eq, aret_eq; [reflexivity|]. apply Z.add_nonneg_nonneg; [lia | apply BITSv_nonneg].
Qed.

Lemma codelens_while_S : forall k s c r,
  codelens_while (S k) (mkW s c r) =
    if is_have s <? is_nlen s + is_ndist s then
      match codelens_body (mkW s c r) with
      | ARun true w1 => codelens_while k w1
      | ARun false w1 => ARun tt w1
      | ALeave w1 => ALeave w1
      | ARet rc w1 => ARet rc w1
      end
    else ARun tt (mkW s c r).
Proof.
  intros k s c r. cbn [codelens_while]. rewrite abind_run, gs_eq.
  destruct (is_have s <? is_nlen s + is_ndist s); [| rewrite aret_eq; reflexivity].
  rewrite abind_run. destruct (codelens_body (mkW s c r)) as [[|] w1 | w1 | rc w1]; try reflexivity.
  all: rewrite ?aret_eq; reflexivity.
Qed.

Lemma codelens_while_stop : forall k s c r, is_nlen s + is_ndist s <= is_have s -> codelens_while k (mkW s c r) = ARun tt (mkW s c r).
Proof. intros k s c r H. destruct k; [reflexivity|]. rewrite codelens_while_S. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.


Definition cl_tab1 (s : inflate_state) (tbl : arr) (next lenbits : Z) (work : arr) : inflate_state :=
  iset_work (iset_lenbits (iset_next (iset_lencode (iset_codes s tbl) (CDyn 0)) next) lenbits) work.
Definition cl_tab2 (s : inflate_state) (tbl : arr) (next distbits : Z) (work : arr) : inflate_state :=
  iset_work (iset_distbits (iset_next (iset_distcode (iset_codes s tbl) (CDyn (is_next s))) next) distbits) work.

Definition cl_post (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  if arr_get (is_lens s) 256 =? 0 then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r)
  else
    let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
    let s1 := cl_tab1 s tbl next lenbits work in
    let r1 := irset_ret r ret in
    if negb (ret =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_literal_lengths_set) r1)
    else
      let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1) in
      let s2 := cl_tab2 s1 tbl2 next2 distbits work2 in
      let r2 := irset_ret r1 ret2 in
      if negb (ret2 =? 0) then ARun tt (mkW (iset_mode s2 BAD) (icset_msg c MSG_invalid_distances_set) r2)
      else if flush =? Z_TREES then ALeave (mkW (iset_mode s2 LEN_) c r2)
      else arm_LEN_ ivar_ref (mkW (iset_mode s2 LEN_) c r2).

Lemma arm_CODELENS_eq : forall flush s c r,
  arm_CODELENS ivar_ref flush (mkW s c r) =
  match codelens_while 321 (mkW s c r) with
  | ARun _ (mkW s1 c1 r1) => if is_mode s1 =? BAD then ARun tt (mkW s1 c1 r1) else cl_post flush s1 c1 r1
  | ALeave w => ALeave w
  | ARet rc w => ARet rc w
  end.
Proof.
  intros flush s c r. unfold arm_CODELENS. rewrite abind_run.
  destruct (codelens_while 321 (mkW s c r)) as [[] [s1 c1 r1] | w | rc w]; [| reflexivity | reflexivity].
  rewrite abind_run, gs_eq. destruct (is_mode s1 =? BAD); [rewrite aret_eq; reflexivity|].
  unfold cl_post. destruct (arr_get (is_lens s1) 256 =? 0); [rewrite go_bad_eq; reflexivity|].
  destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
  mstep1 us_eq. mstep1 ur_eq. fold (cl_tab1 s1 tbl nxt lb wk).
  destruct (negb (ret =? 0)); [rewrite go_bad_eq; reflexivity|].
  rewrite abind_run, gs_eq.
  destruct (inflate_table DISTS _ _ _ _ _ 6 _) as [[[[ret2 tbl2] nxt2] db] wk2].
  mstep1 us_eq. mstep1 ur_eq. fold (cl_tab2 (cl_tab1 s1 tbl nxt lb wk) tbl2 nxt2 db wk2).
  destruct (negb (ret2 =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb].
  destruct (flush =? Z_TREES); [rewrite aleave_eq|]; reflexivity.
Qed.


Definition cl_two (op : Z) : bool := false.

Fixpoint clw_chk (k : nat) (s : inflate_state) (c : icall) (r : iregs) : bool :=
  match k with
  | O => true
  | S k' =>
      if is_have s <? is_nlen s + is_ndist s then
        decode_okb cl_two s c r (is_lencode s) (is_lenbits s) &&
        match codelens_body (mkW s c r) with
        | ARun true (mkW s1 c1 r1) => clw_chk k' s1 c1 r1
        | _ => true
        end
      else true
  end.

Definition lens15b (lens : arr) (lo hi : Z) : bool :=
  forallb (fun i => let j := Z.of_nat i in (j <? lo) || (hi <=? j) || (arr_get lens j <=? 15)) (seq 0 320).

Definition cl_post_ok (s : inflate_state) : bool :=
  if arr_get (is_lens s) 256 =? 0 then true
  else
    lens15b (is_lens s) 0 (is_nlen s)
    && it_safe LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s)
    && (let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
        ll_post_ok tbl next lenbits work
        && (if ret =? 0 then
              let s1 := cl_tab1 s tbl next lenbits work in
              lens15b (is_lens s1) (is_nlen s1) (is_nlen s1 + is_ndist s1)
              && it_safe DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1)
              && (let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1) in
                  ll_post_ok tbl2 next2 distbits work2)
            else true)).

Definition codelens_okb (w : iw) : bool :=
  let s := w_s w in
  (is_nlen s + is_ndist s <=? 320)
  && clw_chk 321 s (w_c w) (w_r w)
  && match codelens_while 321 w with
     | ARun _ (mkW s1 c1 r1) => if is_mode s1 =? BAD then true else cl_post_ok s1
     | _ => true
     end.

Definition codelens_next (flush : Z) (w : iw) : option iw :=
  match codelens_while 321 w with
  | ARun _ (mkW s1 c1 r1) =>
      if is_mode s1 =? BAD then None
      else if arr_get (is_lens s1) 256 =? 0 then None
      else
        let '(ret, tbl, next, lenbits, work) := inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) in
        if negb (ret =? 0) then None
        else
          let s2 := cl_tab1 s1 tbl next lenbits work in
          let '(ret2, tbl2, next2, distbits, work2) := inflate_table DISTS (is_lens s2) (is_nlen s2) (is_ndist s2) (is_codes s2) (is_next s2) 6 (is_work s2) in
          if negb (ret2 =? 0) then None
          else if flush =? Z_TREES then None
          else Some (mkW (iset_mode (cl_tab2 s2 tbl2 next2 distbits work2) LEN_) c1 (irset_ret (irset_ret r1 ret) ret2))
  | _ => None
  end.

Lemma lens15b_sound : forall lens lo hi, lens15b lens lo hi = true -> 0 <= lo -> hi <= 320 ->
  forall i, 0 <= i < hi - lo -> arr_get lens (lo + i) <= 15.
Proof.
  intros lens lo hi H Hlo Hhi i Hi. unfold lens15b in H.
  pose proof (forallb_seq_Z (fun j => (j <? lo) || (hi <=? j) || (arr_get lens j <=? 15)) 320%nat (lo + i) H ltac:(cbn; lia)) as Y.
  cbv beta in Y. destruct (Z.ltb_spec (lo + i) lo); [lia|]. destruct (Z.leb_spec hi (lo + i)); [lia|]. cbn [orb] in Y. apply Z.leb_le in Y. exact Y.
Qed.
