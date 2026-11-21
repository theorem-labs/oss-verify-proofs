(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ItCovIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ItCovRep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvDec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvCov.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms4.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms5.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvArms7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflCtx6.

Module InflA_CodelensS.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.Callee6i.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition cd_S1 (s : inflate_state) (r1 : Z * arr * Z * Z * arr) : inflate_state :=
  iset_work (iset_lenbits (iset_next (iset_lencode (iset_codes s (it_tbl r1)) (CDyn 0)) (it_table r1)) (it_bits r1)) (it_work r1).
(* zlib 1.4 (smodel14-r1's LENLENS row): the CODES table write sets distcode := CDyn 0 with lencode *)
Definition ll_S1 (s : inflate_state) (r1 : Z * arr * Z * Z * arr) : inflate_state :=
  iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s (it_tbl r1)) (CDyn 0)) (CDyn 0)) (it_table r1)) (it_bits r1)) (it_work r1).
Definition cd_S2 (s1 : inflate_state) (r2 : Z * arr * Z * Z * arr) : inflate_state :=
  iset_work (iset_distbits (iset_next (iset_distcode (iset_codes s1 (it_tbl r2)) (CDyn (is_next s1))) (it_table r2)) (it_bits r2)) (it_work r2).
Definition cd_call1 (s : inflate_state) : Z * arr * Z * Z * arr :=
  inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s).
Definition cd_call2 (s1 : inflate_state) : Z * arr * Z * Z * arr :=
  inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) (is_codes s1) (is_next s1) 6 (is_work s1).

Definition cdC_res (flush : Z) (s2 : inflate_state) (c : icall) (r : iregs) (ret2 : Z) : ares unit :=
  if negb (ret2 =? 0) then ARun tt (mkW (iset_mode s2 BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2))
  else if flush =? Z_TREES then ALeave (mkW (iset_mode s2 LEN_) c (irset_ret r ret2))
  else arm_LEN_ ivar_ref (mkW (iset_mode s2 LEN_) c (irset_ret r ret2)).
Definition cdB_res (flush : Z) (s1 : inflate_state) (c : icall) (r : iregs) (ret1 : Z) : ares unit :=
  if negb (ret1 =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret1))
  else cdC_res flush (cd_S2 s1 (cd_call2 s1)) c (irset_ret r ret1) (it_ret (cd_call2 s1)).
Definition cd_after (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  if arr_get (is_lens s) 256 =? 0 then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r)
  else cdB_res flush (cd_S1 s (cd_call1 s)) c r (it_ret (cd_call1 s)).

Lemma arm_CODELENS_after : forall flush w0 s c r,
  codelens_while 321 w0 = ARun tt (mkW s c r) -> is_mode s <> BAD ->
  arm_CODELENS ivar_ref flush w0 = cd_after flush s c r.
Proof.
  intros flush w0 s c r HW NB. unfold arm_CODELENS. rewrite abind_run, HW. mstep1 (@gs_eq inflate_state).
  replace (is_mode s =? BAD) with false by (symmetry; apply Z.eqb_neq; exact NB).
  unfold cd_after. destruct (arr_get (is_lens s) 256 =? 0); [rewrite go_bad_eq; reflexivity|].
  unfold cd_call1, cdB_res. destruct (inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s)) as [[[[ret1 tbl1] nx1] lb1] wk1] eqn:IT1.
  cbn [it_ret it_tbl it_table it_bits it_work fst snd]. mstep1 us_eq. mstep1 ur_eq. unfold cd_S1. cbn [it_ret it_tbl it_table it_bits it_work fst snd].
  destruct (negb (ret1 =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 (@gs_eq inflate_state). unfold cd_call2, cdC_res, cd_S2.
  match goal with |- context [inflate_table DISTS ?a ?b ?cc ?d ?e 6 ?f] =>
    destruct (inflate_table DISTS a b cc d e 6 f) as [[[[ret2 tbl2] nx2] db2] wk2] eqn:IT2 end.
  cbn [it_ret it_tbl it_table it_bits it_work fst snd]. mstep1 us_eq. mstep1 ur_eq.
  destruct (negb (ret2 =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb]. destruct (flush =? Z_TREES); reflexivity.
Qed.


Definition cdrop (r : iregs) (n : Z) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)).

Definition cb_after (here : Z) : AM bool :=
  (if code_val here <? 16 then
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
     end)%am.

Lemma codelens_body_dec1 : forall s c r,
  codelens_body (mkW s c r)
  = match DECODE1 (is_lencode s) (is_lenbits s) (mkW s c r) with
    | ARun here w1 => cb_after here w1 | ALeave w1 => ALeave w1 | ARet rc w1 => ARet rc w1 end.
Proof. intros s c r. unfold codelens_body. mstep1 (@gs_eq inflate_state). rewrite abind_run. reflexivity. Qed.

Definition cb_fin (s : inflate_state) (c : icall) (r : iregs) (len copy : Z) : ares bool :=
  if is_nlen s + is_ndist s <? is_have s + copy
  then ARun false (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_bit_length_repeat) r)
  else (lens_repeat copy len ;; aret true)%am (mkW s c r).

Definition cb_lit_s (s : inflate_state) (here : Z) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (is_have s) (wrap16 (code_val here)))) (wrap32 (is_have s + 1)).
Lemma cb_lit : forall here s c r1,
  code_val here < 16 -> cb_after here (mkW s c r1) = ARun true (mkW (cb_lit_s s here) c (cdrop r1 (code_bits here))).
Proof.
  intros here s c r1 Hv. unfold cb_after. replace (code_val here <? 16) with true by (symmetry; apply Z.ltb_lt; exact Hv).
  mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state). unfold set_lens. mstep1 us_eq. mstep1 us_eq. rewrite aret_eq. reflexivity.
Qed.

Lemma cb_rep16 : forall here s c r1 c2 r2,
  code_val here = 16 -> NEEDBITS (code_bits here + 2) (mkW s c r1) = ARun tt (mkW s c2 r2) ->
  cb_after here (mkW s c r1)
  = (let r3 := cdrop r2 (code_bits here) in
     if is_have s =? 0 then ARun false (mkW (iset_mode s BAD) (icset_msg c2 MSG_invalid_bit_length_repeat) r3)
     else cb_fin s c2 (cdrop r3 2) (arr_get (is_lens s) (is_have s - 1)) (3 + BITSv (ir_hold r3) 2)).
Proof.
  intros here s c r1 c2 r2 Hv HN. unfold cb_after. rewrite Hv. change (16 <? 16) with false. change (16 =? 16) with true. cbv iota.
  rewrite abind_run. rewrite abind_run, HN. mstep1 DROPBITS_eq. mstep1 (@gs_eq inflate_state).
  destruct (is_have s =? 0).
  - mstep1 go_bad_eq. rewrite aret_eq. cbv beta iota. rewrite aret_eq. reflexivity.
  - mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. cbv beta iota. mstep1 (@gs_eq inflate_state).
    unfold cb_fin, cdrop. irnorm. destruct (_ <? _); [mstep1 go_bad_eq; rewrite aret_eq; reflexivity | reflexivity].
Qed.

Lemma cb_rep17 : forall here s c r1 c2 r2,
  code_val here = 17 -> NEEDBITS (code_bits here + 3) (mkW s c r1) = ARun tt (mkW s c2 r2) ->
  cb_after here (mkW s c r1)
  = (let r3 := cdrop r2 (code_bits here) in cb_fin s c2 (cdrop r3 3) 0 (3 + BITSv (ir_hold r3) 3)).
Proof.
  intros here s c r1 c2 r2 Hv HN. unfold cb_after. rewrite Hv. change (17 <? 16) with false. change (17 =? 16) with false. change (17 =? 17) with true. cbv iota.
  rewrite abind_run. rewrite abind_run, HN. mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. cbv beta iota.
  mstep1 (@gs_eq inflate_state). unfold cb_fin, cdrop. irnorm. destruct (_ <? _); [mstep1 go_bad_eq; rewrite aret_eq; reflexivity | reflexivity].
Qed.

Lemma cb_rep18 : forall here s c r1 c2 r2,
  16 <= code_val here -> code_val here <> 16 -> code_val here <> 17 -> NEEDBITS (code_bits here + 7) (mkW s c r1) = ARun tt (mkW s c2 r2) ->
  cb_after here (mkW s c r1)
  = (let r3 := cdrop r2 (code_bits here) in cb_fin s c2 (cdrop r3 7) 0 (11 + BITSv (ir_hold r3) 7)).
Proof.
  intros here s c r1 c2 r2 Hv N16 N17 HN. unfold cb_after.
  replace (code_val here <? 16) with false by (symmetry; apply Z.ltb_ge; exact Hv).
  replace (code_val here =? 16) with false by (symmetry; apply Z.eqb_neq; exact N16).
  replace (code_val here =? 17) with false by (symmetry; apply Z.eqb_neq; exact N17).
  rewrite abind_run. rewrite abind_run, HN. mstep1 DROPBITS_eq. mstep1 BITS_eq. mstep1 DROPBITS_eq. rewrite aret_eq. cbv beta iota.
  mstep1 (@gs_eq inflate_state). unfold cb_fin, cdrop. irnorm. destruct (_ <? _); [mstep1 go_bad_eq; rewrite aret_eq; reflexivity | reflexivity].
Qed.

Lemma cb_rep_leave : forall here s c r1 n w',
  16 <= code_val here ->
  n = (if code_val here =? 16 then 2 else if code_val here =? 17 then 3 else 7) ->
  NEEDBITS (code_bits here + n) (mkW s c r1) = ALeave w' ->
  cb_after here (mkW s c r1) = ALeave w'.
Proof.
  intros here s c r1 n w' Hv Hn HN. unfold cb_after.
  replace (code_val here <? 16) with false by (symmetry; apply Z.ltb_ge; exact Hv).
  rewrite abind_run. destruct (code_val here =? 16); [| destruct (code_val here =? 17)]; subst n; rewrite abind_run, HN; reflexivity.
Qed.

Fixpoint fillk (lens : arr) (have : Z) (k : nat) (len : Z) : arr :=
  match k with O => lens | S k' => fillk (arr_set lens have (wrap16 len)) (have + 1) k' len end.

Lemma lens_repeat_exact : forall k lens have copy len,
  Z.of_nat k = copy -> 0 <= have -> have + copy < 2 ^ 31 ->
  loopZ copy (fun st : arr * Z * Z => let '(lens, have, copy) := st in
     if negb (copy =? 0) then (true, (arr_set lens have (wrap16 len), wrap32 (have + 1), wrap32 (copy - 1)))
     else (false, (lens, have, copy))) (lens, have, copy) = (fillk lens have k len, have + copy, 0).
Proof.
  induction k as [|k IH]; intros lens have copy len Hk Hh Hhc.
  - rewrite loopZ_le0 by lia. cbn [fillk]. f_equal; [f_equal|]; lia.
  - rewrite loopZ_step by lia. cbv beta iota zeta.
    destruct (Z.eqb_spec copy 0) as [C0|C0]; [lia|]. cbn [negb].
    rewrite (wrap32_id (have + 1)), (wrap32_id (copy - 1)) by lia. cbn [fillk].
    specialize (IH (arr_set lens have (wrap16 len)) (have + 1) (copy - 1) len ltac:(lia) ltac:(lia) ltac:(lia)).
    etransitivity; [exact IH|]. f_equal. f_equal. lia.
Qed.

Lemma lens_repeat_fill : forall k copy len s c r,
  Z.of_nat k = copy -> 0 <= is_have s -> is_have s + copy < 2 ^ 31 ->
  lens_repeat copy len (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s (fillk (is_lens s) (is_have s) k len)) (is_have s + copy)) c r).
Proof.
  intros k copy len s c r Hk Hh Hhc. unfold lens_repeat, us. cbn [w_s wset_s].
  rewrite (lens_repeat_exact k) by assumption. reflexivity.
Qed.

End FXG.
End InflA_CodelensS.
Export InflA_CodelensS.

Module InflA_LenlensS.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inftrees.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbBase.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarbFast.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateGarb.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InftreesCoverage.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ItCovIface.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ItCovRep.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvDec.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvCov.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms1.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms3.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms4.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms5.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvArms7.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflCtx6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflArmLib6.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.Callee6i.
Import InflA_CodelensS.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ll1_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_have (iset_lens s (arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv h 3)))) (wrap32 (is_have s + 1)).

Lemma ll1_done : forall k s c r, is_ncode s <= is_have s -> lenlens_while1 k (mkW s c r) = ARun tt (mkW s c r).
Proof.
  intros k s c r H. destruct k; [reflexivity|]. cbn [lenlens_while1]. rewrite abind_run, gs_eq.
  replace (is_have s <? is_ncode s) with false by (symmetry; apply Z.ltb_ge; exact H). reflexivity.
Qed.

Lemma ll1_step_run : forall k s c r r1,
  is_have s < is_ncode s -> NEEDBITS 3 (mkW s c r) = ARun tt (mkW s c r1) ->
  lenlens_while1 (S k) (mkW s c r) = lenlens_while1 k (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)).
Proof.
  intros k s c r r1 Hlt HN. cbn [lenlens_while1]. rewrite abind_run, gs_eq.
  replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
  rewrite abind_run, HN. mstep1 BITS_eq. mstep1 (@gs_eq inflate_state). unfold set_lens. mstep1 us_eq. mstep1 us_eq.
  unfold DROPBITS. rewrite abind_run, ur_eq. reflexivity.
Qed.

Lemma ll1_step_leave : forall k s c r w',
  is_have s < is_ncode s -> NEEDBITS 3 (mkW s c r) = ALeave w' -> lenlens_while1 (S k) (mkW s c r) = ALeave w'.
Proof.
  intros k s c r w' Hlt HN. cbn [lenlens_while1]. rewrite abind_run, gs_eq.
  replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
  rewrite abind_run, HN. reflexivity.
Qed.

Lemma ll1_s_fields : forall s h,
  is_mode (ll1_s s h) = is_mode s /\ is_ncode (ll1_s s h) = is_ncode s /\ is_have (ll1_s s h) = wrap32 (is_have s + 1)
  /\ is_lens (ll1_s s h) = arr_set (is_lens s) (arr_get order_a (is_have s)) (wrap16 (BITSv h 3))
  /\ same_blocks s (ll1_s s h).
Proof. intros s h. destruct s; repeat split; reflexivity. Qed.


Fixpoint fillo (lens : arr) (have : Z) (k : nat) : arr :=
  match k with O => lens | S k' => fillo (arr_set lens (arr_get order_a have) 0) (have + 1) k' end.



Lemma ll2_fill : forall k s c r, 0 <= is_have s <= 19 -> 19 - is_have s <= Z.of_nat k ->
  lenlens_while2 k (mkW s c r)
  = ARun tt (mkW (iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19) c r).
Proof.
  induction k as [|k IH]; intros s c r Hh Hk.
  - cbn [Z.of_nat] in Hk. assert (E : is_have s = 19) by lia. replace (19 - is_have s) with 0 by lia. change (Z.to_nat 0) with 0%nat.
    cbn [fillo lenlens_while2]. unfold aret. rewrite <- E. f_equal; f_equal; destruct s; reflexivity.
  - cbn [lenlens_while2]. rewrite abind_run, gs_eq.
    destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
    + unfold set_lens. mstep1 us_eq. mstep1 us_eq. change (wrap16 0) with 0.
      match goal with |- lenlens_while2 k (mkW ?s1 c r) = _ =>
        assert (E1 : is_have s1 = is_have s + 1) by (destruct s; cbn; apply wrap32_id; cbn in Hh, LT; lia);
        assert (E2 : is_lens s1 = arr_set (is_lens s) (arr_get order_a (is_have s)) 0) by (destruct s; reflexivity);
        rewrite (IH s1 c r) by (rewrite E1; cbn [Z.of_nat] in Hk |- *; lia);
        rewrite E1, E2
      end.
      replace (Z.to_nat (19 - is_have s)) with (S (Z.to_nat (19 - (is_have s + 1)))) by lia. cbn [fillo].
      f_equal; f_equal; destruct s; reflexivity.
    + assert (E : is_have s = 19) by lia. replace (19 - is_have s) with 0 by lia. change (Z.to_nat 0) with 0%nat.
      cbn [fillo]. unfold aret. rewrite <- E. f_equal; f_equal; destruct s; reflexivity.
Qed.


Definition tb_s (s : inflate_state) (h : Z) : inflate_state :=
  iset_ncode (iset_ndist (iset_nlen s (BITSv h 5 + 257)) (BITSv (Z.shiftr h 5) 5 + 1)) (BITSv (Z.shiftr (Z.shiftr h 5) 5) 4 + 4).

Lemma tb_s_fields : forall s h,
  is_nlen (tb_s s h) = BITSv h 5 + 257 /\ is_ndist (tb_s s h) = BITSv (Z.shiftr h 5) 5 + 1
  /\ is_ncode (tb_s s h) = BITSv (Z.shiftr (Z.shiftr h 5) 5) 4 + 4 /\ is_mode (tb_s s h) = is_mode s /\ is_have (tb_s s h) = is_have s
  /\ same_blocks s (tb_s s h).
Proof. intros s h. destruct s; repeat split; reflexivity. Qed.

Lemma arm_TABLE_run : forall flush s c r r1,
  NEEDBITS 14 (mkW s c r) = ARun tt (mkW s c r1) ->
  arm_TABLE ivar_ref flush (mkW s c r)
  = (let s3 := tb_s s (ir_hold r1) in
     let r4 := cdrop (cdrop (cdrop r1 5) 5) 4 in
     if (286 <? is_nlen s3) || (30 <? is_ndist s3)
     then ARun tt (mkW (iset_mode s3 BAD) (icset_msg c MSG_too_many_length_or_distance_symbols) r4)
     else arm_LENLENS ivar_ref flush (mkW (iset_mode (iset_have s3 0) LENLENS) c r4)).
Proof.
  intros flush s c r r1 HN. unfold arm_TABLE. rewrite abind_run, HN.
  mstep1 BITS_eq. mstep1 us_eq. unfold DROPBITS at 1. mstep1 ur_eq.
  mstep1 BITS_eq. mstep1 us_eq. unfold DROPBITS at 1. mstep1 ur_eq.
  mstep1 BITS_eq. mstep1 us_eq. unfold DROPBITS at 1. mstep1 ur_eq.
  mstep1 (@gs_eq inflate_state). cbv zeta. unfold tb_s, cdrop.
  destruct r1 as [n1 h1 p1 l1 ho1 b1 i1 o1 rt1]. destruct s.
  cbn [irset_bits irset_hold iset_ncode iset_ndist iset_nlen iset_have iset_mode].
  destruct (_ || _); reflexivity.
Qed.

Lemma arm_TABLE_leave : forall flush s c r w',
  NEEDBITS 14 (mkW s c r) = ALeave w' -> arm_TABLE ivar_ref flush (mkW s c r) = ALeave w'.
Proof. intros flush s c r w' HN. unfold arm_TABLE. rewrite abind_run, HN. reflexivity. Qed.

Definition ll_call (s : inflate_state) : Z * arr * Z * Z * arr :=
  inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s).
Definition ll_after (flush : Z) (s2 : inflate_state) (c : icall) (r : iregs) : ares unit :=
  let t := ll_call s2 in
  if negb (it_ret t =? 0)
  then ARun tt (mkW (iset_mode (ll_S1 s2 t) BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r (it_ret t)))
  else arm_CODELENS ivar_ref flush (mkW (iset_mode (iset_have (ll_S1 s2 t) 0) CODELENS) c (irset_ret r (it_ret t))).

Lemma arm_LENLENS_run : forall flush w0 w1 s2 c2 r2,
  lenlens_while1 19 w0 = ARun tt w1 -> lenlens_while2 19 w1 = ARun tt (mkW s2 c2 r2) ->
  arm_LENLENS ivar_ref flush w0 = ll_after flush s2 c2 r2.
Proof.
  intros flush w0 w1 s2 c2 r2 H1 H2. unfold arm_LENLENS. rewrite abind_run, H1. rewrite abind_run, H2.
  mstep1 (@gs_eq inflate_state). unfold ll_after, ll_call.
  destruct (inflate_table CODES (is_lens s2) 0 19 (is_codes s2) 0 7 (is_work s2)) as [[[[ret1 tbl1] nx1] lb1] wk1].
  cbn [it_ret it_tbl it_table it_bits it_work fst snd]. mstep1 us_eq. mstep1 ur_eq. unfold ll_S1. cbn [it_ret it_tbl it_table it_bits it_work fst snd].
  destruct (negb (ret1 =? 0)); [rewrite go_bad_eq; reflexivity|].
  mstep1 us_eq. unfold set_mode at 1. mstep1 us_eq. reflexivity.
Qed.

Lemma arm_LENLENS_leave : forall flush w0 w', lenlens_while1 19 w0 = ALeave w' -> arm_LENLENS ivar_ref flush w0 = ALeave w'.
Proof. intros flush w0 w' H1. unfold arm_LENLENS. rewrite abind_run, H1. reflexivity. Qed.


Section Pinv.
  Variables (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).

  Lemma ll1_pinv_step : forall s c r r1,
    pinv (mkW s c r) -> is_mode s = LENLENS -> is_have s < is_ncode s -> NEEDBITS 3 (mkW s c r) = ARun tt (mkW s c r1) ->
    pinv (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)) /\ wle (mkW s c r) (mkW (ll1_s s (ir_hold r1)) c (cdrop r1 3)).
  Proof.
    intros s c r r1 HP Hm Hlt HN.
    pose proof (LL1 NI NO WN TOT0 NI32 NO32 1%nat (mkW s c r) HP Hm) as L.
    rewrite (ll1_step_run 0 s c r r1 Hlt HN) in L. cbn [lenlens_while1 aret] in L.
    destruct L as (P & _ & W). split; [exact P | exact W].
  Qed.

  Lemma table_lenlens_pinv : forall s c r r1,
    pinv (mkW s c r) -> is_mode s = TABLE -> NEEDBITS 14 (mkW s c r) = ARun tt (mkW s c r1) ->
    (286 <? is_nlen (tb_s s (ir_hold r1))) || (30 <? is_ndist (tb_s s (ir_hold r1))) = false ->
    pinv (mkW (iset_mode (iset_have (tb_s s (ir_hold r1)) 0) LENLENS) c (cdrop (cdrop (cdrop r1 5) 5) 4)).
  Proof.
    intros s c r r1 PI Hm HN OR. revert HN OR.
    destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk];
    destruct c as [c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg];
    destruct r as [r_next r_have r_put r_left r_hold r_bits r_in r_out r_ret].
    cbn [is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    lazymatch goal with |- NEEDBITS 14 (mkW ?s ?c ?r) = _ -> _ => pose proof (NEEDBITS_run _ _ NI32 NO32 14 s c r RIr ltac:(lia) ClNI Cinb) as NB end.
    intros HN OR. rewrite HN in NB.
    destruct NB as (r1' & E & RI1 & S5 & Htc & Hnb & Hnor & Hnhv & Hnpre & Hnle).
    injection E as E'. subst r1'.
    destruct r1 as [n1 h1 p1 l1 ho1 b1 i1 o1 rt1].
    unfold same5 in S5; unfold tcons in Htc; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in S5, Htc, Hnb, Hnor, Hnhv, Hnpre, Hnle.
    destruct S5 as (-> & -> & -> & -> & ->).
    rinv_open RI1.
    unfold tb_s, cdrop in OR |- *. wred0. wred in OR.
    pose proof (BITSv_bound ho1 5 ltac:(lia)) as B5. change (2 ^ 5) with 32 in B5.
    dropbits 5%Z RI1 RI2 NI32 NO32. rinv_open RI2.
    pose proof (BITSv_bound (Z.shiftr ho1 5) 5 ltac:(lia)) as B5'. change (2 ^ 5) with 32 in B5'.
    dropbits 5%Z RI2 RI3 NI32 NO32. rinv_open RI3.
    pose proof (BITSv_bound (Z.shiftr (Z.shiftr ho1 5) 5) 4 ltac:(lia)) as B4. change (2 ^ 4) with 16 in B4.
    dropbits 4%Z RI3 RI4 NI32 NO32. rinv_open RI4.
    apply Bool.orb_false_elim in OR. destruct OR as [O1 O2]. apply Z.ltb_ge in O1. apply Z.ltb_ge in O2.
    pinv_auto.
  Qed.

  Lemma lenlens_codelens_pinv : forall s c r ret tbl nx lb wk,
    pinv (mkW s c r) -> is_mode s = LENLENS -> is_have s = 19 ->
    inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (ret, tbl, nx, lb, wk) -> ret = 0 ->
    pinv (mkW (iset_mode (iset_have (iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s tbl) (CDyn 0)) (CDyn 0)) nx) lb) wk) 0) CODELENS) c (irset_ret r 0)).  (* 1.4: distcode too *)
  Proof.
    intros s c r ret1 tbl1 next1 lb1 work1 PI2 M2 H19 IT1 R1. subst ret1.
    destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk];
    destruct c as [c_input c_next_in c_avail_in c_outbuf c_next_out c_avail_out c_total_in c_total_out c_adler c_data_type c_msg];
    destruct r as [r_next r_have r_put r_left r_hold r_bits r_in r_out r_ret].
    cbn [is_mode is_have is_lens is_codes is_work] in M2, H19, IT1. pinv_open PI2. subst f_mode. subst f_have. sinv_triage.
    destruct Qlenlens as (QN & QD & QC & QH & QL).
    pose proof (inflate_table_lengths CODES f_lens 0 19 f_codes 0 7 f_work) as LEN1. cbv zeta in LEN1.
    assert (L7 : forall s, 0 <= s < 19 -> 0 <= arr_get f_lens (0 + s) <= 7).
    { intros s Hs. rewrite Z.add_0_l. destruct (order_cover s Hs) as (i & Hi & <-). apply QL. lia. }
    pose proof (tab_ok_of_shape CODES f_lens 0 19 f_codes 0 7 f_work ltac:(lia)
                  ltac:(intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros _; split; [lia|]; split; [reflexivity|]; intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros X; discriminate X) ltac:(lia) ltac:(lia)
                  ltac:(cbn [it_room]; rewrite Acodes; lia) ltac:(rewrite Awork; lia)) as TS1.
    pose proof (rep_ok_of_shape CODES f_lens 0 19 f_codes 0 7 f_work ltac:(lia)
                  ltac:(intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros _; split; [lia|]; split; [reflexivity|]; intros s Hs; pose proof (L7 s Hs); lia)
                  ltac:(intros X; discriminate X) ltac:(lia) ltac:(lia)
                  ltac:(cbn [it_room]; rewrite Acodes; lia) ltac:(rewrite Awork; lia)) as RS1.
    pose proof (ARRB_table CODES f_lens 0 19 f_codes 0 7 f_work Sarrb Acodes Awork) as AR1.
    rewrite IT1 in LEN1, TS1, RS1, AR1.
    cbn [fst snd] in LEN1, TS1, RS1. destruct LEN1 as [LT1 LW1]. destruct AR1 as (AR1 & _ & _ & _).
    destruct (TS1 eq_refl) as (TC1 & BC1 & NX1 & TL1 & OUT1). cbn [it_room] in NX1. rewrite Z.sub_0_r in TC1. specialize (RS1 eq_refl).
    wred0.
    pinv_auto.
    { intros _. split; [clear - QN; lia|]. split; [clear - QD; lia|]. split; [clear - QN QD; lia|]. split; [| intros i Hi; exfalso; clear - Hi; lia].
      unfold ctab_ok. cbn [is_lencode is_lenbits is_next is_codes]. apply ctab_okf_intro; [clear - NX1; lia | exact TC1]. }
  Qed.

  Lemma ll2_pinv : forall s c r,
    pinv (mkW s c r) -> is_mode s = LENLENS -> 0 <= is_have s <= 19 ->
    pinv (mkW (iset_have (iset_lens s (fillo (is_lens s) (is_have s) (Z.to_nat (19 - is_have s)))) 19) c r).
  Proof.
    intros s c r HP Hm Hh.
    destruct (LL2 NI NO WN TOT0 NI32 NO32 19%nat (mkW s c r) HP Hm ltac:(cbn; lia)) as (w' & E & P & _).
    rewrite (ll2_fill 19 s c r Hh ltac:(cbn; lia)) in E. injection E as <-. exact P.
  Qed.
End Pinv.

Lemma it_eta : forall t : Z * arr * Z * Z * arr, t = (it_ret t, it_tbl t, it_table t, it_bits t, it_work t).
Proof. intros [[[[a b] c] d] e]. reflexivity. Qed.
End FXG.
End InflA_LenlensS.
Export InflA_LenlensS.

