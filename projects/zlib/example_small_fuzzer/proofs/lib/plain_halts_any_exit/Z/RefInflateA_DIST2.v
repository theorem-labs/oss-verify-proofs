(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.

Module RefInflateA_LEN1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST1.
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

Definition lf_w (s : inflate_state) (c : icall) (r : iregs) : iw := LOAD (inflate_fast (RESTORE (mkW s c r))).
Definition lf_res (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  let w := lf_w s c r in
  if is_mode (w_s w) =? TYPE then ARun tt (mkW (iset_back (w_s w) (-1)) (w_c w) (w_r w)) else ARun tt w.

Lemma arm_LEN_fast : forall s c r, 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  arm_LEN ivar_ref (mkW s c r) = lf_res s c r.
Proof.
  intros s c r Hh Hl Hb. unfold arm_LEN. mstep1 (@gr_eq iregs).
  cbn [iv_fast ivar_ref andb].
  rewrite (proj2 (Z.leb_le _ _) Hh), (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hb). cbn [andb].
  unfold lf_res, lf_w. rewrite abind_run. unfold amodify at 1.
  destruct (LOAD (inflate_fast (RESTORE (mkW s c r)))) as [s3 c3 r3] eqn:E3.
  mstep1 (@gs_eq inflate_state). cbn [w_s w_c w_r].
  destruct (is_mode s3 =? TYPE); [| rewrite aret_eq; reflexivity].
  unfold set_back, aux. cbn [iv_aux ivar_ref]. rewrite us_eq. reflexivity.
Qed.

Definition len_tail (c : icall) (here : Z) (r : iregs) (sb : inflate_state) : ares unit :=
  let r' := ddrop r (code_bits here) in
  let s' := iset_length (addback sb (code_bits here)) (code_val here) in
  if code_op here =? 0 then ARun tt (mkW (iset_mode s' LIT) c r')
  else if negb (Z.land (code_op here) 32 =? 0) then ARun tt (mkW (iset_mode (iset_back s' (-1)) TYPE) c r')
  else if negb (Z.land (code_op here) 64 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_invalid_literal_length_code) r')
  else arm_LENEXT ivar_ref (mkW (iset_mode (iset_extra s' (Z.land (code_op here) 15)) LENEXT) c r').

Lemma arm_LEN_slow : forall s c r, (ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) ->
  arm_LEN ivar_ref (mkW s c r) =
    let s0 := iset_back s 0 in
    match DECODE1 (is_lencode s) (is_lenbits s) (mkW s0 c r) with
    | ARun last (mkW _ _ r1) =>
        if negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0) then
          match DECODE2 (is_lencode s) last (mkW s0 c r1) with
          | ARun here (mkW _ _ r2) => len_tail c here (ddrop r2 (code_bits last)) (addback s0 (code_bits last))
          | ALeave w => ALeave w
          | ARet rc w => ARet rc w
          end
        else len_tail c last r1 s0
    | ALeave w => ALeave w
    | ARet rc w => ARet rc w
    end.
Proof.
  intros s c r Hslow. unfold arm_LEN. mstep1 (@gr_eq iregs).
  cbn [iv_fast ivar_ref].
  replace (true && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false
    by (symmetry; destruct Hslow as [H|[H|H]];
        [ rewrite (proj2 (Z.leb_gt _ _) H); reflexivity
        | rewrite (proj2 (Z.leb_gt 258 _) H); destruct (6 <=? ir_have r); reflexivity
        | rewrite (proj2 (Z.ltb_ge _ _) H); destruct (6 <=? ir_have r), (258 <=? ir_left r); reflexivity ]).
  unfold set_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 (@gs_eq inflate_state).
  cbn [is_lencode is_lenbits iset_back]. cbv zeta. rewrite abind_run.
  destruct (DECODE1 (is_lencode s) (is_lenbits s) (mkW (iset_back s 0) c r)) as [last [s1 c1 r1] | w | rc w] eqn:H1; try reflexivity.
  destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H1) as [-> ->].
  rewrite abind_run.
  destruct (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)).
  - rewrite abind_run.
    destruct (DECODE2 (is_lencode s) last (mkW (iset_back s 0) c r1)) as [here [s2 c2 r2] | w | rc w] eqn:H2; try reflexivity.
    destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H2) as [-> ->].
    mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. rewrite aret_eq. cbv beta iota.
    mstep1 DROPBITS_eq. mstep1 us_eq. mstep1 us_eq. unfold len_tail, ddrop, addback. cbn [ir_hold ir_bits irset_bits irset_hold is_back iset_back].
    destruct (code_op here =? 0); [rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op here) 32 =? 0)); [mstep1 us_eq; rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op here) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
  - rewrite aret_eq. cbv beta iota. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 us_eq.
    unfold len_tail, ddrop, addback.
    destruct (code_op last =? 0); [rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op last) 32 =? 0)); [mstep1 us_eq; rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op last) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LEN__eq : forall s c r, arm_LEN_ ivar_ref (mkW s c r) = arm_LEN ivar_ref (mkW (iset_mode s LEN) c r).
Proof. intros. unfold arm_LEN_. mstep1 set_mode_eq. reflexivity. Qed.


Lemma len_okb_fast : forall s c r, len_okb (mkW s c r) = true -> 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  0 <= is_lenbits s <= 15 /\ 0 <= is_distbits s <= 15 /\ lenfast_okb (mkW s c r) = true.
Proof.
  intros s c r H Hh Hl Hb. unfold len_okb in H. cbn [w_s w_r w_c] in H.
  rewrite (proj2 (Z.leb_le _ _) Hh), (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hb) in H. cbn [andb] in H.
  destruct (Z.leb_spec 0 (is_lenbits s)); [| discriminate H]. destruct (Z.leb_spec (is_lenbits s) 15); [| discriminate H].
  destruct (Z.leb_spec 0 (is_distbits s)); [| discriminate H]. destruct (Z.leb_spec (is_distbits s) 15); [| discriminate H].
  cbn [andb] in H. repeat split; try assumption.
Qed.

Lemma len_okb_slow : forall s c r, len_okb (mkW s c r) = true -> (ir_have r < 6 \/ ir_left r < 258) ->
  0 <= is_lenbits s <= 15 /\ 0 <= is_distbits s <= 15 /\ decode_okb len_two s c r (is_lencode s) (is_lenbits s) = true.
Proof.
  intros s c r H Hslow. unfold len_okb in H. cbn [w_s w_r w_c] in H.
  replace ((6 <=? ir_have r) && (258 <=? ir_left r)) with false in H
    by (symmetry; destruct Hslow as [X|X]; [rewrite (proj2 (Z.leb_gt _ _) X); reflexivity | rewrite (proj2 (Z.leb_gt 258 _) X); destruct (6 <=? ir_have r); reflexivity]).
  destruct (Z.leb_spec 0 (is_lenbits s)); [| discriminate H]. destruct (Z.leb_spec (is_lenbits s) 15); [| discriminate H].
  destruct (Z.leb_spec 0 (is_distbits s)); [| discriminate H]. destruct (Z.leb_spec (is_distbits s) 15); [| discriminate H].
  cbn [andb] in H. repeat split; try assumption.
Qed.

Lemma lenfast_okb_sound : forall s c r, lenfast_okb (mkW s c r) = true ->
  let wR := RESTORE (mkW s c r) in
  ff_ok (w_s wR) (w_c wR) (w_r wR) = true
  /\ let c1 := w_c (inflate_fast wR) in
     0 <= ic_next_in c1 /\ 0 <= ic_avail_in c1 /\ ic_next_in c1 + ic_avail_in c1 = arr_len (ic_input c)
     /\ 0 <= ic_next_out c1 /\ 0 <= ic_avail_out c1 /\ ic_next_out c1 + ic_avail_out c1 = arr_len (ic_outbuf c).
Proof.
  intros s c r H. unfold lenfast_okb in H. cbn [w_c] in H. cbv zeta.
  destruct (ff_ok _ _ _); [| discriminate H]. cbn [andb] in H.
  repeat match type of H with (?a && ?b) = true => apply andb_prop in H; destruct H as [H ?X] end.
  repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X end.
  repeat split; assumption.
Qed.

Lemma LOAD_eq : forall s c r,
  LOAD (mkW s c r) = mkW s c (mkIR (ic_next_in c) (ic_avail_in c) (ic_next_out c) (ic_avail_out c) (is_hold s) (is_bits s) (ir_in r) (ir_out r) (ir_ret r)).
Proof. reflexivity. Qed.
End RefInflateA_LEN1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).

Definition i2f (last h : Z) : Z := code_val last + h mod 2 ^ (code_op last + code_bits last) / 2 ^ code_bits last.

Lemma i2f_eq : forall last h, 0 <= h -> code_op last + code_bits last <= 32 -> dec_idx2 last h = i2f last h.
Proof.
  intros last h Hh Hk. unfold dec_idx2, i2f. pose proof (code_bits_range last). pose proof (code_op_range last).
  rewrite BITSv_mod by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.add_comm (code_bits last) (code_op last)). reflexivity.
Qed.

Lemma i2f_range : forall last h, code_op last <= 15 -> 0 <= i2f last h - code_val last < 2 ^ 15 /\ 0 <= i2f last h < 2 ^ 17.
Proof.
  intros last h Hlo. unfold i2f. pose proof (code_bits_range last) as Hb. pose proof (code_op_range last) as Ho. pose proof (code_val_range last) as Hv.
  set (k := code_op last + code_bits last). set (lb := code_bits last) in *.
  pose proof (Z.mod_pos_bound h (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)) as Hm.
  assert (Hq : 0 <= h mod 2 ^ k / 2 ^ lb < 2 ^ (k - lb)).
  { pose proof (Z.pow_pos_nonneg 2 lb ltac:(lia) ltac:(lia)). split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (lb + (k - lb)) with k by lia. lia. }
  assert (2 ^ (k - lb) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 15) with 32768 in *. change (2 ^ 17) with 131072. lia.
Qed.

Lemma n2_eq : forall last h2, dec_need2 last h2 = code_bits h2 + code_bits last.
Proof.
  intros last h2. unfold dec_need2. pose proof (code_bits_range last). pose proof (code_bits_range h2).
  rewrite wrap32_id by lia. lia.
Qed.

Lemma szwrap32_of_mod : forall x, szwrap 32 (x mod 2 ^ 32) = szwrap 32 x.
Proof. intros x. unfold szwrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma iwf_set_extra : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_extra st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

Lemma ddrop_facts : forall r n,
  ir_next (ddrop r n) = ir_next r /\ ir_have (ddrop r n) = ir_have r /\ ir_put (ddrop r n) = ir_put r /\ ir_left (ddrop r n) = ir_left r
  /\ ir_hold (ddrop r n) = Z.shiftr (ir_hold r) n /\ ir_bits (ddrop r n) = wrap32 (ir_bits r - n)
  /\ ir_in (ddrop r n) = ir_in r /\ ir_out (ddrop r n) = ir_out r /\ ir_ret (ddrop r n) = ir_ret r.
Proof. intros r n. unfold ddrop. destruct r; cbn; repeat split; reflexivity. Qed.


Lemma dt_s_facts : forall s B val ext,
  is_mode (dt_s s B val ext) = DISTEXT /\ is_extra (dt_s s B val ext) = ext /\ is_flags (dt_s s B val ext) = is_flags s
  /\ is_wrap (dt_s s B val ext) = is_wrap s /\ is_check (dt_s s B val ext) = is_check s
  /\ is_lens (dt_s s B val ext) = is_lens s /\ is_work (dt_s s B val ext) = is_work s /\ is_codes (dt_s s B val ext) = is_codes s
  /\ is_window (dt_s s B val ext) = is_window s /\ is_window_blk (dt_s s B val ext) = is_window_blk s
  /\ is_wsize (dt_s s B val ext) = is_wsize s /\ is_self_blk (dt_s s B val ext) = is_self_blk s /\ is_wbits (dt_s s B val ext) = is_wbits s.
Proof. intros. unfold dt_s. repeat split; reflexivity. Qed.

Lemma dt_s_iwf : forall s B val ext, - 2 ^ 31 <= B < 2 ^ 31 -> 0 <= val < 2 ^ 32 -> 0 <= ext < 2 ^ 32 -> iwf s -> iwf (dt_s s B val ext).
Proof.
  intros s B val ext HB Hv He H. unfold dt_s. apply iwf_set_mode; [cbv; split; discriminate|].
  apply iwf_set_extra; [exact He|]. apply iwf_set_offset; [exact Hv|]. apply iwf_set_back; [exact HB | exact H].
Qed.

Lemma land15_mod : forall a, Z.land a 15 = a mod 2 ^ 4.
Proof. intros a. change 15 with (Z.ones 4). apply Z.land_ones. lia. Qed.

Section ArmDIST2.
  Variable arm_ok : Z -> iw -> bool.
End ArmDIST2.
