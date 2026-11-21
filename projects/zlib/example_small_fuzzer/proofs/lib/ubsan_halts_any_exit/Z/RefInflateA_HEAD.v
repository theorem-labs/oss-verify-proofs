(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition drop4 (r : iregs) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) 4)) (wrap32 (ir_bits r - 4)).
Definition hd_ok_s (s : inflate_state) (len : Z) : inflate_state := iset_check (iset_flags (iset_dmax s (shl32 1 len)) 0) iadler32_init.
Definition hd_gz_s (s : inflate_state) (hold : Z) : inflate_state :=
  iset_check (iset_check s icrc32_init) (icrc32_upd icrc32_init [wrap8 hold; wrap8 (Z.shiftr hold 8)]).

Definition hd_zres (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
  let hold := ir_hold r1 in
  if (Z.land (is_wrap s) 1 =? 0) || negb (wrap64 (shl32 (BITSv hold 8) 8 + Z.shiftr hold 8) mod 31 =? 0) then
    ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_incorrect_header_check) r1)
  else if negb (BITSv hold 4 =? Z_DEFLATED) then
    ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_unknown_compression_method) r1)
  else
    let r2 := drop4 r1 in
    let len := BITSv (ir_hold r2) 4 + 8 in
    if (15 <? len) || (is_wbits s <? len) then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_window_size) r2)
    else ARun tt (mkW (iset_mode (hd_ok_s s len) (if negb (Z.land (ir_hold r2) 512 =? 0) then DICTID else TYPE)) (icset_adler c iadler32_init) (r00 r1)).
Definition hd_res (s : inflate_state) (c : icall) (r1 : iregs) : ares unit :=
  if negb (Z.land (is_wrap s) 2 =? 0) && (ir_hold r1 =? 35615) then
    ARun tt (mkW (iset_mode (hd_gz_s s (ir_hold r1)) FLAGS) c (r00 r1))
  else hd_zres s c r1.

Lemma r00_drop4 : forall r, r00 (drop4 r) = r00 r.
Proof. intros r. unfold r00, drop4. destruct r; reflexivity. Qed.

Lemma arm_HEAD_eq : forall s c r, is_wbits s <> 0 ->
  arm_HEAD ivar_ref (mkW s c r) =
    if is_wrap s =? 0 then ARun tt (mkW (iset_mode s TYPEDO) c r)
    else match NEEDBITS 16 (mkW s c r) with
         | ARun _ (mkW s1 c1 r1) => hd_res s1 c1 r1
         | ALeave w1 => ALeave w1
         | ARet rc w1 => ARet rc w1
         end.
Proof.
  intros s c r Hwb. unfold arm_HEAD. mstep1 (@gs_eq inflate_state).
  destruct (is_wrap s =? 0); [rewrite set_mode_eq; reflexivity|].
  rewrite abind_run. destruct (NEEDBITS 16 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; try reflexivity.
  destruct (NEEDBITS_k_run 8 16 s c r s1 c1 r1 HN) as [-> ->].
  mstep1 HOLD_eq. unfold hd_res, hd_zres. cbv zeta.
  destruct (negb (Z.land (is_wrap s) 2 =? 0) && (ir_hold r1 =? 35615)).
  - rewrite abind_run. rewrite (proj2 (Z.eqb_neq _ _) Hwb). rewrite aret_eq. cbv beta iota.
    mstep1 us_eq. unfold CRC2. mstep1 us_eq. mstep1 INITBITS_eq. rewrite set_mode_eq. reflexivity.
  - mstep1 BITS_eq.
    destruct ((Z.land (is_wrap s) 1 =? 0) || negb (wrap64 (shl32 (BITSv (ir_hold r1) 8) 8 + Z.shiftr (ir_hold r1) 8) mod 31 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 BITS_eq. destruct (negb (BITSv (ir_hold r1) 4 =? Z_DEFLATED)); [rewrite go_bad_eq; reflexivity|].
    mstep1 DROPBITS_eq. mstep1 BITS_eq. cbn [ir_hold irset_bits irset_hold]. fold (drop4 r1).
    mstep1 (@gs_eq inflate_state).
    change (ir_hold (drop4 r1)) with (Z.shiftr (ir_hold r1) 4).
    rewrite (proj2 (Z.eqb_neq _ _) Hwb). cbn [negb andb].
    destruct ((15 <? BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8) || (is_wbits s <? BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8)); [rewrite go_bad_eq; reflexivity|].
    rewrite abind_run. rewrite aret_eq. cbv beta iota.
    unfold aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 us_eq. mstep1 set_adler_check_eq. mstep1 HOLD_eq. mstep1 set_mode_eq.
    rewrite INITBITS_eq. change (irset_bits (irset_hold (drop4 r1) 0) 0) with (r00 (drop4 r1)). rewrite r00_drop4. reflexivity.
Qed.

Lemma hd_ok_s_facts : forall s l,
  is_mode (hd_ok_s s l) = is_mode s /\ is_flags (hd_ok_s s l) = 0 /\ is_wrap (hd_ok_s s l) = is_wrap s /\ is_check (hd_ok_s s l) = 1
  /\ is_lens (hd_ok_s s l) = is_lens s /\ is_work (hd_ok_s s l) = is_work s /\ is_codes (hd_ok_s s l) = is_codes s
  /\ is_window (hd_ok_s s l) = is_window s /\ is_window_blk (hd_ok_s s l) = is_window_blk s
  /\ is_wsize (hd_ok_s s l) = is_wsize s /\ is_self_blk (hd_ok_s s l) = is_self_blk s /\ is_wbits (hd_ok_s s l) = is_wbits s.
Proof. intros s l. unfold hd_ok_s. repeat split; reflexivity. Qed.
Lemma hd_gz_s_facts : forall s h,
  is_mode (hd_gz_s s h) = is_mode s /\ is_flags (hd_gz_s s h) = is_flags s /\ is_wrap (hd_gz_s s h) = is_wrap s
  /\ is_lens (hd_gz_s s h) = is_lens s /\ is_work (hd_gz_s s h) = is_work s /\ is_codes (hd_gz_s s h) = is_codes s
  /\ is_window (hd_gz_s s h) = is_window s /\ is_window_blk (hd_gz_s s h) = is_window_blk s
  /\ is_wsize (hd_gz_s s h) = is_wsize s /\ is_self_blk (hd_gz_s s h) = is_self_blk s /\ is_wbits (hd_gz_s s h) = is_wbits s.
Proof. intros s h. unfold hd_gz_s. repeat split; reflexivity. Qed.

Lemma iwf_set_dmax : forall st v, 0 <= v < 2 ^ 32 -> iwf st -> iwf (iset_dmax st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma shl32_1 : forall l, 0 <= l <= 31 -> shl32 1 l = 2 ^ l.
Proof.
  intros l Hl. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_id.
  split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.
Lemma hd_ok_s_iwf : forall s l, 8 <= l <= 15 -> iwf s -> iwf (hd_ok_s s l).
Proof.
  intros s l Hl H. unfold hd_ok_s. apply iwf_set_check; [cbv; clear; split; [discriminate | reflexivity]|].
  apply iwf_set_flags; [clear; lia|]. apply iwf_set_dmax; [| exact H].
  rewrite shl32_1 by lia. split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
Qed.
Lemma hd_gz_s_iwf : forall s h, iwf s -> iwf (hd_gz_s s h).
Proof.
  intros s h H. unfold hd_gz_s. apply iwf_set_check; [apply crc_list_range; apply wrap8_in2|].
  apply iwf_set_check; [cbv; clear; split; [discriminate | reflexivity] | exact H].
Qed.


Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_land by lia. apply Z.land_ones. lia. Qed.

Lemma div31_magic : forall x, 0 <= x < 2 ^ 64 ->
  (x * 595056260442243601 / 2 ^ 64 + (x - x * 595056260442243601 / 2 ^ 64) mod 2 ^ 64 / 2 ^ 1) / 2 ^ 4 = x / 31.
Proof.
  intros x Hx.
  assert (Hq : 0 <= x * 595056260442243601 / 2 ^ 64 <= x).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small (x - _)) by lia.
  set (q := x * 595056260442243601 / 2 ^ 64) in *.
  assert (Hd : -31 < 31 * q - x < 15).
  { subst q. change (2 ^ 64) with 18446744073709551616 in *. Z.to_euclidean_division_equations. nia. }
  change (2 ^ 1) with 2. change (2 ^ 4) with 16.
  Z.to_euclidean_division_equations. lia.
Qed.

Definition hd_x (h : Z) : Z := h mod 2 ^ 8 * 2 ^ 8 + h / 2 ^ 8.
Lemma hd_x_spec : forall h, 0 <= h < 2 ^ 64 -> wrap64 (shl32 (BITSv h 8) 8 + Z.shiftr h 8) = hd_x h.
Proof.
  intros h Hh. unfold hd_x. rewrite BITSv_mod by lia. unfold shl32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  assert (H8 : 0 <= h mod 2 ^ 8 < 2 ^ 8) by (apply Z.mod_pos_bound; lia).
  rewrite wrap32_id by (change (2 ^ 8) with 256 in *; change (2 ^ 32) with 4294967296; lia).
  apply wrap64_id. change (2 ^ 8) with 256 in *. change (2 ^ 64) with 18446744073709551616 in *.
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma hd_x_range : forall h, 0 <= h < 2 ^ 64 -> 0 <= hd_x h < 2 ^ 64.
Proof.
  intros h Hh. unfold hd_x. change (2 ^ 8) with 256. change (2 ^ 64) with 18446744073709551616 in *.
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma hd_mod31 : forall x, 0 <= x < 2 ^ 64 ->
  let t := (x * 595056260442243601 / 2 ^ 64 + (x - x * 595056260442243601 / 2 ^ 64) mod 2 ^ 64 / 2 ^ 1) / 2 ^ 4 in
  (x = (t * 2 ^ 5 - t) mod 2 ^ 64 <-> x mod 31 = 0).
Proof.
  intros x Hx. cbv zeta. rewrite div31_magic by exact Hx. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (x / 31 * 32 - x / 31)) by (change (2 ^ 64) with 18446744073709551616 in *; Z.to_euclidean_division_equations; lia).
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma drop4_facts : forall r,
  ir_next (drop4 r) = ir_next r /\ ir_have (drop4 r) = ir_have r /\ ir_put (drop4 r) = ir_put r /\ ir_left (drop4 r) = ir_left r
  /\ ir_hold (drop4 r) = Z.shiftr (ir_hold r) 4 /\ ir_bits (drop4 r) = wrap32 (ir_bits r - 4)
  /\ ir_in (drop4 r) = ir_in r /\ ir_out (drop4 r) = ir_out r /\ ir_ret (drop4 r) = ir_ret r.
Proof. intros r. unfold drop4. destruct r; repeat split; reflexivity. Qed.
Local Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Section ArmHEAD.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_HEAD : forall flush w, is_mode (w_s w) = HEAD -> arm_ok flush w = true -> leave_okb (w_s w) = true.
End ArmHEAD.
