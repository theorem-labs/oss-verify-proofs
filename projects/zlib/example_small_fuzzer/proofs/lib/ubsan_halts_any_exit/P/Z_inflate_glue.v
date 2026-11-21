(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_updwin_pure Z_infl_top_pure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate HarnessSmall RefZApi RefInflateRel RefInflateSafeD RefInflateSafeTY RefInflateSafeTY2 RefInflateEqS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InflateCall InflateFrameIn ZApiInst ZTaintI.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefZApi OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateEqS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateCall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateFrameIn OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaintI.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma W0_PATI : forall X s zc,
  PATIq s -> ix_input X = arr_of_list (zc_input zc) -> zlength (zc_input zc) <= 1 ->
  zc_avail_out zc = Z.of_nat (length (ix_rest0 X)) -> (length (ix_rest0 X) <= 1)%nat ->
  (is_window_blk s <> None <-> ix_hasw X = true) ->
  PATI X (W0 s zc).
Proof.
  intros X s zc (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) EIN LIN EAO LR0 HW.
  assert (EM : is_mode (s_entry s) = (if is_mode s =? TYPE then TYPEDO else is_mode s)) by (destruct (s_entry_facts s) as (_&_&_&_&_&_&_&_&_&_&E&_); exact E).
  assert (EQ : forall A (f : inflate_state -> A), (forall x v, f (iset_mode x v) = f x) -> f (s_entry s) = f s).
  { intros A f Hf. unfold s_entry. destruct (is_mode s =? TYPE); [apply Hf| reflexivity]. }
  unfold PATI, W0, OBYT, ISR. cbn [w_s w_c w_r ir_put ir_out ir_left ic_input ic_outbuf icall_of_zcall].
  rewrite (EQ _ is_wrap), (EQ _ is_wbits), (EQ _ is_head), (EQ _ is_flags), (EQ _ is_window_blk), (EQ _ is_last), (EQ _ is_havedict), (EQ _ is_window) by reflexivity.
  rewrite EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & HM)]; [left; exact F0| right]. split; [exact F1|]. split; [|split; reflexivity].
           destruct HM as [E|E]; rewrite E; [left| right]; reflexivity. }
  split. { destruct (Z.eqb_spec (is_mode s) TYPE) as [E|E]; [unfold TYPEDO, FLAGS, HCRC; lia| exact P5]. }
  split; [exact (proj1 HW)|]. split; [symmetry; exact EIN|]. split; [rewrite EIN, arr_len_of_list; exact LIN|].
  split; [unfold arr_make; rewrite arr_len_init; exact EAO|]. split; [exact LR0|].
  split; [split; assumption|].
  split; [intros i Hi; lia|]. split; [exact P8|]. split; [lia|]. split; [unfold NOPUTb; apply andb_false_r| exact (proj2 HW)].
Qed.

Lemma W0_FI : forall s zc,
  FI (zs_total_in (zc_strm zc)) (zlength (zc_input zc)) (zlength (zc_input zc)) (W0 s zc).
Proof.
  intros s zc. unfold FI, W0. cbn [w_c w_r ic_total_in ir_in ic_input ir_ret icall_of_zcall].
  rewrite arr_len_of_list. unfold Z_OK. repeat split; lia.
Qed.

Lemma zi_step : forall s_a x comprc gw ok,
  IREL s_a x -> ATY s_a -> ZC (zi_zcall comprc x 1 1) ->
  let zc := zi_zcall comprc x 1 1 in
  let r_a := inflate_p (wans_g gw ok) s_a zc Z_NO_FLUSH in
  let zr := snd (fst r_a) in
  exists s_c', zi_inflate comprc x 1 1 ok = (mkIZ s_c' (zr_strm zr), zlength (zc_input zc) - zr_consumed zr, 1 - zlength (zr_output zr), zr_output zr, zr_rc zr)
               /\ IREL (fst (fst r_a)) (mkIZ s_c' (zr_strm zr)) /\ ATY (fst (fst r_a))
               /\ zi_wants_window comprc x = snd (inflate_p (wans_g gw true) s_a zc Z_NO_FLUSH).
Proof.
  intros s_a x comprc gw ok HI HA HZ. cbv zeta.
  pose proof (IREL_step s_a x (zi_zcall comprc x 1 1) gw ok Z_NO_FLUSH HI HZ) as (E1 & _ & E3). cbv zeta in E1, E3.
  pose proof (IREL_step s_a x (zi_zcall comprc x 1 1) gw true Z_NO_FLUSH HI HZ) as (_ & E2' & _). cbv zeta in E2'.
  unfold zi_inflate, zi_wants_window.
  destruct (inflate_p (wans ok) (iz_s x) (zi_zcall comprc x 1 1) Z_NO_FLUSH) as [[s_c' zr_c] ask_c] eqn:EC. cbn [fst snd] in E1, E3.
  exists s_c'. rewrite <- E1. split; [reflexivity|]. split; [rewrite E1; exact E3|]. split; [|symmetry; exact E2'].
  destruct HI as (_ & _ & INVa & _).
  pose proof (inflate_p_pure (wans_g gw ok) s_a (zi_zcall comprc x 1 1) Z_NO_FLUSH (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.INV_check _ INVa)) as PP.
  destruct (fst (inflate_p (wans_g gw ok) s_a (zi_zcall comprc x 1 1) Z_NO_FLUSH)) as [sa' zra] eqn:EA. cbn [fst].
  exact (inflate_aty s_a _ _ _ sa' zra INVa HA PP).
Qed.


Lemma final_leave_facts : forall s c r TI0 TOT0 NO,
  REGS c r -> BK NO TOT0 (mkW s c r) -> ic_total_in c = TI0 -> ir_in r = arr_len (ic_input c) ->
  0 <= TI0 -> TI0 + arr_len (ic_input c) < 2 ^ 64 -> 0 <= TOT0 -> TOT0 + NO < 2 ^ 64 ->
  let c1 := snd (lv_pre (s_rest s r) (c_rest c r) r) in
  ic_next_in c1 = ir_next r /\ ic_avail_in c1 = ir_have r /\ ic_next_out c1 = ir_put r /\ ic_avail_out c1 = ir_left r
  /\ ic_total_in c1 = TI0 + ir_next r /\ ic_total_out c1 = TOT0 + ir_put r
  /\ ic_outbuf c1 = ic_outbuf c /\ ic_input c1 = ic_input c.
Proof.
  intros s c r TI0 TOT0 NO HR (B1 & _ & _ & BC) ETI EIN R1 R2 R3 R4. cbv zeta.
  destruct HR as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & _ & Rli & Rlo).
  rewrite lv_pre_shape. cbv zeta. cbn [snd].
  assert (EI : wrap32 (ir_in r - ic_avail_in (c_rest c r)) = ir_next r).
  { unfold c_rest. cbn [ic_avail_in icset_avail_in]. rewrite EIN, <- Rnh. replace (ir_next r + ir_have r - ir_have r) with (ir_next r) by lia. apply wrap32_id. lia. }
  assert (EO : wrap64 (ic_total_out (c_rest c r) + wrap32 (ir_out r - ic_avail_out (c_rest c r))) = TOT0 + ir_put r).
  { unfold c_rest. cbn [ic_total_out ic_avail_out icset_avail_in icset_next_in icset_avail_out icset_next_out].
    destruct BC as [(A1 & A2)|(A1 & A2 & _)]; cbn [w_c w_r] in A1, A2.
    - rewrite A1, A2, <- B1. cbn [w_c]. rewrite <- Rpl. replace (ir_put r + ir_left r - ir_left r) with (ir_put r) by lia.
      rewrite (wrap32_id (ir_put r)) by lia. apply wrap64_id. cbn [w_c] in B1. lia.
    - rewrite A1, A2, Z.sub_diag. change (wrap32 0) with 0. rewrite Z.add_0_r. cbn [w_c] in B1. rewrite <- B1 in R4. rewrite <- Rpl in R4.
      rewrite (wrap64_id (TOT0 + ir_put r)) by lia. apply wrap64_id. lia. }
  rewrite EI.
  destruct (negb (Z.land (is_wrap (s_rest s r)) 4 =? 0) && negb (wrap32 (ir_out r - ic_avail_out (c_rest c r)) =? 0));
    unfold c_rest in *; cbn [ic_next_in ic_avail_in ic_next_out ic_avail_out ic_total_in ic_total_out ic_outbuf ic_input
                              icset_data_type icset_adler icset_total_out icset_total_in icset_avail_in icset_next_in icset_avail_out icset_next_out] in *;
    rewrite ?EO, ETI; (repeat split; try reflexivity); apply wrap64_id; lia.
Qed.

Lemma window_blit_bytes : forall (win src : arr) d so n,
  (forall i, 0 <= i < arr_len win -> 0 <= arr_get win i < 256) -> (forall j, so <= j < so + n -> 0 <= arr_get src j < 256) ->
  forall i, 0 <= i < arr_len (arr_blit win d src so n) -> 0 <= arr_get (arr_blit win d src so n) i < 256.
Proof.
  intros win src d so n HW HS i Hi. rewrite arr_len_blit in Hi. rewrite arr_get_blit.
  destruct ((d <=? i) && (i <? d + Z.max 0 n) && arr_inb win i) eqn:E; [|apply HW; exact Hi].
  apply andb_prop in E. destruct E as [E _]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply HS. lia.
Qed.

Lemma PATIq_of_PATI : forall X s c r s_f, PATI X (mkW s c r) ->
  is_wrap s_f = is_wrap s -> is_wbits s_f = is_wbits s -> is_head s_f = is_head s -> is_flags s_f = is_flags s ->
  (is_mode s_f = is_mode s \/ (is_mode s_f = MEM /\ is_flags s = 0)) -> is_last s_f = is_last s -> is_havedict s_f = is_havedict s ->
  (forall i, 0 <= i < arr_len (is_window s_f) -> 0 <= arr_get (is_window s_f) i < 256) -> PATIq s_f.
Proof.
  intros X s c r s_f (P1 & P2 & P3 & P4 & P5 & _ & _ & _ & _ & _ & [P11 P12] & _) E1 E2 E3 E4 E5 E6 E7 HWB. cbn [w_s w_r] in *.
  unfold PATIq. rewrite E1, E2, E3, E4, E6, E7. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & HM & _)]; [left; exact F0|]. destruct E5 as [E5|(_ & E5)]; [right; rewrite E5; split; assumption| left; exact E5]. }
  split. { destruct E5 as [E5|(E5 & _)]; rewrite E5; [exact P5| unfold MEM, FLAGS, HCRC; lia]. }
  split; [exact P11|]. split; [exact P12| exact HWB].
Qed.
