(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_infl_top_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_updwin_pure Z_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate HarnessSmall RefZApi RefInflateRel RefInflateSafeD RefInflateSafeTY RefInflateSafeTY2
  RefInflateEqS RefInflate_runA InflateCall InflateFrameIn ZApiInst ZTaintI.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Lemma W0_FI : forall s zc,
  FI (zs_total_in (zc_strm zc)) (zlength (zc_input zc)) (zlength (zc_input zc)) (W0 s zc).
Proof.
  intros s zc. unfold FI, W0. cbn [w_c w_r ic_total_in ir_in ic_input ir_ret icall_of_zcall].
  rewrite arr_len_of_list. unfold Z_OK. repeat split; lia.
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


