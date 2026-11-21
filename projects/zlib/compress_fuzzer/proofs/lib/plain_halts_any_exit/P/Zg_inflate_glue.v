(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_updwin_pure Zg_updwin_pure Z_infl_top_pure Zg_zlib_iface Z_inflate_glue.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate HarnessSmall RefZApi RefInflateRel RefInflateSafeD RefInflateSafeTY RefInflateSafeTY2
  RefInflateEqS RefInflate_runA InflateCall InflateFrameIn ZApiInst ZTaintI RefUpdWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma W0_PATG : forall X s zc,
  PATIq s -> ix_input X = arr_of_list (zc_input zc) -> zlength (zc_input zc) < 2^31 ->
  zc_avail_out zc = Z.of_nat (length (ix_rest0 X)) -> Z.of_nat (length (ix_rest0 X)) < 2^31 ->
  (is_window_blk s <> None <-> ix_hasw X = true) ->
  PATG X (W0 s zc).
Proof.
  intros X s zc (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) EIN LIN EAO LR0 HW.
  assert (EM : is_mode (s_entry s) = (if is_mode s =? TYPE then TYPEDO else is_mode s)) by (destruct (s_entry_facts s) as (_&_&_&_&_&_&_&_&_&_&E&_); exact E).
  assert (EQ : forall A (f : inflate_state -> A), (forall x v, f (iset_mode x v) = f x) -> f (s_entry s) = f s).
  { intros A f Hf. unfold s_entry. destruct (is_mode s =? TYPE); [apply Hf| reflexivity]. }
  unfold PATG, W0, OBYT, ISR. cbn [w_s w_c w_r ir_put ir_out ir_left ic_input ic_outbuf icall_of_zcall].
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

Lemma zi_stepG : forall s_a x comprc ain aout gw ok,
  IREL s_a x -> ATY s_a -> ZC (zi_zcall comprc x ain aout) ->
  let zc := zi_zcall comprc x ain aout in
  let r_a := inflate_p (wans_g gw ok) s_a zc Z_NO_FLUSH in
  let zr := snd (fst r_a) in
  exists s_c', zi_inflate comprc x ain aout ok = (mkIZ s_c' (zr_strm zr), zlength (zc_input zc) - zr_consumed zr, aout - zlength (zr_output zr), zr_output zr, zr_rc zr)
               /\ IREL (fst (fst r_a)) (mkIZ s_c' (zr_strm zr)) /\ ATY (fst (fst r_a))
               /\ zi_wantsG comprc x ain aout = snd (inflate_p (wans_g gw true) s_a zc Z_NO_FLUSH).
Proof.
  intros s_a x comprc ain aout gw ok HI HA HZ. cbv zeta.
  pose proof (IREL_step s_a x (zi_zcall comprc x ain aout) gw ok Z_NO_FLUSH HI HZ) as (E1 & _ & E3). cbv zeta in E1, E3.
  pose proof (IREL_step s_a x (zi_zcall comprc x ain aout) gw true Z_NO_FLUSH HI HZ) as (_ & E2' & _). cbv zeta in E2'.
  unfold zi_inflate, zi_wantsG.
  destruct (inflate_p (wans ok) (iz_s x) (zi_zcall comprc x ain aout) Z_NO_FLUSH) as [[s_c' zr_c] ask_c] eqn:EC. cbn [fst snd] in E1, E3.
  exists s_c'. rewrite <- E1. split; [reflexivity|]. split; [rewrite E1; exact E3|]. split; [|symmetry; exact E2'].
  destruct HI as (_ & _ & INVa & _).
  pose proof (inflate_p_pure (wans_g gw ok) s_a (zi_zcall comprc x ain aout) Z_NO_FLUSH (RefInflateSafeS2.INV_check _ INVa)) as PP.
  destruct (fst (inflate_p (wans_g gw ok) s_a (zi_zcall comprc x ain aout) Z_NO_FLUSH)) as [sa' zra] eqn:EA. cbn [fst].
  exact (inflate_aty s_a _ _ _ sa' zra INVa HA PP).
Qed.

Lemma sA_facts : forall s, is_wbits s = 15 -> (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  is_wsize (sA s) = 32768 /\ 0 <= is_wnext (sA s) < 32768 /\ 0 <= is_whave (sA s) <= 32768 /\ is_window (sA s) = is_window s.
Proof.
  intros s Hb Hws Hwn Hwh. unfold sA, uw_wnext0, uw_whave0 in *. destruct (Z.eqb_spec (is_wsize s) 0) as [E|NE].
  - destruct s; cbn -[Z.le Z.lt shl32] in *. rewrite Hb. change (shl32 1 15) with 32768. repeat split; try lia; reflexivity.
  - rewrite (Hws NE). repeat split; try lia; reflexivity.
Qed.

Lemma updw_core_wbytes : forall s src e copy,
  is_wbits s = 15 -> (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 -> 0 <= copy < 2^32 ->
  (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256) ->
  (forall j, e - copy <= j < e -> 0 <= arr_get src j < 256) ->
  forall i, 0 <= i < arr_len (is_window (updw_core s src e copy)) -> 0 <= arr_get (is_window (updw_core s src e copy)) i < 256.
Proof.
  intros s src e copy Hb Hws Hwn Hwh HC HW HS.
  rewrite (updw_core_sA s src e copy Hb). destruct (sA_facts s Hb Hws Hwn Hwh) as (A1 & A2 & A3 & A4).
  set (s1 := sA s) in *. rewrite <- A4 in HW.
  destruct (Z.le_gt_cases 32768 copy) as [HF|HF].
  { rewrite (updw_full s1 src e copy A1 HF). unfold uw_set. destruct s1; cbn -[Z.le Z.lt Z.add Z.sub arr_blit arr_get arr_len] in *.
    apply window_blit_bytes; [exact HW| intros j Hj; apply HS; lia]. }
  destruct (Z.le_gt_cases copy (32768 - is_wnext s1)) as [HA|HA].
  { rewrite (updw_app s1 src e copy A1 A2 A3 ltac:(lia) HA). unfold uw_set. destruct s1; cbn -[Z.le Z.lt Z.add Z.sub Z.eqb Z.ltb arr_blit arr_get arr_len] in *.
    apply window_blit_bytes; [exact HW| intros j Hj; apply HS; lia]. }
  rewrite (updw_wrap s1 src e copy A1 A2 ltac:(lia) ltac:(lia)). unfold uw_set. destruct s1; cbn -[Z.le Z.lt Z.add Z.sub arr_blit arr_get arr_len] in *.
  apply window_blit_bytes; [| intros j Hj; apply HS; lia]. apply window_blit_bytes; [exact HW| intros j Hj; apply HS; lia].
Qed.

Lemma updw_core_facts : forall s src e copy,
  is_wbits s = 15 -> (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 -> 0 <= copy < 2^32 ->
  (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256) ->
  (forall j, e - copy <= j < e -> 0 <= arr_get src j < 256) ->
  let s' := updw_core s src e copy in
  is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s /\ is_head s' = is_head s /\ is_flags s' = is_flags s
  /\ is_mode s' = is_mode s /\ is_last s' = is_last s /\ is_havedict s' = is_havedict s
  /\ (forall i, 0 <= i < arr_len (is_window s') -> 0 <= arr_get (is_window s') i < 256)
  /\ is_window_blk s' = is_window_blk s.
Proof.
  intros s src e copy Hb Hws Hwn Hwh HC HW HS. cbv zeta.
  pose proof (updw_core_wbytes s src e copy Hb Hws Hwn Hwh HC HW HS) as WB.
  rewrite (updw_core_shape s src e copy) in WB |- *. unfold uw_set in WB |- *.
  destruct s; cbn -[Z.le Z.lt Z.add Z.sub arr_get arr_len updw_core] in WB |- *.
  repeat (split; [reflexivity|]). split; [exact WB| reflexivity].
Qed.

Lemma PATIq_of_PATG : forall X s c r s_f, PATG X (mkW s c r) ->
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
