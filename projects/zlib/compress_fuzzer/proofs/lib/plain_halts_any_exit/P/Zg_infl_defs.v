(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_c_defs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PATG (X : ictx) (w : iw) : Prop :=
  let s := w_s w in let r := w_r w in
  is_wrap s = 5 /\ is_wbits s = 15 /\ is_head s = 0
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_put r = 0 /\ ir_out r = ir_left r))
  /\ ~ (FLAGS <= is_mode s <= HCRC)
  /\ (is_window_blk s <> None -> ix_hasw X = true)
  /\ ic_input (w_c w) = ix_input X /\ arr_len (ix_input X) < 2^31
  /\ arr_len (ic_outbuf (w_c w)) = Z.of_nat (length (ix_rest0 X)) /\ Z.of_nat (length (ix_rest0 X)) < 2^31
  /\ ISR s
  /\ OBYT X w.

Lemma PATG_regs : forall X s c r r1, PATG X (mkW s c r) ->
  ir_put r1 = ir_put r -> ir_out r1 = ir_out r -> ir_left r1 = ir_left r -> PATG X (mkW s c r1).
Proof. intros X s c r r1 H E1 E2 E3. unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3. exact H. Qed.

Lemma PATG_noput : forall X s c r, PATG X (mkW s c r) -> NOPUTb (is_mode s) (ir_put r) = false.
Proof. intros X s c r (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & H & _)). exact H. Qed.

Lemma PATG_step_out : forall X s c r s' c' r', PATG X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  0 <= ir_out r' - ir_left r' <= ir_put r' -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16)) E1 E2 E3 E4 NG E6 E7 E8 E9 E10 HO HN HI.
  unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E10. rewrite E9 in *.
  repeat (split; [first [assumption | left; assumption]|]). assumption.
Qed.

Lemma PATG_step : forall X s c r s' c' r', PATG X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' HP E1 E2 E3 E4 NG E6 E7 E8 E9 E10 E11 E12 HN HI.
  eapply PATG_step_out; try eassumption. rewrite E9, E11, E12.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H & _)). exact H.
Qed.

Lemma PATG_step_put : forall X s c r s' c' r' v, PATG X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = arr_set (ic_outbuf c) (ir_put r) v -> 0 <= v < 256 -> 0 <= ir_put r < arr_len (ic_outbuf c) ->
  ir_put r' = ir_put r + 1 -> is_window s' = is_window s ->
  0 <= ir_out r' - ir_left r' <= ir_put r' -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' v (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16)) E1 E2 E3 E4 NG E6 E7 E8 Hv Hp E9 E10 HO HN HI.
  unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E9, E10. rewrite E9 in HO. rewrite arr_len_set.
  repeat (split; [first [assumption | left; assumption]|]).
  split; [|split; [exact P13| split; [exact HO| split; [rewrite <- E9; exact HN| exact P16]]]].
  intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
  - rewrite arr_get_set_same by lia. exact Hv.
  - rewrite arr_get_set_other by lia. apply P12. lia.
Qed.

Lemma PATG_step_bad : forall X s c r s' c' r', PATG X (mkW s c r) -> is_mode s = HEAD ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_mode s' = BAD -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> ISR s' -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & P14 & P15 & P16)) HM E1 E2 E3 E4 EM E6 E7 E8 E9 E10 E11 E12 HI.
  unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E10, E11, E12, EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & _ & F3 & F4)]; [left; exact F0| right; split; [exact F1|]; split; [right; reflexivity|]; split; assumption]. }
  split; [unfold BAD, FLAGS, HCRC; lia|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|].
  split; [exact HI|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [reflexivity| exact P16].
Qed.

Definition arm_stmtg (flush M PC : Z) (arm : AM unit) : Prop := forall X w x12 ms,
  ix_flush X = flush -> ILOOP X w PC (wz (-3)) x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = M ->
  evt psegs (fun ms' => IPOST X (arm w) ms' /\ PATG X (wof (arm w))) ms.

Definition NBG (X : ictx) (s : inflate_state) (c : icall) (RES : ares unit) (pcj : Z) (Q : iregs -> iscr -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun tt (mkW s c r1) /\ ILOOPg X (mkW s c r1) pcj q ms' /\ Q r1 q)
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

Definition NBGo (X : ictx) (s : inflate_state) (c : icall) (RES : ares unit) (pcj : Z) (x8 : word) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 x12, RES = ARun tt (mkW s c r1) /\ ILOOP X (mkW s c r1) pcj x8 x12 ms')
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

Definition NBG27 (X : ictx) (s : inflate_state) (c : icall) (RES : ares unit) (pcj : Z) (x8 : word) (x26 : iregs -> word) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 x12, RES = ARun tt (mkW s c r1) /\ ILOOP27 X (mkW s c r1) pcj x8 x12 (x26 r1) ms')
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

Definition NBGh (X : ictx) (s : inflate_state) (c : icall) (r0 : iregs) (RES : ares unit) (n : Z) (pcj : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun tt (mkW s c r1)
                  /\ ILOOPh X (mkW s c r0) pcj q ms'
                  /\ h12 q = wz (ir_have r1) /\ h13 q = wz n /\ h14 q = wz (ir_bits r1) /\ h15 q = wz (il_NI (ix_L X) + ir_next r1)
                  /\ h22 q = wz (ir_hold r1) /\ h29 q = wz 30 /\ h31 q = wz (-16180))
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

Lemma NBG_run_facts : forall c n s r r1, REGS c r -> 0 <= n <= 48 ->
  NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1) ->
  REGS c r1 /\ pulled r r1 /\ n <= ir_bits r1 /\ (ir_bits r1 = ir_bits r \/ ir_bits r1 < n + 8).
Proof.
  intros c n s r r1 HR Hn E.
  destruct (NEEDBITS_spec c n s r HR Hn) as [(r' & E' & H1 & H2 & H3 & H4)|(r' & E' & _)]; rewrite E in E'; [|discriminate E'].
  injection E' as <-. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.
Lemma NBG_leave_facts : forall c n s r r1, REGS c r -> 0 <= n <= 48 ->
  NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) ->
  REGS c r1 /\ pulled r r1 /\ ir_bits r1 < n /\ ir_have r1 = 0.
Proof.
  intros c n s r r1 HR Hn E.
  destruct (NEEDBITS_spec c n s r HR Hn) as [(r' & E' & _)|(r' & E' & H1 & H2 & H3 & H4)]; rewrite E in E'; [discriminate E'|].
  injection E' as <-. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma pulled_eqs : forall r r1, pulled r r1 ->
  ir_put r1 = ir_put r /\ ir_left r1 = ir_left r /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r.
Proof. intros r r1 (k & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma pulled_cursor : forall r r1, pulled r r1 ->
  ir_next r1 + ir_have r1 = ir_next r + ir_have r /\ ir_bits r1 + 8 * ir_have r1 = ir_bits r + 8 * ir_have r
  /\ ir_next r <= ir_next r1 /\ 0 <= ir_have r1 <= ir_have r /\ ir_bits r <= ir_bits r1.
Proof. intros r r1 (k & Hk & E1 & E2 & H0 & E3 & _). rewrite E1, E2, E3. lia. Qed.

Lemma nbG_r1_facts : forall c r r1 n, REGS c r1 -> pulled r r1 -> n <= ir_bits r1 ->
  ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r
  /\ n <= ir_bits r1 <= 63 /\ 0 <= ir_hold r1 < 2^64 /\ 0 <= ir_have r1 < 2^32 /\ 0 <= ir_next r1.
Proof.
  intros c r r1 n (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo) HP Hn.
  destruct (pulled_eqs _ _ HP) as (E1 & E2 & E3 & E4 & E5).
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  repeat split; try assumption; lia.
Qed.

Lemma PATG_pulled : forall X s c r r1, PATG X (mkW s c r) -> pulled r r1 -> PATG X (mkW s c r1).
Proof. intros X s c r r1 HP HQ. destruct (pulled_eqs _ _ HQ) as (E1 & E2 & _ & E4 & _). eapply PATG_regs; [exact HP| assumption..]. Qed.

Lemma pullr_SafeH : RefInflateSafeH.pullr = RefInflateArmLib.pullr.
Proof. reflexivity. Qed.

Lemma pull_step : forall c r0 r, REGS c r -> 0 <= ir_bits r0 -> pulled r0 r -> 0 < ir_have r -> ir_bits r <= 55 ->
  let r' := RefInflateArmLib.pullr c r in
  REGS c r' /\ pulled r0 r'
  /\ ir_next r' = ir_next r + 1 /\ ir_have r' = ir_have r - 1
  /\ ir_hold r' = ir_hold r + arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r /\ ir_bits r' = ir_bits r + 8
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r
  /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r
  /\ 0 <= ir_hold r' < 2 ^ (ir_bits r + 8).
Proof.
  intros c r0 r HR HB0 HP Hh Hb. rewrite <- pullr_SafeH. cbv zeta.
  pose proof HR as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  destruct (REGS_pullr c r HR Hh Hb) as (HR1 & HP1 & EB & EH).
  destruct (pullr_facts c r Hh ltac:(lia) Rli ltac:(lia) RH (Rin _)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  split; [exact HR1|]. split; [exact (pulled_trans r0 r (pullr c r) HB0 HP HP1)|].
  split; [exact E1|]. split; [exact E2|]. split; [exact E5|]. split; [exact E6|]. split; [exact E3|]. split; [exact E4|].
  split; [exact E7|]. split; [exact E8|]. split; [exact E9| exact E10].
Qed.

Lemma NB_dry : forall f n s c r, ir_bits r < n -> ir_have r = 0 -> NEEDBITS_k (S f) n (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros f n s c r Hb Hh. rewrite NEEDBITS_k_S.
  rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.eqb_eq _ _) Hh). reflexivity.
Qed.
Lemma NB_pull : forall f n s c r, ir_bits r < n -> ir_have r <> 0 ->
  NEEDBITS_k (S f) n (mkW s c r) = NEEDBITS_k f n (mkW s c (RefInflateArmLib.pullr c r)).
Proof.
  intros f n s c r Hb Hh. rewrite RefInflateArmLib.NEEDBITS_k_S.
  rewrite (proj2 (Z.ltb_lt _ _) Hb), (proj2 (Z.eqb_neq _ _) Hh). reflexivity.
Qed.
Lemma NB_done : forall f n s c r, n <= ir_bits r -> NEEDBITS_k f n (mkW s c r) = ARun tt (mkW s c r).
Proof. intros. apply NEEDBITS_k_done. assumption. Qed.
Lemma NB_top : forall n w, NEEDBITS n w = NEEDBITS_k 8 n w.
Proof. reflexivity. Qed.

Lemma nbG_pull_ok : forall n s c r, 0 < ir_have r -> 0 <= ir_bits r <= 56 -> ir_bits r < n <= ir_bits r + 8 ->
  NEEDBITS n (mkW s c r) = ARun tt (mkW s c (RefInflateArmLib.pullr c r)).
Proof.
  intros n s c r Hh Hb Hn. rewrite NB_top, (NB_pull 7 n s c r) by lia. apply NB_done.
  unfold RefInflateArmLib.pullr. cbn [ir_bits]. rewrite wrap32_id by lia. lia.
Qed.

Lemma zx32_small : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. Qed.

Lemma REGS_hold64 : forall c r, REGS c r -> 0 <= ir_hold r < 2^64.
Proof.
  intros c r (_ & _ & _ & _ & _ & _ & [RB RH] & _).
  split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia.
Qed.
