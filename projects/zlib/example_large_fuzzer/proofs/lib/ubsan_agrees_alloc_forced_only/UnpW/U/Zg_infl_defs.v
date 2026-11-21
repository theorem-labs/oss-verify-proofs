(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Module GP := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zg_infl_defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PATG (X : ictx) (w : iw) : Prop :=
  let s := w_s w in let r := w_r w in
  is_wrap s = 5 /\ is_wbits s = 15 /\ is_head s = 0
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_put r = 0 /\ ir_out r = ir_left r))
  /\ ~ (FLAGS <= is_mode s <= HCRC)
  /\ (is_window_blk s <> None -> ix_hasw X = true)
  /\ ic_input (w_c w) = ix_input X /\ arr_len (ix_input X) < 2^31
  /\ arr_len (ic_outbuf (w_c w)) = Z.of_nat (length (ix_rest0 X)) /\ Z.of_nat (length (ix_rest0 X)) < 2^31
  /\ ISR s
  /\ OBYT X w
  /\ bk_ok s.

Lemma PATG_regs : forall X s c r r1, PATG X (mkW s c r) ->
  ir_put r1 = ir_put r -> ir_out r1 = ir_out r -> ir_left r1 = ir_left r -> PATG X (mkW s c r1).
Proof. intros X s c r r1 H E1 E2 E3. unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3. exact H. Qed.

Lemma PATG_noput : forall X s c r, PATG X (mkW s c r) -> NOPUTb (is_mode s) (ir_put r) = false.
Proof. intros X s c r (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & H & _) & _). exact H. Qed.

Lemma PATG_bk : forall X s c r, PATG X (mkW s c r) -> bk_ok s.
Proof. intros X s c r (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma PATG_step_out : forall X s c r s' c' r', PATG X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  0 <= ir_out r' - ir_left r' <= ir_put r' -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> (bk_ok s -> bk_ok s') -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16) & P17) E1 E2 E3 E4 NG E6 E7 E8 E9 E10 HO HN HI HBK.
  unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E10. rewrite E9 in *.
  repeat (split; [first [assumption | left; assumption]|]). split; [|exact (HBK P17)]. repeat (split; [assumption|]). assumption.
Qed.

Lemma PATG_step : forall X s c r s' c' r', PATG X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> (bk_ok s -> bk_ok s') -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' HP E1 E2 E3 E4 NG E6 E7 E8 E9 E10 E11 E12 HN HI HBK.
  eapply PATG_step_out; try eassumption. rewrite E9, E11, E12.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H & _) & _). exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma PATG_step_bad : forall X s c r s' c' r', PATG X (mkW s c r) -> is_mode s = HEAD ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_mode s' = BAD -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> ir_put r' = ir_put r -> is_window s' = is_window s ->
  ir_out r' = ir_out r -> ir_left r' = ir_left r -> ISR s' -> (bk_ok s -> bk_ok s') -> PATG X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & P14 & P15 & P16) & P17) HM E1 E2 E3 E4 EM E6 E7 E8 E9 E10 E11 E12 HI HBK.
  specialize (HBK P17).
  unfold PATG, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E4, E6, E7, E8, E9, E10, E11, E12, EM.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split. { destruct P4 as [F0|(F1 & _ & F3 & F4)]; [left; exact F0| right; split; [exact F1|]; split; [right; reflexivity|]; split; assumption]. }
  split; [unfold BAD, FLAGS, HCRC; lia|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|].
  split; [exact HI|]. split; [|exact HBK]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|]. split; [reflexivity| exact P16].
Qed.

(* [comment removed for export] *)
Definition arm_stmtg (flush M PC : Z) (arm : AM unit) : Prop := forall X w x12 ms,
  ix_flush X = flush -> ILOOP X w PC (wz (-3)) x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> is_mode (w_s w) = M ->
  evt usegs (fun ms' => IPOST X (arm w) ms' /\ PATG X (wof (arm w))) ms.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition NBGq (X : ictx) (s : inflate_state) (c : icall) (RES : ares unit) (pcj : Z) (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun tt (mkW s c r1) /\ ILOOPh X (mkW s c r1) pcj q ms' /\ Q r1 q)
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

(* [comment removed for export] *)
Definition NBGh (X : ictx) (s : inflate_state) (c : icall) (r0 : iregs) (RES : ares unit) (pcj : Z) (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun tt (mkW s c r1) /\ ILOOPh X (mkW s c r0) pcj q ms' /\ Q r1 q)
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

(* [comment removed for export] *)
Definition NBGo (X : ictx) (s : inflate_state) (c : icall) (RES : ares unit) (pcj : Z) (x26 : word) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 x12, RES = ARun tt (mkW s c r1) /\ ILOOP X (mkW s c r1) pcj x26 x12 ms')
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ ILEAVE X (mkW s c r1) ms').

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NBG_run_facts := GP.NBG_run_facts.
Definition NBG_leave_facts := GP.NBG_leave_facts.
Definition pulled_eqs := GP.pulled_eqs.
Definition pulled_cursor := GP.pulled_cursor.
Definition nbG_r1_facts := GP.nbG_r1_facts.
Definition pullr_SafeH := GP.pullr_SafeH.
Definition pull_step := GP.pull_step.
Definition NB_dry := GP.NB_dry.
Definition NB_pull := GP.NB_pull.
Definition NB_done := GP.NB_done.
Definition NB_top := GP.NB_top.
Definition nbG_pull_ok := GP.nbG_pull_ok.
Definition zx32_small := GP.zx32_small.
Definition REGS_byte := GP.REGS_byte.
Definition REGS_hold64 := GP.REGS_hold64.

(* [comment removed for export] *)
Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.
Lemma shl3 : forall x, Z.shiftl x 3 = 8 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

(* [comment removed for export] *)
Lemma PATG_pulled : forall X s c r r1, PATG X (mkW s c r) -> pulled r r1 -> PATG X (mkW s c r1).
Proof. intros X s c r r1 HP HQ. destruct (pulled_eqs _ _ HQ) as (E1 & E2 & _ & E4 & _). eapply PATG_regs; [exact HP| assumption..]. Qed.
(* [comment removed for export] *)

