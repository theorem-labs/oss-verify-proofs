From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_latest_queue_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- machine words ---- *)

Lemma qu_eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma qu_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

(* slli 32 then srli 32 of a sign-extended 32-bit value: its low 32 bits *)
Lemma qu_shl_shr : forall x, -2^31 <= x < 2^31 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x mod 2^32.
Proof.
  intros x Hx. rewrite !unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma qu_s32_mod : forall B k, s32_at B k mod 2^32 = u_at B k 4.
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma qu_s32_zero : forall B k, (s32_at B k =? 0) = (u_at B k 4 =? 0).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec (u_at B k 4) 0) as [E|E]; [rewrite E; reflexivity|].
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(* a 4-byte field below 2^31 reads the same signed and unsigned *)
Lemma qu_s32_small : forall B k, u_at B k 4 < 2^31 -> s32_at B k = u_at B k 4.
Proof.
  intros B k H. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the model ---- *)

Lemma qu_false : forall fuel B j, queue_loop fuel B j false <> Some true.
Proof. intros [|fuel] B j; cbn [queue_loop andb]; discriminate. Qed.

Lemma qu_model : forall B B', check_latest_queue_m B = Some (B', tt) ->
  B' = B /\ S_queued B = g_nq B /\ queue_loop (S (Z.to_nat QUEUE_MAX)) B 0 true = Some true.
Proof.
  intros B B' H. unfold check_latest_queue_m in H.
  destruct (queue_loop (S (Z.to_nat QUEUE_MAX)) B 0 (S_queued B =? g_nq B)) as [same|] eqn:E; [|discriminate].
  destruct same; [|discriminate]. injection H as <-.
  destruct (Z.eqb_spec (S_queued B) (g_nq B)) as [Q|Q].
  - split; [reflexivity|]. split; [exact Q | exact E].
  - exfalso. exact (qu_false _ B 0 E).
Qed.

Lemma qu_beq : forall l r, beq_bytes l r = true -> l = r.
Proof.
  intros l r H. unfold beq_bytes in H. destruct (list_eq_dec Z.eq_dec (zs l) (zs r)) as [E|E]; [|discriminate].
  clear H. unfold zs in E. revert r E. induction l as [|a l IH]; intros [|b r] E; cbn in E; try discriminate.
  - reflexivity.
  - injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma qu_memcmp_refl : forall l n, length l = n -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|a l IH]; intros n H; cbn in H; subst n; [reflexivity|].
  cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. reflexivity.
Qed.

Lemma qu_step : forall fuel B i, queue_loop fuel B i true = Some true -> i < g_nq B ->
  exists fuel', fuel = S fuel' /\ i < CMDS_MAX /\ Q_at B i < CMDS_MAX /\ i < QUEUE_MAX /\
    S_queue_len B i = Cmd_len B (Q_at B i) /\
    sub B (A_S_queue_bytes i) (Z.to_nat (Cmd_len B (Q_at B i)))
      = sub B (A_Cmd_bytes (Q_at B i)) (Z.to_nat (Cmd_len B (Q_at B i))) /\
    queue_loop fuel' B (i + 1) true = Some true.
Proof.
  intros [|fuel] B i H Hi; [discriminate|]. cbn [queue_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H. cbn [andb] in H.
  destruct (CMDS_MAX <=? i) eqn:C1; [discriminate|].
  destruct (CMDS_MAX <=? Q_at B i) eqn:C2; [discriminate|].
  destruct (QUEUE_MAX <=? i) eqn:C3; [discriminate|].
  apply Z.leb_gt in C1, C2, C3.
  destruct ((S_queue_len B i =? Cmd_len B (Q_at B i)) &&
            beq_bytes (sub B (A_S_queue_bytes i) (Z.to_nat (Cmd_len B (Q_at B i))))
                      (sub B (A_Cmd_bytes (Q_at B i)) (Z.to_nat (Cmd_len B (Q_at B i))))) eqn:S.
  - apply andb_true_iff in S. destruct S as [S1 S2]. apply Z.eqb_eq in S1. apply qu_beq in S2.
    exists fuel. repeat split; assumption.
  - exfalso. exact (qu_false fuel B (i + 1) H).
Qed.

Theorem check_latest_queue_holds : bcmp_contract -> check_latest_queue_contract.
Proof.
  intros BC. unfold bcmp_contract, BCMP in BC.
  unfold check_latest_queue_contract, check_latest_queue_ENTRY, check_latest_queue_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' WM HM Hsp ST LO WOS MI.
  destruct (qu_model B B' HM) as [-> [HQN HL]]. clear HM.
  change (S_queued B) with (u_at B 19792 4) in HQN. change (g_nq B) with (u_at B 64980 4) in HQN.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts. unfold w_off_stack in WOS.
  carve_frame 80%nat ST.
  do 11 step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -80) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -80) ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  pose proof (u_at_range B 64980 4) as RNQ. change (8 * Z.of_nat 4) with 32 in RNQ.
  (* the epilogue, 0x16758 *)
  assert (EPI : forall (m2 : word -> option byte)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC -> stk rsegs m2 lo (bv_unsigned sp + -80) ->
    munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x16758) fc None m2 (seg_rom rsegs))).
  { intros m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
      FR2 ST2 MU2 WMo2 MI2 WM2.
    unfold FRC in FR2.
    do 10 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    step. step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WMo2|]. split; [exact MI2|]. split; [exact ST2|]. split; [reflexivity | exact WM2]. }
  (* 0x16754: a1 holds same = 1 *)
  assert (FIN : forall (m2 : word -> option byte)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
    x11 = Z_to_bv 64 1 ->
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC -> stk rsegs m2 lo (bv_unsigned sp + -80) ->
    munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x16754) fc None m2 (seg_rom rsegs))).
  { intros m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 ->
      FR2 ST2 MU2 WMo2 MI2 WM2.
    step.
    replace (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false by reflexivity. cbv iota.
    apply EPI; assumption. }
  (* the loop over g_q, 0x16708 *)
  assert (LOOP : forall fuel i (m2 : word -> option byte)
                        (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x28 x29 x30 x31 : word),
    queue_loop fuel B i true = Some true -> 0 <= i < u_at B 64980 4 ->
    x8 = Z_to_bv 64 (213072 + 32 * i) -> x20 = Z_to_bv 64 (270536 + 4 * i) -> x10 = Z_to_bv 64 (i + 1) ->
    rw_cells rsegs m2 (bv_unsigned sp + -80) FRC -> stk rsegs m2 lo (bv_unsigned sp + -80) ->
    munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 (Z_to_bv 64 1024) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 40) (Z_to_bv 64 (u_at B 64980 4)) x20 (Z_to_bv 64 229576)
                          (Z_to_bv 64 18446744073709322039) (Z_to_bv 64 513) x24 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x16708) fc None m2 (seg_rom rsegs))).
  { induction fuel as [|fuel IH];
      intros i m2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x28 x29 x30 x31 HLi Hi -> -> -> FR2 ST2 MU2 WMo2 MI2 WM2;
      [discriminate|].
    destruct (qu_step (S fuel) B i HLi ltac:(change (g_nq B) with (u_at B 64980 4); lia))
      as (f' & Ef & Hi1 & Hq & Hi2 & HLEN & HBY & HL1).
    injection Ef as <-. unfold CMDS_MAX in Hi1, Hq. unfold QUEUE_MAX in Hi2.
    assert (RQ : 0 <= Q_at B i) by (unfold Q_at; apply u_at_range).
    step.
    rewrite ?wm_lw.
    repeat match goal with |- context [s32_at B ?k] =>
      replace (s32_at B k) with (Q_at B i)
        by (replace k with (OFF_g_q + 4 * i) by (unfold OFF_g_q; lia);
            rewrite qu_s32_small; [reflexivity | exact (Z.lt_trans _ 1024 (2 ^ 31) Hq ltac:(lia))]) end.
    set (q := Q_at B i) in *.
    set (tl := Cmd_len B q) in *.
    assert (RT : 0 <= tl < 256) by (unfold tl, Cmd_len; pose proof (u_at_range B (A_Cmd_len q) 1) as R; cbn in R; lia).
    step.
    rewrite qu_ltu_lit by lia. replace (1024 <? q) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step.
    rewrite (unsigned_lit q) by lia.
    step.
    rewrite qu_ltu_lit by lia. replace (18446744073709322039 <? q * 40) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    step.
    rewrite qu_eqb_lit by lia.
    match goal with |- context [?x =? 513] => replace (x =? 513) with false by (symmetry; apply Z.eqb_neq; lia) end.
    cbv iota.
    step.
    assert (RD3 : ov_read_bytes rsegs m2 (Z_to_bv 64 (213072 + 32 * i + 24)) 1 = Some (sub B (A_S_queue_len i) 1)).
    { apply (wm_read rsegs W_BASE_UBSAN m2 B); [exact WM2 | unfold A_S_queue_len, OFF_g_s; lia
                                               | unfold A_S_queue_len, OFF_g_s; lia |].
      f_equal. unfold A_S_queue_len, OFF_g_s. lia. }
    assert (RD4 : ov_read_bytes rsegs m2 (Z_to_bv 64 (229576 + q * 40 + 36)) 1 = Some (sub B (A_Cmd_len q) 1)).
    { apply (wm_read rsegs W_BASE_UBSAN m2 B); [exact WM2 | unfold A_Cmd_len, OFF_g_cmd; lia
                                               | unfold A_Cmd_len, OFF_g_cmd; lia |].
      f_equal. unfold A_Cmd_len, OFF_g_cmd. lia. }
    step. step.
    rewrite ?wm_lbu.
    change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i). change (u_at B (A_Cmd_len q) 1) with tl.
    rewrite HLEN.
    step.
    rewrite qu_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
    do 3 step.
    set (bs := sub B (A_Cmd_bytes q) (Z.to_nat tl)) in *.
    assert (LB : length bs = Z.to_nat tl).
    { unfold bs. apply length_sub; [unfold A_Cmd_bytes, OFF_g_cmd; lia|].
      rewrite (wm_len rsegs W_BASE_UBSAN m2 B WM2). unfold W_LEN, A_Cmd_bytes, OFF_g_cmd. lia. }
    eapply evt_cut.
    { eapply BC with (ls := bs) (rs := bs) (v := 0).
      - rewrite unsigned_lit by lia. rewrite <- HBY.
        apply (wm_src rsegs W_BASE_UBSAN m2 B (A_S_queue_bytes i) (Z.to_nat tl));
          [exact WM2 | unfold A_S_queue_bytes, OFF_g_s; lia | unfold A_S_queue_bytes, OFF_g_s; lia
          | unfold A_S_queue_bytes, OFF_g_s; lia].
      - rewrite unsigned_lit by lia. unfold bs.
        apply (wm_src rsegs W_BASE_UBSAN m2 B (A_Cmd_bytes q) (Z.to_nat tl));
          [exact WM2 | unfold A_Cmd_bytes, OFF_g_cmd; lia | unfold A_Cmd_bytes, OFF_g_cmd; lia
          | unfold A_Cmd_bytes, OFF_g_cmd; lia].
      - rewrite unsigned_lit by lia. apply qu_memcmp_refl. exact LB.
      - exact MI2. }
    wk_post_call rsegs m2.
    step. step.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb]. cbv iota.
    do 4 step.
    rewrite qu_ltu_lit by lia.
    destruct (Z.ltb_spec (i + 1) (u_at B 64980 4)) as [Lt|Ge]; cbn [negb]; cbv iota.
    - apply (IH (i + 1)); first [assumption | lia | (f_equal; lia)].
    - apply FIN; first [assumption | reflexivity]. }
  do 10 step.
  assert (SQ : s32_at B 19792 = s32_at B 64980) by (unfold s32_at; rewrite HQN; reflexivity).
  rewrite SQ.
  pose proof (s32_range B 64980) as RS.
  rewrite qu_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  step.
  rewrite qu_eqb_lit by lia. rewrite qu_s32_zero.
  destruct (Z.eqb_spec (u_at B 64980 4) 0) as [N0|N0]; cbv iota.
  - apply FIN; first [assumption | (rewrite Z.lxor_nilpotent; reflexivity)].
  - do 12 step.
    rewrite qu_shl_shr by lia. rewrite qu_s32_mod.
    apply (LOOP (S (Z.to_nat QUEUE_MAX)) 0); first [assumption | lia | (f_equal; lia)].
Qed.
