(* Walk of diginet_session_config_default in the plain image, entry 0x161d8. a0 = &g_cfg = W_BASE_PLAIN + OFF_g_cfg
   (0x42590), so beqz a0 is not taken; then fifteen sw at a0 + 0, 4, ..., 56 in increasing order write the 60 bytes of
   g_cfg, and ret. The world after the walk is upd B OFF_g_cfg cd_image; so is the model's (cd_model). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC
  diginet_session_config_default_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the 60 bytes of g_cfg after the call ---- *)

Definition cd_image : list byte :=
  put 16 0 ++ put 4 1 ++ put 4 0 ++ put 4 10000 ++ put 4 100 ++ put 4 5 ++ put 4 300 ++ put 4 25000 ++
  put 4 3000 ++ put 4 2000 ++ put 4 48 ++ put 4 314.

(* A write inside an earlier write's span goes into that span. *)
Lemma cd_upd_in : forall (B v w : list byte) k j, 0 <= k -> k <= j ->
  j + Z.of_nat (length w) <= k + Z.of_nat (length v) -> k + Z.of_nat (length v) <= Z.of_nat (length B) ->
  upd (upd B k v) j w = upd B k (upd v (j - k) w).
Proof.
  intros B v w k j Hk Hkj Hw Hv.
  assert (Lv : length (upd v (j - k) w) = length v) by (apply length_upd; lia).
  assert (Lu : length (upd B k v) = length B) by (apply length_upd; lia).
  apply nth_error_ext. intros i.
  rewrite (ne_upd (upd B k v) w j i) by (try rewrite Lu; lia).
  rewrite (ne_upd B v k i) by lia.
  rewrite (ne_upd B (upd v (j - k) w) k i) by (try rewrite Lv; lia).
  rewrite (ne_upd v w (j - k) (i - Z.to_nat k)) by lia.
  rewrite ?Lv.
  destruct (Nat.leb_spec (Z.to_nat j) i); destruct (Nat.ltb_spec i (Z.to_nat j + length w));
  destruct (Nat.leb_spec (Z.to_nat k) i); destruct (Nat.ltb_spec i (Z.to_nat k + length v));
  destruct (Nat.leb_spec (Z.to_nat (j - k)) (i - Z.to_nat k));
  destruct (Nat.ltb_spec (i - Z.to_nat k) (Z.to_nat (j - k) + length w));
  cbn [andb]; try reflexivity; try (exfalso; lia); f_equal; lia.
Qed.

(* A write right after an earlier write's span extends that span. *)
Lemma cd_upd_adj : forall (B v w : list byte) k j, 0 <= k -> j = k + Z.of_nat (length v) ->
  k + Z.of_nat (length v) + Z.of_nat (length w) <= Z.of_nat (length B) ->
  upd (upd B k v) j w = upd B k (v ++ w).
Proof.
  intros B v w k j Hk Hj Hl. subst j.
  assert (Lu : length (upd B k v) = length B) by (apply length_upd; lia).
  apply nth_error_ext. intros i.
  rewrite (ne_upd (upd B k v) w (k + Z.of_nat (length v)) i) by (try rewrite Lu; lia).
  rewrite (ne_upd B v k i) by lia.
  rewrite (ne_upd B (v ++ w) k i) by (try rewrite length_app; lia).
  rewrite ?length_app.
  destruct (Nat.ltb_spec (i - Z.to_nat k) (length v)) as [Hi|Hi];
    [rewrite nth_error_app1 by exact Hi | rewrite nth_error_app2 by exact Hi];
  destruct (Nat.leb_spec (Z.to_nat (k + Z.of_nat (length v))) i);
  destruct (Nat.ltb_spec i (Z.to_nat (k + Z.of_nat (length v)) + length w));
  destruct (Nat.leb_spec (Z.to_nat k) i); destruct (Nat.ltb_spec i (Z.to_nat k + length v));
  destruct (Nat.ltb_spec i (Z.to_nat k + (length v + length w)));
  cbn [andb]; try reflexivity; try (exfalso; lia); f_equal; lia.
Qed.

(* Two byte lists with the same values are equal. *)
Lemma cd_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx | apply IH; exact Hl].
Qed.

(* Side conditions of cd_upd_in / cd_upd_adj: linear facts, or closed sizes once length B is its value LB. *)
Ltac cd_side B LB :=
  first [ lia
        | (rewrite LB; vm_compute; congruence)
        | (lazymatch goal with |- context [B] => fail | _ => idtac end; vm_compute; congruence) ].

(* The model: memset of the 60 bytes, then the eleven setters, all inside [OFF_g_cfg, OFF_g_cfg + 60). *)
Lemma cd_model : forall B, Z.of_nat (length B) = 65616 ->
  diginet_session_config_default_m B = Some (upd B OFF_g_cfg cd_image, tt).
Proof.
  intros B LB.
  cbv beta zeta delta [diginet_session_config_default_m set_Cfg_auto_wake set_Cfg_sum_mode set_Cfg_keepalive_ms
    set_Cfg_ack_timeout_ms set_Cfg_max_retries set_Cfg_backoff_ms set_Cfg_offline_ms set_Cfg_wake_timeout_ms
    set_Cfg_display_gap_us set_Cfg_max_cmds set_Cfg_max_body A_Cfg_auto_wake A_Cfg_sum_mode A_Cfg_keepalive_ms
    A_Cfg_ack_timeout_ms A_Cfg_max_retries A_Cfg_backoff_ms A_Cfg_offline_ms A_Cfg_wake_timeout_ms
    A_Cfg_display_gap_us A_Cfg_max_cmds A_Cfg_max_body OFF_g_cfg SZ_g_cfg DIGINET_SUM_BODY].
  do 11 rewrite (cd_upd_in B) by (cd_side B LB).
  apply (f_equal (fun X => Some (upd B 65024 X, tt))). apply cd_bytes_eq. vm_compute. reflexivity.
Qed.

(* A branch whose condition is closed and false. *)
Ltac cd_if_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
      lazymatch pc with
      | context [if ?c then _ else _] => replace c with false by reflexivity; cbv iota
      end
  end.

Theorem diginet_session_config_default_holds : diginet_session_config_default_contract.
Proof.
  unfold diginet_session_config_default_contract, diginet_session_config_default_ENTRY,
    diginet_session_config_default_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    -> WM HM Hsp ST LO WS MI.
  unfold w_off_stack in WS.
  assert (LBZ : Z.of_nat (length B) = 65616)
    by (rewrite (wm_len _ _ _ _ WM), Z2Nat.id by (unfold W_LEN; lia); reflexivity).
  rewrite (cd_model B LBZ) in HM. injection HM as HB'. subst B'.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_cfg)) with (Z_to_bv 64 0x42590).
  step.                                   (* 0x161d8 beqz a0: a0 = 0x42590, not taken *)
  try cd_if_false.
  do 4 step.                              (* 0x161dc .. 0x161e8 sw zero at 0, 4, 8, 12 *)
  do 9 step.                              (* 0x161ec .. 0x1620c li / lui / addi *)
  do 4 step.                              (* 0x16210 .. 0x1621c sw at 16, 20, 24, 28 *)
  do 3 step.                              (* 0x16220 .. 0x16228 li / addi *)
  do 4 step.                              (* 0x1622c .. 0x16238 sw at 32, 36, 40, 44 *)
  step.                                   (* 0x1623c li a2, 314 *)
  do 3 step.                              (* 0x16240 .. 0x16248 sw at 48, 52, 56 *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN [CB _ ?BW] |- _ =>
    assert (EQ : BW = upd B OFF_g_cfg cd_image)
      by (unfold OFF_g_cfg; do 14 rewrite (cd_upd_adj B) by (cd_side B LBZ);
          apply (f_equal (upd B 65024)); apply cd_bytes_eq; vm_compute; reflexivity);
    rewrite EQ in H
  end.
  step.                                   (* 0x1624c ret *)
  apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|]. eassumption.
Qed.
