(* Walk of diginet_session_config_default in the ubsan image, entry 0x1693c. A 16-byte frame saves ra and s0;
   a0 = &g_cfg = W_BASE_UBSAN + OFF_g_cfg (0x43100), so beqz a0 is not taken; memset (a0, 0, 60) zeroes g_cfg (the
   callee's span is folded into the world by wm_fill); the UBSan alignment test (a0 & 3) is 0, so bnez does not reach
   the trap; ten sw at a0 + 16, 24, ..., 56 write the nonzero fields; the frame is restored and ret. The world after the
   walk is upd B OFF_g_cfg cd_image; so is the model's (cd_model). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
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

(* Two byte lists with the same values are equal. *)
Lemma cd_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx | apply IH; exact Hl].
Qed.

(* A callee that wrote the span [X, X + n) and returned it as a cell leaves a stack window a stack window: outside
   the span the memory is unchanged, inside it every byte is readable from the cell. *)
Lemma cd_stk_span : forall segs (m m' : word -> option byte) lo hi X n src,
  stk segs m lo hi -> munch [(X, X + n)] m m' -> wmono segs m m' ->
  rw_cells segs m' X [CB (Z.to_nat n) src] -> stk segs m' lo hi.
Proof.
  intros segs m m' lo hi X n src (H1 & H2 & H) Hm Hw [[Hwf Hb] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hc _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. destruct Hb as (HX & HXl & Hb).
  split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hwa (b & Hbb)]. split; [apply Hw; exact Hwa|].
  destruct (Z_lt_le_dec a X) as [Lt|Ge]; [|destruct (Z_lt_le_dec a (X + n)) as [In|Out]].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hbb|]. rewrite wa_unsigned by lia. cbn [outside].
    split; [lia | exact I].
  - assert (Hi : (Z.to_nat (a - X) < length src)%nat) by (rewrite Hc; lia).
    pose proof (Hb _ Hi) as E. replace (X + Z.of_nat (Z.to_nat (a - X))) with a in E by lia.
    rewrite E. destruct (nth_error src (Z.to_nat (a - X))) as [b'|] eqn:N; [exists b'; reflexivity|].
    apply nth_error_None in N. lia.
  - exists b. unfold mrd in *. rewrite Hm; [exact Hbb|]. rewrite wa_unsigned by lia. cbn [outside].
    split; [lia | exact I].
Qed.

(* Side conditions of cd_upd_in: linear facts, or closed sizes once length B is its value LB. *)
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

Theorem diginet_session_config_default_holds : memset_contract -> diginet_session_config_default_contract.
Proof.
  intros HMEMSET. unfold memset_contract in HMEMSET.
  unfold diginet_session_config_default_contract, diginet_session_config_default_ENTRY,
    diginet_session_config_default_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    -> WM HM Hsp ST LO WS MI.
  unfold w_off_stack in WS.
  assert (LBZ : Z.of_nat (length B) = 65616)
    by (rewrite (wm_len _ _ _ _ WM), Z2Nat.id by (unfold W_LEN; lia); reflexivity).
  rewrite (cd_model B LBZ) in HM. injection HM as HB'. subst B'.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  wk_facts.                               (* W_LEN and W_BASE_UBSAN by value, for lia *)
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) with (Z_to_bv 64 0x43100).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  step.                                   (* 0x1693c addi sp, sp, -16 *)
  step.                                   (* 0x16940 sd ra, 8(sp) *)
  step.                                   (* 0x16944 sd s0, 0(sp) *)
  step.                                   (* 0x16948 beqz a0: a0 = 0x43100, not taken *)
  try cd_if_false.
  step.                                   (* 0x1694c mv s0, a0 *)
  step.                                   (* 0x16950 li a2, 60 *)
  step.                                   (* 0x16954 li a1, 0 *)
  step.                                   (* 0x16958 jal memset *)
  (* memset (&g_cfg, 0, 60): the destination is the world's piece [OFF_g_cfg, OFF_g_cfg + 60) *)
  assert (U0 : bv_unsigned (Z_to_bv 64 0x43100) = 0x43100) by (apply unsigned_lit; lia).
  assert (U60 : bv_unsigned (Z_to_bv 64 60) = 60) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (wm_piece rsegs W_BASE_UBSAN m1 B 65024 (bv_unsigned (Z_to_bv 64 60)) (bv_unsigned (Z_to_bv 64 0x43100))
                WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST.
  eapply evt_cut.
  { eapply HMEMSET; [exact DST | exact MI]. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 &
                    EQs & MUc & WOc & MI2 & DST2).
  subst ms'.
  pose proof (cd_stk_span rsegs m1 m2 _ _ _ _ _ ST MUc WOc DST2) as ST2.
  clear ST. rename ST2 into ST.
  wk_world_after_call rsegs m1 m2.
  transport_after_call rsegs m1 m2 MUc WOc.
  clear MUc WOc MI. rename MI2 into MI. try clear m1.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  step.                                   (* 0x1695c andi a0, s0, 3: 0x43100 & 3 = 0 *)
  step.                                   (* 0x16960 bnez a0: not taken, the trap at 0x169d0 is not reached *)
  try cd_if_false.
  do 9 step.                              (* 0x16964 .. 0x16984 li / lui / addi *)
  do 4 step.                              (* 0x16988 .. 0x16994 sw at 16, 24, 28, 32 *)
  do 3 step.                              (* 0x16998 .. 0x169a0 li / addi *)
  do 4 step.                              (* 0x169a4 .. 0x169b0 sw at 36, 40, 44, 48 *)
  step.                                   (* 0x169b4 li a1, 314 *)
  do 2 step.                              (* 0x169b8 .. 0x169bc sw at 52, 56 *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?BW] |- _ =>
    assert (EQ : BW = upd B OFF_g_cfg cd_image)
      by (unfold OFF_g_cfg; do 10 rewrite (cd_upd_in B) by (cd_side B LBZ);
          apply (f_equal (upd B 65024)); apply cd_bytes_eq; vm_compute; reflexivity);
    rewrite EQ in H
  end.
  step.                                   (* 0x169c0 ld ra, 8(sp) *)
  step.                                   (* 0x169c4 ld s0, 0(sp) *)
  release_frame FR ST (bv_unsigned sp).
  step.                                   (* 0x169c8 addi sp, sp, 16 *)
  step.                                   (* 0x169cc ret *)
  apply evt_done. unfold QQ. hnf. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|]. eassumption.
Qed.
