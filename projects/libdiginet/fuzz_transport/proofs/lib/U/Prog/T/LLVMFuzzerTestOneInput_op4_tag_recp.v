(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the tagged arm 0x143f0 .. the latch: t4r_rec_holds (the statement
   t4r_rec_stmt of _op4_tag_rec.v). 0x143f0 .. 0x1454c records the command when want = 0
   (fuzz_transport.c:1108-1118); the tail 0x1454c .. the latch is _op4_tag_tl.v's t4r_tail. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_rec LLVMFuzzerTestOneInput_op4_tag_tl.
Import ListNotations.
Open Scope Z_scope.

(* the struct diginet_cmd in the frame, as cells the loads read *)
Lemma t4r_cs_cells : forall m A cb len display key jhi, length cb = 24%nat -> length jhi = 8%nat ->
  rw_cells rsegs m A [CB 40 (cmd_struct cb len display key ++ jhi)] ->
  rw_cells rsegs m A [CB 24 cb; C1 (b8 len); C1 (b8 display); C1 (b8 0); C1 (b8 0); C4 (Z_to_bv 64 key); CB 8 jhi].
Proof.
  intros m A cb len display key jhi L1 L2 H. eapply rw_cells_conv; [| | | exact H].
  - cbn [cells_wf cell_wf]. repeat split; try assumption.
  - cbn [cells_bytes cbytes]. rewrite le4_put, !app_nil_r. unfold cmd_struct. rewrite <- !app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma t4r_want_rng : forall B1 D c3 at_, -10 <= t4_want B1 D c3 at_ <= 0.
Proof.
  intros B1 D c3 at_. unfold t4_want, SPEC_E_REFUSED, SPEC_E_SPACE, SPEC_OK.
  destruct (t4_sys B1 D c3); [lia|]. destruct ((at_ <? 0) && (g_nq (t4_B2 B1) =? QUEUE_MAX)); lia.
Qed.

Lemma t4r_len_rng : forall D c3, 3 <= t4_len D c3 <= 24.
Proof.
  intros D c3. unfold t4_len. pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22 ltac:(lia)). lia.
Qed.

Lemma t4r_off : forall D c3, t4_off D c3 = fi_off (t4_c4 D c3).
Proof. intros D c3. unfold t4_off, t4_tk, fuzz_take_m. reflexivity. Qed.

Lemma t4r_n_le : forall D c3, t4_n D c3 <= t4_len D c3 - 3.
Proof.
  intros D c3. unfold t4_n, t4_tk, fuzz_take_m. cbn [snd].
  destruct (Z.ltb_spec (t4_len D c3 - 3) (fi_n (t4_c4 D c3))); lia.
Qed.

Ltac t4r_hyp_mi := match goal with H : mem_inv rsegs _ |- _ => exact H end.
Ltac t4r_hyp_stk := match goal with H : stk rsegs _ _ _ |- _ => exact H end.
Ltac t4r_hyp_wmem := match goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => exact H end.

Lemma t4r_le4_sx32 : forall v, 0 <= v < 2 ^ 64 -> le4 (sx32 (Z_to_bv 64 v)) = put 4 v.
Proof. intros v Hv. unfold sx32. rewrite le4_put, unsigned_lit by lia. apply t4_put4_swrap. Qed.

Lemma t4r_b8u : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof.
  intros z Hz. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma t4r_prefix : forall m A (l r : list byte) n, bytes_at rsegs m A (l ++ r) -> (n <= length l)%nat ->
  bytes_at rsegs m A (firstn n l).
Proof.
  intros m A l r n H Hn. rewrite <- (firstn_skipn n l), <- app_assoc in H.
  exact (proj1 (proj1 (bytes_at_app rsegs m A _ _) H)).
Qed.

(* a world the loop's invariant accepts: its length, and g_fail_next <= 1 *)
Definition t4r_ok (B : list byte) : Prop := length B = Z.to_nat W_LEN /\ g_fail_next B <= 1.

Lemma t4r_ok_upd : forall B k v, t4r_ok B -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  t4r_ok (upd B k v).
Proof.
  intros B k v [L G] Hk Hv Hd. split.
  - apply t4_len_upd; assumption.
  - rewrite t4_gf_upd; assumption.
Qed.

Ltac t4r_off_lia :=
  rewrite ?length_put, ?repeat_length, ?firstn_length;
  unfold A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_len, A_Cmd_bytes, OFF_g_cmd, OFF_g_q, OFF_g_nq,
    OFF_g_fail_next, W_LEN in *; cbn [Z.of_nat]; lia.

Ltac t4r_ok_tac := repeat (apply t4r_ok_upd; [ | t4r_off_lia | t4r_off_lia | t4r_off_lia ]).

Lemma t4r_record : memcpy_contract ->
  forall data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 B6 F fc ms (Q : machine_state -> Prop),
  0 <= ops < OPS_MAX -> llvm_cursor D c3 -> 0 <= display <= 1 -> 0 <= key < 2 ^ 32 ->
  0 <= g_ncmd B1 < CMDS_MAX -> length jhi = 8%nat -> (at_ = -1 \/ 0 <= at_ < CMDS_MAX) ->
  (if t4_want B1 D c3 at_ =? SPEC_OK
   then t4_rec B5 (g_ncmd B1) key display (t4_len D c3) (t4_cb B1 D c3) at_
   else Some B5) = Some B6 ->
  t4r_at data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 F fc ms ->
  (forall ms', t4r_tl data D regs0 m0 Sp lo ops c3 B6 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros MCP data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 B6 F fc ms Q
    HOPS HC3 HDSP HKEY HSER LJ HAT H6 H HK.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s10 & t3 & t4 & t5 & t6 & m & jio &
                 -> & HM).
  pose proof (t4r_want_rng B1 D c3 at_) as WR.
  destruct (Z.eqb_spec (t4_want B1 D c3 at_) SPEC_OK) as [W0|W0].
  2: { (* want <> 0: 0x143f0 bnez s7, to 0x1454c *)
       cbv iota in H6. injection H6 as E6. subst B6.
       pose proof HM as HM1. unfold llvm_mem in HM1.
       destruct HM1 as (_ & _ & _ & _ & _ & _ & HLO & HSP2 & _).
       unfold LH_K, LH_FRAME in *. unfold SPEC_OK in W0.
       zstep. br.
       apply HK. unfold t4r_tl.
       do 22 eexists. exists m, (le8 (Z_to_bv 64 (bv_swrap 32 before))), jio, (t4_cs B1 D c3 display key ++ jhi).
       split; [reflexivity|]. split; [apply length_le8 | exact HM]. }
  cbv iota in H6.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  destruct (t4r_n_rng D c3 HC3) as (HNR & HC4 & HC5).
  pose proof HC4 as (HO4 & HN4 & HD4).
  pose proof (t4r_len_rng D c3) as HLEN. pose proof (t4r_n_le D c3) as HNL.
  assert (LCB : length (t4_cb B1 D c3) = 24%nat) by (apply t4_cb_len; rewrite ?t4r_off; lia).
  clear HD HRO HMU HWMO.
  rewrite W0. change SPEC_OK with 0.
  unfold t4_cs in *.
  set (serial := g_ncmd B1) in *. set (len := t4_len D c3) in *. set (cb := t4_cb B1 D c3) in *.
  clearbody serial len cb.
  unfold CMDS_MAX in HSER, HAT.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_M. wk_eq_fact OFF_g_cmd. wk_eq_fact OFF_g_q.
  wk_eq_fact OFF_g_nq.
  change (W_BASE_UBSAN + OFF_g_cmd) with 229576.
  destruct (llvm_frame_split regs0 m Sp _ jio _ HRW) as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW.
  unfold llvm_saved in F6.
  apply (t4r_cs_cells _ _ _ _ _ _ _ LCB LJ) in F5.
  (* ---- 0x143f0 bnez s7; 0x143f4 li a0, 0x400; 0x143f8 beq s0, a0; 0x143fc beqz s2 ---- *)
  zstep. br. zstep. zstep. br. zstep. br.
  (* ---- 0x14400 lw a0, 0x7c(sp); 0x14404 lbu a1, 0x79(sp); 0x14408 lbu a2, 0x78(sp) ---- *)
  do 3 zstep.
  cbv beta. rewrite (t4r_b8u len) by lia. rewrite (t4r_b8u display) by lia.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* ---- 0x1440c sw s1, 0(s2); 0x14410 sw a0, 4(s2); 0x14414 sw a1, 8(s2); 0x14418 sb a2, 0x24(s2) ---- *)
  do 4 zstep.
  set (W4 := upd (upd (upd (upd B5 (A_Cmd_st serial) (put 4 1)) (A_Cmd_key serial) (put 4 key))
                      (A_Cmd_display serial) (put 4 display)) (A_Cmd_len serial) (put 1 len)).
  lazymatch goal with W : wmem rsegs ?m2 (upd _ (A_Cmd_len serial) _) |- _ =>
    let T := type of W in
    lazymatch T with wmem _ _ ?X =>
      assert (EW4 : X = W4)
        by (unfold W4, A_Cmd_st, OFF_g_cmd; rewrite ?t4r_le4_sx32 by lia;
            replace (19912 + serial * 40) with (19912 + 40 * serial + 0) by lia; reflexivity)
    end;
    rewrite EW4 in W; clear EW4
  end.
  assert (OK4 : t4r_ok W4) by (unfold W4; t4r_ok_tac; split; [exact LB | exact HFN]).
  (* ---- 0x1441c addi a0, s2, 0xc; 0x14420 addi a1, sp, 0x60; 0x14424 jal memcpy: c.bytes, len bytes ---- *)
  do 3 zstep.
  pose proof F5 as [[_ HB5] _]. cbn [cells_bytes cbytes] in HB5.
  pose proof (t4r_prefix _ _ _ _ (Z.to_nat len) HB5 ltac:(rewrite LCB; lia)) as HSRC.
  clear HB5.
  lazymatch goal with W : wmem rsegs ?m2 W4 |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (wm_piece rsegs W_BASE_UBSAN m2 W4 (A_Cmd_bytes serial) len (229576 + serial * 40 + 12) W
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd, W_BASE_UBSAN; lia)
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd; lia) ltac:(lia)
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd, W_LEN; lia)) as DST
  end.
  eapply evt_cut.
  { eapply (MCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
              (firstn (Z.to_nat len) cb) (sub W4 (A_Cmd_bytes serial) (Z.to_nat len))).
    - rewrite unsigned_lit by lia. exact HSRC.
    - rewrite unsigned_lit by lia. rewrite firstn_length, LCB. lia.
    - rewrite !unsigned_lit by lia. exact DST.
    - rewrite !unsigned_lit by lia. right. lia.
    - t4r_hyp_mi. }
  intros ms' Hpost.
  destruct Hpost as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 &
                     -> & MUc & WMOc & MIc & CZc & _).
  rewrite !unsigned_lit in MUc, CZc by lia.
  try (rewrite (ret_pc_even 0x14428) by (first [lia | reflexivity])).
  lazymatch goal with W : wmem rsegs ?m2 W4 |- _ =>
    pose proof (wm_fill rsegs W_BASE_UBSAN m2 m3 W4 (229576 + serial * 40 + 12) (A_Cmd_bytes serial) len
                  (firstn (Z.to_nat len) cb) W MUc WMOc CZc
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd, W_BASE_UBSAN; lia)
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd; lia) ltac:(lia)
                  ltac:(unfold A_Cmd_bytes, OFF_g_cmd, W_LEN; lia)) as WM3;
    clear W
  end.
  assert (MU3 : munch [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m3).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    intros x Hx. cbn [outside] in *. destruct Hx as (_ & Hw & _). split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WMO WMOc) as WMO3.
  assert (ST3 : stk rsegs m3 lo Sp).
  { eapply stk_transport_disjoint; [t4r_hyp_stk | exact MUc | exact WMOc |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (OKw : t4r_ok (upd W4 (A_Cmd_bytes serial) (firstn (Z.to_nat len) cb))).
  { apply t4r_ok_upd; [exact OK4 | t4r_off_lia | t4r_off_lia | t4r_off_lia ]. }
  unfold W4 in WM3, OKw. rewrite t4_cmdw in WM3, OKw.
  clear MU WMO MUc WMOc CZc DST HSRC OK4 F1 F2 F3 F4 F5 F6.
  repeat match goal with H : stk rsegs ?mm lo Sp |- _ => lazymatch mm with m3 => fail | _ => clear H end end.
  repeat match goal with H : mem_inv rsegs ?mm |- _ => lazymatch mm with m3 => fail | _ => clear H end end.
  clearbody W4. clear W4.
  unfold t4_rec in H6.
  set (Bw := t4_Bw B5 serial key display len cb) in *. clearbody Bw.
  (* ---- 0x14428 sext.w a0, s4; 0x1442c bltz a0 ---- *)
  destruct HAT as [-> | HAT].
  - (* at = -1: the append arm 0x1451c *)
    change (-1 mod 4294967296) with 4294967295.
    change (0 <=? -1) with false in H6. cbv iota in H6.
    destruct (Z.leb_spec CMDS_MAX (g_nq Bw)) as [NQ|NQ]; [discriminate H6|]. cbv iota in H6.
    injection H6 as E6.
    pose proof (u_at_range Bw OFF_g_nq 4) as RNQ. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RNQ.
    change (u_at Bw OFF_g_nq 4) with (g_nq Bw) in RNQ.
    unfold CMDS_MAX in NQ.
    assert (ENQ : s32_at Bw 64980 = g_nq Bw)
      by (apply t4_s32_small; change (u_at Bw 64980 4) with (g_nq Bw); lia).
    zstep. zstep. br.
    (* 0x1451c lw a0, 0xc(s9); 0x14520 addi a1, a0, 1; 0x14524 sw a1, 0xc(s9); 0x14528 li a1, 0x3ff;
       0x1452c bltu a1, a0 *)
    zstep. rewrite ENQ.
    do 4 zstep. br.
    (* 0x14530 slli a0, a0, 2; auipc; addi a1 (&g_q); not a2, a1; 0x14540 bltu a2, a0; 0x14544 add; 0x14548 sw s0 *)
    do 5 zstep. br.
    do 2 zstep.
    lazymatch goal with W : wmem rsegs ?m4 ?X |- _ =>
      assert (EB6 : X = B6)
        by (rewrite ?Z.shiftl_mul_pow2 by lia;
            replace (60872 + g_nq Bw * 2 ^ 2) with (OFF_g_q + 4 * g_nq Bw) by (unfold OFF_g_q; lia);
            change 64980 with OFF_g_nq;
            rewrite t4_appw by (first [exact (proj1 OKw) | unfold CMDS_MAX; lia]); exact E6);
      rewrite EB6 in W
    end.
    assert (OK6 : t4r_ok B6).
    { rewrite <- E6. unfold set_g_nq, set_Q_at. t4r_ok_tac. exact OKw. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 0 B5 B6 m m4 _ _ _ HM0 ltac:(unfold LH_K; lia)
                    MU3 WMO3 ltac:(t4r_hyp_mi) ST3 ltac:(t4r_hyp_wmem) (proj2 OK6)) as HMF
    end.
    apply HK. unfold t4r_tl.
    do 23 eexists. exists (le8 (Z_to_bv 64 (bv_swrap 32 before))), jio,
      (cmd_struct cb len display key ++ jhi).
    split; [reflexivity|]. split; [apply length_le8 | exact HMF].
  - (* 0 <= at: the coalescing arm 0x14430 *)
    rewrite (Z.mod_small at_ 4294967296) by lia.
    replace (0 <=? at_) with true in H6 by (symmetry; apply Z.leb_le; lia). cbv iota in H6.
    destruct (Z.leb_spec CMDS_MAX (Q_at Bw at_)) as [QA|QA]; [discriminate H6|]. cbv iota in H6.
    injection H6 as E6.
    pose proof (u_at_range Bw (OFF_g_q + 4 * at_) 4) as RQA.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQA.
    change (u_at Bw (OFF_g_q + 4 * at_) 4) with (Q_at Bw at_) in RQA.
    unfold CMDS_MAX in QA.
    assert (EQA : s32_at Bw (OFF_g_q + 4 * at_) = Q_at Bw at_)
      by (apply t4_s32_small; change (u_at Bw (OFF_g_q + 4 * at_) 4) with (Q_at Bw at_); lia).
    zstep. zstep.
    rewrite (swrap32_small (at_ + 0)) by lia. rewrite bv_lts_zero_r.
    br.
    (* 0x14430 slli; auipc; addi; not; 0x14440 bltu; 0x14444 add; 0x14448 lw a1 *)
    do 5 zstep. br. do 2 zstep.
    lazymatch goal with |- context [s32_at Bw ?k] =>
      replace k with (OFF_g_q + 4 * at_) by (rewrite ?Z.shiftl_mul_pow2 by lia; unfold OFF_g_q; lia)
    end.
    rewrite EQA.
    (* 0x1444c li; 0x14450 bltu; 0x14454 li 0x28; mul; not; 0x14460 bltu; add; li 3; 0x1446c sw; j; 0x14548 sw *)
    do 2 zstep. br. do 4 zstep. br. do 4 zstep. zstep.
    lazymatch goal with W : wmem rsegs ?m4 ?X |- _ =>
      assert (EB6 : X = B6)
        by (rewrite ?Z.shiftl_mul_pow2 by lia;
            replace (60872 + at_ * 2 ^ 2) with (OFF_g_q + 4 * at_) by (unfold OFF_g_q; lia);
            replace (19912 + Q_at Bw at_ * 40) with (A_Cmd_st (Q_at Bw at_))
              by (unfold A_Cmd_st, OFF_g_cmd; lia);
            rewrite t4_coalw; exact E6);
      rewrite EB6 in W
    end.
    assert (OK6 : t4r_ok B6).
    { rewrite <- E6. unfold set_Q_at, set_Cmd_st. t4r_ok_tac. exact OKw. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      pose proof (llvm_mem_after_call data D regs0 m0 Sp lo 0 B5 B6 m m4 _ _ _ HM0 ltac:(unfold LH_K; lia)
                    MU3 WMO3 ltac:(t4r_hyp_mi) ST3 ltac:(t4r_hyp_wmem) (proj2 OK6)) as HMF
    end.
    apply HK. unfold t4r_tl.
    do 23 eexists. exists (le8 (Z_to_bv 64 (bv_swrap 32 before))), jio,
      (cmd_struct cb len display key ++ jhi).
    split; [reflexivity|]. split; [apply length_le8 | exact HMF].
Qed.

(* 0x143f0 .. the latch: the record, then the tail *)
Theorem t4r_rec_holds : memcpy_contract -> settle_contract -> t4r_rec_stmt.
Proof.
  intros MCP STL.
  unfold t4r_rec_stmt.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 B6 B8 F fc ms
    HOPS HC3 HDSP HKEY HSER LJ HAT H6 HSE H.
  eapply t4r_record; [exact MCP | exact HOPS | exact HC3 | exact HDSP | exact HKEY | exact HSER | exact LJ
    | exact HAT | exact H6 | exact H |].
  intros ms3 HS3.
  exact (t4r_tail STL data D regs0 m0 Sp lo ops c3 B6 B8 F fc ms3 HOPS HC3 HSE HS3).
Qed.
