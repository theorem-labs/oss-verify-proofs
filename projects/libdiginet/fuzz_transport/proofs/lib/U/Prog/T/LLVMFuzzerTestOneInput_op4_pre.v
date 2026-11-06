(* The prefix of case 4 of the ubsan LLVMFuzzerTestOneInput (op_submit inlined, fuzz_transport.c:1068-1077):
   0x13a48 .. 0x13a94, before = s->queued (lw at g_s + 0x46e0), op_begin (two memsets, OW.desk_off = -1,
   M.fail = g_fail_next) and the 32-byte struct diginet_cmd zeroed at sp+0x60 (four sd). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs.
Import ListNotations.
Open Scope Z_scope.


Lemma op4_begin : forall data D regs0 m0 Sp lo ops c c1 B B1 F fc ms (Q : machine_state -> Prop),
  memset_contract ->
  llvm_case data D regs0 4 m0 Sp lo ops c c1 B F fc ms ->
  op_begin_m B = Some (B1, tt) ->
  (forall ms', op4_s1 data D regs0 m0 Sp lo ops c c1 (S_queued B) B1 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops c c1 B B1 F fc ms Q MSC H HB1 HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m &
                 j10 & jio & j60 & -> & HOPS & HN & HC & HC1 & HOP & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  assert (RQ : 0 <= S_queued B < 2 ^ 32) by exact (u_at_range B A_S_queued 4).
  change (Z_to_bv 64 (LH_CASE 4)) with (Z_to_bv 64 0x13a48).
  unfold LH_K, LH_FRAME in *.
  clear HD HSTK HRW HMU HWMO HRO.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_OW. wk_eq_fact OFF_GOT. wk_eq_fact OFF_g_s.
  wk_eq_fact OFF_M. wk_eq_fact A_M_fail. wk_eq_fact A_OW_desk_off. wk_eq_fact SZ_OW. wk_eq_fact SZ_GOT.
  (* ---- 0x13a48 lui a0, 4; 0x13a4c add a0, s10, a0; 0x13a50 lw s0, 0x6e0(a0): before = s->queued ---- *)
  do 3 zstep.
  (* ---- 0x13a54-0x13a60: memset(&OW, 0, 0x130); a0 = s9 + 0x158 = W_BASE_UBSAN + OFF_OW ---- *)
  do 4 zstep.
  assert (CW1 : rw_cells rsegs m (W_BASE_UBSAN + OFF_OW) [CB (Z.to_nat 304) (sub B OFF_OW 304)]).
  { pose proof (wm_cell rsegs W_BASE_UBSAN m B OFF_OW 304 (W_BASE_UBSAN + OFF_OW) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B OFF_OW 304).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_UBSAN + OFF_g_fail_next + 344) with (W_BASE_UBSAN + OFF_OW) by lia. exact CW1.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  replace (W_BASE_UBSAN + OFF_g_fail_next + 344) with (W_BASE_UBSAN + OFF_OW) in MU1, CZ1 by lia.
  cbn [Z.to_nat] in CZ1.
  assert (HM1 : llvm_mem data D regs0 m0 Sp lo (upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) m1 j10 jio j60).
  { eapply llvm_mem_after_fill;
      [ exact HM0 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_OW in *; lia).
    exact HFN. }
  clear HM0 HMI HWM HFN CW1 CZ1 MU1 WMO1 MI1.
  (* ---- 0x13a64-0x13a70: memset(&GOT, 0, 0xe0); a0 = s9 + 0x74 = W_BASE_UBSAN + OFF_GOT ---- *)
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HWM & HFN & _ & _ & _ & _ & _ & _).
  set (Ba := upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) in *.
  assert (LBa : Z.of_nat (length Ba) = W_LEN)
    by (unfold Ba; rewrite length_upd; [exact LBz | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13a64) by (first [lia | reflexivity]).
  do 4 zstep.
  assert (CW2 : rw_cells rsegs m1 (W_BASE_UBSAN + OFF_GOT) [CB (Z.to_nat 224) (sub Ba OFF_GOT 224)]).
  { pose proof (wm_cell rsegs W_BASE_UBSAN m1 Ba OFF_GOT 224 (W_BASE_UBSAN + OFF_GOT) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub Ba OFF_GOT 224).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_UBSAN + OFF_g_fail_next + 116) with (W_BASE_UBSAN + OFF_GOT) by lia. exact CW2.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 &
                     -> & MU2 & WMO2 & MI2 & CZ2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace (W_BASE_UBSAN + OFF_g_fail_next + 116) with (W_BASE_UBSAN + OFF_GOT) in MU2, CZ2 by lia.
  cbn [Z.to_nat] in CZ2.
  assert (HM2 : llvm_mem data D regs0 m0 Sp lo (upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) m2 j10 jio j60).
  { eapply llvm_mem_after_fill;
      [ exact HM1 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_GOT in *; lia).
    exact HFN. }
  clear HM1 HMI HWM HFN CW2 CZ2 MU2 WMO2 MI2.
  (* ---- 0x13a74 lbu a0, g_fail_next; 0x13a78 li a1, -1; 0x13a7c sw a1, OW.desk_off (s9 + 0x240);
     0x13a80 sw a0, M.fail (s8 + 0x58): op_begin's last two writes ---- *)
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & _ & HSTK & _ & _ & _ & HMI & _ & HWM & HFN & _ & _ & _ & _ & _ & _).
  set (Bb := upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) in *.
  assert (LBb : Z.of_nat (length Bb) = 65616)
    by (unfold Bb; rewrite length_upd; [rewrite LBa; reflexivity | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13a74) by (first [lia | reflexivity]).
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m2) as MU3.
  pose proof (wmono_refl rsegs m2) as WMO3.
  do 4 zstep.
  (* the world is now op_begin's result, the model's B1 *)
  assert (EB1 : upd (upd Bb 65544 (put 4 (-1))) 88 (put 4 (u_at Bb OFF_g_fail_next 1)) = B1).
  { rewrite (op4_begin_world B Bb LBz eq_refl) in HB1. apply opt_pair_inv in HB1. destruct HB1 as [E _].
    exact (eq_sym E). }
  assert (L1' : Z.of_nat (length (upd Bb 65544 (put 4 (-1)))) = 65616)
    by (rewrite length_upd_put; [exact LBb | lia | rewrite LBb; cbn [Z.of_nat]; lia]).
  assert (FN1 : g_fail_next B1 = g_fail_next Bb).
  { rewrite <- EB1. rewrite (op4_fn_put _ 88 4 _ L1') by (cbn [Z.of_nat]; lia).
    apply op4_fn_put; [exact LBb | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia]. }
  lazymatch goal with
  | W : wmem rsegs ?m4 (upd (upd Bb 65544 (put 4 (-1))) 88 (put 4 (u_at Bb OFF_g_fail_next 1))) |- _ =>
      rewrite EB1 in W;
      assert (HM3 : llvm_mem data D regs0 m0 Sp lo B1 m4 j10 jio j60)
        by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 Bb B1 m2 m4);
              [ exact HM2 | unfold LH_K; lia | exact MU3 | exact WMO3 | exact HMI | exact HSTK | exact W
              | rewrite FN1; exact HFN ]);
      clear W
  end.
  clear HM2 HMI HSTK HFN MU3 WMO3.
  (* ---- 0x13a84-0x13a90: sd zero at sp+0x60, 0x68, 0x70, 0x78: the struct diginet_cmd c = 0 (:1075) ---- *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
    pose proof HM3 as HM3c; unfold llvm_mem in HM3c;
    destruct HM3c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & HRW);
    destruct (llvm_frame_split regs0 m4 Sp j10 jio j60 HRW) as (F1 & F2 & F3 & F4 & F5 & F6); clear HRW;
    unfold llvm_saved in F6;
    pose proof (munch_refl [(Sp, Sp + 240)] m4) as MU4; pose proof (wmono_refl rsegs m4) as WMO4
  end.
  do 4 zstep.
  (* the four sd leave the struct zero *)
  apply rw_cells_merge_all in F5. cbn [cells_size csize Nat.add cells_bytes cbytes] in F5.
  rewrite op4_zeros32 in F5.
  lazymatch type of F5 with rw_cells rsegs ?m5 (Sp + 96) [CB 40 (repeat (b8 0) 32 ++ ?X)] =>
    pose proof (rw_cells_CB_len _ _ _ _ F5) as L60;
    pose proof (llvm_frame_join regs0 m5 Sp j10 jio (repeat (b8 0) 32 ++ X) F1 F2 F3 F4 F5 F6) as HRW5;
    pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 _ m5 j10 jio j60 j10 jio _ HM3 MU4 WMO4 HMI HRW5
                  HJ1 HJ2 L60) as HM5;
    apply HK; unfold op4_s1;
    do 16 eexists; exists m5, j10, jio, X
  end.
  split; [reflexivity|]. split; [exact HOPS|]. split; [exact HN|]. split; [exact HC|]. split; [exact HC1|].
  split; [exact RQ|]. split; [rewrite app_length, repeat_length in L60; lia|]. exact HM5.
Qed.
